'use strict';
/* ═══════════════════════════════════════════════════════════════════
   АЙКА МИР v2 — живая пиксельная деревня.
   Мир генерируется случайно. Жители думают, строят, заводят детей.
   Ночью из тьмы приходят слаймы. В лесу живут волки и кролики.
   Идёт дождь. Деревня сражается, растёт и эволюционирует.
   ═══════════════════════════════════════════════════════════════════ */

// ── Константы мира ────────────────────────────────────────────────
const W = 120, H = 76, TILE = 8;
const MAP_W = W * TILE, MAP_H = H * TILE;
const DAY_LEN = 240; // сим-секунд на сутки

// ── Глобальное состояние ──────────────────────────────────────────
let world = null;
let objects = [];
let objAt = new Map();
let villagers = [];
let animals = [];   // кролики и волки
let monsters = [];  // слаймы (враги, приходят ночью)
let campfire = { x: 0, y: 0 };
let huts = [];
let farms = [];     // объекты типа 'farm' тоже лежат в objects
let stocks = { wood: 0, berries: 6, stone: 0, fur: 0 };
let totalWood = 0;
let pendingBuild = null;   // { kind:'hut'|'farm', x, y, assigned }
let settlersThresholds = [30, 70, 130, 220, 340];
let settlersSpawned = 0;
let simTime = 0;
let simSpeed = 1, paused = false, inMenu = true, menuScene = true;
let mode = 'observer'; // 'observer' | 'life'
let P = null;        // игрок в режиме «Жизнь»
let worldId = null, worldName = '';
let seed = (Date.now() % 2147483647) | 0;
function urlSeed() {
  try { const p = new URLSearchParams(location.search).get('seed'); return p ? (Math.abs(parseInt(p, 10)) || null) : null; } catch (e) { return null; }
}
let rng = null;
let camX = 0, camY = 0, zoom = 1.6;
let selected = null;
let nextId = 1;
let lastPhase = 0;
let weather = { rain: false, kind: 'clear', t: 80, bolt: 0 };
const regrowQueue = [];
const SIM = { monsterWaves: 0, monsterKills: 0, deaths: 0, births: 0, harvests: 0, rains: 0 };

// ── Утилиты ───────────────────────────────────────────────────────
function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
const key = (x, y) => x + y * W;
const inb = (x, y) => x >= 0 && y >= 0 && x < W && y < H;
const dist2 = (ax, ay, bx, by) => (ax - bx) * (ax - bx) + (ay - by) * (ay - by);
const dist = (ax, ay, bx, by) => Math.hypot(ax - bx, ay - by);

function makeNoise(s) {
  function hash(ix, iy) {
    let n = Math.imul(ix, 374761393) + Math.imul(iy, 668265263) + Math.imul(s, 1442695041);
    n = Math.imul(n ^ n >>> 13, 1274126177);
    n ^= n >>> 16;
    return (n >>> 0) / 4294967295;
  }
  const sm = t => t * t * (3 - 2 * t);
  function n2(x, y) {
    const ix = Math.floor(x), iy = Math.floor(y);
    const fx = sm(x - ix), fy = sm(y - iy);
    const a = hash(ix, iy), b = hash(ix + 1, iy), c = hash(ix, iy + 1), d = hash(ix + 1, iy + 1);
    return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
  }
  return function (x, y) {
    let v = 0, amp = 0.5, f = 1;
    for (let o = 0; o < 4; o++) { v += amp * n2(x * f, y * f); amp *= 0.5; f *= 2; }
    return v / 0.9375;
  };
}

// ── Типы тайлов ───────────────────────────────────────────────────
const TILE_COLORS = {
  0: [27, 54, 93], 1: [52, 110, 166], 2: [216, 196, 122],
  3: [94, 140, 66], 4: [110, 156, 74], 5: [120, 120, 128], 6: [225, 228, 235],
  7: [224, 188, 124], 8: [172, 160, 88],
  9: [66, 92, 66], 10: [96, 106, 74], 11: [40, 58, 38], 12: [150, 178, 132], 13: [228, 234, 242]
};
const isWalkTile = t => (t >= 2 && t <= 4) || t === 7 || t === 8 || (t >= 9 && t <= 13);
const BLOCKING = new Set(['tree', 'pine', 'bush', 'stone', 'hut', 'campfire', 'farm', 'shelter', 'house', 'mine', 'cactus', 'acacia', 'mangrove', 'deadtree', 'darkpine', 'cherry', 'reed', 'mushroom']);
const seedArid = s => mulberry32((s | 0) + 12345)();
const seedClimate = s => Math.floor(mulberry32((s | 0) + 54321)() * 6); // 0 луга 1 пустыня 2 болота 3 тёмный лес 4 вишнёвый 5 снежный
let worldArid = 0, worldClimate = 0;
const CLIMATE_NAMES = ['луга', 'пустыня', 'болота', 'тёмный лес', 'вишнёвая роща', 'снежная тундра'];
const CLIMATE_LLM = ['зелёные луга', 'бескрайняя пустыня с оазисами', 'мангровые болота и топи', 'тёмный дремучий лес', 'цветущая вишнёвая роща', 'снежная тундра'];

function blockingAt(x, y) {
  const o = objAt.get(key(x, y));
  return o && BLOCKING.has(o.type);
}
const walkable = (x, y) => inb(x, y) && isWalkTile(world[key(x, y)]) && !blockingAt(x, y);

function randWalkable(minDistFromCamp, maxTry) {
  for (let i = 0; i < (maxTry || 300); i++) {
    const x = Math.floor(rng() * W), y = Math.floor(rng() * H);
    if (walkable(x, y) && (!minDistFromCamp || dist2(x, y, campfire.x, campfire.y) > minDistFromCamp * minDistFromCamp))
      return { x: x + 0.5, y: y + 0.5 };
  }
  return { x: campfire.x + 0.5, y: campfire.y + 2.5 };
}

// ── Генерация мира ────────────────────────────────────────────────
function genWorld(s) {
  rng = mulberry32(s);
  const clim = seedClimate(s); worldClimate = clim; worldArid = clim === 1 ? 0.85 : 0.25;
  const arid = worldArid;
  const nE = makeNoise(s), nM = makeNoise(s + 7777);
  world = new Uint8Array(W * H);
  const moistArr = new Float32Array(W * H);
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const dx = (x / W - 0.5) * 2, dy = (y / H - 0.5) * 2;
      const grad = Math.sqrt(dx * dx + dy * dy);
      let e = nE(x * 0.05, y * 0.05) * 0.85 + (1 - grad) * 0.35 - 0.1;
      const m = nM(x * 0.06 + 400, y * 0.06);
      moistArr[key(x, y)] = m;
      let t;
      if (e < 0.30) t = 0;
      else if (e < 0.38) t = 1;
      else if (e < 0.44) t = 2;
      else if (e > 0.82) t = arid > 0.6 ? 5 : 6;
      else if (e > 0.74) t = 5;
      else if (clim === 1) { // пустыня
        const dry = 0.8 + (0.55 - m) * 0.42;
        if (dry > 0.6) t = 7;
        else if (dry > 0.48) t = 8;
        else if (m > 0.86) t = 4; // оазис
        else t = m > 0.55 ? 4 : 3;
      }
      else if (clim === 2) { t = m > 0.52 ? 9 : (m > 0.34 ? 10 : 3); }   // мангры / топи
      else if (clim === 3) { t = m > 0.3 ? 11 : 3; }                     // тёмный лес
      else if (clim === 4) { t = m > 0.38 ? 12 : 3; }                    // вишнёвый лес
      else if (clim === 5) { t = 13; }                                    // снега
      else { t = m > 0.55 ? 4 : 3; }
      world[key(x, y)] = t;
    }
  }
  objects = []; objAt = new Map();
  for (let y = 1; y < H - 1; y++) {
    for (let x = 1; x < W - 1; x++) {
      const t = world[key(x, y)];
      const m = moistArr[key(x, y)];
      const r = rng();
      if (t === 4 && r < 0.045) addObject('bush', x, y);
      else if (t === 3 && r < (m > 0.45 ? 0.26 : 0.06)) addObject(m < 0.33 ? 'pine' : 'tree', x, y);
      else if (t === 4 && r < 0.07) addObject('tree', x, y);
      else if (t === 3 && r < 0.19) addObject('flower', x, y);
      else if ((t === 5 || t === 2) && r < 0.02) addObject('stone', x, y);
      else if (t === 7 && r < 0.05) addObject('cactus', x, y);
      else if (t === 7 && r < 0.058) addObject('stone', x, y);
      else if (t === 7 && r < 0.064) addObject('acacia', x, y); // одинокая акация в песках
      else if (t === 8 && r < 0.05) addObject('acacia', x, y);
      else if (t === 8 && r < 0.08) addObject('bush', x, y);
      else if (t === 9 && r < 0.12) addObject('mangrove', x, y);
      else if (t === 10 && r < 0.05) addObject('reed', x, y);
      else if (t === 10 && r < 0.07) addObject('deadtree', x, y);
      else if (t === 11 && r < 0.32) addObject('darkpine', x, y);
      else if (t === 11 && r < 0.36) addObject('mushroom', x, y);
      else if (t === 12 && r < 0.1) addObject('cherry', x, y);
      else if (t === 12 && r < 0.15) addObject('bush', x, y);
      else if (t === 12 && r < 0.33) addObject('flower', x, y);
      else if (t === 13 && r < 0.035) addObject('pine', x, y);
      else if (t === 13 && r < 0.042) addObject('stone', x, y);
      else if (t === 13 && r < 0.048) addObject('bush', x, y);
    }
  }
  // место для деревни
  let best = null, bestScore = -1;
  for (let ty = 12; ty < H - 12; ty += 2) {
    for (let tx = 12; tx < W - 12; tx += 2) {
      if (!walkable(tx, ty)) continue;
      let score = 0;
      for (let k = 0; k < 40; k++) {
        const ox = tx + Math.floor(rng() * 13) - 6, oy = ty + Math.floor(rng() * 13) - 6;
        if (walkable(ox, oy)) score++;
      }
      score += (400 - dist2(tx, ty, W / 2, H / 2) * 0.5) * 0.02;
      if (score > bestScore) { bestScore = score; best = { x: tx, y: ty }; }
    }
  }
  if (!best) best = { x: W >> 1, y: H >> 1 };
  campfire.x = best.x; campfire.y = best.y;
  for (let y = best.y - 3; y <= best.y + 3; y++)
    for (let x = best.x - 3; x <= best.x + 3; x++) {
      const o = objAt.get(key(x, y));
      if (o && ['tree', 'bush', 'stone', 'pine', 'cactus', 'acacia', 'mangrove', 'deadtree', 'darkpine', 'cherry', 'reed', 'mushroom'].includes(o.type)) removeObject(o);
    }
  addObject('campfire', campfire.x, campfire.y);
  huts = [];
  farms = [];

  // двое древних людей — начало великого пути
  villagers = [];
  const spawn = [[best.x - 2, best.y + 2], [best.x + 2, best.y - 2]];
  for (let i = 0; i < 2; i++) {
    const p = spawn[i];
    if (!walkable(p[0], p[1])) { p[0] = best.x; p[1] = best.y + 1 + i; }
    villagers.push(makeVillager(p[0] + 0.5, p[1] + 0.5));
  }

  // животные
  animals = [];
  for (let i = 0; i < 14; i++) {
    const p = randWalkable(8);
    animals.push({ id: nextId++, kind: 'rabbit', x: p.x, y: p.y, hp: 5, state: 'idle', t: rng() * 2, dirX: 0, dirY: 0, facing: 1, animT: 0 });
  }
  const nWolves = (clim === 1 || clim === 5) ? 2 : 5;
  for (let i = 0; i < nWolves; i++) {
    const p = randWalkable(14);
    animals.push({ id: nextId++, kind: 'wolf', x: p.x, y: p.y, hp: 12, state: 'idle', t: rng() * 3, dirX: 0, dirY: 0, facing: 1, animT: 0, preyId: 0 });
  }
  if (clim === 1) for (let i = 0; i < 4; i++) {
    const p = randWalkable(8);
    animals.push({ id: nextId++, kind: 'camel', x: p.x, y: p.y, hp: 16, state: 'idle', t: rng() * 3, dirX: 0, dirY: 0, facing: 1, animT: 0, preyId: 0 });
  }
  if (clim === 5) for (let i = 0; i < 6; i++) {
    const p = randWalkable(8);
    animals.push({ id: nextId++, kind: 'deer', x: p.x, y: p.y, hp: 14, state: 'idle', t: rng() * 3, dirX: 0, dirY: 0, facing: 1, animT: 0, preyId: 0 });
  }
  monsters = [];
  stocks = { wood: 0, berries: 6, stone: 0, fur: 0 };
  totalWood = 0; pendingBuild = null; settlersSpawned = 0;
  simTime = 0; selected = null; selectedObj = null; selectedEnt = null; lastPhase = 0;
  weather = { rain: false, kind: 'clear', t: 60 + rng() * 120, bolt: 0 };
  SIM.monsterWaves = 0; SIM.monsterKills = 0; SIM.melted = 0; SIM.deaths = 0; SIM.births = 0; SIM.harvests = 0; SIM.rains = 0;
  renderMapCanvas();
  const climate = [' на зелёных лугах', ' среди бескрайних песков', ' в мангровых болотах', ' в дремучем тёмном лесу', ' в цветущей вишнёвой роще', ' среди снегов и льдов'][clim];
  logEvent('🔥', 'Двое древних людей разожгли костёр' + climate + '!');
  if (clim > 0) logEvent('🌍', 'Климат этого мира: ' + CLIMATE_NAMES[clim] + '.');
}

function addObject(type, x, y) {
  const o = { id: nextId++, type, x, y };
  if (type === 'tree' || type === 'pine' || type === 'acacia' || type === 'mangrove' || type === 'deadtree' || type === 'darkpine' || type === 'cherry') { o.variant = Math.floor(rng() * 3); o.regrow = 0; }
  if (type === 'bush' || type === 'cactus') { o.depleted = false; o.regrowAt = 0; }
  if (type === 'farm') { o.stage = 1; o.growAt = 0; farms.push(o); }
  objects.push(o); objAt.set(key(x, y), o);
  return o;
}
function removeObject(o) {
  const i = objects.indexOf(o);
  if (i >= 0) objects.splice(i, 1);
  objAt.delete(key(o.x, o.y));
  if (o.type === 'farm') { const j = farms.indexOf(o); if (j >= 0) farms.splice(j, 1); }
}
function addHut(x, y) {
  if (!walkable(x, y)) return false;
  addObject('hut', x, y);
  huts.push({ x, y });
  return true;
}
const ERAS = [null, 'Древний лагерь', 'Стоянка', 'Деревня', 'Поселение', 'Бронзовый век', 'Пороховая эпоха', 'Современность'];
function cnt(type) { let n = 0; for (const o of objects) if (o.type === type) n++; return n; }
function beds() { return cnt('shelter') * 2 + cnt('hut') * 2 + cnt('house') * 3; }
function homes() { return objects.filter(o => o.type === 'shelter' || o.type === 'hut' || o.type === 'house'); }
function era() {
  if (mode === 'life' && P) {
    if (P.weapon === 5) return 7; // автомат — современность
    if (P.weapon === 4) return 6; // мушкет — порох
  }
  if (cnt('house') >= 2) {
    if (mode === 'life' && P && P.weapon === 3) return 5; // игрок принёс деревне бронзу
    return 4;
  }
  if (cnt('hut') >= 2) return 3;
  if (cnt('shelter') >= 1) return 2;
  return 1;
}
let lastEra = 1;

// ── Текстуры ─────────────────────────────────────────────────────
const tileTex = {};
const spr = {};

function px(g, x, y, r, g2, b) { g.fillStyle = `rgb(${r},${g2},${b})`; g.fillRect(x, y, 1, 1); }
function jitter(base, r) {
  return [
    Math.max(0, Math.min(255, base[0] + Math.floor((r() - 0.5) * 26))),
    Math.max(0, Math.min(255, base[1] + Math.floor((r() - 0.5) * 26))),
    Math.max(0, Math.min(255, base[2] + Math.floor((r() - 0.5) * 26)))
  ];
}

function makeTextures() {
  const r = mulberry32(12345);
  for (const t of Object.keys(TILE_COLORS)) {
    tileTex[t] = [];
    for (let v = 0; v < 4; v++) {
      const c = document.createElement('canvas');
      c.width = TILE; c.height = TILE;
      const g = c.getContext('2d');
      const base = TILE_COLORS[t];
      for (let y = 0; y < TILE; y++)
        for (let x = 0; x < TILE; x++) {
          const col = jitter(base, r);
          px(g, x, y, col[0], col[1], col[2]);
        }
      if (+t === 3 || +t === 4) {
        for (let k = 0; k < 3; k++) {
          const x = Math.floor(r() * 8), y = Math.floor(r() * 8);
          const d = r() < 0.5 ? [62, 104, 44] : [128, 172, 88];
          px(g, x, y, d[0], d[1], d[2]);
        }
      }
      if (+t === 2) {
        for (let k = 0; k < 2; k++)
          px(g, Math.floor(r() * 8), Math.floor(r() * 8), 190, 170, 100);
      }
      if (+t === 5) {
        const x0 = Math.floor(r() * 6), y0 = Math.floor(r() * 8);
        px(g, x0, y0, 90, 90, 98); px(g, x0 + 1, y0, 90, 90, 98);
      }
      if (+t === 4 && r() < 0.5) {
        const fx2 = Math.floor(r() * 7), fy = Math.floor(r() * 7);
        const col = r() < 0.5 ? [235, 220, 120] : [220, 130, 150];
        px(g, fx2, fy, col[0], col[1], col[2]);
      }
      tileTex[t].push(c);
    }
  }
  // деревья
  spr.tree = [];
  for (let v = 0; v < 3; v++) {
    const c = document.createElement('canvas'); c.width = 10; c.height = 14;
    const g = c.getContext('2d');
    g.fillStyle = 'rgb(92,64,38)'; g.fillRect(4, 9, 2, 5);
    g.fillStyle = 'rgb(70,48,28)'; g.fillRect(5, 10, 1, 4);
    const leaves = [[2,2],[3,1],[4,1],[5,1],[6,2],[7,3],[1,3],[2,3],[3,2],[4,2],[5,2],[6,3],[7,4],[1,4],[2,4],[3,3],[4,3],[5,3],[6,4],[2,5],[3,4],[4,4],[5,4],[3,5],[4,5],[5,5],[6,5]];
    for (const [lx, ly] of leaves) {
      const shade = r();
      const col = shade < 0.3 ? [40, 92, 34] : shade < 0.7 ? [58, 116, 44] : [78, 140, 58];
      px(g, lx + 1, ly, col[0], col[1], col[2]);
    }
    px(g, 4, 0, 58, 116, 44); px(g, 5, 0, 58, 116, 44);
    spr.tree.push(c);
  }
  // сосны
  spr.pine = [];
  for (let v = 0; v < 3; v++) {
    const c = document.createElement('canvas'); c.width = 10; c.height = 14;
    const g = c.getContext('2d');
    g.fillStyle = 'rgb(80,56,34)'; g.fillRect(4, 11, 2, 3);
    for (let row = 0; row < 10; row++) {
      const width = 2 + Math.floor(row * 0.6);
      for (let x = 5 - Math.ceil(width / 2); x <= 4 + Math.ceil(width / 2); x++) {
        const shade = r();
        const col = shade < 0.4 ? [24, 70, 40] : [34, 88, 50];
        px(g, Math.max(0, x), row + 1, col[0], col[1], col[2]);
      }
    }
    spr.pine.push(c);
  }
  // кусты
  spr.bush = [makeBush(false, r), makeBush(true, r)];
  // кактус (с плодами / обобранный)
  spr.cactus = (() => {
    const mk = withFruit => {
      const c = document.createElement('canvas'); c.width = 10; c.height = 14;
      const g = c.getContext('2d');
      for (let y = 4; y < 14; y++) { px(g, 4, y, 62, 132, 66); px(g, 5, y, 48, 108, 52); }
      px(g, 4, 13, 40, 84, 42); px(g, 5, 13, 40, 84, 42);
      // руки
      for (let y = 6; y < 9; y++) px(g, 2, y, 56, 120, 60);
      px(g, 1, 5, 56, 120, 60); px(g, 2, 5, 62, 132, 66); px(g, 1, 6, 62, 132, 66);
      for (let y = 8; y < 11; y++) px(g, 7, y, 56, 120, 60);
      px(g, 8, 7, 56, 120, 60); px(g, 8, 8, 62, 132, 66); px(g, 7, 7, 62, 132, 66);
      px(g, 4, 4, 74, 150, 74); px(g, 5, 4, 74, 150, 74);
      if (withFruit) { px(g, 4, 3, 224, 92, 60); px(g, 5, 3, 224, 92, 60); px(g, 1, 5, 224, 92, 60); px(g, 8, 7, 224, 92, 60); }
      return c;
    };
    return [mk(true), mk(false)];
  })();
  // акация — плоское сухое дерево
  spr.acacia = (() => {
    const c = document.createElement('canvas'); c.width = 14; c.height = 14;
    const g = c.getContext('2d');
    for (let y = 9; y < 14; y++) { px(g, 6, y, 118, 88, 52); px(g, 7, y, 96, 70, 40); }
    px(g, 6, 13, 80, 58, 34);
    for (let x = 1; x < 13; x++) for (let y = 4; y < 9; y++) {
      const edge = Math.abs(x - 6.5) / 5.5 + Math.abs(y - 6) / 3.2;
      if (edge < 1) px(g, x, y, r() < 0.35 ? [124, 130, 60] : [148, 152, 72]);
    }
    px(g, 5, 3, 148, 152, 72); px(g, 6, 3, 148, 152, 72); px(g, 7, 3, 148, 152, 72);
    return c;
  })();
  function makeBush(depleted, r) {
    const c = document.createElement('canvas'); c.width = 10; c.height = 8;
    const g = c.getContext('2d');
    for (let y = 2; y < 7; y++) for (let x = 1; x < 9; x++) {
      const d = Math.abs(x - 4.5) + (6 - y);
      if (d < 6) {
        const col = r() < 0.4 ? [34, 86, 40] : [52, 110, 52];
        px(g, x, y, col[0], col[1], col[2]);
      }
    }
    if (!depleted) for (let k = 0; k < 5; k++)
      px(g, 2 + Math.floor(r() * 6), 2 + Math.floor(r() * 4), 210, 60, 70);
    return c;
  }
  // камень
  spr.stone = (() => {
    const c = document.createElement('canvas'); c.width = 8; c.height = 7;
    const g = c.getContext('2d');
    for (let y = 1; y < 6; y++) for (let x = 1; x < 7; x++) {
      if (Math.abs(x - 3.5) + Math.abs(y - 3) < 4) {
        const col = r() < 0.5 ? [110, 110, 118] : [140, 140, 148];
        px(g, x, y, col[0], col[1], col[2]);
      }
    }
    px(g, 2, 1, 165, 165, 172);
    return c;
  })();
  // цветок
  spr.flower = (() => {
    const c = document.createElement('canvas'); c.width = 6; c.height = 6;
    const g = c.getContext('2d');
    px(g, 2, 5, 70, 120, 50); px(g, 2, 4, 70, 120, 50);
    const cols = [[240, 210, 90], [235, 130, 140], [140, 160, 240]];
    const col = cols[Math.floor(r() * 3)];
    px(g, 2, 3, col[0], col[1], col[2]); px(g, 1, 3, col[0], col[1], col[2]);
    px(g, 3, 3, col[0], col[1], col[2]); px(g, 2, 2, col[0], col[1], col[2]);
    return c;
  })();
  // пень
  spr.stump = (() => {
    const c = document.createElement('canvas'); c.width = 6; c.height = 4;
    const g = c.getContext('2d');
    for (let y = 1; y < 4; y++) for (let x = 0; x < 6; x++)
      if (y < 2 || (x > 0 && x < 5)) px(g, x, y, 110, 80, 50);
    px(g, 1, 0, 150, 116, 76); px(g, 2, 0, 150, 116, 76); px(g, 3, 0, 150, 116, 76);
    px(g, 2, 1, 120, 90, 58);
    return c;
  })();
  // хижина v2 — аккуратный сруб с дверью, окном и трубой
  spr.hut = (() => {
    const c = document.createElement('canvas'); c.width = 18; c.height = 16;
    const g = c.getContext('2d');
    // стены: горизонтальные брёвна
    for (let y = 8; y < 15; y++) {
      for (let x = 1; x < 17; x++) {
        const log = y % 2 === 0;
        const col = log ? [148, 106, 66] : [128, 92, 58];
        px(g, x, y, col[0], col[1], col[2]);
        if (x % 4 === 0 && log) px(g, x, y, 108, 76, 48); // стыки брёвен
      }
    }
    // тёмная обвязка
    for (let x = 1; x < 17; x++) { px(g, x, 8, 96, 68, 44); px(g, x, 14, 90, 64, 42); }
    // дверь по центру
    for (let y = 10; y < 15; y++) for (let x = 8; x < 11; x++) px(g, x, y, 66, 46, 30);
    px(g, 7, 10, 84, 60, 40); px(g, 11, 10, 84, 60, 40);
    px(g, 10, 12, 210, 180, 120); // ручка
    // окно слева
    for (let y = 10; y < 12; y++) for (let x = 4; x < 7; x++) px(g, x, y, 40, 30, 24);
    px(g, 3, 10, 84, 60, 40); px(g, 7, 10, 84, 60, 40);
    // крыша: двухскатная с коньком и свесами (узко у конька сверху, широко у стен снизу)
    for (let row = 0; row < 8; row++) {
      const inset = 7 - row;
      for (let x = inset; x < 18 - inset; x++) {
        const col = row === 7 ? [70, 46, 32] : (row % 2 ? [96, 62, 44] : [112, 74, 50]);
        px(g, x, row, col[0], col[1], col[2]);
      }
    }
    for (let x = 7; x < 11; x++) px(g, x, 0, 132, 92, 64); // конёк
    // труба
    for (let y = 0; y < 3; y++) for (let x = 13; x < 15; x++) px(g, x, y, 130, 130, 138);
    spr.hutWindow = { x: 4, y: 10, w: 3, h: 2 };
    spr.hutChimney = { x: 13, y: 0 };
    return c;
  })();
  // шалаш — вигвам из жердей
  spr.shelter = (() => {
    const c = document.createElement('canvas'); c.width = 14; c.height = 14;
    const g = c.getContext('2d');
    for (let i = 0; i < 12; i++) {
      const spread = Math.round(i * 0.5);
      px(g, 6 - spread, 1 + i, 118, 86, 54);
      px(g, 6 + spread + 1, 1 + i, 102, 74, 46);
    }
    // вход
    for (let y = 8; y < 13; y++) for (let x = 5; x < 9; x++) px(g, x, y, 34, 26, 20);
    // связка сверху
    px(g, 6, 0, 140, 104, 64); px(g, 7, 0, 140, 104, 64);
    return c;
  })();
  // дом — каменный фундамент, трубы, два окна
  spr.house = (() => {
    const c = document.createElement('canvas'); c.width = 22; c.height = 18;
    const g = c.getContext('2d');
    // каменный фундамент
    for (let y = 15; y < 18; y++) for (let x = 1; x < 21; x++) {
      const col = (x + y) % 3 ? [128, 126, 132] : [106, 104, 112];
      px(g, x, y, col[0], col[1], col[2]);
    }
    // стены светлые
    for (let y = 7; y < 15; y++) for (let x = 2; x < 20; x++) {
      const col = (x + y) % 2 ? [170, 136, 92] : [156, 124, 84];
      px(g, x, y, col[0], col[1], col[2]);
    }
    // дверь
    for (let y = 10; y < 15; y++) for (let x = 10; x < 13; x++) px(g, x, y, 70, 48, 32);
    px(g, 12, 12, 214, 184, 124);
    // окна
    for (const wx of [4, 16]) {
      for (let y = 10; y < 12; y++) for (let x = wx; x < wx + 3; x++) px(g, x, y, 44, 34, 28);
      px(g, wx + 1, 10, 120, 130, 140); px(g, wx + 1, 11, 120, 130, 140);
      px(g, wx - 1, 10, 96, 68, 44); px(g, wx + 3, 10, 96, 68, 44);
    }
    // крыша тёмная с чередованием (узко у конька сверху, широко у стен снизу)
    for (let row = 0; row < 7; row++) {
      const inset = 6 - row;
      for (let x = inset; x < 22 - inset; x++) {
        const col = row === 6 ? [80, 52, 40] : (x + row) % 2 ? [140, 74, 54] : [122, 62, 46];
        px(g, x, row, col[0], col[1], col[2]);
      }
    }
    // труба кирпичная
    for (let y = 0; y < 5; y++) for (let x = 15; x < 18; x++) {
      const col = y % 2 ? [150, 84, 62] : [134, 72, 54];
      px(g, x, y, col[0], col[1], col[2]);
    }
    spr.houseWindows = [{ x: 4, y: 10, w: 3, h: 2 }, { x: 16, y: 10, w: 3, h: 2 }];
    spr.houseChimney = { x: 16, y: 0 };
    return c;
  })();
  // глинобитные варианты для пустыни
  const adobeTint = (base, tr, tg, tb, a) => {
    const c = document.createElement('canvas'); c.width = base.width; c.height = base.height;
    const g = c.getContext('2d');
    g.drawImage(base, 0, 0);
    g.globalCompositeOperation = 'source-atop';
    g.fillStyle = 'rgba(' + tr + ',' + tg + ',' + tb + ',' + a + ')';
    g.fillRect(0, 0, c.width, c.height);
    return c;
  };
  spr.hutD = adobeTint(spr.hut, 205, 165, 110, 0.5);
  spr.shelterD = adobeTint(spr.shelter, 210, 175, 120, 0.55);
  spr.houseD = adobeTint(spr.house, 205, 160, 105, 0.45);
  // топи и тёмный лес — тёмная промёрзлая древесина
  spr.hutN = adobeTint(spr.hut, 42, 48, 40, 0.55);
  spr.shelterN = adobeTint(spr.shelter, 40, 46, 38, 0.55);
  spr.houseN = adobeTint(spr.house, 44, 50, 44, 0.5);
  // вишнёвая роща — розоватое дерево
  spr.hutK = adobeTint(spr.hut, 255, 190, 210, 0.42);
  spr.shelterK = adobeTint(spr.shelter, 255, 196, 214, 0.45);
  spr.houseK = adobeTint(spr.house, 255, 188, 208, 0.4);
  // снега — морозные избы
  spr.hutS = adobeTint(spr.hut, 222, 234, 252, 0.5);
  spr.shelterS = adobeTint(spr.shelter, 226, 238, 254, 0.55);
  spr.houseS = adobeTint(spr.house, 220, 232, 250, 0.45);
  // мангр, сухостой, тёмная ель, сакура — тинты деревьев
  const treeTint = (list, tr, tg, tb, a) => list.map(c => adobeTint(c, tr, tg, tb, a));
  spr.mangrove = treeTint(spr.tree, 46, 74, 44, 0.55);
  spr.deadtree = treeTint(spr.tree, 120, 112, 96, 0.6);
  spr.darkpine = treeTint(spr.pine, 14, 22, 16, 0.55);
  spr.cherry = treeTint(spr.tree, 255, 168, 196, 0.5);
  // камыш
  spr.reed = (() => {
    const c = document.createElement('canvas'); c.width = 10; c.height = 10;
    const g = c.getContext('2d');
    for (let i = 0; i < 5; i++) {
      const bx = 1 + i * 2, h = 6 + Math.floor(r() * 3);
      for (let y = 0; y < h; y++) px(g, bx + (y % 2 ? 0 : 1), 9 - y, 96, 122, 60);
      px(g, bx + 1, 9 - h, 116, 88, 44); px(g, bx + 1, 8 - h, 116, 88, 44);
    }
    return c;
  })();
  // грибы (со шляпкой / обобранный)
  spr.mushroom = (() => {
    const mk = full => {
      const c = document.createElement('canvas'); c.width = 8; c.height = 7;
      const g = c.getContext('2d');
      px(g, 3, 4, 220, 210, 190); px(g, 4, 4, 220, 210, 190); px(g, 3, 5, 200, 190, 170); px(g, 4, 5, 200, 190, 170);
      px(g, 2, 2, 196, 60, 50); px(g, 3, 2, 214, 70, 58); px(g, 4, 2, 196, 60, 50); px(g, 5, 2, 178, 52, 44);
      px(g, 2, 3, 214, 70, 58); px(g, 3, 3, 224, 84, 68); px(g, 4, 3, 214, 70, 58); px(g, 5, 3, 196, 60, 50);
      if (full) { px(g, 3, 1, 236, 226, 210); px(g, 5, 1, 236, 226, 210); }
      return c;
    };
    return [mk(true), mk(false)];
  })();
  // костёр
  spr.campfire = (() => {
    const c = document.createElement('canvas'); c.width = 10; c.height = 10;
    const g = c.getContext('2d');
    g.fillStyle = 'rgb(96,68,40)'; g.fillRect(1, 7, 8, 2);
    g.fillStyle = 'rgb(120,86,50)'; g.fillRect(2, 6, 6, 1);
    px(g, 0, 8, 110, 110, 118); px(g, 9, 8, 110, 110, 118);
    return c;
  })();
  // ферма (пшеница), 16×10, стадии 1..3
  spr.farm = [null, makeFarm(1, r), makeFarm(2, r), makeFarm(3, r)];
  function makeFarm(stage, r) {
    const c = document.createElement('canvas'); c.width = 16; c.height = 10;
    const g = c.getContext('2d');
    // грядки
    for (let y = 0; y < 10; y++) for (let x = 0; x < 16; x++) {
      const col = (y % 3 === 2) ? [86, 62, 40] : [104, 78, 50];
      px(g, x, y, col[0], col[1], col[2]);
    }
    // ростки
    for (let row = 0; row < 3; row++) {
      for (let k = 0; k < 5; k++) {
        const x = k * 3 + 1, y = row * 3 + 1;
        if (stage === 1) { px(g, x, y, 90, 160, 60); px(g, x, y - 1, 110, 180, 70); }
        else if (stage === 2) { px(g, x, y, 110, 170, 60); px(g, x, y - 1, 130, 190, 80); px(g, x, y - 2, 150, 200, 90); }
        else { px(g, x, y, 190, 170, 60); px(g, x, y - 1, 210, 180, 70); px(g, x, y - 2, 230, 200, 80); px(g, x, y - 3, 240, 210, 90); }
      }
    }
    return c;
  }
  // могилка
  spr.grave = (() => {
    const c = document.createElement('canvas'); c.width = 6; c.height = 7;
    const g = c.getContext('2d');
    for (let y = 1; y < 6; y++) px(g, 2, y, 150, 150, 158);
    px(g, 3, 1, 150, 150, 158); px(g, 4, 1, 150, 150, 158);
    px(g, 1, 6, 110, 110, 118); px(g, 2, 6, 110, 110, 118); px(g, 3, 6, 110, 110, 118); px(g, 4, 6, 110, 110, 118);
    px(g, 2, 2, 90, 90, 98);
    return c;
  })();
  // кролик (2 кадра)
  spr.rabbit = (() => {
    const frames = [];
    for (let f = 0; f < 2; f++) {
      const c = document.createElement('canvas'); c.width = 7; c.height = 7;
      const g = c.getContext('2d');
      g.fillStyle = 'rgb(235,230,220)'; g.fillRect(1, 2 + f, 5, 4);           // тело
      g.fillRect(2, 0 + f, 1, 2); g.fillRect(4, 0 + f, 1, 2);                  // уши
      px(g, 5, 3, 20, 20, 20);                                                  // глаз
      px(g, 0, 5 + f, 200, 195, 185); px(g, 6, 5 + f, 200, 195, 185);          // лапки
      px(g, 2, 2 + f, 220, 215, 205);
      frames.push(c);
    }
    return frames;
  })();
  // волк (2 кадра)
  spr.wolf = (() => {
    const frames = [];
    for (let f = 0; f < 2; f++) {
      const c = document.createElement('canvas'); c.width = 11; c.height = 7;
      const g = c.getContext('2d');
      g.fillStyle = 'rgb(120,118,125)'; g.fillRect(1, 2, 8, 4);               // тело
      g.fillRect(8, 0, 2, 3); g.fillRect(9, 1, 1, 2);                          // голова+морда
      px(g, 7, 0, 120, 118, 125); px(g, 8, 0, 120, 118, 125);                  // уши
      px(g, 10, 1, 30, 30, 32);                                                 // нос
      px(g, 9, 1, 200, 60, 60);                                                  // глаз
      g.fillStyle = 'rgb(100,98,105)';
      g.fillRect(2 + f, 5, 2, 2); g.fillRect(6 - f, 5, 2, 2);                  // лапы
      px(g, 0, 2 + f, 100, 98, 105);                                            // хвост
      frames.push(c);
    }
    return frames;
  })();
  // слайма (2 кадра — пружинит)
  spr.slime = (() => {
    const frames = [];
    for (let f = 0; f < 2; f++) {
      const c = document.createElement('canvas'); c.width = 8; c.height = 8;
      const g = c.getContext('2d');
      const hgt = f ? 6 : 7, y0 = 8 - hgt;
      for (let y = y0; y < 8; y++) for (let x = 0; x < 8; x++) {
        if (Math.abs(x - 3.5) < 4 - (y - y0) * 0.3) {
          const col = y < y0 + 2 ? [110, 200, 90] : [70, 160, 60];
          px(g, x, y, col[0], col[1], col[2]);
        }
      }
      px(g, 2, y0 + 2, 20, 20, 20); px(g, 5, y0 + 2, 20, 20, 20);              // глаза
      frames.push(c);
    }
    return frames;
  })();
  // персонажи
  const HAIRS = [[62, 38, 24], [30, 24, 20], [150, 100, 50], [90, 60, 30], [40, 44, 90], [110, 40, 44]];
  const SHIRTS = [[170, 60, 60], [60, 90, 170], [80, 140, 80], [170, 140, 60], [140, 80, 150], [90, 90, 100]];
  const PANTS = [[50, 52, 70], [70, 50, 40], [40, 60, 50]];
  const SKINS = [[238, 190, 150], [220, 170, 130], [196, 148, 108]];
  spr.bodies = [];
  for (const hair of HAIRS) for (const shirt of SHIRTS)
    spr.bodies.push({ hair, shirt, pants: PANTS[Math.floor(r() * 3)], skin: SKINS[Math.floor(r() * 3)] });
  makeVillagerSprites();
}

function makeVillagerSpriteSet(body) {
  // 4-кадровый цикл ходьбы (шаг/проход/шаг/проход) с махами рук и
  // подъёмом корпуса на проходных кадрах. Раскладка по строкам (холст 8x14):
  //   волосы y0..y0+1, лицо y0+2..y0+4 (глаза y0+3), торс y0+5..y0+8,
  //   ремень y0+9, ноги y0+10..13. y0 = 2 (обычный) / 1 (корпус приподнят).
  const frames = [];
  const { hair, shirt, pants, skin } = body;
  const SHOE = [40, 34, 30], EYE = [28, 22, 20];
  const hi = (c, k) => `rgb(${Math.min(255, c[0] + k)},${Math.min(255, c[1] + k)},${Math.min(255, c[2] + k)})`;
  for (let f = 0; f < 4; f++) {
    const c = document.createElement('canvas'); c.width = 8; c.height = 14;
    const g = c.getContext('2d');
    const bob = (f === 1 || f === 3) ? 1 : 0;
    const y0 = 2 - bob;
    // волосы
    g.fillStyle = `rgb(${hair[0]},${hair[1]},${hair[2]})`;
    g.fillRect(1, y0, 6, 2); g.fillRect(0, y0 + 1, 8, 2);
    // лицо
    g.fillStyle = `rgb(${skin[0]},${skin[1]},${skin[2]})`;
    g.fillRect(1, y0 + 2, 6, 3);
    px(g, 2, y0 + 3, EYE[0], EYE[1], EYE[2]);
    px(g, 5, y0 + 3, EYE[0], EYE[1], EYE[2]);
    px(g, 1, y0 + 4, skin[0] * 0.86 | 0, skin[1] * 0.86 | 0, skin[2] * 0.86 | 0); // щека-тень
    // торс
    g.fillStyle = `rgb(${shirt[0]},${shirt[1]},${shirt[2]})`;
    g.fillRect(1, y0 + 5, 6, 4);
    g.fillStyle = hi(shirt, 45);
    g.fillRect(2, y0 + 5, 3, 1); // блик на груди
    // руки — качаются: на шаге Л правая рука вперёд(длиннее/ниже), левая назад(короче/выше); на шаге П зеркально
    g.fillStyle = `rgb(${shirt[0]},${shirt[1]},${shirt[2]})`;
    const leftDown  = f === 2;   // шаг П: левая рука идёт вниз-вперёд
    const rightDown = f === 0;   // шаг Л: правая рука вперёд
    const armTop = (down) => y0 + 6 + (down ? 0 : 1);
    const armLen = (down) => (down ? 3 : 2);
    // левая рука (x=0)
    g.fillRect(0, armTop(leftDown), 1, armLen(leftDown) - 1);
    px(g, 0, armTop(leftDown) + armLen(leftDown) - 1, skin[0], skin[1], skin[2]); // кисть
    // правая рука (x=7)
    g.fillRect(7, armTop(rightDown), 1, armLen(rightDown) - 1);
    px(g, 7, armTop(rightDown) + armLen(rightDown) - 1, skin[0], skin[1], skin[2]);
    // ремень
    g.fillStyle = `rgb(${pants[0]},${pants[1]},${pants[2]})`;
    g.fillRect(2, y0 + 9, 4, 1);
    // ноги (низ закреплён у земли: y11..y13)
    g.fillStyle = `rgb(${pants[0]},${pants[1]},${pants[2]})`;
    const shoe = (x) => px(g, x, 13, SHOE[0], SHOE[1], SHOE[2]);
    if (f === 0) {          // шаг Л: левая нога вперёд (2 ряда), правая назад (1 ряд)
      g.fillRect(1, 12, 2, 1); g.fillRect(5, 12, 2, 1);
      px(g, 1, 13, SHOE[0], SHOE[1], SHOE[2]); px(g, 2, 13, SHOE[0], SHOE[1], SHOE[2]);
      shoe(6);
    } else if (f === 2) {   // шаг П: зеркально
      g.fillRect(1, 12, 2, 1); g.fillRect(5, 12, 2, 1);
      shoe(1); px(g, 2, 13, SHOE[0], SHOE[1], SHOE[2]);
      px(g, 5, 13, SHOE[0], SHOE[1], SHOE[2]); px(g, 6, 13, SHOE[0], SHOE[1], SHOE[2]);
    } else {                // проход: ноги вместе, корпус приподнят — ноги длиннее на 1
      g.fillRect(2, 11, 2, 2); g.fillRect(4, 11, 2, 2);
      px(g, 2, 13, SHOE[0], SHOE[1], SHOE[2]); px(g, 3, 13, SHOE[0], SHOE[1], SHOE[2]);
      px(g, 4, 13, SHOE[0], SHOE[1], SHOE[2]); px(g, 5, 13, SHOE[0], SHOE[1], SHOE[2]);
    }
    frames.push(c);
  }
  return frames;
}

function makeVillagerSprites() {
  spr.villagerFrames = spr.bodies.map(b => makeVillagerSpriteSet(b));
  spr.villagerFlip = spr.villagerFrames.map(f => f.map(c => {
    const c2 = document.createElement('canvas'); c2.width = 8; c2.height = 14;
    const g = c2.getContext('2d');
    g.translate(8, 0); g.scale(-1, 1); g.drawImage(c, 0, 0);
    return c2;
  }));
}

// ── Канвас карты ─────────────────────────────────────────────────
let mapCanvas = null;
function renderMapCanvas() {
  mapCanvas = document.createElement('canvas');
  mapCanvas.width = MAP_W; mapCanvas.height = MAP_H;
  const g = mapCanvas.getContext('2d');
  const r = mulberry32(seed ^ 0x9e37);
  for (let y = 0; y < H; y++)
    for (let x = 0; x < W; x++) {
      const t = world[key(x, y)];
      const v = Math.floor(r() * 4);
      g.drawImage(tileTex[t][v], x * TILE, y * TILE);
      if (t >= 2 && t <= 4) {
        if (inb(x, y - 1) && world[key(x, y - 1)] <= 1) {
          g.fillStyle = 'rgba(220,220,180,0.25)'; g.fillRect(x * TILE, y * TILE, TILE, 1);
        }
      }
    }
}

// ── Персонажи ─────────────────────────────────────────────────────
const NAMES = ['Аскар', 'Дана', 'Марат', 'Айгерим', 'Тимур', 'Мадина', 'Арман', 'Камила', 'Ерлан', 'Сабина', 'Нурлан', 'Алия', 'Данияр', 'Жанна', 'Кайрат', 'Дина', 'Бекзат', 'Асель', 'Ислам', 'Гульнара'];
const TRAITS = [
  { k: 'hardworking', label: 'трудолюбивый' },
  { k: 'brave', label: 'храбрый' },
  { k: 'sociable', label: 'общительный' },
  { k: 'curious', label: 'любопытный' },
  { k: 'dreamer', label: 'мечтательный' },
  { k: 'kind', label: 'добрый' }
];
const THOUGHTS = {
  chop: ['Дерево само себя не срубит.', 'Тук-тук-тук… делу время.', 'Настрою дров на всю деревню!', 'Хорошая древесина, крепкая.',
    'Это дерево помнит ещё моего деда.', 'Ещё пара ударов — и готово.', 'Топор тупеет, а лес — нет.', 'Считаю: раз… два… ещё раз!',
    'Слушай, как гулко!', 'Дымом потом пахнуть будет — уют.', 'Лес густой, работы на месяц.', 'Ух, сучок попался упрямый.'],
  forage: ['Ягодки, сладкие как мёд!', 'Вот и кустик со спелыми ягодами.', 'Соберу-ка ягод на всех.',
    'Тёмные — самые сладкие, знаю.', 'Осторожно, ветки царапаются.', 'Птицы тоже сюда летят, конкурент.', 'Одну себе, остальные — в общий котёл.',
    'Кустик почти пустой, кто-то опередил.', 'Руки уже фиолетовые.', 'Тише идёшь — больше соберёшь.'],
  harvest: ['Пшеница созрела, урожай!', 'Хлеб будет!', 'Урожай удался на славу.', 'Колос к колосу — зима не страшна.',
    'Пахнет хлебом уже сейчас.', 'Жнецы мы нынче.', 'Снопы сами в руки просятся.'],
  eat: ['Ням… вот теперь можно и поработать.', 'Какая вкуснотища!', 'Сытый житель — счастливый житель.',
    'Ягоды — это хорошо, а вот мясо бы…', 'Ем — значит живу.', 'Косточка в зубах, а всё равно вкусно.', 'Не спеша, с чувством.',
    'Кажется, я недоедаю. Или мне кажется.', 'Вкуснее только чужая порция.', 'Ещё немного — и можно копать.'],
  sleep: ['Какая звёздная ночь…', 'Спать-спать-спать…', 'Завтра будет новый день.', 'Дым костра убаюкивает…',
    'Храп соседа громче волка.', 'Завтра встану до рассвета. Наверное.', 'Сон — маленькая смерть, а потом утро.', 'Спина болит, солома жесткая.',
    'Даже слаймы, наверное, спят.', 'Считаю слаймов… нет, лучше овец.', 'Тихо… только сверчки.', 'Кто там ходит?.. да нет, ветер.'],
  social: ['Сто лет не виделись!', 'Слышал, скоро новый дом строим?', 'Болтать у костра — лучшее время.',
    'А мне вчера такое приснилось…', 'Ну и как тебе новый камень?', 'Ты слышал? Волки опять у реки.', 'Сплетни — тоже работа.',
    'Только между нами…', 'Твоя кирка-то тупая, гляди.', 'Старики говорили, раньше трава была зеленее.', 'Сядь, расскажу про звёзды.',
    'А ты почему не спишь?'],
  deposit: ['Вклад в общее дело!', 'Дрова в общую кучу — так честно.', 'Склад пополнился — деревня дышит.',
    'Чтоб до зимы хватило.', 'Общее добро — оно такое.', 'Кто последний, тот и носил, ха.'],
  wander: ['Пойду посмотрю, что там.', 'Интересно, что за холмом?', 'Прогулка ещё никому не мешала.', 'Мир большой, надо всё обойти.',
    'Что-то там блеснуло…', 'Ноги сами ведут.', 'Земля под ногами — и та чужая, незнакомая.', 'Проверю, далеко ли вода.',
    'Ходить — самое честное дело.', 'Тропинку бы тут протоптать.', 'Кажется, я тут уже был. Или нет?'],
  idle: ['Сегодня хороший день.', 'Чем бы заняться?', 'Птички поют… красота.', 'Погода — само счастье.',
    'Посижу, мир посмотрю.', 'Ветер в траве шуршит…', 'Лениво, как кролик на солнце.', 'Топор бы наточить… потом.',
    'Облако на мамонта похоже.', 'Тихий день — хороший день.', 'Надо бы камень посчитать. Или не надо.',
    'Дым от костра ровный — к удаче.', 'Пятки чешутся — к дороге.', 'Интересно, куда уходит река.'],
  craft: ['Нужен топор — сделаю топор.', 'Хороший инструмент — половина дела.', 'Из камня и палки выйдет орудие!',
    'Камень требует терпения.', 'Сколько ни бей — сядет как надо.', 'Нож по пальцам — топор по бревну.', 'Геология — вторая натура.',
    'Вот это — изделие!', 'Вершина инженерной мысли… по местным меркам.'],
  mine: ['Камень — основа всех орудий.', 'Тяжёлый, но очень нужный.', 'Осторожно, пальцы!',
    'Карьер — наш хлеб… ну, камень.', 'Гранит! То-то будет скол.', 'Звон хороший — значит, крепкий.', 'Глубже — камень крепче.',
    'Комары тут наглые, как хозяева.', 'Ух, бахнул!','Пыль в глаза, а работа в радость.'],
  fight: ['За деревню!', 'А ну, тварь, отступай!', 'Не сегодня, слайма!', 'Костром клянусь, ты не пройдёшь!',
    'Их тут несколько… ну и пусть!', 'Копьё, не подведи!', 'Смотрите, как надо!', 'Ты желе желейное!', 'Кыш отсюда!',
    'За детей и за костёр!', 'Мне не страшно. Почти.'],
  flee: ['Спасайся кто может!', 'Отступаем!', 'Надо в укрытие!', 'Живым — значит, воюющим!', 'Не догонишь, студень!',
    'Костёр, укрой нас!', 'Бежать умею — не впервой!', 'Животное спасается умное.'],
  hunt: ['Тише… кролик близко.', 'Ужин сам бежит в руки.', 'Кролик, я всё вижу.', 'Ушки торчат — не спрячешься.',
    'Терпение… терпение…', 'Ты бы ещё прыжок сделал, беглец.'],
  greet: ['Новый человек! Надо познакомиться.', 'О, к нам пополнение!', 'Свежие руки — свежие дела.',
    'Наконец-то новые сплетни!', 'Стой, ты кто такой?', 'Путь долог? Присядь к костру.'],
  nightDream: ['Что там, за туманом?..', 'Звёзды… интересно, из чего они?', 'Если слаймы живут, то и драконы могут.',
    'Вот бы дом до неба…', 'Небо как шкура зверя, только дырявая.', 'Мне снилось море. Я его и не видел никогда.',
    'Слаймы из луны капают, точно вам говорю.', 'А вдруг мы не одни в мире?', 'Завтра придумаю колесо.', 'Луна — это чей-то костёр.',
    'Сны снятся только тем, кто спит на спине.'],
  child: ['Когда я вырасту, стану строителем!', 'Ух, большой мир!', 'Мама сказала не уходить далеко…',
    'А слаймов можно дрессировать?', 'Я тоже так умею! Почти.', 'Дайте мне топор! Ну пожа-а-алуйста!', 'Кролик — мой друг. Вчера.',
    'Взрослые всё время что-то рубят. Скучно.', 'Я нашёл жука! Теперь он мой.', 'Считаю до ста… сбился.']
};

// мысли по характерам — у каждого типа свой голос
const DESERT_THOUGHTS = [
  'Песок звенит под ногами, как стекло.', 'Солнце жжёт макушку. Терпи.', 'Хоть бы капля дождя… хоть одна.',
  'Кактус опять уколол палец. Но какой вкусный!', 'За дюной — мираж или вода? Проверю.', 'Ночью холодно, как в горах.',
  'Верблюд смотрит на меня с упрёком.', 'Ветер несёт песок прямо в глаза.', 'Наши дома из глины — самые крепкие.',
  'Оазис — это чудо, не иначе.', 'Тень от пальмы — как подарок.', 'Пустыня проверяет на прочность.'
];
const SWAMP_THOUGHTS = ['Хлюп… хлюп… ноги по колено в топи.', 'Комары сегодня злее волков.', 'Мангры держат землю — не утонем.', 'Туман над болотом, хоть факел бери.', 'В трясине что-то булькает. Не хочу знать что.', 'Камшиш хрустит под ногами.', 'Тут каждая тропа — на удачу.'];
const DARK_THOUGHTS = ['Лес такой густой — солнце не видно.', 'Тихо… слишком тихо.', 'Здесь грибы растут выше колена.', 'Ели давят со всех сторон.', 'В темноте между стволами кто-то смотрит.', 'Хорошо, что мы вместе.', 'Мрак кругом, а костёр — наш маяк.'];
const CHERRY_THOUGHTS = ['Лепестки летят, как снег вишнёвый.', 'Какая красота вокруг!', 'Пахнет мёдом и цветами.', 'Розовый вечер… сердце поёт.', 'Из этих деревьев выйдут самые красивые дома.', 'Пчёлы тут счастливее нас.'];
const SNOW_THOUGHTS = ['Шуба греет лучше любого костра.', 'Мех — валюта тундры.', 'Буран — к костру, это закон тундры.', 'Хрустит под ногами — только мой след.', 'Видишь пар от дыхания? Мы живы.', 'Ноги мёрзнут, но очаг ждёт.', 'За белой мглой — целая тундра.', 'Олени уводят нас за собой.', 'Снег засыпает все тропы. Идем по звёздам.', 'Мороз щиплет щёки — бодрит!'];
const BIOME_THOUGHTS = { 1: DESERT_THOUGHTS, 2: SWAMP_THOUGHTS, 3: DARK_THOUGHTS, 4: CHERRY_THOUGHTS, 5: SNOW_THOUGHTS };
const TRAIT_THOUGHTS = {
  hardworking: {
    chop: ['Даже отдыхая, я думаю о дровах.', 'Работа не волк… волк — в лесу, а работа — тут.'],
    mine: ['Ещё один камень — и можно не волноваться о зиме.', 'Труд — это честно.'],
    deposit: ['Склад полнее — сон крепче.', 'Порядок в куче — порядок в голове.'],
    idle: ['Стоять без дела — мучение.', 'Так и тянет что-нибудь починить.']
  },
  brave: {
    fight: ['Наконец-то настоящее дело!', 'Одно копьё — сто слаймов!', 'Не отступлю ни шагу!'],
    flee: ['Я не бегу — я тактически отвлекаю!', 'Прикрою вас, бегите!'],
    nightDream: ['Вот бы слайм побольше — было бы интересно.', 'Храбрость — это когда страшно, но идёшь.'],
    idle: ['Слишком тихо. Не доверяю я этой тишине.']
  },
  sociable: {
    social: ['Говорить — моя стихия!', 'Слушай, у меня столько новостей!', 'Давай болтать до рассвета?'],
    greet: ['Расскажи всё-всё-всё о себе!', 'Сводить знакомство надо правильно: у костра!'],
    idle: ['Скучно без разговора.', 'Кто бы пришёл поболтать…']
  },
  curious: {
    wander: ['А что если за той горой — другой мир?', 'Надо всё осмотреть и потрогать!'],
    mine: ['Интересно, а глубоко камень другого цвета?', 'Что если копать до центра земли?'],
    nightDream: ['Из чего сделаны слаймы? Надо бы поймать и изучить.', 'Кто-то же придумал каменные дома. Значит, и я смогу.'],
    idle: ['Земля тут другого оттенка… хм.', 'А кролики как видят в темноте?']
  },
  dreamer: {
    sleep: ['Луна подмигнула мне, кажется…', 'Сны — это бесплатно, а красиво.'],
    nightDream: ['Когда-нибудь мы построим город до звёзд.', 'Я вижу эту долину цветущей. Вижу!'],
    wander: ['Красиво тут… как в сказке, которую сам сочинил.'],
    idle: ['Вот бы дождь из ягод…', 'Ветер что-то шепчет. Надо вслушаться.']
  },
  kind: {
    eat: ['Как хорошо, когда все сыты.', 'Отдам половину малышне, если попросят.'],
    social: ['Как твои дела? Честно спрашиваю.', 'Тебе помочь? Мне не сложно.'],
    greet: ['Ночёвка у костра, еда — за мной!', 'Устал с дороги? Отдохни, я подежурю.'],
    flee: ['Сначала дети, потом я!', 'Помогите раненым, я подержу слайма!']
  }
};

// споры у костра — два взгляда на жизнь
const DISPUTES = [
  { a: 'Копать надо глубже — камень внизу крепче', b: 'Камень на поверхности лежит, зачем упарываться' },
  { a: 'Забор от слаймов обязателен', b: 'Дым костра их сам отпугивает, забор — трата дров' },
  { a: 'Детей ремеслу учить надо с трёх лет', b: 'Пусть сначала в игры играют, детство одно' },
  { a: 'Ягоды с северных кустов слаще', b: 'Все ягоды одинаковые, ты просто капризный' },
  { a: 'Новый дом ставить ближе к воде', b: 'Ближе к лесу — дрова важнее' },
  { a: 'Ночью дежурить надо по очереди', b: 'Все спать, слаймы к утру сами растают' },
  { a: 'Топор — главное изобретение человека', b: 'Копьё! Без копья ты слайму просто обед' },
  { a: 'Пшеницу сажать в три ряда', b: 'В четыре, места на поле хватит' },
  { a: 'Звёзды — это дырки в небе', b: 'Звёзды — костры великанов, очевидно' },
  { a: 'Волк опаснее слайма', b: 'Слайм хлеще: волк хоть убегает' },
  { a: 'Дождь — к удаче', b: 'К сырости и гнили в шалаше, вот к чему' },
  { a: 'Спать на земле полезно для спины', b: 'Вот поэтому ты с утра злюка' },
  { a: 'Малышей надо называть по их делам', b: 'По деду называть, так заведено испокон' },
  { a: 'Костёр нужно переносить на гору', b: 'В низине он теплее, все знают' }
];

function makeVillager(x, y) {
  const bodyIdx = Math.floor(rng() * spr.bodies.length);
  const usedNames = villagers.map(v => v.name);
  const freeNames = NAMES.filter(n => !usedNames.includes(n));
  const name = freeNames.length ? freeNames[Math.floor(rng() * freeNames.length)] : 'Житель ' + nextId;
  const pool = [...TRAITS];
  const traits = [];
  for (let i = 0; i < 2 && pool.length; i++)
    traits.push(pool.splice(Math.floor(rng() * pool.length), 1)[0]);
  return {
    id: nextId++, name, bodyIdx, traits,
    x, y, path: null, pathIdx: 0, facing: 1,
    state: 'idle', stateT: 0, workT: 0, targetObj: null, targetVil: null,
    carry: { wood: 0, berries: 0, stone: 0, fur: 0 },
    coat: false,
    needs: { hunger: 70 + rng() * 30, energy: 70 + rng() * 30, social: 50 + rng() * 40 },
    skill: { chop: 1, forage: 1, combat: 1 },
    hp: 20, tool: null, spear: false,
    isChild: false, growAt: 0, relP: Math.floor(rng() * 8), pregUntil: 0,
    thought: '', thoughtUntil: 0, thoughts: [],
    home: null, decideT: rng() * 2,
    threatT: 0, atkT: 0, fightId: 0, repathT: 0, huntId: 0,
    hostileP: 0, atkT2: 0
  };
}
function makeChild(a, b) {
  const v = makeVillager(a.x, a.y);
  v.name = 'Малыш ' + a.name[0] + (b.name[0] || '');
  v.traits = [a.traits[Math.floor(rng() * 2)], b.traits[Math.floor(rng() * 2)]];
  v.bodyIdx = rng() < 0.5 ? a.bodyIdx : b.bodyIdx;
  v.isChild = true;
  v.growAt = simTime + DAY_LEN * 1.2;
  v.skill = { chop: 0.4, forage: 0.4, combat: 0.4 };
  return v;
}

function makePlayerChild(v) {
  const c = makeChild(v, v);
  c.name = 'Малыш ' + ((P && P.name) || 'С')[0] + (v.name[0] || '');
  c.growAt = simTime + DAY_LEN * 1.4;
  return c;
}
function hasTrait(v, k) { return v.traits.some(t => t.k === k); }
function think(v, text) {
  v.thought = text;
  v.thoughtUntil = simTime + 5;
  v.thoughts.unshift({ t: simTime, text });
  if (v.thoughts.length > 8) v.thoughts.pop();
}

// ── A* ───────────────────────────────────────────────────────────
class Heap {
  constructor() { this.a = []; }
  push(n, f) { this.a.push({ n, f }); let i = this.a.length - 1; while (i > 0) { const p = (i - 1) >> 1; if (this.a[p].f <= this.a[i].f) break; const tmp = this.a[p]; this.a[p] = this.a[i]; this.a[i] = tmp; i = p; } }
  pop() { const top = this.a[0]; const last = this.a.pop(); if (this.a.length) { this.a[0] = last; let i = 0; for (;;) { const l = i * 2 + 1, r = l + 1; let m = i; if (l < this.a.length && this.a[l].f < this.a[m].f) m = l; if (r < this.a.length && this.a[r].f < this.a[m].f) m = r; if (m === i) break; const tmp = this.a[m]; this.a[m] = this.a[i]; this.a[i] = tmp; i = m; } } return top ? top.n : null; }
  get size() { return this.a.length; }
}
function astar(sx, sy, tx, ty) {
  if (!inb(tx, ty) || !walkable(tx, ty)) return null;
  sx = Math.floor(sx); sy = Math.floor(sy);
  if (sx === tx && sy === ty) return [];
  const open = new Heap();
  const g = new Map(), came = new Map();
  const startK = key(sx, sy);
  g.set(startK, 0);
  open.push({ x: sx, y: sy, k: startK }, 0);
  const closed = new Set();
  let iter = 0;
  while (open.size && iter++ < 4000) {
    const cur = open.pop();
    if (closed.has(cur.k)) continue;
    closed.add(cur.k);
    if (cur.x === tx && cur.y === ty) {
      const path = [];
      let k = cur.k;
      while (k !== startK) {
        path.push({ x: k % W, y: Math.floor(k / W) });
        k = came.get(k);
      }
      path.reverse();
      return path;
    }
    const cg = g.get(cur.k);
    for (const d of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const nx = cur.x + d[0], ny = cur.y + d[1];
      if (!walkable(nx, ny)) continue;
      const nk = key(nx, ny);
      if (closed.has(nk)) continue;
      const ng = (cg === undefined ? 0 : cg) + 1;
      if (ng < (g.has(nk) ? g.get(nk) : Infinity)) {
        g.set(nk, ng); came.set(nk, cur.k);
        open.push({ x: nx, y: ny, k: nk }, ng + Math.abs(nx - tx) + Math.abs(ny - ty));
      }
    }
  }
  return null;
}
function approachTile(v, ox, oy) {
  if (walkable(ox, oy)) return { x: ox, y: oy };
  let best = null, bd = Infinity;
  for (const d of [[0, -1], [0, 1], [-1, 0], [1, 0], [-1, -1], [1, -1], [-1, 1], [1, 1]]) {
    const x = ox + d[0], y = oy + d[1];
    if (!walkable(x, y)) continue;
    const dd = dist2(v.x, v.y, x, y);
    if (dd < bd) { bd = dd; best = { x, y }; }
  }
  return best;
}
function gotoObj(v, o) {
  const t = approachTile(v, o.x, o.y);
  if (!t) return false;
  v.path = astar(v.x, v.y, t.x, t.y);
  v.pathIdx = 0;
  return !!v.path || (Math.floor(v.x) === t.x && Math.floor(v.y) === t.y);
}
function findNearestObj(v, types, extra) {
  let best = null, bd = Infinity;
  for (const o of objects) {
    if (!types.includes(o.type)) continue;
    if (o.regrow > simTime) continue;
    if ((o.type === 'bush' || o.type === 'cactus' || o.type === 'reed' || o.type === 'mushroom') && o.depleted) continue;
    if (extra && !extra(o)) continue;
    const d = dist2(v.x, v.y, o.x, o.y);
    if (d < bd) { bd = d; best = o; }
  }
  return best;
}

// ── Время, погода ────────────────────────────────────────────────
function phase() { return (simTime % DAY_LEN) / DAY_LEN; }
function isNight() { const p = phase(); return p > 0.65 || p < 0.1; }
function nightAmount() {
  const p = phase();
  let n = 0;
  if (p > 0.58) n = Math.min(1, (p - 0.58) / 0.14);
  if (p < 0.2) n = Math.max(n, 1 - p / 0.2);
  return n;
}
function rainMult() { return weather.rain ? 2 : (weather.kind === 'snow' || weather.kind === 'fog') ? 1.5 : 1; }

// ── Решения ──────────────────────────────────────────────────────
function nearestMonster(v, range) {
  let best = null, bd = range * range;
  for (const m of monsters) {
    const d = dist2(m.x, m.y, v.x, v.y);
    if (d < bd) { bd = d; best = m; }
  }
  return best;
}
function decide(v) {
  const night = isNight();
  const n = v.needs;
  // 1. угроза — выжить важнее всего
  const threat = nearestMonster(v, v.isChild ? 7 : 5);
  if (threat) {
    const braveEnough = !v.isChild && (hasTrait(v, 'brave') ? v.hp > 8 : v.hp > 12 || v.spear);
    if (braveEnough) startFight(v, threat);
    else startFlee(v);
    return;
  }
  if (v.isChild) { decideChild(v, night, n); return; }
  // буран: выживание важнее работы — все к огню и под крыши
  if (worldClimate === 5 && weather.kind === 'blizzard' && v.state !== 'warm' && v.state !== 'goto_warm' && !isWarm(v)) { startWarm(v); return; }
  if (pendingBuild && !pendingBuild.assigned && !night) { startBuild(v); return; }
  if (n.hunger < 32) { startEat(v); return; }
  if (n.energy < 22 || (night && n.energy < 70)) { startSleep(v); return; }
  if (tryLlmDesire(v)) return;
  if (v.carry.wood + v.carry.berries + v.carry.stone >= 6) { startDeposit(v); return; }
  if (n.social < 30 && !night) {
    const partner = villagers.find(o => o !== v && o !== v.targetVil && !['sleep', 'social', 'flee', 'hide'].includes(o.state) && o.needs.social < 60);
    if (partner) { startSocial(v, partner); return; }
  }
  // ферма созрела — урожай важнее всего из работы
  const readyFarm = stocks.berries < 100 ? farms.find(f => f.stage >= 3) : null;
  if (readyFarm && !night) { startHarvest(v, readyFarm); return; }
  // еда кончается — фуражируем / охотимся
  if (stocks.berries < 8 && !night) {
    const b = findNearestObj(v, ['bush', 'cactus', 'reed', 'mushroom']);
    if (b) { startForage(v, b); return; }
    const rb = nearestAnimal(v, 'rabbit', 9) || (worldClimate === 1 ? nearestAnimal(v, 'camel', 12) : null) || (worldClimate === 5 ? nearestAnimal(v, 'deer', 12) : null);
    if (rb) { startHunt(v, rb); return; }
  }
  // северная деревня: каждому — шуба
  if (worldClimate === 5 && !night && !v.isChild) {
    if (!v.coat && (stocks.fur || 0) >= 3 && stocks.wood >= 2) { startCraft(v, 'coat'); return; }
    if ((stocks.fur || 0) < 3 && villagers.some(o => !o.coat && !o.isChild)) {
      const bg = nearestAnimal(v, 'deer', 16) || nearestAnimal(v, 'wolf', 12);
      if (bg) { startHunt(v, bg); return; }
    }
  }
  // орудия труда: каменный топор = палка + камень.
  // Порядок: дрова → камень → крафт. Карьер — только когда дерево уже есть.
  if (!v.tool && !night) {
    const woodNow = stocks.wood + v.carry.wood;
    const stoneNow = stocks.stone + v.carry.stone;
    if (woodNow >= 3 && stoneNow >= 2) { startCraft(v, 'axe'); return; }
    if (woodNow >= 3 && stoneNow < 2) {
      const st = findNearestObj(v, ['stone']);
      if (st) { startMine(v, st); return; }
      // камня нет вовсе — рубим без инструмента
    }
  }
  // перед ночной войной — копьё
  if (night && monsters.length > 0 && !v.spear && stocks.wood >= 4 && stocks.stone >= 3) {
    startCraft(v, 'spear');
    return;
  }
  // камень нужен для эпохи каменных домов
  if (era() >= 3 && stocks.stone + v.carry.stone < 24 && !night) {
    const st = findNearestObj(v, ['stone']);
    if (st) { startMine(v, st); return; }
  }
  const t = stocks.wood < 400 ? findNearestObj(v, ['tree', 'pine', 'acacia', 'mangrove', 'deadtree', 'darkpine', 'cherry']) : null;
  if (t && !night) { startChop(v, t); return; }
  if (!t && !night && stocks.wood >= 400 && rng() < 0.2) think(v, 'Дров на складе выше крыши — можно и отдохнуть.');
  if (night && hasTrait(v, 'dreamer') && rng() < 0.5) { think(v, pickThought(v, 'nightDream')); startWander(v); return; }
  startWander(v);
}
function decideChild(v, night, n) {
  if (worldClimate === 5 && weather.kind === 'blizzard' && !isWarm(v) && v.state !== 'warm' && v.state !== 'goto_warm') { startWarm(v); return; }
  if (n.hunger < 35) { startEat(v); return; }
  if (n.energy < 30 || night) { startSleep(v); return; }
  if (v.carry.berries > 0) { startDeposit(v); return; }
  const b = findNearestObj(v, ['bush', 'cactus', 'reed', 'mushroom']);
  if (b && !night) { startForage(v, b); return; }
  if (rng() < 0.3) think(v, pickThought(v, 'child'));
  startWander(v);
}
function pick(arr) { return arr[Math.floor(rng() * arr.length)]; }
function pickThought(v, key) {
  const base = THOUGHTS[key];
  const bth = BIOME_THOUGHTS[worldClimate];
  if (bth && rng() < 0.3) return pick(bth);
  if (v && v.traits && rng() < 0.4) {
    for (const t of v.traits) {
      const pool = (TRAIT_THOUGHTS[t.k] || {})[key];
      if (pool) return pick(pool);
    }
  }
  return base ? pick(base) : '…';
}

function startChop(v, o) {
  if (!gotoObj(v, o)) { startWander(v); return; }
  v.state = 'goto_chop'; v.targetObj = o;
  think(v, pickThought(v, 'chop'));
}
function startForage(v, o) {
  if (!gotoObj(v, o)) { startWander(v); return; }
  v.state = 'goto_forage'; v.targetObj = o;
  think(v, pickThought(v, 'forage'));
}
function startHarvest(v, o) {
  if (!gotoObj(v, o)) { startWander(v); return; }
  v.state = 'goto_harvest'; v.targetObj = o;
  think(v, pickThought(v, 'harvest'));
}
function startHunt(v, a) {
  v.state = 'hunt'; v.huntId = a.id; v.workT = 12;
  think(v, pickThought(v, 'hunt'));
}
function startMine(v, o) {
  if (!gotoObj(v, o)) { startWander(v); return; }
  v.state = 'goto_mine'; v.targetObj = o;
  think(v, pickThought(v, 'mine'));
}
function startCraft(v, kind) {
  const t = approachTile(v, campfire.x, campfire.y) || { x: campfire.x, y: campfire.y + 1 };
  v.path = astar(v.x, v.y, t.x, t.y); v.pathIdx = 0;
  v.state = 'goto_craft'; v.craftKind = kind;
  think(v, pickThought(v, 'craft'));
}
function startDeposit(v) {
  const t = approachTile(v, campfire.x, campfire.y) || { x: campfire.x, y: campfire.y + 1 };
  v.path = astar(v.x, v.y, t.x, t.y); v.pathIdx = 0;
  v.state = 'goto_deposit';
  think(v, pickThought(v, 'deposit'));
}
function startEat(v) {
  if (stocks.berries > 0) {
    const t = approachTile(v, campfire.x, campfire.y) || { x: campfire.x, y: campfire.y + 1 };
    v.path = astar(v.x, v.y, t.x, t.y); v.pathIdx = 0;
    v.state = 'goto_eat';
    think(v, 'Проголодался… пойду к костру.');
  } else {
    const b = findNearestObj(v, ['bush', 'cactus', 'reed', 'mushroom']);
    if (b) { startForage(v, b); v.eatIntent = true; }
    else {
      let rb = nearestAnimal(v, 'rabbit', 10);
      if (!rb && (worldClimate === 1 || worldClimate === 5) && !v.isChild) rb = nearestAnimal(v, worldClimate === 1 ? 'camel' : 'deer', 12);
      if (rb && !v.isChild) { startHunt(v, rb); v.eatIntent = true; }
      else { v.state = 'idle'; v.decideT = 3; think(v, 'В деревне пусто… надо искать еду.'); }
    }
  }
}
function startSleep(v) {
  const hm = homes(); const home = hm.length ? hm[v.id % hm.length] : campfire;
  v.sleepHome = home;
  const t = approachTile(v, home.x, home.y) || { x: home.x, y: home.y + 1 };
  v.path = astar(v.x, v.y, t.x, t.y); v.pathIdx = 0;
  v.state = 'goto_sleep';
  think(v, pickThought(v, 'sleep'));
}
function startSocial(v, partner) {
  v.state = 'goto_social'; v.targetVil = partner;
  if (partner.state === 'idle' || partner.state === 'wander') {
    partner.state = 'goto_social'; partner.targetVil = v;
  }
  think(v, pickThought(v, 'social'));
}
function startWander(v) {
  const blz = worldClimate === 5 && weather.kind === 'blizzard';
  for (let tries = 0; tries < 10; tries++) {
    let x, y;
    if (blz) { // в буран гуляем только вокруг костра
      const a = rng() * Math.PI * 2, r2 = 1 + rng() * 2;
      x = Math.floor(campfire.x + Math.cos(a) * r2); y = Math.floor(campfire.y + Math.sin(a) * r2);
    } else { x = Math.floor(v.x + (rng() * 21) - 10); y = Math.floor(v.y + (rng() * 21) - 10); }
    if (walkable(x, y)) {
      const p = astar(v.x, v.y, x, y);
      if (p) { v.path = p; v.pathIdx = 0; v.state = 'wander'; think(v, pickThought(v, 'wander')); return; }
    }
  }
  v.state = 'idle'; v.decideT = 1 + rng() * 2;
  if (rng() < 0.4) think(v, pickThought(v, 'idle'));
}
function startBuild(v) {
  pendingBuild.assigned = v; pendingBuild.at = simTime;
  v.path = astar(v.x, v.y, pendingBuild.x, pendingBuild.y); v.pathIdx = 0;
  v.state = 'goto_build';
  think(v, pendingBuild.kind === 'farm' ? 'Вспашу поле — хлеб сам себя не посадит!' : 'Строим новый дом! За работу.');
}
function startFight(v, m) {
  v.state = 'fight'; v.fightId = m.id; v.repathT = 0;
  think(v, pickThought(v, 'fight'));
}
function isWarm(v) {
  if (dist(v.x, v.y, campfire.x, campfire.y) < 3.5) return true;
  return homes().some(h => Math.abs(Math.floor(v.x) - h.x) <= 1 && Math.abs(Math.floor(v.y) - h.y) <= 1);
}
function startWarm(v) {
  const t = approachTile(v, campfire.x, campfire.y) || { x: campfire.x, y: campfire.y + 1 };
  v.path = astar(v.x, v.y, t.x, t.y);
  v.pathIdx = 0;
  v.state = 'goto_warm';
  if (rng() < 0.6) think(v, pick(['Буран! Бегом к костру!', 'Все к огню — иначе замёрзнем!', 'Домой, к теплу!', 'Снег залепляет глаза — к огню!']));
}
function startFlee(v) {
  const hm = homes(); const home = hm.length ? hm[v.id % hm.length] : campfire;
  const t = approachTile(v, home.x, home.y) || { x: home.x, y: home.y + 1 };
  v.path = astar(v.x, v.y, t.x, t.y); v.pathIdx = 0;
  v.state = 'flee';
  think(v, pickThought(v, 'flee'));
}
function nearestAnimal(v, kind, range) {
  let best = null, bd = range * range;
  for (const a of animals) {
    if (a.kind !== kind || a.hp <= 0) continue;
    const d = dist2(a.x, a.y, v.x, v.y);
    if (d < bd) { bd = d; best = a; }
  }
  return best;
}

// ── Симуляция ────────────────────────────────────────────────────
function updateSim(dt) {
  simTime += dt;
  const p = phase();
  // погода
  weather.t -= dt;
  if (weather.t <= 0) {
    let kind = 'clear';
    const r = rng();
    if (worldClimate === 5) kind = r < 0.5 ? 'snow' : (r < 0.68 ? 'blizzard' : 'clear');
    else if (worldClimate === 2) kind = r < 0.38 ? 'fog' : (r < 0.56 ? 'rain' : 'clear');
    else if (worldClimate === 4) kind = r < 0.35 ? 'petals' : 'clear';
    else kind = r < 0.45 ? 'rain' : 'clear';
    if (kind === 'clear') weather.t = 60 + rng() * 140;
    else weather.t = 40 + rng() * 60;
    if (kind !== weather.kind) {
      const MSG = {
        rain: ['🌧', 'Пошёл дождь. Растения растут быстрее!'],
        snow: ['❄', 'Пошёл снегопад. Мир замело белым пухом.'],
        blizzard: ['🌨', 'Метель бьёт в стены хижин! Ветер рвёт крыши.'],
        fog: ['🌫', 'С топей ползёт туман — ни зги не видно.'],
        petals: ['🌸', 'Лепестки вишни летят по всей роще.']
      }[kind];
      if (MSG) logEvent(MSG[0], MSG[1]);
    }
    weather.kind = kind;
    weather.rain = kind === 'rain';
  }
  if (weather.kind === 'rain' && rng() < 0.002) {
    weather.bolt = 0.4;
    if (rng() < 0.3) logEvent('⚡', 'Гром гремит по холмам!');
  }
  if (weather.bolt > 0) weather.bolt = Math.max(0, weather.bolt - dt);

  // фазы суток
  if (lastPhase < 0.65 && p >= 0.65) onNightfall();
  if (lastPhase < 0.12 && p >= 0.12) onMorning();
  lastPhase = p;

  // появление новых жителей по нарубленному
  if (settlersSpawned < settlersThresholds.length &&
      totalWood >= settlersThresholds[settlersSpawned] && !isNight()) {
    arriveSettler();
  }

  tryPlanBuild();
  const er = era();
  if (er !== lastEra) {
    lastEra = er;
    logEvent('🏆', `Деревня перешла в новую эпоху: «${ERAS[er]}»!`);
  }

  // игрок режима «Жизнь»
  if (mode === 'life') updatePlayer(dt);

  // жители (в режиме жизни враждебные тебе обходят свой AI)
  for (const v of [...villagers]) {
    if (mode === 'life' && P && !P.dead && v.hostileP > 0) { updateHostileVillager(v, dt); continue; }
    updateVillager(v, dt);
  }
  // животные
  for (const a of [...animals]) updateAnimal(a, dt);
  // монстры
  for (const m of [...monsters]) updateMonster(m, dt);

  // регенерация
  for (const o of objects) {
    if ((o.type === 'bush' || o.type === 'cactus' || o.type === 'reed' || o.type === 'mushroom') && o.depleted && o.regrowAt && simTime >= o.regrowAt) {
      o.depleted = false; o.regrowAt = 0;
    }
  }
  processRegrow();
  // рост пшеницы
  for (const f of farms) {
    if (f.stage < 3 && simTime >= f.growAt) {
      f.stage++;
      f.growAt = simTime + 60 / rainMult();
    }
  }
}

function onNightfall() {
  const day = Math.floor(simTime / DAY_LEN) + 1;
  if (day < 3) {
    logEvent('🌙', 'Ночь спокойная… пока.');
    for (const v of villagers) if (hasTrait(v, 'dreamer')) think(v, pickThought(v, 'nightDream'));
    return;
  }
  const count = Math.min(3, Math.ceil(villagers.length / 4) + (day > 6 ? 1 : 0));
  for (let i = 0; i < count; i++) {
    const p = randWalkable(22);
    monsters.push({
      id: nextId++, kind: 'slime', x: p.x, y: p.y,
      hp: 10 + Math.min(8, day), maxHp: 10 + Math.min(8, day), dmg: 2 + Math.min(3, Math.floor(day / 4)),
      state: 'wander', t: 0, targetId: 0, atkT: 0, facing: 1, animT: 0
    });
  }
  SIM.monsterWaves += count;
  logEvent('👾', `Ночь. Из тьмы выползли слаймы (${count})!`);
  if (rng() < 0.4) logEvent('🐺', 'Волки воют в лесу…');
  for (const v of villagers)
    if (hasTrait(v, 'dreamer') && v.state !== 'sleep') think(v, pickThought(v, 'nightDream'));
}

function onMorning() {
  saveGame(); // автосохранение каждый рассвет
  // дети растут
  for (const v of [...villagers]) {
    if (v.isChild && simTime >= v.growAt) {
      v.isChild = false;
      v.name = v.name.replace('Малыш ', '');
      logEvent('🧒', `${v.name} вырос и теперь полноправный житель!`);
    }
  }
  // пополнение природы
  let rabbits = animals.filter(a => a.kind === 'rabbit' && a.hp > 0).length;
  if (rabbits < 8) {
    const p = randWalkable(8);
    animals.push({ id: nextId++, kind: 'rabbit', x: p.x, y: p.y, hp: 5, state: 'idle', t: 1, dirX: 0, dirY: 0, facing: 1, animT: 0 });
  }
  const wildKind = worldClimate === 1 ? 'camel' : worldClimate === 5 ? 'deer' : null;
  if (wildKind) {
    const wildTarget = worldClimate === 1 ? 4 : 6;
    const wilds = animals.filter(a => a.kind === wildKind && a.hp > 0).length;
    if (wilds < wildTarget) {
      const p = randWalkable(20);
      animals.push({ id: nextId++, kind: wildKind, x: p.x, y: p.y, hp: worldClimate === 1 ? 16 : 14, state: 'idle', t: rng() * 3, dirX: 0, dirY: 0, facing: 1, animT: 0, preyId: 0 });
    }
  }
  const wolves = animals.filter(a => a.kind === 'wolf' && a.hp > 0).length;
  if (wolves < 2) {
    const p = randWalkable(14);
    animals.push({ id: nextId++, kind: 'wolf', x: p.x, y: p.y, hp: 12, state: 'idle', t: rng() * 3, dirX: 0, dirY: 0, facing: 1, animT: 0, preyId: 0 });
  }
  // рождение: еда есть, дома есть, любовь есть
  const adults = villagers.filter(v => !v.isChild);
  if (adults.length >= 2 && stocks.berries >= 12 && beds() >= 4 && era() >= 2 && rng() < 0.65 && villagers.length < 16) {
    const a = adults[Math.floor(rng() * adults.length)];
    let b = adults[Math.floor(rng() * adults.length)];
    if (b === a) b = adults[(adults.indexOf(a) + 1) % adults.length];
    const child = makeChild(a, b);
    villagers.push(child);
    stocks.berries -= 10;
    SIM.births++;
    think(a, 'У нас родился малыш!');
    logEvent('👶', `У ${a.name} и ${b.name} родился ребёнок! Деревня растёт.`);
  }
  // подселение после потерь
  if (villagers.length === 0) { arriveSettler(); if (villagers.length === 0) arriveSettler(); }
  else if (villagers.length * 2 < beds() + 2 && rng() < 0.3) arriveSettler();
  let stonesTo = 6 - cnt('stone');
  while (stonesTo > 0 && rng() < 0.65) {
    const p = randWalkable(9);
    addObject('stone', Math.floor(p.x), Math.floor(p.y));
    stonesTo--;
  }
}

function arriveSettler() {
  let sx = -1, sy = -1;
  for (let tries = 0; tries < 200; tries++) {
    const x = Math.floor(rng() * W), y = rng() < 0.5 ? 1 : H - 2;
    if (walkable(x, y)) { sx = x; sy = y; break; }
  }
  if (sx >= 0) {
    const nv = makeVillager(sx + 0.5, sy + 0.5);
    nv.state = 'goto_camp';
    nv.path = astar(sx, sy, campfire.x, campfire.y); nv.pathIdx = 0;
    villagers.push(nv);
    think(nv, 'Говорят, тут хорошие люди живут.');
    logEvent('🎉', `${nv.name} пришёл в деревню! Теперь нас ${villagers.length}.`);
    settlersSpawned++;
    for (const v of villagers)
      if (v !== nv && hasTrait(v, 'curious')) think(v, pickThought(v, 'greet'));
  }
}

function tryPlanBuild() {
  if (pendingBuild) {
    // сторожевой пёс: план, который никто не строит, снимаем или отменяем
    if (pendingBuild.at === undefined) pendingBuild.at = simTime;
    const a = pendingBuild.assigned;
    if (a && (a.hp <= 0 || (simTime - pendingBuild.at > 40 && !['build', 'goto_build'].includes(a.state)))) {
      pendingBuild.assigned = null; pendingBuild.at = simTime;
      logEvent('📐', 'Стройка стоит без мастера — деревня ищет другого строителя.');
    }
    if (!pendingBuild.assigned && simTime - pendingBuild.at > 90) {
      stocks.wood += (pendingBuild.wood || 0); stocks.stone += (pendingBuild.stone || 0);
      logEvent('📐', 'Деревня отложила стройку — материалы вернулись на склад.');
      pendingBuild = null;
    }
    if (pendingBuild) return;
  }
  if (isNight()) return;
  const e = era();
  const bedsNow = beds();
  const pop = villagers.length;
  let plan = null;
  if (bedsNow < pop + 1) {
    if (e >= 3 && stocks.wood >= 50 && stocks.stone >= 10 && cnt('house') < 5) plan = { kind: 'house', wood: 50, stone: 10 };
    else if (e >= 2 && stocks.wood >= 25 && cnt('hut') < 8) plan = { kind: 'hut', wood: 25 };
    else if (stocks.wood >= 10 && cnt('shelter') < 6) plan = { kind: 'shelter', wood: 10 };
  } else if (e >= 3 && stocks.berries < 25 && farms.length < 4 && stocks.wood >= 15) {
    plan = { kind: 'farm', wood: 15 };
  }
  if (!plan) return;
  const spot = findBuildSpot(plan.kind);
  if (!spot) return;
  stocks.wood -= plan.wood;
  if (plan.stone) stocks.stone -= plan.stone;
  pendingBuild = { kind: plan.kind, x: spot.x, y: spot.y, assigned: null, wood: plan.wood, stone: plan.stone || 0, at: simTime };
  const names = { shelter: 'шалаш 🏕', hut: 'хижину 🏠', house: 'настоящий дом 🏡', farm: 'поле 🌾' };
  logEvent('📐', `Деревня планирует строить: ${names[plan.kind]}. Материалы выделены.`);
}

function findBuildSpot(kind) {
  for (let r = 2; r <= 7; r++) {
    for (let a = 0; a < 24; a++) {
      const ang = a / 24 * Math.PI * 2;
      const x = Math.round(campfire.x + Math.cos(ang) * r);
      const y = Math.round(campfire.y + Math.sin(ang) * r);
      if (kind === 'farm') {
        if (walkable(x, y) && walkable(x + 1, y) && dist2(x, y, campfire.x, campfire.y) >= 9) return { x, y };
      } else {
        if (walkable(x, y) && walkable(x, y + 1) && dist2(x, y, campfire.x, campfire.y) >= 4) return { x, y };
      }
    }
  }
  return null;
}

// прямолинейное движение со скольжением вдоль препятствий
function steer(e, tx, ty, speed, dt) {
  const dx = tx - e.x, dy = ty - e.y;
  const d = Math.hypot(dx, dy) || 1;
  if (dx !== 0) e.facing = dx > 0 ? 1 : -1;
  const nx = e.x + dx / d * speed * dt, ny = e.y + dy / d * speed * dt;
  if (walkable(Math.floor(nx), Math.floor(e.y))) e.x = nx;
  if (walkable(Math.floor(e.x), Math.floor(ny))) e.y = ny;
  return d;
}

function updateAnimal(a, dt) {
  if (a.hp <= 0) return;
  a.t -= dt;
  a.animT += dt;
  if (a.kind === 'rabbit') {
    // паника от хищника/охотника
    let threat = null, td = 5 * 5;
    for (const w of animals) if (w.kind === 'wolf' && w.hp > 0) {
      const d = dist2(w.x, w.y, a.x, a.y);
      if (d < td) { td = d; threat = w; }
    }
    for (const v of villagers) {
      if (v.huntId && v.state === 'hunt') {
        const d = dist2(v.x, v.y, a.x, a.y);
        if (d < td) { td = d; threat = v; }
      }
    }
    if (mode === 'life' && P && !P.dead && !P.asleep) {
      const d = dist2(P.x, P.y, a.x, a.y);
      if (d < 3 * 3 && d < td) { td = d; threat = P; }
    }
    if (threat) {
      const away = { x: a.x + (a.x - threat.x) * 2, y: a.y + (a.y - threat.y) * 2 };
      steer(a, away.x, away.y, 5.5, dt);
      a.state = 'flee';
      return;
    }
    a.state = 'idle';
    if (a.t <= 0) {
      a.t = 0.8 + rng() * 1.5;
      a.dirX = a.x + (rng() * 6 - 3);
      a.dirY = a.y + (rng() * 6 - 3);
    }
    steer(a, a.dirX, a.dirY, 2.2, dt);
  } else if (a.kind === 'camel' || a.kind === 'deer') {
    a.state = 'idle';
    if (a.t <= 0) {
      a.t = 2 + rng() * 4;
      a.dirX = a.x + (rng() * 10 - 5);
      a.dirY = a.y + (rng() * 10 - 5);
    }
    steer(a, a.dirX, a.dirY, a.kind === 'deer' ? 1.5 : 1.1, dt);
  } else if (a.kind === 'wolf') {
    if (mode === 'life' && P && !P.dead && a.hostileP > 0) {
      a.hostileP -= dt;
      if (P.asleep) { P.asleep = false; logEvent('🐺', 'Волк разбудил тебя рычанием!'); }
      const d7 = dist(a.x, a.y, P.x, P.y);
      if (d7 < 9) {
        const d = steer(a, P.x, P.y, 2.4, dt);
        if (d < 1.1) {
          a.atkT2 = (a.atkT2 || 0) - dt;
          if (a.atkT2 <= 0) {
            a.atkT2 = 1.4;
            P.hp -= 3.5;
            lifeBubble('Волк кусает! Отбивайся или беги!');
            if (P.hp <= 0) playerDie('Тебя загрыз волк');
          }
        }
      }
      return;
    }
    // охота на кролика
    if (a.preyId) {
      const prey = animals.find(x => x.id === a.preyId && x.hp > 0);
      if (!prey) { a.preyId = 0; a.state = 'idle'; a.t = 2; }
      else {
        const d = steer(a, prey.x, prey.y, 3.4, dt);
        if (d < 0.8) {
          prey.hp = 0;
          a.preyId = 0; a.state = 'idle'; a.t = 6;
          if (rng() < 0.3) logEvent('🐺', 'Волк поймал кролика. Такова природа.');
        }
        return;
      }
    } else {
      if (a.t <= 0) {
        a.t = 2 + rng() * 3;
        let prey = null, bd = 7 * 7;
        for (const rb of animals) {
          if (rb.kind !== 'rabbit' || rb.hp <= 0) continue;
          const d = dist2(rb.x, rb.y, a.x, a.y);
          if (d < bd) { bd = d; prey = rb; }
        }
        if (prey) a.preyId = prey.id;
        else { a.dirX = a.x + (rng() * 10 - 5); a.dirY = a.y + (rng() * 10 - 5); }
      }
      if (a.state !== 'idle' || true) steer(a, a.dirX || a.x, a.dirY || a.y, 0.9, dt);
    }
  }
}

function updateMonster(m, dt) {
  m.animT += dt;
  // на солнце слаймы тают
  if (!isNight()) {
    m.hp -= 10 * dt;
    if (m.hp <= 0) {
      killMonster(m, 'растаял на солнце');
      return;
    }
  }
  // цель: ближайший житель (кроме спрятавшихся)
  let target = null, bd = 9 * 9;
  for (const v of villagers) {
    if (v.state === 'hide') continue;
    const d = dist2(v.x, v.y, m.x, m.y);
    if (d < bd) { bd = d; target = v; }
  }
  if (mode === 'life' && P && !P.dead && !P.asleep) {
    const d = dist2(P.x, P.y, m.x, m.y);
    if (d < bd) { bd = d; target = P; }
  }
  if (target) {
    const d = steer(m, target.x, target.y, 1.55, dt);
    if (d < 1.15) {
      m.atkT -= dt;
      if (m.atkT <= 0) {
        m.atkT = 1.45;
        if (target === P) {
          P.hp -= m.dmg;
          lifeBubble('Слайма кусает тебя! Бей кулаками или оружием!');
          if (P.hp <= 0) playerDie('Тебя растворила слайма');
          return;
        }
        target.hp -= m.dmg;
        if (rng() < 0.3) think(target, 'Ай! Эта тварь кусается!');
        // шум боя будит спящих рядом — деревня обороняется толпой
        for (const w of villagers) {
          if (dist(w.x, w.y, target.x, target.y) < 11) {
            if (w.state === 'sleep') { w.path = null; decide(w); }
            else if (w.state === 'idle' || w.state === 'goto_sleep') { decide(w); }
          }
        }
        if (target.hp <= 0) killVillager(target, m);
      }
    }
  } else {
    // бредут к деревне
    m.t -= dt;
    if (m.t <= 0) {
      m.t = 3 + rng() * 3;
      m.dirX = campfire.x + (rng() * 16 - 8);
      m.dirY = campfire.y + (rng() * 16 - 8);
    }
    steer(m, m.dirX, m.dirY, 0.7, dt);
  }
}

function killMonster(m, how) {
  const i = monsters.indexOf(m);
  if (i >= 0) monsters.splice(i, 1);
  if (how === 'растаял на солнце') SIM.melted = (SIM.melted || 0) + 1;
  else SIM.monsterKills++;
  if (how === 'растаял на солнце') {
    if (rng() < 0.3) logEvent('☀️', 'Слайма растаяла под лучами солнца.');
  } else {
    logEvent('⚔️', `Слайма побеждена (${how})!`);
  }
}
function killVillager(v, by) {
  const i = villagers.indexOf(v);
  if (i >= 0) villagers.splice(i, 1);
  if (selected === v) selected = null;
  addObject('grave', Math.floor(v.x), Math.floor(v.y));
  SIM.deaths++;
  if (by === 'player') logEvent('💀', `${v.name} убит. Могила молчаливо ждёт ответа.`);
  else if (by === 'cold') logEvent('🥶', `${v.name} не дошёл${v.isChild ? '' : (v.gender === 'f' ? 'а' : '')} до огня и замёрз${v.gender === 'f' ? 'ла' : ''} в буран. Деревня скорбит…`);
  else logEvent('😢', `${v.name} погиб${v.isChild ? '' : ' как герой'}, защищая деревню. Деревня скорбит…`);
}

function updateVillager(v, dt) {
  // мороз в буран: кто не у огня и не в доме — замерзает
  if (worldClimate === 5 && weather.kind === 'blizzard' && !v.isChild) {
    if (!isWarm(v) && !v.coat) {
      v.hp -= 0.05 * dt;
      if (v.hp <= 0) { killVillager(v, 'cold'); return; }
    }
  }
  const n = v.needs;
  const working = ['chop', 'forage', 'goto_chop', 'goto_forage', 'goto_build', 'build', 'goto_harvest', 'harvest'].includes(v.state);
  n.hunger = Math.max(0, n.hunger - dt * 0.09);
  n.energy = Math.max(0, n.energy - dt * (working ? 0.055 : v.state === 'sleep' ? -0.14 : 0.03));
  n.social = Math.max(0, n.social - dt * (v.state === 'social' ? -0.2 : 0.035));
  if (n.hunger < 12) n.energy = Math.max(0, n.energy - dt * 0.05);
  // реген HP
  if (v.state === 'sleep' || v.state === 'eat') v.hp = Math.min(20, v.hp + 0.8 * dt);
  else if (v.state === 'idle' && dist(v.x, v.y, campfire.x, campfire.y) < 3) v.hp = Math.min(20, v.hp + 0.3 * dt);

  // угроза каждые полсекунды — прерывает всё
  v.threatT -= dt;
  if (v.threatT <= 0 && !['fight', 'flee'].includes(v.state)) {
    v.threatT = 0.5;
    const threat = nearestMonster(v, v.isChild ? 7 : 4.5);
    if (threat) {
      v.path = null;
      decide(v);
      return;
    }
  }

  if (v.state === 'sleep') {
    // тревога будит: слайма рядом — просыпаемся и действуем
    const threat = nearestMonster(v, 5);
    if (threat) {
      v.path = null;
      decide(v);
      return;
    }
    if ((phase() < 0.5 && !isNight()) || n.hunger < 15) {
      v.state = 'idle'; v.decideT = 0.5;
      think(v, 'Доброе утро!');
    }
    return;
  }

  // движение по пути
  if (v.path && v.pathIdx < v.path.length) {
    const node = v.path[v.pathIdx];
    const tx = node.x + 0.5, ty = node.y + 0.5;
    const dx = tx - v.x, dy = ty - v.y;
    const d = Math.hypot(dx, dy);
    const sp = (v.isChild ? 2.4 : 3.1) * dt;
    if (d <= sp) { v.x = tx; v.y = ty; v.pathIdx++; }
    else {
      v.x += dx / d * sp; v.y += dy / d * sp;
      if (dx !== 0) v.facing = dx > 0 ? 1 : -1;
    }
    v.animT += dt;
    return;
  }
  v.path = null;

  switch (v.state) {
    case 'goto_chop': {
      const o = v.targetObj;
      if (!o || o.regrow > 0) { v.state = 'idle'; v.decideT = 0.3; break; }
      v.state = 'chop'; v.workT = Math.max(1.4, (3.2 - v.skill.chop * 0.4) / (v.tool === 'axe' ? 1.6 : 1));
      break;
    }
    case 'chop': {
      v.workT -= dt;
      if (v.workT <= 0) {
        const o = v.targetObj;
        if (o && o.regrow === 0) {
          removeObject(o);
          addObject('stump', o.x, o.y);
          regrowQueue.push({ x: o.x, y: o.y, at: simTime + 2 * DAY_LEN / rainMult() });
          v.carry.wood += Math.ceil(4 * v.skill.chop);
          v.skill.chop = Math.min(3, v.skill.chop + 0.06);
          totalWood += 3;
          logEvent('🪓', `${v.name} срубил дерево (+4 🪵${v.tool === 'axe' ? ' топором' : ''})`);
          if (hasTrait(v, 'hardworking') && rng() < 0.4) think(v, 'Работать так работать! Ещё одно!');
        }
        v.targetObj = null; v.state = 'idle'; v.decideT = 0.4 + rng() * 1.2;
      }
      break;
    }
    case 'goto_forage': {
      const o = v.targetObj;
      if (!o || o.depleted) { v.state = 'idle'; v.decideT = 0.3; break; }
      v.state = 'forage'; v.workT = 3;
      break;
    }
    case 'forage': {
      v.workT -= dt;
      if (v.workT <= 0) {
        const o = v.targetObj;
        if (o && !o.depleted) {
          o.depleted = true;
          o.regrowAt = simTime + (90 + rng() * 60) / rainMult();
          v.carry.berries += 2;
          v.skill.forage = Math.min(3, v.skill.forage + 0.05);
          if (v.eatIntent) {
            v.eatIntent = false;
            v.carry.berries = Math.max(0, v.carry.berries - 1);
            v.needs.hunger = Math.min(100, v.needs.hunger + 45);
            think(v, pickThought(v, 'eat'));
          }
          logEvent('🍓', `${v.name} собрал ягоды (+2 🫐)`);
        }
        v.targetObj = null; v.state = 'idle'; v.decideT = 0.4 + rng();
      }
      break;
    }
    case 'goto_harvest': {
      const o = v.targetObj;
      if (!o || o.stage < 3) { v.state = 'idle'; v.decideT = 0.3; break; }
      v.state = 'harvest'; v.workT = 2.5;
      break;
    }
    case 'harvest': {
      v.workT -= dt;
      if (v.workT <= 0) {
        const o = v.targetObj;
        if (o && o.stage >= 3) {
          o.stage = 1;
          o.growAt = simTime + 60 / rainMult();
          v.carry.berries += 4;
          v.skill.forage = Math.min(3, v.skill.forage + 0.08);
          SIM.harvests++;
          logEvent('🌾', `${v.name} собрал урожай пшеницы (+4 🫐)`);
        }
        v.targetObj = null; v.state = 'idle'; v.decideT = 0.4;
      }
      break;
    }
    case 'goto_craft': {
      // сдаём ношу в общий котёл — из неё и мастерим
      stocks.wood += v.carry.wood; stocks.stone += v.carry.stone; stocks.berries += v.carry.berries;
      stocks.fur = (stocks.fur || 0) + (v.carry.fur || 0); v.carry.fur = 0;
      v.carry = { wood: 0, berries: 0, stone: 0 };
      v.state = 'craft'; v.workT = 2.5;
      break;
    }
    case 'craft': {
      v.workT -= dt;
      if (v.workT <= 0) {
        const kind = v.craftKind;
        if (kind === 'coat') {
          if ((stocks.fur || 0) >= 3 && stocks.wood >= 2) {
            stocks.fur -= 3; stocks.wood -= 2; v.coat = true;
            logEvent('🧥', `${v.name} сшил${v.gender === 'f' ? 'а' : ''} меховую шубу — метель теперь нипочём!`);
          } else think(v, 'Меха на шубу не хватило…');
          v.state = 'idle'; v.decideT = 0.5;
          break;
        }
        const cost = kind === 'axe' ? { wood: 3, stone: 2 } : { wood: 3, stone: 2 };
        if (stocks.wood >= cost.wood && stocks.stone >= cost.stone) {
          stocks.wood -= cost.wood; stocks.stone -= cost.stone;
          if (kind === 'axe') v.tool = 'axe'; else v.spear = true;
          logEvent('🔨', `${v.name} смастерил ${kind === 'axe' ? 'каменный топор 🪓' : 'каменное копьё 🔱'} (−${cost.wood} 🪵 −${cost.stone} 🪨)`);
        } else {
          think(v, 'Камня на орудие не хватило…');
        }
        v.state = 'idle'; v.decideT = 0.5;
      }
      break;
    }
    case 'hunt': {
      v.workT -= dt;
      if (v.workT <= 0) {
        think(v, 'Уф… не догнать. Пусть живёт.');
        v.state = 'idle'; v.decideT = 1; v.huntId = 0; v.eatIntent = false;
        break;
      }
      const a = animals.find(x => x.id === v.huntId && x.hp > 0);
      if (!a) { v.state = 'idle'; v.decideT = 0.5; v.huntId = 0; break; }
      const d = dist(v.x, v.y, a.x, a.y);
      if (d > 0.9) {
        // прямая погоня
        v.repathT = (v.repathT || 0) - dt;
        if (v.repathT <= 0) {
          v.repathT = 0.4;
          v.path = astar(v.x, v.y, Math.floor(a.x), Math.floor(a.y));
          v.pathIdx = 0;
          if (!v.path) {
            // не дойти по сетке — идём напрямую
            steer(v, a.x, a.y, 3.0, dt);
          }
        } else if (!v.path) steer(v, a.x, a.y, 3.0, dt);
      } else {
        a.hp = 0;
        v.huntId = 0;
        if (a.kind === 'rabbit') {
          v.carry.berries += 2;
          logEvent('🏹', `${v.name} поймал кролика (+2 🫐)`);
        } else {
          const meat = a.kind === 'wolf' ? 3 : 4;
          v.carry.berries += meat;
          v.carry.fur = (v.carry.fur || 0) + (a.kind === 'wolf' ? 1 : 2);
          const AN = { wolf: 'волка', camel: 'верблюда', deer: 'оленя' }[a.kind] || 'зверя';
          logEvent('🏹', `${v.name} добыл${v.gender === 'f' ? 'а' : ''} ${AN} (+${meat} 🍖 +2 🧥 мех)`);
        }
        if (v.eatIntent) {
          v.eatIntent = false;
          v.carry.berries = Math.max(0, v.carry.berries - 1);
          v.needs.hunger = Math.min(100, v.needs.hunger + 45);
          think(v, 'Свежатина! Ням.');
        }
        v.state = 'idle'; v.decideT = 1;
      }
      break;
    }
    case 'fight': {
      const m = monsters.find(mm => mm.id === v.fightId && mm.hp > 0);
      if (!m) { v.state = 'idle'; v.decideT = 0.5; break; }
      const d = dist(v.x, v.y, m.x, m.y);
      if (d > 1.1) {
        v.repathT -= dt;
        if (v.repathT <= 0) {
          v.repathT = 0.6;
          const t = approachTile(v, Math.floor(m.x), Math.floor(m.y));
          if (t) { v.path = astar(v.x, v.y, t.x, t.y); v.pathIdx = 0; }
          if (!v.path) steer(v, m.x, m.y, 2.6, dt);
        } else if (!v.path) steer(v, m.x, m.y, 2.6, dt);
      } else {
        v.atkT -= dt;
        if (v.atkT <= 0) {
          v.atkT = 0.7;
          const dmg = (v.spear ? 8 : 5) * (0.5 + v.skill.combat * 0.5) + (hasTrait(v, 'brave') ? 1 : 0);
          m.hp -= dmg;
          v.skill.combat = Math.min(3, v.skill.combat + 0.08);
          if (m.hp <= 0) {
            killMonster(m, `${v.name} одолел её`);
            think(v, 'Победа! Деревня в безопасности.');
            v.state = 'idle'; v.decideT = 1.2;
          }
        }
      }
      break;
    }
    case 'flee': {
      v.state = 'hide'; v.stateT = 8;
      break;
    }
    case 'hide': {
      v.hp = Math.min(20, v.hp + 0.9 * dt);
      v.stateT -= dt;
      if (v.stateT <= 0) { v.state = 'idle'; v.decideT = 0.4; }
      break;
    }
    case 'goto_mine': {
      const o = v.targetObj;
      if (!o) { v.state = 'idle'; v.decideT = 0.3; break; }
      v.state = 'mine'; v.workT = 4;
      break;
    }
    case 'mine': {
      v.workT -= dt;
      if (v.workT <= 0) {
        const o = v.targetObj;
        if (o && objects.includes(o)) {
          removeObject(o);
          v.carry.stone += 2;
          logEvent('🪨', `${v.name} добыл камень (+2 🪨)`);
        }
        v.targetObj = null; v.state = 'idle'; v.decideT = 0.4 + rng();
      }
      break;
    }
    case 'goto_deposit': {
      stocks.wood += v.carry.wood; stocks.berries += v.carry.berries; stocks.stone += v.carry.stone;
      stocks.fur = (stocks.fur || 0) + (v.carry.fur || 0); v.carry.fur = 0;
      if (v.carry.wood > 0 || v.carry.berries > 0 || v.carry.stone > 0)
        logEvent('📦', `${v.name} сдал запасы: +${v.carry.wood} 🪵 +${v.carry.berries} 🫐 +${v.carry.stone} 🪨`);
      v.carry = { wood: 0, berries: 0, stone: 0 };
      v.state = 'idle'; v.decideT = 0.5 + rng();
      break;
    }
    case 'goto_eat': {
      if (stocks.berries > 0) {
        stocks.berries--;
        v.needs.hunger = Math.min(100, v.needs.hunger + 55);
        v.state = 'eat'; v.workT = 2;
        think(v, pickThought(v, 'eat'));
      } else { v.state = 'idle'; v.decideT = 0.3; }
      break;
    }
    case 'eat': {
      v.workT -= dt;
      if (v.workT <= 0) { v.state = 'idle'; v.decideT = 0.4; }
      break;
    }
    case 'goto_warm': {
      v.state = 'warm'; v.workT = 4 + rng() * 4;
      if (rng() < 0.5) think(v, pick(['У огня жизнь теплее.', 'Погреться — святое дело.', 'Метель воет, а мы живы.', 'Тепло… Пока тепло.']));
      break;
    }
    case 'warm': {
      // греются у костра, пока не кончится буран
      v.workT -= dt;
      if (v.workT <= 0 || weather.kind !== 'blizzard') { v.state = 'idle'; v.decideT = 0.5; }
      break;
    }
    case 'goto_sleep': {
      v.state = 'sleep';
      // заходит внутрь дома — визуально скрывается там
      if (v.sleepHome) { v.x = v.sleepHome.x + 0.5; v.y = v.sleepHome.y + 0.5; }
      think(v, pickThought(v, 'sleep'));
      break;
    }
    case 'goto_social': {
      const other = villagers.find(o => o.id === (v.targetVil && v.targetVil.id));
      if (!other) { v.state = 'idle'; v.decideT = 0.5; break; }
      const d = dist(other.x, other.y, v.x, v.y);
      if (d > 1.6) {
        const p = astar(v.x, v.y, Math.floor(other.x), Math.floor(other.y));
        if (p && p.length > 0) { v.path = p.slice(0, Math.ceil(p.length / 2)); v.pathIdx = 0; }
        else { v.state = 'idle'; v.decideT = 1; }
        break;
      }
      v.state = 'social'; v.workT = 3; v.socialWith = other.id;
      if (other.state !== 'social' && other.state !== 'goto_social') {
        other.state = 'social'; other.workT = 3; other.socialWith = v.id; think(other, pickThought(other, 'social'));
      }
      break;
    }
    case 'social': {
      v.workT -= dt;
      if (v.workT <= 0) {
        v.needs.social = 100;
        const other = villagers.find(o => o.id === v.socialWith);
        if (other && other.state === 'social') { other.needs.social = 100; other.state = 'idle'; other.decideT = 1; }
        if (other && other.state === 'social' && rng() < 0.25) {
          const d = pick(DISPUTES);
          logEvent('💬', `${v.name} и ${other.name} заспорили: «${d.a}!» — «Нет же: ${d.b}!»`);
          think(v, d.a + '.');
          think(other, d.b + '.');
        } else if (rng() < 0.45) logEvent('💬', `${v.name} и ${other ? other.name : 'кто-то'} поболтали у костра`);
        v.state = 'idle'; v.decideT = 1;
      }
      break;
    }
    case 'goto_build': {
      if (!pendingBuild || pendingBuild.assigned !== v) { v.state = 'idle'; v.decideT = 0.5; break; }
      const bd = dist(v.x, v.y, pendingBuild.x + 0.5, pendingBuild.y + 0.5);
      if (bd > 2.4) {
        if (!v.path) {
          const t = approachTile(v, pendingBuild.x, pendingBuild.y);
          v.path = t ? astar(v.x, v.y, t.x, t.y) : null;
          v.pathIdx = 0;
          if (!v.path) {
            // место недостижимо — отмена стройки с возвратом материалов
            const COSTS = { shelter: { wood: 10 }, farm: { wood: 15 }, hut: { wood: 25 }, house: { wood: 50, stone: 10 } };
            const c = COSTS[pendingBuild.kind] || {};
            stocks.wood += c.wood || 0; stocks.stone += c.stone || 0;
            logEvent('🚧', 'Стройку отменили: место недостижимо. Материалы вернули на склад.');
            pendingBuild = null;
          }
        }
        v.state = 'goto_build';
        break;
      }
      v.state = 'build';
      v.workT = { shelter: 2.5, farm: 3.5, hut: 4.5, house: 6 }[pendingBuild.kind] || 4;
      break;
    }
    case 'build': {
      v.workT -= dt;
      if (v.workT <= 0) {
        if (pendingBuild && pendingBuild.assigned === v) {
          const { kind, x, y } = pendingBuild;
          if (kind === 'farm') {
            addObject('farm', x, y);
            const f = farms[farms.length - 1];
            f.growAt = simTime + 60 / rainMult();
            logEvent('🌾', `${v.name} распахал поле. Будет хлеб!`);
          } else if (kind === 'shelter') {
            addObject('shelter', x, y);
            logEvent('🏕', `${v.name} построил шалаш. У деревни есть первое жильё!`);
          } else if (kind === 'house') {
            addObject('house', x, y);
            logEvent('🏡', `${v.name} построил настоящий дом из камня и дерева!`);
          } else {
            if (addHut(x, y)) logEvent('🏠', `${v.name} построил хижину! Деревня растёт.`);
          }
          pendingBuild = null;
        }
        v.state = 'idle'; v.decideT = 1;
      }
      break;
    }
    case 'goto_camp': {
      v.state = 'idle'; v.decideT = 0.5;
      think(v, 'Вот и деревня. Красиво тут!');
      break;
    }
    case 'wander': {
      v.state = 'idle'; v.decideT = 0.5 + rng() * 1.5;
      break;
    }
    case 'idle':
    default: {
      if (!isNight()) v.hp = Math.min(20, v.hp + 0.5 * dt); // днём раны затягиваются
      v.decideT -= dt;
      if (v.decideT <= 0) decide(v);
      break;
    }
  }
}

function processRegrow() {
  for (let i = regrowQueue.length - 1; i >= 0; i--) {
    const r = regrowQueue[i];
    if (simTime >= r.at) {
      const o = objAt.get(key(r.x, r.y));
      if (o && o.type === 'stump') {
        removeObject(o);
        addObject('tree', r.x, r.y);
      }
      regrowQueue.splice(i, 1);
    }
  }
}

// ── Хроника ───────────────────────────────────────────────────────
const chronicleEl = document.getElementById('chronicle');
function logEvent(icon, text) {
  const d = document.createElement('div');
  d.className = 'chron-item';
  const day = Math.floor(simTime / DAY_LEN) + 1;
  const p = phase();
  const hh = String(Math.floor(p * 24)).padStart(2, '0');
  const mm = String(Math.floor((p * 24 % 1) * 60)).padStart(2, '0');
  d.innerHTML = `<span class="chron-icon">${icon}</span><span class="chron-time">Д${day} ${hh}:${mm}</span> ${text}`;
  chronicleEl.prepend(d);
  while (chronicleEl.children.length > 60) chronicleEl.lastChild.remove();
}

// ── Отрисовка ─────────────────────────────────────────────────────
const canvas = document.getElementById('game');
const ctx = canvas.getContext('2d');
let cw = 0, ch = 0;
function resize() {
  const dpr = Math.min(2, window.devicePixelRatio || 1);
  cw = window.innerWidth; ch = window.innerHeight;
  canvas.width = cw * dpr; canvas.height = ch * dpr;
  canvas.style.width = cw + 'px'; canvas.style.height = ch + 'px';
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
}
window.addEventListener('resize', resize);

const menuStars = Array.from({ length: 110 }, (_, i) => ({ x: Math.random(), y: Math.random() * 0.62, p: Math.random() * 6.28 }));
function drawMenuScene() {
  const t = performance.now() / 1000;
  // небо
  const g = ctx.createLinearGradient(0, 0, 0, ch);
  g.addColorStop(0, '#070b1c'); g.addColorStop(0.65, '#121a36'); g.addColorStop(1, '#1a2340');
  ctx.fillStyle = g; ctx.fillRect(0, 0, cw, ch);
  // звёзды мерцают
  for (const s of menuStars) {
    const a = 0.3 + 0.7 * Math.abs(Math.sin(t * 0.7 + s.p));
    ctx.fillStyle = 'rgba(220,228,255,' + a.toFixed(2) + ')';
    ctx.fillRect(s.x * cw, s.y * ch, 2, 2);
  }
  // луна с кратерами
  ctx.fillStyle = '#e8e4d0'; ctx.beginPath(); ctx.arc(cw * 0.84, ch * 0.17, Math.min(30, ch * 0.045), 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = 'rgba(160,160,150,0.5)';
  ctx.beginPath(); ctx.arc(cw * 0.85, ch * 0.15, 5, 0, Math.PI * 2); ctx.fill();
  ctx.beginPath(); ctx.arc(cw * 0.82, ch * 0.19, 3, 0, Math.PI * 2); ctx.fill();
  // дальние холмы
  ctx.fillStyle = '#0c1129';
  ctx.beginPath(); ctx.moveTo(0, ch * 0.8);
  ctx.quadraticCurveTo(cw * 0.25, ch * 0.6, cw * 0.5, ch * 0.78);
  ctx.quadraticCurveTo(cw * 0.75, ch * 0.62, cw, ch * 0.8);
  ctx.lineTo(cw, ch); ctx.lineTo(0, ch); ctx.fill();
  // ели-силуэты
  ctx.fillStyle = '#0a0f22';
  for (let i = 0; i < 14; i++) {
    const ex = (i / 13) * cw + Math.sin(i * 3.7) * 14;
    const eh = ch * (0.1 + 0.05 * Math.abs(Math.sin(i * 1.3)));
    const ey = ch * 0.78;
    ctx.beginPath(); ctx.moveTo(ex, ey - eh);
    ctx.lineTo(ex + eh * 0.34, ey); ctx.lineTo(ex - eh * 0.34, ey); ctx.fill();
  }
  // земля
  ctx.fillStyle = '#101d0e'; ctx.fillRect(0, ch * 0.78, cw, ch * 0.22);
  ctx.fillStyle = '#152610'; ctx.fillRect(0, ch * 0.78, cw, 3);
  // костёр по центру
  const fx = cw / 2, fy = ch * 0.78 + 18;
  ctx.fillStyle = 'rgba(255,150,50,0.07)';
  ctx.beginPath(); ctx.arc(fx, fy - 16, 130 + Math.sin(t * 3) * 8, 0, Math.PI * 2); ctx.fill();
  // брёвна
  ctx.save(); ctx.translate(fx, fy); ctx.rotate(0.45); ctx.fillStyle = '#5c3d22'; ctx.fillRect(-34, -5, 68, 10); ctx.restore();
  ctx.save(); ctx.translate(fx, fy); ctx.rotate(-0.45); ctx.fillStyle = '#6b4a2b'; ctx.fillRect(-34, -5, 68, 10); ctx.restore();
  // пламя в три слоя
  const f1 = Math.sin(t * 9) * 3, f2 = Math.sin(t * 13 + 1) * 2;
  ctx.fillStyle = '#ff7b1c';
  ctx.beginPath(); ctx.moveTo(fx - 17, fy);
  ctx.quadraticCurveTo(fx - 12 + f1, fy - 42, fx + f1 * 0.6, fy - 52);
  ctx.quadraticCurveTo(fx + 13 + f1, fy - 34, fx + 17, fy); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#ffb52e';
  ctx.beginPath(); ctx.moveTo(fx - 11, fy);
  ctx.quadraticCurveTo(fx - 7 + f2, fy - 28, fx + f2 * 0.5, fy - 36);
  ctx.quadraticCurveTo(fx + 9 + f2, fy - 22, fx + 11, fy); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#ffe58a';
  ctx.beginPath(); ctx.moveTo(fx - 6, fy);
  ctx.quadraticCurveTo(fx - 3 + f2, fy - 14, fx + f2 * 0.4, fy - 20);
  ctx.quadraticCurveTo(fx + 5 + f2, fy - 10, fx + 6, fy); ctx.closePath(); ctx.fill();
  // искры и дым
  for (let i = 0; i < 7; i++) {
    const ph = (t * 0.35 + i / 7) % 1;
    ctx.fillStyle = 'rgba(255,200,90,' + (1 - ph).toFixed(2) + ')';
    ctx.fillRect(fx + Math.sin(t * 2 + i * 2.1) * 24, fy - 55 - ph * 100, 3, 3);
  }
  for (let i = 0; i < 5; i++) {
    const ph = (t * 0.12 + i / 5) % 1;
    ctx.fillStyle = 'rgba(180,190,210,' + (0.25 * (1 - ph)).toFixed(2) + ')';
    ctx.beginPath(); ctx.arc(fx + Math.sin(t * 0.8 + i) * 30, fy - 60 - ph * 200, 8 + ph * 18, 0, Math.PI * 2); ctx.fill();
  }
  // светлячки
  for (let i = 0; i < 9; i++) {
    const a = Math.abs(Math.sin(t * 0.9 + i * 1.9));
    ctx.fillStyle = 'rgba(180,255,140,' + (a * 0.8).toFixed(2) + ')';
    ctx.fillRect((Math.sin(i * 5.3) * 0.4 + 0.5) * cw, ch * (0.55 + 0.2 * Math.abs(Math.sin(i * 2.7 + t * 0.3))), 3, 3);
  }
  // виньетка
  const vg = ctx.createRadialGradient(cw / 2, ch / 2, ch * 0.25, cw / 2, ch / 2, ch * 0.9);
  vg.addColorStop(0, 'rgba(0,0,0,0)'); vg.addColorStop(1, 'rgba(0,0,0,0.55)');
  ctx.fillStyle = vg; ctx.fillRect(0, 0, cw, ch);
}
function draw() {
  if (menuScene) drawMenuScene();
  else drawWorld();
}

function drawWorld() {
  ctx.imageSmoothingEnabled = false;
  ctx.fillStyle = '#0b0d14';
  ctx.fillRect(0, 0, cw, ch);
  if (!mapCanvas) return;
  const z = zoom;
  ctx.save();
  ctx.translate(cw / 2, ch / 2);
  ctx.scale(z, z);
  ctx.translate(-camX, -camY);
  ctx.drawImage(mapCanvas, 0, 0);
  const drawList = [];
  for (const o of objects) drawList.push({ y: o.y, draw: () => drawObject(o) });
  for (const a of animals) if (a.hp > 0) drawList.push({ y: a.y, draw: () => drawAnimal(a) });
  for (const m of monsters) drawList.push({ y: m.y, draw: () => drawMonster(m) });
  for (const v of villagers) drawList.push({ y: v.y + 0.4, draw: () => drawVillager(v) });
  if (mode === 'life' && P && !P.dead) drawList.push({ y: P.y + 0.5, draw: () => drawLifePlayer() });
  drawList.sort((a, b) => a.y - b.y);
  for (const d of drawList) d.draw();
  ctx.restore();
  // ночь
  const night = nightAmount();
  if (night > 0) {
    ctx.fillStyle = `rgba(16,20,52,${(night * 0.52).toFixed(3)})`;
    ctx.fillRect(0, 0, cw, ch);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    const fx = (campfire.x * TILE + 4 - camX) * z + cw / 2;
    const fy = (campfire.y * TILE + 4 - camY) * z + ch / 2;
    const flick = 0.85 + Math.sin(performance.now() / 130) * 0.15;
    const rad = ctx.createRadialGradient(fx, fy, 0, fx, fy, 90 * z * flick);
    rad.addColorStop(0, `rgba(255,150,50,${0.30 * night})`);
    rad.addColorStop(1, 'rgba(255,150,50,0)');
    ctx.fillStyle = rad;
    ctx.fillRect(fx - 100 * z, fy - 100 * z, 200 * z, 200 * z);
    ctx.restore();
  }
  // дождь
  if (weather.kind === 'rain') {
    ctx.fillStyle = 'rgba(40,60,110,0.18)';
    ctx.fillRect(0, 0, cw, ch);
    ctx.strokeStyle = 'rgba(180,200,255,0.45)';
    ctx.lineWidth = 1;
    const t = performance.now() / 1000;
    ctx.beginPath();
    for (let i = 0; i < 90; i++) {
      const rx = (i * 137 + (t * 260 + i * 31)) % cw;
      const ry = (i * 79 + t * 520) % ch;
      ctx.moveTo(rx, ry);
      ctx.lineTo(rx - 3, ry + 11);
    }
    ctx.stroke();
  }
  // снегопад
  if (weather.kind === 'snow' || weather.kind === 'blizzard') {
    const blz = weather.kind === 'blizzard';
    if (blz) { ctx.fillStyle = 'rgba(205,220,240,0.22)'; ctx.fillRect(0, 0, cw, ch); }
    const t = performance.now() / 1000;
    const n = blz ? 110 : 70;
    ctx.fillStyle = blz ? 'rgba(235,242,252,0.9)' : 'rgba(245,248,255,0.85)';
    for (let i = 0; i < n; i++) {
      const sx = (i * 149 + t * (blz ? 240 : 42) + Math.sin(t * 0.8 + i) * (blz ? 14 : 8)) % cw;
      const sy = (i * 83 + t * (blz ? 340 : 60)) % ch;
      ctx.fillRect(sx, sy, 2, 2);
    }
  }
  // туман
  if (weather.kind === 'fog') {
    const t = performance.now() / 1000;
    for (let b = 0; b < 3; b++) {
      const fy = ch * (0.2 + b * 0.3) + Math.sin(t * 0.3 + b * 2) * 14;
      const fx = (t * (12 + b * 9)) % (cw + 300) - 300;
      ctx.fillStyle = `rgba(190,204,196,${(0.16 - b * 0.03).toFixed(2)})`;
      ctx.beginPath();
      ctx.ellipse(fx + 150, fy, 260, 46, 0, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.fillStyle = 'rgba(186,198,190,0.10)';
    ctx.fillRect(0, 0, cw, ch);
  }
  // лепестки вишни
  if (weather.kind === 'petals') {
    const t = performance.now() / 1000;
    for (let i = 0; i < 34; i++) {
      const px2 = (i * 163 + t * 30 + Math.sin(t * 0.9 + i * 1.7) * 20) % cw;
      const py2 = (i * 97 + t * 46) % ch;
      ctx.fillStyle = i % 3 ? 'rgba(255,182,208,0.9)' : 'rgba(255,214,228,0.9)';
      ctx.fillRect(px2, py2, 2, 2);
      ctx.fillRect(px2 + 1, py2 - 1, 1, 1);
    }
  }
  // молния
  if (weather.bolt > 0) {
    ctx.fillStyle = `rgba(255,255,255,${(weather.bolt * 0.5).toFixed(2)})`;
    ctx.fillRect(0, 0, cw, ch);
  }
  // пузыри мыслей
  for (const v of villagers) {
    if (v.thought && simTime < v.thoughtUntil) {
      const sx = (v.x * TILE - camX) * z + cw / 2;
      const sy = (v.y * TILE - 18 - camY) * z + ch / 2;
      drawBubble(sx, sy, v.thought, v === selected);
    }
  }
  // zZ над спящими
  if (night > 0.3) {
    for (const v of villagers) {
      if (v.state === 'sleep') {
        const sx = (v.x * TILE - camX) * z + cw / 2;
        const sy = (v.y * TILE - 14 - camY) * z + ch / 2;
        ctx.font = `${Math.round(10 * Math.min(z, 2))}px sans-serif`;
        ctx.fillStyle = 'rgba(200,210,255,0.9)';
        const t = (performance.now() / 500) % 2;
        ctx.fillText('z', sx + 4, sy - t * 4);
      }
    }
  }
}

function drawObject(o) {
  const x = o.x * TILE, y = o.y * TILE;
  const tt = inb(o.x, o.y) ? world[key(o.x, o.y)] : 3;
  let hutSpr = spr.hut, shelSpr = spr.shelter, houseSpr = spr.house;
  if (tt === 7 || tt === 8) { hutSpr = spr.hutD; shelSpr = spr.shelterD; houseSpr = spr.houseD; }
  else if (tt === 9 || tt === 10 || tt === 11) { hutSpr = spr.hutN; shelSpr = spr.shelterN; houseSpr = spr.houseN; }
  else if (tt === 12) { hutSpr = spr.hutK; shelSpr = spr.shelterK; houseSpr = spr.houseK; }
  else if (tt === 13) { hutSpr = spr.hutS; shelSpr = spr.shelterS; houseSpr = spr.houseS; }
  switch (o.type) {
    case 'tree': ctx.drawImage(spr.tree[o.variant % 3], x - 1, y - 6); break;
    case 'pine': ctx.drawImage(spr.pine[o.variant % 3], x - 1, y - 6); break;
    case 'bush': ctx.drawImage(spr.bush[o.depleted ? 1 : 0], x - 1, y + 2); break;
    case 'cactus': ctx.drawImage(spr.cactus[o.depleted ? 1 : 0], x - 1, y - 6); break;
    case 'acacia': ctx.drawImage(spr.acacia, x - 3, y - 6); break;
    case 'mangrove': ctx.drawImage(spr.mangrove[o.variant % 3], x - 1, y - 6); break;
    case 'deadtree': ctx.drawImage(spr.deadtree[o.variant % 3], x - 1, y - 6); break;
    case 'darkpine': ctx.drawImage(spr.darkpine[o.variant % 3], x - 1, y - 6); break;
    case 'cherry': ctx.drawImage(spr.cherry[o.variant % 3], x - 1, y - 6); break;
    case 'reed': ctx.drawImage(spr.reed, x - 1, y + 1); break;
    case 'mushroom': ctx.drawImage(spr.mushroom[o.depleted ? 1 : 0], x, y + 2); break;
    case 'stone': ctx.drawImage(spr.stone, x, y + 1); break;
    case 'flower': ctx.drawImage(spr.flower, x + 1, y + 1); break;
    case 'stump': ctx.drawImage(spr.stump, x + 1, y + 4); break;
    case 'grave': ctx.drawImage(spr.grave, x + 1, y + 2); break;
    case 'farm': ctx.drawImage(spr.farm[o.stage] || spr.farm[1], x - 4, y - 1); break;
    case 'hut': {
      ctx.drawImage(hutSpr, x - 5, y - 8);
      if (nightAmount() > 0.3) {
        ctx.fillStyle = 'rgba(255,220,120,0.9)';
        ctx.fillRect(x - 5 + spr.hutWindow.x, y - 8 + spr.hutWindow.y, spr.hutWindow.w, spr.hutWindow.h);
        drawSmoke(x - 5 + spr.hutChimney.x + 1, y - 8 + spr.hutChimney.y);
      }
      break;
    }
    case 'shelter': {
      ctx.drawImage(shelSpr, x - 3, y - 6);
      break;
    }
    case 'house': {
      ctx.drawImage(houseSpr, x - 7, y - 10);
      if (nightAmount() > 0.3) {
        ctx.fillStyle = 'rgba(255,220,120,0.9)';
        for (const wnd of spr.houseWindows)
          ctx.fillRect(x - 7 + wnd.x, y - 10 + wnd.y, wnd.w, wnd.h);
        drawSmoke(x - 7 + spr.houseChimney.x + 1, y - 10 + spr.houseChimney.y);
      }
      break;
    }
    case 'mine': {
      ctx.drawImage(spr.stone, x, y + 1);
      ctx.fillStyle = '#151009'; ctx.fillRect(x + 2, y + 3, 4, 5);
      ctx.fillStyle = '#6a5335'; ctx.fillRect(x + 1, y + 2, 6, 1);
      px(ctx, x + 1, y + 3, 96, 74, 40); px(ctx, x + 6, y + 3, 96, 74, 40);
      if (nightAmount() > 0.3) { ctx.fillStyle = 'rgba(255,220,120,0.35)'; ctx.fillRect(x + 3, y + 5, 2, 1); }
      break;
    }
    case 'campfire': {
      ctx.drawImage(spr.campfire, x - 1, y - 1);
      const f = Math.sin(performance.now() / 90 + o.id);
      const h2 = 5 + f * 1.5;
      ctx.fillStyle = 'rgb(255,120,30)';
      ctx.fillRect(x + 2, y + 3 - h2, 4, h2);
      ctx.fillStyle = 'rgb(255,200,60)';
      ctx.fillRect(x + 3, y + 4 - h2 * 0.6, 2, h2 * 0.6);
      break;
    }
  }
}

function drawSmoke(sx, sy) {
  const t = performance.now() / 400;
  for (let i = 0; i < 3; i++) {
    const p = (t + i * 1.4) % 4;
    const a = 0.5 - p * 0.11;
    if (a <= 0) continue;
    ctx.fillStyle = `rgba(180,180,190,${a.toFixed(2)})`;
    ctx.fillRect(sx + Math.sin(p * 2 + i) * 1.2, sy - p * 1.6, 1.5, 1.5);
  }
}
function drawAnimal(a) {
  const x = a.x * TILE - 3, y = a.y * TILE - 3;
  const frame = Math.floor(a.animT * 6) % 2;
  if (a.kind === 'rabbit') {
    const set = a.facing >= 0 ? spr.rabbit : spr.rabbit;
    ctx.drawImage(set[frame], Math.round(x), Math.round(y));
  } else if (a.kind === 'camel') {
    const bob = frame ? 0 : 1;
    ctx.fillStyle = 'rgb(196,160,110)'; ctx.fillRect(x + 1, y + 4 + bob, 8, 4);
    ctx.fillStyle = 'rgb(168,132,88)'; ctx.fillRect(x + 1, y + 7, 8, 1);
    ctx.fillStyle = 'rgb(206,170,120)'; ctx.fillRect(x + 2, y + 2 + bob, 4, 4);
    ctx.fillStyle = 'rgb(196,160,110)'; ctx.fillRect(x + 3, y + 1 + bob, 3, 2);
    ctx.fillStyle = 'rgb(150,112,74)'; ctx.fillRect(x + 3, y + 1, 1, 1);
    ctx.fillStyle = 'rgb(206,170,120)'; ctx.fillRect(x, y + 6 + bob, 1, 3); ctx.fillRect(x + 8, y + 6 + bob, 1, 3);
    ctx.fillStyle = 'rgb(120,86,56)'; ctx.fillRect(x, y + 8 + bob, 1, 1); ctx.fillRect(x + 8, y + 8 + bob, 1, 1);
  } else if (a.kind === 'deer') {
    const bob = frame ? 0 : 1;
    ctx.fillStyle = 'rgb(158,124,88)'; ctx.fillRect(x + 1, y + 4 + bob, 8, 4);
    ctx.fillStyle = 'rgb(132,100,70)'; ctx.fillRect(x + 1, y + 7, 8, 1);
    ctx.fillStyle = 'rgb(170,136,98)'; ctx.fillRect(x + 3, y + 1 + bob, 3, 4);
    ctx.fillStyle = 'rgb(92,72,54)'; ctx.fillRect(x + 3, y, 1, 1); ctx.fillRect(x + 5, y, 1, 1);
    px(ctx, x + 2, y - 1, 92, 72, 54); px(ctx, x + 6, y - 1, 92, 72, 54);
    ctx.fillStyle = 'rgb(158,124,88)'; ctx.fillRect(x, y + 6 + bob, 1, 3); ctx.fillRect(x + 8, y + 6 + bob, 1, 3);
    ctx.fillStyle = 'rgb(110,84,60)'; ctx.fillRect(x, y + 8 + bob, 1, 1); ctx.fillRect(x + 8, y + 8 + bob, 1, 1);
  } else {
    const set = a.facing >= 0 ? spr.wolf : spr.wolf;
    ctx.drawImage(set[frame], Math.round(x), Math.round(y));
  }
}

function drawMonster(m) {
  const x = m.x * TILE - 4, y = m.y * TILE - 4;
  const frame = Math.floor(m.animT * 3) % 2;
  ctx.drawImage(spr.slime[frame], Math.round(x), Math.round(y));
  // полоска HP
  if (m.hp < m.maxHp) {
    ctx.fillStyle = 'rgba(0,0,0,0.5)';
    ctx.fillRect(x, y - 3, 8, 2);
    ctx.fillStyle = 'rgb(120,220,80)';
    ctx.fillRect(x, y - 3, 8 * Math.max(0, m.hp) / m.maxHp, 2);
  }
}

function drawVillager(v) {
  if (v.state === 'sleep') return; // спит внутри дома — не рисуем поверх крыши
  const scale = v.isChild ? 0.65 : 1;
  const x = v.x * TILE - 4, y = v.y * TILE - 6 + (v.isChild ? 4 : 0);
  if (v === selected) {
    ctx.strokeStyle = 'rgba(140,120,255,0.9)';
    ctx.lineWidth = 0.8;
    ctx.strokeRect(x - 1.5, y - 1.5, 11, 16.5);
  }
  const moving = v.path && v.pathIdx < v.path.length;
  // ходьба: 4-кадровый цикл 8 к/с; простой: лёгкое дыхание (покачивание корпуса)
  const frame = moving
    ? Math.floor((v.animT || 0) * 8) % 4
    : (Math.sin((simTime + v.id) * 2.2) > 0 ? 1 : 3);
  const set = v.facing >= 0 ? spr.villagerFrames[v.bodyIdx] : spr.villagerFlip[v.bodyIdx];
  // тень под ногами — приземляет фигуру, не даёт 'повиснуть в воздухе'
  ctx.fillStyle = 'rgba(0,0,0,0.28)';
  ctx.beginPath();
  ctx.ellipse(x + 4, y + 14 * scale - 1, 3.6 * scale, 1.3 * scale, 0, 0, Math.PI * 2);
  ctx.fill();
  if (v.isChild) ctx.drawImage(set[frame], Math.round(x), Math.round(y), 8 * scale, 14 * scale);
  else ctx.drawImage(set[frame], Math.round(x), Math.round(y));
  if (v.coat && !v.isChild) { px(ctx, x + 2, y + 5, 122, 84, 48); px(ctx, x + 5, y + 5, 122, 84, 48); px(ctx, x + 3, y + 6, 100, 66, 38); px(ctx, x + 4, y + 6, 100, 66, 38); }
  // имя при зуме
  if (zoom >= 2) {
    ctx.font = '4px monospace';
    ctx.fillStyle = 'rgba(255,255,255,0.75)';
    ctx.textAlign = 'center';
    ctx.fillText(v.name, x + 4, y - 1);
    ctx.textAlign = 'left';
  }
  // сердечки HP (если ранен)
  if (v.hp < 20) {
    const hearts = Math.ceil(v.hp / 4);
    for (let i = 0; i < hearts; i++) {
      ctx.fillStyle = 'rgb(220,60,80)';
      ctx.fillRect(x + i * 2, y - 4, 1.5, 1.5);
    }
  }
  // иконки занятия — рисуем векторно (эмодзи в canvas на некоторых WebView не рендерится, вместо
  // иконки показывает пустой квадрат/крестик — поэтому никаких fillText с эмодзи тут)
  if (v.state === 'chop' || v.state === 'fight' || v.state === 'craft' || v.state === 'hunt') {
    drawActionIcon(v.state, x + 8, y + 2, v.tool);
  }
}

// маленькие векторные значки занятий жителя (без зависимости от эмодзи-шрифта)
function drawActionIcon(kind, ix, iy, tool) {
  ctx.save();
  ctx.translate(ix, iy);
  ctx.lineWidth = 0.9;
  if (kind === 'chop') {
    if (tool === 'axe') {
      ctx.strokeStyle = 'rgb(130,90,50)';
      ctx.beginPath(); ctx.moveTo(0, 5); ctx.lineTo(3.5, 0.5); ctx.stroke();
      ctx.fillStyle = 'rgb(200,200,208)';
      ctx.beginPath(); ctx.moveTo(3, 0); ctx.lineTo(5.5, 0.8); ctx.lineTo(3.4, 2.6); ctx.closePath(); ctx.fill();
    } else {
      ctx.fillStyle = 'rgb(220,180,140)';
      ctx.beginPath(); ctx.arc(2, 2, 2, 0, Math.PI * 2); ctx.fill();
    }
  } else if (kind === 'fight') {
    if (tool === 'spear') {
      ctx.strokeStyle = 'rgb(150,105,60)';
      ctx.beginPath(); ctx.moveTo(0, 5.5); ctx.lineTo(4.5, 0.3); ctx.stroke();
      ctx.fillStyle = 'rgb(210,210,220)';
      ctx.beginPath(); ctx.moveTo(4.2, 0); ctx.lineTo(5.6, 0.9); ctx.lineTo(3.6, 2); ctx.closePath(); ctx.fill();
    } else {
      ctx.fillStyle = 'rgb(225,90,90)';
      ctx.fillRect(0, 1, 4, 3.4);
    }
  } else if (kind === 'craft') {
    ctx.fillStyle = 'rgb(150,90,55)';
    ctx.fillRect(1.6, 1.5, 1, 4);
    ctx.fillStyle = 'rgb(170,170,180)';
    ctx.fillRect(0, 0, 4.2, 2);
  } else if (kind === 'hunt') {
    ctx.strokeStyle = 'rgb(155,115,75)';
    ctx.beginPath(); ctx.arc(1.6, 2.6, 2.6, -1.05, 1.05); ctx.stroke();
    ctx.strokeStyle = 'rgba(240,240,245,0.85)'; ctx.lineWidth = 0.5;
    ctx.beginPath(); ctx.moveTo(0.5, 0.5); ctx.lineTo(0.5, 4.7); ctx.stroke();
  }
  ctx.restore();
}

function drawBubble(sx, sy, text, isSel) {
  ctx.font = '12px sans-serif';
  const pad = 7;
  const wTxt = ctx.measureText(text).width;
  const bw = wTxt + pad * 2, bh = 22;
  let x = sx - bw / 2, yy = sy - bh - 6;
  x = Math.max(4, Math.min(cw - bw - 4, x));
  yy = Math.max(4, yy);
  ctx.fillStyle = isSel ? 'rgba(60,50,110,0.95)' : 'rgba(24,28,44,0.92)';
  ctx.strokeStyle = isSel ? 'rgba(150,130,255,0.8)' : 'rgba(90,100,130,0.5)';
  roundRect(x, yy, bw, bh, 6);
  ctx.fill(); ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(sx - 3, yy + bh); ctx.lineTo(sx + 3, yy + bh); ctx.lineTo(sx, yy + bh + 5);
  ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#e8eaf2';
  ctx.fillText(text, x + pad, yy + 15);
}
function roundRect(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

// ── Панель жителя ────────────────────────────────────────────────
const panelEl = document.getElementById('villagerPanel');
function fmtLeft(sec) {
  if (!isFinite(sec) || sec <= 0) return 'вот-вот';
  if (sec < 60) return Math.ceil(sec) + ' с';
  return Math.ceil(sec / 60) + ' мин';
}
function objInfo(o) {
  const titles = { tree: ['🌳', 'Лиственное дерево'], pine: ['🌲', 'Сосна'], bush: ['🫐', 'Ягодный куст'], cactus: ['🌵', 'Кактус'], acacia: ['🌳', 'Акация'], mangrove: ['🌿', 'Мангр'], deadtree: ['🪵', 'Сухостой'], darkpine: ['🌲', 'Тёмная ель'], cherry: ['🌸', 'Вишня'], reed: ['🌾', 'Камыш'], mushroom: ['🍄', 'Гриб'], stone: ['🪨', 'Валун'], flower: ['🌸', 'Цветок'], stump: ['🪵', 'Пень'], grave: ['🪦', 'Могила жителя'], farm: ['🌾', 'Поле пшеницы'], shelter: ['🏕', 'Шалаш'], hut: ['🏠', 'Хижина'], house: ['🏡', 'Каменный дом'], campfire: ['🔥', 'Костёр — сердце деревни'], mine: ['⛏️', 'Шахта'] };
  const t = titles[o.type] || ['❓', 'Объект'];
  const lines = [];
  if (o.type === 'tree' || o.type === 'pine' || o.type === 'acacia' || o.type === 'mangrove' || o.type === 'deadtree' || o.type === 'darkpine' || o.type === 'cherry') lines.push('Древесина: <b>3 🪵</b>', 'Срубит любой житель с топором');
  if (o.type === 'bush') {
    if (o.depleted) lines.push('Пусто. Ягоды вернутся через <b>' + fmtLeft(o.regrowAt - simTime) + '</b>');
    else lines.push('Спелые ягоды: <b>2 🫐</b>');
  }
  if (o.type === 'cactus') {
    if (o.depleted) lines.push('Плоды сорваны. Вернутся через <b>' + fmtLeft(o.regrowAt - simTime) + '</b>');
    else lines.push('Сладкие плоды кактуса: <b>2 🫐</b>', 'Осторожно — колючий!');
  }
  if (o.type === 'acacia') lines.push('Сухое дерево саванны', 'Древесина: <b>3 🪵</b>');
  if (o.type === 'mangrove') lines.push('Дерево болот с корнями-ходулями', 'Древесина: <b>3 🪵</b>');
  if (o.type === 'deadtree') lines.push('Мёртвое дерево топей', 'Древесина: <b>3 🪵</b>');
  if (o.type === 'darkpine') lines.push('Ель дремучего леса', 'Древесина: <b>3 🪵</b>');
  if (o.type === 'cherry') lines.push('Вишня в цвету', 'Древесина: <b>3 🪵</b>', 'Лепестки летят по всей роще');
  if (o.type === 'reed') lines.push('Камыш с съедобными кореньями: <b>2 🫐</b>');
  if (o.type === 'mushroom') {
    if (o.depleted) lines.push('Сорван. Вырастет через <b>' + fmtLeft(o.regrowAt - simTime) + '</b>');
    else lines.push('Съедобный: <b>2 🫐</b>');
  }
  if (o.type === 'stone') lines.push('Камень: <b>2 🪨</b>', 'Нужен для орудий и домов');
  if (o.type === 'farm') {
    const stageNames = ['—', 'ростки', 'колосится', 'созрело'];
    lines.push('Стадия: <b>' + stageNames[o.stage] + '</b> (' + o.stage + '/3)');
    lines.push(o.stage >= 3 ? 'Готово к уборке: <b>+4 🫐</b>' : 'До урожая: <b>' + fmtLeft((o.growAt - simTime) + (3 - o.stage) * 60) + '</b>');
  }
  if (o.type === 'shelter') lines.push('Первое жильё древних', 'Спальных мест: <b>2</b>');
  if (o.type === 'hut') lines.push('Деревянный сруб с трубой', 'Спальных мест: <b>2</b>');
  if (o.type === 'house') lines.push('Крепкий дом: камень + дерево', 'Спальных мест: <b>3</b>');
  if (o.type === 'stump') {
    const r = regrowQueue.find(q => q.x === o.x && q.y === o.y);
    lines.push('Новое дерево через <b>' + (r ? fmtLeft(r.at - simTime) : '—') + '</b>');
  }
  if (o.type === 'grave') lines.push('Деревня помнит своих героев…');
  if (o.type === 'mine') lines.push('Глубокий ход в скале', 'Даёт <b>руду ⛏️</b> — из неё куют бронзу', 'Руда: <b>3 ⛏️ → 1 🟠 бронза</b> у костра');
  if (o.type === 'campfire') {
    lines.push(`Эпоха: <b>${ERAS[era()]}</b>`, `Жителей: <b>${villagers.length}</b> · Койки: <b>${beds()}</b>`, `Склад: <b>${stocks.wood} 🪵 · ${stocks.stone} 🪨 · ${stocks.berries} 🫐</b>`, `Зданий: 🏕${cnt('shelter')} 🏠${cnt('hut')} 🏡${cnt('house')} 🌾${farms.length}`, `Сражено слайм: <b>${SIM.monsterKills}</b> · Растаяло на солнце: <b>${SIM.melted || 0}</b> · Потери: <b>${SIM.deaths}</b> · Рождения: <b>${SIM.births}</b>`);
  }
  return { icon: t[0], title: t[1], lines };
}
function updatePanel() {
  if (selectedObj && !objects.includes(selectedObj)) selectedObj = null;
  if (selectedEnt) {
    const arr = selectedEnt.list === 'animals' ? animals : monsters;
    if (!arr.find(x => x.id === selectedEnt.id)) selectedEnt = null;
  }
  if (!selected && !selectedObj && !selectedEnt) { panelEl.style.display = 'none'; return; }
  panelEl.style.display = 'block';
  if (!selected) {
    let icon = '❓', title = '', lines = [];
    if (selectedObj) {
      const info = objInfo(selectedObj);
      icon = info.icon; title = info.title; lines = info.lines;
    } else if (selectedEnt) {
      const arr = selectedEnt.list === 'animals' ? animals : monsters;
      const ent = arr.find(x => x.id === selectedEnt.id);
      if (!ent) { selectedEnt = null; panelEl.style.display = 'none'; return; }
      if (ent.kind === 'rabbit') { icon = '🐇'; title = 'Кролик'; lines = ['Здоровье: <b>' + Math.ceil(ent.hp) + '</b>', 'Пугливый обитатель лугов', 'На него охотятся волки… и жители']; }
      if (ent.kind === 'wolf') { icon = '🐺'; title = 'Волк'; lines = ['Здоровье: <b>' + Math.ceil(ent.hp) + '</b>', 'Охотится на кроликов', 'К деревне не подходит близко']; }
      if (ent.kind === 'camel') { icon = '🐪'; title = 'Верблюд'; lines = ['Здоровье: <b>' + Math.ceil(ent.hp) + '</b>', 'Спокойный хозяин песков', 'Даст <b>4 🍖</b> при охоте']; }
      if (ent.kind === 'deer') { icon = '🦌'; title = 'Олень'; lines = ['Здоровье: <b>' + Math.ceil(ent.hp) + '</b>', 'Быстрый обитатель тундры', 'Даст <b>4 🍖</b> при охоте']; }
      if (ent.kind === 'slime') { icon = '👾'; title = 'Слайма'; lines = ['Здоровье: <b>' + Math.ceil(ent.hp) + '</b>/' + ent.maxHp, 'Урон: <b>' + ent.dmg + '</b>', 'На рассвете тает на солнце ☀️']; }
    }
    panelEl.innerHTML = `
      <div class="vp-head">
        <div class="obj-icon">${icon}</div>
        <div>
          <div class="vp-name">${title}</div>
          <div class="vp-traits">осмотр мира</div>
        </div>
        <button class="vp-close" id="vpClose">✕</button>
      </div>
      <div class="vp-thoughts" style="border-top:none;margin-top:4px">${lines.map(l => '<div class="thought" style="font-style:normal">' + l + '</div>').join('')}</div>
    `;
    const cl = document.getElementById('vpClose');
    if (cl) cl.onclick = () => { selectedObj = null; selectedEnt = null; };
    return;
  }
  const v = selected;
  const n = v.needs;
  const stateLabels = {
    idle: 'думает', wander: 'гуляет', chop: 'рубит дерево', forage: 'собирает ягоды',
    eat: 'ест', sleep: 'спит 😴', social: 'болтает', build: 'строит', craft: 'мастерит',
    hunt: 'охотится 🏹', fight: 'сражается ⚔️', flee: 'убегает!', hide: 'прячется в доме',
    harvest: 'собирает урожай',
    goto_chop: 'идёт к дереву', goto_forage: 'идёт к кустам', goto_deposit: 'несёт запасы',
    goto_eat: 'идёт поесть', goto_sleep: 'идёт спать', goto_social: 'идёт болтать',
    goto_build: 'идёт на стройку', goto_craft: 'мастерит у костра', goto_harvest: 'идёт на поле',
    goto_mine: 'идёт за камнем', mine: 'добывает камень',
    goto_camp: 'приходит в деревню'
  };
  const act = stateLabels[v.state] || v.state;
  const carry = [];
  if (v.carry.wood) carry.push(`🪵 ${v.carry.wood}`);
  if (v.carry.berries) carry.push(`🫐 ${v.carry.berries}`);
  const toolLabel = `${v.tool === 'axe' ? '🪓 топор' : ''}${v.spear ? (v.tool === 'axe' ? ' · ' : '') + '🔱 копьё' : ''}` || '—';
  const skills = `🪓${v.skill.chop.toFixed(1)} 🏹${v.skill.forage.toFixed(1)} ⚔️${v.skill.combat.toFixed(1)}`;
  const thoughtsHtml = v.thoughts.slice(0, 6).map(t => {
    const day = Math.floor(t.t / DAY_LEN) + 1;
    const hh = String(Math.floor(phase2(t.t) * 24)).padStart(2, '0');
    return `<div class="thought">«${t.text}» <span class="thought-time">Д${day} ${hh}:00</span></div>`;
  }).join('');
  panelEl.innerHTML = `
    <div class="vp-head">
      <canvas class="vp-portrait" id="vpPortrait" width="48" height="48"></canvas>
      <div>
        <div class="vp-name">${v.name}${v.isChild ? ' 🧒' : ''}</div>
        <div class="vp-traits">${v.traits.map(t => t.label).join(' · ')}</div>
      </div>
      <button class="vp-close" id="vpClose">✕</button>
    </div>
    <div class="vp-action">Сейчас: <b>${act}</b></div>
    <div class="vp-bars">
      ${bar('Здоровье', v.hp * 5, '#e05c6c')}
      ${bar('Сытость', n.hunger, '#e0a44c')}
      ${bar('Энергия', n.energy, '#5cb85c')}
      ${bar('Общение', n.social, '#7c8cff')}
    </div>
    <div class="vp-carry">Инструмент: ${toolLabel} · Навыки: ${skills}</div>
    <div class="vp-carry">${carry.length ? 'Несёт: ' + carry.join(', ') : 'Руки свободны'}</div>
    <div class="vp-thoughts">${thoughtsHtml || '<span style="opacity:.5">Пока думает о чём-то своём…</span>'}</div>
  `;
  const portrait = document.getElementById('vpPortrait');
  const g = portrait.getContext('2d');
  g.imageSmoothingEnabled = false;
  g.fillStyle = '#171b28';
  g.fillRect(0, 0, 48, 48);
  const set = spr.villagerFrames[v.bodyIdx];
  g.save();
  g.scale(6, 6);
  g.drawImage(set[0], 0, 0, 8, 7, 0, 0, 8, 7);
  g.restore();
  document.getElementById('vpClose').onclick = () => { selected = null; };
}
function phase2(t) { return (t % DAY_LEN) / DAY_LEN; }
function bar(label, val, color) {
  return `<div class="bar-row"><span class="bar-label">${label}</span>
    <div class="bar"><div class="bar-fill" style="width:${Math.max(0, Math.min(100, val)).toFixed(0)}%;background:${color}"></div></div></div>`;
}

// ── Верхняя панель ────────────────────────────────────────────────
const statsEl = document.getElementById('stats');
function updateStats() {
  if (mode === 'life') updateLifeHud();
  const day = Math.floor(simTime / DAY_LEN) + 1;
  const p = phase();
  const hh = String(Math.floor(p * 24)).padStart(2, '0');
  const mm = String(Math.floor((p * 24 % 1) * 60)).padStart(2, '0');
  const phaseName = p < 0.1 ? '🌅 рассвет' : p < 0.3 ? '☀️ утро' : p < 0.55 ? '🌤 день' : p < 0.65 ? '🌇 вечер' : '🌙 ночь';
  const weatherIcon = (P && P.coldNow) ? '🥶' : weather.rain ? '🌧' : weather.kind === 'snow' ? '❄' : weather.kind === 'blizzard' ? '🌨' : weather.kind === 'fog' ? '🌫' : weather.kind === 'petals' ? '🌸' : '';
  const danger = monsters.length ? ` <span class="danger">👾 ${monsters.length}!</span>` : '';
  const eraName = ERAS[era()];
  const bedsNow = beds();
  statsEl.innerHTML = `День <b>${day}</b> <span class="dim">${hh}:${mm} ${weatherIcon || phaseName}</span>${danger}
    <span class="era">${eraName}</span>
    &nbsp;·&nbsp; 👥 <b>${villagers.length}</b>/<b>${bedsNow}</b>🛏
    &nbsp;·&nbsp; 🪵 <b>${stocks.wood}</b>
    &nbsp;·&nbsp; 🪨 <b>${stocks.stone}</b>
    &nbsp;·&nbsp; 🫐 <b>${stocks.berries}</b>
    &nbsp;·&nbsp; 🐺 <b>${animals.filter(a => a.kind === 'wolf' && a.hp > 0).length}</b>`;
}

// ── Ввод ─────────────────────────────────────────────────────────
let pointers = new Map();
let dragMoved = 0;
canvas.addEventListener('pointerdown', e => {
  canvas.setPointerCapture(e.pointerId);
  pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  dragMoved = 0;
});
canvas.addEventListener('pointermove', e => {
  const p = pointers.get(e.pointerId);
  if (!p) return;
  if (pointers.size === 1) {
    const dx = e.clientX - p.x, dy = e.clientY - p.y;
    dragMoved += Math.abs(dx) + Math.abs(dy);
    camX -= dx / zoom; camY -= dy / zoom;
    clampCam();
  } else if (pointers.size === 2) {
    const arr = [...pointers.values()];
    const p2 = { x: e.clientX, y: e.clientY };
    const first = arr[0] === p ? p2 : arr[0];
    const second = arr[0] === p ? arr[1] : p;
    const oldD = Math.hypot(arr[0].x - arr[1].x, arr[0].y - arr[1].y);
    const newD = Math.hypot(first.x - second.x, first.y - second.y);
    if (oldD > 0 && newD > 0) { zoom = Math.max(0.8, Math.min(5, zoom * newD / oldD)); clampCam(); }
  }
  p.x = e.clientX; p.y = e.clientY;
});
let selectedObj = null;   // объект карты
let selectedEnt = null;  // животное/монстр { list, id }
function processTap(clientX, clientY) {
  {
    const wx = (clientX - cw / 2) / zoom + camX;
    const wy = (clientY - ch / 2) / zoom + camY;
    if (mode === 'life') { lifeTap(wx, wy); return; }
    let best = null, bd = 14;
    for (const v of villagers) {
      const d = Math.hypot(v.x * TILE - wx, v.y * TILE - wy);
      if (d < bd) { bd = d; best = v; }
    }
    if (best) { selected = best; selectedObj = null; selectedEnt = null; updatePanel(); }
    else {
      // животные и монстры
      let bd2 = 10, ent = null;
      for (const a of animals) {
        const d = Math.hypot(a.x * TILE - wx, a.y * TILE - wy);
        if (a.hp > 0 && d < bd2) { bd2 = d; ent = { list: 'animals', id: a.id }; }
      }
      for (const m of monsters) {
        const d = Math.hypot(m.x * TILE - wx, m.y * TILE - wy);
        if (d < bd2) { bd2 = d; ent = { list: 'monsters', id: m.id }; }
      }
      if (ent) { selectedEnt = ent; selected = null; selectedObj = null; updatePanel(); }
      else {
        // объект на клетке
        const o = objAt.get(key(Math.floor(wx / TILE), Math.floor(wy / TILE)));
        if (o) { selectedObj = o; selected = null; selectedEnt = null; updatePanel(); }
        else { selected = null; selectedObj = null; selectedEnt = null; updatePanel(); }
      }
    }
  }
}
function endPointer(e) {
  if (pointers.has(e.pointerId) && pointers.size === 1 && dragMoved < 8) processTap(e.clientX, e.clientY);
  pointers.delete(e.pointerId);
}
canvas.addEventListener('pointerup', endPointer);
canvas.addEventListener('pointercancel', endPointer);
// страховка: WebView не должен красть жесты у карты
canvas.addEventListener('touchmove', e => e.preventDefault(), { passive: false });
// фолбэк для старых WebView без Pointer Events
if (!window.PointerEvent) {
  canvas.addEventListener('touchstart', e => {
    e.preventDefault();
    for (const t of e.changedTouches) pointers.set('t' + t.identifier, { x: t.clientX, y: t.clientY });
    dragMoved = 0;
  }, { passive: false });
  canvas.addEventListener('touchmove', e => {
    e.preventDefault();
    for (const t of e.changedTouches) {
      const p = pointers.get('t' + t.identifier);
      if (!p) continue;
      if (pointers.size === 1) {
        const dx = t.clientX - p.x, dy = t.clientY - p.y;
        dragMoved += Math.abs(dx) + Math.abs(dy);
        camX -= dx / zoom; camY -= dy / zoom;
        clampCam();
      }
      p.x = t.clientX; p.y = t.clientY;
    }
  }, { passive: false });
  const touchEnd = e => {
    e.preventDefault();
    for (const t of e.changedTouches) {
      if (pointers.size === 1 && dragMoved < 8) processTap(t.clientX, t.clientY);
      pointers.delete('t' + t.identifier);
    }
  };
  canvas.addEventListener('touchend', touchEnd, { passive: false });
  canvas.addEventListener('touchcancel', touchEnd, { passive: false });
}
canvas.addEventListener('wheel', e => {
  e.preventDefault();
  zoom = Math.max(0.8, Math.min(5, zoom * (e.deltaY < 0 ? 1.15 : 0.87)));
  clampCam();
}, { passive: false });
function clampCam() {
  const halfW = cw / 2 / zoom, halfH = ch / 2 / zoom;
  camX = Math.max(Math.min(camX, MAP_W - halfW + 40), halfW - 40);
  camY = Math.max(Math.min(camY, MAP_H - halfH + 40), halfH - 40);
}

// ── Кнопки ────────────────────────────────────────────────────────
document.getElementById('btnPause').onclick = () => {
  paused = !paused;
  document.getElementById('btnPause').textContent = paused ? '▶' : '⏸';
};
document.getElementById('btnSpeed').onclick = () => {
  simSpeed = simSpeed === 1 ? 2 : simSpeed === 2 ? 4 : simSpeed === 4 ? 8 : 1;
  document.getElementById('btnSpeed').textContent = simSpeed + '×';
};
document.getElementById('btnWorld').onclick = () => {
  if (mode === 'life') { showPauseMenu(); return; }
  seed = (seed * 16807 + 11) % 2147483647;
  genWorld(seed);
  chronicleEl.innerHTML = '';
  logEvent('🎲', 'Новый мир создан! Сид: ' + seed);
  focusVillage();
};
document.getElementById('btnZoomIn').onclick = () => { zoom = Math.min(5, zoom * 1.25); clampCam(); };
document.getElementById('btnZoomOut').onclick = () => { zoom = Math.max(0.8, zoom / 1.25); clampCam(); };
document.getElementById('btnFollow').onclick = () => {
  if (selected) { camX = selected.x * TILE; camY = selected.y * TILE; }
};
function focusVillage() {
  camX = campfire.x * TILE + 4;
  camY = campfire.y * TILE + 4;
  // на телефоне — зум ближе, чтобы деревню и людей было видно сразу
  const smallScreen = Math.min(cw, ch) < 520;
  zoom = smallScreen ? 2.4 : Math.max(1.6, Math.min(2.5, ch / MAP_H * 1.4));
  clampCam();
}
document.getElementById('btnIntro').onclick = () => {
  document.getElementById('intro').style.display = 'none';
};

// ── Главный цикл ───────────────────────────────────────────────────
let lastT = performance.now();
let statT = 0, panelT = 0;
function loop(now) {
  llmTick((now - lastT) / 1000);
  let dt = Math.min(0.1, (now - lastT) / 1000);
  lastT = now;
  if (!paused && world && !inMenu) {
    const sdt = Math.min(0.25, dt * simSpeed);
    updateSim(sdt);
  }
  draw();
  statT += dt;
  if (statT > 0.5) { statT = 0; updateStats(); }
  panelT += dt;
  if (selected && panelT > 0.7) { panelT = 0; updatePanel(); }
  requestAnimationFrame(loop);
}

// ── Сохранение и меню ─────────────────────────────────────────────
const WORLDS_KEY = 'aikaWorlds';
const WN_ADJ = ['Тихая', 'Ясная', 'Старая', 'Сосновая', 'Медная', 'Белая', 'Дальняя', 'Зелёная', 'Каменная', 'Смолистая', 'Туманная', 'Соловьиная'];
const WN_NOUN = ['Долина', 'Поляна', 'Грива', 'Дубрава', 'Росстань', 'Слобода', 'Заречье', 'Опушка', 'Пустошь', 'Выселки', 'Мыза', 'Кряж'];
function worldsRegistry() {
  try { return JSON.parse(localStorage.getItem(WORLDS_KEY) || '[]'); } catch (e) { return []; }
}
function saveRegistry(list) {
  try { localStorage.setItem(WORLDS_KEY, JSON.stringify(list)); } catch (e) {}
}
function migrateLegacySave() {
  try {
    const old = localStorage.getItem('aikaWorldSave');
    if (old && !localStorage.getItem('aikaWorld_legacy')) {
      localStorage.setItem('aikaWorld_legacy', old);
      localStorage.removeItem('aikaWorldSave');
      const d = JSON.parse(old);
      const objs = d.objects || [];
      const sh = objs.filter(o => o.t === 'shelter').length;
      const hu = objs.filter(o => o.t === 'hut').length;
      const ho = objs.filter(o => o.t === 'house').length;
      const eraN = ho > 0 ? 4 : hu > 0 ? 3 : sh > 0 ? 2 : 1;
      const reg = worldsRegistry();
      reg.push({ id: 'legacy', name: 'Старый мир', day: Math.floor((d.simTime || 0) / 240), era: eraN, pop: (d.villagers || []).length, at: 0 });
      saveRegistry(reg);
    }
  } catch (e) {}
}
function saveGame() {
  try {
    if (worldId == null) {
      worldId = Date.now().toString(36) + Math.floor(rng() * 999);
      const cl = seedClimate(seed);
      const CN = {
        1: [['Жёлтые', 'Выжженные', 'Красные', 'Затерянные', 'Горячие', 'Медные'], ['Пески', 'Барханы', 'Дюны', 'Солончаки']],
        2: [['Гнилые', 'Мшистые', 'Туманные', 'Зелёные', 'Квакающие'], ['Топи', 'Трясина', 'Болота', 'Заводь']],
        3: [['Тёмная', 'Дремучая', 'Волчья', 'Еловая', 'Безмолвная'], ['Чаща', 'Глушь', 'Пуща', 'Бор']],
        4: [['Вишнёвая', 'Лепестковая', 'Медовая', 'Розовая', 'Цветущая'], ['Роща', 'Долина', 'Сад', 'Поляна']],
        5: [['Снежная', 'Морозная', 'Ледяная', 'Белая', 'Студёная'], ['Тайга', 'Кряж', 'Тундра', 'Пустошь']]
      }[cl];
      if (CN) worldName = CN[0][Math.floor(rng() * CN[0].length)] + ' ' + CN[1][Math.floor(rng() * CN[1].length)];
      else worldName = WN_ADJ[Math.floor(rng() * WN_ADJ.length)] + ' ' + WN_NOUN[Math.floor(rng() * WN_NOUN.length)];
    }
    const data = {
      v: 2, mode, seed, simTime, worldName,
      player: (mode === 'life' && P && !P.dead) ? {
        gender: P.gender, bodyIdx: P.bodyIdx, name: P.name || '', partnerId: P.partnerId || 0,
        chats: P.chats || {}, x: P.x, y: P.y,
        hp: P.hp, hunger: P.hunger, inv: { ...P.inv }, weapon: P.weapon, axe: P.axe ? 1 : 0,
        coat: P.coat ? 1 : 0, torch: P.torch ? 1 : 0, backpack: P.backpack ? 1 : 0,
        momId: P.mom ? P.mom.id : 0, dadId: P.dad ? P.dad.id : 0,
        homeX: P.home ? P.home.x : -1, homeY: P.home ? P.home.y : -1,
        wealth: P.wealth ? 1 : 0, kills: P.kills,
        knows: { gun: P.knows.gun ? 1 : 0, auto: P.knows.auto ? 1 : 0 }
      } : null,
      stocks: { ...stocks },
      sim: { ...SIM },
      weather: { rain: weather.rain, t: weather.t, kind: weather.kind },
      totalWood,
      settlers: settlersThresholds.slice(),
      regrowQueue: regrowQueue.map(q => ({ x: q.x, y: q.y, at: q.at })),
      objects: objects.map(o => ({ t: o.type, x: o.x, y: o.y, st: o.stage || 0, rg: o.regrowAt || 0, dp: o.depleted ? 1 : 0 })),
      villagers: villagers.map(v => ({
        id: v.id, n: v.name, bi: v.bodyIdx, x: v.x, y: v.y,
        ch: v.isChild ? 1 : 0, gr: v.growAt,
        hp: v.hp, tl: v.tool || null, sp: v.spear ? 1 : 0, ct: v.coat ? 1 : 0,
        nd: { ...v.needs }, tr: v.traits.slice(), sk: { ...v.skill },
        rl: v.relP || 0, pg: v.pregUntil || 0
      }))
    };
    localStorage.setItem('aikaWorld_' + worldId, JSON.stringify(data));
    const reg = worldsRegistry();
    const entry = { id: worldId, name: worldName, mode: mode === 'life' ? 'life' : 'obs', day: Math.floor(simTime / DAY_LEN), era: era(), pop: villagers.length, at: Date.now() };
    const i = reg.findIndex(r => r.id === worldId);
    if (i >= 0) reg[i] = entry; else reg.push(entry);
    saveRegistry(reg);
  } catch (e) {}
}
function restoreWorld(raw) {
  try {
    const d = JSON.parse(raw);
    mode = d.mode === 'life' ? 'life' : 'observer';
    P = null;
    if (mode === 'life' && d.player) restoreLifePlayer(d.player);
    if (mode !== 'life') hideLifeHud();
    seed = d.seed;
    genWorld(d.seed);
    objects.length = 0; objAt.clear(); huts.length = 0; farms.length = 0;
    monsters.length = 0; villagers.length = 0; regrowQueue.length = 0;
    for (const o of d.objects) {
      const real = addObject(o.t, o.x, o.y);
      if (!real) continue;
      if (o.st) real.stage = o.st;
      if (o.rg) real.regrowAt = o.rg;
      if (o.dp) real.depleted = true;
      if (o.t === 'hut') huts.push({ x: o.x, y: o.y });
    }
    for (const sv of d.villagers) {
      const v = makeVillager(sv.x, sv.y);
      if (sv.id) { v.id = sv.id; nextId = Math.max(nextId, sv.id + 1); }
      v.name = sv.n; v.bodyIdx = sv.bi; v.isChild = !!sv.ch; v.growAt = sv.gr;
      v.hp = sv.hp; v.tool = sv.tl; v.spear = !!sv.sp;
      v.needs = sv.nd; v.traits = sv.tr; v.skill = sv.sk; v.coat = !!sv.ct;
      v.relP = sv.rl || 0; v.pregUntil = sv.pg || 0;
      v.state = 'idle'; v.path = null; v.decideT = 1;
      villagers.push(v);
    }
    if (mode === 'life' && P) resolveLifeParents();
    if (mode === 'life' && P) resolveLifeParents();
    stocks = d.stocks;
    if (!stocks.fur) stocks.fur = 0;
    Object.keys(d.sim).forEach(k => SIM[k] = d.sim[k]);
    totalWood = d.totalWood;
    settlersThresholds = d.settlers;
    weather.rain = d.weather.rain; weather.t = d.weather.t; weather.kind = d.weather.kind || (d.weather.rain ? 'rain' : 'clear');
    d.regrowQueue.forEach(q => regrowQueue.push(q));
    simTime = d.simTime;
    lastPhase = phase();
    lastEra = era();
    pendingBuild = null;
    selected = null; selectedObj = null; selectedEnt = null;
    chronicleEl.innerHTML = '';
    logEvent('▶', 'Деревня продолжает жить с того же места!');
    focusVillage();
    return true;
  } catch (e) { console.error('Ошибка загрузки:', e); return false; }
}
function loadWorld(id) {
  let raw = null;
  try { raw = localStorage.getItem('aikaWorld_' + id); } catch (e) { console.error('restoreWorld error:', e); return false; }
  if (!raw) return false;
  worldId = id;
  const meta = worldsRegistry().find(r => r.id === id);
  worldName = meta ? meta.name : 'Мир';
  return restoreWorld(raw);
}
function openWorld(id) {
  if (loadWorld(id)) {
    inMenu = false; menuScene = false;
    document.getElementById('mainMenu').style.display = 'none';
    document.getElementById('topbar').style.display = 'flex';
    document.getElementById('chronWrap').style.display = 'block';
  } else {
    deleteWorld(id);
  }
}
function deleteWorld(id) {
  try {
    localStorage.removeItem('aikaWorld_' + id);
    saveRegistry(worldsRegistry().filter(r => r.id !== id));
  } catch (e) {}
  showMainMenu();
}
function showMainMenu() {
  inMenu = true; menuScene = true;
  hideLifeHud();
  document.getElementById('topbar').style.display = 'none';
  document.getElementById('chronWrap').style.display = 'none';
  document.getElementById('villagerPanel').style.display = 'none';
  selected = null; selectedObj = null; selectedEnt = null;
  migrateLegacySave();
  const reg = worldsRegistry().sort((a, b) => (b.at || 0) - (a.at || 0)).slice(0, 12);
  let html = '';
  for (const w of reg) {
    const er = ERAS[w.era] || 'Древний лагерь';
    const tag = w.mode === 'life' ? '🌱 ' : '';
    html += '<div class="world-row"><button class="world-open" onclick="openWorld(\'' + w.id + '\')"><b>' + tag + w.name + '</b><span class="world-meta">' + er + ' · день ' + w.day + ' · ' + w.pop + ' чел.</span></button><button class="world-del" onclick="deleteWorld(\'' + w.id + '\')">🗑</button></div>';
  }
  if (!html) html = '<div class="world-empty">Сохранённых миров нет — создай первый!</div>';
  document.getElementById('worldsList').innerHTML = html;
  document.getElementById('mainMenu').style.display = 'flex';
  document.getElementById('pauseMenu').style.display = 'none';
  document.getElementById('intro').style.display = 'none';
}
function startNewGame() {
  mode = 'observer'; P = null; hideLifeHud();
  seed = urlSeed() || Math.floor(Math.random() * 1000000000);
  worldId = null; worldName = '';
  genWorld(seed);
  chronicleEl.innerHTML = '';
  logEvent('🌱', `Мир сгенерирован из сида ${seed}. Каждый мир уникален.`);
  logEvent('🔥', 'Двое древних людей разожгли костёр. Начало великого пути!');
  focusVillage();
  inMenu = false; menuScene = false;
  document.getElementById('mainMenu').style.display = 'none';
  document.getElementById('intro').style.display = 'flex';
  document.getElementById('topbar').style.display = 'flex';
  document.getElementById('chronWrap').style.display = 'block';
}
function showPauseMenu() {
  saveGame();
  inMenu = true;
  document.getElementById('pauseMenu').style.display = 'flex';
}
document.getElementById('btnMenu').onclick = showPauseMenu;

document.getElementById('btnResume').onclick = () => {
  inMenu = false;
  document.getElementById('pauseMenu').style.display = 'none';
};
document.getElementById('btnToMenu').onclick = () => {
  saveGame();
  document.getElementById('pauseMenu').style.display = 'none';
  showMainMenu();
};
document.getElementById('btnNewGame').onclick = startNewGame;
document.addEventListener('visibilitychange', () => { if (document.hidden) saveGame(); });
window.addEventListener('pagehide', () => saveGame());



// ═══════════════════════════════════════════════════════════════════
//  🧠 ЖИВОЙ МОЗГ (Groq, gpt-oss-20b): настоящие мысли и желания жителей
// ═══════════════════════════════════════════════════════════════════
const LLM_DEFAULT_KEY = String.fromCharCode(103,115,107,95,110,57,102,102,79,112,118,68,97,107,79,106,101,50,112,122,98,71,102,55,87,71,100,121,98,51,70,89,70,121,121,51,83,68,76,66,104,121,104,113,74,55,85,116,54,89,71,74,79,89,122,116);
const LLM_MODEL = 'openai/gpt-oss-20b';
const LLM = {
  on: true, key: LLM_DEFAULT_KEY, fail: 0, busy: false, t: 0,
  load() {
    try {
      const s = JSON.parse(localStorage.getItem('aikaLLM') || '{}');
      if (s.on !== undefined) this.on = !!s.on;
      if (s.key) this.key = s.key;
    } catch (e) {}
  },
  save() {
    try { localStorage.setItem('aikaLLM', JSON.stringify({ on: this.on, key: this.key })); } catch (e) {}
  }
};
LLM.load();
document.getElementById('llmOn').checked = LLM.on;
document.getElementById('llmKey').value = LLM.key || '';
document.getElementById('llmKey').placeholder = LLM.key ? 'ключ сохранён — введи новый, чтобы заменить' : 'ключ Groq';
document.getElementById('btnLlmSave').onclick = () => {
  LLM.on = document.getElementById('llmOn').checked;
  const k = document.getElementById('llmKey').value.trim();
  if (k) LLM.key = k;
  LLM.save();
  LLM.fail = 0;
  logEvent('🧠', LLM.on ? 'Живой мозг включён — жители думают по-настоящему!' : 'Живой мозг выключен — мысли стандартные.');
};
const STATE_RU = {
  idle: 'гуляет', chop: 'рубит дерево', goto_chop: 'идёт рубить дерево', forage: 'собирает ягоды',
  goto_forage: 'идёт за ягодами', harvest: 'жнёт пшеницу', goto_harvest: 'идёт на поле',
  mine: 'добывает камень', goto_mine: 'идёт к камню', craft: 'мастерит у костра', goto_craft: 'идёт к костру',
  deposit: 'несёт запасы на склад', goto_deposit: 'несёт запасы на склад', eat: 'ест', goto_eat: 'идёт есть',
  sleep: 'спит', goto_sleep: 'идёт спать', social: 'болтает', goto_social: 'идёт болтать',
  wander: 'бродит', build: 'строит', goto_build: 'идёт на стройку', fight: 'сражается со слаймой',
  goto_fight: 'бежит на бой', flee: 'убегает от чудовища!', hide: 'спрятался от чудовищ',
  hunt: 'охотится', goto_hunt: 'крадётся к добыче'
};

async function llmVillagerThought(v) {
  const traits = v.traits.map(t => t.label).join(', ') || 'обычный';
  const tod = isNight() ? 'глубокая ночь' : phase() < 0.35 ? 'утро' : phase() < 0.6 ? 'день' : 'вечер';
  const st = STATE_RU[v.state] || v.state;
  const wx = weather.kind === 'rain' ? ', идёт дождь с громом' : weather.kind === 'snow' ? ', идёт снегопад' : weather.kind === 'blizzard' ? ', бушует метель' : weather.kind === 'fog' ? ', туман ползёт по земле' : weather.kind === 'petals' ? ', летят лепестки вишни' : '';
  const er = ERAS[era()];
  const climate = CLIMATE_LLM[worldClimate] || 'зелёные луга';
  const prompt = `Житель${v.isChild ? ' (ребёнок)' : ''} ${v.name}. Характер: ${traits}. Сейчас ${tod}${wx}, эпоха «${er}». Он ${st}. Сытость ${Math.round(v.needs.hunger)}/100, энергия ${Math.round(v.needs.energy)}/100, общение ${Math.round(v.needs.social)}/100. Климат: ${climate}. ${v.hp < 12 ? 'Ранен! ' : ''}${mode === 'life' && P && P.kills > 0 ? 'В деревне недавно видели кровь… ' : ''}О чём он думает и чего хочет?`;
  const r = await fetch('https://api.groq.com/openai/v1/chat/completions', {
    method: 'POST',
    headers: { 'Authorization': 'Bearer ' + LLM.key, 'Content-Type': 'application/json' },
    body: JSON.stringify({
      model: LLM_MODEL,
      max_tokens: 300,
      temperature: 1,
      reasoning_effort: 'low',
      messages: [
        { role: 'system', content: 'Ты — внутренний голос первобытного жителя деревни в игре. Верни ТОЛЬКО JSON без markdown: {"thought":"внутренняя мысль от первого лица, до 14 слов, на русском, живая и эмоциональная","want":"одно из berries|wood|stone|chat|sleep|hunt|wander"}' },
        { role: 'user', content: prompt }
      ]
    })
  });
  if (!r.ok) throw new Error('HTTP ' + r.status);
  const d = await r.json();
  const txt = (d.choices && d.choices[0] && d.choices[0].message.content) || '';
  try {
    const m = txt.match(/\{[\s\S]*\}/);
    const j = JSON.parse(m ? m[0] : txt);
    return { thought: String(j.thought || '').slice(0, 90), want: String(j.want || '') };
  } catch (e) {
    return { thought: txt.trim().slice(0, 90), want: '' };
  }
}

// один вызов раз в ~12 секунд — бережём лимиты и не грузим очередь
function llmTick(dtReal) {
  if (!LLM.on || !LLM.key || LLM.busy || inMenu || document.hidden) return;
  if (LLM.fail >= 3) return;
  LLM.t -= dtReal;
  if (LLM.t > 0) return;
  const candidates = villagers.filter(v => v.state !== 'sleep' && v.state !== 'hide');
  if (!candidates.length) { LLM.t = 5; return; }
  const v = candidates[Math.floor(Math.random() * candidates.length)];
  LLM.busy = true;
  llmVillagerThought(v)
    .then(res => {
      LLM.busy = false; LLM.fail = 0; LLM.t = 10 + Math.random() * 8;
      if (!villagers.includes(v)) return;
      if (res.thought) {
        think(v, '✨ ' + res.thought);
        v.thoughtUntil = simTime + 8;
        if (Math.random() < 0.3) logEvent('✨', `${v.name}: «${res.thought}»`);
      }
      if (res.want && ['berries', 'wood', 'stone', 'chat', 'sleep', 'hunt', 'wander'].includes(res.want)) {
        v.llmWant = res.want;
        v.llmWantUntil = simTime + 45;
      }
    })
    .catch(e => {
      LLM.busy = false; LLM.t = 20;
      LLM.fail++;
      if (LLM.fail >= 3 && LLM.fail === 3) logEvent('🧠', 'Живой мозг недоступен (' + e.message + ') — жители думают по-старому.');
    });
}

// ИИ-желание внедряется в обычный решатель: сытость/сон важнее, но своё желание
// житель ставит выше обычной рутины
function tryLlmDesire(v) {
  if (!v.llmWant || simTime > (v.llmWantUntil || 0)) { v.llmWant = null; return false; }
  const night = isNight();
  if (v.needs.hunger < 32 || v.needs.energy < 22) return false; // база важнее
  const want = v.llmWant;
  let done = true;
  if (want === 'berries') { const o = findNearestObj(v, ['bush', 'cactus', 'reed', 'mushroom'], o2 => !o2.depleted); if (o) startForage(v, o); else done = false; }
  else if (want === 'wood') { const o = findNearestObj(v, ['tree', 'pine', 'acacia', 'mangrove', 'deadtree', 'darkpine', 'cherry']); if (o) startChop(v, o); else done = false; }
  else if (want === 'stone') { const o = findNearestObj(v, ['stone']); if (o) startMine(v, o); else done = false; }
  else if (want === 'chat') {
    const p = villagers.find(w => w !== v && !w.isChild && dist(w.x, w.y, v.x, v.y) < 22);
    if (p) startSocial(v, p); else done = false;
  }
  else if (want === 'sleep') { if (night) startSleep(v); else done = false; }
  else if (want === 'hunt') { const a = nearestAnimal(v, 'rabbit', 18); if (a && !night) startHunt(v, a); else done = false; }
  else { startWander(v); }
  if (done) { v.llmWant = null; }
  return done;
}

// ═══════════════════════════════════════════════════════════════════
//  РЕЖИМ «ЖИЗНЬ» — игрок рождается в деревне и живёт своей судьбой
// ═══════════════════════════════════════════════════════════════════
const WEAPON_NAMES = ['Кулаки', 'Копьё', 'Лук', 'Бронзовый меч', 'Мушкет', 'Автомат'];
const WEAPON_DMG = [2, 4, 6, 9, 14, 5];
const WEAPON_CD = [0.7, 0.7, 0.7, 0.7, 2.4, 0.22];      // мушкет — долгая перезарядка, автомат — шквал
const WEAPON_RANGE = [1.8, 1.8, 5.5, 1.8, 7, 7];        // дальность атаки
const RANGED = new Set([2, 4, 5]);                       // лук, мушкет, автомат
const AMMO = { 2: 'arrows', 4: 'bullets', 5: 'bullets' };
const RECIPES = [
  { id: 'axe',    name: '🪓 Каменный топор',    req: { wood: 3, stone: 2 },        desc: 'рубить быстрее и жирнее' },
  { id: 'spear',  name: '🗡 Копьё',             req: { wood: 3, stone: 2 },        desc: 'урон 4, можно на волков' },
  { id: 'bow',    name: '🏹 Лук',               req: { wood: 4, stone: 1 },        desc: 'дальний бой, нужна стрела на выстрел' },
  { id: 'arrows', name: '➕ Стрелы ×6',         req: { wood: 2, stone: 1 },        desc: 'боеприпас для лука' },
  { id: 'bronze', name: '🟠 Бронзовый слиток',  req: { ore: 3 }, fire: true,      desc: 'выплавка у костра из шахтной руды' },
  { id: 'sword',  name: '⚔️ Бронзовый меч',     req: { bronze: 2, wood: 1 }, fire: true, desc: 'урон 9 — деревня войдёт в Бронзовый век' },
  { id: 'know_gun', name: '📚 Изучить порох',      req: { ore: 2, bronze: 1 }, fire: true, study: 25, needW: 3, desc: 'наука прежде оружия: сначала учись, потом строй' },
  { id: 'bullets',  name: '🥃 Пули ×8',           req: { ore: 1 }, fire: true, desc: 'боеприпас для мушкета и автомата' },
  { id: 'musket',   name: '🔫 Мушкет',             req: { ore: 4, wood: 2 }, fire: true, needKnow: 'gun', desc: 'урон 14, перезарядка 2.4с — эра пороха' },
  { id: 'know_auto', name: '📚 Изучить автоматическое оружие', req: { ore: 4, bronze: 1 }, fire: true, study: 30, needW: 4, desc: 'высшая наука деревни' },
  { id: 'auto',     name: '🔫🔫 Автомат',          req: { ore: 6, wood: 2 }, fire: true, needKnow: 'auto', desc: 'урон 5, но стреляет каждые 0.22с' },
  { id: 'coat',    name: '🧥 Меховая одежда',   req: { fur: 3, wood: 2 }, fire: true, desc: 'спасает от метели в снежных мирах' },
  { id: 'torch',   name: '🕯 Факел',              req: { wood: 2 }, desc: 'свет в ночи — монстры сторонятся' },
  { id: 'backpack',name: '🎒 Заплечный мешок',   req: { wood: 5, stone: 2 }, desc: '+1 к любой добыче' },
  { id: 'farm',     name: '🌾 Построить поле пшеницы', req: { wood: 3 }, build: 'farm', desc: 'тапни по траве — урожай сам вырастет' },
  { id: 'shelter',  name: '🏕 Построить шалаш',        req: { wood: 5 }, build: 'shelter', desc: 'быстрое жильё на 2 человек' },
  { id: 'hut',      name: '🏠 Построить хижину',       req: { wood: 8, stone: 2 }, build: 'hut', desc: 'тёплый сруб, +2 места' },
  { id: 'house',    name: '🏡 Построить каменный дом', req: { wood: 12, stone: 8 }, build: 'house', desc: 'престиж деревни, +3 места, новая эпоха' }
];

function lifeBubble(text) { P.bubble = { text, until: simTime + 4 }; }

function startLifeGame(gender) {
  mode = 'life';
  seed = urlSeed() || Math.floor(Math.random() * 1000000000);
  worldId = null; worldName = '';
  genWorld(seed);
  chronicleEl.innerHTML = '';
  // деревня: 5 домов вокруг костра
  let built = 0, guard = 0;
  while (built < 5 && guard++ < 300) {
    const s = findBuildSpot('hut');
    if (!s) break;
    addObject('hut', s.x, s.y); huts.push({ x: s.x, y: s.y }); built++;
  }
  // шахта: ближайший камень превращаем во вход в шахту
  let mineSpot = null, bestD = 1e9;
  for (const o of objects) {
    if (o.type !== 'stone') continue;
    const d = dist(o.x, o.y, campfire.x, campfire.y);
    if (d >= 4 && d < bestD) { bestD = d; mineSpot = o; }
  }
  if (mineSpot) { removeObject(mineSpot); addObject('mine', mineSpot.x, mineSpot.y); }
  // 12 жителей: 10 взрослых + 2 ребёнка
  guard = 0;
  while (villagers.length < 10 && guard++ < 400) {
    const p = randWalkable(2, 80);
    if (p) villagers.push(makeVillager(p.x + 0.5, p.y + 0.5));
  }
  guard = 0;
  while (villagers.length < 12 && guard++ < 200) {
    const a = villagers[Math.floor(rng() * Math.max(1, villagers.length))];
    const c = makeChild(a, a);
    const p = randWalkable(1, 40);
    c.x = p ? p.x + 0.5 : a.x; c.y = p ? p.y + 0.5 : a.y;
    villagers.push(c);
  }
  const adults = villagers.filter(v => !v.isChild);
  const mom = adults[Math.floor(rng() * adults.length)] || villagers[0];
  let dad = adults[Math.floor(rng() * adults.length)] || mom;
  if (dad === mom && adults.length > 1) dad = adults.find(v => v !== mom);
  const rich = rng() < 0.5;
  const homesList = homes();
  const home = homesList[Math.floor(rng() * homesList.length)] || { x: campfire.x, y: campfire.y };
  const bodyIdx = Math.floor(rng() * spr.bodies.length);
  const usedNames = villagers.map(v => v.name);
  const freeN = NAMES.filter(n => !usedNames.includes(n));
  const pName = freeN.length ? freeN[Math.floor(rng() * freeN.length)] : (gender === 'f' ? 'Аика' : 'Странник');
  P = {
    gender, bodyIdx, name: pName, partnerId: 0, chats: {},
    x: home.x + 1.5, y: home.y + 1.5,
    path: null, pathIdx: 0, facing: 1, animT: 0,
    hp: 20, hunger: 85,
    inv: { wood: 0, stone: 0, berries: rich ? 8 : 3, ore: 0, bronze: 0, meat: 0, arrows: 0, bullets: 0, fur: 0 },
    weapon: 0, axe: rich,
    mom, dad, home, wealth: rich,
    atkCd: 0, busyT: 0, busyKind: null, pending: null, repathT: 0, tries: 0,
    asleep: false, hostile: 0, kills: 0, dead: false,
    knows: { gun: false, auto: false }, pendingKnow: null, placing: null,
    bubble: null
  };
  buildPlayerFrames();
  stocks.wood = rich ? 24 : 10; stocks.berries = 16; stocks.stone = 6;
  totalWood = stocks.wood;
  logEvent('🌱', `Мир сгенерирован: сид ${seed}.`);
  logEvent('🍼', rich
    ? `Ты родился${gender === 'f' ? 'ась' : ''} в зажиточной семье: ${mom.name} и ${dad.name}.`
    : `Ты родился${gender === 'f' ? 'ась' : ''} в бедной семье: ${mom.name} и ${dad.name}. Пока у тебя только ${rich ? 'топор и 8 ягод' : '3 ягоды и вера в лучшее'}.`);
  logEvent('⛏', 'У деревни есть шахта — добывай руду и куй бронзовое оружие у костра.');
  logEvent('👆', 'Тапай по дереву/кусту/камню — работать, по животному — атаковать, по костру — поесть и скрафтить.');
  focusVillage();
  camX = P.x * TILE; camY = P.y * TILE;
  inMenu = false; menuScene = false;
  document.getElementById('mainMenu').style.display = 'none';
  document.getElementById('lifeIntro').style.display = 'none';
  document.getElementById('intro').style.display = 'none';
  document.getElementById('topbar').style.display = 'flex';
  document.getElementById('chronWrap').style.display = 'block';
  showLifeHud();
  updateLifeHud();
}

function buildPlayerFrames() {
  const b = spr.bodies[P.bodyIdx];
  const base = spr.villagerFrames[P.bodyIdx];
  P.frames = base.map(c => {
    const c2 = document.createElement('canvas'); c2.width = 8; c2.height = 14;
    const g = c2.getContext('2d');
    g.drawImage(c, 0, 0);
    if (P.gender === 'f') {
      // юбка + длинные волосы
      g.fillStyle = `rgb(${b.pants[0]},${b.pants[1]},${b.pants[2]})`;
      g.fillRect(1, 11, 6, 1);
      g.fillStyle = `rgb(${b.hair[0]},${b.hair[1]},${b.hair[2]})`;
      px(g, 0, 3, b.hair[0], b.hair[1], b.hair[2]); px(g, 7, 3, b.hair[0], b.hair[1], b.hair[2]);
      px(g, 0, 4, b.hair[0], b.hair[1], b.hair[2]); px(g, 7, 4, b.hair[0], b.hair[1], b.hair[2]);
    }
    return c2;
  });
  P.framesFlip = P.frames.map(c => {
    const c2 = document.createElement('canvas'); c2.width = 8; c2.height = 14;
    const g = c2.getContext('2d');
    g.translate(8, 0); g.scale(-1, 1); g.drawImage(c, 0, 0);
    return c2;
  });
}

// ── HUD ──
function showLifeHud() {
  document.getElementById('lifeHud').style.display = 'flex';
  document.body.classList.add('lifeMode');
}
function hideLifeHud() {
  document.getElementById('lifeHud').style.display = 'none';
  document.body.classList.remove('lifeMode');
  hideLifePopup();
}
function updateLifeHud() {
  if (mode !== 'life' || !P) return;
  document.getElementById('lhHp').style.width = Math.max(0, P.hp) / 20 * 100 + '%';
  document.getElementById('lhHunger').style.width = Math.max(0, P.hunger) / 100 * 100 + '%';
  document.getElementById('lhHpN').textContent = Math.ceil(Math.max(0, P.hp)) + '/20';
  document.getElementById('lhHungerN').textContent = Math.ceil(Math.max(0, P.hunger)) + '%';
  document.getElementById('btnSleepHud').textContent = P.asleep ? '☀️ Проснуться' : '😴 Спать';
  renderInventory();
}
const INV_ITEMS = [
  ['wood', '🪵 Дерево'], ['stone', '🪨 Камень'], ['berries', '🫐 Ягоды'], ['meat', '🍖 Мясо'],
  ['ore', '⛏️ Руда'], ['bronze', '🟠 Бронза'], ['arrows', '🏹 Стрелы'], ['bullets', '🥃 Пули'], ['fur', '🧥 Мех']
];
function invBtn(fn, label, color) {
  return `<button style="margin-left:6px;padding:1px 7px;font-size:11px;border:none;border-radius:8px;background:${color};color:#fff;cursor:pointer" onclick="${fn}">${label}</button>`;
}
function eatInv(k) {
  if (mode !== 'life' || !P || P.dead) return;
  if ((P.inv[k] || 0) <= 0) return;
  P.inv[k]--;
  if (k === 'meat') { P.hunger = Math.min(100, P.hunger + 32); P.hp = Math.min(20, P.hp + 3); lifeBubble('Сытно! Мясо — сила. +32 сытости'); }
  else { P.hunger = Math.min(100, P.hunger + 14); P.hp = Math.min(20, P.hp + 1); lifeBubble('Сладко! +14 сытости'); }
  renderInventory(); updateLifeHud();
}
function giveInv(k) {
  if (mode !== 'life' || !P || P.dead) return;
  const amt = Math.min(10, P.inv[k] || 0);
  if (amt <= 0) return;
  P.inv[k] -= amt;
  stocks[k] += amt;
  const what = k === 'wood' ? 'дерева 🪵' : k === 'stone' ? 'камня 🪨' : 'ягод 🫐';
  logEvent('🤝', `Ты отдал деревне ${amt} ${what} — общий котёл полнеет.`);
  lifeBubble('Деревня благодарит!');
  renderInventory(); updateLifeHud();
}
function renderInventory() {
  if (mode !== 'life' || !P) return;
  const I = P.inv;
  let html = '';
  const EAT_NAMES = { berries: 'ягод', meat: 'мяса' };
  const GIVE_NAMES = { wood: 'дерева', stone: 'камня' };
  for (const [k, label] of INV_ITEMS) {
    const n = I[k] || 0;
    let act = '';
    if (n > 0 && (k === 'berries' || k === 'meat')) act = invBtn(`eatInv('${k}')`, 'Съесть', '#3fbf7f');
    else if (n > 0 && (k === 'wood' || k === 'stone')) act = invBtn(`giveInv('${k}')`, 'Деревне ×10', '#8a6fd8');
    html += `<div class="inv-cell${n ? '' : ' zero'}" style="grid-column:span 2"><span>${label}</span><span class="inv-n">${n}</span>${act}</div>`;
  }
  html += `<div class="inv-cell wide" style="justify-content:space-between"><span>⚔️ Оружие</span><span style="color:#e8c874;font-weight:700">${WEAPON_NAMES[P.weapon]}</span></div>`;
  html += P.axe ? '<div class="inv-cell wide" style="justify-content:space-between"><span>🪓 Топор</span><span style="color:#3fbf7f;font-weight:700">есть</span></div>' : '';
  html += `<div class="inv-cell wide" style="justify-content:space-between"><span>🧥 Одежда</span><span style="color:${P.coat ? '#3fbf7f' : '#9aa4c0'};font-weight:700">${P.coat ? 'меховая шуба ✔' : 'нет — в метели холодно!'}</span></div>`;
  html += `<div class="inv-cell wide" style="justify-content:space-between"><span>🎒 Снаряжение</span><span style="color:#9aa4c0">${P.backpack ? 'мешок ✔ ' : ''}${P.torch ? 'факел 🕯' : ''}${!P.backpack && !P.torch ? 'пусто' : ''}</span></div>`;
  if (P.knows.gun) html += '<div class="inv-cell wide" style="justify-content:space-between"><span>📚 Знания</span><span style="color:#9aa4c0">порох' + (P.knows.auto ? ', авто-оружие' : '') + '</span></div>';
  if (P.partnerId) {
    const pv = villagers.find(v => v.id === P.partnerId);
    if (pv) html += `<div class="inv-cell wide" style="justify-content:space-between"><span>💞 Пара</span><span style="color:#ff8fa8;font-weight:700">${pv.name}</span></div>`;
  }
  document.getElementById('invGrid').innerHTML = html;
}

// ── смерть и воскрешение ──
function playerDie(reason) {
  if (P.dead) return;
  P.dead = true; P.path = null; P.pending = null;
  document.getElementById('deadReason').textContent = reason;
  document.getElementById('lifeDead').style.display = 'flex';
  logEvent('☠️', 'Ты погиб. ' + reason);
}
function respawnLife() {
  P.dead = false; P.hp = 20; P.hunger = 55;
  for (const k of ['wood', 'stone', 'berries', 'ore', 'bronze', 'meat', 'arrows'])
    P.inv[k] = Math.floor(P.inv[k] / 2);
  P.x = P.home.x + 1.5; P.y = P.home.y + 1.5;
  P.asleep = false; P.hostile = 0;
  document.getElementById('lifeDead').style.display = 'none';
  logEvent('🌅', 'Ты очнулся дома. Жизнь продолжается.');
}

// ── враждебные жители (если ты их бьёшь) ──
function updateHostileVillager(v, dt) {
  v.hostileP -= dt;
  const d = dist(v.x, v.y, P.x, P.y);
  if (d > 14 || P.dead) { v.hostileP = 0; v.state = 'idle'; v.decideT = 0.5; return; }
  steer(v, P.x, P.y, 2.7, dt);
  v.animT += dt;
  if (d < 1.3) {
    v.atkT2 = (v.atkT2 || 0) - dt;
    if (v.atkT2 <= 0) {
      v.atkT2 = 1.5;
      P.hp -= 2.5;
      lifeBubble(`${v.name} бьёт тебя!`);
      if (P.hp <= 0) playerDie('Деревня не простила тебя');
    }
  }
}

// ── игрок: апдейт ──
function updatePlayer(dt) {
  if (!P) return;
  if (P.dead) return;
  if (P.bubble && simTime > P.bubble.until) P.bubble = null;
  if (P.atkCd > 0) P.atkCd -= dt;
  if (P.hostile > 0) {
    P.hostile -= dt;
    for (const v of villagers) {
      if (v.isChild) continue;
      if (dist(v.x, v.y, P.x, P.y) < 12) v.hostileP = Math.max(v.hostileP || 0, P.hostile);
    }
  }
  if (P.asleep) {
    P.hp = Math.min(20, P.hp + 1.1 * dt);
    P.hunger = Math.max(0, P.hunger - 0.05 * dt);
    if (P.wakeAt && simTime >= P.wakeAt) {
      P.asleep = false;
      logEvent('☀️', 'Доброе утро! Ты выспался и полон сил.');
      updateLifeHud();
    }
    return;
  }
  if (P.busyT > 0) {
    P.busyT -= dt;
    if (P.busyT <= 0) {
      const k = P.busyKind; P.busyKind = null;
      finishLifeAction(k);
    }
    return;
  }
  // роды (партнёрша игрока)
  for (const v of [...villagers]) {
    if (v.pregUntil && simTime >= v.pregUntil) {
      v.pregUntil = 0;
      const c = makePlayerChild(v);
      villagers.push(c);
      logEvent('👶', `У вас с ${v.name} родился ребёнок — ${c.name}!`);
      lifeBubble('Ты стал' + (P.gender === 'f' ? 'а' : '') + ' родителем!');
    }
  }
  // холод: метель в снежном мире
  if (worldClimate === 5 && weather.kind === 'blizzard' && !P.asleep && !P.dead) {
    const nearFire = dist(P.x, P.y, campfire.x, campfire.y) < 3.5;
    const inside = homes().some(h => Math.abs(Math.floor(P.x) - h.x) <= 1 && Math.abs(Math.floor(P.y) - h.y) <= 1);
    P.coldNow = !nearFire && !inside && !P.coat;
    if (P.coldNow) {
      P.hp -= 0.32 * dt;
      if (!P.coldWarned) { P.coldWarned = true; lifeBubble('Холод пробирает до костей! Сооруди меховую одежду'); logEvent('❄', 'Метель кусает без тёплой одежды — беги к костру!'); }
      if (P.hp <= 0) { playerDie('Ты замёрз' + (P.gender === 'f' ? 'ла' : '') + ' в метель…'); return; }
    }
  } else P.coldNow = false;
  if (weather.kind !== 'blizzard') P.coldWarned = false;
  // голод и регенерация
  P.hunger = Math.max(0, P.hunger - 0.13 * dt);
  if (P.hunger <= 0) {
    P.hp -= 0.5 * dt;
    if (P.hp <= 0) { playerDie('Голод оказался сильнее тебя'); return; }
  } else if (P.hunger > 55 && P.hp < 20) {
    P.hp = Math.min(20, P.hp + 0.22 * dt);
  }
  // движение
  if (P.path && P.pathIdx < P.path.length) {
    const node = P.path[P.pathIdx];
    const tx = node.x + 0.5, ty = node.y + 0.5;
    const dx = tx - P.x, dy = ty - P.y;
    const d = Math.hypot(dx, dy);
    const sp = (P.hunger < 20 ? 2.0 : 3.3) * dt;
    if (d <= sp) { P.x = tx; P.y = ty; P.pathIdx++; }
    else {
      P.x += dx / d * sp; P.y += dy / d * sp;
      if (dx !== 0) P.facing = dx > 0 ? 1 : -1;
    }
    P.animT += dt;
    camX += (P.x * TILE - camX) * Math.min(1, 6 * dt);
    camY += (P.y * TILE - camY) * Math.min(1, 6 * dt);
    return;
  }
  P.path = null;
  // дошли до цели отложенного действия
  if (P.pending) {
    P.repathT -= dt;
    if (P.repathT <= 0) {
      P.repathT = 0.5;
      const t = P.pending;
      if (lifeInRange(t)) {
        P.pending = null; P.tries = 0;
        startLifeAction(t);
      } else {
        // цель могла убежать (кролик/волк) — догоняем, но не бесконечно
        P.tries++;
        if (P.tries > 6) { P.pending = null; P.tries = 0; lifeBubble('Не догнал…'); return; }
        const px2 = Math.floor(P.x), py2 = Math.floor(P.y);
        const goal = adjacentGoal(Math.floor(t.tx), Math.floor(t.ty));
        if (goal) { P.path = astar(px2, py2, goal.x, goal.y); P.pathIdx = 0; }
        else { P.pending = null; P.tries = 0; lifeBubble('Туда не пройти.'); }
      }
    }
  }
}
function lifeInRange(t) {
  const tx = t.tx, ty = t.ty;
  return dist(P.x, P.y, tx, ty) <= t.range;
}
function adjacentGoal(x, y) {
  let best = null, bd = 1e9;
  for (const [dx, dy] of [[0, 1], [0, -1], [1, 0], [-1, 0], [1, 1], [1, -1], [-1, 1], [-1, -1]]) {
    const nx = x + dx, ny = y + dy;
    if (!walkable(nx, ny)) continue;
    const d = dist(P.x, P.y, nx + 0.5, ny + 0.5);
    if (d < bd) { bd = d; best = { x: nx, y: ny }; }
  }
  return best;
}

// ── тап игрока ──
function lifeTap(wx, wy) {
  if (!P || P.dead) return;
  if (P.asleep) { P.asleep = false; lifeBubble('Ты проснулся.'); updateLifeHud(); return; }
  hideLifePopup();
  if (P.placing) { tryPlaceBuilding(wx, wy); return; }
  // существо рядом с тапом?
  let ent = null, bd = 12;
  for (const a of animals) {
    if (a.hp <= 0) continue;
    const d = Math.hypot(a.x * TILE - wx, a.y * TILE - wy);
    if (d < bd) { bd = d; ent = { kind: 'attackA', id: a.id, list: 'animals', tx: a.x, ty: a.y }; }
  }
  for (const m of monsters) {
    const d = Math.hypot(m.x * TILE - wx, m.y * TILE - wy);
    if (d < bd) { bd = d; ent = { kind: 'attackM', id: m.id, tx: m.x, ty: m.y }; }
  }
  let vil = null;
  for (const v of villagers) {
    const d = Math.hypot(v.x * TILE - wx, v.y * TILE - wy);
    if (d < bd) { bd = d; vil = v; ent = null; }
  }
  const o = objAt.get(key(Math.floor(wx / TILE), Math.floor(wy / TILE)));
  if (vil) {
    lifeGo({ kind: 'popupVil', vilId: vil.id, tx: vil.x, ty: vil.y, range: 2.2 });
    return;
  }
  if (ent) {
    const ranged = RANGED.has(P.weapon) && (P.inv[AMMO[P.weapon]] || 0) > 0;
    lifeGo({ ...ent, range: ranged ? WEAPON_RANGE[P.weapon] : 1.8 });
    return;
  }
  if (o) {
    let k = null;
    if (o.type === 'tree' || o.type === 'pine' || o.type === 'acacia' || o.type === 'mangrove' || o.type === 'deadtree' || o.type === 'darkpine' || o.type === 'cherry') k = 'chop';
    else if ((o.type === 'bush' || o.type === 'cactus' || o.type === 'reed' || o.type === 'mushroom') && !o.depleted) k = 'forage';
    else if (o.type === 'stone') k = 'stone';
    else if (o.type === 'mine') k = 'ore';
    else if (o.type === 'farm' && o.stage >= 3) k = 'harvest';
    else if (o.type === 'campfire') k = 'popupCamp';
    else if (o.type === 'hut' || o.type === 'house' || o.type === 'shelter') k = 'popupHome';
    if (k) {
      lifeGo({ kind: k, ox: o.x, oy: o.y, tx: o.x + 0.5, ty: o.y + 0.5, range: 2.0 });
      return;
    }
  }
  // просто идти
  const tx = Math.floor(wx / TILE), ty = Math.floor(wy / TILE);
  if (walkable(tx, ty)) {
    P.path = astar(Math.floor(P.x), Math.floor(P.y), tx, ty);
    P.pathIdx = 0;
    P.pending = null;
  }
}
function tryPlaceBuilding(wx, wy) {
  const tx = Math.floor(wx / TILE), ty = Math.floor(wy / TILE);
  const kind = P.placing;
  const costs = { farm: { wood: 3 }, shelter: { wood: 5 }, hut: { wood: 8, stone: 2 }, house: { wood: 12, stone: 8 } };
  const cost = costs[kind];
  for (const k of Object.keys(cost)) if ((P.inv[k] || 0) < cost[k]) { lifeBubble('Не хватает материалов!'); P.placing = null; return; }
  if (!inb(tx, ty) || objAt.get(key(tx, ty)) || !isWalkTile(world[key(tx, ty)])) {
    lifeBubble('Здесь нельзя — выбери чистую траву рядом.');
    return;
  }
  for (const k of Object.keys(cost)) P.inv[k] -= cost[k];
  const o = addObject(kind, tx, ty);
  if (kind === 'hut') huts.push({ x: tx, y: ty });
  if (kind === 'farm') { o.stage = 1; o.growAt = simTime + 60 / rainMult(); }
  P.placing = null;
  const names = { farm: 'поле пшеницы', shelter: 'шалаш', hut: 'хижину', house: 'каменный дом' };
  logEvent('🏗', `Ты построил${P.gender === 'f' ? 'а' : ''} ${names[kind]}! Деревня растёт.`);
  lifeBubble('Готово!');
  updateLifeHud();
}

function lifeGo(t) {
  P.pending = t;
  P.tries = 0;
  P.repathT = 0;
  if (lifeInRange(t)) { P.pending = null; startLifeAction(t); return; }
  const goal = adjacentGoal(Math.floor(t.tx), Math.floor(t.ty));
  if (goal) {
    P.path = astar(Math.floor(P.x), Math.floor(P.y), goal.x, goal.y);
    P.pathIdx = 0;
  } else if (t.kind === 'attackA' || t.kind === 'attackM') {
    // цель на непроходимой клетке (вода?) — лук ещё может
    if (RANGED.has(P.weapon) && (P.inv[AMMO[P.weapon]] || 0) > 0 && dist(P.x, P.y, t.tx, t.ty) <= WEAPON_RANGE[P.weapon]) {
      P.pending = null; startLifeAction(t);
    } else { P.pending = null; lifeBubble('Не подобраться.'); }
  } else { P.pending = null; lifeBubble('Не подобраться.'); }
}

// ── выполнение действий ──
function startLifeAction(t) {
  if (!P || P.dead) return;
  switch (t.kind) {
    case 'chop':
      P.busyKind = { kind: 'chop', ox: t.ox, oy: t.oy, t: P.axe ? 1.6 : 2.8, total: P.axe ? 1.6 : 2.8 };
      P.busyT = P.busyKind.t;
      break;
    case 'forage':
      P.busyKind = { kind: 'forage', ox: t.ox, oy: t.oy, t: 1.6, total: 1.6 };
      P.busyT = 1.6;
      break;
    case 'stone':
      P.busyKind = { kind: 'stone', ox: t.ox, oy: t.oy, t: 2.2, total: 2.2 };
      P.busyT = 2.2;
      break;
    case 'ore':
      P.busyKind = { kind: 'ore', ox: t.ox, oy: t.oy, t: 2.6, total: 2.6 };
      P.busyT = 2.6;
      break;
    case 'harvest':
      P.busyKind = { kind: 'harvest', ox: t.ox, oy: t.oy, t: 1.4, total: 1.4 };
      P.busyT = 1.4;
      break;
    case 'attackA':
    case 'attackM': {
      if (P.atkCd > 0) break;
      const list = t.kind === 'attackA' ? animals : monsters;
      const e = list.find(x => x.id === t.id && x.hp > 0);
      if (!e) { lifeBubble('Цель ушла.'); break; }
      const d = dist(P.x, P.y, e.x, e.y);
      const dmg = WEAPON_DMG[P.weapon];
      if (RANGED.has(P.weapon)) {
        const ammo = AMMO[P.weapon];
        if ((P.inv[ammo] || 0) <= 0) { lifeBubble(P.weapon === 2 ? 'Нет стрел!' : 'Нет пуль! Скрафти у костра.'); break; }
        if (d > WEAPON_RANGE[P.weapon]) { lifeGo({ ...t, tx: e.x, ty: e.y, range: WEAPON_RANGE[P.weapon] }); break; }
        P.inv[ammo]--;
      } else if (d > WEAPON_RANGE[P.weapon]) { lifeGo({ ...t, tx: e.x, ty: e.y, range: WEAPON_RANGE[P.weapon] }); break; }
      P.atkCd = WEAPON_CD[P.weapon];
      e.hp -= dmg;
      if (e.kind === 'wolf') e.hostileP = 30;
      if (e.hp <= 0) {
        if (t.kind === 'attackA') {
          const i = animals.indexOf(e);
          if (i >= 0) animals.splice(i, 1);
          const meat = e.kind === 'wolf' ? 3 : (e.kind === 'camel' || e.kind === 'deer') ? 4 : 2;
          P.inv.meat += meat;
          if (e.kind === 'wolf' || e.kind === 'deer' || e.kind === 'camel') { P.inv.fur = (P.inv.fur || 0) + 1; }
          const A_NAME = { wolf: 'волка', rabbit: 'кролика', camel: 'верблюда', deer: 'оленя' }[e.kind] || 'зверя';
          logEvent(e.kind === 'wolf' ? '🐺' : '🐇', `Ты добыл${P.gender === 'f' ? 'а' : ''} ${A_NAME} (+${meat} 🍖${(e.kind === 'wolf' || e.kind === 'deer' || e.kind === 'camel') ? ' +1 🧥 мех' : ''})`);
        } else {
          const i = monsters.indexOf(e);
          if (i >= 0) monsters.splice(i, 1);
          SIM.monsterKills++;
          logEvent('⚔️', 'Ты сокрушил слайму!');
        }
      }
      updateLifeHud();
      break;
    }
    case 'popupCamp': showLifePopup('🔥 Костёр', [
      { l: '🫐 Поесть ягод (−3, +22 сытости)', fn: 'lifeEat(3, 22)' },
      { l: '🍖 Съесть мясо (−1, +45, +3 HP)', fn: 'lifeEatMeat()' },
      { l: '🎁 Отдать запасы деревне', fn: 'lifeDonate()' },
      { l: '🎒 Открыть крафт', fn: 'lifeOpenCraft()' }
    ]); break;
    case 'popupHome': showLifePopup('🏠 Дом', [
      { l: P.asleep ? 'Проснуться' : '😴 Спать до утра (+HP)', fn: 'lifeSleep()' }
    ]); break;
    case 'popupVil': {
      const v = villagers.find(x => x.id === t.vilId);
      if (!v) { lifeBubble('Уже ушёл.'); break; }
      const hearts = v.isChild ? '🧒' : '❤️'.repeat(Math.max(1, Math.ceil((v.relP || 0) / 25))) + (P.partnerId === v.id ? ' 💞' : '');
      const btns = [
        { l: '💬 Поговорить', fn: 'lifeTalk(' + v.id + ')' },
        { l: '🫐 Подарить ягоды (−3)', fn: 'lifeGive(' + v.id + ')' }
      ];
      if (P.inv.meat > 0) btns.push({ l: '🍖 Подарить мясо (−1)', fn: 'lifeGiveMeat(' + v.id + ')' });
      if (!v.isChild) {
        const hasPartner = P.partnerId && villagers.some(x => x.id === P.partnerId);
        if (!hasPartner && (v.relP || 0) >= 50 && P.partnerId !== v.id)
          btns.push({ l: '💘 Признаться в чувствах', fn: 'lifeConfess(' + v.id + ')' });
        if (P.partnerId === v.id)
          btns.push({ l: '❤️ Провести ночь вместе', fn: 'lifeNight(' + v.id + ')' });
      }
      btns.push({ l: '⚔️ Атаковать', fn: 'lifeAttackVil(' + v.id + ')', danger: true });
      showLifePopup((v.isChild ? '🧒 ' : '🧑 ') + v.name + ' ' + hearts + (v.traits.length ? '<div style="font-size:11px;color:#8a94b8">' + v.traits.map(x => x.label).join(', ') + '</div>' : ''), btns);
      break;
    }
  }
}
function finishLifeAction(k) {
  if (!k) return;
  const o = objAt.get(key(k.ox, k.oy));
  switch (k.kind) {
    case 'chop': {
      if (o && (o.type === 'tree' || o.type === 'pine' || o.type === 'acacia' || o.type === 'mangrove' || o.type === 'deadtree' || o.type === 'darkpine' || o.type === 'cherry')) {
        removeObject(o);
        addObject('stump', o.x, o.y);
        regrowQueue.push({ x: o.x, y: o.y, at: simTime + 2 * DAY_LEN / rainMult() });
        const got = (P.axe ? 5 : 3) + (P.backpack ? 1 : 0);
        P.inv.wood += got;
        logEvent('🪓', `Ты срубил${P.gender === 'f' ? 'а' : ''} дерево (+${got} 🪵${P.axe ? ' топором' : ''})`);
      } else lifeBubble('Дерево уже срубили.');
      break;
    }
    case 'forage': {
      if (o && (o.type === 'bush' || o.type === 'cactus' || o.type === 'reed' || o.type === 'mushroom') && !o.depleted) {
        o.depleted = true;
        o.regrowAt = simTime + 25 / rainMult();
        const bgot = 2 + (P.backpack ? 1 : 0);
        P.inv.berries += bgot;
        logEvent('🫐', 'Ты собрал' + (P.gender === 'f' ? 'а' : '') + ' ягоды (+' + bgot + ')');
      } else lifeBubble('Куст уже обобрали.');
      break;
    }
    case 'stone': {
      if (o && o.type === 'stone') {
        removeObject(o);
        P.inv.stone += 3 + (P.backpack ? 1 : 0);
        logEvent('🪨', 'Ты добыл' + (P.gender === 'f' ? 'а' : '') + ' камень (+3 🪨)');
      } else lifeBubble('Камень уже разобрали.');
      break;
    }
    case 'ore': {
      if (o && o.type === 'mine') {
        const bonus = rng() < 0.12 ? 2 : 1;
        const stone = 1 + Math.floor(rng() * 3);
        P.inv.ore += bonus + (P.backpack ? 1 : 0);
        P.inv.stone += stone + (P.backpack ? 1 : 0);
        logEvent('⛏️', 'Ты добыл' + (P.gender === 'f' ? 'а' : '') + ' в шахте: +' + bonus + ' ⛏️ и +' + stone + ' 🪨');
      } else lifeBubble('Здесь больше нечего копать.');
      break;
    }
    case 'study': {
      const id2 = P.pendingKnow;
      P.pendingKnow = null;
      if (id2 === 'know_gun') {
        P.knows.gun = true;
        logEvent('📚', 'Наука усвоена: ПОРОХ! Теперь можно собрать мушкет.');
        lifeBubble('Теперь я знаю порох!');
      } else if (id2 === 'know_auto') {
        P.knows.auto = true;
        logEvent('📚', 'Наука усвоена: автоматическое оружие! Деревня на пороге современности.');
        lifeBubble('Гениально! Автоматическое оружие!');
      }
      updateLifeHud();
      break;
    }
    case 'harvest': {
      if (o && o.type === 'farm' && o.stage >= 3) {
        o.stage = 1;
        o.growAt = simTime + 60 / rainMult();
        P.inv.berries += 3;
        logEvent('🌾', 'Ты собрал' + (P.gender === 'f' ? 'а' : '') + ' урожай пшеницы (+3 🫐)');
      } else lifeBubble('Пшеница ещё зелёная.');
      break;
    }
  }
  updateLifeHud();
}

// ── popup-действия ──
function showLifePopup(title, btns) {
  const el = document.getElementById('lifeAct');
  let html = `<div class="act-title">${title}</div>`;
  for (const b of btns)
    html += `<button class="act-btn${b.danger ? ' danger' : ''}" onclick="${b.fn};hideLifePopup()">${b.l}</button>`;
  html += `<button class="act-btn" style="background:rgba(255,255,255,0.06);color:#9aa4c0" onclick="hideLifePopup()">Отмена</button>`;
  el.innerHTML = html;
  el.style.display = 'flex';
}
function hideLifePopup() { document.getElementById('lifeAct').style.display = 'none'; }

function lifeEat(b, sat) {
  if (P.inv.berries < b) { lifeBubble('Мало ягод!'); return; }
  P.inv.berries -= b;
  P.hunger = Math.min(100, P.hunger + sat);
  lifeBubble('Вкусно!');
  updateLifeHud();
}
function lifeEatMeat() {
  if (P.inv.meat < 1) { lifeBubble('Нет мяса! На охоту!'); return; }
  P.inv.meat--;
  P.hunger = Math.min(100, P.hunger + 45);
  P.hp = Math.min(20, P.hp + 3);
  lifeBubble('Мясо у костра — это жизнь!');
  updateLifeHud();
}
function lifeDonate() {
  const I = P.inv;
  const w = I.wood, s = I.stone, bb = I.berries;
  if (!w && !s && !bb) { lifeBubble('Тебе и отдать нечего.'); return; }
  stocks.wood += w; stocks.stone += s; stocks.berries += bb;
  totalWood += w;
  I.wood = 0; I.stone = 0; I.berries = 0;
  logEvent('🎁', `Ты отдал${P.gender === 'f' ? 'а' : ''} деревне: +${w} 🪵 +${bb} 🫐 +${s} 🪨. Деревня ускоряет развитие!`);
  lifeBubble('Деревня благодарит!');
  updateLifeHud();
}
function lifeSleep() {
  const near = homes().find(h => dist(h.x + 0.5, h.y + 0.5, P.x, P.y) < 2.6);
  if (!near) { lifeBubble('Спать можно только возле дома.'); return; }
  P.asleep = true;
  P.x = near.x + 0.5; P.y = near.y + 0.5;
  P.wakeAt = simTime + DAY_LEN * ((0.12 - phase() + 1) % 1);
  lifeBubble('Спокойной ночи…');
  updateLifeHud();
}
// ── живой чат с жителем (LLM) ──
const CHAT = { v: null, busy: false };
function lifeTalk(id) {
  const v = villagers.find(x => x.id === id);
  if (!v) return;
  openChat(v);
}
function chatHearts(v) {
  const rel = v.relP || 0;
  if (P.partnerId === v.id) return '💞';
  return '❤️'.repeat(Math.max(1, Math.ceil(rel / 25)));
}
function greetingLine(v) {
  const rel = v.relP || 0;
  if (P.partnerId === v.id) return 'Привет, любимый мой человек… я как раз думал о тебе ❤️';
  if (v.isChild) return 'Привет! А ты кто? Меня зовут ' + v.name + '!';
  if (rel > 60) return 'О, ' + P.name + '! Как же я рад тебя видеть!';
  if (rel > 30) return 'Привет, ' + P.name + '. Хорошая погода, да?';
  return 'Привет… Мы, кажется, ещё мало знакомы.';
}
function chatBubble(role, text) {
  const box = document.getElementById('chatMsgs');
  const div = document.createElement('div');
  div.className = 'chat-row ' + (role === 'me' ? 'chat-me' : 'chat-vil');
  div.textContent = text;
  box.appendChild(div);
  box.scrollTop = box.scrollHeight;
  return div;
}
function openChat(v) {
  CHAT.v = v; CHAT.busy = false;
  if (!P.chats) P.chats = {};
  if (!Array.isArray(P.chats[v.id])) P.chats[v.id] = [];
  document.getElementById('chatTitle').innerHTML = '💬 ' + v.name + ' <span style="font-size:12px">' + chatHearts(v) + '</span>';
  document.getElementById('chatMsgs').innerHTML = '';
  if (!P.chats[v.id].length) chatBubble('vil', greetingLine(v));
  for (const m of P.chats[v.id]) chatBubble(m.r, m.t);
  document.getElementById('chatInput').value = '';
  document.getElementById('chatBox').style.display = 'flex';
}
function closeChat() {
  document.getElementById('chatBox').style.display = 'none';
  CHAT.v = null; CHAT.busy = false;
}
function cannedReply() {
  const lines = ['Ммм, надо подумать…', 'Ты вообще откуда взялся, такой интересный?', 'Сегодня хороший день, правда?', 'Деревня наша растёт — глядишь, и городом станет.', 'Давай к костру сядем, там и поговорим.', 'Ох, дела-дела…', 'А ты смелый, я такое уважаю.', 'Слышал, у шахты камень сыпется — выгодное место.'];
  return lines[Math.floor(Math.random() * lines.length)];
}
async function llmChatReply(v, userText) {
  if (!LLM.on || !LLM.key) return cannedReply();
  const traits = v.traits.map(t => t.label).join(', ') || 'обычный';
  const tod = isNight() ? 'глубокая ночь' : phase() < 0.35 ? 'утро' : phase() < 0.6 ? 'день' : 'вечер';
  const st = STATE_RU[v.state] || v.state;
  const rel = v.relP || 0;
  const bond = P.partnerId === v.id
    ? `игрок ${P.name} — твоя вторая половинка, вы пара, ты очень его любишь`
    : rel > 60 ? `игрок ${P.name} — твой близкий друг`
    : rel > 30 ? `игрок ${P.name} — твой хороший знакомый`
    : `игрок ${P.name} — человек, которого ты почти не знаешь`;
  const history = (P.chats[v.id] || []).slice(-8).map(m => ({ role: m.r === 'me' ? 'user' : 'assistant', content: m.t }));
  const r = await fetch('https://api.groq.com/openai/v1/chat/completions', {
    method: 'POST',
    headers: { 'Authorization': 'Bearer ' + LLM.key, 'Content-Type': 'application/json' },
    body: JSON.stringify({
      model: LLM_MODEL,
      max_tokens: 140,
      temperature: 0.9,
      reasoning_effort: 'low',
      messages: [
        { role: 'system', content: `Ты — ${v.isChild ? 'ребёнок' : 'житель'} по имени ${v.name} в первобытной деревне (эпоха «${ERAS[era()]}», сейчас ${tod}, ты ${st}). Характер: ${traits}. ${bond}. Отвечай на русском как живой человек: 1-2 коротких предложения от первого лица, по-характеру. Без markdown.` },
        ...history,
        { role: 'user', content: userText }
      ]
    })
  });
  if (!r.ok) throw new Error('HTTP ' + r.status);
  const d = await r.json();
  const txt = ((d.choices && d.choices[0] && d.choices[0].message.content) || '').trim();
  if (!txt) throw new Error('пусто');
  return txt;
}
async function chatSendMsg() {
  if (!CHAT.v || CHAT.busy || !P || P.dead) return;
  const inp = document.getElementById('chatInput');
  const text = inp.value.trim();
  if (!text) return;
  const v = CHAT.v;
  inp.value = '';
  P.chats[v.id].push({ r: 'me', t: text });
  chatBubble('me', text);
  CHAT.busy = true;
  const typing = chatBubble('vil', '…');
  let reply;
  try { reply = await llmChatReply(v, text); }
  catch (e) { reply = cannedReply(); }
  CHAT.busy = false;
  if (!villagers.includes(v)) { typing.textContent = '…'; setTimeout(closeChat, 600); return; }
  reply = String(reply).slice(0, 240);
  typing.textContent = reply;
  const box = document.getElementById('chatMsgs');
  box.scrollTop = box.scrollHeight;
  P.chats[v.id].push({ r: 'vil', t: reply });
  if (P.chats[v.id].length > 16) P.chats[v.id].splice(0, P.chats[v.id].length - 16);
  v.relP = Math.min(100, (v.relP || 0) + 2);
  v.needs.social = Math.min(100, v.needs.social + 8);
  think(v, reply.slice(0, 50));
  const t2 = document.getElementById('chatTitle');
  t2.innerHTML = '💬 ' + v.name + ' <span style="font-size:12px">' + chatHearts(v) + '</span>';
}
function lifeConfess(id) {
  const v = villagers.find(x => x.id === id);
  if (!v || v.isChild) return;
  if (P.partnerId && villagers.some(x => x.id === P.partnerId)) { lifeBubble('У тебя уже есть любимый человек.'); return; }
  if ((v.relP || 0) >= 50) {
    P.partnerId = v.id;
    v.relP = 100;
    think(v, 'Моё сердце теперь твоё…');
    logEvent('💘', `Вы с ${v.name} теперь пара!`);
    lifeBubble(v.name + ' — теперь твоя вторая половинка 💞');
  } else {
    v.relP = Math.max(0, (v.relP || 0) - 5);
    lifeBubble(v.name + ' смущён(а): «Мы слишком мало знакомы…»');
  }
}
function lifeNight(id) {
  const v = villagers.find(x => x.id === id);
  if (!v || P.partnerId !== v.id) return;
  hideLifePopup();
  const el = document.getElementById('loveScene');
  el.style.display = 'flex';
  requestAnimationFrame(() => { el.style.opacity = '1'; });
  setTimeout(() => {
    el.style.opacity = '0';
    setTimeout(() => { el.style.display = 'none'; }, 900);
    if (!villagers.includes(v)) return;
    logEvent('❤️', `Ночь с ${v.name} была тёплой… Дальше — только ваше воображение.`);
    think(v, 'Какая ночь…');
    v.relP = 100;
    if (Math.random() < 0.55) {
      v.pregUntil = simTime + DAY_LEN * 1.1;
      logEvent('🤰', `${v.name} чувствует: скоро в семье будет прибавление…`);
    }
  }, 2800);
}
function lifeGive(id) {
  const v = villagers.find(x => x.id === id);
  if (!v) return;
  if (P.inv.berries < 3) { lifeBubble('Мало ягод для подарка.'); return; }
  P.inv.berries -= 3;
  v.needs.hunger = Math.min(100, v.needs.hunger + 30);
  v.needs.social = Math.min(100, v.needs.social + 15);
  v.relP = Math.min(100, (v.relP || 0) + 6);
  think(v, 'Спасибо! Какие щедрые руки!');
  lifeBubble(v.name + ' рад подарку! (симпатия +6)');
  updateLifeHud();
}
function lifeGiveMeat(id) {
  const v = villagers.find(x => x.id === id);
  if (!v) return;
  if (P.inv.meat < 1) { lifeBubble('Нет мяса!'); return; }
  P.inv.meat--;
  v.needs.hunger = Math.min(100, v.needs.hunger + 50);
  v.needs.social = Math.min(100, v.needs.social + 20);
  v.relP = Math.min(100, (v.relP || 0) + 10);
  think(v, 'Мясо?! Для меня?! Ты чудо!');
  lifeBubble(v.name + ' в восторге от такого подарка! (симпатия +10)');
  updateLifeHud();
}
function lifeAttackVil(id) {
  const v = villagers.find(x => x.id === id);
  if (!v || P.atkCd > 0) return;
  if (dist(P.x, P.y, v.x, v.y) > 1.8) { lifeBubble('Подойди ближе.'); return; }
  P.atkCd = 0.7;
  v.hp -= WEAPON_DMG[P.weapon];
  P.hostile = Math.max(P.hostile, 45);
  v.hostileP = 45;
  if (v.hp <= 0) {
    P.kills++;
    killVillager(v, 'player');
    logEvent('💀', `Ты убил${P.gender === 'f' ? 'а' : ''} ${v.name}. Деревня смотрит на тебя с ужасом.`);
    lifeBubble('Что ты наделал…');
  } else {
    lifeBubble(v.name + ' в ярости!');
  }
}

// ── крафт ──
function canCraft(r) {
  if (r.fire && dist(P.x, P.y, campfire.x, campfire.y) > 3.2) return false;
  for (const k of Object.keys(r.req)) if ((P.inv[k] || 0) < r.req[k]) return false;
  if (r.needW !== undefined && P.weapon < r.needW) return false;
  if (r.needKnow && !P.knows[r.needKnow]) return false;
  if (r.id === 'axe' && P.axe) return false;
  if (r.id === 'coat' && P.coat) return false;
  if (r.id === 'torch' && P.torch) return false;
  if (r.id === 'backpack' && P.backpack) return false;
  if (r.id === 'spear' && P.weapon >= 1) return false;
  if (r.id === 'bow' && (P.weapon === 2 || P.weapon === 3)) return false;
  if (r.id === 'sword' && P.weapon === 3) return false;
  if (r.id === 'know_gun' && P.knows.gun) return false;
  if (r.id === 'know_auto' && P.knows.auto) return false;
  if (r.id === 'musket' && P.weapon >= 4) return false;
  if (r.id === 'auto' && P.weapon === 5) return false;
  if (r.build && P.placing) return false;
  return true;
}
function ownedLabel(r) {
  if (r.id === 'axe' && P.axe) return '✔ есть';
  if (r.id === 'coat' && P.coat) return '✔ надета';
  if (r.id === 'torch' && P.torch) return '✔ есть';
  if (r.id === 'backpack' && P.backpack) return '✔ надет';
  if (r.id === 'spear' && P.weapon >= 1) return P.weapon > 1 ? '✔ лучшее' : '✔ есть';
  if (r.id === 'bow' && P.weapon === 2) return '✔ есть';
  if (r.id === 'bow' && P.weapon === 3) return '✔ есть меч';
  if (r.id === 'sword' && P.weapon === 3) return '✔ есть';
  if (r.id === 'know_gun' && P.knows.gun) return '✔ изучено';
  if (r.id === 'know_auto' && P.knows.auto) return '✔ изучено';
  if (r.id === 'musket' && P.weapon >= 4) return P.weapon === 5 ? '✔ есть автомат' : '✔ есть';
  if (r.id === 'auto' && P.weapon === 5) return '✔ есть';
  return null;
}
function renderCraft() {
  const reqStr = r => Object.entries(r.req).map(([k, n]) => n + ({ wood: ' 🪵', stone: ' 🪨', ore: ' ⛏️', bronze: ' 🟠' })[k]).join('  ');
  let html = '';
  for (const r of RECIPES) {
    const owned = ownedLabel(r);
    html += `<div class="craft-item"><div><span class="craft-name">${r.name}</span><span class="craft-req">${reqStr(r)}${r.fire ? ' · у костра' : ''} — ${r.desc}</span></div>`;
    if (owned) html += `<span class="owned">${owned}</span>`;
    else html += `<button class="craft-btn" ${canCraft(r) ? '' : 'disabled'} onclick="craftItem('${r.id}')">Создать</button>`;
    html += `</div>`;
  }
  document.getElementById('craftList').innerHTML = html;
  document.getElementById('craftInfo').innerHTML = `Оружие: <b>${WEAPON_NAMES[P.weapon]}</b>${P.axe ? ' · топор ✔' : ''} · стрел: ${P.inv.arrows} · пуль: ${P.inv.bullets || 0}`;
}
function craftItem(id) {
  const r = RECIPES.find(x => x.id === id);
  if (!r || !canCraft(r)) { lifeBubble('Не хватает ресурсов или костра рядом.'); return; }
  for (const k of Object.keys(r.req)) P.inv[k] -= r.req[k];
  if (r.build) {
    P.placing = r.build;
    lifeBubble('Тапни по траве — поставлю ' + r.name.replace(/^[^ ]+ /, ''));
    document.getElementById('craftMenu').style.display = 'none';
    return;
  }
  if (r.study) {
    // обучение: сидим у костра и грызём гранит науки
    P.busyKind = { kind: 'study', total: r.study, t: r.study, label: r.name.replace('📚 ', '') };
    P.busyT = r.study;
    P.pendingKnow = id;
    logEvent('📚', 'Ты засел за науку: ' + r.name.replace('📚 ', '') + '…');
    document.getElementById('craftMenu').style.display = 'none';
    return;
  }
  if (id === 'axe') P.axe = true;
  else if (id === 'coat') { P.coat = true; logEvent('🧥', 'Меховая одежда готова — теперь метель не страшна!'); }
  else if (id === 'torch') { P.torch = true; logEvent('🕯', 'Факел в руке — ночь не так темна.'); }
  else if (id === 'backpack') { P.backpack = true; logEvent('🎒', 'Заплечный мешок собран — уносишь больше добычи.'); }
  else if (id === 'spear') P.weapon = Math.max(P.weapon, 1);
  else if (id === 'bow') P.weapon = Math.max(P.weapon, 2);
  else if (id === 'arrows') P.inv.arrows += 6;
  else if (id === 'bronze') P.inv.bronze++;
  else if (id === 'bullets') P.inv.bullets += 8;
  else if (id === 'sword') {
    P.weapon = 3;
    logEvent('⚔️', 'Ты выковал бронзовый меч! Деревня входит в Бронзовый век!');
  } else if (id === 'musket') {
    P.weapon = Math.max(P.weapon, 4);
    logEvent('🔫', 'Мушкет готов! Деревня вступает в Пороховую эпоху!');
  } else if (id === 'auto') {
    P.weapon = 5;
    logEvent('🔫', 'АВТОМАТ! Деревня доскакала до Современности за одну жизнь!');
  }
  logEvent('🔨', 'Скрафчено: ' + r.name);
  renderCraft();
  updateLifeHud();
}
function lifeOpenCraft() { hideLifePopup(); renderCraft(); document.getElementById('craftMenu').style.display = 'flex'; }

// ── отрисовка игрока ──
function drawLifePlayer() {
  if (P.asleep) return; // спит внутри дома
  const x = P.x * TILE - 4, y = P.y * TILE - 6;
  const moving = P.path && P.pathIdx < P.path.length;
  const frame = moving ? Math.floor(P.animT * 8) % 4 : (Math.sin(simTime * 2.4) > 0 ? 1 : 3);
  const set = P.facing >= 0 ? P.frames : P.framesFlip;
  ctx.fillStyle = 'rgba(0,0,0,0.28)';
  ctx.beginPath();
  ctx.ellipse(x + 4, y + 13, 3.6, 1.3, 0, 0, Math.PI * 2);
  ctx.fill();
  ctx.drawImage(set[frame], Math.round(x), Math.round(y));
  // факел: тёплое свечение ночью
  if (P.torch && nightAmount() > 0.25 && !P.asleep) {
    const flick = 0.85 + Math.sin(performance.now() / 90) * 0.15;
    const rad = 26 * flick;
    const g = ctx.createRadialGradient(x + 4, y + 6, 2, x + 4, y + 6, rad);
    g.addColorStop(0, 'rgba(255,190,90,0.30)');
    g.addColorStop(0.5, 'rgba(255,160,60,0.12)');
    g.addColorStop(1, 'rgba(255,140,40,0)');
    ctx.fillStyle = g;
    ctx.beginPath(); ctx.arc(x + 4, y + 6, rad, 0, Math.PI * 2); ctx.fill();
    px(ctx, x + 8, y + 1, 255, 200, 90); px(ctx, x + 8, y, 255, 160, 40); // огонёк
  }
  // шуба: коричневый ворот
  if (P.coat) { px(ctx, x + 2, y + 5, 122, 84, 48); px(ctx, x + 5, y + 5, 122, 84, 48); px(ctx, x + 3, y + 6, 100, 66, 38); px(ctx, x + 4, y + 6, 100, 66, 38); }
  // холод: синий фильтр на герое
  if (P.coldNow) { ctx.fillStyle = 'rgba(120,170,255,0.25)'; ctx.fillRect(Math.round(x), Math.round(y), 8, 14); }
  // мягкая метка «это ты»
  const t = performance.now() / 320;
  ctx.strokeStyle = `rgba(124,140,255,${0.45 + Math.sin(t) * 0.2})`;
  ctx.lineWidth = 0.7;
  ctx.strokeRect(x - 1.5, y - 1.5, 11, 16.5);
  if (zoom >= 2) {
    ctx.font = '4px monospace';
    ctx.fillStyle = '#cdd6ff';
    ctx.textAlign = 'center';
    ctx.fillText('ТЫ', x + 4, y - 1);
    ctx.textAlign = 'left';
  }
  // прогресс работы
  if (P.busyT > 0 && P.busyKind) {
    const p = 1 - P.busyT / P.busyKind.total;
    ctx.fillStyle = 'rgba(0,0,0,0.5)';
    ctx.fillRect(x - 1, y - 4, 10, 2);
    ctx.fillStyle = P.busyKind.kind === 'study' ? 'rgb(124,140,255)' : 'rgb(120,220,80)';
    ctx.fillRect(x - 1, y - 4, 10 * p, 2);
    if (P.busyKind.kind === 'study') {
      ctx.font = '4px monospace';
      ctx.fillStyle = '#aebaff';
      ctx.textAlign = 'center';
      ctx.fillText('учёба…', x + 4, y - 6);
      ctx.textAlign = 'left';
    }
  }
  if (P.placing) {
    ctx.font = '4px monospace';
    ctx.fillStyle = '#8dffa8';
    ctx.textAlign = 'center';
    ctx.fillText('стройка: тапни место', x + 4, y - 9);
    ctx.textAlign = 'left';
  }
  if (P.hp < 20) {
    const hearts = Math.ceil(P.hp / 4);
    for (let i = 0; i < hearts; i++) {
      ctx.fillStyle = 'rgb(220,60,80)';
      ctx.fillRect(x + i * 2, y - 7, 1.5, 1.5);
    }
  }
  if (P.bubble && simTime < P.bubble.until) drawBubble(x + 4, y - 10, P.bubble.text, true);
}

// ── сейв/лоад игрока ──
function restoreLifePlayer(pd, saved) {
  P = {
    gender: pd.gender, bodyIdx: pd.bodyIdx,
    name: pd.name || 'Странник', partnerId: pd.partnerId || 0, chats: pd.chats || {},
    x: pd.x, y: pd.y,
    path: null, pathIdx: 0, facing: 1, animT: 0,
    hp: pd.hp, hunger: pd.hunger,
    inv: { wood: 0, stone: 0, berries: 0, ore: 0, bronze: 0, meat: 0, arrows: 0, bullets: 0, fur: 0, ...pd.inv },
    weapon: pd.weapon, axe: !!pd.axe, coat: !!pd.coat, torch: !!pd.torch, backpack: !!pd.backpack,
    mom: null, dad: null,
    home: { x: pd.homeX, y: pd.homeY },
    wealth: !!pd.wealth,
    atkCd: 0, busyT: 0, busyKind: null, pending: null, repathT: 0, tries: 0,
    asleep: false, hostile: 0, kills: pd.kills || 0, dead: false,
    knows: { gun: !!(pd.knows && pd.knows.gun), auto: !!(pd.knows && pd.knows.auto) }, pendingKnow: null, placing: null,
    bubble: null, momId: pd.momId, dadId: pd.dadId
  };
  buildPlayerFrames();
  showLifeHud();
}
function resolveLifeParents() {
  if (!P) return;
  P.mom = villagers.find(v => v.id === P.momId) || null;
  P.dad = villagers.find(v => v.id === P.dadId) || null;
}

// ── кнопки UI ──
document.getElementById('btnNewLife').onclick = () => {
  document.getElementById('mainMenu').style.display = 'none';
  document.getElementById('lifeIntro').style.display = 'flex';
};
document.getElementById('chatSend').onclick = () => chatSendMsg();
document.getElementById('chatClose').onclick = () => closeChat();
document.getElementById('chatInput').addEventListener('keydown', e => { if (e.key === 'Enter') chatSendMsg(); });
document.getElementById('btnLifeF').onclick = () => startLifeGame('f');
document.getElementById('btnLifeM').onclick = () => startLifeGame('m');
document.getElementById('btnCraft').onclick = () => {
  if (P && P.placing) { P.placing = null; lifeBubble('Стройка отменена.'); return; }
  lifeOpenCraft();
};
document.getElementById('btnCraftClose').onclick = () => { document.getElementById('craftMenu').style.display = 'none'; };
document.getElementById('btnInv').onclick = () => {
  renderInventory();
  document.getElementById('invMenu').style.display = 'flex';
};
document.getElementById('invClose').onclick = () => { document.getElementById('invMenu').style.display = 'none'; };
(function () {
  const wrap = document.getElementById('chronWrap');
  const btn = document.getElementById('btnChron');
  const head = document.getElementById('chronHead');
  let hid = false;
  try { hid = localStorage.getItem('aikaChronHide') === '1'; } catch (e) {}
  const apply = () => {
    wrap.classList.toggle('collapsed', hid);
    btn.textContent = hid ? '▸' : '▾';
  };
  apply();
  btn.onclick = e => { e.stopPropagation(); hid = !hid; try { localStorage.setItem('aikaChronHide', hid ? '1' : '0'); } catch (e2) {} apply(); };
  head.onclick = () => { hid = !hid; try { localStorage.setItem('aikaChronHide', hid ? '1' : '0'); } catch (e2) {} apply(); };
})();
document.getElementById('btnSleepHud').onclick = () => {
  if (!P || P.dead) return;
  if (P.asleep) { P.asleep = false; lifeBubble('Ты проснулся.'); }
  else {
    const near = homes().find(h => dist(h.x + 0.5, h.y + 0.5, P.x, P.y) < 2.6);
    if (near) lifeSleep();
    else lifeBubble('Иди к дому, чтобы поспать.');
  }
  updateLifeHud();
};
document.getElementById('btnLifeHelp').onclick = () => {
  showLifePopup('❔ Как играть', [
    { l: '👆 Тап по дереву/кусту/камню/шахте — работать', fn: '0' },
    { l: '🐺 Тап по животному — атаковать (лук бьёт издалека)', fn: '0' },
    { l: '🔥 Тап по костру — еда, подарки деревне, крафт', fn: '0' },
    { l: '💬 Тап по жителю — ИИ-чат, подарки, симпатия ❤️, при 50+ признание 💘 и дети 👶', fn: '0' },
    { l: '⛏️ Шахта даёт руду И камень', fn: '0' },
    { l: '🏠 Возле дома можно спать до утра', fn: '0' },
    { l: '🍖 Голод убивает — ешь ягоды и мясо', fn: '0' },
    { l: '⛏️ Руда из шахты → бронза → меч = новая эпоха', fn: '0' }
  ]);
};

// ── Старт ─────────────────────────────────────────────────────────
// самовосстановление: если браузер подсунул старый HTML из кэша — перезагружаем целиком
if (!document.getElementById('worldsList')) {
  let reloaded = false;
  try { reloaded = !!sessionStorage.getItem('aikaReloaded'); } catch (e) {}
  if (!reloaded) {
    try { sessionStorage.setItem('aikaReloaded', '1'); } catch (e) {}
    location.replace(location.origin + location.pathname + '?v=36&r=' + Date.now());
  }
}
resize();
makeTextures();
genWorld(seed);
focusVillage();
showMainMenu();
requestAnimationFrame(loop);
