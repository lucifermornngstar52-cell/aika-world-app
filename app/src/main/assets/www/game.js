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
let stocks = { wood: 0, berries: 6, stone: 0 };
let totalWood = 0;
let pendingBuild = null;   // { kind:'hut'|'farm', x, y, assigned }
let settlersThresholds = [30, 70, 130, 220, 340];
let settlersSpawned = 0;
let simTime = 0;
let simSpeed = 1, paused = false, inMenu = true, menuScene = true;
let worldId = null, worldName = '';
let seed = (Date.now() % 2147483647) | 0;
let rng = null;
let camX = 0, camY = 0, zoom = 1.6;
let selected = null;
let nextId = 1;
let lastPhase = 0;
let weather = { rain: false, t: 80, bolt: 0 };
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
  3: [94, 140, 66], 4: [110, 156, 74], 5: [120, 120, 128], 6: [225, 228, 235]
};
const isWalkTile = t => t >= 2 && t <= 4;
const BLOCKING = new Set(['tree', 'pine', 'bush', 'stone', 'hut', 'campfire', 'farm', 'shelter', 'house']);

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
      else if (e > 0.82) t = 6;
      else if (e > 0.74) t = 5;
      else t = m > 0.55 ? 4 : 3;
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
      if (o && ['tree', 'bush', 'stone', 'pine'].includes(o.type)) removeObject(o);
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
  for (let i = 0; i < 5; i++) {
    const p = randWalkable(14);
    animals.push({ id: nextId++, kind: 'wolf', x: p.x, y: p.y, hp: 12, state: 'idle', t: rng() * 3, dirX: 0, dirY: 0, facing: 1, animT: 0, preyId: 0 });
  }
  monsters = [];
  stocks = { wood: 0, berries: 6, stone: 0 };
  totalWood = 0; pendingBuild = null; settlersSpawned = 0;
  simTime = 0; selected = null; selectedObj = null; selectedEnt = null; lastPhase = 0;
  weather = { rain: false, t: 60 + rng() * 120, bolt: 0 };
  SIM.monsterWaves = 0; SIM.monsterKills = 0; SIM.melted = 0; SIM.deaths = 0; SIM.births = 0; SIM.harvests = 0; SIM.rains = 0;
  renderMapCanvas();
  logEvent('🔥', 'Двое древних людей разожгли костёр. Начало великого пути!');
}

function addObject(type, x, y) {
  const o = { id: nextId++, type, x, y };
  if (type === 'tree' || type === 'pine') { o.variant = Math.floor(rng() * 3); o.regrow = 0; }
  if (type === 'bush') { o.depleted = false; o.regrowAt = 0; }
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
const ERAS = [null, 'Древний лагерь', 'Стоянка', 'Деревня', 'Поселение'];
function cnt(type) { let n = 0; for (const o of objects) if (o.type === type) n++; return n; }
function beds() { return cnt('shelter') * 2 + cnt('hut') * 2 + cnt('house') * 3; }
function homes() { return objects.filter(o => o.type === 'shelter' || o.type === 'hut' || o.type === 'house'); }
function era() {
  if (cnt('house') >= 2) return 4;
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
  const frames = [];
  for (let f = 0; f < 2; f++) {
    const c = document.createElement('canvas'); c.width = 8; c.height = 14;
    const g = c.getContext('2d');
    const { hair, shirt, pants, skin } = body;
    g.fillStyle = `rgb(${hair[0]},${hair[1]},${hair[2]})`;
    g.fillRect(1, 0, 6, 2); g.fillRect(0, 1, 8, 2);
    g.fillStyle = `rgb(${skin[0]},${skin[1]},${skin[2]})`;
    g.fillRect(1, 3, 6, 3);
    px(g, 2, 4, 30, 24, 22); px(g, 5, 4, 30, 24, 22);
    g.fillStyle = `rgb(${shirt[0]},${shirt[1]},${shirt[2]})`;
    g.fillRect(1, 6, 6, 4);
    px(g, 0, 6, shirt[0], shirt[1], shirt[2]); px(g, 7, 6, shirt[0], shirt[1], shirt[2]);
    px(g, 0, 7, skin[0], skin[1], skin[2]); px(g, 7, 7, skin[0], skin[1], skin[2]);
    g.fillStyle = `rgb(${pants[0]},${pants[1]},${pants[2]})`;
    g.fillRect(2, 10, 4, 2);
    g.fillStyle = `rgb(${pants[0]},${pants[1]},${pants[2]})`;
    if (f === 0) { g.fillRect(2, 12, 2, 2); g.fillRect(5, 12, 1, 2); }
    else { g.fillRect(3, 12, 1, 2); g.fillRect(4, 12, 2, 2); }
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
    carry: { wood: 0, berries: 0, stone: 0 },
    needs: { hunger: 70 + rng() * 30, energy: 70 + rng() * 30, social: 50 + rng() * 40 },
    skill: { chop: 1, forage: 1, combat: 1 },
    hp: 20, tool: null, spear: false,
    isChild: false, growAt: 0,
    thought: '', thoughtUntil: 0, thoughts: [],
    home: null, decideT: rng() * 2,
    threatT: 0, atkT: 0, fightId: 0, repathT: 0, huntId: 0
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
    if (o.type === 'bush' && o.depleted) continue;
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
function rainMult() { return weather.rain ? 2 : 1; }

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
  if (pendingBuild && !pendingBuild.assigned && !night) { startBuild(v); return; }
  if (n.hunger < 32) { startEat(v); return; }
  if (n.energy < 22 || (night && n.energy < 70)) { startSleep(v); return; }
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
    const b = findNearestObj(v, ['bush']);
    if (b) { startForage(v, b); return; }
    const rb = nearestAnimal(v, 'rabbit', 9);
    if (rb) { startHunt(v, rb); return; }
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
  const t = stocks.wood < 400 ? findNearestObj(v, ['tree', 'pine']) : null;
  if (t && !night) { startChop(v, t); return; }
  if (!t && !night && stocks.wood >= 400 && rng() < 0.2) think(v, 'Дров на складе выше крыши — можно и отдохнуть.');
  if (night && hasTrait(v, 'dreamer') && rng() < 0.5) { think(v, pickThought(v, 'nightDream')); startWander(v); return; }
  startWander(v);
}
function decideChild(v, night, n) {
  if (n.hunger < 35) { startEat(v); return; }
  if (n.energy < 30 || night) { startSleep(v); return; }
  if (v.carry.berries > 0) { startDeposit(v); return; }
  const b = findNearestObj(v, ['bush']);
  if (b && !night) { startForage(v, b); return; }
  if (rng() < 0.3) think(v, pickThought(v, 'child'));
  startWander(v);
}
function pick(arr) { return arr[Math.floor(rng() * arr.length)]; }
function pickThought(v, key) {
  const base = THOUGHTS[key];
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
    const b = findNearestObj(v, ['bush']);
    if (b) { startForage(v, b); v.eatIntent = true; }
    else {
      const rb = nearestAnimal(v, 'rabbit', 10);
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
  for (let tries = 0; tries < 10; tries++) {
    const x = Math.floor(v.x + (rng() * 21) - 10), y = Math.floor(v.y + (rng() * 21) - 10);
    if (walkable(x, y)) {
      const p = astar(v.x, v.y, x, y);
      if (p) { v.path = p; v.pathIdx = 0; v.state = 'wander'; think(v, pickThought(v, 'wander')); return; }
    }
  }
  v.state = 'idle'; v.decideT = 1 + rng() * 2;
  if (rng() < 0.4) think(v, pickThought(v, 'idle'));
}
function startBuild(v) {
  pendingBuild.assigned = v;
  v.path = astar(v.x, v.y, pendingBuild.x, pendingBuild.y); v.pathIdx = 0;
  v.state = 'goto_build';
  think(v, pendingBuild.kind === 'farm' ? 'Вспашу поле — хлеб сам себя не посадит!' : 'Строим новый дом! За работу.');
}
function startFight(v, m) {
  v.state = 'fight'; v.fightId = m.id; v.repathT = 0;
  think(v, pickThought(v, 'fight'));
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
    weather.rain = !weather.rain;
    if (weather.rain) {
      weather.t = 40 + rng() * 60;
      SIM.rains++;
      logEvent('🌧', 'Пошёл дождь. Растения растут быстрее!');
    } else weather.t = 60 + rng() * 160;
  }
  if (weather.rain && rng() < 0.002) {
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

  // жители
  for (const v of [...villagers]) updateVillager(v, dt);
  // животные
  for (const a of [...animals]) updateAnimal(a, dt);
  // монстры
  for (const m of [...monsters]) updateMonster(m, dt);

  // регенерация
  for (const o of objects) {
    if (o.type === 'bush' && o.depleted && o.regrowAt && simTime >= o.regrowAt) {
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
  // рождение: еда есть, дома есть, любовь есть
  const adults = villagers.filter(v => !v.isChild);
  if (adults.length >= 2 && stocks.berries >= 15 && beds() >= 4 && era() >= 2 && rng() < 0.5 && villagers.length < 16) {
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
  if (pendingBuild || isNight()) return;
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
  pendingBuild = { kind: plan.kind, x: spot.x, y: spot.y, assigned: null };
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
  } else if (a.kind === 'wolf') {
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
  if (target) {
    const d = steer(m, target.x, target.y, 1.55, dt);
    if (d < 1.15) {
      m.atkT -= dt;
      if (m.atkT <= 0) {
        m.atkT = 1.2;
        target.hp -= m.dmg;
        if (rng() < 0.3) think(target, 'Ай! Эта тварь кусается!');
        // шум боя будит спящих рядом — деревня обороняется толпой
        for (const w of villagers) {
          if (w.state === 'sleep' && dist(w.x, w.y, target.x, target.y) < 7) {
            w.path = null;
            decide(w);
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
  logEvent('😢', `${v.name} погиб${v.isChild ? '' : ' как герой'}, защищая деревню. Деревня скорбит…`);
}

function updateVillager(v, dt) {
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
      v.state = 'chop'; v.workT = Math.max(2, (4.5 - v.skill.chop * 0.4) / (v.tool === 'axe' ? 1.6 : 1));
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
          v.carry.wood += Math.ceil(3 * v.skill.chop);
          v.skill.chop = Math.min(3, v.skill.chop + 0.06);
          totalWood += 3;
          logEvent('🪓', `${v.name} срубил дерево (+3 🪵${v.tool === 'axe' ? ' топором' : ''})`);
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
      v.carry = { wood: 0, berries: 0, stone: 0 };
      v.state = 'craft'; v.workT = 2.5;
      break;
    }
    case 'craft': {
      v.workT -= dt;
      if (v.workT <= 0) {
        const kind = v.craftKind;
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
        v.carry.berries += 2;
        logEvent('🏹', `${v.name} поймал кролика (+2 🫐)`);
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
          v.atkT = 0.8;
          const dmg = (v.spear ? 7 : 4) * (0.5 + v.skill.combat * 0.5) + (hasTrait(v, 'brave') ? 1 : 0);
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
      v.workT = { shelter: 4, farm: 5, hut: 6, house: 8 }[pendingBuild.kind] || 6;
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
  if (weather.rain) {
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
  switch (o.type) {
    case 'tree': ctx.drawImage(spr.tree[o.variant % 3], x - 1, y - 6); break;
    case 'pine': ctx.drawImage(spr.pine[o.variant % 3], x - 1, y - 6); break;
    case 'bush': ctx.drawImage(spr.bush[o.depleted ? 1 : 0], x - 1, y + 2); break;
    case 'stone': ctx.drawImage(spr.stone, x, y + 1); break;
    case 'flower': ctx.drawImage(spr.flower, x + 1, y + 1); break;
    case 'stump': ctx.drawImage(spr.stump, x + 1, y + 4); break;
    case 'grave': ctx.drawImage(spr.grave, x + 1, y + 2); break;
    case 'farm': ctx.drawImage(spr.farm[o.stage] || spr.farm[1], x - 4, y - 1); break;
    case 'hut': {
      ctx.drawImage(spr.hut, x - 5, y - 8);
      if (nightAmount() > 0.3) {
        ctx.fillStyle = 'rgba(255,220,120,0.9)';
        ctx.fillRect(x - 5 + spr.hutWindow.x, y - 8 + spr.hutWindow.y, spr.hutWindow.w, spr.hutWindow.h);
        drawSmoke(x - 5 + spr.hutChimney.x + 1, y - 8 + spr.hutChimney.y);
      }
      break;
    }
    case 'shelter': {
      ctx.drawImage(spr.shelter, x - 3, y - 6);
      break;
    }
    case 'house': {
      ctx.drawImage(spr.house, x - 7, y - 10);
      if (nightAmount() > 0.3) {
        ctx.fillStyle = 'rgba(255,220,120,0.9)';
        for (const wnd of spr.houseWindows)
          ctx.fillRect(x - 7 + wnd.x, y - 10 + wnd.y, wnd.w, wnd.h);
        drawSmoke(x - 7 + spr.houseChimney.x + 1, y - 10 + spr.houseChimney.y);
      }
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
  const frame = moving && Math.floor((v.animT || 0) * 6) % 2 ? 1 : 0;
  const set = v.facing >= 0 ? spr.villagerFrames[v.bodyIdx] : spr.villagerFlip[v.bodyIdx];
  if (v.isChild) ctx.drawImage(set[frame], Math.round(x), Math.round(y), 8 * scale, 14 * scale);
  else ctx.drawImage(set[frame], Math.round(x), Math.round(y));
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
  // иконки занятия
  if (v.state === 'chop') { ctx.font = '5px sans-serif'; ctx.fillText(v.tool === 'axe' ? '🪓' : '✊', x + 8, y + 4); }
  if (v.state === 'fight') { ctx.font = '5px sans-serif'; ctx.fillText(v.tool === 'spear' ? '🔱' : '👊', x + 8, y + 4); }
  if (v.state === 'craft') { ctx.font = '5px sans-serif'; ctx.fillText('🔨', x + 8, y + 4); }
  if (v.state === 'hunt') { ctx.font = '5px sans-serif'; ctx.fillText('🏹', x + 8, y + 4); }
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
  const titles = { tree: ['🌳', 'Лиственное дерево'], pine: ['🌲', 'Сосна'], bush: ['🫐', 'Ягодный куст'], stone: ['🪨', 'Валун'], flower: ['🌸', 'Цветок'], stump: ['🪵', 'Пень'], grave: ['🪦', 'Могила жителя'], farm: ['🌾', 'Поле пшеницы'], shelter: ['🏕', 'Шалаш'], hut: ['🏠', 'Хижина'], house: ['🏡', 'Каменный дом'], campfire: ['🔥', 'Костёр — сердце деревни'] };
  const t = titles[o.type] || ['❓', 'Объект'];
  const lines = [];
  if (o.type === 'tree' || o.type === 'pine') lines.push('Древесина: <b>3 🪵</b>', 'Срубит любой житель с топором');
  if (o.type === 'bush') {
    if (o.depleted) lines.push('Пусто. Ягоды вернутся через <b>' + fmtLeft(o.regrowAt - simTime) + '</b>');
    else lines.push('Спелые ягоды: <b>2 🫐</b>');
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
  const day = Math.floor(simTime / DAY_LEN) + 1;
  const p = phase();
  const hh = String(Math.floor(p * 24)).padStart(2, '0');
  const mm = String(Math.floor((p * 24 % 1) * 60)).padStart(2, '0');
  const phaseName = p < 0.1 ? '🌅 рассвет' : p < 0.3 ? '☀️ утро' : p < 0.55 ? '🌤 день' : p < 0.65 ? '🌇 вечер' : '🌙 ночь';
  const weatherIcon = weather.rain ? '🌧' : '';
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
  simSpeed = simSpeed === 1 ? 2 : simSpeed === 2 ? 4 : 1;
  document.getElementById('btnSpeed').textContent = simSpeed + '×';
};
document.getElementById('btnWorld').onclick = () => {
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
      worldName = WN_ADJ[Math.floor(rng() * WN_ADJ.length)] + ' ' + WN_NOUN[Math.floor(rng() * WN_NOUN.length)];
    }
    const data = {
      v: 2, seed, simTime, worldName,
      stocks: { ...stocks },
      sim: { ...SIM },
      weather: { rain: weather.rain, t: weather.t },
      totalWood,
      settlers: settlersThresholds.slice(),
      regrowQueue: regrowQueue.map(q => ({ x: q.x, y: q.y, at: q.at })),
      objects: objects.map(o => ({ t: o.type, x: o.x, y: o.y, st: o.stage || 0, rg: o.regrowAt || 0, dp: o.depleted ? 1 : 0 })),
      villagers: villagers.map(v => ({
        n: v.name, bi: v.bodyIdx, x: v.x, y: v.y,
        ch: v.isChild ? 1 : 0, gr: v.growAt,
        hp: v.hp, tl: v.tool || null, sp: v.spear ? 1 : 0,
        nd: { ...v.needs }, tr: v.traits.slice(), sk: { ...v.skill }
      }))
    };
    localStorage.setItem('aikaWorld_' + worldId, JSON.stringify(data));
    const reg = worldsRegistry();
    const entry = { id: worldId, name: worldName, day: Math.floor(simTime / DAY_LEN), era: era(), pop: villagers.length, at: Date.now() };
    const i = reg.findIndex(r => r.id === worldId);
    if (i >= 0) reg[i] = entry; else reg.push(entry);
    saveRegistry(reg);
  } catch (e) {}
}
function restoreWorld(raw) {
  try {
    const d = JSON.parse(raw);
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
      v.name = sv.n; v.bodyIdx = sv.bi; v.isChild = !!sv.ch; v.growAt = sv.gr;
      v.hp = sv.hp; v.tool = sv.tl; v.spear = !!sv.sp;
      v.needs = sv.nd; v.traits = sv.tr; v.skill = sv.sk;
      v.state = 'idle'; v.path = null; v.decideT = 1;
      villagers.push(v);
    }
    stocks = d.stocks;
    Object.keys(d.sim).forEach(k => SIM[k] = d.sim[k]);
    totalWood = d.totalWood;
    settlersThresholds = d.settlers;
    weather.rain = d.weather.rain; weather.t = d.weather.t;
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
  try { raw = localStorage.getItem('aikaWorld_' + id); } catch (e) {}
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
    document.getElementById('chronicle').style.display = 'block';
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
  document.getElementById('topbar').style.display = 'none';
  document.getElementById('chronicle').style.display = 'none';
  document.getElementById('villagerPanel').style.display = 'none';
  selected = null; selectedObj = null; selectedEnt = null;
  migrateLegacySave();
  const reg = worldsRegistry().sort((a, b) => (b.at || 0) - (a.at || 0)).slice(0, 12);
  let html = '';
  for (const w of reg) {
    const er = ERAS[w.era] || 'Древний лагерь';
    html += '<div class="world-row"><button class="world-open" onclick="openWorld(\'' + w.id + '\')"><b>' + w.name + '</b><span class="world-meta">' + er + ' · день ' + w.day + ' · ' + w.pop + ' чел.</span></button><button class="world-del" onclick="deleteWorld(\'' + w.id + '\')">🗑</button></div>';
  }
  if (!html) html = '<div class="world-empty">Сохранённых миров нет — создай первый!</div>';
  document.getElementById('worldsList').innerHTML = html;
  document.getElementById('mainMenu').style.display = 'flex';
  document.getElementById('pauseMenu').style.display = 'none';
  document.getElementById('intro').style.display = 'none';
}
function startNewGame() {
  seed = Math.floor(Math.random() * 1000000000);
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
  document.getElementById('chronicle').style.display = 'block';
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

// ── Старт ─────────────────────────────────────────────────────────
// самовосстановление: если браузер подсунул старый HTML из кэша — перезагружаем целиком
if (!document.getElementById('worldsList')) {
  let reloaded = false;
  try { reloaded = !!sessionStorage.getItem('aikaReloaded'); } catch (e) {}
  if (!reloaded) {
    try { sessionStorage.setItem('aikaReloaded', '1'); } catch (e) {}
    location.replace(location.origin + location.pathname + '?v=33&r=' + Date.now());
  }
}
resize();
makeTextures();
genWorld(seed);
focusVillage();
showMainMenu();
requestAnimationFrame(loop);
