package com.aika.world;

import android.app.Activity;
import android.graphics.Color;
import android.net.ConnectivityManager;
import android.net.NetworkInfo;
import android.os.Bundle;
import android.view.View;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceError;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;

public class MainActivity extends Activity {
  private static final String REMOTE = "https://lucifermornngstar52-cell.github.io/aika-world/";
  private static final String LOCAL = "file:///android_asset/www/index.html";
  private WebView web;
  private boolean usingLocal = false;

  @Override
  protected void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);
    web = new WebView(this);
    web.setBackgroundColor(Color.parseColor("#0b0d14"));
    WebSettings st = web.getSettings();
    st.setJavaScriptEnabled(true);
    st.setDomStorageEnabled(true);
    st.setLoadWithOverviewMode(true);
    st.setUseWideViewPort(true);
    web.setWebViewClient(new WebViewClient() {
      @Override
      public void onReceivedError(WebView view, WebResourceRequest req, WebResourceError err) {
        if (req.isForMainFrame()) goLocal();
      }
      @Override
      public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest req) {
        // не выпускаем за пределы игры
        String u = req.getUrl().toString();
        return !(u.startsWith("https://lucifermornngstar52-cell.github.io/") || u.startsWith("file:///"));
      }
    });
    web.loadUrl(isOnline() ? REMOTE : LOCAL);
    setContentView(web);
    hideBars();
  }

  private void goLocal() {
    if (!usingLocal) {
      usingLocal = true;
      web.loadUrl(LOCAL);
    }
  }

  private boolean isOnline() {
    try {
      ConnectivityManager cm = (ConnectivityManager) getSystemService(CONNECTIVITY_SERVICE);
      NetworkInfo n = cm.getActiveNetworkInfo();
      return n != null && n.isConnected();
    } catch (Exception e) {
      return false;
    }
  }

  private void hideBars() {
    View d = getWindow().getDecorView();
    d.setSystemUiVisibility(View.SYSTEM_UI_FLAG_IMMERSIVE_STICKY
      | View.SYSTEM_UI_FLAG_FULLSCREEN
      | View.SYSTEM_UI_FLAG_HIDE_NAVIGATION
      | View.SYSTEM_UI_FLAG_LAYOUT_STABLE
      | View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN
      | View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION);
  }

  @Override
  public void onWindowFocusChanged(boolean has) {
    super.onWindowFocusChanged(has);
    if (has) hideBars();
  }

  @Override
  public void onBackPressed() {
    if (web.canGoBack()) web.goBack();
    else super.onBackPressed();
  }
}
