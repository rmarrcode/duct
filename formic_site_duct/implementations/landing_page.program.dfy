module DuctLandingImpl {

  import opened DB
  import opened DuctTools
  import opened DuctSpecs
  import opened SpecsTools

  function LandingPageStatus(ctx: UserInfo): string
  {
    if ctx.authenticated then "Signed in" else "Anonymous"
  }

  function LandingPageAction(ctx: UserInfo): string
  {
    if ctx.authenticated then Link("Log out", "/logout") else Link("Sign in", "/login")
  }

  function LandingPagePicturePanel(ctx: UserInfo): string
  {
    if ctx.picture == "" then
      "<div class=\"avatar avatar-fallback\">F</div>"
    else
      "<div class=\"avatar\"><img src=\"" + ctx.picture + "\" alt=\"" + ctx.name + "\" /></div>"
  }

  function LandingPageEmailPanel(ctx: UserInfo): string
  {
    if ctx.email == "" then
      "<span class=\"meta-value muted\">No email linked</span>"
    else
      "<span class=\"meta-value\">" + ctx.email + "</span>"
  }

  function LandingPagePictureMeta(ctx: UserInfo): string
  {
    if ctx.picture == "" then
      "<span class=\"meta-value muted\">No profile photo</span>"
    else
      "<span class=\"meta-value\">Profile image connected</span>"
  }

  function LandingPageHtml(ctx: UserInfo): string
  {
    var status := LandingPageStatus(ctx);
    var action := LandingPageAction(ctx);
    "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" />" +
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />" +
    "<title>Formic</title>" +
    "<style>" +
    ":root{--bg:#f7f3ea;--ink:#171717;--muted:#63635f;--card:#fffdf8;--accent:#0f766e;--line:rgba(23,23,23,.12);}" +
    "*{box-sizing:border-box;}body{margin:0;font-family:\"Avenir Next\",\"Segoe UI\",sans-serif;background:linear-gradient(180deg,#faf7f0,#ebe7dd);color:var(--ink);}" +
    ".shell{min-height:100vh;display:grid;place-items:center;padding:32px 18px;}" +
    ".panel{width:min(920px,100%);background:rgba(255,253,248,.92);border:1px solid var(--line);border-radius:20px;overflow:hidden;box-shadow:0 24px 70px rgba(23,23,23,.12);}" +
    ".hero{display:grid;grid-template-columns:150px 1fr;gap:26px;padding:32px;border-bottom:1px solid var(--line);}" +
    ".avatar{width:150px;height:150px;border-radius:18px;overflow:hidden;background:#e5e0d6;border:1px solid var(--line);display:grid;place-items:center;}" +
    ".avatar img{width:100%;height:100%;object-fit:cover;display:block;}" +
    ".avatar-fallback{font-size:52px;font-weight:800;color:var(--accent);letter-spacing:.08em;}" +
    ".eyebrow{margin:0 0 10px;font-size:12px;letter-spacing:.18em;text-transform:uppercase;color:var(--accent);}" +
    ".title{margin:0;font-size:42px;line-height:1;font-weight:800;}" +
    ".status-badge{display:inline-flex;align-items:center;gap:10px;margin-top:16px;padding:9px 14px;border-radius:999px;background:#fff;border:1px solid var(--line);font-size:14px;font-weight:700;}" +
    ".status-dot{width:10px;height:10px;border-radius:999px;background:var(--accent);}" +
    ".lede{margin:18px 0 0;color:var(--muted);font-size:16px;line-height:1.6;max-width:42rem;}" +
    ".content{display:grid;grid-template-columns:1.2fr .9fr;gap:20px;padding:28px 32px 32px;}" +
    ".card{padding:22px;border-radius:14px;background:rgba(255,255,255,.7);border:1px solid var(--line);}" +
    ".card-title{margin:0 0 16px;font-size:13px;letter-spacing:.16em;text-transform:uppercase;color:var(--muted);}" +
    ".meta-grid{display:grid;gap:14px;}" +
    ".meta-row{display:flex;justify-content:space-between;gap:18px;padding-bottom:12px;border-bottom:1px solid rgba(23,23,23,.08);}" +
    ".meta-row:last-child{border-bottom:0;padding-bottom:0;}" +
    ".meta-label{font-weight:700;color:var(--muted);}" +
    ".meta-value{text-align:right;font-weight:600;max-width:22rem;overflow-wrap:anywhere;}" +
    ".muted{color:var(--muted);font-weight:500;}" +
    ".actions{display:flex;flex-wrap:wrap;gap:12px;margin-top:22px;}" +
    ".actions a{display:inline-flex;align-items:center;justify-content:center;padding:13px 18px;border-radius:999px;text-decoration:none;font-weight:800;background:var(--accent);color:#fff;}" +
    ".aside-copy{margin:0;color:var(--muted);line-height:1.7;}" +
    "@media (max-width:780px){.hero,.content{grid-template-columns:1fr;}.avatar{width:112px;height:112px;border-radius:14px;}.title{font-size:34px;}}" +
    "</style></head><body>" +
    "<main class=\"shell\"><section class=\"panel\">" +
    "<div class=\"hero\">" +
    LandingPagePicturePanel(ctx) +
    "<div>" +
    "<p class=\"eyebrow\">Formic Landing Page</p>" +
    "<h1 class=\"title\">" + ctx.name + "</h1>" +
    "<div class=\"status-badge\"><span class=\"status-dot\"></span>" + status + "</div>" +
    "<p class=\"lede\">A generated profile surface for the formic demo.</p>" +
    "</div></div>" +
    "<div class=\"content\">" +
    "<section class=\"card\">" +
    "<p class=\"card-title\">Profile</p>" +
    "<div class=\"meta-grid\">" +
    "<div class=\"meta-row\"><span class=\"meta-label\">Name</span><span class=\"meta-value\">" + ctx.name + "</span></div>" +
    "<div class=\"meta-row\"><span class=\"meta-label\">Email</span>" + LandingPageEmailPanel(ctx) + "</div>" +
    "<div class=\"meta-row\"><span class=\"meta-label\">Picture</span>" + LandingPagePictureMeta(ctx) + "</div>" +
    "<div class=\"meta-row\"><span class=\"meta-label\">Session</span><span class=\"meta-value\">" + status + "</span></div>" +
    "</div>" +
    "<div class=\"actions\">" + action + "</div>" +
    "</section>" +
    "<aside class=\"card\">" +
    "<p class=\"card-title\">Notes</p>" +
    "<p class=\"aside-copy\">This page is generated from Dafny and rendered through the ASP.NET host.</p>" +
    "</aside>" +
    "</div></section></main></body></html>"
  }

  class FormicLandingPage extends LandingPageSpec {

    constructor () {}

    function Response(u: UserInfo): ReturnType
    {
      Content(LandingPageHtml(u))
    }

    function Program(u: UserInfo): DbProgram
    {
      Return
    }
  }
}
