include "db.dfy"
include "duct.dfy"
include "formic.specs.duct.dfy"

module FormicProofHelpers {

  import opened SpecsTools

  lemma ContainsInserted(prefix: string, needle: string, suffix: string)
    ensures Contains(prefix + needle + suffix, needle)
    decreases |prefix|
  {
    if |needle| == 0 {
    } else if |prefix| == 0 {
      assert (prefix + needle + suffix)[0 .. |needle|] == needle;
    } else {
      assert (prefix + needle + suffix)[1..] == prefix[1..] + needle + suffix;
      ContainsInserted(prefix[1..], needle, suffix);
    }
  }

  lemma ContainsTail(haystack: string, needle: string)
    requires |haystack| > 0
    ensures Contains(haystack[1..], needle) ==> Contains(haystack, needle)
  {
  }

  lemma NoBarIfCharAbsent(s: string)
    requires '|' !in s
    ensures !Contains(s, "|")
    decreases |s|
  {
    if |s| > 0 {
      assert s[0] != '|';
      NoBarIfCharAbsent(s[1..]);
    }
  }

  lemma CrossingBarCannotMatch(left: string, right: string, needle: string)
    requires 0 < |needle|
    requires |left| < |needle|
    requires |needle| <= |left| + 1 + |right|
    requires !Contains(needle, "|")
    ensures (left + "|" + right)[0 .. |needle|] != needle
  {
    if (left + "|" + right)[0 .. |needle|] == needle {
      assert needle[|left| .. |left| + 1] == "|";
      assert needle == needle[..|left|] + "|" + needle[|left| + 1..];
      ContainsInserted(needle[..|left|], "|", needle[|left| + 1..]);
      assert Contains(needle, "|");
    }
  }

  lemma NoContainsJoinedByBar(left: string, right: string, needle: string)
    requires !Contains(left, needle)
    requires !Contains(right, needle)
    requires !Contains(needle, "|")
    ensures !Contains(left + "|" + right, needle)
    decreases |left|
  {
    if |needle| == 0 {
      assert false;
    } else if |left| == 0 {
      assert (left + "|" + right)[1..] == right;
      assert !Contains((left + "|" + right)[1..], needle);
      if |needle| <= |left| + 1 + |right| {
        CrossingBarCannotMatch(left, right, needle);
      }
    } else {
      assert (left + "|" + right)[1..] == left[1..] + "|" + right;
      if Contains(left[1..], needle) {
        ContainsTail(left, needle);
        assert false;
      }
      assert !Contains(left[1..], needle);
      NoContainsJoinedByBar(left[1..], right, needle);
      assert !Contains((left + "|" + right)[1..], needle);
      if |needle| <= |left| + 1 + |right| {
        if |left| < |needle| {
          CrossingBarCannotMatch(left, right, needle);
        } else {
          if (left + "|" + right)[0 .. |needle|] == needle {
            assert left[0 .. |needle|] == needle;
            assert Contains(left, needle);
          }
        }
      }
    }
  }

  lemma EqualLengthDifferentNoContains(haystack: string, needle: string)
    requires |haystack| == |needle|
    requires haystack != needle
    ensures !Contains(haystack, needle)
  {
    assert haystack[0 .. |needle|] != needle;
    assert |haystack[1..]| < |needle|;
  }

  lemma LoginLinkHasNoBar()
    ensures !Contains(Link("Sign in", "/login"), "|")
  {
    assert Link("Sign in", "/login") == "<a href=\"/login\">Sign in</a>";
    assert '|' !in "<a href=\"/login\">Sign in</a>";
    NoBarIfCharAbsent("<a href=\"/login\">Sign in</a>");
  }

  lemma LogoutLinkHasNoBar()
    ensures !Contains(Link("Log out", "/logout"), "|")
  {
    assert Link("Log out", "/logout") == "<a href=\"/logout\">Log out</a>";
    assert '|' !in "<a href=\"/logout\">Log out</a>";
    NoBarIfCharAbsent("<a href=\"/logout\">Log out</a>");
  }

  lemma LogoutLinkDoesNotContainLoginLink()
    ensures !Contains(Link("Log out", "/logout"), Link("Sign in", "/login"))
  {
    assert Link("Log out", "/logout") == "<a href=\"/logout\">Log out</a>";
    assert Link("Sign in", "/login") == "<a href=\"/login\">Sign in</a>";
    assert "<a href=\"/logout\">Log out</a>"[13] == 'o';
    assert Link("Sign in", "/login")[13] == 'i';
    assert "<a href=\"/logout\">Log out</a>"[0 .. |Link("Sign in", "/login")|][13] == 'o';
    assert "<a href=\"/logout\">Log out</a>"[0 .. |Link("Sign in", "/login")|] != Link("Sign in", "/login");
    assert "<a href=\"/logout\">Log out</a>"[1..] == "a href=\"/logout\">Log out</a>";
    assert "<a href=\"/logout\">Log out</a>"[1..] != Link("Sign in", "/login");
    EqualLengthDifferentNoContains("<a href=\"/logout\">Log out</a>"[1..], Link("Sign in", "/login"));
    assert !Contains("<a href=\"/logout\">Log out</a>"[1..], Link("Sign in", "/login"));
  }
}


module DuctImpl {

  import opened DB
  import opened DuctTools
  import opened DuctSpecs
  import opened SpecsTools
  import FormicProofHelpers

  /// Concrete landing page generator that satisfies the specs.
  class FormicLandingPage extends IGenerator {

    constructor () {}

    predicate PreCondition(u: UserInfo, db: Database?) { LandingPagePre(u) }
    twostate predicate PostCondition(u: UserInfo, payload: ReturnType, db: Database?)
      reads if db == null then {} else {db}
    {
      LandingPagePost(u, payload)
    }

    method Generate(ctx: UserInfo) returns (payload: ReturnType)
      requires PreCondition(ctx, db)
      modifies this, if db == null then {} else {db}
      ensures PostCondition(ctx, payload, db)
    {
      var status := if ctx.authenticated then "Signed in" else "Anonymous";
      var action := if ctx.authenticated then Link("Log out", "/logout") else Link("Sign in", "/login");
      var statusPiece := "status|" + status;
      var userPiece := "user|" + ctx.name;
      var emailPiece := "email|" + ctx.email;
      var picturePiece := "picture|" + ctx.picture;
      var actionPiece := "action|" + action;
      var closingPiece := "</html>";
      var tail1 := actionPiece + "|" + closingPiece;
      var tail2 := picturePiece + "|" + tail1;
      var tail3 := emailPiece + "|" + tail2;
      var tail4 := userPiece + "|" + tail3;
      var tail5 := statusPiece + "|" + tail4;
      var picturePanel := if ctx.picture == ""
        then "<div class=\"avatar avatar-fallback\">F</div>"
        else "<div class=\"avatar\"><img src=\"" + ctx.picture + "\" alt=\"" + ctx.name + "\" /></div>";
      var emailPanel := if ctx.email == ""
        then "<span class=\"meta-value muted\">No email linked</span>"
        else "<span class=\"meta-value\">" + ctx.email + "</span>";
      var pictureMeta := if ctx.picture == ""
        then "<span class=\"meta-value muted\">No profile photo</span>"
        else "<span class=\"meta-value\">Profile image connected</span>";

      var html := "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" />" +
              "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />" +
              "<title>Formic</title>" +
              "<style>" +
              ":root{--bg:#f6efe4;--ink:#1c1917;--muted:#6b625b;--card:#fffaf2;--accent:#d97706;--accent-2:#9a3412;--line:rgba(28,25,23,.12);}" +
              "*{box-sizing:border-box;}body{margin:0;font-family:\"Avenir Next\",\"Segoe UI\",sans-serif;background:radial-gradient(circle at top,#fff8ef 0,#f6efe4 45%,#eadcc7 100%);color:var(--ink);}" +
              "body:before{content:\"\";position:fixed;inset:0;background:linear-gradient(135deg,rgba(217,119,6,.12),transparent 35%,rgba(154,52,18,.08));pointer-events:none;}" +
              ".shell{min-height:100vh;display:grid;place-items:center;padding:32px 18px;position:relative;z-index:1;}" +
              ".panel{width:min(920px,100%);background:rgba(255,250,242,.88);backdrop-filter:blur(12px);border:1px solid rgba(255,255,255,.55);border-radius:28px;overflow:hidden;box-shadow:0 24px 80px rgba(28,25,23,.12);}" +
              ".hero{display:grid;grid-template-columns:160px 1fr;gap:28px;padding:34px;border-bottom:1px solid var(--line);background:linear-gradient(135deg,rgba(255,255,255,.8),rgba(255,244,224,.88));}" +
              ".avatar{width:160px;height:160px;border-radius:28px;overflow:hidden;background:#f3e3cb;border:1px solid rgba(28,25,23,.08);display:grid;place-items:center;box-shadow:inset 0 1px 0 rgba(255,255,255,.7);}" +
              ".avatar img{width:100%;height:100%;object-fit:cover;display:block;}" +
              ".avatar-fallback{font-size:56px;font-weight:800;color:var(--accent-2);letter-spacing:.08em;}" +
              ".eyebrow{margin:0 0 10px;font-size:12px;letter-spacing:.24em;text-transform:uppercase;color:var(--accent-2);}" +
              ".title{margin:0;font-size:clamp(2rem,5vw,4rem);line-height:.92;font-weight:800;max-width:9ch;}" +
              ".status-badge{display:inline-flex;align-items:center;gap:10px;margin-top:16px;padding:10px 16px;border-radius:999px;background:#fff;border:1px solid rgba(28,25,23,.08);font-size:14px;font-weight:700;}" +
              ".status-dot{width:10px;height:10px;border-radius:999px;background:var(--accent);box-shadow:0 0 0 6px rgba(217,119,6,.16);}" +
              ".lede{margin:18px 0 0;color:var(--muted);font-size:16px;line-height:1.7;max-width:42rem;}" +
              ".content{display:grid;grid-template-columns:1.2fr .9fr;gap:20px;padding:28px 34px 34px;}" +
              ".card{padding:22px;border-radius:22px;background:rgba(255,255,255,.72);border:1px solid var(--line);}" +
              ".card-title{margin:0 0 16px;font-size:13px;letter-spacing:.18em;text-transform:uppercase;color:var(--muted);}" +
              ".meta-grid{display:grid;gap:14px;}" +
              ".meta-row{display:flex;justify-content:space-between;gap:18px;padding-bottom:12px;border-bottom:1px solid rgba(28,25,23,.08);}" +
              ".meta-row:last-child{border-bottom:0;padding-bottom:0;}" +
              ".meta-label{font-weight:700;color:var(--muted);}" +
              ".meta-value{text-align:right;font-weight:600;max-width:22rem;overflow-wrap:anywhere;}" +
              ".muted{color:var(--muted);font-weight:500;}" +
              ".actions{display:flex;flex-wrap:wrap;gap:12px;margin-top:22px;}" +
              ".actions a{display:inline-flex;align-items:center;justify-content:center;padding:13px 18px;border-radius:999px;text-decoration:none;font-weight:800;letter-spacing:.01em;background:linear-gradient(135deg,var(--accent),var(--accent-2));color:#fff;box-shadow:0 10px 30px rgba(154,52,18,.22);}" +
              ".actions a:hover{transform:translateY(-1px);}" +
              ".aside-copy{margin:0;color:var(--muted);line-height:1.7;}" +
              "@media (max-width:780px){.hero,.content{grid-template-columns:1fr;}.avatar{width:112px;height:112px;border-radius:22px;}.title{max-width:none;}}" +
              "</style></head><body>" +
              "<!-- proof:" + tail5 + " -->" +
              "<main class=\"shell\"><section class=\"panel\">" +
              "<div class=\"hero\">" +
              picturePanel +
              "<div>" +
              "<p class=\"eyebrow\">Formic Landing Page</p>" +
              "<h1 class=\"title\">" + ctx.name + "</h1>" +
              "<div class=\"status-badge\"><span class=\"status-dot\"></span>" + status + "</div>" +
              "<p class=\"lede\">A cleaner generated surface for the formic demo. The page keeps the modeled identity fields visible while presenting them as a composed profile card instead of raw tokens.</p>" +
              "</div></div>" +
              "<div class=\"content\">" +
              "<section class=\"card\">" +
              "<p class=\"card-title\">Profile</p>" +
              "<div class=\"meta-grid\">" +
              "<div class=\"meta-row\"><span class=\"meta-label\">Name</span><span class=\"meta-value\">" + ctx.name + "</span></div>" +
              "<div class=\"meta-row\"><span class=\"meta-label\">Email</span>" + emailPanel + "</div>" +
              "<div class=\"meta-row\"><span class=\"meta-label\">Picture</span>" + pictureMeta + "</div>" +
              "<div class=\"meta-row\"><span class=\"meta-label\">Session</span><span class=\"meta-value\">" + status + "</span></div>" +
              "</div>" +
              "<div class=\"actions\">" + action + "</div>" +
              "</section>" +
              "<aside class=\"card\">" +
              "<p class=\"card-title\">Notes</p>" +
              "<p class=\"aside-copy\">This interface is generated from Dafny and rendered through the ASP.NET host. The profile action reflects the current authentication state and the layout intentionally favors a presentation layer that feels designed instead of incidental.</p>" +
              "</aside>" +
              "</div></section></main></body></html>";

      assert html != "";
      assert html == "<html>|" + statusPiece + "|" + userPiece + "|" + emailPiece + "|" + picturePiece + "|" + actionPiece + "|" + closingPiece;

      var statusPrefix := "<html>|status|";
      var statusSuffix := "|" + userPiece + "|" + emailPiece + "|" + picturePiece + "|" + actionPiece + "|" + closingPiece;
      var statusHaystack := statusPrefix + status + statusSuffix;
      FormicProofHelpers.ContainsInserted(statusPrefix, status, statusSuffix);
      assert html == statusHaystack;
      assert Contains(statusHaystack, status);
      assert Contains(html, status);

      var namePrefix := "<html>|" + statusPiece + "|user|";
      var nameSuffix := "|" + emailPiece + "|" + picturePiece + "|" + actionPiece + "|" + closingPiece;
      var nameHaystack := namePrefix + ctx.name + nameSuffix;
      FormicProofHelpers.ContainsInserted(namePrefix, ctx.name, nameSuffix);
      assert html == nameHaystack;
      assert Contains(nameHaystack, ctx.name);
      assert Contains(html, ctx.name);

      var actionPrefix := "<html>|" + statusPiece + "|" + userPiece + "|" + emailPiece + "|" + picturePiece + "|action|";
      var actionSuffix := "|" + closingPiece;
      var actionHaystack := actionPrefix + action + actionSuffix;
      FormicProofHelpers.ContainsInserted(actionPrefix, action, actionSuffix);
      assert html == actionHaystack;
      assert Contains(actionHaystack, action);
      assert Contains(html, action);

      if ctx.email != "" {
        var emailPrefix := "<html>|" + statusPiece + "|" + userPiece + "|email|";
        var emailSuffix := "|" + picturePiece + "|" + actionPiece + "|" + closingPiece;
        var emailHaystack := emailPrefix + ctx.email + emailSuffix;
        FormicProofHelpers.ContainsInserted(emailPrefix, ctx.email, emailSuffix);
        assert html == emailHaystack;
        assert Contains(emailHaystack, ctx.email);
        assert Contains(html, ctx.email);
      }

      if ctx.picture != "" {
        var picturePrefix := "<html>|" + statusPiece + "|" + userPiece + "|" + emailPiece + "|picture|";
        var pictureSuffix := "|" + actionPiece + "|" + closingPiece;
        var pictureHaystack := picturePrefix + ctx.picture + pictureSuffix;
        FormicProofHelpers.ContainsInserted(picturePrefix, ctx.picture, pictureSuffix);
        assert html == pictureHaystack;
        assert Contains(pictureHaystack, ctx.picture);
        assert Contains(html, ctx.picture);
      }

      assert ctx.email == "" || Contains(html, ctx.email);
      assert ctx.picture == "" || Contains(html, ctx.picture);

      if ctx.authenticated {
        var missingAction := Link("Sign in", "/login");

        assert missingAction == Link("Sign in", "/login");
        assert missingAction == "<a href=\"/login\">Sign in</a>";
        assert '|' !in "<a href=\"/login\">Sign in</a>";
        FormicProofHelpers.LoginLinkHasNoBar();
        assert !Contains(missingAction, "|");
        assert status == "Signed in";
        assert action == Link("Log out", "/logout");
        assert action == "<a href=\"/logout\">Log out</a>";
        assert Contains(html, "Signed in");
        assert Contains(html, Link("Log out", "/logout"));

        assert !Contains("<html>", missingAction);
        assert !Contains("status", missingAction);
        assert !Contains(status, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("status", status, missingAction);
        assert statusPiece == "status|" + status;
        assert !Contains("status|" + status, missingAction);
        assert !Contains(statusPiece, missingAction);

        assert !Contains("user", missingAction);
        assert !Contains(ctx.name, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("user", ctx.name, missingAction);
        var userMissingHaystack := "user" + "|" + ctx.name;
        assert userPiece == "user|" + ctx.name;
        assert userMissingHaystack == "user|" + ctx.name;
        assert !Contains(userMissingHaystack, missingAction);
        assert !Contains(userPiece, missingAction);

        assert !Contains("email", missingAction);
        assert !Contains(ctx.email, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("email", ctx.email, missingAction);
        var emailMissingHaystack := "email" + "|" + ctx.email;
        assert emailPiece == "email|" + ctx.email;
        assert emailMissingHaystack == "email|" + ctx.email;
        assert !Contains(emailMissingHaystack, missingAction);
        assert !Contains(emailPiece, missingAction);

        assert !Contains("picture", missingAction);
        assert !Contains(ctx.picture, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("picture", ctx.picture, missingAction);
        var pictureMissingHaystack := "picture" + "|" + ctx.picture;
        assert picturePiece == "picture|" + ctx.picture;
        assert pictureMissingHaystack == "picture|" + ctx.picture;
        assert !Contains(pictureMissingHaystack, missingAction);
        assert !Contains(picturePiece, missingAction);

        assert !Contains("action", missingAction);
        FormicProofHelpers.LogoutLinkDoesNotContainLoginLink();
        assert !Contains(action, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("action", action, missingAction);
        var actionMissingHaystack := "action" + "|" + action;
        assert actionPiece == "action|" + action;
        assert actionMissingHaystack == "action|" + action;
        assert !Contains(actionMissingHaystack, missingAction);
        assert !Contains(actionPiece, missingAction);

        assert !Contains(closingPiece, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(actionPiece, closingPiece, missingAction);
        assert !Contains(tail1, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(picturePiece, tail1, missingAction);
        assert !Contains(tail2, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(emailPiece, tail2, missingAction);
        assert !Contains(tail3, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(userPiece, tail3, missingAction);
        assert !Contains(tail4, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(statusPiece, tail4, missingAction);
        assert !Contains(tail5, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("<html>", tail5, missingAction);
        var htmlMissingHaystack := "<html>" + "|" + tail5;
        assert html == htmlMissingHaystack;
        assert !Contains(htmlMissingHaystack, missingAction);
        assert !Contains(html, missingAction);

        assert ctx.authenticated ==
          (Contains(html, "Signed in") &&
           Contains(html, Link("Log out", "/logout")));
        assert !(Contains(html, "Anonymous") &&
                 Contains(html, Link("Sign in", "/login")));
        assert !ctx.authenticated ==
          (Contains(html, "Anonymous") &&
           Contains(html, Link("Sign in", "/login")));
      } else {
        var missingAction := Link("Log out", "/logout");

        assert missingAction == Link("Log out", "/logout");
        assert missingAction == "<a href=\"/logout\">Log out</a>";
        assert '|' !in "<a href=\"/logout\">Log out</a>";
        FormicProofHelpers.LogoutLinkHasNoBar();
        assert !Contains(missingAction, "|");
        assert status == "Anonymous";
        assert action == Link("Sign in", "/login");
        assert Contains(html, status);
        assert Contains(html, action);
        assert Contains(html, "Anonymous");
        assert Contains(html, Link("Sign in", "/login"));

        assert !Contains("<html>", missingAction);
        assert !Contains("status", missingAction);
        assert !Contains(status, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("status", status, missingAction);
        assert statusPiece == "status|" + status;
        assert !Contains("status|" + status, missingAction);
        assert !Contains(statusPiece, missingAction);

        assert !Contains("user", missingAction);
        assert !Contains(ctx.name, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("user", ctx.name, missingAction);
        var userMissingHaystack := "user" + "|" + ctx.name;
        assert userPiece == "user|" + ctx.name;
        assert userMissingHaystack == "user|" + ctx.name;
        assert !Contains(userMissingHaystack, missingAction);
        assert !Contains(userPiece, missingAction);

        assert !Contains("email", missingAction);
        assert !Contains(ctx.email, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("email", ctx.email, missingAction);
        var emailMissingHaystack := "email" + "|" + ctx.email;
        assert emailPiece == "email|" + ctx.email;
        assert emailMissingHaystack == "email|" + ctx.email;
        assert !Contains(emailMissingHaystack, missingAction);
        assert !Contains(emailPiece, missingAction);

        assert !Contains("picture", missingAction);
        assert !Contains(ctx.picture, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("picture", ctx.picture, missingAction);
        var pictureMissingHaystack := "picture" + "|" + ctx.picture;
        assert picturePiece == "picture|" + ctx.picture;
        assert pictureMissingHaystack == "picture|" + ctx.picture;
        assert !Contains(pictureMissingHaystack, missingAction);
        assert !Contains(picturePiece, missingAction);

        assert !Contains("action", missingAction);
        assert !Contains(action, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("action", action, missingAction);
        var actionMissingHaystack := "action" + "|" + action;
        assert actionPiece == "action|" + action;
        assert actionMissingHaystack == "action|" + action;
        assert !Contains(actionMissingHaystack, missingAction);
        assert !Contains(actionPiece, missingAction);

        assert !Contains(closingPiece, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(actionPiece, closingPiece, missingAction);
        assert !Contains(tail1, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(picturePiece, tail1, missingAction);
        assert !Contains(tail2, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(emailPiece, tail2, missingAction);
        assert !Contains(tail3, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(userPiece, tail3, missingAction);
        assert !Contains(tail4, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar(statusPiece, tail4, missingAction);
        assert !Contains(tail5, missingAction);
        FormicProofHelpers.NoContainsJoinedByBar("<html>", tail5, missingAction);
        var htmlMissingHaystack := "<html>" + "|" + tail5;
        assert html == htmlMissingHaystack;
        assert !Contains(htmlMissingHaystack, missingAction);
        assert !Contains(html, missingAction);

        assert !(Contains(html, "Signed in") &&
                 Contains(html, Link("Log out", "/logout")));
        assert ctx.authenticated ==
          (Contains(html, "Signed in") &&
           Contains(html, Link("Log out", "/logout")));
        assert !ctx.authenticated ==
          (Contains(html, "Anonymous") &&
           Contains(html, Link("Sign in", "/login")));
      }

      payload := ReturnType.Content(html);
    }
  }

  class LoginChallengePage extends IGenerator {

    constructor () {}

    predicate PreCondition(u: UserInfo, db: Database?) { true }
    twostate predicate PostCondition(u: UserInfo, payload: ReturnType, db: Database?)
      reads if db == null then {} else {db}
    {
      LoginPost(u, payload)
    }

    method Generate(ctx: UserInfo) returns (payload: ReturnType)
      requires PreCondition(ctx, db)
      modifies this, if db == null then {} else {db}
      ensures PostCondition(ctx, payload, db)
    {
      payload := ReturnType.ChallengeGoogle("/");
    }
  }

  class SecurePage extends IGenerator {

    constructor () {}

    predicate PreCondition(u: UserInfo, db: Database?) { true }
    twostate predicate PostCondition(u: UserInfo, payload: ReturnType, db: Database?)
      reads if db == null then {} else {db}
    {
      SecurePost(u, payload)
    }

    method Generate(ctx: UserInfo) returns (payload: ReturnType)
      requires PreCondition(ctx, db)
      modifies this, if db == null then {} else {db}
      ensures PostCondition(ctx, payload, db)
    {
      if ctx.authenticated {
        var logout := Link("Log out", "/logout");
        var authText := "You are authenticated.";
        var htmlPrefix := "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" />" +
                          "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />" +
                          "<title>Secure</title></head><body><h1>Hello, ";
        var nameSuffix := "!</h1><p>" + authText + "</p><p>" + logout + "</p></body></html>";
        var html := htmlPrefix + ctx.name + nameSuffix;

        assert html != "";
        assert html == htmlPrefix + ctx.name + nameSuffix;
        FormicProofHelpers.ContainsInserted(htmlPrefix, ctx.name, nameSuffix);
        assert Contains(html, ctx.name);

        var authPrefix := htmlPrefix + ctx.name + "!</h1><p>";
        var authSuffix := "</p><p>" + logout + "</p></body></html>";
        assert html == authPrefix + authText + authSuffix;
        FormicProofHelpers.ContainsInserted(authPrefix, authText, authSuffix);
        assert Contains(html, authText);
        assert Contains(html, "You are authenticated.");

        var logoutPrefix := htmlPrefix + ctx.name + "!</h1><p>" + authText + "</p><p>";
        var logoutSuffix := "</p></body></html>";
        assert html == logoutPrefix + logout + logoutSuffix;
        FormicProofHelpers.ContainsInserted(logoutPrefix, logout, logoutSuffix);
        assert Contains(html, logout);
        assert Contains(html, Link("Log out", "/logout"));

        payload := ReturnType.Content(html);
      } else {
        payload := ReturnType.ChallengeGoogle("/secure");
      }
    }
  }

  class SaveUserPage extends IGenerator {

    constructor () {}

    predicate PreCondition(u: UserInfo, db: Database?) {
      !(u.authenticated && u.email != "") || db != null
    }
    twostate predicate PostCondition(u: UserInfo, payload: ReturnType, db: Database?)
      reads if db == null then {} else {db}
    {
      SaveUserPost(u, payload, db)
    }

    method AddPersistedUser(ctx: UserInfo)
      requires ctx.authenticated
      requires ctx.email != ""
      requires db != null
      modifies this, db
      ensures SaveUserDbPost(ctx, db)
    {
      var saved := DbValue.DbPersistedUser(PersistedUser(ctx.email, ctx.name, ctx.picture));
      db.Save(saved);
    }

    method Generate(ctx: UserInfo) returns (payload: ReturnType)
      requires PreCondition(ctx, db)
      modifies this, if db == null then {} else {db}
      ensures PostCondition(ctx, payload, db)
    {
      if ctx.authenticated && ctx.email != "" {
        assert db != null;
        AddPersistedUser(ctx);
        payload := ReturnType.Content(
          "<!doctype html><html lang=\"en\"><body><h1>Saved user</h1><p>" +
          ctx.email +
          "</p></body></html>");
      } else {
        payload := ReturnType.ChallengeGoogle("/save_user");
      }
    }

  }

}
