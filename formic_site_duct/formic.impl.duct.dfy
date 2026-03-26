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

  import opened DuctApi
  import opened DuctSpecs
  import opened SpecsTools
  import FormicProofHelpers

  /// Concrete landing page generator that satisfies the specs.
  class FormicLandingPage extends IGenerator {

    constructor () {}

    ghost predicate PreCondition(u: UserInfo) { LandingPagePre(u) }
    ghost predicate PostCondition(u: UserInfo, html: string) { LandingPagePost(u, html) }

    method Generate(ctx: UserInfo) returns (html: string)
      requires PreCondition(ctx)
      ensures PostCondition(ctx, html)
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

      html := "<html>|" + tail5;

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
    }
  }
}
