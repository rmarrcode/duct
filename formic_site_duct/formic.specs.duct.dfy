module DuctSpecs {
  import opened DuctApi

  function Contains(haystack: string, needle: string): bool {
    exists i :: 0 <= i <= |haystack| - |needle| && haystack[i .. i + |needle|] == needle
  }

  function Link(label: string, url: string): string {
    "<a href=\"" + url + "\">" + label + "</a>"
  }

  trait FormicLandingSpec extends IGenerator {
    method Generate(ctx: UserInfo) returns (html: string);
      requires ctx.name != ""                // minimal precondition: we have a display name
      ensures html != ""
      ensures Contains(html, ctx.name)       // name must appear
      ensures (ctx.email == "" ==> true) && (ctx.email != "" ==> Contains(html, ctx.email))
      ensures (ctx.picture == "" ==> true) && (ctx.picture != "" ==> Contains(html, ctx.picture))
      ensures ctx.authenticated ==> (
        Contains(html, "Signed in") &&
        Contains(html, Link("Log out", "/logout")))
      ensures !ctx.authenticated ==> (
        Contains(html, "Anonymous") &&
        Contains(html, Link("Sign in", "/login")))
  }
}
