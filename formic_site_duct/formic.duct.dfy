module FormicCatalog {

  import opened DuctApi

  function Contains(haystack: string, needle: string): bool {
    exists i :: 0 <= i <= |haystack| - |needle| && haystack[i .. i + |needle|] == needle
  }

  /// Helper to emit an anchor tag with custom label and url.
  function method Link(label: string, url: string): string {
    "<a href=" + url + ">" + label + "</a>"
  }

  class RenderHomeGenerator extends IGenerator {
    constructor () {}

    method Generate(ctx: UserInfo) returns (html: string)
      requires ctx.name != ""                // minimal precondition: we have a display name
      ensures html != ""
      ensures Contains(html, ctx.name)       // name must appear
      ensures (ctx.email == "" ==> true) && (ctx.email != "" ==> Contains(html, ctx.email))
      ensures (ctx.picture == "" ==> true) && (ctx.picture != "" ==> Contains(html, ctx.picture))
      ensures (ctx.authenticated == true) == (
        Contains(html, "Signed in") && 
        Contains(html, Link("Log Out", "/logout")))
      ensures (ctx.authenticated == false) ==> (
        Contains(html, "Anonymous") &&
        Contains(html, Link("Sign in", "/login"))
      ) 
    {
    }
  }

  class Catalog {
    static method Endpoints() returns (all: AllApiEndpoints)
      ensures |all.endpoints| == 1
    {
      var catalog := new AllApiEndpoints();
      var generator := new RenderHomeGenerator();
      var ep := new ApiEndpoint("/", ReturnType.Content, generator);
      catalog.Add(ep);
      return catalog;
    }
  }
}
