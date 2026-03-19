module DuctApi {

  datatype UserInfo = UserInfo(
    name: string,
    email: string,
    picture: string,
    authenticated: bool)

  class ApiEndpoint {
    var apiUrl: string;
    var user: UserInfo;
    datatype ReturnType = Content | Redirect

    constructor (apiUrl: string, user: UserInfo)
      requires apiUrl != ""
      requires apiUrl[0] == '/' // simple invariant: path-like
      ensures this.apiUrl == apiUrl
      ensures this.user == user
    {
      this.apiUrl := apiUrl;
      this.user := user;
    }

    function method Contains(haystack: string, needle: string): bool {
        exists i :: 0 <= i <= |haystack| - |needle| && haystack[i .. i + |needle|] == needle
    }

    method RenderHome(ctx: UserInfo) returns (html: string)
        requires ctx.name != ""                // minimal precondition: we have a display name
        // No other preconditions; unauthenticated users may have blank email/picture
        ensures html != ""
        ensures Contains(html, ctx.name)       // name must appear
        ensures (ctx.email == "" ==> true) && (ctx.email != "" ==> Contains(html, ctx.email))
        ensures (ctx.picture == "" ==> true) && (ctx.picture != "" ==> Contains(html, ctx.picture))
        ensures Contains(html, if ctx.authenticated then "Signed in" else "Anonymous")
        ensures ctx.authenticated == false ==> Contains(html, "Continue with Google") // sign-in button text
        ensures ctx.authenticated == true  ==> Contains(html, "Log out")               // sign-out option
    {
        // Implementation body can be provided or left blank (abstract) if you only need the contract.
    }

  }

  /// Collection of API endpoints.
  class AllApiEndpoints {
    var endpoints: seq<ApiEndpoint>;

    constructor ()
      ensures endpoints == []
    {
      endpoints := [];
    }

    method Add(ep: ApiEndpoint)
      requires ep != null
      ensures endpoints == old(endpoints) + [ep]
    {
      endpoints := endpoints + [ep];
    }

    method Count() returns (n: int)
      ensures n == |endpoints|
    {
      n := |endpoints|;
    }

    method Get(i: int) returns (ep: ApiEndpoint)
      requires 0 <= i < |endpoints|
      ensures ep == endpoints[i]
    {
      ep := endpoints[i];
    }
  }

}
