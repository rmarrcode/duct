module DuctApi {

  datatype ReturnType = Content | Redirect

  datatype UserInfo = UserInfo(
    name: string,
    email: string,
    picture: string,
    authenticated: bool)

  class ApiEndpoint {
    var apiUrl: string;
    var returnType: ReturnType;
    var generator: IGenerator;

    constructor(apiUrl: string, rt: ReturnType, generator: IGenerator)
      requires apiUrl != ""
      requires apiUrl[0] == '/' // simple invariant: path-like
      requires generator != null
      ensures this.apiUrl == apiUrl
      ensures this.returnType == rt
      ensures this.generator == generator
    {
      this.apiUrl := apiUrl;
      this.returnType := rt;
      this.generator := generator;
    }
  }

  /// Collection of API endpoints.
  class AllApiEndpoints {
    var endpoints: seq<ApiEndpoint>

    constructor ()
      ensures endpoints == []
    {
      endpoints := [];
    }

    method Add(ep: ApiEndpoint)
      requires ep != null
      modifies this
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


module SpecsTools {

  function Contains(haystack: string, needle: string): bool {
    exists i :: 0 <= i <= |haystack| - |needle| && haystack[i .. i + |needle|] == needle
  }

  function {:compile true} Link(label: string, url: string): string {
    "<a href=" + url + ">" + label + "</a>"
  }

  trait {:termination false} IGenerator {
    method Generate(user: UserInfo) returns (content: string)
      ensures content != ""
  }

}