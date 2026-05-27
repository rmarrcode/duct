module Tools {

  import opened DB

  datatype UserInfo = UserInfo(
    name: string,
    email: string,
    picture: string,
    authenticated: bool)

  datatype ReturnType = 
    Content(body: string)
  | ChallengeGoogle(returnUrl: string)
  | Redirect(url: string)

  datatype GeneratedEndpointResult = GeneratedEndpointResult(
    program: DbProgram,
    response: ReturnType)

  trait IGeneratorSpec {

    predicate PreCondition(u: UserInfo)

    ghost predicate PostCondition(
      u: UserInfo,
      before: seq<DbValue>,
      payload: ReturnType,
      after: seq<DbValue>)
  }

  trait {:termination false} IGeneratorCore extends IGeneratorSpec {

    function Implementation(u: UserInfo, before: seq<DbValue>): GeneratedEndpointResult

    ghost predicate ImplementationCorrect(u: UserInfo)
    {
      forall before: seq<DbValue> ::
        PostCondition(
          u,
          before,
          Implementation(u, before).response,
          ExecuteProgram(before, Implementation(u, before).program))
    }

    method Generate(u: UserInfo, before: seq<DbValue>) returns (prog: DbProgram, payload: ReturnType)
      requires PreCondition(u)
      ensures prog == Implementation(u, before).program
      ensures payload == Implementation(u, before).response
    {
      var result := Implementation(u, before);
      prog := result.program;
      payload := result.response;
    }
  }

  class ApiEndpoint {
    var apiUrl: string
    var generator: IGeneratorCore

    constructor(apiUrl: string, generator: IGeneratorCore)
      requires apiUrl != ""
      requires apiUrl[0] == '/' // simple invariant: path-like
      ensures this.apiUrl == apiUrl
      ensures this.generator == generator
    {
      this.apiUrl := apiUrl;
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

  function Contains(haystack: string, needle: string): bool
    decreases |haystack|
  {
    if |needle| == 0 then true
    else if |haystack| < |needle| then false
    else haystack[0 .. |needle|] == needle || Contains(haystack[1..], needle)
  }

  function {:compile true} Link(linkLabel: string, url: string): string {
    "<a href=\"" + url + "\">" + linkLabel + "</a>"
  }

}
