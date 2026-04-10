module DuctTools {

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

  trait {:termination false} IGenerator {

    var db: Database

    method SetDb(db: Database)
      modifies this
      ensures this.db == db
    {
      this.db := db;
    }

    predicate PreCondition(u: UserInfo, db: Database)

    twostate predicate PostCondition(u: UserInfo, payload: ReturnType, db: Database)
      reads db

    method Generate(user: UserInfo) returns (payload: ReturnType)
      requires PreCondition(user, db)
      modifies this, db
      ensures PostCondition(user, payload, db)
  }

  class ApiEndpoint {
    var apiUrl: string
    var returnType: ReturnType
    var generator: IGenerator

    constructor(apiUrl: string, rt: ReturnType, generator: IGenerator)
      requires apiUrl != ""
      requires apiUrl[0] == '/' // simple invariant: path-like
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
