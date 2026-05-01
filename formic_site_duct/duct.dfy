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

  trait IGeneratorSpec {

    predicate PreCondition(u: UserInfo)

    ghost predicate PostCondition(
      u: UserInfo,
      before: seq<DbValue>,
      payload: ReturnType,
      after: seq<DbValue>)
  }

  trait {:termination false} IGeneratorCore extends IGeneratorSpec {

    function Program(u: UserInfo): DbProgram
    function Response(u: UserInfo): ReturnType

    ghost predicate ImplementationCorrect(u: UserInfo)
    {
      forall before: seq<DbValue> ::
        PostCondition(u, before, Response(u), ExecuteProgram(before, Program(u)))
    }

    ghost predicate GeneratePost(
      u: UserInfo,
      payload: ReturnType,
      prog: DbProgram)
    {
      payload == Response(u) &&
      prog == Program(u) &&
      forall before: seq<DbValue> ::
        PostCondition(u, before, payload, ExecuteProgram(before, prog))
    }

    method Generate(u: UserInfo) returns (payload: ReturnType, prog: DbProgram)
      requires PreCondition(u)
      ensures payload == Response(u)
      ensures prog == Program(u)
    {
      payload := Response(u);
      prog := Program(u);
    }
  }

  //trait {:termination false} IGenerator {

    //var db: Database
    //method GetOperations() returns (ops: DbProgram) { return db.GetOperations() }

    //predicate RestPreCondition(u: UserInfo, db: Database)
    //predicate RestPostCondition(u: UserInfo, payload: ReturnType, db_before: Database, db_after: Database)

    //predicate DbPreCondition(u: UserInfo, db_before: Database)
    //predicate PreCondition(u: UserInfo, db: Database) {
      //DbPreCondition(u, db)
    //}

    //// only one that spec defines 
    //predicate DbPostCondition(u: UserInfo, db_before: Database, db_after: Database)
    //predicate DbOpsCorrect(u: UserInfo, operations: DbProgram) //, db_post_condition: (UserInfo, Database, Database) -> bool)
      //forall before DbPostCondition(u, before, ExecuteProgram(before, operations))
    //predicate PostCondition(u: UserInfo, operations: DbProgram) {
      //DbOpsCorrect(u, operations) &&
      //WellForned(operations)
    //}

    //method Generate(user: UserInfo) returns (api_result: Map<string, ReturnType>)
      //requires PreCondition(user, db)
      //ensures PostCondition(u, operations) 
  //}

  //trait {:termination false} IGenerator {

    //var db: Database
    //method GetOperations() returns (ops: DbProgram) { return db.GetOperations() }

    //predicate RestPreCondition(u: UserInfo, db: Database)
    //predicate RestPostCondition(u: UserInfo, payload: ReturnType, db_before: Database, db_after: Database)

    //predicate DbPreCondition(u: UserInfo, db_before: Database)
    //predicate PreCondition(u: UserInfo, db: Database) {
      //DbPreCondition(u, db)
    //}

    //// only one that spec defines 
    //predicate DbPostCondition(u: UserInfo, db_before: Database, db_after: Database)
    //predicate DbOpsCorrect(u: UserInfo, operations: DbProgram) //, db_post_condition: (UserInfo, Database, Database) -> bool)
      //forall before DbPostCondition(u, before, ExecuteProgram(before, operations))
    //predicate PostCondition(u: UserInfo, operations: DbProgram) {
      //DbOpsCorrect(u, operations) &&
      //WellForned(operations)
    //}

    //method Generate(user: UserInfo) returns (api_result: Map<string, ReturnType>)
      //requires PreCondition(user, db)
      //ensures PostCondition(u, operations) 
  //}

  //trait {:termination false} IGenerator {

    //var db: Database
    //method GetOperations() returns (ops: DbProgram) { return db.GetOperations() }

    //predicate RestPreCondition(u: UserInfo, db: Database)
    //predicate RestPostCondition(u: UserInfo, payload: ReturnType, db_before: Database, db_after: Database)

    //predicate DbPreCondition(u: UserInfo, db_before: Database)
    //predicate PreCondition(u: UserInfo, db: Database) {
      //DbPreCondition(u, db)
    //}

    //// only one that spec defines 
    //predicate DbPostCondition(u: UserInfo, db_before: Database, db_after: Database)
    //predicate DbOpsCorrect(u: UserInfo, operations: DbProgram) //, db_post_condition: (UserInfo, Database, Database) -> bool)
      //forall before DbPostCondition(u, before, ExecuteProgram(before, operations))
    //predicate PostCondition(u: UserInfo, operations: DbProgram) {
      //DbOpsCorrect(u, operations) &&
      //WellForned(operations)
    //}

    //method Generate(user: UserInfo) returns (api_result: Map<string, ReturnType>)
      //requires PreCondition(user, db)
      //ensures PostCondition(u, operations) 
  //}

  //trait {:termination false} IGenerator {

    //var db: Database
    //method GetOperations() returns (ops: DbProgram) { return db.GetOperations() }

    //predicate RestPreCondition(u: UserInfo, db: Database)
    //predicate RestPostCondition(u: UserInfo, payload: ReturnType, db_before: Database, db_after: Database)

    //predicate DbPreCondition(u: UserInfo, db_before: Database)
    //predicate PreCondition(u: UserInfo, db: Database) {
      //DbPreCondition(u, db)
    //}

    //// only one that spec defines 
    //predicate DbPostCondition(u: UserInfo, db_before: Database, db_after: Database)
    //predicate DbOpsCorrect(u: UserInfo, operations: DbProgram) //, db_post_condition: (UserInfo, Database, Database) -> bool)
      //forall before DbPostCondition(u, before, ExecuteProgram(before, operations))
    //predicate PostCondition(u: UserInfo, operations: DbProgram) {
      //DbOpsCorrect(u, operations) &&
      //WellForned(operations)
    //}

    //method Generate(user: UserInfo) returns (api_result: Map<string, ReturnType>)
      //requires PreCondition(user, db)
      //ensures PostCondition(u, operations) 
  //}

  //trait {:termination false} IGenerator {

    //var db: Database
    //method GetOperations() returns (ops: DbProgram) { return db.GetOperations() }

    //predicate RestPreCondition(u: UserInfo, db: Database)
    //predicate RestPostCondition(u: UserInfo, payload: ReturnType, db_before: Database, db_after: Database)

    //predicate DbPreCondition(u: UserInfo, db_before: Database)
    //predicate PreCondition(u: UserInfo, db: Database) {
      //DbPreCondition(u, db)
    //}

    //// only one that spec defines 
    //predicate DbPostCondition(u: UserInfo, db_before: Database, db_after: Database)
    //predicate DbOpsCorrect(u: UserInfo, operations: DbProgram) //, db_post_condition: (UserInfo, Database, Database) -> bool)
      //forall before DbPostCondition(u, before, ExecuteProgram(before, operations))
    //predicate PostCondition(u: UserInfo, operations: DbProgram) {
      //DbOpsCorrect(u, operations) &&
      //WellForned(operations)
    //}

    //method Generate(user: UserInfo) returns (api_result: Map<string, ReturnType>)
      //requires PreCondition(user, db)
      //ensures PostCondition(u, operations) 
  //}

  class ApiEndpoint {
    var apiUrl: string
    var returnType: ReturnType
    var generator: IGeneratorCore

    constructor(apiUrl: string, rt: ReturnType, generator: IGeneratorCore)
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
