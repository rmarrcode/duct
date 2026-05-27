module LoginImpl {

  import opened DB
  import opened Tools
  import opened Specs

  class LoginChallengePage extends LoginChallengePageSpec {

    constructor () {}

    function Implementation(u: UserInfo, before: seq<DbValue>): GeneratedEndpointResult
    {
      GeneratedEndpointResult(Return, ChallengeGoogle("/save_user"))
    }

    lemma ProveImplementationCorrect(u: UserInfo)
      requires PreCondition(u)
      ensures ImplementationCorrect(u)
    {
      assert forall before: seq<DbValue> ::
        PostCondition(
          u,
          before,
          Implementation(u, before).response,
          ExecuteProgram(before, Implementation(u, before).program)) by {
        forall before: seq<DbValue>
          ensures PostCondition(
            u,
            before,
            Implementation(u, before).response,
            ExecuteProgram(before, Implementation(u, before).program))
        {
          assert Implementation(u, before).response == ChallengeGoogle("/save_user");
          assert Implementation(u, before).program == Return;
          assert ProgramOperations(before, Implementation(u, before).program) == [];
          assert ExecuteProgram(before, Implementation(u, before).program) == before;
        }
      }
    }
  }
}
