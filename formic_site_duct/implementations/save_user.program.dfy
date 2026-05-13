module DuctSaveUserImpl {

  import opened DB
  import opened DuctTools
  import opened DuctSpecs

  class SaveUserPage extends SaveUserPageSpec {

    constructor () {}

    function Implementation(u: UserInfo): GeneratedEndpointResult
    {
      if u.authenticated && u.email != "" then
        GeneratedEndpointResult(
          Insert(DbPersistedUser(PersistedUser(u.email, u.name, u.picture))),
          Redirect("/"))
      else
        GeneratedEndpointResult(Return, ChallengeGoogle("/signin-google"))
    }

    lemma ProveImplementationCorrect(u: UserInfo)
      requires PreCondition(u)
      ensures ImplementationCorrect(u)
    {
      assert forall before: seq<DbValue> ::
        PostCondition(
          u,
          before,
          Implementation(u).response,
          ExecuteProgram(before, Implementation(u).program)) by {
        forall before: seq<DbValue>
          ensures PostCondition(
            u,
            before,
            Implementation(u).response,
            ExecuteProgram(before, Implementation(u).program))
        {
          if u.authenticated && u.email != "" {
            var row := DbPersistedUser(PersistedUser(u.email, u.name, u.picture));

            assert Implementation(u).response == Redirect("/");
            assert KeyOf(row) == PersistedUserKey(u.email);
            assert Implementation(u).program == Insert(row);
            assert ProgramOperations(before, Implementation(u).program) == [Put(row)];
            assert ExecuteProgram(before, Implementation(u).program) == ExecuteOperations(before, [Put(row)]);
            assert ExecuteProgram(before, Implementation(u).program)
                 == FilterEntries(before, PersistedUserKey(u.email)) + [row];
          } else {
            assert Implementation(u).response == ChallengeGoogle("/signin-google");
            assert Implementation(u).program == Return;
            assert ProgramOperations(before, Implementation(u).program) == [];
            assert ExecuteProgram(before, Implementation(u).program) == before;
          }
        }
      }
    }
  }
}
