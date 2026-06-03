module SaveUserImpl {

  import opened DB
  import opened Tools
  import opened SaveUserSpecs

  class SaveUserPage extends SaveUserPageSpec {

    constructor () {}

    function Implementation(u: UserInfo, before: seq<DbValue>): GeneratedEndpointResult
    {
      if u.authenticated && u.email != "" then
        GeneratedEndpointResult(
          Insert(DbPersistedUser(PersistedUser(u.email, u.name, u.picture))),
          Redirect("/"))
      else
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
          if u.authenticated && u.email != "" {
            var row := DbPersistedUser(PersistedUser(u.email, u.name, u.picture));

            assert Implementation(u, before).response == Redirect("/");
            assert KeyOf(row) == PersistedUserKey(u.email);
            assert Implementation(u, before).program == Insert(row);
            assert ProgramOperations(before, Implementation(u, before).program) == [Put(row)];
            assert ExecuteProgram(before, Implementation(u, before).program) == ExecuteOperations(before, [Put(row)]);
            assert ExecuteProgram(before, Implementation(u, before).program)
                 == FilterEntries(before, PersistedUserKey(u.email)) + [row];
          } else {
            assert Implementation(u, before).response == ChallengeGoogle("/save_user");
            assert Implementation(u, before).program == Return;
            assert ProgramOperations(before, Implementation(u, before).program) == [];
            assert ExecuteProgram(before, Implementation(u, before).program) == before;
          }
        }
      }
    }
  }
}
