module DuctSaveUserImpl {

  import opened DB
  import opened DuctTools
  import opened DuctSpecs

  class SaveUserPage extends SaveUserPageSpec {

    constructor () {}

    function Response(u: UserInfo): ReturnType
    {
      if u.authenticated && u.email != "" then
        Redirect("/")
      else
        ChallengeGoogle("/save_user")
    }

    function Program(u: UserInfo): DbProgram
    {
      if u.authenticated && u.email != "" then
        Insert(DbPersistedUser(PersistedUser(u.email, u.name, u.picture)))
      else
        Return
    }

    lemma ProveImplementationCorrect(u: UserInfo)
      requires PreCondition(u)
      ensures ImplementationCorrect(u)
    {
      assert forall before: seq<DbValue> ::
        PostCondition(u, before, Response(u), ExecuteProgram(before, Program(u))) by {
        forall before: seq<DbValue>
          ensures PostCondition(u, before, Response(u), ExecuteProgram(before, Program(u)))
        {
          if u.authenticated && u.email != "" {
            var row := DbPersistedUser(PersistedUser(u.email, u.name, u.picture));

            assert Response(u) == Redirect("/");
            assert KeyOf(row) == PersistedUserKey(u.email);
            assert Program(u) == Insert(row);
            assert ProgramOperations(before, Program(u)) == [Put(row)];
            assert ExecuteProgram(before, Program(u)) == ExecuteOperations(before, [Put(row)]);
            assert ExecuteProgram(before, Program(u))
                 == FilterEntries(before, PersistedUserKey(u.email)) + [row];
          } else {
            assert Response(u) == ChallengeGoogle("/save_user");
            assert Program(u) == Return;
            assert ProgramOperations(before, Program(u)) == [];
            assert ExecuteProgram(before, Program(u)) == before;
          }
        }
      }
    }
  }
}
