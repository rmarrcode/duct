module SaveUserSpecs {

  import opened Tools
  import opened DB

  predicate SaveUserPost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
  {
    if ctx.authenticated && ctx.email != "" then
      var row := DbPersistedUser(PersistedUser(ctx.email, ctx.name, ctx.picture));
      payload == Redirect("/") &&
      after == FilterEntries(before, PersistedUserKey(ctx.email)) + [row]
    else
      payload == ChallengeGoogle("/save_user") &&
      after == before
  }

  trait {:termination false} SaveUserPageSpec extends IGeneratorCore {

    predicate PreCondition(u: UserInfo)
    {
      true
    }

    ghost predicate PostCondition(
      u: UserInfo,
      before: seq<DbValue>,
      payload: ReturnType,
      after: seq<DbValue>)
    {
      SaveUserPost(u, before, payload, after)
    }
  }
}
