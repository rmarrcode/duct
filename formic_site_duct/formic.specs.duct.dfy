module DuctSpecs {

  import opened DuctTools
  import opened SpecsTools
  import opened DB

  predicate LandingPagePre(ctx: UserInfo)
  {
    ctx.name != "" &&
    !Contains(ctx.name, "Signed in") &&
    !Contains(ctx.name, "Anonymous") &&
    !Contains(ctx.name, Link("Log out", "/logout")) &&
    !Contains(ctx.name, Link("Sign in", "/login")) &&
    !Contains(ctx.email, "Signed in") &&
    !Contains(ctx.email, "Anonymous") &&
    !Contains(ctx.email, Link("Log out", "/logout")) &&
    !Contains(ctx.email, Link("Sign in", "/login")) &&
    !Contains(ctx.picture, "Signed in") &&
    !Contains(ctx.picture, "Anonymous") &&
    !Contains(ctx.picture, Link("Log out", "/logout")) &&
    !Contains(ctx.picture, Link("Sign in", "/login"))
  }

  predicate LandingPagePayloadPost(ctx: UserInfo, payload: ReturnType)
  {
    payload.Content? &&
    var html := payload.body;
    html != "" &&
    Contains(html, ctx.name) &&
    (ctx.email == "" || Contains(html, ctx.email)) &&
    (ctx.picture == "" || Contains(html, ctx.picture)) &&
    (ctx.authenticated ==
      (Contains(html, "Signed in") &&
       Contains(html, Link("Log out", "/logout")))) &&
    (!ctx.authenticated ==
      (Contains(html, "Anonymous") &&
       Contains(html, Link("Sign in", "/login"))))
  }

  predicate LandingPagePost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
  {
    LandingPagePayloadPost(ctx, payload) &&
    after == before
  }

  predicate LoginPost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
  {
    payload == ReturnType.ChallengeGoogle("/save_user") &&
    after == before
  }

  predicate SecurePost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
  {
    after == before &&
    if ctx.authenticated then
      payload.Content? &&
      Contains(payload.body, ctx.name) &&
      Contains(payload.body, "You are authenticated")
    else
      payload == ReturnType.ChallengeGoogle("/secure")
  }

  function {:compile true} SaveUserOperations(ctx: UserInfo): seq<DbChange>
  {
    if ctx.authenticated && ctx.email != "" then
      [DbChange.Put(DbValue.DbPersistedUser(PersistedUser(ctx.email, ctx.name, ctx.picture)))]
    else
      []
  }

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

  trait {:termination false} LandingPageSpec extends IGeneratorCore {

    predicate PreCondition(u: UserInfo)
    {
      LandingPagePre(u)
    }

    ghost predicate PostCondition(
      u: UserInfo,
      before: seq<DbValue>,
      payload: ReturnType,
      after: seq<DbValue>)
    {
      LandingPagePost(u, before, payload, after)
    }
  }

  trait {:termination false} LoginChallengePageSpec extends IGeneratorCore {

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
      LoginPost(u, before, payload, after)
    }
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

  trait {:termination false} SecurePageSpec extends IGeneratorCore {

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
      SecurePost(u, before, payload, after)
    }
  }

}
