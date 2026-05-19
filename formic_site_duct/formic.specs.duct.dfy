module DuctSpecs {

  import opened DuctTools
  import opened SpecsTools
  import opened DB

  predicate IsValidUserInfoField(field: string) {
    !Contains(field, "Signed in") &&
    !Contains(field, "Anonymous") &&
    !Contains(field, Link("Log out", "/logout")) &&
    !Contains(field, Link("Sign in", "/login"))
  }

  predicate LandingPagePre(ctx: UserInfo)
  {
    ctx.name != "" &&
    IsValidUserInfoField(ctx.name) &&
    IsValidUserInfoField(ctx.email) &&
    IsValidUserInfoField(ctx.picture)
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
       Contains(html, Link("Log out", "/logout")) &&
       Contains(html, Link("User Info", "/user_info")))) &&
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
    // The /login endpoint is only for initiating the sign-in flow.
    // It should always issue a challenge and never change the database.
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

  predicate SaveUserPost(ctx: UserInfo, before: seq<DbValue>, payload: ReturnType, after: seq<DbValue>)
  {
    // This endpoint is the callback after a successful Google sign-in.
    // The user's context MUST be authenticated.
    if ctx.authenticated && ctx.email != "" then
      var row := DbPersistedUser(PersistedUser(ctx.email, ctx.name, ctx.picture));
      payload == Redirect("/") &&
      after == FilterEntries(before, PersistedUserKey(ctx.email)) + [row]
    else
      // If an unauthenticated user somehow hits this URL, just send them back to the start.
      payload == ChallengeGoogle("/save_user") &&
      after == before
  }

  function DigitString(d: nat): string
    requires d < 10
  {
    if d == 0 then "0"
    else if d == 1 then "1"
    else if d == 2 then "2"
    else if d == 3 then "3"
    else if d == 4 then "4"
    else if d == 5 then "5"
    else if d == 6 then "6"
    else if d == 7 then "7"
    else if d == 8 then "8"
    else "9"
  }

  function NatToString(n: nat): string
  {
    if n < 10 then DigitString(n) else NatToString(n / 10) + DigitString(n % 10)
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

  trait {:termination false} UserInfoSpec extends IGeneratorCore {

    predicate PreCondition(u: UserInfo)
    {
      true
    }

    ghost predicate PostCondition(
      u: UserInfo,
      before: seq<DbValue>,
      payload: ReturnType,
      after: seq<DbValue>
    )
    {
      payload == Content(NatToString(|after|))
    }
  }

}