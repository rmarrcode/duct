module LandingPageSpecs {

  import opened Tools
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
}
