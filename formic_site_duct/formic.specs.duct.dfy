module DuctSpecs {

  import opened DuctTools
  import opened SpecsTools

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

  predicate LandingPagePost(ctx: UserInfo, payload: ReturnType)
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

  predicate LoginPost(ctx: UserInfo, payload: ReturnType) 
  {
    payload == ReturnType.ChallengeGoogle("/")
  }

  predicate SecurePost(ctx: UserInfo, payload: ReturnType)
  {
    (ctx.authenticated ==>
      payload.Content? &&
      Contains(payload.body, ctx.name) && 
      Contains(payload.body, "You are authenticated")
    ) &&
    (!ctx.authenticated ==>
      payload.Content? &&
      Contains(payload.body, "You are not authenticated")
    )
  }

}


dotnet add formic_site_cs/FormicSite.csproj package Microsoft.EntityFrameworkCore.Sqlite
