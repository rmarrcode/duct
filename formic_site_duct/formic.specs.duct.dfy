module DuctSpecs {

  import opened DuctApi
  import opened SpecsTools

  ghost predicate LandingPagePre(ctx: UserInfo)
  {
    ctx.name != ""
  }

  ghost predicate LandingPagePost(ctx: UserInfo, html: string)
  {
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

}
