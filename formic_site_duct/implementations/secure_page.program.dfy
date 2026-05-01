module DuctSecureImpl {

  import opened DB
  import opened DuctTools
  import opened DuctSpecs
  import opened SpecsTools

  function SecureHtml(ctx: UserInfo): string
  {
    var logout := Link("Log out", "/logout");
    var authText := "You are authenticated.";
    "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" />" +
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />" +
    "<title>Secure</title></head><body><h1>Hello, " +
    ctx.name +
    "!</h1><p>" + authText + "</p><p>" + logout + "</p></body></html>"
  }

  class SecurePage extends SecurePageSpec {

    constructor () {}

    function Response(u: UserInfo): ReturnType
    {
      if u.authenticated then
        Content(SecureHtml(u))
      else
        ChallengeGoogle("/secure")
    }

    function Program(u: UserInfo): DbProgram
    {
      Return
    }
  }
}
