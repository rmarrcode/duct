include "duct.dfy"
include "formic.specs.duct.dfy"

module DuctImpl {

  import opened DuctApi
  import opened DuctSpecs
  import opened SpecsTools

  /// Concrete landing page generator that satisfies the specs.
  class FormicLandingPage extends IGenerator {

    constructor () {}

    ghost predicate PreCondition(u: UserInfo) { LandingPagePre(u) }
    ghost predicate PostCondition(u: UserInfo, html: string) { LandingPagePost(u, html) }

    method Generate(ctx: UserInfo) returns (html: string)
      requires PreCondition(ctx) 
      ensures PostCondition(ctx, html)
    {
      var status := if ctx.authenticated then "Signed in" else "Anonymous";
      var signIn := Link("Sign in", "/login");
      var logout := Link("Log out", "/logout");
      var emailPart := ctx.email;
      var picPart := ctx.picture;

      html := "<!doctype html><html><head><meta charset=\"utf-8\" />" +
              "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />" +
              "<title>formic-site</title>" +
              "<style>" +
              "body{font-family:Segoe UI,Arial,sans-serif;margin:2rem;background:#f9fbff;color:#0f172a;}" +
              ".card{max-width:720px;margin:auto;padding:28px;border-radius:14px;" +
              "box-shadow:0 12px 40px rgba(15,23,42,0.08);background:#fff;}" +
              ".actions a{margin-right:12px;text-decoration:none;font-weight:600;color:#2563eb;}" +
              "</style></head><body>" +
              "<div class=\"card\">" +
              "<h1>formic-site</h1>" +
              "<p>Status: " + status + "</p>" +
              "<p>User: " + ctx.name + "</p>" +
              (if emailPart == "" then "" else "<p>Email: " + emailPart + "</p>") +
              (if picPart == "" then "" else "<p>Picture: " + picPart + "</p>") +
              "<div class=\"actions\">" + signIn + logout + "</div>" +
              "</div></body></html>";
    }
  }
}
