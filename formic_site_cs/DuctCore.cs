using System.Security.Claims;
using System.Numerics;
using System.Linq;
using Dafny;
using DuctTools;
using DuctApis;
using Microsoft.AspNetCore.Authentication;
using Microsoft.AspNetCore.Authentication.Cookies;
using Microsoft.AspNetCore.Authentication.Google;
const string PictureClaim = "urn:google:picture";

WebApplicationBuilder builder = WebApplication.CreateBuilder(args);

// Load user secrets even when not in Development so local runs still pick up credentials.
builder.Configuration.AddUserSecrets<Program>(optional: true);

IConfigurationSection googleSection = builder.Configuration.GetSection("Authentication:Google");
builder.Services.Configure<GoogleOptions>(GoogleDefaults.AuthenticationScheme, googleSection);

builder.Services
    .AddAuthentication(options =>
    {
        options.DefaultScheme = CookieAuthenticationDefaults.AuthenticationScheme; // logged in 
        options.DefaultChallengeScheme = GoogleDefaults.AuthenticationScheme; // not logged in
    })
    .AddCookie(options =>
    {
        options.LoginPath = "/login";
        options.LogoutPath = "/logout";
        //options.Cookie.SameSite = SameSiteMode.Lax; // works with external redirects on localhost
        //options.Cookie.SecurePolicy = CookieSecurePolicy.None; // allow http during local dev
        options.Cookie.Path = "/";
        options.Cookie.Name = "formic.auth";
    })
    .AddGoogle(options =>
    {
        options.ClientId = builder.Configuration["Authentication:Google:ClientId"] ?? string.Empty;
        options.ClientSecret = builder.Configuration["Authentication:Google:ClientSecret"] ?? string.Empty;
        options.SaveTokens = true; // keep access/refresh tokens in the auth ticket
        options.CallbackPath = "/signin-google";
        options.CorrelationCookie.SameSite = SameSiteMode.Lax;
        options.CorrelationCookie.SecurePolicy = CookieSecurePolicy.None;
        options.Scope.Add("profile");
        options.Scope.Add("email");
        options.ClaimActions.MapJsonKey(ClaimTypes.GivenName, "given_name");
        options.ClaimActions.MapJsonKey(ClaimTypes.Surname, "family_name");
        options.ClaimActions.MapJsonKey(PictureClaim, "picture", "url");
    });

builder.Services.AddAuthorization();

var app = builder.Build();

app.UseHttpsRedirection();
// Inspect request, find auth cookie if present -> pipulate httpcontext.user
app.UseAuthentication();
app.UseAuthorization();

// Endpoints supplied by Dafny. The host only attaches handlers.
AllApiEndpoints catalog = Views.Endpoints();

BigInteger endpointCount = catalog.Count();
for (int i = 0; i < endpointCount; i++)
{
    ApiEndpoint ep = catalog.Get(new BigInteger(i));
    string path = FromDafnyString(ep.apiUrl);
    app.MapGet(path, (HttpContext context) =>
    {
        _IUserInfo userInfo = ToDafnyUserInfo(context.User);
        return RenderResponse(ep.generator, userInfo);
    });
}

// TODO: need to decide what 'base truth' is
app.MapGet("/logout", async (HttpContext context) =>
{
    await context.SignOutAsync(CookieAuthenticationDefaults.AuthenticationScheme);
    return Results.Redirect("/");
});

app.Run();

static DuctTools._IUserInfo ToDafnyUserInfo(ClaimsPrincipal user) =>
    DuctTools.UserInfo.create_UserInfo(
        ToDafnyString(user?.Identity?.Name ?? "Guest"),
        ToDafnyString(user?.FindFirstValue(ClaimTypes.Email) ?? string.Empty),
        ToDafnyString(user?.FindFirst(PictureClaim)?.Value ?? string.Empty),
        user?.Identity?.IsAuthenticated ?? false);

static IResult RenderResponse(IGenerator generator, DuctTools._IUserInfo user)
{
    _IReturnType payload = generator.Generate(user);

    if (payload.is_Content)
    {
        string html = FromDafnyString(payload.dtor_body);
        return Results.Content(html, "text/html");
    }

    if (payload.is_ChallengeGoogle)
    {
        AuthenticationProperties props = new AuthenticationProperties
        {
            RedirectUri = FromDafnyString(payload.dtor_returnUrl)
        };
        return Results.Challenge(props, new[] { GoogleDefaults.AuthenticationScheme });
    }

    return Results.StatusCode(StatusCodes.Status501NotImplemented);
}

static Dafny.ISequence<Dafny.Rune> ToDafnyString(string text) =>
    Dafny.Sequence<Dafny.Rune>.UnicodeFromString(text ?? string.Empty);

static string FromDafnyString(Dafny.ISequence<Dafny.Rune> seq) =>
    string.Concat(seq.Select(r => char.ConvertFromUtf32(((Dafny.Rune)r).Value)));
