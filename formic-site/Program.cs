using System.Net;
using System.Security.Claims;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Collections.Generic;
using Microsoft.AspNetCore.Authentication;
using Microsoft.AspNetCore.Authentication.Cookies;
using Microsoft.AspNetCore.Authentication.Google;

const string PictureClaim = "urn:google:picture";

var builder = WebApplication.CreateBuilder(args);

// Load user secrets even when not in Development so local runs still pick up credentials.
builder.Configuration.AddUserSecrets<Program>(optional: true);

var googleSection = builder.Configuration.GetSection("Authentication:Google");
builder.Services.Configure<GoogleOptions>(GoogleDefaults.AuthenticationScheme, googleSection);

builder.Services
    .AddAuthentication(options =>
    {
        options.DefaultScheme = CookieAuthenticationDefaults.AuthenticationScheme;
        options.DefaultChallengeScheme = GoogleDefaults.AuthenticationScheme;
    })
    .AddCookie(options =>
    {
        options.LoginPath = "/login";
        options.LogoutPath = "/logout";
        options.Cookie.SameSite = SameSiteMode.Lax; // works with external redirects on localhost
        options.Cookie.SecurePolicy = CookieSecurePolicy.None; // allow http during local dev
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

var settingsFilePath = Path.Combine(builder.Environment.ContentRootPath, "appsettings.json");
var templatesRoot = Path.Combine(builder.Environment.ContentRootPath, "Templates");
var homeTemplate = LoadTemplate(templatesRoot, "home.html");
var settingsTemplate = LoadTemplate(templatesRoot, "settings.html");

app.UseHttpsRedirection();
app.UseAuthentication();
app.UseAuthorization();

app.MapGet("/", (HttpContext context, IConfiguration config) =>
{
    var user = context.User;
    var authenticated = user?.Identity?.IsAuthenticated ?? false;
    var name = WebUtility.HtmlEncode(user?.Identity?.Name ?? "Guest");
    var email = WebUtility.HtmlEncode(user?.FindFirstValue(ClaimTypes.Email));
    var picture = user?.FindFirst(PictureClaim)?.Value;
    var pictureHtml = picture is not null
        ? $"<img class=\"avatar\" src=\"{picture}\" alt=\"avatar\" />"
        : string.Empty;
    var clientId = config["Authentication:Google:ClientId"];
    var clientIdLabelRaw = string.IsNullOrWhiteSpace(clientId)
        ? "Not set"
        : clientId.Length > 8
            ? $"{clientId[..4]}…{clientId[^4..]}"
            : clientId;
    var clientIdLabel = WebUtility.HtmlEncode(clientIdLabelRaw);

    var loginBlock = authenticated
        ? "<p class=\"chip success\">Signed in with Google</p><p><a class=\"button secondary\" href=\"/logout\">Log out</a></p>"
        : "<p class=\"chip neutral\">Anonymous</p><p><a class=\"button\" href=\"/login\">Continue with Google</a></p>";

    var emailRow = email is not null ? $"<div><strong>Email:</strong> {email}</div>" : string.Empty;

    var html = RenderTemplate(homeTemplate, new Dictionary<string, string>
    {
        ["PICTURE_HTML"] = pictureHtml,
        ["STATUS"] = authenticated ? "Signed in" : "Anonymous",
        ["USER"] = name,
        ["EMAIL_ROW"] = emailRow,
        ["LOGIN_BLOCK"] = loginBlock,
        ["CLIENT_ID_LABEL"] = clientIdLabel
    });

    return Results.Content(html, "text/html");
});

app.MapGet("/settings", (IConfiguration config, string? saved) =>
{
    var settings = ReadGoogleSettings(config);
    var savedBanner = saved == "1" ? "<p class=\"chip success\">Saved. Reload the home page and sign in again if you changed credentials.</p>" : string.Empty;

    var html = RenderTemplate(settingsTemplate, new Dictionary<string, string>
    {
        ["SAVED_BANNER"] = savedBanner,
        ["CLIENT_ID_VALUE"] = WebUtility.HtmlEncode(settings.ClientId)
    });

    return Results.Content(html, "text/html");
});

app.MapPost("/settings", async (HttpContext context, IConfiguration config) =>
{
    var form = await context.Request.ReadFormAsync();
    var existing = ReadGoogleSettings(config);

    var clientId = form["clientId"].ToString().Trim();
    var clientSecret = form["clientSecret"].ToString().Trim();

    var updated = new GoogleAuthSettings(
        string.IsNullOrWhiteSpace(clientId) ? existing.ClientId : clientId,
        string.IsNullOrWhiteSpace(clientSecret) ? existing.ClientSecret : clientSecret);

    await PersistGoogleSettingsAsync(settingsFilePath, updated);

    return Results.Redirect("/settings?saved=1");
});

app.MapGet("/login", (string? returnUrl) =>
{
    var props = new AuthenticationProperties { RedirectUri = returnUrl ?? "/" };
    return Results.Challenge(props, new[] { GoogleDefaults.AuthenticationScheme });
});

app.MapGet("/logout", async (HttpContext context) =>
{
    await context.SignOutAsync(CookieAuthenticationDefaults.AuthenticationScheme);
    return Results.Redirect("/");
});

app.MapGet("/secure", (ClaimsPrincipal user) =>
{
    var name = user.Identity?.Name ?? "unknown";
    return Results.Json(new { message = $"Hello, {name}!", issued = DateTimeOffset.UtcNow });
}).RequireAuthorization();

app.Run();

static GoogleAuthSettings ReadGoogleSettings(IConfiguration config) => new(
    config["Authentication:Google:ClientId"] ?? string.Empty,
    config["Authentication:Google:ClientSecret"] ?? string.Empty);

static async Task PersistGoogleSettingsAsync(string path, GoogleAuthSettings settings)
{
    JsonObject root;
    if (File.Exists(path))
    {
        var json = await File.ReadAllTextAsync(path);
        root = JsonNode.Parse(json)?.AsObject() ?? new JsonObject();
    }
    else
    {
        root = new JsonObject();
    }

    var auth = root["Authentication"] as JsonObject ?? new JsonObject();
    root["Authentication"] = auth;

    var google = auth["Google"] as JsonObject ?? new JsonObject();
    auth["Google"] = google;

    google["ClientId"] = settings.ClientId;
    google["ClientSecret"] = settings.ClientSecret;

    var options = new JsonSerializerOptions { WriteIndented = true };
    await File.WriteAllTextAsync(path, root.ToJsonString(options));
}

static string RenderTemplate(string template, IReadOnlyDictionary<string, string> values)
{
    var result = template;
    foreach (var kvp in values)
    {
        result = result.Replace($"{{{{{kvp.Key}}}}}", kvp.Value ?? string.Empty);
    }
    return result;
}

static string LoadTemplate(string root, string fileName)
{
    var path = Path.Combine(root, fileName);
    if (!File.Exists(path))
    {
        return $"Template '{fileName}' not found at {path}.";
    }
    return File.ReadAllText(path);
}

record GoogleAuthSettings(string ClientId, string ClientSecret);
