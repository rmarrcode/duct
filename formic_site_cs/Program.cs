using System.Net;
using System.Security.Claims;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Collections.Generic;
using System.Threading;
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
        options.DefaultScheme = CookieAuthenticationDefaults.AuthenticationScheme; // logged in 
        options.DefaultChallengeScheme = GoogleDefaults.AuthenticationScheme; // not logged in
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
var profileTemplate = LoadTemplate(templatesRoot, "profile.html");
var profileStore = new ProfileStore(Path.Combine(builder.Environment.ContentRootPath, "profiles.json"));

app.UseHttpsRedirection();
app.UseAuthentication();
app.UseAuthorization();

app.MapGet("/", async (HttpContext context, IConfiguration config) =>
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

    var about = email is not null ? await profileStore.GetAsync(WebUtility.HtmlDecode(email)) : null;
    var aboutCard = authenticated
        ? $@"<div class=""card"">
      <h3>Your note</h3>
      <p>{(string.IsNullOrWhiteSpace(about) ? "Add something on your <a href=\"/profile\">profile page</a>." : Htmlize(about))}</p>
      <p><a class=""pill-link"" href=""/profile"">Edit profile note →</a></p>
    </div>"
        : @"<div class=""card"">
      <h3>Your note</h3>
      <p>Sign in to add a short note to your profile.</p>
      <p><a class=""pill-link"" href=""/login"">Sign in →</a></p>
    </div>";

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
        ["CLIENT_ID_LABEL"] = clientIdLabel,
        ["ABOUT_CARD"] = aboutCard
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

app.MapGet("/profile", async (ClaimsPrincipal user, string? saved) =>
{
    var email = user.FindFirstValue(ClaimTypes.Email);
    var about = email is not null ? await profileStore.GetAsync(email) : string.Empty;
    var savedBanner = saved == "1" ? "<p class=\"chip success\">Saved.</p>" : string.Empty;

    var html = RenderTemplate(profileTemplate, new Dictionary<string, string>
    {
        ["SAVED_BANNER"] = savedBanner,
        ["ABOUT_VALUE"] = WebUtility.HtmlEncode(about ?? string.Empty)
    });

    return Results.Content(html, "text/html");
}).RequireAuthorization();

app.MapPost("/profile", async (ClaimsPrincipal user, HttpContext context) =>
{
    var email = user.FindFirstValue(ClaimTypes.Email);
    if (email is null) return Results.Challenge();

    var form = await context.Request.ReadFormAsync();
    var about = form["about"].ToString();
    await profileStore.SetAsync(email, about);

    return Results.Redirect("/profile?saved=1");
}).RequireAuthorization();

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

static string Htmlize(string? text)
{
    var encoded = WebUtility.HtmlEncode(text ?? string.Empty);
    return encoded.Replace("\n", "<br />");
}

record GoogleAuthSettings(string ClientId, string ClientSecret);

class ProfileStore
{
    private readonly string _path;
    private readonly SemaphoreSlim _lock = new(1, 1);

    public ProfileStore(string path) => _path = path;

    public async Task<string?> GetAsync(string email)
    {
        if (string.IsNullOrWhiteSpace(email)) return null;
        var data = await LoadAsync();
        return data.TryGetValue(email, out var about) ? about : null;
    }

    public async Task SetAsync(string email, string about)
    {
        if (string.IsNullOrWhiteSpace(email)) return;
        await _lock.WaitAsync();
        try
        {
            var data = await LoadUnsafeAsync();
            data[email] = about ?? string.Empty;
            var json = JsonSerializer.Serialize(data, new JsonSerializerOptions { WriteIndented = true });
            await File.WriteAllTextAsync(_path, json);
        }
        finally
        {
            _lock.Release();
        }
    }

    private async Task<Dictionary<string, string>> LoadAsync()
    {
        await _lock.WaitAsync();
        try
        {
            return await LoadUnsafeAsync();
        }
        finally
        {
            _lock.Release();
        }
    }

    private async Task<Dictionary<string, string>> LoadUnsafeAsync()
    {
        if (!File.Exists(_path))
            return new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);

        var json = await File.ReadAllTextAsync(_path);
        var data = JsonSerializer.Deserialize<Dictionary<string, string>>(json, new JsonSerializerOptions
        {
            PropertyNameCaseInsensitive = true
        });

        return data ?? new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
    }
}
