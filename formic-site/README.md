# formic-site — Google sign-in sample with editable config

A minimal ASP.NET Core 8 app that lets users sign in with Google, now branded as **formic-site** with a built-in page to edit the OAuth client ID/secret at runtime (saved to `appsettings.json`).

## Prerequisites
- .NET 8 SDK (LTS). Download from https://dotnet.microsoft.com/download/dotnet/8.0
- A Google Cloud project with OAuth 2.0 Client ID (type **Web application**).

## Configure Google OAuth
1. Open Google Cloud Console → **APIs & Services** → **Credentials** → **Create credentials** → **OAuth client ID** → choose **Web application**.
2. Add Authorized redirect URIs:
   - https://localhost:5001/signin-google
   - http://localhost:5000/signin-google (optional http fallback)
3. Copy the **Client ID** and **Client secret**.

## Set credentials locally
Option A — use user secrets or env vars (preferred so secrets stay out of git):

```bash
# from the project folder
dotnet user-secrets init
dotnet user-secrets set "Authentication:Google:ClientId" "<client-id>"
dotnet user-secrets set "Authentication:Google:ClientSecret" "<client-secret>"
```

Alternatively, export environment variables before running:

```bash
export Authentication__Google__ClientId=<client-id>
export Authentication__Google__ClientSecret=<client-secret>
```

Option B — use the in-app editor: run the app then open `https://localhost:5001/settings` (or `http://localhost:5000/settings`) and fill in the Client ID/Secret. Leaving the secret blank keeps the previous value. Changes persist to `appsettings.json` and the Google options reload automatically.

## Run the app
```bash
cd formic-site
dotnet restore
dotnet dev-certs https --trust   # once, to trust the dev certificate
dotnet run
```
Visit https://localhost:5001 to try it. `/secure` is protected and will challenge unauthenticated users.

## How it works
- Cookie authentication stores the signed-in session.
- `AddGoogle` handles the OAuth flow and reads `Authentication:Google:ClientId/ClientSecret` from configuration.
- The default Google callback path is `/signin-google`, which must match your OAuth redirect URIs.
- `/settings` lets you edit the Google Client ID/Secret; updates write to `appsettings.json` and trigger configuration reload.

## Project layout
- `Program.cs` — top-level minimal API with login/logout endpoints and a simple HTML UI.
- `appsettings.json` — placeholder config for Google ClientId/ClientSecret (do not commit real secrets).
- `FormicSite.csproj` — targets `net8.0` and references `Microsoft.AspNetCore.Authentication.Google`.
