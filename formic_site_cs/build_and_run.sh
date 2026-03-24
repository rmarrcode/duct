#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DAFNY_DIR="$SCRIPT_DIR/../formic_site_duct"
OUT_DIR="$DAFNY_DIR/converted_duct"

PORT="${PORT:-5002}"
URL="${URL:-http://localhost:${PORT}}"
NUGET_PACKAGES="${NUGET_PACKAGES:-/tmp/nuget}"

echo "[1/3] Generating Dafny -> C# into $OUT_DIR"
(cd "$DAFNY_DIR" && bash ./build_formic.sh)

echo "[2/3] Building .NET project"
cd "$SCRIPT_DIR"
NUGET_PACKAGES="$NUGET_PACKAGES" dotnet build

echo "[3/3] Running at $URL"
NUGET_PACKAGES="$NUGET_PACKAGES" dotnet run --urls "$URL"
