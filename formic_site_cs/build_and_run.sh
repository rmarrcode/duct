#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DAFNY_DIR="$SCRIPT_DIR/../formic_site_duct"
OUT_DIR="$DAFNY_DIR/converted_duct"
SRC_DB="$DAFNY_DIR/db.dfy"
SRC_DUCT="$DAFNY_DIR/duct.dfy"
SRC_SPECS="$DAFNY_DIR/formic.specs.duct.dfy"
SRC_APIS="$DAFNY_DIR/formic.apis.duct.dfy"
mapfile -t IMPLEMENTATIONS < <(find "$DAFNY_DIR/implementations" -maxdepth 1 -name '*.program.dfy' | sort)

PORT="${PORT:-5002}"
URL="${URL:-http://localhost:${PORT}}"

echo "[1/3] Generating Dafny -> C# into $OUT_DIR"
mkdir -p "$OUT_DIR"
"${DAFNY:-dafny}" translate cs "$SRC_DB" "$SRC_DUCT" "$SRC_SPECS" "${IMPLEMENTATIONS[@]}" "$SRC_APIS" \
  --no-verify \
  --allow-warnings \
  --include-runtime \
  --output "$OUT_DIR/formic_duct"

echo "[2/3] Building .NET project"
cd "$SCRIPT_DIR"
dotnet build

echo "[3/3] Running at $URL"
dotnet run --urls "$URL"
