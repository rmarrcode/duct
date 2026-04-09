#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DAFNY_DIR="$SCRIPT_DIR/../formic_site_duct"
OUT_DIR="$DAFNY_DIR/converted_duct"
SRC1="$DAFNY_DIR/duct.dfy"
SRC2="$DAFNY_DIR/formic.impl.duct.dfy"
SRC3="$DAFNY_DIR/formic.apis.duct.dfy"

PORT="${PORT:-5002}"
URL="${URL:-http://localhost:${PORT}}"

echo "[1/3] Generating Dafny -> C# into $OUT_DIR"
mkdir -p "$OUT_DIR"
"${DAFNY:-dafny}" translate cs "$SRC2" "$SRC3" "$SRC1" \
  --no-verify \
  --allow-warnings \
  --include-runtime \
  --output "$OUT_DIR/formic_duct"

echo "[2/3] Building .NET project"
cd "$SCRIPT_DIR"
dotnet build

echo "[3/3] Running at $URL"
dotnet run --urls "$URL"
