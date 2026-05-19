#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="$SCRIPT_DIR/converted_duct"
SRC_DB="$SCRIPT_DIR/db.dfy"
SRC_DUCT="$SCRIPT_DIR/duct.dfy"
SRC_SPECS="$SCRIPT_DIR/formic.specs.duct.dfy"
SRC_APIS="$SCRIPT_DIR/formic.apis.duct.dfy"
mapfile -t IMPLEMENTATIONS < <(find "$SCRIPT_DIR/implementations" -maxdepth 1 -name '*.program.dfy' | sort)
start_port="${PORT:-5000}"
host="${HOST:-localhost}"
allow_port_fallback="${ALLOW_PORT_FALLBACK:-0}"

port_is_busy() {
  local p="$1"
  ss -H -tln 2>/dev/null | grep -q ":${p} "
}

show_port_owner() {
  local p="$1"
  if command -v lsof >/dev/null 2>&1; then
    lsof -nP -iTCP:"$p" -sTCP:LISTEN 2>/dev/null || true
  else
    ss -ltnp "( sport = :$p )" || true
  fi
}

find_free_port() {
  local p="$1"
  while port_is_busy "$p"; do
    p=$((p+1))
  done
  echo "$p"
}

if port_is_busy "$start_port"; then
  echo "Port $start_port is busy:"
  show_port_owner "$start_port"

  if [[ "$allow_port_fallback" == "1" ]]; then
    port_to_use="$(find_free_port "$start_port")"
    echo "Using $port_to_use instead because ALLOW_PORT_FALLBACK=1."
  else
    echo
    echo "Refusing to fall back because Google OAuth redirect URIs are port-specific."
    echo "Free port $start_port, set PORT to a configured OAuth port, or run with ALLOW_PORT_FALLBACK=1."
    exit 1
  fi
else
  port_to_use="$start_port"
fi

mkdir -p "$OUT_DIR"

echo "Generating C# from Dafny sources into $OUT_DIR ..."
"${DAFNY:-dafny}" translate cs "$SRC_DB" "$SRC_DUCT" "$SRC_SPECS" "${IMPLEMENTATIONS[@]}" "$SRC_APIS" \
  --no-verify \
  --allow-warnings \
  --include-runtime \
  --output "$OUT_DIR/formic_duct"

echo "Done. Generated files:"
ls -1 "$OUT_DIR"

echo "Building and running ASP.NET app..."
pushd "$SCRIPT_DIR/../formic_site_cs" >/dev/null
NUGET_PACKAGES="${NUGET_PACKAGES:-/tmp/nuget}" dotnet build
ASPNETCORE_URLS="http://${host}:${port_to_use}"
echo "Starting web app on ${ASPNETCORE_URLS} (Ctrl+C to stop)..."
echo "Google OAuth redirect URI: ${ASPNETCORE_URLS}/signin-google"
NUGET_PACKAGES="${NUGET_PACKAGES:-/tmp/nuget}" ASPNETCORE_URLS="$ASPNETCORE_URLS" dotnet run --urls "$ASPNETCORE_URLS"
popd >/dev/null
