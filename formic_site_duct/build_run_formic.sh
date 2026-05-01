#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="$SCRIPT_DIR/converted_duct"
SRC_DB="$SCRIPT_DIR/db.dfy"
SRC_DUCT="$SCRIPT_DIR/duct.dfy"
SRC_SPECS="$SCRIPT_DIR/formic.specs.duct.dfy"
SRC_APIS="$SCRIPT_DIR/formic.apis.duct.dfy"
mapfile -t IMPLEMENTATIONS < <(find "$SCRIPT_DIR/implementations" -maxdepth 1 -name '*.program.dfy' | sort)

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
start_port="${PORT:-5000}"
find_free_port() {
  local p="$1"
  while ss -tln 2>/dev/null | grep -q ":${p} " ; do
    p=$((p+1))
  done
  echo "$p"
}
port_to_use="$(find_free_port "$start_port")"
if [[ "$port_to_use" != "$start_port" ]]; then
  echo "Port $start_port is busy; using $port_to_use instead."
fi
ASPNETCORE_URLS="http://127.0.0.1:${port_to_use}"
echo "Starting web app on ${ASPNETCORE_URLS} (Ctrl+C to stop)..."
NUGET_PACKAGES="${NUGET_PACKAGES:-/tmp/nuget}" ASPNETCORE_URLS="$ASPNETCORE_URLS" dotnet run --urls "$ASPNETCORE_URLS"
popd >/dev/null
