#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
OUT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
ROOT_DIR="$(cd "$OUT_DIR/.." && pwd)"
SMARTBFT_DIR="${SMARTBFT_DIR:-$ROOT_DIR/SmartBFT}"
TRACE_DIR="${TRACE_DIR:-$OUT_DIR/traces}"
GO_CACHE_DIR="${GO_CACHE_DIR:-$OUT_DIR/go-cache}"
GO_MOD_CACHE_DIR="${GO_MOD_CACHE_DIR:-$OUT_DIR/go-mod-cache}"

mkdir -p "$TRACE_DIR"
mkdir -p "$GO_CACHE_DIR" "$GO_MOD_CACHE_DIR"

bash "$SCRIPT_DIR/apply.sh"

if ! command -v go >/dev/null 2>&1; then
  echo "go is not available on PATH; instrumentation applied but tests cannot run." >&2
  exit 127
fi

cd "$SMARTBFT_DIR"

run_with_timeout() {
  local seconds="$1"
  shift
  "$@" &
  local pid=$!
  (
    sleep "$seconds"
    if kill -0 "$pid" 2>/dev/null; then
      echo "command timed out after ${seconds}s: $*" >&2
      kill "$pid" 2>/dev/null || true
    fi
  ) &
  local watchdog=$!
  local status=0
  wait "$pid" || status=$?
  kill "$watchdog" 2>/dev/null || true
  wait "$watchdog" 2>/dev/null || true
  return "$status"
}

run_scenario() {
  local name="$1"
  local pattern="$2"
  local pkg="$3"
  local trace_file="$TRACE_DIR/${name}.ndjson"
  rm -f "$trace_file"
  echo "==> scenario: $name"
  SMARTBFT_TLA_TRACE=1 SMARTBFT_TLA_TRACE_FILE="$trace_file" TRACE_DIR="$TRACE_DIR" \
    GOCACHE="$GO_CACHE_DIR" GOMODCACHE="$GO_MOD_CACHE_DIR" \
    run_with_timeout 300 go test -run "$pattern" -count=1 -timeout 300s "$pkg"
  if [[ -f "$trace_file" ]]; then
    local lines
    lines="$(wc -l < "$trace_file" | tr -d ' ')"
    echo "trace: $trace_file ($lines lines)"
  else
    echo "trace missing: $trace_file" >&2
  fi
}

run_scenario normal_basic 'TestBasic|TestBasicView|TestBasicConsensus' './test'
run_scenario reconfig 'TestReconfig' './test'
run_scenario controller_unit 'TestController' './internal/bft'
run_scenario viewchange_unit 'TestViewChanger' './internal/bft'

echo "==> generated traces"
ls -la "$TRACE_DIR"/*.ndjson 2>/dev/null || true
