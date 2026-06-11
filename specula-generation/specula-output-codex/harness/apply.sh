#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
SMARTBFT_DIR="${SMARTBFT_DIR:-$ROOT_DIR/SmartBFT}"

if [[ ! -d "$SMARTBFT_DIR" ]]; then
  echo "SmartBFT directory not found: $SMARTBFT_DIR" >&2
  exit 1
fi

mkdir -p "$SMARTBFT_DIR/internal/bft"
cp "$SCRIPT_DIR/src/tla_trace.go" "$SMARTBFT_DIR/internal/bft/tla_trace.go"

cd "$SMARTBFT_DIR"
if git apply --check "$SCRIPT_DIR/patches/instrumentation.patch" >/dev/null 2>&1; then
  git apply "$SCRIPT_DIR/patches/instrumentation.patch"
else
  echo "Instrumentation patch did not apply cleanly. It may already be applied." >&2
fi

if command -v gofmt >/dev/null 2>&1; then
  gofmt -w internal/bft/tla_trace.go internal/bft/controller.go internal/bft/view.go internal/bft/viewchanger.go internal/bft/state.go
fi
