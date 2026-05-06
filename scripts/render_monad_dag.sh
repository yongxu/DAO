#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
CONFIG="scripts/mermaid-puppeteer-config.json"
mmdc -p "$CONFIG" -c scripts/mermaid-config.json -i formal/SSBX/MonadDAG.mmd -o formal/SSBX/MonadDAG.svg
