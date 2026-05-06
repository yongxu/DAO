#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
CONFIG="scripts/mermaid-puppeteer-config.json"
mmdc -p "$CONFIG" -i formal/SSBX/diagrams/ConstructionDAG.mmd -o formal/SSBX/diagrams/ConstructionDAG.svg
