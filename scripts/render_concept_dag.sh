#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

CONFIG="scripts/mermaid-puppeteer-config.json"

mmdc -p "$CONFIG" -i formal/SSBX/ConceptDAG.core.mmd -o formal/SSBX/ConceptDAG.core.svg
mmdc -p "$CONFIG" -i formal/SSBX/ConceptDAG.layered.mmd -o formal/SSBX/ConceptDAG.layered.svg
mmdc -p "$CONFIG" -i formal/SSBX/ConceptDAG.complete.mmd -o formal/SSBX/ConceptDAG.complete.svg
