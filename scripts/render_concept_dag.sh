#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

CONFIG="scripts/mermaid-puppeteer-config.json"

mmdc -p "$CONFIG" -i formal/SSBX/diagrams/ConceptDAG.core.mmd -o formal/SSBX/diagrams/ConceptDAG.core.svg
mmdc -p "$CONFIG" -i formal/SSBX/diagrams/ConceptDAG.layered.mmd -o formal/SSBX/diagrams/ConceptDAG.layered.svg
mmdc -p "$CONFIG" -i formal/SSBX/diagrams/ConceptDAG.complete.mmd -o formal/SSBX/diagrams/ConceptDAG.complete.svg
