#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  scripts/link_lake_packages.sh [source-worktree]

Link this worktree's .lake/packages to an existing worktree that already has
the Lake dependency packages, avoiding a fresh mathlib clone in new worktrees.

If source-worktree is omitted, the script scans sibling git worktrees and uses
the first one with .lake/packages/mathlib.
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

repo_root="$(git rev-parse --show-toplevel)"
current="$(cd "$repo_root" && pwd -P)"
source_worktree="${1:-}"

if [[ -z "$source_worktree" ]]; then
  while IFS= read -r line; do
    case "$line" in
      worktree\ *)
        candidate="${line#worktree }"
        candidate_real="$(cd "$candidate" 2>/dev/null && pwd -P || true)"
        if [[ "$candidate_real" != "$current" && -d "$candidate/.lake/packages/mathlib/.git" ]]; then
          source_worktree="$candidate"
          break
        fi
        ;;
    esac
  done < <(git worktree list --porcelain)
fi

if [[ -z "$source_worktree" ]]; then
  echo "error: no source worktree with .lake/packages/mathlib found" >&2
  echo "hint: pass one explicitly, e.g. scripts/link_lake_packages.sh /path/to/main/worktree" >&2
  exit 1
fi

source_packages="$source_worktree/.lake/packages"
if [[ ! -d "$source_packages/mathlib/.git" ]]; then
  echo "error: source does not contain .lake/packages/mathlib: $source_worktree" >&2
  exit 1
fi

mkdir -p "$repo_root/.lake"

if [[ -e "$repo_root/.lake/packages" || -L "$repo_root/.lake/packages" ]]; then
  existing="$(readlink "$repo_root/.lake/packages" 2>/dev/null || true)"
  if [[ "$existing" == "$source_packages" ]]; then
    echo ".lake/packages already linked to $source_packages"
    exit 0
  fi
  echo "error: $repo_root/.lake/packages already exists" >&2
  echo "hint: remove it manually only if it is a disposable dependency checkout" >&2
  exit 1
fi

ln -s "$source_packages" "$repo_root/.lake/packages"
echo "linked .lake/packages -> $source_packages"
