#!/usr/bin/env bash
# Searches GitHub code for OPL models and writes <dir>/hits.tsv (repository, path, blob sha).
# usage: scripts/corpus/search.sh corpus      (needs `gh auth login`)
set -euo pipefail
dir=${1:-corpus}
mkdir -p "$dir/files"
q() { gh api -X GET search/code -f q="$1" -f per_page=100 --jq '.items[] | [.repository.full_name, .path, .sha] | @tsv' || true; sleep 7; }
{
  q '"subject to" "var int" extension:mod'
  q '"subject to" "var float" extension:mod'
  q '"solve {" "var" extension:mod'
  q 'tryall extension:mod'
  q 'UnaryResource extension:mod'
  q 'dvar "subject to" extension:mod'
  q '"using CP" dvar extension:mod'
  q 'dvar constraints extension:mod'
  q 'dvar execute extension:mod'
} | sort -u > "$dir/hits.tsv"
wc -l < "$dir/hits.tsv"
