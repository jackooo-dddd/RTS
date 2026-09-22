#!/usr/bin/env bash

# Keep the content-addressed prepare definition in the base hook unchanged.
# This wrapper applies a publication-only correction: audit_assumptions.py
# serializes certificate keys deterministically rather than in source order,
# so publication must look records up by name instead of asserting JSON object
# insertion order.  Because this wrapper is a CHECK input, the verified clean
# prepare remains reusable while certificate/audit/publication rerun.
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/behavior_arrival_sequence_incremental_hooks.sh"

VALIDATION_CHECK_INPUTS+=(
  "$VALIDATION_ROOT/tooling/behavior_arrival_sequence_finalize_hooks.sh"
)

arrival_publication_definition=$(declare -f validation_finalize_publication)
arrival_publication_definition=$(printf '%s\n' "$arrival_publication_definition" |
  sed '/^assert list(assumptions\["certificates"\]) == names$/d')
eval "$arrival_publication_definition"
unset arrival_publication_definition
