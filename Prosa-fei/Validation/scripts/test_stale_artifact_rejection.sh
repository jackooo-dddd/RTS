#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
tool="$validation_root/scripts/artifact_provenance.py"
work=$(mktemp -d "${TMPDIR:-/tmp}/stale-validation-artifact.XXXXXX")
trap 'rm -rf "$work"' EXIT

cp "$validation_root/lean_fixtures/completes_at_corrected/CompletesAtCorrected.lean" "$work/Fixture.lean"
cp "$validation_root/export/CompletesAtValidation.out" "$work/Artifact.out"
cp "$validation_root/rocq/ImportedCompletesAt93.vo" "$work/Imported.vo"

record() {
  python3 "$tool" record --manifest "$work/provenance.json" \
    --source "$work/Fixture.lean" --artifact "$work/Artifact.out" \
    --imported "$work/Imported.vo" >/dev/null
}
verify_must_reject() {
  local label=$1
  if python3 "$tool" verify --manifest "$work/provenance.json" \
      --source "$work/Fixture.lean" --artifact "$work/Artifact.out" \
      --imported "$work/Imported.vo" > "$work/$label.log" 2>&1; then
    echo "$label was incorrectly accepted" >&2
    exit 1
  fi
  rg -q 'STALE_REJECTED' "$work/$label.log"
  cat "$work/$label.log"
}

record
printf '\n-- validation-only source mutation\n' >> "$work/Fixture.lean"
verify_must_reject stale_source_with_old_artifact

cp "$validation_root/lean_fixtures/completes_at_corrected/CompletesAtCorrected.lean" "$work/Fixture.lean"
record
printf '# stale-export probe\n' >> "$work/Artifact.out"
verify_must_reject changed_artifact_with_old_import

echo "stale source/artifact/import chain: REJECTED"
