#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
rocq_dir="$validation_root/rocq"
log_dir="$validation_root/reports/logs/experiment7"
switch_name=${IMPORT_OPAM_SWITCH:-rocq93rc1}
importer_src=${ROCQLI_SRC:-/private/tmp/rocq-lean-import-93}
prosa_src=${PROSA_ROCQ_SRC:-/Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6}

mkdir -p "$log_dir"
"$validation_root/scripts/export_interval_mutation_fixture.sh" \
  > "$log_dir/interval_mutation_export_run.log" 2>&1

compile() {
  local file=$1 log=$2
  opam exec --switch="$switch_name" -- rocq c \
    -R "$prosa_src" prosa \
    -Q "$importer_src/src" LeanImport -I "$importer_src/src" \
    "$file" > "$log_dir/$log" 2>&1
}

cd "$rocq_dir"
ulimit -s 65520
compile ImportedIntervalMutation93.v interval_mutation_import.log
compile IntervalMutationCertificate.v interval_mutation_certificate.log

rg -q 'MUTATION_AUDIT mutation_detected' \
  "$log_dir/interval_mutation_certificate.log"
rg -q 'MUTATION_AUDIT positive_control' \
  "$log_dir/interval_mutation_certificate.log"

echo "interval endpoint semantic mutation: PASS (actual Icc artifact differs at m=n=0, F 0=1)"
echo "semantics-preserving helper refactor: PASS (general equality kernel-checked)"
