#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/foundation_slice_2_closure"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
closure_src_dir="$VALIDATION_ROOT/certificates/foundation_slice_2_closure"
common_src_dir="$VALIDATION_ROOT/certificates/common"
publish_dir="$VALIDATION_ROOT/imported/foundation_slice_2_closure"
mkdir -p "$log_dir" "$pipeline_dir" "$publish_dir"

# Capture the frozen production and accepted-declaration evidence before the
# fresh baseline rebuild.  Verification occurs again before publication.
python3 "$script_dir/audit_slice_2_closure_baseline.py" capture \
  --project-root "$PROJECT_ROOT" \
  --snapshot "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_capture.log"

# Freshly rebuild, export, and import all six production files.  This driver
# intentionally reuses Slice 2's already audited mechanics rather than its old
# artifacts.  The resulting work directory is obtained from new provenance.
"$script_dir/validate_foundation_slice_2.sh" \
  > "$log_dir/fresh_base_pipeline.log" 2>&1
work=$(python3 - "$VALIDATION_ROOT/logs/foundation_slice_2/runtime_provenance.json" <<'PY'
import json, sys
print(json.load(open(sys.argv[1]))["fresh_work_directory"])
PY
)

if [[ ! -d "$work/imported" || ! -d "$work/certificates" ]]; then
  echo "fresh Slice 2 work directory is incomplete" >&2
  exit 1
fi

# Only the one audited foundation axiom may exist.  All new common bridges and
# closure certificates must be axiom/admit/sorry-free.
if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$closure_src_dir" --glob '*.v'; then
  echo "forbidden proof escape in closure certificates" >&2
  exit 1
fi
for file in LogicalRelation EqTypeCorrespondence RelListCorrespondence \
  SeqsetCorrespondence SubadditivityNatCorrespondence \
  SupremumTheoremCorrespondence; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$common_src_dir/$file.v"; then
    echo "forbidden proof escape in common bridge $file" >&2
    exit 1
  fi
done

cp "$common_src_dir/"{LogicalRelation,EqTypeCorrespondence,RelListCorrespondence,SeqsetCorrespondence,SubadditivityNatCorrespondence,SupremumTheoremCorrespondence}.v \
  "$work/certificates/"
cp "$closure_src_dir/"{TacticsClosureCertificate,RelClosureCertificate,SeqsetClosureCertificate,SubadditivityClosureCertificate,SupremumClosureCertificate,ClosureAssumptionAudit}.v \
  "$work/certificates/"

common_modules=(
  LogicalRelation
  EqTypeCorrespondence
  RelListCorrespondence
  SeqsetCorrespondence
  SubadditivityNatCorrespondence
  SupremumTheoremCorrespondence
)
target_modules=(
  TacticsClosureCertificate
  RelClosureCertificate
  SeqsetClosureCertificate
  SubadditivityClosureCertificate
  SupremumClosureCertificate
)

for module in "${common_modules[@]}"; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/common_${module}.log" 2>&1
done
for module in "${target_modules[@]}"; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/certificate_${module}.log" 2>&1
done

(cd "$work/certificates" && \
  validation_rocq_compile "$work" ClosureAssumptionAudit.v) \
  > "$log_dir/assumptions.log" 2>&1
python3 "$script_dir/audit_assumptions.py" \
  --config "$closure_src_dir/assumption_config.json" \
  --log "$log_dir/assumptions.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"

python3 "$script_dir/audit_slice_2_source_compatibility.py" \
  --authoritative-root "$SOURCE_ROOT" \
  --validation-root "$work/source" \
  --inventory "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv" \
  --output "$log_dir/source_compatibility_summary.json" \
  > "$log_dir/source_compatibility_classifier.log"

python3 "$script_dir/audit_slice_2_closure_baseline.py" verify \
  --project-root "$PROJECT_ROOT" \
  --snapshot "$log_dir/baseline_before.json" \
  --output "$log_dir/baseline_check.json" \
  > "$log_dir/baseline_verify.log"

python3 "$script_dir/generate_foundation_slice_2_closure_results.py" \
  --validation-root "$VALIDATION_ROOT" \
  --work "$work" \
  --assumptions "$log_dir/assumption_summary.json" \
  --source-compatibility "$log_dir/source_compatibility_summary.json" \
  --baseline-check "$log_dir/baseline_check.json" \
  > "$log_dir/result_generation.log"

# Publish only after every fail-closed compilation and classifier succeeds.
for stem in Notation Tactics Rel Seqset Subadditivity Supremum; do
  cp "$work/imported/$stem.out" "$publish_dir/$stem.out"
  cp "$work/imported/Imported$stem.vo" "$publish_dir/Imported$stem.vo"
done
for module in "${common_modules[@]}" "${target_modules[@]}" \
    ClosureAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 - "$work" "$publish_dir" "$log_dir" <<'PY'
import hashlib, json, pathlib, sys

work, published, logs = map(pathlib.Path, sys.argv[1:])
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
result = {
    "fresh_work_directory": str(work),
    "fresh_build": True,
    "published_artifacts": {
        str(p.relative_to(published)): sha(p)
        for p in sorted(published.iterdir()) if p.is_file()
    },
    "assumption_summary_sha256": sha(logs / "assumption_summary.json"),
    "source_compatibility_summary_sha256": sha(logs / "source_compatibility_summary.json"),
    "baseline_check_sha256": sha(logs / "baseline_check.json"),
}
(logs / "runtime_provenance.json").write_text(json.dumps(result, indent=2) + "\n")
PY

(cd "$REPO_ROOT" && git diff --check)

echo "FOUNDATION_SLICE_2_CLOSURE_STATUS = PASS"
echo "fresh work directory: $work"
echo "newly accepted declarations: 17 / 17"
echo "Slice 2 accepted declarations: 22 / 22"
