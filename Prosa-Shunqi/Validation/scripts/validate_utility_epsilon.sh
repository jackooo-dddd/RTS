#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/translation_order/epsilon"
publish_dir="$VALIDATION_ROOT/imported/translation_order/epsilon"
fixture_dir="$VALIDATION_ROOT/fixtures/utility_foundation"
cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
common_dir="$VALIDATION_ROOT/certificates/common"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
mkdir -p "$log_dir" "$publish_dir"

[[ $(validation_sha256 "$SOURCE_ROOT/util/epsilon.v") == \
  66f666ac1c6a290f006024a99ef48e0fa2bfa010d52dcb4dc387fef4bc0c533e ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/epsilon.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 0 ]]
if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Epsilon.lean"; then
  echo "forbidden production proof escape" >&2; exit 1
fi
for path in "$cert_dir/EpsilonCertificate.v" \
  "$cert_dir/EpsilonAssumptionAudit.v"; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
    echo "forbidden certificate proof escape" >&2; exit 1
  fi
done

work=$(validation_fresh_workdir utility_epsilon)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/utility_foundation" \
  "$work/source/util" "$work/imported" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

validation_compile_lean_module "$work" Prosa/Util/Epsilon \
  > "$log_dir/fresh_Epsilon.log" 2>&1
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/utility_foundation/EpsilonInterface.olean" \
  "$fixture_dir/EpsilonInterface.lean" > "$log_dir/fresh_interface.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/EpsilonInterface.lean" \
  > "$log_dir/lean_interface_audit.log" 2>&1

export LEAN4EXPORT_STATEMENT_ONLY=
export LEAN4EXPORT_BODY_THEOREMS=
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  Validation.fixtures.utility_foundation.EpsilonInterface -- \
  Prosa.Validation.EpsilonInterface.epsilonNatValue \
  > "$work/imported/Epsilon.out" 2> "$log_dir/export.log"
[[ -s "$work/imported/Epsilon.out" ]]

cp "$SOURCE_ROOT/util/epsilon.v" "$work/source/util/epsilon.v"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa util/epsilon.v) \
  > "$log_dir/source_compile.log" 2>&1
cp "$fixture_dir/EpsilonSourceInterface.v" "$work/source/"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa EpsilonSourceInterface.v) \
  > "$log_dir/source_interface_compile.log" 2>&1

cp "$fixture_dir/ImportedEpsilon.v" "$work/imported/"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
  99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
(cd "$work/imported" && validation_rocq_compile "$work" ImportedEpsilon.v) \
  > "$log_dir/import.log" 2>&1

cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
  "$work/certificates/"
cp "$cert_dir/"{EpsilonCertificate,EpsilonAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  EpsilonCertificate EpsilonAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_EpsilonAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$cert_dir/epsilon_assumption_config.json" \
  --log "$log_dir/assumptions.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"
jq -e '.certificates.epsilon_notation_value.status == "CERTIFIED" and
  (.certificates.epsilon_notation_value.semantic_premises | length == 0) and
  (.certificates.epsilon_notation_value.unexpected | length == 0)' \
  "$log_dir/assumption_summary.json" >/dev/null

cp "$work/imported/"{Epsilon.out,ImportedEpsilon.v,ImportedEpsilon.vo} \
  "$publish_dir/"
cp "$work/certificates/"{EpsilonCertificate.vo,EpsilonAssumptionAudit.vo} \
  "$publish_dir/"

python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$work" "$log_dir" \
  "$pipeline_dir/utility_foundation_expansion_status.json" \
  "$pipeline_dir/epsilon_module_manifest.json" \
  "$pipeline_dir/epsilon_module_status.json" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, logs, previous, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
previous_data = json.loads(previous.read_text())
assert previous_data["coverage"]["accepted_files"] == 12
assert previous_data["coverage"]["accepted_declarations"] == 128
assumptions = json.loads((logs / "assumption_summary.json").read_text())
record = assumptions["certificates"]["epsilon_notation_value"]
assert record["status"] == "CERTIFIED"
manifest = {
  "slice": "TRANSLATION_ORDER_UTIL_EPSILON",
  "generated_at": datetime.now().astimezone().isoformat(),
  "source_file": "util/epsilon.v",
  "source_commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
  "source_file_sha256": sha(source / "util/epsilon.v"),
  "public_declaration_count": 0,
  "observable_interface": "parsing notation ε expands to numeral one",
  "production_file": "Prosa/Util/Epsilon.lean",
  "production_source_sha256": sha(project / "Prosa/Util/Epsilon.lean"),
  "production_olean_sha256": sha(work / "olean/Prosa/Util/Epsilon.olean"),
  "validation_interface_source_sha256": sha(project / "Validation/fixtures/utility_foundation/EpsilonInterface.lean"),
  "export_sha256": sha(work / "imported/Epsilon.out"),
  "import_sha256": sha(work / "imported/ImportedEpsilon.vo"),
  "certificate_source_sha256": sha(project / "Validation/certificates/utility_foundation/EpsilonCertificate.v"),
  "certificate_vo_sha256": sha(work / "certificates/EpsilonCertificate.vo"),
  "assumption_audit": record,
  "actual_artifact_note": "The source has no named declaration. A compiled validation interface imports the actual production module and materializes the parser expansion as Nat before export/import.",
  "acceptance": "ACCEPTED_V06_FILE"
}
manifest_out.write_text(json.dumps(manifest, indent=2) + "\n")
status = {
  "slice": "TRANSLATION_ORDER_UTIL_EPSILON",
  "per_file": {
    "util/epsilon.v": {
      "public_declarations": 0,
      "translated": 0,
      "proof_clean": 0,
      "certified": 0,
      "module_interface_audited": True,
      "status": "ACCEPTED_V06_FILE",
      "reason": "zero-declaration notation module; both parser expansions are kernel-observed as Nat one through an actual-artifact interface"
    }
  },
  "coverage": {
    "accepted_files": 13,
    "authoritative_files": 357,
    "accepted_declarations": 128,
    "authoritative_declarations": 2439,
    "translated_but_not_certified": 0,
    "deferred_external_boundary": 239
  },
  "previous_status_sha256": sha(previous),
  "status": "PASS"
}
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY

(cd "$REPO_ROOT" && git diff --check)
echo "util/epsilon.v notation/module interface: ACCEPTED_V06_FILE"
echo "fresh work directory: $work"
