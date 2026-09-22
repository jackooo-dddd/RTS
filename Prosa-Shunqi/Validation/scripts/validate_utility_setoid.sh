#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/translation_order/setoid"
publish_dir="$VALIDATION_ROOT/imported/translation_order/setoid"
cluster_dir="$VALIDATION_ROOT/logs/translation_order/cluster_results"
fixture_dir="$VALIDATION_ROOT/fixtures/translation_order"
common_dir="$VALIDATION_ROOT/certificates/common"
cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
mkdir -p "$log_dir" "$publish_dir" "$cluster_dir"

[[ $(validation_sha256 "$SOURCE_ROOT/util/setoid.v") == \
  163c87ece26427032dd5e4ced3ec1598447b4e055a94964574d77196f0a51622 ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/setoid.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 3 ]]
jq -e '.coverage.accepted_files == 14 and
  .coverage.accepted_declarations == 129 and
  .coverage.translated_but_not_certified == 0' \
  "$pipeline_dir/bigop_module_status.json" >/dev/null

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_before.log"

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Setoid.lean"; then
  echo "forbidden production proof escape" >&2; exit 1
fi
for path in \
  "$common_dir/SetoidCorrespondence.v" \
  "$cert_dir/SetoidCertificate.v" \
  "$cert_dir/SetoidTypeAudit.v" \
  "$cert_dir/SetoidAssumptionAudit.v"; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
    echo "forbidden certificate proof escape in $path" >&2; exit 1
  fi
done

work=$(validation_fresh_workdir translation_order_setoid)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/translation_order" \
  "$work/imported" "$work/source/util" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

validation_compile_lean_module "$work" Prosa/Util/Setoid \
  > "$log_dir/fresh_Setoid.log" 2>&1
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/SetoidComputationInterface.olean" \
  "$fixture_dir/SetoidComputationInterface.lean" \
  > "$log_dir/fresh_interface.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanSetoidAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/setoid_lean_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

export LEAN4EXPORT_STATEMENT_ONLY=Prosa.Util.Setoid.leb_eq
export LEAN4EXPORT_BODY_THEOREMS=Prosa.Validation.SetoidInterface.production_leqRW_apply
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  Validation.fixtures.translation_order.SetoidComputationInterface -- \
  Prosa.Util.Setoid.leb \
  Prosa.Util.Setoid.leb_eq \
  Prosa.Util.Setoid.leqRW \
  Prosa.Validation.SetoidInterface.production_leqRW_apply \
  > "$work/imported/Setoid.out" 2> "$log_dir/export.log"
[[ -s "$work/imported/Setoid.out" ]]

cp "$SOURCE_ROOT/util/setoid.v" "$work/source/util/setoid.v"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa util/setoid.v) \
  > "$log_dir/source_compile.log" 2>&1

cp "$fixture_dir/ImportedSetoid.v" "$work/imported/"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
  99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedSetoid.v) \
  > "$log_dir/import.log" 2>&1

cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,SetoidCorrespondence}.v \
  "$work/certificates/"
cp "$cert_dir/"{SetoidCertificate,SetoidTypeAudit,SetoidAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  SetoidCorrespondence SetoidCertificate SetoidTypeAudit SetoidAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_SetoidAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$cert_dir/setoid_assumption_config.json" \
  --log "$log_dir/assumptions.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"
jq -e '[.certificates[] |
    .status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" and
    (.semantic_premises | length == 0) and
    (.unexpected | length == 0) and
    (.source_theorem_dependency == false) and
    (.target_theorem_dependency == false)] | all' \
  "$log_dir/assumption_summary.json" >/dev/null

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_after.json" \
  > "$log_dir/baseline_after.log"
python3 "$script_dir/publish_utility_cluster.py" \
  --project-root "$PROJECT_ROOT" --validation-root "$VALIDATION_ROOT" \
  --source-root "$SOURCE_ROOT" --exporter-root "$EXPORTER_ROOT" \
  --importer-root "$IMPORTER_ROOT" --work "$work" \
  --config "$cert_dir/setoid_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/setoid.json" \
  > "$log_dir/publication.log"

cp "$work/imported/"{Setoid.out,ImportedSetoid.v,ImportedSetoid.vo} "$publish_dir/"
for module in SetoidCorrespondence SetoidCertificate SetoidTypeAudit SetoidAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$work" "$log_dir" \
  "$cluster_dir/setoid.json" "$pipeline_dir/bigop_module_status.json" \
  "$pipeline_dir/setoid_module_manifest.json" \
  "$pipeline_dir/setoid_module_status.json" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, logs, cluster_path, previous_path, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
cluster = json.loads(cluster_path.read_text())
previous = json.loads(previous_path.read_text())
assert cluster["file_status"] == "ACCEPTED_V06_FILE"
assert len(cluster["declarations"]) == 3
assert all(r["acceptance"] == "ACCEPTED_V06_TRANSLATION" for r in cluster["declarations"])
manifest = {
  "slice": "TRANSLATION_ORDER_UTIL_SETOID",
  "generated_at": datetime.now().astimezone().isoformat(),
  "source_file": "util/setoid.v",
  "source_commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
  "source_file_sha256": sha(source / "util/setoid.v"),
  "production_file": "Prosa/Util/Setoid.lean",
  "production_source_sha256": sha(project / "Prosa/Util/Setoid.lean"),
  "production_olean_sha256": sha(work / "olean/Prosa/Util/Setoid.olean"),
  "export_sha256": sha(work / "imported/Setoid.out"),
  "import_sha256": sha(work / "imported/ImportedSetoid.vo"),
  "certificate_source_sha256": sha(project / "Validation/certificates/utility_foundation/SetoidCertificate.v"),
  "certificate_vo_sha256": sha(work / "certificates/SetoidCertificate.vo"),
  "type_audit_vo_sha256": sha(work / "certificates/SetoidTypeAudit.vo"),
  "cluster_evidence_sha256": sha(cluster_path),
  "declarations": cluster["declarations"],
  "acceptance": "ACCEPTED_V06_FILE"
}
manifest_out.write_text(json.dumps(manifest, indent=2) + "\n")
status = {
  "slice": "TRANSLATION_ORDER_UTIL_SETOID",
  "per_file": {
    "util/setoid.v": {
      "public_declarations": 3,
      "translated": 3,
      "proof_clean": 3,
      "certified": 3,
      "status": "ACCEPTED_V06_FILE"
    }
  },
  "coverage": {
    "accepted_files": previous["coverage"]["accepted_files"] + 1,
    "authoritative_files": 357,
    "accepted_declarations": previous["coverage"]["accepted_declarations"] + 3,
    "authoritative_declarations": 2439,
    "translated_but_not_certified": 0,
    "deferred_external_boundary": 239
  },
  "previous_status_sha256": sha(previous_path),
  "status": "PASS"
}
assert status["coverage"]["accepted_files"] == 15
assert status["coverage"]["accepted_declarations"] == 132
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY

(cd "$REPO_ROOT" && git diff --check)
echo "util/setoid.v: 3 / 3 ACCEPTED_V06_FILE"
echo "fresh work directory: $work"
