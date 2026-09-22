#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/translation_order/minmax"
publish_dir="$VALIDATION_ROOT/imported/translation_order/minmax"
cluster_dir="$VALIDATION_ROOT/logs/translation_order/cluster_results"
fixture_dir="$VALIDATION_ROOT/fixtures/translation_order"
common_dir="$VALIDATION_ROOT/certificates/common"
cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
mkdir -p "$log_dir" "$publish_dir" "$cluster_dir"

[[ $(validation_sha256 "$SOURCE_ROOT/util/minmax.v") == \
  a7ab36b3770500f8e136e51f8e324e54c6d8b741e368bc23ff8d87b240009830 ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/minmax.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 10 ]]
jq -e '.coverage.accepted_files == 17 and
  .coverage.accepted_declarations == 146 and
  .coverage.translated_but_not_certified == 0' \
  "$pipeline_dir/bigcat_module_status.json" >/dev/null

# Extending the bridge library must not silently invalidate the immediately
# preceding file. TypeSPropRelation is deliberately separate for this reason.
python3 - "$VALIDATION_ROOT" "$pipeline_dir/bigcat_module_manifest.json" <<'PY'
import hashlib, json, sys
from pathlib import Path
root, manifest_path = map(Path, sys.argv[1:])
manifest = json.loads(manifest_path.read_text())
current = hashlib.sha256(
    (root / "certificates/common/LogicalRelation.v").read_bytes()
).hexdigest()
recorded = {
    row["foundation_dependencies"]["bridge_source_sha256"]["LogicalRelation.v"]
    for row in manifest["declarations"]
}
assert recorded == {current}, (recorded, current)
PY

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_before.log"

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Minmax.lean"; then
  echo "forbidden production proof escape" >&2; exit 1
fi
for path in \
  "$common_dir/TypeSPropRelation.v" \
  "$common_dir/MinmaxCorrespondence.v" \
  "$cert_dir/MinmaxCertificate.v" \
  "$cert_dir/MinmaxTypeAudit.v" \
  "$cert_dir/MinmaxAssumptionAudit.v"; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
    echo "forbidden certificate proof escape in $path" >&2; exit 1
  fi
done

work=$(validation_fresh_workdir translation_order_minmax)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/translation_order" \
  "$work/imported" "$work/source" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

for module in Tactics Notation Rel Seqset Subadditivity Supremum Nat List Setoid Minmax; do
  validation_compile_lean_module "$work" "Prosa/Util/$module" \
    > "$log_dir/fresh_${module}.log" 2>&1
done
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/MinmaxComputationInterface.olean" \
  "$fixture_dir/MinmaxComputationInterface.lean" \
  > "$log_dir/fresh_interface.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanMinmaxAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/minmax_lean_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

statement_targets=(
  Prosa.Util.Minmax.leq_bigmax_cond_seq
  Prosa.Util.Minmax.leq_bigmax_sup
  Prosa.Util.Minmax.bigmax_leq_seqP
  Prosa.Util.Minmax.leq_big_max
  Prosa.Util.Minmax.bigmax_ord_ltn_identity
  Prosa.Util.Minmax.bigmax_ltn_ord
  Prosa.Util.Minmax.bigmax_pred
  Prosa.Util.Minmax.bigmax_witness
  Prosa.Util.Minmax.bigmax_witness_diff
  Prosa.Util.Minmax.bigmax_subset
)
definition_targets=(
  Prosa.Util.Minmax.bigMaxListCond
  Prosa.Util.Minmax.bigMaxNatRange
)
body_targets=(
  Prosa.Validation.MinmaxInterface.production_bigMaxListCond_nil
  Prosa.Validation.MinmaxInterface.production_bigMaxListCond_cons
  Prosa.Validation.MinmaxInterface.production_bigMaxNatRange_zero
  Prosa.Validation.MinmaxInterface.production_bigMaxNatRange_succ
  Prosa.Validation.MinmaxInterface.production_any_nil
  Prosa.Validation.MinmaxInterface.production_any_cons
  Prosa.Validation.MinmaxInterface.production_natMax_zero_left
  Prosa.Validation.MinmaxInterface.production_natMax_zero_right
  Prosa.Validation.MinmaxInterface.production_natMax_succ_succ
)
export LEAN4EXPORT_STATEMENT_ONLY=$(printf '%s\n' "${statement_targets[@]}")
export LEAN4EXPORT_BODY_THEOREMS=$(printf '%s\n' "${body_targets[@]}")
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  Validation.fixtures.translation_order.MinmaxComputationInterface -- \
  "${statement_targets[@]}" "${definition_targets[@]}" "${body_targets[@]}" \
  > "$work/imported/Minmax.out" 2> "$log_dir/export.log"
[[ -s "$work/imported/Minmax.out" ]]

declarations=$(printf '%s\n' "${statement_targets[@]}" | sed 's/.*\.//' | paste -sd, -)
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" --source-file util/minmax.v \
  --module GeneratedMinmaxSource --declarations "$declarations" \
  --type-valued bigmax_leq_seqP \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.minmax \
  --drop-import 'Require Export prosa.util.notation prosa.util.nat prosa.util.list prosa.util.setoid.' \
  --output "$work/source/GeneratedMinmaxSource.v" \
  --metadata "$work/source/minmax_source_extraction.json" \
  > "$log_dir/source_extraction.log"
jq -e '(.declarations | length) == 10 and
  ([.declarations[].elaborated_type_evidence == "ELABORATED_ROCQ_CHECK"] | all) and
  .declarations.bigmax_leq_seqP.statement_sort == "Type" and
  ([.declarations | to_entries[] | select(.key != "bigmax_leq_seqP") |
      .value.statement_sort == "Prop"] | all) and
  .transformations.dropped_irrelevant_imports ==
    ["Require Export prosa.util.notation prosa.util.nat prosa.util.list prosa.util.setoid."]' \
  "$work/source/minmax_source_extraction.json" >/dev/null
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedMinmaxSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/minmax_source_extraction.json" "$log_dir/source_extraction.json"

cp "$fixture_dir/ImportedMinmax.v" "$work/imported/"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
  99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedMinmax.v) \
  > "$log_dir/import.log" 2>&1

cp "$common_dir/"{PropSPropFoundation,LogicalRelation,TypeSPropRelation,SubadditivityNatCorrespondence,MinmaxCorrespondence}.v \
  "$work/certificates/"
cp "$cert_dir/"{MinmaxCertificate,MinmaxTypeAudit,MinmaxAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation TypeSPropRelation \
  SubadditivityNatCorrespondence MinmaxCorrespondence MinmaxCertificate \
  MinmaxTypeAudit MinmaxAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_MinmaxAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$cert_dir/minmax_assumption_config.json" \
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
  --config "$cert_dir/minmax_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/minmax.json" \
  > "$log_dir/publication.log"

cp "$work/imported/"{Minmax.out,ImportedMinmax.v,ImportedMinmax.vo} "$publish_dir/"
for module in TypeSPropRelation MinmaxCorrespondence MinmaxCertificate \
  MinmaxTypeAudit MinmaxAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$work" "$log_dir" \
  "$cluster_dir/minmax.json" "$pipeline_dir/bigcat_module_status.json" \
  "$pipeline_dir/minmax_module_manifest.json" \
  "$pipeline_dir/minmax_module_status.json" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, logs, cluster_path, previous_path, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
cluster = json.loads(cluster_path.read_text())
previous = json.loads(previous_path.read_text())
assert cluster["file_status"] == "ACCEPTED_V06_FILE"
assert len(cluster["declarations"]) == 10
assert all(r["acceptance"] == "ACCEPTED_V06_TRANSLATION" for r in cluster["declarations"])
assert all(r["semantic_status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" for r in cluster["declarations"])
manifest = {
  "slice": "TRANSLATION_ORDER_UTIL_MINMAX",
  "generated_at": datetime.now().astimezone().isoformat(),
  "source_file": "util/minmax.v",
  "source_commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
  "source_file_sha256": sha(source / "util/minmax.v"),
  "production_file": "Prosa/Util/Minmax.lean",
  "production_source_sha256": sha(project / "Prosa/Util/Minmax.lean"),
  "production_olean_sha256": sha(work / "olean/Prosa/Util/Minmax.olean"),
  "export_sha256": sha(work / "imported/Minmax.out"),
  "import_sha256": sha(work / "imported/ImportedMinmax.vo"),
  "certificate_source_sha256": sha(project / "Validation/certificates/utility_foundation/MinmaxCertificate.v"),
  "certificate_vo_sha256": sha(work / "certificates/MinmaxCertificate.vo"),
  "type_audit_vo_sha256": sha(work / "certificates/MinmaxTypeAudit.vo"),
  "assumption_audit_vo_sha256": sha(work / "certificates/MinmaxAssumptionAudit.vo"),
  "source_acquisition_metadata_sha256": sha(work / "source/minmax_source_extraction.json"),
  "cluster_evidence_sha256": sha(cluster_path),
  "declarations": cluster["declarations"],
  "acceptance": "ACCEPTED_V06_FILE"
}
manifest_out.write_text(json.dumps(manifest, indent=2) + "\n")
status = {
  "slice": "TRANSLATION_ORDER_UTIL_MINMAX",
  "per_file": {
    "util/minmax.v": {
      "public_declarations": 10,
      "translated": 10,
      "proof_clean": 10,
      "certified": 10,
      "status": "ACCEPTED_V06_FILE"
    }
  },
  "coverage": {
    "accepted_files": previous["coverage"]["accepted_files"] + 1,
    "authoritative_files": 357,
    "accepted_declarations": previous["coverage"]["accepted_declarations"] + 10,
    "authoritative_declarations": 2439,
    "translated_but_not_certified": 0,
    "deferred_external_boundary": 239
  },
  "previous_status_sha256": sha(previous_path),
  "status": "PASS"
}
assert status["coverage"]["accepted_files"] == 18
assert status["coverage"]["accepted_declarations"] == 156
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY

(cd "$REPO_ROOT" && git diff --check)
echo "util/minmax.v: 10 / 10 ACCEPTED_V06_FILE"
echo "fresh work directory: $work"
