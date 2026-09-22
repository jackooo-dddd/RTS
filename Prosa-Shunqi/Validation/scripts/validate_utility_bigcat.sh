#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/translation_order/bigcat"
publish_dir="$VALIDATION_ROOT/imported/translation_order/bigcat"
cluster_dir="$VALIDATION_ROOT/logs/translation_order/cluster_results"
fixture_dir="$VALIDATION_ROOT/fixtures/translation_order"
common_dir="$VALIDATION_ROOT/certificates/common"
cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
mkdir -p "$log_dir" "$publish_dir" "$cluster_dir"

[[ $(validation_sha256 "$SOURCE_ROOT/util/bigcat.v") == \
  2d6b62336f7f045dee0ce48265d8af295b4625522e8dcdddd06159e3780eede2 ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/bigcat.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 13 ]]
jq -e '.coverage.accepted_files == 16 and
  .coverage.accepted_declarations == 133 and
  .coverage.translated_but_not_certified == 0' \
  "$pipeline_dir/poet_module_status.json" >/dev/null

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_before.log"

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Bigcat.lean"; then
  echo "forbidden production proof escape" >&2; exit 1
fi
for path in \
  "$common_dir/BigcatCorrespondence.v" \
  "$cert_dir/BigcatCertificate.v" \
  "$cert_dir/BigcatTypeAudit.v" \
  "$cert_dir/BigcatAssumptionAudit.v"; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
    echo "forbidden certificate proof escape in $path" >&2; exit 1
  fi
done

work=$(validation_fresh_workdir translation_order_bigcat)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/translation_order" \
  "$work/imported" "$work/source/util" "$work/certificates" "$work/evidence"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

for module in Supremum Tactics Notation List Bigcat; do
  validation_compile_lean_module "$work" "Prosa/Util/$module" \
    > "$log_dir/fresh_${module}.log" 2>&1
done
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/BigcatComputationInterface.olean" \
  "$fixture_dir/BigcatComputationInterface.lean" \
  > "$log_dir/fresh_interface.log" 2>&1
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/BigcatNormalizationGuard.olean" \
  "$fixture_dir/BigcatNormalizationGuard.lean" \
  > "$work/evidence/normalization_guard.log" 2>&1
cp "$work/evidence/normalization_guard.log" "$log_dir/normalization_guard.log"
rg -q 'KERNEL_NORMALIZATION_GUARD.*size_big_nat.*proof=Eq.refl' \
  "$work/evidence/normalization_guard.log"
lean -DautoImplicit=false "$fixture_dir/LeanBigcatAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/bigcat_lean_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

statement_targets=(
  Prosa.Util.Bigcat.mem_bigcat_nat
  Prosa.Util.Bigcat.mem_bigcat_nat_exists
  Prosa.Util.Bigcat.mem_bigcat_ord
  Prosa.Util.Bigcat.bigcat_nat_uniq
  Prosa.Util.Bigcat.bigcat_nat_filter_eq_filter_bigcat_nat
  Prosa.Util.Bigcat.size_big_nat
  Prosa.Util.Bigcat.mem_bigcat
  Prosa.Util.Bigcat.mem_bigcat_exists
  Prosa.Util.Bigcat.bigcat_filter_eq_filter_bigcat
  Prosa.Util.Bigcat.bigcat_uniq
  Prosa.Util.Bigcat.seq_different_elements_nil
  Prosa.Util.Bigcat.bigcat_seq_uniqK
  Prosa.Util.Bigcat.bigcat_partitions
)
definition_targets=(
  Prosa.Util.Notation.bigCat
  Prosa.Util.Bigcat.bigCatFin
  Prosa.Util.Bigcat.bigCatSeq
  Prosa.Util.Bigcat.bigCatSeqAll
)
body_targets=(
  Prosa.Validation.BigcatInterface.production_bigCat_same
  Prosa.Validation.BigcatInterface.production_bigCat_of_le
  Prosa.Validation.BigcatInterface.production_bigCat_add_succ
  Prosa.Validation.BigcatInterface.production_bigCatFin_zero
  Prosa.Validation.BigcatInterface.production_bigCatFin_succ
  Prosa.Validation.BigcatInterface.production_bigCatSeq_eq
  Prosa.Validation.BigcatInterface.production_bigCatSeqAll_eq
  Prosa.Validation.BigcatInterface.production_append_nil
  Prosa.Validation.BigcatInterface.production_append_cons
  Prosa.Validation.BigcatInterface.production_flatMap_nil
  Prosa.Validation.BigcatInterface.production_flatMap_cons
  Prosa.Validation.BigcatInterface.production_filter_nil
  Prosa.Validation.BigcatInterface.production_filter_cons
  Prosa.Validation.BigcatInterface.production_length_nil
  Prosa.Validation.BigcatInterface.production_length_cons
)
export LEAN4EXPORT_STATEMENT_ONLY=$(printf '%s\n' "${statement_targets[@]}")
export LEAN4EXPORT_BODY_THEOREMS=$(printf '%s\n' "${body_targets[@]}")
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=Prosa.Util.Bigcat.size_big_nat
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=Finset.sum
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  Validation.fixtures.translation_order.BigcatComputationInterface -- \
  "${statement_targets[@]}" "${definition_targets[@]}" "${body_targets[@]}" \
  > "$work/imported/Bigcat.out" 2> "$log_dir/export.log"
[[ -s "$work/imported/Bigcat.out" ]]
rg -q '^NORMALIZED_THEOREM_TYPE Prosa.Util.Bigcat.size_big_nat.*defeq=true$' \
  "$log_dir/export.log"

cp "$SOURCE_ROOT/util/tactics.v" "$work/source/util/tactics.v"
cp "$SOURCE_ROOT/util/notation.v" "$work/source/util/notation.v"
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch") \
  > "$log_dir/source_patch_tactics.log" 2>&1
for source in tactics notation; do
  (cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
    rocq c -R "$work/source" prosa "util/$source.v") \
    > "$log_dir/source_${source}_compile.log" 2>&1
done
# Construct the source declaration list independently of array expansion
# details in the user's default shell.
declarations=$(printf '%s\n' "${statement_targets[@]}" | sed 's/.*\.//' | paste -sd, -)
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" --source-file util/bigcat.v \
  --module GeneratedBigcatSource --declarations "$declarations" \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.bigcat \
  --drop-import 'Require Export prosa.util.tactics prosa.util.list.' \
  --output "$work/source/GeneratedBigcatSource.v" \
  --metadata "$work/source/bigcat_source_extraction.json" \
  > "$log_dir/source_extraction.log"
jq -e '(.declarations | length) == 13 and
  ([.declarations[].elaborated_type_evidence == "ELABORATED_ROCQ_CHECK"] | all) and
  .transformations.dropped_irrelevant_imports ==
    ["Require Export prosa.util.tactics prosa.util.list."]' \
  "$work/source/bigcat_source_extraction.json" >/dev/null
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedBigcatSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/bigcat_source_extraction.json" \
  "$log_dir/source_extraction.json"

cp "$fixture_dir/ImportedBigcat.v" "$work/imported/"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
  99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedBigcat.v) \
  > "$log_dir/import.log" 2>&1

cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,BigcatCorrespondence}.v \
  "$work/certificates/"
cp "$cert_dir/"{BigcatCertificate,BigcatTypeAudit,BigcatAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  BigcatCorrespondence BigcatCertificate BigcatTypeAudit BigcatAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_BigcatAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$cert_dir/bigcat_assumption_config.json" \
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
  --config "$cert_dir/bigcat_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/bigcat.json" \
  > "$log_dir/publication.log"

cp "$work/imported/"{Bigcat.out,ImportedBigcat.v,ImportedBigcat.vo} "$publish_dir/"
for module in BigcatCorrespondence BigcatCertificate BigcatTypeAudit BigcatAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$work" "$log_dir" \
  "$cluster_dir/bigcat.json" "$pipeline_dir/poet_module_status.json" \
  "$pipeline_dir/bigcat_module_manifest.json" \
  "$pipeline_dir/bigcat_module_status.json" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, logs, cluster_path, previous_path, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
cluster = json.loads(cluster_path.read_text())
previous = json.loads(previous_path.read_text())
assert cluster["file_status"] == "ACCEPTED_V06_FILE"
assert len(cluster["declarations"]) == 13
assert all(r["acceptance"] == "ACCEPTED_V06_TRANSLATION" for r in cluster["declarations"])
assert all(r["semantic_status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" for r in cluster["declarations"])
manifest = {
  "slice": "TRANSLATION_ORDER_UTIL_BIGCAT",
  "generated_at": datetime.now().astimezone().isoformat(),
  "source_file": "util/bigcat.v",
  "source_commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
  "source_file_sha256": sha(source / "util/bigcat.v"),
  "production_file": "Prosa/Util/Bigcat.lean",
  "production_source_sha256": sha(project / "Prosa/Util/Bigcat.lean"),
  "production_olean_sha256": sha(work / "olean/Prosa/Util/Bigcat.olean"),
  "export_sha256": sha(work / "imported/Bigcat.out"),
  "import_sha256": sha(work / "imported/ImportedBigcat.vo"),
  "certificate_source_sha256": sha(project / "Validation/certificates/utility_foundation/BigcatCertificate.v"),
  "certificate_vo_sha256": sha(work / "certificates/BigcatCertificate.vo"),
  "type_audit_vo_sha256": sha(work / "certificates/BigcatTypeAudit.vo"),
  "assumption_audit_vo_sha256": sha(work / "certificates/BigcatAssumptionAudit.vo"),
  "normalization_guard_olean_sha256": sha(work / "olean/Validation/fixtures/translation_order/BigcatNormalizationGuard.olean"),
  "source_acquisition_metadata_sha256": sha(work / "source/bigcat_source_extraction.json"),
  "cluster_evidence_sha256": sha(cluster_path),
  "declarations": cluster["declarations"],
  "acceptance": "ACCEPTED_V06_FILE"
}
manifest_out.write_text(json.dumps(manifest, indent=2) + "\n")
status = {
  "slice": "TRANSLATION_ORDER_UTIL_BIGCAT",
  "per_file": {
    "util/bigcat.v": {
      "public_declarations": 13,
      "translated": 13,
      "proof_clean": 13,
      "certified": 13,
      "status": "ACCEPTED_V06_FILE"
    }
  },
  "coverage": {
    "accepted_files": previous["coverage"]["accepted_files"] + 1,
    "authoritative_files": 357,
    "accepted_declarations": previous["coverage"]["accepted_declarations"] + 13,
    "authoritative_declarations": 2439,
    "translated_but_not_certified": 0,
    "deferred_external_boundary": 239
  },
  "previous_status_sha256": sha(previous_path),
  "status": "PASS"
}
assert status["coverage"]["accepted_files"] == 17
assert status["coverage"]["accepted_declarations"] == 146
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY

(cd "$REPO_ROOT" && git diff --check)
echo "util/bigcat.v: 13 / 13 ACCEPTED_V06_FILE"
echo "fresh work directory: $work"
