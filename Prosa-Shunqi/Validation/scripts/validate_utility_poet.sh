#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/translation_order/poet"
publish_dir="$VALIDATION_ROOT/imported/translation_order/poet"
cluster_dir="$VALIDATION_ROOT/logs/translation_order/cluster_results"
fixture_dir="$VALIDATION_ROOT/fixtures/translation_order"
common_dir="$VALIDATION_ROOT/certificates/common"
cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
mkdir -p "$log_dir" "$publish_dir" "$cluster_dir"

[[ $(validation_sha256 "$SOURCE_ROOT/util/poet.v") == \
  e14348ab5a0f3e262df7eb8702d34b4714e347f14c1f00bfbf24647bfc887c95 ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/poet.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 1 ]]
jq -e '.coverage.accepted_files == 15 and
  .coverage.accepted_declarations == 132 and
  .coverage.translated_but_not_certified == 0' \
  "$pipeline_dir/setoid_module_status.json" >/dev/null

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_before.log"

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Poet.lean"; then
  echo "forbidden production proof escape" >&2; exit 1
fi
for path in \
  "$common_dir/PoetCorrespondence.v" \
  "$cert_dir/PoetCertificate.v" \
  "$cert_dir/PoetTypeAudit.v" \
  "$cert_dir/PoetAssumptionAudit.v"; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
    echo "forbidden certificate proof escape in $path" >&2; exit 1
  fi
done

work=$(validation_fresh_workdir translation_order_poet)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/translation_order" \
  "$work/imported" "$work/source" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

validation_compile_lean_module "$work" Prosa/Util/Supremum \
  > "$log_dir/fresh_Supremum.log" 2>&1
validation_compile_lean_module "$work" Prosa/Util/List \
  > "$log_dir/fresh_List.log" 2>&1
validation_compile_lean_module "$work" Prosa/Util/Poet \
  > "$log_dir/fresh_Poet.log" 2>&1
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/PoetComputationInterface.olean" \
  "$fixture_dir/PoetComputationInterface.lean" \
  > "$log_dir/fresh_interface.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanPoetAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/poet_lean_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

export LEAN4EXPORT_STATEMENT_ONLY=Prosa.Util.Poet.forall_exists_implied_by_forall_in_zip
export LEAN4EXPORT_BODY_THEOREMS=$'Prosa.Validation.PoetInterface.production_length_nil\nProsa.Validation.PoetInterface.production_length_cons\nProsa.Validation.PoetInterface.production_zip_nil_left\nProsa.Validation.PoetInterface.production_zip_nil_right\nProsa.Validation.PoetInterface.production_zip_cons\nProsa.Validation.PoetInterface.production_all_nil\nProsa.Validation.PoetInterface.production_all_cons'
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  Validation.fixtures.translation_order.PoetComputationInterface -- \
  Prosa.Util.Poet.forall_exists_implied_by_forall_in_zip \
  Prosa.Validation.PoetInterface.production_length_nil \
  Prosa.Validation.PoetInterface.production_length_cons \
  Prosa.Validation.PoetInterface.production_zip_nil_left \
  Prosa.Validation.PoetInterface.production_zip_nil_right \
  Prosa.Validation.PoetInterface.production_zip_cons \
  Prosa.Validation.PoetInterface.production_all_nil \
  Prosa.Validation.PoetInterface.production_all_cons \
  > "$work/imported/Poet.out" 2> "$log_dir/export.log"
[[ -s "$work/imported/Poet.out" ]]

python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" --source-file util/poet.v \
  --module GeneratedPoetSource \
  --declarations forall_exists_implied_by_forall_in_zip \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.poet \
  --drop-import 'Require Export prosa.util.list.' \
  --output "$work/source/GeneratedPoetSource.v" \
  --metadata "$work/source/poet_source_extraction.json" \
  > "$log_dir/source_extraction.log"
jq -e '.transformations.dropped_irrelevant_imports ==
    ["Require Export prosa.util.list."] and
  .declarations.forall_exists_implied_by_forall_in_zip.elaborated_type_evidence ==
    "ELABORATED_ROCQ_CHECK"' \
  "$work/source/poet_source_extraction.json" >/dev/null
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedPoetSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/poet_source_extraction.json" "$log_dir/source_extraction.json"

cp "$fixture_dir/ImportedPoet.v" "$work/imported/"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
  99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedPoet.v) \
  > "$log_dir/import.log" 2>&1

cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,PoetCorrespondence}.v \
  "$work/certificates/"
cp "$cert_dir/"{PoetCertificate,PoetTypeAudit,PoetAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  PoetCorrespondence PoetCertificate PoetTypeAudit PoetAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_PoetAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$cert_dir/poet_assumption_config.json" \
  --log "$log_dir/assumptions.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"
jq -e '.certificates.forall_exists_implied_by_forall_in_zip |
    .status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" and
    (.semantic_premises | length == 0) and
    (.unexpected | length == 0) and
    (.source_theorem_dependency == false) and
    (.target_theorem_dependency == false)' \
  "$log_dir/assumption_summary.json" >/dev/null

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_after.json" \
  > "$log_dir/baseline_after.log"
python3 "$script_dir/publish_utility_cluster.py" \
  --project-root "$PROJECT_ROOT" --validation-root "$VALIDATION_ROOT" \
  --source-root "$SOURCE_ROOT" --exporter-root "$EXPORTER_ROOT" \
  --importer-root "$IMPORTER_ROOT" --work "$work" \
  --config "$cert_dir/poet_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/poet.json" \
  > "$log_dir/publication.log"

cp "$work/imported/"{Poet.out,ImportedPoet.v,ImportedPoet.vo} "$publish_dir/"
for module in PoetCorrespondence PoetCertificate PoetTypeAudit PoetAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$work" \
  "$cluster_dir/poet.json" "$pipeline_dir/setoid_module_status.json" \
  "$pipeline_dir/poet_module_manifest.json" \
  "$pipeline_dir/poet_module_status.json" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, cluster_path, previous_path, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
cluster = json.loads(cluster_path.read_text())
previous = json.loads(previous_path.read_text())
assert cluster["file_status"] == "ACCEPTED_V06_FILE"
assert len(cluster["declarations"]) == 1
row = cluster["declarations"][0]
assert row["acceptance"] == "ACCEPTED_V06_TRANSLATION"
assert row["semantic_status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
manifest = {
  "slice": "TRANSLATION_ORDER_UTIL_POET",
  "generated_at": datetime.now().astimezone().isoformat(),
  "source_file": "util/poet.v",
  "source_commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
  "source_file_sha256": sha(source / "util/poet.v"),
  "production_file": "Prosa/Util/Poet.lean",
  "production_source_sha256": sha(project / "Prosa/Util/Poet.lean"),
  "production_olean_sha256": sha(work / "olean/Prosa/Util/Poet.olean"),
  "export_sha256": sha(work / "imported/Poet.out"),
  "import_sha256": sha(work / "imported/ImportedPoet.vo"),
  "certificate_source_sha256": sha(project / "Validation/certificates/utility_foundation/PoetCertificate.v"),
  "certificate_vo_sha256": sha(work / "certificates/PoetCertificate.vo"),
  "type_audit_vo_sha256": sha(work / "certificates/PoetTypeAudit.vo"),
  "source_acquisition_metadata_sha256": sha(work / "source/poet_source_extraction.json"),
  "cluster_evidence_sha256": sha(cluster_path),
  "declarations": cluster["declarations"],
  "acceptance": "ACCEPTED_V06_FILE"
}
manifest_out.write_text(json.dumps(manifest, indent=2) + "\n")
status = {
  "slice": "TRANSLATION_ORDER_UTIL_POET",
  "per_file": {
    "util/poet.v": {
      "public_declarations": 1,
      "translated": 1,
      "proof_clean": 1,
      "certified": 1,
      "status": "ACCEPTED_V06_FILE"
    }
  },
  "coverage": {
    "accepted_files": previous["coverage"]["accepted_files"] + 1,
    "authoritative_files": 357,
    "accepted_declarations": previous["coverage"]["accepted_declarations"] + 1,
    "authoritative_declarations": 2439,
    "translated_but_not_certified": 0,
    "deferred_external_boundary": 239
  },
  "previous_status_sha256": sha(previous_path),
  "status": "PASS"
}
assert status["coverage"]["accepted_files"] == 16
assert status["coverage"]["accepted_declarations"] == 133
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY

(cd "$REPO_ROOT" && git diff --check)
echo "util/poet.v: 1 / 1 ACCEPTED_V06_FILE"
echo "fresh work directory: $work"
