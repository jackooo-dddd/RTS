#!/usr/bin/env bash

VALIDATION_PREPARE_INPUTS=(
  "$VALIDATION_ROOT/tooling/nondecreasing_incremental_descriptor.json"
  "$VALIDATION_ROOT/tooling/nondecreasing_export_config.json"
  "$VALIDATION_ROOT/tooling/nondecreasing_incremental_hooks.sh"
  "$VALIDATION_ROOT/scripts/run_incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/validation_common.sh"
)

VALIDATION_CHECK_INPUTS=(
  "$VALIDATION_ROOT/scripts/audit_assumptions.py"
  "$VALIDATION_ROOT/scripts/audit_utility_foundation_baseline.py"
  "$VALIDATION_ROOT/scripts/publish_utility_cluster.py"
  "$VALIDATION_ROOT/certificates/common/PropSPropFoundation.v"
  "$VALIDATION_ROOT/certificates/common/LogicalRelation.v"
  "$VALIDATION_ROOT/certificates/common/SubadditivityNatCorrespondence.v"
  "$VALIDATION_ROOT/certificates/common/NatSubCorrespondence.v"
  "$VALIDATION_ROOT/certificates/common/NondecreasingBaseAdapter.v"
  "$VALIDATION_ROOT/certificates/common/NondecreasingCorrespondence.v"
  "$VALIDATION_ROOT/certificates/utility_foundation/NondecreasingSimpleCertificate.v"
  "$VALIDATION_ROOT/certificates/utility_foundation/NondecreasingTypeAudit.v"
  "$VALIDATION_ROOT/certificates/utility_foundation/NondecreasingAssumptionAudit.v"
  "$VALIDATION_ROOT/certificates/utility_foundation/nondecreasing_assumption_config.json"
  "$VALIDATION_ROOT/certificates/utility_foundation/nondecreasing_cluster_config.json"
)

validation_prepare_lean_build() {
  [[ $(validation_sha256 "$SOURCE_ROOT/util/nondecreasing.v") == \
    34c20d63e8e9bf22691466a247704518093ea66e8e89ed3c913891ba425b93a3 ]]
  [[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/nondecreasing.v" for r in csv.DictReader(open(sys.argv[1]))))' \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 33 ]]
  jq -e '.coverage.accepted_files == 19 and
    .coverage.accepted_declarations == 171 and
    .coverage.translated_but_not_certified == 0' \
    "$VALIDATION_ROOT/planning/v06_pipeline/div_mod_module_status.json" >/dev/null
  if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Nondecreasing.lean"; then
    echo "forbidden production proof escape" >&2
    return 1
  fi
  mkdir -p "$VALIDATION_PREPARED/olean/Prosa/Util" \
    "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order"
  local module
  for module in Tactics Supremum List Epsilon Nat Nondecreasing; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Util/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/NondecreasingComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/NondecreasingComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_interface.log" 2>&1
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    "$VALIDATION_ROOT/fixtures/translation_order/NondecreasingNormalizationGuards.lean" \
    > "$VALIDATION_PREPARED/normalization_guards.log" 2>&1
  cp "$VALIDATION_PREPARED/normalization_guards.log" \
    "$VALIDATION_RUN_LOG/normalization_guards.log"
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    "$VALIDATION_ROOT/fixtures/translation_order/LeanNondecreasingAudit.lean" \
    > "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" 2>&1
  cp "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    "$VALIDATION_RUN_LOG/lean_freeze_and_axioms.log"
  python3 "$VALIDATION_ROOT/scripts/audit_lean_axioms.py" \
    --config "$VALIDATION_ROOT/fixtures/translation_order/nondecreasing_lean_axiom_config.json" \
    --log "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    --output "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    > "$VALIDATION_RUN_LOG/lean_axiom_classifier.log"
  jq -e '((.declarations | length) == 33) and
    ([.declarations[] | (.unexpected_axioms | length == 0)] | all)' \
    "$VALIDATION_PREPARED/lean_axiom_summary.json" >/dev/null
  VALIDATION_STAGE_OUTPUTS=(
    "tactics_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Tactics.olean"
    "supremum_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Supremum.olean"
    "list_olean=$VALIDATION_PREPARED/olean/Prosa/Util/List.olean"
    "epsilon_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Epsilon.olean"
    "nat_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Nat.olean"
    "nondecreasing_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Nondecreasing.olean"
    "interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/NondecreasingComputationInterface.olean"
    "normalization_guards=$VALIDATION_PREPARED/normalization_guards.log"
    "lean_freeze=$VALIDATION_PREPARED/lean_freeze_and_axioms.log"
    "lean_axiom_summary=$VALIDATION_PREPARED/lean_axiom_summary.json"
  )
}

validation_prepare_source_acquisition() {
  mkdir -p "$VALIDATION_PREPARED/source/util"
  local module
  for module in tactics epsilon nat; do
    cp "$SOURCE_ROOT/util/${module}.v" \
      "$VALIDATION_PREPARED/source/util/${module}.v"
  done
  patch -s -d "$VALIDATION_PREPARED/source" -p1 \
    < "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch"
  ulimit -s 65520
  for module in tactics epsilon nat; do
    (cd "$VALIDATION_PREPARED/source" && \
      opam exec --switch="$ROCQ_SWITCH" -- rocq c \
        -R "$VALIDATION_PREPARED/source" prosa \
        "util/${module}.v") \
      > "$VALIDATION_RUN_LOG/source_${module}.log" 2>&1
  done
  python3 "$VALIDATION_ROOT/scripts/extract_v06_semantic_source.py" \
    --source-root "$SOURCE_ROOT" --source-file util/nondecreasing.v \
    --module GeneratedNondecreasingSource \
    --declarations 'nondecreasing_sequence,increasing_sequence,distances,iota_is_increasing_sequence,increasing_implies_nondecreasing,nondec_seq_zero_first,nondecreasing_sequence_2cons_leVeq,nondecreasing_sequence_cons,nondecreasing_sequence_add_min,nondecreasing_sequence_cons_double,nondecreasing_sequence_cons_min,nondecreasing_sequence_cons_smin,antidensity_of_nondecreasing_seq,belonging_to_segment_of_seq_is_total,last_is_max_in_nondecreasing_seq,nodup_sort_2cons_eq,nodup_sort_2cons_lt,last0_undup,nondecreasing_sequence_undup,undup_nth_le,distances_unfold_2cons,distances_unfold_2app_last,distances_unfold_1app_last,distance_between_neighboring_elements_le_max_distance_in_seq,function_of_distances_is_correct,size_of_seq_of_distances,distances_of_iota_ε,max_distance_in_nontrivial_seq_is_positive,last_seq_minus_last_distance_seq,max_distance_in_seq_le_last_element_of_seq,distances_iota_filtered,distances_positive_undup,domination_of_distances_implies_domination_of_seq' \
    --computational 'nondecreasing_sequence,increasing_sequence,distances' \
    --drop-import 'Require Export prosa.util.list.' \
    --local-binding 'max0=foldl maxn 0' \
    --local-binding 'first0=head 0' \
    --local-binding 'last0=last 0' \
    --elaborated-evidence \
      "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
    --qualified-prefix prosa.util.nondecreasing \
    --output "$VALIDATION_PREPARED/source/GeneratedNondecreasingSource.v" \
    --metadata "$VALIDATION_PREPARED/source/nondecreasing_source_extraction.json" \
    > "$VALIDATION_RUN_LOG/source_extraction.log"
  jq -e '(.declarations | length) == 33 and
      ([.declarations | to_entries[] |
        select(.key == "nondecreasing_sequence" or
               .key == "increasing_sequence" or
               .key == "distances") |
        .value.acquisition_mode == "BODY_EXACT"] | all) and
      (.transformations.dropped_irrelevant_imports ==
        ["Require Export prosa.util.list."]) and
      (.transformations.local_bindings == {
        "max0": "foldl maxn 0",
        "first0": "head 0",
        "last0": "last 0"
      }) and
      ([.declarations | to_entries[] |
        select(.key != "nondecreasing_sequence" and
               .key != "increasing_sequence" and
               .key != "distances") |
        (.value.acquisition_mode == "STATEMENT_EXACT_PROOF_OMITTED" and
         .value.elaborated_type_evidence == "ELABORATED_ROCQ_CHECK")] | all)' \
    "$VALIDATION_PREPARED/source/nondecreasing_source_extraction.json" >/dev/null
  (cd "$VALIDATION_PREPARED/source" && \
    opam exec --switch="$ROCQ_SWITCH" -- rocq c \
      -R "$VALIDATION_PREPARED/source" prosa \
      GeneratedNondecreasingSource.v) \
    > "$VALIDATION_RUN_LOG/generated_source_compile.log" 2>&1
  VALIDATION_STAGE_OUTPUTS=(
    "source_tactics=$VALIDATION_PREPARED/source/util/tactics.vo"
    "source_epsilon=$VALIDATION_PREPARED/source/util/epsilon.vo"
    "source_nat=$VALIDATION_PREPARED/source/util/nat.vo"
    "source_signature=$VALIDATION_PREPARED/source/GeneratedNondecreasingSource.v"
    "source_signature_vo=$VALIDATION_PREPARED/source/GeneratedNondecreasingSource.vo"
    "source_metadata=$VALIDATION_PREPARED/source/nondecreasing_source_extraction.json"
  )
}

validation_prepare_export() {
  "$VALIDATION_ROOT/scripts/export_actual_artifact.sh" \
    --config "$VALIDATION_ROOT/tooling/nondecreasing_export_config.json" \
    --output "$VALIDATION_PREPARED/imported/Nondecreasing.out" \
    --log "$VALIDATION_RUN_LOG/export.log" \
    --metadata "$VALIDATION_PREPARED/imported/nondecreasing_export_metadata.json"
  VALIDATION_STAGE_OUTPUTS=(
    "export=$VALIDATION_PREPARED/imported/Nondecreasing.out"
    "export_metadata=$VALIDATION_PREPARED/imported/nondecreasing_export_metadata.json"
  )
}

validation_prepare_rocq_import() {
  mkdir -p "$VALIDATION_PREPARED/certificates"
  cp "$VALIDATION_ROOT/imported/utility_foundation/Nat.out" \
    "$VALIDATION_PREPARED/imported/Nat.out"
  cp "$VALIDATION_ROOT/imported/utility_foundation/ImportedNat.v" \
    "$VALIDATION_PREPARED/imported/ImportedNat.v"
  cp "$VALIDATION_ROOT/imported/foundation_slice_2_closure/Subadditivity.out" \
    "$VALIDATION_PREPARED/imported/Subadditivity.out"
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/ImportedSubadditivity.v" \
    "$VALIDATION_PREPARED/imported/ImportedSubadditivity.v"
  cp "$VALIDATION_ROOT/fixtures/translation_order/ImportedNondecreasing.v" \
    "$VALIDATION_PREPARED/imported/ImportedNondecreasing.v"
  ulimit -s 65520
  local module
  for module in ImportedNat ImportedSubadditivity ImportedNondecreasing; do
    (cd "$VALIDATION_PREPARED/imported" && \
      validation_rocq_compile "$VALIDATION_PREPARED" "${module}.v") \
      > "$VALIDATION_RUN_LOG/import_${module}.log" 2>&1
  done
  VALIDATION_STAGE_OUTPUTS=(
    "nat_export=$VALIDATION_PREPARED/imported/Nat.out"
    "nat_import_source=$VALIDATION_PREPARED/imported/ImportedNat.v"
    "nat_import_vo=$VALIDATION_PREPARED/imported/ImportedNat.vo"
    "subadditivity_export=$VALIDATION_PREPARED/imported/Subadditivity.out"
    "subadditivity_import_source=$VALIDATION_PREPARED/imported/ImportedSubadditivity.v"
    "subadditivity_import_vo=$VALIDATION_PREPARED/imported/ImportedSubadditivity.vo"
    "import_source=$VALIDATION_PREPARED/imported/ImportedNondecreasing.v"
    "import_vo=$VALIDATION_PREPARED/imported/ImportedNondecreasing.vo"
  )
}

validation_check_setup() {
  cp -R "$VALIDATION_PREPARED/olean/." "$VALIDATION_PHASE_WORK/olean/"
  cp -R "$VALIDATION_PREPARED/source/." "$VALIDATION_PHASE_WORK/source/"
  cp -R "$VALIDATION_PREPARED/imported/." "$VALIDATION_PHASE_WORK/imported/"
  cp "$VALIDATION_PREPARED/normalization_guards.log" \
    "$VALIDATION_PHASE_WORK/normalization_guards.log"
}

validation_check_certificate_compile() {
  local common_dir="$VALIDATION_ROOT/certificates/common"
  local cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
  mkdir -p "$VALIDATION_PHASE_WORK/certificates"
  cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,NatSubCorrespondence,NondecreasingBaseAdapter,NondecreasingCorrespondence}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$cert_dir/"{NondecreasingSimpleCertificate,NondecreasingTypeAudit,NondecreasingAssumptionAudit}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  local path
  for path in \
    "$common_dir/NondecreasingBaseAdapter.v" \
    "$common_dir/NondecreasingCorrespondence.v" \
    "$cert_dir/NondecreasingSimpleCertificate.v" \
    "$cert_dir/NondecreasingTypeAudit.v" \
    "$cert_dir/NondecreasingAssumptionAudit.v"; do
    if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
      echo "forbidden certificate proof escape in $path" >&2
      return 1
    fi
  done
  ulimit -s 65520
  local module
  for module in PropSPropFoundation LogicalRelation \
      SubadditivityNatCorrespondence NatSubCorrespondence \
      NondecreasingBaseAdapter NondecreasingCorrespondence \
      NondecreasingSimpleCertificate NondecreasingTypeAudit \
      NondecreasingAssumptionAudit; do
    validation_rocq_compile "$VALIDATION_PHASE_WORK" \
      "$VALIDATION_PHASE_WORK/certificates/$module.v" \
      > "$VALIDATION_RUN_LOG/rocq_${module}.log" 2>&1
  done
  cp "$VALIDATION_RUN_LOG/rocq_NondecreasingAssumptionAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  VALIDATION_STAGE_OUTPUTS=(
    "adapter_vo=$VALIDATION_PHASE_WORK/certificates/NondecreasingBaseAdapter.vo"
    "bridge_vo=$VALIDATION_PHASE_WORK/certificates/NondecreasingCorrespondence.vo"
    "certificate_vo=$VALIDATION_PHASE_WORK/certificates/NondecreasingSimpleCertificate.vo"
    "type_audit_vo=$VALIDATION_PHASE_WORK/certificates/NondecreasingTypeAudit.vo"
    "assumption_audit_vo=$VALIDATION_PHASE_WORK/certificates/NondecreasingAssumptionAudit.vo"
    "assumption_log=$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  )
}

validation_check_assumption_audit() {
  local cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/nondecreasing_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/assumption_classifier.log"
  jq -e '
    (.certificates | length) == 33 and
    ([.certificates[] | select(.status == "CERTIFIED")] | length) == 1 and
    ([.certificates[] |
      select(.status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")] | length) == 32 and
    ([.certificates[] |
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" >/dev/null
  python3 "$VALIDATION_ROOT/scripts/audit_utility_foundation_baseline.py" \
    --project-root "$PROJECT_ROOT" \
    --output "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" \
    > "$VALIDATION_RUN_LOG/baseline_after.log"
  jq -e '.status == "PASS"' \
    "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" >/dev/null
  VALIDATION_STAGE_OUTPUTS=(
    "assumption_summary=$VALIDATION_PHASE_WORK/certificates/assumption_summary.json"
    "baseline_audit=$VALIDATION_PHASE_WORK/certificates/baseline_after.json"
  )
}

validation_finalize_publication() {
  local cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
  local cluster_dir="$VALIDATION_ROOT/logs/translation_order/cluster_results"
  local publish_dir="$VALIDATION_ROOT/imported/translation_order/nondecreasing"
  local pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
  mkdir -p "$cluster_dir" "$publish_dir"
  python3 "$VALIDATION_ROOT/scripts/publish_utility_cluster.py" \
    --project-root "$PROJECT_ROOT" --validation-root "$VALIDATION_ROOT" \
    --source-root "$SOURCE_ROOT" --exporter-root "$EXPORTER_ROOT" \
    --importer-root "$IMPORTER_ROOT" --work "$VALIDATION_PHASE_WORK" \
    --config "$cert_dir/nondecreasing_cluster_config.json" \
    --freeze-log "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    --lean-axioms "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    --assumptions "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    --baseline "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" \
    --snapshot-id "$VALIDATION_SNAPSHOT_ID" \
    --prepare-manifest "$VALIDATION_PREPARED/prepare_manifest.json" \
    --prepare-evidence "$VALIDATION_PREPARE_EVIDENCE" \
    --output "$cluster_dir/nondecreasing.json" \
    > "$VALIDATION_RUN_LOG/publication.log"

  cp "$VALIDATION_PHASE_WORK/imported/"{Nondecreasing.out,ImportedNondecreasing.v,ImportedNondecreasing.vo} \
    "$publish_dir/"
  local module
  for module in NondecreasingBaseAdapter NondecreasingCorrespondence \
      NondecreasingSimpleCertificate NondecreasingTypeAudit \
      NondecreasingAssumptionAudit; do
    cp "$VALIDATION_PHASE_WORK/certificates/$module.vo" \
      "$publish_dir/$module.vo"
  done

  python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$VALIDATION_PHASE_WORK" \
    "$cluster_dir/nondecreasing.json" "$pipeline_dir/div_mod_module_status.json" \
    "$pipeline_dir/nondecreasing_module_manifest.json" \
    "$pipeline_dir/nondecreasing_module_status.json" <<'PY2'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, cluster_path, previous_path, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
cluster = json.loads(cluster_path.read_text())
previous = json.loads(previous_path.read_text())
assert cluster["file_status"] == "ACCEPTED_V06_FILE"
assert len(cluster["declarations"]) == 33
assert all(r["acceptance"] == "ACCEPTED_V06_TRANSLATION" for r in cluster["declarations"])
statuses = [r["semantic_status"] for r in cluster["declarations"]]
assert statuses.count("CERTIFIED") == 1
assert statuses.count("CERTIFIED_WITH_PROP_SPROP_FOUNDATION") == 32
manifest = {
  "slice": "TRANSLATION_ORDER_UTIL_NONDECREASING",
  "generated_at": datetime.now().astimezone().isoformat(),
  "source_file": "util/nondecreasing.v",
  "source_commit": subprocess.check_output(
      ["git", "-C", str(source), "rev-parse", "HEAD"], text=True
  ).strip(),
  "source_file_sha256": sha(source / "util/nondecreasing.v"),
  "production_file": "Prosa/Util/Nondecreasing.lean",
  "production_source_sha256": sha(project / "Prosa/Util/Nondecreasing.lean"),
  "production_olean_sha256": sha(work / "olean/Prosa/Util/Nondecreasing.olean"),
  "export_sha256": sha(work / "imported/Nondecreasing.out"),
  "import_sha256": sha(work / "imported/ImportedNondecreasing.vo"),
  "adapter_source_sha256": sha(project / "Validation/certificates/common/NondecreasingBaseAdapter.v"),
  "adapter_vo_sha256": sha(work / "certificates/NondecreasingBaseAdapter.vo"),
  "bridge_source_sha256": sha(project / "Validation/certificates/common/NondecreasingCorrespondence.v"),
  "bridge_vo_sha256": sha(work / "certificates/NondecreasingCorrespondence.vo"),
  "certificate_source_sha256": sha(project / "Validation/certificates/utility_foundation/NondecreasingSimpleCertificate.v"),
  "certificate_vo_sha256": sha(work / "certificates/NondecreasingSimpleCertificate.vo"),
  "type_audit_vo_sha256": sha(work / "certificates/NondecreasingTypeAudit.vo"),
  "assumption_audit_vo_sha256": sha(work / "certificates/NondecreasingAssumptionAudit.vo"),
  "source_acquisition_metadata_sha256": sha(work / "source/nondecreasing_source_extraction.json"),
  "cluster_evidence_sha256": sha(cluster_path),
  "snapshot_id": cluster["snapshot_id"],
  "declarations": cluster["declarations"],
  "acceptance": "ACCEPTED_V06_FILE"
}
manifest_out.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
status = {
  "slice": "TRANSLATION_ORDER_UTIL_NONDECREASING",
  "per_file": {
    "util/nondecreasing.v": {
      "public_declarations": 33,
      "translated": 33,
      "proof_clean": 33,
      "certified": 33,
      "certified_without_prop_sprop_foundation": 1,
      "certified_with_prop_sprop_foundation": 32,
      "status": "ACCEPTED_V06_FILE"
    }
  },
  "coverage": {
    "accepted_files": previous["coverage"]["accepted_files"] + 1,
    "authoritative_files": 357,
    "accepted_declarations": previous["coverage"]["accepted_declarations"] + 33,
    "authoritative_declarations": 2439,
    "translated_but_not_certified": 0,
    "deferred_external_boundary": 239
  },
  "previous_status_sha256": sha(previous_path),
  "snapshot_id": cluster["snapshot_id"],
  "status": "PASS"
}
assert status["coverage"]["accepted_files"] == 20
assert status["coverage"]["accepted_declarations"] == 204
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY2
  (cd "$REPO_ROOT" && git diff --check)
  VALIDATION_STAGE_OUTPUTS=(
    "cluster_evidence=$cluster_dir/nondecreasing.json"
    "module_manifest=$pipeline_dir/nondecreasing_module_manifest.json"
    "module_status=$pipeline_dir/nondecreasing_module_status.json"
    "published_import=$publish_dir/ImportedNondecreasing.vo"
    "published_certificate=$publish_dir/NondecreasingSimpleCertificate.vo"
  )
}
