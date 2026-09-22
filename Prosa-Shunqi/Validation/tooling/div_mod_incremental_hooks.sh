#!/usr/bin/env bash

VALIDATION_PREPARE_INPUTS=(
  "$VALIDATION_ROOT/tooling/div_mod_incremental_descriptor.json"
  "$VALIDATION_ROOT/tooling/div_mod_export_config.json"
  "$VALIDATION_ROOT/tooling/div_mod_incremental_hooks.sh"
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
  "$VALIDATION_ROOT/certificates/common/DivModCorrespondence.v"
  "$VALIDATION_ROOT/certificates/foundation_slice_2_closure/SubadditivityClosureCertificate.v"
  "$VALIDATION_ROOT/certificates/utility_foundation/DivModCertificate.v"
  "$VALIDATION_ROOT/certificates/utility_foundation/DivModTypeAudit.v"
  "$VALIDATION_ROOT/certificates/utility_foundation/DivModAssumptionAudit.v"
  "$VALIDATION_ROOT/certificates/utility_foundation/div_mod_assumption_config.json"
  "$VALIDATION_ROOT/certificates/utility_foundation/div_mod_cluster_config.json"
  "$VALIDATION_ROOT/imported/utility_foundation/ImportedNat.vo"
  "$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
)

validation_prepare_lean_build() {
  [[ $(validation_sha256 "$SOURCE_ROOT/util/div_mod.v") == \
    7705c2f251bd96daab96e891b145ea8ca839b269c6f67f1bc954ba0219883b32 ]]
  [[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/div_mod.v" for r in csv.DictReader(open(sys.argv[1]))))' \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 15 ]]
  jq -e '.coverage.accepted_files == 18 and
    .coverage.accepted_declarations == 156 and
    .coverage.translated_but_not_certified == 0' \
    "$VALIDATION_ROOT/planning/v06_pipeline/minmax_module_status.json" >/dev/null
  if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Div_mod.lean"; then
    echo "forbidden production proof escape" >&2
    return 1
  fi
  mkdir -p "$VALIDATION_PREPARED/olean/Prosa/Util" \
    "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order"
  local module
  for module in Tactics Nat Subadditivity Div_mod; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Util/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/DivModComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/DivModComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_interface.log" 2>&1
  lean -DautoImplicit=false "$VALIDATION_ROOT/fixtures/translation_order/LeanDivModAudit.lean" \
    > "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" 2>&1
  cp "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    "$VALIDATION_RUN_LOG/lean_freeze_and_axioms.log"
  python3 "$VALIDATION_ROOT/scripts/audit_lean_axioms.py" \
    --config "$VALIDATION_ROOT/fixtures/translation_order/div_mod_lean_axiom_config.json" \
    --log "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    --output "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    > "$VALIDATION_RUN_LOG/lean_axiom_classifier.log"
  jq -e '[.declarations[] | (.unexpected_axioms | length == 0)] | all' \
    "$VALIDATION_PREPARED/lean_axiom_summary.json" >/dev/null
  VALIDATION_STAGE_OUTPUTS=(
    "tactics_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Tactics.olean"
    "nat_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Nat.olean"
    "subadditivity_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Subadditivity.olean"
    "div_mod_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Div_mod.olean"
    "interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/DivModComputationInterface.olean"
    "lean_freeze=$VALIDATION_PREPARED/lean_freeze_and_axioms.log"
    "lean_axiom_summary=$VALIDATION_PREPARED/lean_axiom_summary.json"
  )
}

validation_prepare_source_acquisition() {
  mkdir -p "$VALIDATION_PREPARED/source/util"
  cp "$SOURCE_ROOT/util/tactics.v" "$VALIDATION_PREPARED/source/util/tactics.v"
  patch -s -d "$VALIDATION_PREPARED/source" -p1 \
    < "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch"
  cp "$SOURCE_ROOT/util/nat.v" "$VALIDATION_PREPARED/source/util/nat.v"
  cp "$SOURCE_ROOT/util/subadditivity.v" \
    "$VALIDATION_PREPARED/source/util/subadditivity.v"
  local module
  for module in tactics nat subadditivity; do
    (cd "$VALIDATION_PREPARED/source" && \
      opam exec --switch="$ROCQ_SWITCH" -- rocq c \
        -R "$VALIDATION_PREPARED/source" prosa \
        "util/${module}.v") \
      > "$VALIDATION_RUN_LOG/source_${module}.log" 2>&1
  done
  python3 "$VALIDATION_ROOT/scripts/extract_v06_semantic_source.py" \
    --source-root "$SOURCE_ROOT" --source-file util/div_mod.v \
    --module GeneratedDivModSource \
    --declarations 'eqdivn_leqmodn,ltdivn_dvdn,addn1_modn_commute,addmod_le_mod,divn_leq,div_floor,div_ceil,div_ceil0,div_ceil_gt0,div_ceil_monotone1,leq_div_ceil_add1,div_ceil_subadditive,div_ceil_multiple,div_floor_add_g,mod_elim' \
    --computational 'div_floor,div_ceil' \
    --elaborated-evidence \
      "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
    --qualified-prefix prosa.util.div_mod \
    --output "$VALIDATION_PREPARED/source/GeneratedDivModSource.v" \
    --metadata "$VALIDATION_PREPARED/source/div_mod_source_extraction.json" \
    > "$VALIDATION_RUN_LOG/source_extraction.log"
  jq -e '(.declarations | length) == 15 and
      .declarations.div_floor.acquisition_mode == "BODY_EXACT" and
      .declarations.div_ceil.acquisition_mode == "BODY_EXACT" and
      ([.declarations | to_entries[] |
        select(.key != "div_floor" and .key != "div_ceil") |
        .value.elaborated_type_evidence == "ELABORATED_ROCQ_CHECK"] | all)' \
    "$VALIDATION_PREPARED/source/div_mod_source_extraction.json" >/dev/null
  (cd "$VALIDATION_PREPARED/source" && \
    opam exec --switch="$ROCQ_SWITCH" -- rocq c \
      -R "$VALIDATION_PREPARED/source" prosa \
      GeneratedDivModSource.v) \
    > "$VALIDATION_RUN_LOG/generated_source_compile.log" 2>&1
  VALIDATION_STAGE_OUTPUTS=(
    "source_tactics=$VALIDATION_PREPARED/source/util/tactics.vo"
    "source_nat=$VALIDATION_PREPARED/source/util/nat.vo"
    "source_subadditivity=$VALIDATION_PREPARED/source/util/subadditivity.vo"
    "source_signature=$VALIDATION_PREPARED/source/GeneratedDivModSource.v"
    "source_signature_vo=$VALIDATION_PREPARED/source/GeneratedDivModSource.vo"
    "source_metadata=$VALIDATION_PREPARED/source/div_mod_source_extraction.json"
  )
}

validation_prepare_export() {
  "$VALIDATION_ROOT/scripts/export_actual_artifact.sh" \
    --config "$VALIDATION_ROOT/tooling/div_mod_export_config.json" \
    --output "$VALIDATION_PREPARED/imported/DivMod.out" \
    --log "$VALIDATION_RUN_LOG/export.log" \
    --metadata "$VALIDATION_PREPARED/imported/div_mod_export_metadata.json"
  VALIDATION_STAGE_OUTPUTS=(
    "export=$VALIDATION_PREPARED/imported/DivMod.out"
    "export_metadata=$VALIDATION_PREPARED/imported/div_mod_export_metadata.json"
  )
}

validation_prepare_rocq_import() {
  cp "$VALIDATION_ROOT/fixtures/translation_order/ImportedDivMod.v" \
    "$VALIDATION_PREPARED/imported/ImportedDivMod.v"
  (cd "$VALIDATION_PREPARED/imported" && \
    validation_rocq_compile "$VALIDATION_PREPARED" ImportedDivMod.v) \
    > "$VALIDATION_RUN_LOG/import.log" 2>&1
  VALIDATION_STAGE_OUTPUTS=(
    "import_source=$VALIDATION_PREPARED/imported/ImportedDivMod.v"
    "import_vo=$VALIDATION_PREPARED/imported/ImportedDivMod.vo"
  )
}

validation_check_setup() {
  cp -R "$VALIDATION_PREPARED/olean/." "$VALIDATION_PHASE_WORK/olean/"
  cp -R "$VALIDATION_PREPARED/source/." "$VALIDATION_PHASE_WORK/source/"
  cp -R "$VALIDATION_PREPARED/imported/." "$VALIDATION_PHASE_WORK/imported/"
  cp "$VALIDATION_ROOT/imported/utility_foundation/ImportedNat.vo" \
    "$VALIDATION_PHASE_WORK/imported/ImportedNat.vo"
  cp "$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo" \
    "$VALIDATION_PHASE_WORK/imported/ImportedSubadditivity.vo"
}

validation_check_certificate_compile() {
  local common_dir="$VALIDATION_ROOT/certificates/common"
  local cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
  mkdir -p "$VALIDATION_PHASE_WORK/certificates"
  cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,NatSubCorrespondence,DivModCorrespondence}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$VALIDATION_ROOT/certificates/foundation_slice_2_closure/SubadditivityClosureCertificate.v" \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$cert_dir/"{DivModCertificate,DivModTypeAudit,DivModAssumptionAudit}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  local path
  for path in \
    "$common_dir/DivModCorrespondence.v" \
    "$cert_dir/DivModCertificate.v" \
    "$cert_dir/DivModTypeAudit.v" \
    "$cert_dir/DivModAssumptionAudit.v"; do
    if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
      echo "forbidden certificate proof escape in $path" >&2
      return 1
    fi
  done
  local module
  for module in PropSPropFoundation LogicalRelation \
      SubadditivityNatCorrespondence NatSubCorrespondence \
      SubadditivityClosureCertificate DivModCorrespondence \
      DivModCertificate DivModTypeAudit DivModAssumptionAudit; do
    validation_rocq_compile "$VALIDATION_PHASE_WORK" \
      "$VALIDATION_PHASE_WORK/certificates/$module.v" \
      > "$VALIDATION_RUN_LOG/rocq_${module}.log" 2>&1
  done
  cp "$VALIDATION_RUN_LOG/rocq_DivModAssumptionAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  VALIDATION_STAGE_OUTPUTS=(
    "bridge_vo=$VALIDATION_PHASE_WORK/certificates/DivModCorrespondence.vo"
    "certificate_vo=$VALIDATION_PHASE_WORK/certificates/DivModCertificate.vo"
    "type_audit_vo=$VALIDATION_PHASE_WORK/certificates/DivModTypeAudit.vo"
    "assumption_audit_vo=$VALIDATION_PHASE_WORK/certificates/DivModAssumptionAudit.vo"
    "assumption_log=$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  )
}

validation_check_assumption_audit() {
  local cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/div_mod_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/assumption_classifier.log"
  jq -e '[.certificates[] |
      .status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" and
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all' \
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
  local publish_dir="$VALIDATION_ROOT/imported/translation_order/div_mod"
  local pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
  mkdir -p "$cluster_dir" "$publish_dir"
  python3 "$VALIDATION_ROOT/scripts/publish_utility_cluster.py" \
    --project-root "$PROJECT_ROOT" --validation-root "$VALIDATION_ROOT" \
    --source-root "$SOURCE_ROOT" --exporter-root "$EXPORTER_ROOT" \
    --importer-root "$IMPORTER_ROOT" --work "$VALIDATION_PHASE_WORK" \
    --config "$cert_dir/div_mod_cluster_config.json" \
    --freeze-log "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    --lean-axioms "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    --assumptions "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    --baseline "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" \
    --snapshot-id "$VALIDATION_SNAPSHOT_ID" \
    --prepare-manifest "$VALIDATION_PREPARED/prepare_manifest.json" \
    --prepare-evidence "$VALIDATION_PREPARE_EVIDENCE" \
    --output "$cluster_dir/div_mod.json" \
    > "$VALIDATION_RUN_LOG/publication.log"

  cp "$VALIDATION_PHASE_WORK/imported/"{DivMod.out,ImportedDivMod.v,ImportedDivMod.vo} \
    "$publish_dir/"
  local module
  for module in DivModCorrespondence DivModCertificate DivModTypeAudit \
      DivModAssumptionAudit; do
    cp "$VALIDATION_PHASE_WORK/certificates/$module.vo" \
      "$publish_dir/$module.vo"
  done

  python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$VALIDATION_PHASE_WORK" \
    "$cluster_dir/div_mod.json" "$pipeline_dir/minmax_module_status.json" \
    "$pipeline_dir/div_mod_module_manifest.json" \
    "$pipeline_dir/div_mod_module_status.json" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, cluster_path, previous_path, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
cluster = json.loads(cluster_path.read_text())
previous = json.loads(previous_path.read_text())
assert cluster["file_status"] == "ACCEPTED_V06_FILE"
assert len(cluster["declarations"]) == 15
assert all(r["acceptance"] == "ACCEPTED_V06_TRANSLATION" for r in cluster["declarations"])
assert all(r["semantic_status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" for r in cluster["declarations"])
manifest = {
  "slice": "TRANSLATION_ORDER_UTIL_DIV_MOD",
  "generated_at": datetime.now().astimezone().isoformat(),
  "source_file": "util/div_mod.v",
  "source_commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
  "source_file_sha256": sha(source / "util/div_mod.v"),
  "production_file": "Prosa/Util/Div_mod.lean",
  "production_source_sha256": sha(project / "Prosa/Util/Div_mod.lean"),
  "production_olean_sha256": sha(work / "olean/Prosa/Util/Div_mod.olean"),
  "export_sha256": sha(work / "imported/DivMod.out"),
  "import_sha256": sha(work / "imported/ImportedDivMod.vo"),
  "certificate_source_sha256": sha(project / "Validation/certificates/utility_foundation/DivModCertificate.v"),
  "certificate_vo_sha256": sha(work / "certificates/DivModCertificate.vo"),
  "type_audit_vo_sha256": sha(work / "certificates/DivModTypeAudit.vo"),
  "assumption_audit_vo_sha256": sha(work / "certificates/DivModAssumptionAudit.vo"),
  "source_acquisition_metadata_sha256": sha(work / "source/div_mod_source_extraction.json"),
  "cluster_evidence_sha256": sha(cluster_path),
  "snapshot_id": cluster["snapshot_id"],
  "declarations": cluster["declarations"],
  "acceptance": "ACCEPTED_V06_FILE"
}
manifest_out.write_text(json.dumps(manifest, indent=2) + "\n")
status = {
  "slice": "TRANSLATION_ORDER_UTIL_DIV_MOD",
  "per_file": {
    "util/div_mod.v": {
      "public_declarations": 15,
      "translated": 15,
      "proof_clean": 15,
      "certified": 15,
      "status": "ACCEPTED_V06_FILE"
    }
  },
  "coverage": {
    "accepted_files": previous["coverage"]["accepted_files"] + 1,
    "authoritative_files": 357,
    "accepted_declarations": previous["coverage"]["accepted_declarations"] + 15,
    "authoritative_declarations": 2439,
    "translated_but_not_certified": 0,
    "deferred_external_boundary": 239
  },
  "previous_status_sha256": sha(previous_path),
  "snapshot_id": cluster["snapshot_id"],
  "status": "PASS"
}
assert status["coverage"]["accepted_files"] == 19
assert status["coverage"]["accepted_declarations"] == 171
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY
  (cd "$REPO_ROOT" && git diff --check)
  VALIDATION_STAGE_OUTPUTS=(
    "cluster_evidence=$cluster_dir/div_mod.json"
    "module_manifest=$pipeline_dir/div_mod_module_manifest.json"
    "module_status=$pipeline_dir/div_mod_module_status.json"
    "published_import=$publish_dir/ImportedDivMod.vo"
    "published_certificate=$publish_dir/DivModCertificate.vo"
  )
}
