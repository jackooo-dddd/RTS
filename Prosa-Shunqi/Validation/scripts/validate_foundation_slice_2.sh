#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/foundation_slice_2"
canonical_import_dir="$VALIDATION_ROOT/imported/foundation_slice_2"
certificate_src_dir="$VALIDATION_ROOT/certificates/foundation_slice_2"
foundation_src_dir="$VALIDATION_ROOT/certificates/common"
fixture_dir="$VALIDATION_ROOT/fixtures/foundation_slice_2"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
mkdir -p "$log_dir" "$canonical_import_dir" "$pipeline_dir"

work=$(validation_fresh_workdir foundation_slice_2)
mkdir -p "$work/olean/Prosa/Util" "$work/source/util" "$work/imported" \
  "$work/certificates" "$work/artifacts"
validation_prepare_lean_path "$work"

production_files=(Notation Tactics Rel Seqset Subadditivity Supremum)
source_files=(notation tactics rel seqset subadditivity supremum)
source_hashes=(
  bcf52e6ffd31ceca50e479567147014b7ed1fc941cbf38ceba74917962a8b17d
  b55a2ee4f5efbd6e8593b0c95d6ae42414517a4f2cc0f4ccf90488371c2a7eff
  6479aed5a7b8254defac344fa85886446b2095fd848184196dadfa9f5a90779b
  85f90ee3725f452c81cffd963050bca3bcdc2357cd49cca8f6abb39a0b9ab7c2
  6ddce0f7553d2a09b606ef71e1ea108ce31bbc3c082da2625804cc2824eda8f2
  f62d8c1221ea790940762d7d870d3a8ae976fc83838c1cf007e6c5fa3651eac4
)

# Additional textual checks supplement, but never replace, kernel and
# Print Assumptions/#print axioms audits.
for stem in "${production_files[@]}"; do
  if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/$stem.lean"; then
    echo "forbidden production proof escape in $stem" >&2
    exit 1
  fi
done
if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$certificate_src_dir" --glob '*.v'; then
  echo "forbidden Slice 2 certificate proof escape" >&2
  exit 1
fi
# The shared foundation has one exact, previously approved trust boundary.
foundation_axioms=$(rg -n '^Axiom ' "$foundation_src_dir/PropSPropFoundation.v" || true)
if [[ "$foundation_axioms" != *"Axiom interpret_strict"* ]] || \
   [[ $(printf '%s\n' "$foundation_axioms" | sed '/^$/d' | wc -l | tr -d ' ') != 1 ]]; then
  echo "Prop/SProp foundation axiom boundary changed" >&2
  exit 1
fi
if rg -n '\b(Admitted|admit)\b|\bsorry\b' "$foundation_src_dir/PropSPropFoundation.v"; then
  echo "forbidden proof escape in Prop/SProp foundation" >&2
  exit 1
fi

# Each production module is rebuilt into a unique directory; no project .olean
# can satisfy an import because this fresh directory is first on LEAN_PATH.
for stem in "${production_files[@]}"; do
  validation_compile_lean_module "$work" "Prosa/Util/$stem" \
    > "$log_dir/fresh_${stem}.log" 2>&1
done
lean -DautoImplicit=false "$fixture_dir/LeanFreezeAudit.lean" \
  > "$log_dir/lean_freeze_audit.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/ProductionDeclarationAudit.lean" \
  > "$log_dir/production_declaration_audit.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/production_axiom_config.json" \
  --log "$log_dir/production_declaration_audit.log" \
  --output "$log_dir/production_axiom_summary.json" \
  > "$log_dir/production_axiom_classifier.log"

# Exact declaration lists. Selected theorem proof bodies are deliberately not
# exported; their types still come from this freshly compiled environment.
targets=(
  'Prosa.Util.Notation.constant'
  'Prosa.Util.Tactics.neqP Prosa.Util.Tactics.modusponens'
  'Prosa.Util.Rel.monotone Prosa.Util.Rel.total_over_list Prosa.Util.Rel.antisymmetric_over_list'
  'Prosa.Util.Seqset.set Prosa.Util.Seqset.set_of Prosa.Util.Seqset.set_uniq'
  'Prosa.Util.Subadditivity.subadditive_at Prosa.Util.Subadditivity.subadditive_until Prosa.Util.Subadditivity.subadditive Prosa.Util.Subadditivity.subadditive_standard Prosa.Util.Subadditivity.subadditive_standard_equivalence Prosa.Util.Subadditivity.subadditive_leq_mul'
  'Prosa.Util.Supremum.choose_superior Prosa.Util.Supremum.supremum Prosa.Util.Supremum.supremum_unfold Prosa.Util.Supremum.supremum_exists Prosa.Util.Supremum.supremum_none Prosa.Util.Supremum.supremum_in Prosa.Util.Supremum.supremum_spec'
)
statement_only=(
  ''
  $'Prosa.Util.Tactics.neqP\nProsa.Util.Tactics.modusponens'
  ''
  'Prosa.Util.Seqset.set_uniq'
  $'Prosa.Util.Subadditivity.subadditive_standard_equivalence\nProsa.Util.Subadditivity.subadditive_leq_mul'
  $'Prosa.Util.Supremum.supremum_unfold\nProsa.Util.Supremum.supremum_exists\nProsa.Util.Supremum.supremum_none\nProsa.Util.Supremum.supremum_in\nProsa.Util.Supremum.supremum_spec'
)

export LEAN4EXPORT_BODY_THEOREMS=
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
for i in "${!production_files[@]}"; do
  stem=${production_files[$i]}
  export LEAN4EXPORT_STATEMENT_ONLY="${statement_only[$i]}"
  # shellcheck disable=SC2086
  "$EXPORTER_ROOT/.lake/build/bin/lean4export" "Prosa.Util.$stem" -- ${targets[$i]} \
    > "$work/imported/$stem.out" 2> "$log_dir/export_${stem}.log"
done

# Acquire each official source byte-for-byte and verify before applying two
# isolated Rocq-9.3 syntax/tactic compatibility patches to validation copies.
for i in "${!source_files[@]}"; do
  src=${source_files[$i]}
  cp "$SOURCE_ROOT/util/$src.v" "$work/source/util/$src.v"
  actual_source_hash=$(validation_sha256 "$work/source/util/$src.v")
  if [[ "$actual_source_hash" != "${source_hashes[$i]}" ]]; then
    echo "official source hash mismatch for util/$src.v: $actual_source_hash" >&2
    exit 1
  fi
done
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch") \
  > "$log_dir/source_patch_tactics.log" 2>&1
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-seqset.patch") \
  > "$log_dir/source_patch_seqset.log" 2>&1
for src in "${source_files[@]}"; do
  (
    cd "$work/source"
    opam exec --switch="$ROCQ_SWITCH" -- rocq c -R "$work/source" prosa "util/$src.v"
  ) > "$log_dir/official_${src}_compile.log" 2>&1
done

# Import each fresh artifact and compile the source fidelity/type audit.
for stem in "${production_files[@]}"; do
  cp "$canonical_import_dir/Imported$stem.v" "$work/imported/"
done
cp "$foundation_src_dir/PropSPropFoundation.v" "$work/certificates/"
cp "$certificate_src_dir"/*.v "$work/certificates/"
ulimit -s 65520
for stem in "${production_files[@]}"; do
  (cd "$work/imported" && validation_rocq_compile "$work" "Imported$stem.v") \
    > "$log_dir/import_${stem}.log" 2>&1
done
(cd "$work/certificates" && validation_rocq_compile "$work" SourceTypeAudit.v) \
  > "$log_dir/source_type_audit.log" 2>&1
(cd "$work/certificates" && validation_rocq_compile "$work" PropSPropFoundation.v) \
  > "$log_dir/prop_sprop_foundation.log" 2>&1
for cert in NotationCertificate TacticsCertificate RelCertificate SupremumCertificate; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$cert.v") \
    > "$log_dir/certificate_${cert}.log" 2>&1
done
(cd "$work/certificates" && validation_rocq_compile "$work" AssumptionAudit.v) \
  > "$log_dir/assumptions.log" 2>&1
python3 "$script_dir/audit_assumptions.py" \
  --config "$certificate_src_dir/assumption_config.json" \
  --log "$log_dir/assumptions.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"

# Publish only after every preceding fail-closed step succeeded.
for stem in "${production_files[@]}"; do
  cp "$work/imported/$stem.out" "$canonical_import_dir/$stem.out"
  cp "$work/imported/Imported$stem.vo" "$canonical_import_dir/Imported$stem.vo"
done
for artifact in PropSPropFoundation NotationCertificate TacticsCertificate \
  RelCertificate SupremumCertificate SourceTypeAudit AssumptionAudit; do
  cp "$work/certificates/$artifact.vo" "$canonical_import_dir/$artifact.vo"
done

export FS2_WORK="$work" FS2_PROJECT_ROOT="$PROJECT_ROOT" \
  FS2_VALIDATION_ROOT="$VALIDATION_ROOT" FS2_SOURCE_ROOT="$SOURCE_ROOT" \
  FS2_EXPORTER_ROOT="$EXPORTER_ROOT" FS2_IMPORTER_ROOT="$IMPORTER_ROOT" \
  FS2_ROCQ_SWITCH="$ROCQ_SWITCH"
python3 - <<'PY' > "$log_dir/runtime_provenance.json"
import hashlib, json, os, pathlib, subprocess

def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
def git(path, *args):
    return subprocess.check_output(["git", "-C", path, *args], text=True).strip()

w = pathlib.Path(os.environ["FS2_WORK"])
p = pathlib.Path(os.environ["FS2_PROJECT_ROOT"])
v = pathlib.Path(os.environ["FS2_VALIDATION_ROOT"])
source = pathlib.Path(os.environ["FS2_SOURCE_ROOT"])
files = {}
for lower, stem in zip(
    ["notation", "tactics", "rel", "seqset", "subadditivity", "supremum"],
    ["Notation", "Tactics", "Rel", "Seqset", "Subadditivity", "Supremum"]):
    files[f"util/{lower}.v"] = {
        "source_sha256": sha(source / f"util/{lower}.v"),
        "source_validation_copy_sha256": sha(w / f"source/util/{lower}.v"),
        "official_source_vo_sha256": sha(w / f"source/util/{lower}.vo"),
        "lean_source_sha256": sha(p / f"Prosa/Util/{stem}.lean"),
        "fresh_olean_sha256": sha(w / f"olean/Prosa/Util/{stem}.olean"),
        "export_sha256": sha(w / f"imported/{stem}.out"),
        "imported_vo_sha256": sha(w / f"imported/Imported{stem}.vo"),
    }
certs = {}
for path in sorted((v / "certificates/foundation_slice_2").glob("*.v")):
    certs[path.stem] = sha(path)
certs.update({
    "constant_value_certificate": sha(v / "certificates/foundation_slice_2/NotationCertificate.v"),
    "modusponens_statement_certificate": sha(v / "certificates/foundation_slice_2/TacticsCertificate.v"),
    "monotone_correspondence_certificate": sha(v / "certificates/foundation_slice_2/RelCertificate.v"),
    "choose_superior_correspondence_certificate": sha(v / "certificates/foundation_slice_2/SupremumCertificate.v"),
    "supremum_correspondence_certificate": sha(v / "certificates/foundation_slice_2/SupremumCertificate.v"),
})
result = {
    "fresh_work_directory": str(w),
    "fresh_build": True,
    "source_commit": git(source, "rev-parse", "HEAD"),
    "source_tree": git(source, "rev-parse", "HEAD^{tree}"),
    "toolchain": {
        "lean": subprocess.check_output(["lean", "--version"], text=True).splitlines()[0],
        "mathlib_commit": git(p / ".lake/packages/mathlib", "rev-parse", "HEAD"),
        "rocq": subprocess.check_output([
            "opam", "exec", "--switch=" + os.environ["FS2_ROCQ_SWITCH"],
            "--", "rocq", "--version"], text=True).splitlines()[0],
    },
    "tooling_manifest_sha256": sha(v / "tooling/tooling_manifest.json"),
    "tooling": {
        "lean4export_base_commit": git(os.environ["FS2_EXPORTER_ROOT"], "rev-parse", "HEAD"),
        "lean4export_binary_sha256": sha(pathlib.Path(os.environ["FS2_EXPORTER_ROOT"]) / ".lake/build/bin/lean4export"),
        "rocq_lean_import_base_commit": git(os.environ["FS2_IMPORTER_ROOT"], "rev-parse", "HEAD"),
        "rocq_lean_import_plugin_sha256": sha(pathlib.Path(os.environ["FS2_IMPORTER_ROOT"]) / "src/lean_import.cmxs"),
        "rocq_lean_import_foundation_sha256": sha(pathlib.Path(os.environ["FS2_IMPORTER_ROOT"]) / "src/Lean.vo"),
    },
    "source_compatibility_patches": {
        "util/tactics.v": sha(v / "patches/prosa-v06-rocq93-util-tactics.patch"),
        "util/seqset.v": sha(v / "patches/prosa-v06-rocq93-util-seqset.patch"),
    },
    "files": files,
    "certificates": certs,
}
print(json.dumps(result, indent=2))
PY

python3 "$script_dir/generate_foundation_slice_2_results.py" \
  --project-root "$PROJECT_ROOT" --validation-root "$VALIDATION_ROOT" \
  --work "$work" --runtime "$log_dir/runtime_provenance.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --freeze-log "$log_dir/lean_freeze_audit.log"

echo "FOUNDATION_SLICE_2_STATUS = PARTIAL"
echo "fresh work directory: $work"
echo "accepted declarations: 5 / 22"
echo "accepted files: 1 / 6"
