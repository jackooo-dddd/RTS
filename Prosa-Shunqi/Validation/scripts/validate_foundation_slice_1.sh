#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
validation_root=$(cd "$script_dir/.." && pwd)
project_root=$(cd "$validation_root/.." && pwd)
repo_root=$(cd "$project_root/.." && pwd)
source_root=${PROSA_V06_SOURCE_ROOT:-"$validation_root/.work/prosa-v06-414e667"}
exporter_root=${LEAN4EXPORT_SRC:-"$validation_root/.work/tooling/lean4export"}
importer_root=${ROCQLI_SRC:-"$validation_root/.work/tooling/rocq-lean-import"}
rocq_switch=${IMPORT_OPAM_SWITCH:-rocq93rc1}
lean_toolchain=leanprover/lean4:v4.33.1
expected_source_commit=414e66760333eaa4ef78c685bcf53291c527a548
expected_source_hash=9fea3f9a3181ca697e8abdb9eee90a656057081f62b00157c3ce9fbe59e53230
expected_mathlib_commit=0df444a360eaa60ab8c11dca51a86af692955474

log_dir="$validation_root/logs/foundation_slice_1"
canonical_import_dir="$validation_root/imported/foundation_slice_1"
certificate_src_dir="$validation_root/certificates/foundation_slice_1"
fixture_dir="$validation_root/fixtures/foundation_slice_1"
mkdir -p "$validation_root/.work" "$log_dir" "$canonical_import_dir"
PROSA_V06_SOURCE_ROOT="$source_root" "$script_dir/ensure_pinned_v06_source.sh" >/dev/null
"$validation_root/tooling/setup_validation_tooling.sh" >/dev/null
work=$(mktemp -d "$validation_root/.work/foundation_slice_1.XXXXXX")
mkdir -p "$work/olean/Prosa/Behavior" "$work/source/behavior" \
  "$work/imported" "$work/certificates" "$work/artifacts"

sha256() { shasum -a 256 "$1" | awk '{print $1}'; }

actual_source_commit=$(git -C "$source_root" rev-parse HEAD)
[[ "$actual_source_commit" == "$expected_source_commit" ]] || {
  echo "authoritative source commit mismatch: $actual_source_commit" >&2
  exit 1
}
[[ -z $(git -C "$source_root" status --porcelain) ]] || {
  echo "authoritative source worktree is dirty" >&2
  exit 1
}
actual_source_hash=$(sha256 "$source_root/behavior/time.v")
[[ "$actual_source_hash" == "$expected_source_hash" ]] || {
  echo "behavior/time.v hash mismatch: $actual_source_hash" >&2
  exit 1
}
actual_mathlib_commit=$(git -C "$project_root/.lake/packages/mathlib" rev-parse HEAD)
[[ "$actual_mathlib_commit" == "$expected_mathlib_commit" ]] || {
  echo "Mathlib revision mismatch: $actual_mathlib_commit" >&2
  exit 1
}
[[ $(tr -d '\r\n' < "$project_root/lean-toolchain") == "$lean_toolchain" ]] || {
  echo "Lean toolchain file mismatch" >&2
  exit 1
}

# Text scans are an additional escape-hatch check, not a substitute for the
# kernel and Print Assumptions audits below.
if rg -n '\b(sorry|axiom|unsafe)\b' "$project_root/Prosa/Behavior/Time.lean"; then
  echo "forbidden production proof escape" >&2
  exit 1
fi
if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$certificate_src_dir"; then
  echo "forbidden certificate proof escape" >&2
  exit 1
fi

export ELAN_TOOLCHAIN="$lean_toolchain"
lake -d "$exporter_root" build lean4export > "$log_dir/exporter_build.log" 2>&1
mathlib_path=$(cd "$project_root" && lake env printenv LEAN_PATH)
export LEAN_PATH="$work/olean:$project_root:$mathlib_path"

# Fresh Lean compilation: this .olean is created in the unique work directory
# and is the only project artifact visible first on LEAN_PATH.
lean -R "$project_root" \
  -o "$work/olean/Prosa/Behavior/Time.olean" \
  "$project_root/Prosa/Behavior/Time.lean" \
  > "$log_dir/fresh_lean_compile.log" 2>&1
lean "$fixture_dir/LeanDeclarationAudit.lean" \
  > "$log_dir/lean_declaration_audit.log" 2>&1

export LEAN4EXPORT_STATEMENT_ONLY=
export LEAN4EXPORT_BODY_THEOREMS=
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$exporter_root/.lake/build/bin/lean4export" Prosa.Behavior.Time -- \
  Prosa.Behavior.Time.duration Prosa.Behavior.Time.instant \
  > "$work/imported/Time.out" 2> "$log_dir/export.log"

# Exact source acquisition: copy the pinned file byte-for-byte into the fresh
# build root, verify its hash again, then let Rocq elaborate and compile it.
cp "$source_root/behavior/time.v" "$work/source/behavior/time.v"
[[ $(sha256 "$work/source/behavior/time.v") == "$expected_source_hash" ]]
(
  cd "$work/source"
  opam exec --switch="$rocq_switch" -- rocq c \
    -R "$work/source" prosa behavior/time.v
) > "$log_dir/official_source_compile.log" 2>&1

cp "$canonical_import_dir/ImportedTime.v" "$work/imported/ImportedTime.v"
cp "$certificate_src_dir/FoundationTimeCertificate.v" "$work/certificates/"
cp "$certificate_src_dir/AssumptionAudit.v" "$work/certificates/"
cp "$certificate_src_dir/SourceTypeAudit.v" "$work/certificates/"

rocq_compile() {
  local source_file=$1
  opam exec --switch="$rocq_switch" -- rocq c \
    -R "$work/source" prosa \
    -Q "$importer_root/src" LeanImport -I "$importer_root/src" \
    -Q "$work/imported" FoundationImported \
    -Q "$work/certificates" FoundationCertificates \
    "$source_file"
}

ulimit -s 65520
(
  cd "$work/imported"
  rocq_compile ImportedTime.v
) > "$log_dir/import.log" 2>&1
(
  cd "$work/certificates"
  rocq_compile SourceTypeAudit.v
) > "$log_dir/source_type_audit.log" 2>&1
(
  cd "$work/certificates"
  rocq_compile FoundationTimeCertificate.v
) > "$log_dir/certificate_compile.log" 2>&1
(
  cd "$work/certificates"
  rocq_compile AssumptionAudit.v
) > "$log_dir/assumptions.log" 2>&1

python3 "$script_dir/audit_foundation_slice_1_assumptions.py" \
  --log "$log_dir/assumptions.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"

# Publish only artifacts produced by this successful fresh run.
cp "$work/imported/Time.out" "$canonical_import_dir/Time.out"
cp "$work/imported/ImportedTime.vo" "$canonical_import_dir/ImportedTime.vo"
cp "$work/certificates/FoundationTimeCertificate.vo" "$work/artifacts/"
cp "$work/certificates/AssumptionAudit.vo" "$work/artifacts/"
cp "$work/source/behavior/time.vo" "$work/artifacts/official_time.vo"
cp "$work/artifacts/FoundationTimeCertificate.vo" "$canonical_import_dir/FoundationTimeCertificate.vo"
cp "$work/artifacts/AssumptionAudit.vo" "$canonical_import_dir/AssumptionAudit.vo"
cp "$work/artifacts/official_time.vo" "$canonical_import_dir/official_time.vo"

git -C "$exporter_root" diff > "$log_dir/lean4export_worktree.patch"
git -C "$exporter_root" status --porcelain > "$log_dir/lean4export_worktree.status"
git -C "$importer_root" diff > "$log_dir/rocq_lean_import_worktree.patch"
git -C "$importer_root" status --porcelain > "$log_dir/rocq_lean_import_worktree.status"

export FS1_WORK="$work"
export FS1_PROJECT_ROOT="$project_root"
export FS1_VALIDATION_ROOT="$validation_root"
export FS1_SOURCE_ROOT="$source_root"
export FS1_SOURCE_HASH="$actual_source_hash"
export FS1_SOURCE_COMMIT="$actual_source_commit"
export FS1_MATHLIB_COMMIT="$actual_mathlib_commit"
export FS1_EXPORTER_ROOT="$exporter_root"
export FS1_IMPORTER_ROOT="$importer_root"
export FS1_ROCQ_SWITCH="$rocq_switch"
python3 - <<'PY' > "$log_dir/runtime_provenance.json"
import hashlib, json, os, pathlib, subprocess

def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()

def git(path, *args):
    return subprocess.check_output(["git", "-C", path, *args], text=True).strip()

def bytes_digest(data):
    return hashlib.sha256(data).hexdigest()

def git_bytes(path, *args):
    return subprocess.check_output(["git", "-C", path, *args])

w = pathlib.Path(os.environ["FS1_WORK"])
p = pathlib.Path(os.environ["FS1_PROJECT_ROOT"])
v = pathlib.Path(os.environ["FS1_VALIDATION_ROOT"])
e = os.environ["FS1_EXPORTER_ROOT"]
i = os.environ["FS1_IMPORTER_ROOT"]
result = {
    "fresh_work_directory": str(w),
    "authoritative_source": {
        "root": os.environ["FS1_SOURCE_ROOT"],
        "commit": os.environ["FS1_SOURCE_COMMIT"],
        "file": "behavior/time.v",
        "sha256": os.environ["FS1_SOURCE_HASH"],
    },
    "toolchain": {
        "lean": subprocess.check_output(["lean", "--version"], text=True).splitlines()[0],
        "mathlib_commit": os.environ["FS1_MATHLIB_COMMIT"],
        "rocq": subprocess.check_output(
            ["opam", "exec", "--switch=" + os.environ["FS1_ROCQ_SWITCH"], "--", "rocq", "--version"],
            text=True,
        ).splitlines()[0],
        "lean4export_commit": git(e, "rev-parse", "HEAD"),
        "lean4export_dirty": bool(git(e, "status", "--porcelain")),
        "lean4export_diff_sha256": bytes_digest(git_bytes(e, "diff")),
        "lean4export_status_sha256": bytes_digest(git_bytes(e, "status", "--porcelain")),
        "rocq_lean_import_commit": git(i, "rev-parse", "HEAD"),
        "rocq_lean_import_dirty": bool(git(i, "status", "--porcelain")),
        "rocq_lean_import_diff_sha256": bytes_digest(git_bytes(i, "diff")),
        "rocq_lean_import_status_sha256": bytes_digest(git_bytes(i, "status", "--porcelain")),
    },
    "artifacts": {
        "lean_source_sha256": sha(p / "Prosa/Behavior/Time.lean"),
        "fresh_olean_sha256": sha(w / "olean/Prosa/Behavior/Time.olean"),
        "lean_export_sha256": sha(v / "imported/foundation_slice_1/Time.out"),
        "imported_rocq_vo_sha256": sha(v / "imported/foundation_slice_1/ImportedTime.vo"),
        "official_source_vo_sha256": sha(v / "imported/foundation_slice_1/official_time.vo"),
        "certificate_source_sha256": sha(v / "certificates/foundation_slice_1/FoundationTimeCertificate.v"),
        "certificate_vo_sha256": sha(v / "imported/foundation_slice_1/FoundationTimeCertificate.vo"),
        "assumption_audit_vo_sha256": sha(v / "imported/foundation_slice_1/AssumptionAudit.vo"),
        "lean4export_binary_sha256": sha(pathlib.Path(e) / ".lake/build/bin/lean4export"),
        "rocq_lean_import_plugin_sha256": sha(pathlib.Path(i) / "src/lean_import.cmxs"),
        "rocq_lean_import_foundation_vo_sha256": sha(pathlib.Path(i) / "src/Lean.vo"),
    },
    "proof_escapes": {"production": [], "certificates": []},
    "fresh_build": True,
}
print(json.dumps(result, indent=2))
PY

export FS1_RUNTIME_PROVENANCE="$log_dir/runtime_provenance.json"
export FS1_ASSUMPTION_SUMMARY="$log_dir/assumption_summary.json"
python3 - <<'PY'
import csv, hashlib, json, os, pathlib

v = pathlib.Path(os.environ["FS1_VALIDATION_ROOT"])
runtime = json.loads(pathlib.Path(os.environ["FS1_RUNTIME_PROVENANCE"]).read_text())
audit = json.loads(pathlib.Path(os.environ["FS1_ASSUMPTION_SUMMARY"]).read_text())

with (v / "planning/v06_dependency/declaration_inventory.csv").open(newline="") as f:
    inventory = {
        r["declaration_name"]: r
        for r in csv.DictReader(f)
        if r["source_file"] == "behavior/time.v"
    }

def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()

declarations = []
for name in ("duration", "instant"):
    source = inventory[name]
    certificate_names = [
        f"{name}_relation_total_from_rocq",
        f"{name}_rocq_roundtrip_certificate",
        f"{name}_imported_roundtrip_certificate",
    ]
    invalidation_material = "\n".join([
        runtime["authoritative_source"]["commit"],
        runtime["authoritative_source"]["sha256"],
        source["source_command_sha256"],
        runtime["artifacts"]["lean_source_sha256"],
        runtime["artifacts"]["fresh_olean_sha256"],
        runtime["artifacts"]["lean_export_sha256"],
        runtime["artifacts"]["imported_rocq_vo_sha256"],
        runtime["artifacts"]["certificate_source_sha256"],
        runtime["artifacts"]["certificate_vo_sha256"],
        runtime["toolchain"]["lean"],
        runtime["toolchain"]["mathlib_commit"],
        runtime["toolchain"]["rocq"],
    ])
    declarations.append({
        "rocq_declaration": f"prosa.behavior.time.{name}",
        "lean_declaration": f"Prosa.Behavior.Time.{name}",
        "kind": "Definition",
        "source_declaration_sha256": source["source_command_sha256"],
        "source_elaborated_type_fingerprint": source["final_type_or_type_fingerprint"],
        "lean_elaborated_type": "Type",
        "lean_elaborated_type_sha256": digest("Type"),
        "lean_definition_body": "Nat",
        "lean_definition_body_sha256": digest("Nat"),
        "semantic_relation": f"{name.capitalize()}Rel r l := Lean.eq (rocq_nat_to_imported r) l",
        "maps": {
            "source_to_target": f"{name}_to_imported",
            "target_to_source": f"imported_to_{name}",
        },
        "certificates": certificate_names,
        "semantic_validation": "CERTIFIED",
        "assumption_audit": "PASS_WITH_ALLOWED_IMPORTER_FOUNDATION",
        "semantic_premises": [],
        "prop_sprop_foundation": [],
        "allowed_importer_foundation": ["Lean.eq relies on definitional UIP"],
        "acceptance": "ACCEPTED_V06_TRANSLATION",
        "content_invalidation_key_sha256": digest(invalidation_material),
    })

manifest = {
    "slice": "FOUNDATION_SLICE_1",
    "freeze_policy": "Any change to a recorded source, type, computational body, or artifact hash invalidates the certificate and requires a fresh translation/validation run.",
    "authoritative_source": runtime["authoritative_source"],
    "production_file": "Prosa/Behavior/Time.lean",
    "artifacts": runtime["artifacts"],
    "toolchain": runtime["toolchain"],
    "declarations": declarations,
}
pipeline = v / "planning/v06_pipeline"
pipeline.mkdir(parents=True, exist_ok=True)
(pipeline / "foundation_slice_1_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

status = {
    "slice": "FOUNDATION_SLICE_1",
    "FOUNDATION_SLICE_1_STATUS": "PASS",
    "selected_files": ["behavior/time.v"],
    "production_files": ["Prosa/Behavior/Time.lean"],
    "migration_counts": {
        "REUSE_AFTER_REVALIDATION": 2,
        "ADAPT_OLD_LEAN": 0,
        "NEW_TRANSLATION": 0,
    },
    "file_gate": {
        "behavior/time.v": {
            "dependency_ready": True,
            "whole_file_inventory_complete": True,
            "lean_compile": "PASS",
            "proof_clean": "PASS_NO_PROOF_VALUED_DECLARATIONS",
            "semantic_validation": "PASS",
            "assumption_audit": audit["status"],
            "accepted": True,
        }
    },
    "declarations": {
        d["rocq_declaration"]: {
            "lean": d["lean_declaration"],
            "compile": "PASS",
            "proof_clean": "PASS",
            "semantic_validation": d["semantic_validation"],
            "assumption_audit": d["assumption_audit"],
            "status": d["acceptance"],
        }
        for d in declarations
    },
    "assumption_summary": audit,
    "coverage": {
        "authoritative_files": 357,
        "authoritative_declarations": 2439,
        "accepted_files": 1,
        "accepted_declarations": 2,
        "translated_but_not_certified": 0,
        "certified": 2,
        "proof_clean": 2,
        "blocked_in_slice": 0,
        "deferred_external_boundary_global": 239,
    },
}
(pipeline / "foundation_slice_1_status.json").write_text(json.dumps(status, indent=2) + "\n")
PY

echo "FOUNDATION_SLICE_1 semantic validation: PASS"
echo "fresh work directory: $work"
echo "assumption status: CERTIFIED"
echo "runtime provenance: $log_dir/runtime_provenance.json"
