#!/usr/bin/env bash
set -euo pipefail

project_root=$(cd "$(dirname "$0")/../../.." && pwd)
mapping_dir="$project_root/Validation/planning/v06_mapping"
dependency_dir="$project_root/Validation/planning/v06_dependency"
history_repo="$project_root/Validation/.work/prosa_history_repo"
v04_root="$project_root/Validation/.work/prosa-v04-ee05f255"
v06_root="$project_root/Validation/.work/prosa-v06-414e667"
mathlib_dir=${MATHLIB_DIR:-/private/tmp/mathlib4-v4.33.1}
v04=ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7
v06=414e66760333eaa4ef78c685bcf53291c527a548
mathlib_commit=0df444a360eaa60ab8c11dca51a86af692955474

mkdir -p "$mapping_dir/logs"

if [[ ! -d "$history_repo/.git" ]]; then
  git clone --filter=blob:none --no-checkout \
    https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs.git "$history_repo"
fi
if [[ ! -e "$v04_root/.git" ]]; then
  git -C "$history_repo" worktree add --detach "$v04_root" "$v04"
fi
if [[ ! -e "$v06_root/.git" ]]; then
  git -C "$history_repo" worktree add --detach "$v06_root" "$v06"
fi
[[ "$(git -C "$v04_root" rev-parse HEAD)" == "$v04" ]]
[[ "$(git -C "$v06_root" rev-parse HEAD)" == "$v06" ]]
[[ "$(git -C "$mathlib_dir" rev-parse HEAD)" == "$mathlib_commit" ]]

repo_root=$(git -C "$project_root" rev-parse --show-toplevel)
production_tree_before=$(git -C "$repo_root" rev-parse HEAD:Prosa-fei/Prosa)

python3 "$mapping_dir/generate_mapping.py" \
  --repo-root "$project_root" \
  --v04-root "$v04_root" \
  --v06-root "$v06_root" \
  --dependency "$dependency_dir" \
  --output "$mapping_dir" \
  > "$mapping_dir/logs/generation.log"

export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
export LEAN_PATH="$(cd "$mathlib_dir" && lake env printenv LEAN_PATH)"
lean --version > "$mapping_dir/logs/lean_version.log"
lean "$mapping_dir/prototypes/RepresentationPrototype.lean" \
  > "$mapping_dir/logs/prototype_compile.log" 2>&1

python3 - "$mapping_dir" <<'PY'
import csv, json, sys
from pathlib import Path
p = Path(sys.argv[1])
s = json.loads((p / "mapping_summary.json").read_text())
assert all(s["integrity"].values()), s["integrity"]
with (p / "v06_migration_table.csv").open(newline="") as f:
    rows = list(csv.DictReader(f))
assert len(rows) == 2439
assert len({r["v06_qualified_name"] for r in rows}) == 2439
assert sum(r["external_boundary"] == "True" for r in rows) == 239
assert all(r["lean_file"] and r["lean_candidate_provenance"] not in {"NAME_ONLY", "NONE"}
           for r in rows if r["reuse_action"] == "REUSE_AFTER_REVALIDATION")
assert all(r["v04_counterpart_status"] == "NONE"
           for r in rows if r["v04_to_v06_class"] == "NEW_IN_V06")
assert all(r["reason"] for r in rows if r["reuse_action"] == "REVIEW_REQUIRED")
foundations = {(r["v06_file"], r["v06_declaration"]): r for r in rows if r["foundation_sensitive"] == "True"}
assert len(foundations) == 19
for key in [("behavior/schedule.v", "ProcessorState"),
            ("behavior/job.v", "JobType"),
            ("model/task/concept.v", "TaskType")]:
    assert foundations[key]["representation_policy"] != "DEFAULT_DECLARATION_FIDELITY"
print("MAPPING_INTEGRITY_PASS")
PY

production_tree_after=$(git -C "$repo_root" rev-parse HEAD:Prosa-fei/Prosa)
[[ "$production_tree_before" == "$production_tree_after" ]]
[[ -z "$(git -C "$repo_root" status --short -- Prosa-fei/Prosa)" ]]
git -C "$repo_root" diff --check

python3 - "$mapping_dir" "$project_root" "$production_tree_after" <<'PY'
import hashlib, json, subprocess, sys
from pathlib import Path
out, project, tree = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
def h(path): return hashlib.sha256(path.read_bytes()).hexdigest()
manifest = {
  "v06_source_commit": "414e66760333eaa4ef78c685bcf53291c527a548",
  "v04_reference_commit": "ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7",
  "current_repository_commit": subprocess.check_output(["git", "-C", str(project), "rev-parse", "HEAD"], text=True).strip(),
  "production_lean_tree": tree,
  "lean_toolchain": (out / "logs/lean_version.log").read_text().strip(),
  "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
  "artifact_sha256": {name: h(out / name) for name in [
    "v04_file_inventory.csv", "v04_declaration_inventory.csv",
    "v06_migration_table.csv", "v06_migration_table.json",
    "v04_legacy_only.csv", "mapping_summary.json"]},
  "production_lean_modified": False,
}
(out / "reproduction_manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
PY

echo "V06_MAPPING_REPRODUCTION_PASS"
