#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VALIDATION_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
PROSA_FEI_DIR="$(cd "$VALIDATION_DIR/.." && pwd)"
REPO_ROOT="$(git -C "$PROSA_FEI_DIR" rev-parse --show-toplevel)"
PINNED_COMMIT=414e66760333eaa4ef78c685bcf53291c527a548
HISTORY_REPO="${PROSA_HISTORY_REPO:-$VALIDATION_DIR/.work/prosa_history_repo}"
SOURCE_DIR="${PROSA_V06_SOURCE_DIR:-$VALIDATION_DIR/.work/prosa-v06-414e667}"
OPAM_SWITCH="${PROSA_OPAM_SWITCH:-prosa-0.6}"
MATHLIB_DIR="${MATHLIB_DIR:-/private/tmp/mathlib4-v4.33.1}"
JOBS="${JOBS:-8}"
LOG_DIR="$SCRIPT_DIR/logs"
mkdir -p "$LOG_DIR"

before_tree="$(git -C "$REPO_ROOT" rev-parse HEAD:Prosa-fei/Prosa)"
if [[ ! -d "$SOURCE_DIR/.git" && ! -f "$SOURCE_DIR/.git" ]]; then
  git -C "$HISTORY_REPO" worktree add --detach "$SOURCE_DIR" "$PINNED_COMMIT"
fi
actual_commit="$(git -C "$SOURCE_DIR" rev-parse HEAD)"
[[ "$actual_commit" == "$PINNED_COMMIT" ]] || { echo "wrong source commit: $actual_commit" >&2; exit 1; }

# Exhaustive file dependency extraction. The all target deliberately includes
# implementation/refinements even when its external CoqEAL boundary is absent.
(cd "$SOURCE_DIR" && make allCoqProject >/dev/null)
(cd "$SOURCE_DIR" && opam exec --switch "$OPAM_SWITCH" -- coqdep -f _CoqProject \
  >"$LOG_DIR/coqdep_all.raw" 2>"$LOG_DIR/coqdep_all.stderr")

# Build the official main package to obtain exact .glob reference positions.
# Refinements remain inventoried, but are an explicit external build boundary.
(cd "$SOURCE_DIR" && make prosaCoqProject >/dev/null)
(cd "$SOURCE_DIR" && opam exec --switch "$OPAM_SWITCH" -- make -j"$JOBS" \
  >"$LOG_DIR/main_build.log" 2>&1)

python3 "$SCRIPT_DIR/generate_v06_inventory.py" \
  --source "$SOURCE_DIR" \
  --coqdep-output "$LOG_DIR/coqdep_all.raw" \
  --coqdep-errors "$LOG_DIR/coqdep_all.stderr" \
  --output "$SCRIPT_DIR" \
  --repo-root "$REPO_ROOT" \
  --mathlib "$MATHLIB_DIR" | tee "$LOG_DIR/generator_summary.log"

python3 "$SCRIPT_DIR/elaborate_declaration_types.py" generate \
  --inventory "$SCRIPT_DIR/declaration_inventory.csv" \
  --files "$SCRIPT_DIR/file_inventory.csv" \
  --output "$LOG_DIR/elaborated_type_probe.v" | tee "$LOG_DIR/type_probe_generation.log"
opam exec --switch "$OPAM_SWITCH" -- coqtop -quiet -batch -R "$SOURCE_DIR" prosa \
  -l "$LOG_DIR/elaborated_type_probe.v" \
  >"$LOG_DIR/elaborated_type_probe.stdout" 2>"$LOG_DIR/elaborated_type_probe.stderr"
python3 "$SCRIPT_DIR/elaborate_declaration_types.py" merge \
  --inventory "$SCRIPT_DIR/declaration_inventory.csv" \
  --probe-output "$LOG_DIR/elaborated_type_probe.stdout" \
  --evidence "$SCRIPT_DIR/declaration_type_evidence.json" | tee "$LOG_DIR/type_probe_merge.log"
python3 "$SCRIPT_DIR/harden_declaration_dependency_docs.py" \
  --source "$SOURCE_DIR" --output "$SCRIPT_DIR" | tee "$LOG_DIR/declaration_hardening_docs.log"

if command -v dot >/dev/null 2>&1; then
  dot -Tsvg "$SCRIPT_DIR/file_dag.dot" -o "$SCRIPT_DIR/file_dag.svg"
fi

# Completeness and safety checks.
python3 - "$SCRIPT_DIR" "$SOURCE_DIR" <<'PY'
import csv, json, sys
from pathlib import Path
out, source = map(Path, sys.argv[1:])
source_files = sorted(p.relative_to(source).as_posix() for p in source.rglob("*.v") if ".git" not in p.parts)
inventory = list(csv.DictReader((out / "file_inventory.csv").open()))
listed = [row["file"] for row in inventory]
assert len(listed) == len(set(listed)), "duplicate source file in inventory"
assert sorted(listed) == source_files, "inventory does not cover every source file exactly once"
modules = {row["module"] for row in inventory}
for edge in csv.DictReader((out / "file_dag_edges.csv").open()):
    assert edge["dependency_module"] in modules and edge["dependent_module"] in modules
dag = json.loads((out / "file_dag.json").read_text())
covered = {node["file"] for node in dag["nodes"]}
assert covered == set(source_files), "graph node coverage mismatch"
component_coverage = {node for component in dag["strongly_connected_components"] for node in component}
assert component_coverage == set(source_files), "SCC/condensation coverage mismatch"
layers = {row["file"]: int(row["layer"]) for row in csv.DictReader((out / "file_layers.csv").open())}
if not dag["cycles"]:
    for edge in dag["edges"]:
        assert layers[edge["dependency_file"]] < layers[edge["dependent_file"]], "invalid topological layer"
decl_dag = json.loads((out / "declaration_dag.json").read_text())
assert set(decl_dag["unresolved_files"]) == {
    row["file"] for row in inventory if row["build_group"] == "refinements"
}, "unresolved declaration files are not exactly the explicit refinement boundary"
declarations = list(csv.DictReader((out / "declaration_inventory.csv").open()))
assert all(row["type_evidence_status"] in {
    "ELABORATED_ROCQ_CHECK", "UNRESOLVED_EXTERNAL_BUILD_BOUNDARY_COQEAL"
} for row in declarations), "unclassified declaration type evidence"
assert all(row["implicit_dependency_status"] in {
    "UNRESOLVED_IMPLICIT_DEPENDENCY", "UNRESOLVED_EXTERNAL"
} for row in csv.DictReader((out / "declaration_layers.csv").open()))
assert (out / "foundation_dependency_audit.md").exists()
assert (out / "declaration_dependency_method.md").exists()
print(f"completeness: {len(source_files)} files, exactly once")
PY

after_tree="$(git -C "$REPO_ROOT" rev-parse HEAD:Prosa-fei/Prosa)"
[[ "$before_tree" == "$after_tree" ]] || { echo "production Lean tree changed" >&2; exit 1; }
git -C "$REPO_ROOT" diff --check

{
  echo "source_commit=$actual_commit"
  echo "rts_commit=$(git -C "$REPO_ROOT" rev-parse HEAD)"
  echo "prosa_lean_tree=$after_tree"
  opam exec --switch "$OPAM_SWITCH" -- rocq --version | tr '\n' ' '
  echo
  lean --version
  if [[ -d "$MATHLIB_DIR/.git" ]]; then echo "mathlib_commit=$(git -C "$MATHLIB_DIR" rev-parse HEAD)"; fi
  shasum -a 256 "$SCRIPT_DIR"/*.csv "$SCRIPT_DIR"/*.json "$SCRIPT_DIR"/*.dot
} >"$LOG_DIR/reproduction_manifest.txt"

echo "Prosa v0.6 dependency inventory reproduced successfully."
