#!/usr/bin/env bash
set -euo pipefail

# Config-driven front end for the audited lean4export modes used by the
# Prosa validator.  This script does not compile Lean; call it from a prepared
# snapshot whose LEAN_PATH already points at fresh, hash-bound .olean files.

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

config=
output=
log=
metadata=
while [[ $# -gt 0 ]]; do
  case "$1" in
    --config) config=$2; shift 2 ;;
    --output) output=$2; shift 2 ;;
    --log) log=$2; shift 2 ;;
    --metadata) metadata=$2; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
[[ -n "$config" && -n "$output" && -n "$log" && -n "$metadata" ]]
[[ -s "$config" ]]
mkdir -p "$(dirname "$output")" "$(dirname "$log")" "$(dirname "$metadata")"

python3 - "$config" <<'PY'
import json, sys
from pathlib import Path
c = json.loads(Path(sys.argv[1]).read_text())
required = {"schema_version", "module", "targets", "statement_only",
            "body_theorems", "definition_targets", "normalization"}
missing = required - set(c)
if missing:
    raise SystemExit("export config missing keys: " + ",".join(sorted(missing)))
targets = c["targets"]
if len(targets) != len(set(targets)) or not targets:
    raise SystemExit("export targets must be a nonempty unique list")
for key in ("statement_only", "body_theorems", "definition_targets"):
    unknown = set(c[key]) - set(targets)
    if key == "statement_only":
        # The audited exporter supports `*` as a generic request to omit all
        # theorem proof bodies in the transitive export closure.  This keeps
        # Lean's proof dependency graph out of an independent semantic
        # certificate while retaining each theorem's exact compiled type.
        unknown.discard("*")
    if unknown:
        raise SystemExit(f"{key} contains non-targets: {sorted(unknown)}")
n = c["normalization"]
for key in ("theorem_types", "subexpression_heads", "definition_bodies",
            "body_projections"):
    if key not in n or not isinstance(n[key], list):
        raise SystemExit("normalization missing list: " + key)
if any(n.values()) and not c.get("kernel_guard_artifacts"):
    raise SystemExit("normalized export requires kernel_guard_artifacts")
for path in c.get("kernel_guard_artifacts", []):
    p = Path(path)
    if not p.is_file() or p.stat().st_size == 0:
        raise SystemExit("kernel guard artifact missing: " + path)
PY

json_lines() {
  python3 - "$config" "$1" <<'PY'
import json, sys
print("\n".join(json.load(open(sys.argv[1]))[sys.argv[2]]))
PY
}
normalization_lines() {
  python3 - "$config" "$1" <<'PY'
import json, sys
print("\n".join(json.load(open(sys.argv[1]))["normalization"][sys.argv[2]]))
PY
}

module=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["module"])' "$config")
mapfile_compat=()
while IFS= read -r target; do [[ -n "$target" ]] && mapfile_compat+=("$target"); done < <(json_lines targets)
export LEAN4EXPORT_STATEMENT_ONLY=$(json_lines statement_only)
export LEAN4EXPORT_BODY_THEOREMS=$(json_lines body_theorems)
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=$(normalization_lines theorem_types)
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=$(normalization_lines subexpression_heads)
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=$(normalization_lines definition_bodies)
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=$(normalization_lines body_projections)

"$EXPORTER_ROOT/.lake/build/bin/lean4export" "$module" -- \
  "${mapfile_compat[@]}" > "$output" 2> "$log"
[[ -s "$output" ]]

python3 - "$config" "$output" "$metadata" \
  "$EXPORTER_ROOT/.lake/build/bin/lean4export" <<'PY'
import hashlib, json, sys, time
from pathlib import Path
config, output, metadata, exporter = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
c = json.loads(config.read_text())
guards = {
    str(Path(p).resolve()): sha(Path(p))
    for p in c.get("kernel_guard_artifacts", [])
}
result = {
    "schema_version": 1,
    "recorded_at_unix_ns": time.time_ns(),
    "module": c["module"],
    "target_count": len(c["targets"]),
    "statement_only_count": len(c["statement_only"]),
    "body_theorem_count": len(c["body_theorems"]),
    "definition_target_count": len(c["definition_targets"]),
    "normalization": c["normalization"],
    "kernel_guard_artifacts": guards,
    "config_sha256": sha(config),
    "exporter_sha256": sha(exporter),
    "output_sha256": sha(output),
    "output_bytes": output.stat().st_size,
}
metadata.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
PY
