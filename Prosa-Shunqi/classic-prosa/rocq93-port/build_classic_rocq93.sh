#!/usr/bin/env bash
# Build ProsaBuddy's classic Prosa (scope: scope_files.txt) under this project's
# validation environment (Rocq 9.3+rc1 + MathComp 2.6, opam switch `rocq93rc1`).
#
# Inputs are read-only: ProsaBuddy's sources, this project's existing v0.6 util
# patches, and the files next to this script.  Everything is built in WORKDIR.
#
# usage: build_classic_rocq93.sh [WORKDIR] [PROSABUDDY_WORKSPACE] [OPAM_SWITCH]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${1:-$HERE/.work}"
PB="${2:-$HERE/../../../prosabuddy/prosaworkspace}"
SWITCH="${3:-rocq93rc1}"
PATCHES="$HERE/../../Validation/patches"
JOBS="${JOBS:-6}"

export PATH="$HOME/.opam/$SWITCH/bin:$PATH" OPAM_SWITCH_PREFIX="$HOME/.opam/$SWITCH"
echo "Rocq: $(rocq --version | head -1)"

rm -rf "$WORK"; mkdir -p "$WORK/src" "$WORK/compat"
# 1. sources: ProsaBuddy util (= official v0.6 util) + classic; follow symlinks
rsync -aL --include='*/' --include='*.v' --exclude='*' "$PB/util" "$PB/classic" "$WORK/src/"
# 2. this project's existing Rocq 9.3 patches for v0.6 util (util hunks only)
( cd "$WORK/src"
  git apply --include='util/*' "$PATCHES/prosa-v06-rocq93-official-proof-closure-common.patch"
  git apply "$PATCHES/prosa-v06-rocq93-util-fixpoint.patch" "$PATCHES/prosa-v06-rocq93-util-minmax.patch"
  # 3. the single proof-script fix needed by classic under Rocq 9.3
  git apply "$HERE/prosabuddy-classic-rocq93.patch" )
# 4. compatibility prelude restoring two Rocq 9.0 defaults (no source edits)
cp "$HERE/Rocq90Compat.v" "$WORK/compat/"
( cd "$WORK/compat" && rocq compile -Q . Compat Rocq90Compat.v )
# 5. build: v0.6 util as the project builds it; classic with the prelude
cd "$WORK/src"
printf -- '-R . prosa\n-arg "-w -notation-overriden,-parsing,-projection-no-head-constant,-ambiguous-paths"\n' > _CoqProject
UTIL=$(grep '^util/' "$HERE/scope_files.txt" | tr '\n' ' ')
CLASSIC=$(grep '^classic/' "$HERE/scope_files.txt" | tr '\n' ' ')
rocq makefile -f _CoqProject $UTIL $CLASSIC -o Makefile >/dev/null 2>&1
make -j"$JOBS" ${UTIL//.v/.vo}
make -j"$JOBS" OTHERFLAGS="-Q $WORK/compat Compat -ri Compat.Rocq90Compat" ${CLASSIC//.v/.vo}
n=$(for f in $UTIL $CLASSIC; do [ -f "${f%.v}.vo" ] && echo; done | wc -l | tr -d ' ')
echo "built $n / $(wc -l < "$HERE/scope_files.txt" | tr -d ' ') files"
echo "To load these .vo files later, add: -R $WORK/src prosa -Q $WORK/compat Compat"
