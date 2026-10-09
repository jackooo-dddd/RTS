#!/usr/bin/env bash
# Stage a run copy or verification copy of the built Lean package (DECISIONS D14).
#
# usage: stage_copy.sh <master copy with built .lake> <destination>
#
# - sources are copied from the master (never a `Solutions/` folder);
# - .lake/packages is a symlink to the master's (Mathlib etc., read-only, never rebuilt);
# - .lake/build is a writable copy of the master's (APFS clone with `cp -c` on macOS, plain copy elsewhere).
set -euo pipefail
master=$(cd "$1" && pwd)
dest=$2
[ -d "$master/.lake/build" ] && [ -d "$master/.lake/packages" ] || { echo "master is not built: $master" >&2; exit 2; }
[ -e "$dest" ] && { echo "destination exists: $dest" >&2; exit 2; }
mkdir -p "$dest"
rsync -a --exclude '.lake' --exclude 'Solutions' --exclude '.DS_Store' --exclude '.build_*' "$master/" "$dest/"
mkdir -p "$dest/.lake"
ln -s "$master/.lake/packages" "$dest/.lake/packages"
if [ "$(uname)" = Darwin ]; then
  cp -c -R "$master/.lake/build" "$dest/.lake/build"
else
  cp -a "$master/.lake/build" "$dest/.lake/build"
fi
echo "$dest"
