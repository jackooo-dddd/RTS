#!/usr/bin/env python3
"""Split the accepted v0.6 Rocq 9.3 util patches into per-file patches for classic official closures.

Classic official closures compile ProsaBuddy's v0.6 `util/` files under rocq93rc1, which needs the
same proof-only compatibility hunks the v0.6 chain already records.  The pipeline only accepts
patches that touch files of the closure, so every `util/` section of
  patches/prosa-v06-rocq93-official-proof-closure-common.patch
is copied verbatim into patches/classic/rocq93-<file>.patch (and the per-file util patches are
referenced as they are).  Writes patches/classic/util_patch_map.json: {util file: [patch, ...]}.
"""
import hashlib
import json
import re
from pathlib import Path

V = Path(__file__).resolve().parents[1]
COMMON = V / "patches/prosa-v06-rocq93-official-proof-closure-common.patch"
OUT = V / "patches/classic"


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    text = COMMON.read_text()
    sections = re.split(r"(?m)^(?=--- a/)", text)
    mapping: dict[str, list[str]] = {}
    for sec in sections:
        m = re.match(r"--- a/(util/\S+)\n\+\+\+ b/\1\n", sec)
        if not m:
            continue
        rel = m.group(1)
        name = f"rocq93-{rel.replace('/', '-')[:-2]}.patch"
        header = (f"Verbatim `{rel}` section of patches/{COMMON.name}\n"
                  f"(sha256 {hashlib.sha256(text.encode()).hexdigest()}), split out for classic official closures.\n")
        (OUT / name).write_text(header + sec)
        mapping[rel] = [f"patches/classic/{name}"]
    for rel, patch in (("util/minmax.v", "patches/prosa-v06-rocq93-util-minmax.patch"),
                       ("util/fixpoint.v", "patches/prosa-v06-rocq93-util-fixpoint.patch")):
        mapping.setdefault(rel, []).append(patch)
    (OUT / "util_patch_map.json").write_text(json.dumps(mapping, indent=2, sort_keys=True) + "\n")
    print(json.dumps(mapping, indent=1))


if __name__ == "__main__":
    main()
