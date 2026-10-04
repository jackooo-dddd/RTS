#!/usr/bin/env python3
"""Dump the elaborated Rocq contract of classic files from the trial build in ProsaBuddy's toolchain.

usage: dump_contracts.py [SOURCE ...]     (default: every TODO/IN_PROGRESS file of file_order.csv)

For each file writes contracts/<slug>.txt: `Print Module` of the file's module (every declaration with its
elaborated type, nested modules included) followed by `About` of each declaration (implicit arguments).
The build is `Validation/.work/classic_full_probe_rocq90` (opam switch `prosa-0.6`, Rocq 9.0.1).
"""
import csv, re, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
WS = HERE.parents[1]
BUILD = WS / "Validation/.work/classic_full_probe_rocq90"
OUT = HERE / "contracts"
ITEM = re.compile(r"(?:^|\. |Struct )(Definition|Parameter|Fixpoint|Inductive|CoInductive|Record|Structure|Class|Instance)"
                  r" (\S+)")


def rocq(vfile):
    r = subprocess.run(["zsh", "-c", 'ulimit -s 65520 && exec "$@"', "_", "opam", "exec", "--switch=prosa-0.6",
                        "--", "rocq", "c", "-R", "src", "prosa", str(vfile)],
                       cwd=BUILD, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


KW = r"(?:Definition|Parameter|Fixpoint|Inductive|CoInductive|Record|Structure|Class|Instance|Module|End)\b"


def names(printed, top):
    """Qualified declaration names in a `Print Module` output, following nested `Module M := Struct ... End`.
    The outermost `Module <file> := Struct ... End` is the file itself and adds no qualifier."""
    text = " ".join(printed.split()).replace(":= Struct ", ":= Struct. ")
    # a collapsed submodule or module alias prints as a bare `Module X` with no terminating period;
    # make it its own item so that the declaration following it is not swallowed
    text = re.sub(r"\bModule (\w+) (?=" + KW + ")", r"Module \1. ", text)
    items = re.split(r"(?<=\.)\s+(?=" + KW + ")", text)
    out, stack = [], []
    for it in items:
        m = re.match(r"Module (\w+) := Struct", it)
        if m:
            stack.append(m.group(1)); continue
        if re.match(r"End\b", it):
            if stack: stack.pop()
            continue
        m = re.match(r"(?:Definition|Parameter|Fixpoint|Inductive|CoInductive|Record|Structure|Class|Instance) (\S+)", it)
        if m:
            out.append(".".join(stack[1:] + [m.group(1)]))
    return out


def print_module(path, probe, mod):
    probe.write_text(f"Require Import {mod}.\nSet Printing Depth 100000.\nSet Printing Width 4000.\n"
                     f"Print Module {path}.\n")
    return rocq(probe)


def collect(path, probe, mod, qual, printed_all, decls, aliases=frozenset()):
    """Print module `path`; collapsed nested modules (`Module M End`) are printed recursively."""
    rc, printed = print_module(path, probe, mod)
    if rc:
        raise RuntimeError(printed[-500:])
    printed = printed.strip()
    printed_all.append(printed)
    decls += [".".join(qual + [n]) for n in names(printed, path)]
    # collapsed submodules print as `Module A Module B ... End` (no `:= Struct`)
    for sub in re.findall(r"Module (\w+)(?! :=)(?=\s|$)", " ".join(printed.split())):
        if sub in aliases:        # `Module X := path.` is an alias of another file's module
            continue
        collect(f"{path}.{sub}", probe, mod, qual + [sub], printed_all, decls, aliases)


def dump(src):
    mod = "prosa." + src[:-2].replace("/", ".")
    slug = src[len("classic/"):-2].replace("/", "__")
    probe = BUILD / "probe" / f"C_{slug}.v"
    probe.parent.mkdir(exist_ok=True)
    printed_all, decls = [], []
    try:
        src_text = (WS / "Validation/.work/prosabuddy-f692cb7/prosaworkspace" / src).read_text()
        aliases = frozenset(re.findall(r"Module\s+(\w+)\s*:=", src_text))
        collect(mod, probe, mod, [], printed_all, decls, aliases)
    except RuntimeError as e:
        return f"FAILED Print Module: {e}"
    probe.write_text(f"Require Import {mod}.\nSet Printing Depth 100000.\nSet Printing Width 4000.\n" +
                     "".join(f"About {mod}.{d}.\n" for d in decls))
    rc, about = rocq(probe) if decls else (0, "")
    OUT.mkdir(exist_ok=True)
    (OUT / f"{slug}.txt").write_text(f"# {src}: {len(decls)} declarations\n\n## Print Module\n\n"
                                     + "\n\n".join(printed_all) + f"\n\n## About\n\n{about.strip()}\n")
    return f"{len(decls)} declarations" + ("" if rc == 0 else " (About failed)")


def main():
    srcs = sys.argv[1:] or [r["source"] for r in csv.DictReader(open(HERE / "file_order.csv"))
                            if r["status"] in ("TODO", "IN_PROGRESS", "TRANSLATED")]
    for s in srcs:
        print(s, dump(s), flush=True)


if __name__ == "__main__":
    main()
