#!/usr/bin/env python3
"""Build the translation plan for the whole classic Prosa folder of ProsaBuddy (f692cb7).

usage: make_plan.py            (re)write file_dependencies.csv and file_order.csv, keeping existing statuses

* file_dependencies.csv: one row per direct `Require` edge `file,depends_on` (classic → classic or v0.6 util).
* file_order.csv: the ranked translation order.  Ranks are a topological order of the dependency graph:
  layer = length of the longest dependency chain below the file; within a layer files are ordered by area
  (util, model, analysis, implementation) and then by path, so that related files stay together.
  The 49 files translated for the case studies keep their Lean modules and status (ACCEPTED); they are
  reused, not re-translated.  Statuses of the other files are preserved across re-runs.
"""
import csv, hashlib, re
from pathlib import Path

HERE = Path(__file__).resolve().parent
WS = HERE.parents[1]                                   # Prosa-Shunqi
SRC = WS / "Validation/.work/prosabuddy-f692cb7/prosaworkspace"
CASE = WS / "classic-prosa/casestudy-translation/file_order.csv"
DEPS = HERE / "file_dependencies.csv"
ORDER = HERE / "file_order.csv"
AREA = {"util": 0, "model": 1, "analysis": 2, "implementation": 3}


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def strip_comments(t):
    out, i, d = [], 0, 0
    while i < len(t):
        if t.startswith("(*", i): d += 1; i += 2; continue
        if d and t.startswith("*)", i): d -= 1; i += 2; continue
        if not d: out.append(t[i])
        i += 1
    return "".join(out)


def requires(text):
    deps = []
    for m in re.finditer(r"Require\s+(?:Import|Export)?\s*(.*?)\.(?:\s|$)", strip_comments(text), re.S):
        for x in m.group(1).split():
            if x.startswith("prosa."):
                deps.append(x[len("prosa."):].replace(".", "/") + ".v")
    return deps


DECL = re.compile(r"^\s*(?:Local\s+|Global\s+|#\[[^\]]*\]\s*|Program\s+)*"
                  r"(Lemma|Theorem|Corollary|Remark|Fact|Proposition|Definition|Fixpoint|CoFixpoint|Inductive|"
                  r"CoInductive|Record|Structure|Class|Instance|Let|Variant|Canonical|Coercion)\s", re.M)


def decl_count(src, cs):
    """Exact count: the case-study inventory, or the `Print Module` contract of the trial build."""
    if cs:
        return int(cs["decls"])
    c = HERE / "contracts" / (src[len("classic/"):-2].replace("/", "__") + ".txt")
    if c.exists():
        return int(re.match(r"# \S+: (\d+) declarations", c.read_text()).group(1))
    return len(DECL.findall(strip_comments((SRC / src).read_text())))


def lean_target(rel):
    parts = rel[:-2].split("/")                         # classic/model/schedule/uni/basic/platform
    camel = lambda s: "".join(w[:1].upper() + w[1:] for w in re.split(r"_", s))
    return "Prosa/" + "/".join(camel(p) for p in parts) + ".lean"


def main():
    classic = sorted(p.relative_to(SRC).as_posix() for p in (SRC / "classic").rglob("*.v"))
    edges, util = {}, set()
    for rel in classic:
        ds = []
        for d in requires((SRC / rel).read_text()):
            if d not in ds:
                ds.append(d)
            if d.startswith("util/"):
                util.add(d)
        edges[rel] = ds
    missing = {d for ds in edges.values() for d in ds if d.startswith("classic/") and d not in edges}
    assert not missing, missing
    # layers (longest chain of classic dependencies)
    layer = {}
    def L(f):
        if f not in layer:
            layer[f] = 1 + max([L(d) for d in edges[f] if d.startswith("classic/")], default=-1)
        return layer[f]
    for f in classic: L(f)
    order = sorted(classic, key=lambda f: (layer[f], AREA[f.split("/")[1]], f))
    case = {r["source"]: r for r in csv.DictReader(open(CASE))}
    old = {r["source"]: r for r in csv.DictReader(open(ORDER))} if ORDER.exists() else {}
    with open(DEPS, "w", newline="") as fh:
        w = csv.writer(fh); w.writerow(["file", "depends_on"])
        for f in order:
            for d in edges[f]:
                w.writerow([f, d])
    rows = []
    for rank, f in enumerate(order, 1):
        text = (SRC / f).read_text()
        cs = case.get(f)
        prev = old.get(f, {})
        status = prev.get("status") or ("ACCEPTED" if cs else "TODO")
        note = prev.get("note") or ("case-study translation (reused): " + cs["note"] if cs else "")
        rows.append({
            "rank": rank, "layer": layer[f], "area": f.split("/")[1], "source": f, "sha256": sha(SRC / f),
            "lines": text.count("\n"), "decls": decl_count(f, cs),
            "classic_deps": " ".join(d for d in edges[f] if d.startswith("classic/")),
            "v06_util_deps": " ".join(d for d in edges[f] if d.startswith("util/")),
            "lean_target": cs["lean_target"] if cs else lean_target(f),
            "case_study": "yes" if cs else "", "status": status, "note": note})
    with open(ORDER, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    update_readme(rows)
    print(f"{len(rows)} classic files, {sum(r['case_study'] == 'yes' for r in rows)} from the case studies; "
          f"{len(util)} v0.6 util modules imported; layers 0..{max(layer.values())}")


def update_readme(rows):
    readme = HERE / "README.md"
    if not readme.exists():
        return
    import collections, datetime
    st = collections.Counter(r["status"] for r in rows)
    todo = [r for r in rows if r["case_study"] != "yes"]
    done = sum(r["status"] in ("TRANSLATED", "ACCEPTED") for r in todo)
    status = (f"**Progress: {done} / {len(todo)} remaining classic files translated** "
              f"(+ {len(rows) - len(todo)} reused from the case studies; "
              + ", ".join(f"{k} {v}" for k, v in sorted(st.items())) +
              f") · last update: {datetime.date.today().isoformat()}")
    table = ["| Rank | Layer | ProsaBuddy source (`classic/…`) | Decls | Lines | Lean target (`Prosa/Classic/…`) | Status |",
             "|---:|---:|---|---:|---:|---|---|"]
    for r in rows:
        mark = " ᶜ" if r["case_study"] == "yes" else ""
        table.append(f"| {r['rank']} | {r['layer']} | `{r['source'][len('classic/'):]}`{mark} | {r['decls']} | "
                     f"{r['lines']} | `{r['lean_target'][len('Prosa/Classic/'):]}` | {r['status']} |")
    text = readme.read_text()
    text = re.sub(r"<!-- STATUS_BEGIN -->.*?<!-- STATUS_END -->",
                  "<!-- STATUS_BEGIN -->\n" + status + "\n<!-- STATUS_END -->", text, flags=re.S)
    text = re.sub(r"<!-- TABLE_BEGIN -->.*?<!-- TABLE_END -->",
                  "<!-- TABLE_BEGIN -->\n" + "\n".join(table) + "\n<!-- TABLE_END -->", text, flags=re.S)
    readme.write_text(text)


if __name__ == "__main__":
    main()
