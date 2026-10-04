"""Split each contract into per-declaration blocks (Check type + Print body) for comparison across case studies."""
import json, re, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
NOISE = re.compile(r"incompatible prefixes|defined at level|^with arguments|^File |have incompatible|One of them")
def blocks(cs):
    text = "\n".join(l for l in (HERE / "contracts" / f"{cs}.txt").read_text().splitlines() if not NOISE.search(l))
    m = json.load(open(HERE / "contracts/manifest.json"))[cs]
    out = {}
    names = m["declarations"]
    for i, n in enumerate(names):
        s = text.find(f"@{n}\n") if f"@{n}\n" in text else text.find(f"{n}\n")
        e = len(text)
        for n2 in names[i + 1:]:
            k = text.find(f"@{n2}\n", s + 1)
            if k < 0: k = text.find(f"\n{n2}\n", s + 1)
            if k > 0: e = min(e, k); break
        out[n.split(".")[-1]] = " ".join(text[s:e].split())
    return out
if __name__ == "__main__":
    m = json.load(open(HERE / "contracts/manifest.json"))
    fam = [c for c in m if c.startswith(("2009", "2014", "2015-BOOK"))]
    B = {c: blocks(c) for c in fam}
    names = sorted({n for c in fam for n in B[c]})
    for n in names:
        groups = {}
        for c in fam:
            if n in B[c]:
                groups.setdefault(B[c][n], []).append(c)
        if len(groups) > 1 or len(next(iter(groups.values()))) > 1:
            print(f"{n}: {len(groups)} variant(s): " + " | ".join(",".join(x.replace('2009-RTSS-','09:').replace('2014-RTCSA-','14:') for x in v) for v in groups.values()))
