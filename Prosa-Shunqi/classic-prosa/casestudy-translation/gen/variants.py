"""Group the declarations of the 2009/2014/2015-BOOK case studies into variants with textually identical contracts
(contracts/variants.json, contracts/variants.txt)."""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from cs_bodies import blocks
m = json.load(open(ROOT / 'contracts/manifest.json'))
fam = [c for c in m if c.startswith(('2009', '2014', '2015-BOOK'))]
B = {c: blocks(c) for c in fam}
order = []
for c in fam:
    for n in B[c]:
        if n not in order: order.append(n)
out, variants = [], {}
for n in order:
    groups = {}
    for c in fam:
        if n in B[c]: groups.setdefault(B[c][n], []).append(c)
    for i, (body, cs) in enumerate(groups.items()):
        vid = f"{n}#{chr(65 + i)}"
        variants[vid] = cs
        out.append(f"===== {vid}  [{', '.join(cs)}]\n{body}\n")
(ROOT / 'contracts/variants.txt').write_text('\n'.join(out))
(ROOT / 'contracts/variants.json').write_text(json.dumps(variants, indent=1) + '\n')
print(len(variants), 'variants')
