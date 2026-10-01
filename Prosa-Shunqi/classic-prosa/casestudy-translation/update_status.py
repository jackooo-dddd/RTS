#!/usr/bin/env python3
"""Update translation status in file_order.csv and regenerate the README
status block and rank table from it (the CSV is the single source of truth).

usage:
  update_status.py                         # only regenerate README from the CSV
  update_status.py RANK[,RANK...] STATUS [NOTE]
    STATUS in TODO, IN_PROGRESS, TRANSLATED, ACCEPTED, BLOCKED, DEFERRED
"""
import csv, datetime, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
CSV = os.path.join(HERE, 'file_order.csv')
README = os.path.join(HERE, 'README.md')
STATUSES = {'TODO', 'IN_PROGRESS', 'TRANSLATED', 'ACCEPTED', 'BLOCKED', 'DEFERRED'}

rows = list(csv.DictReader(open(CSV)))
fields = list(rows[0].keys())

if len(sys.argv) >= 3:
    ranks = {int(r) for r in sys.argv[1].split(',')}
    status = sys.argv[2]
    assert status in STATUSES, status
    note = sys.argv[3] if len(sys.argv) > 3 else None
    for r in rows:
        if int(r['rank']) in ranks:
            r['status'] = status
            if note is not None:
                r['note'] = note
    with open(CSV, 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)

def short(p):
    return p.replace('classic/', '', 1)

count = {s: sum(r['status'] == s for r in rows) for s in STATUSES}
nxt = next((r for r in rows if r['status'] in ('TODO', 'IN_PROGRESS', 'BLOCKED')), None)
nS = sum(r['tier'] == 'S' for r in rows)
today = datetime.date.today().isoformat()
block = (
    f"**Progress: {count['ACCEPTED']} / {len(rows)} classic files accepted** "
    f"({count['TRANSLATED']} translated, {count['IN_PROGRESS']} in progress, "
    f"{count['DEFERRED']} deferred, {count['BLOCKED']} blocked) ·\n"
    f"tier S {nS} files · tier P {len(rows) - nS} files · "
    f"v0.6 `util` dependencies: 14 / 14 already accepted ·\n"
    + (f"next file: **rank {nxt['rank']}** `{nxt['source']}`" if nxt else "all files processed")
    + f" · last update: {today}"
)
table = ['| Rank | Layer | Tier | ProsaBuddy source (`classic/…`) | Decls (used) | Lines '
         '| Lean target (`Prosa/Classic/…`) | Status |',
         '|---:|---:|:---:|---|---:|---:|---|---|']
for r in rows:
    mark = ' ¹' if 're-exported' in r['note'] else ''
    table.append(f"| {r['rank']} | {r['layer']} | {r['tier']} | `{short(r['source'])}`{mark} "
                 f"| {r['decls']} ({r['needed_decls']}) | {r['lines']} "
                 f"| `{r['lean_target'].replace('Prosa/Classic/', '')}` | {r['status']} |")

text = open(README).read()
text = re.sub(r'(<!-- STATUS_BEGIN -->\n).*?(\n<!-- STATUS_END -->)',
              lambda m: m.group(1) + block + m.group(2), text, flags=re.S)
start = text.index('| Rank | Layer | Tier |')
end = text.index('\n\n', start)
text = text[:start] + '\n'.join(table) + text[end:]
open(README, 'w').write(text)
print(block.replace('\n', ' '))
