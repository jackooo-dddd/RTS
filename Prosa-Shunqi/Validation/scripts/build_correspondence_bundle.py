#!/usr/bin/env python3
"""Build Deliverables/correspondence-verification: for each Prosa v0.6 file, the official Rocq file, its Lean
translation, every declaration printed three ways, the correspondence certificates and their assumption audit.

Usage (from any directory):
  build_correspondence_bundle.py stage SLUG ...       a file with a pipeline spec (tooling/file_specs/SLUG.json)
  build_correspondence_bundle.py early SRC ...        an early file validated by its own script (src path, e.g. behavior/service.v)
  build_correspondence_bundle.py foundation SRC ...   one of the twelve foundation files (behavior/time.v, util/*.v)
  build_correspondence_bundle.py zero SRC ...         a file without public declarations
  build_correspondence_bundle.py finalize             assemble the bundle from everything staged

Staging prints declarations with Rocq and Lean and caches the output in Validation/.work/correspondence_cache/<key>/,
so later runs reuse it. `finalize` groups certificate modules by content: a text used by at least two files goes to
shared/certificates/ (with its origin, the first file in dependency order whose certificates contain it), the rest to
each file's 4_correspondence/. It then writes the READMEs, shared.md files, CSVs, FILES.md and SHA256SUMS.
The script only reads validation artifacts; it writes only the bundle and its cache."""
import csv, glob, hashlib, io, json, os, re, shutil, subprocess, sys
from pathlib import Path

P = Path(__file__).resolve().parents[2]
V = P / 'Validation'
OUT = P.parent / 'Deliverables/correspondence-verification'
CACHE = P / 'Validation/.work/correspondence_cache'
IMP = V / '.work/tooling/rocq-lean-import/src'
OFFICIAL = V / '.work/prosa-v06-414e667'
NOISE = re.compile(r'Warning|notation-overridden|^File |overriding|previously bound|remapped|missing-proof|^\[|deprecated|fragile')
INV = list(csv.DictReader(open(V / 'planning/v06_dependency/declaration_inventory.csv')))
SPECS = {}
for p in glob.glob(str(V / 'tooling/file_specs/*.json')):
    try: s = json.load(open(p))
    except Exception: continue
    SPECS[s.get('slug') or Path(p).stem] = s
COMMONS = {Path(f).stem for f in os.listdir(V / 'certificates/common')}

ORDER = {m.group(3): int(m.group(1)) for m in re.finditer(r'^(\d{3})\s+L(\d{2})\s+(\S+\.v)',
         (P / 'v06_file_translation_order.md').read_text(), re.M)}

def project_index():
    """loose-normalized text hash -> sorted [(rank, source file, module path)] over the certificates of every file of the
    project: the published copy of each file's certificates (imported/translation_order/<slug>/certificates) and the
    certificate directories of the pipeline specs."""
    by_summary = {}
    for m in glob.glob(str(V / 'planning/v06_pipeline/*_module_manifest.json')):
        j = json.load(open(m))
        h = j.get('artifact_hashes', {}).get('assumption_summary_sha256') or j.get('assumption_summary_sha256')
        if h and j.get('source_file'): by_summary[h] = j['source_file']
    spec_dirs = {V / sp['cert_dir'] for sp in SPECS.values() if sp.get('cert_dir')}
    early_v = {}   # certificate sources of the early (pre-pipeline) files, kept in shared directories
    for d in (V / 'certificates').iterdir():
        if d.is_dir() and d not in spec_dirs and not d.name.startswith('classic') and d.name != 'common':
            for f in d.glob('*.v'): early_v.setdefault(f.stem, []).append(f)
    dirs, files = [], []
    for sp in SPECS.values():
        if sp.get('cert_dir') and sp.get('source'): dirs.append((V / sp['cert_dir'], sp['source']))
    for d in (V / 'imported/translation_order').iterdir():
        f = d / 'assumption_summary.json'
        src = by_summary.get(sha(f.read_bytes())) if f.exists() else None
        if not src:
            c = [o for o in ORDER if o[:-2].replace('/', '_') == d.name] or \
                [o for o in ORDER if o[:-2].replace('/', '_').endswith('_' + d.name)]
            src = c[0] if len(c) == 1 else None
        if not src: continue
        if (d / 'certificates').is_dir(): dirs.append((d / 'certificates', src))
        else:
            imps = {g.stem for g in d.glob('Imported*.vo')}
            files += [(g, src) for vo in d.glob('*.vo') for g in early_v.get(vo.stem, [])
                      if imported_name(g.read_text()) in imps | {None}]
    for d, src in dirs: files += [(f, src) for f in d.glob('*.v')] if d.is_dir() else []
    # early files: their manifests record the SHA-256 of each certificate source they compiled
    by_raw = {}
    for f in list((V / 'certificates').glob('*/*.v')) + list((V / '.work/experiments').glob('*/certificates/*.v')):
        by_raw.setdefault(sha(f.read_bytes()), f)
    for m in glob.glob(str(V / 'planning/v06_pipeline/*_module_manifest.json')):
        j = json.load(open(m)); src = j.get('source_file')
        hs = {**j, **j.get('artifact_hashes', {})}
        files += [(by_raw[h], src) for k, h in hs.items() if k.endswith('_source_sha256') and isinstance(h, str) and h in by_raw]
    # common modules: owned by the file whose Lean import they are bound to (else named after), e.g. ImportedNat -> util/nat.v
    def owner(stem):
        words = re.findall(r'[A-Z][a-z0-9]*', stem)
        for k in range(len(words), 0, -1):
            base = '_'.join(w.lower() for w in words[:k]) + '.v'
            c = sorted((r, o) for o, r in ORDER.items() if o.split('/')[-1] == base)
            if c: return c[0][1]
    for f in (V / 'certificates/common').glob('*.v'):
        imp = imported_name(f.read_text())
        o = owner(imp[len('Imported'):]) if imp else owner(re.sub(r'(Correspondence|BaseAdapter|Base)$', '', f.stem))
        if o: files.append((f, o))
    idx = {}
    for f, src in files:
        if src in ORDER: idx.setdefault(sha(norm(f.read_text(), True)), set()).add((ORDER[src], src, str(f.relative_to(V))))
    return {h: sorted(v) for h, v in idx.items()}

def sha(b): return hashlib.sha256(b if isinstance(b, bytes) else b.encode()).hexdigest()

BOILER = re.compile(r'^(GENERATED|Re-bound|Rebound|source:|Copy of|Artifact-local replay|Mechanical replay|This file is generated)', re.I)

def first_sentence(text):
    """First informative sentence of the module's comments; if there is none, what the module proves or defines."""
    for m in re.finditer(r'\(\*\*?\s*(.*?)\*\)', text, re.S):
        c = re.sub(r'\s+', ' ', m.group(1)).strip()
        if len(c) < 12 or BOILER.match(c) or c.startswith('*'): continue
        c = re.sub(r'\[([^\]]+)\]', r'`\1`', c)
        c = re.split(r'(?<=\.)\s+(?=[A-Z(`])', c)[0]
        if len(c) > 200: c = c[:200].rsplit(' ', 1)[0] + ' …'
        return c
    names = re.findall(r'^\s*(?:Lemma|Theorem|Corollary|Definition|Fixpoint|Instance)\s+([\w\']+)', text, re.M)
    if not names: return 'No description in the module.'
    more = f' and {len(names) - 3} more' if len(names) > 3 else ''
    return 'Proves or defines ' + ', '.join(f'`{n}`' for n in names[:3]) + more + '.'

def lean_desc(text):
    """Module doc (/-! -/), else first doc comment (/-- -/), else a generated summary of what the interface declares."""
    for pat in (r'/-!\s*(.*?)-/', r'/--\s*(.*?)-/'):
        m = re.search(pat, text, re.S)
        if m:
            d = re.sub(r'\s+', ' ', m.group(1)).strip()
            d = re.split(r'(?<=[.;])\s', d)[0]
            if d: return d if len(d) <= 160 else d[:160].rsplit(' ', 1)[0] + ' …'
    about = [i for i in re.findall(r'^import (Prosa\.\S+)', text, re.M)]
    names = re.findall(r'^(?:noncomputable )?(?:theorem|lemma|def|abbrev) (\w+)', text, re.M)
    kinds = 'equations' if all(re.search(r'^(?:theorem|lemma) ' + n, text, re.M) for n in names) else 'definitions and equations'
    shown = ', '.join(f'`{n}`' for n in names[:4]) + (', …' if len(names) > 4 else '')
    return (f"{len(names)} validation-only {kinds} about `{about[0]}`" if about else f"{len(names)} validation-only {kinds}") + \
           (f': {shown}' if names else '')

def norm(t, loose):
    t = re.sub(r'\(\*.*?\*\)', '', t, flags=re.S)
    t = re.sub(r'\bImported\w+\b', 'IMPORTED', t)
    if loose: t = re.sub(r'From Foundation(Certificates|Imported) Require (Import|Export)[^.]*\.', '', t)
    return re.sub(r'\s+', ' ', t).strip()

def imported_name(text):
    m = re.search(r'From FoundationImported Require Import\s+(Imported\w+)', text)
    return m.group(1) if m else None

def commons_of(text):
    out = set()
    for req in re.findall(r'From FoundationCertificates Require (?:Import|Export)([^.]*)\.', text):
        out |= {x for x in req.split() if x in COMMONS}
    return out

# ---------------------------------------------------------------- printing (cached)
def cached(path, probe_text, run):
    """Return cached output for probe_text, or run() and cache it."""
    key = path.with_suffix('.key')
    if path.exists() and key.exists() and key.read_text() == sha(probe_text): return path.read_text()
    out = run(); path.write_text(out); key.write_text(sha(probe_text)); return out

def rocq(switch, args, vfile, cwd):
    r = subprocess.run(['zsh', '-c', f'ulimit -s 65520; opam exec --switch={switch} -- rocq c {args} {vfile.name}'],
                       cwd=cwd, capture_output=True, text=True)
    return r.stdout + r.stderr

def blocks(text):
    out, cur = {}, None
    for line in text.splitlines():
        m = re.match(r'^=== (.*) ===$', line)
        if m: cur = m.group(1); out[cur] = []; continue
        if cur is not None and not NOISE.search(line): out[cur].append(line)
    return {k: '\n'.join(v).strip() for k, v in out.items()}

def lean_path(run):
    lp = [str(run / 'olean'), str(P / '.lake/build/lib/lean')]
    for p in ('mathlib', 'plausible', 'proofwidgets', 'batteries', 'aesop', 'importGraph', 'LeanSearchClient', 'Qq', 'Cli'):
        lp.append(str(P / f'.lake/packages/{p}/.lake/build/lib/lean'))
    return ':'.join(lp)

def rq(name):
    """The importer's Rocq spelling of a Lean name: dots become `_`, non-ASCII characters `_UUxxxx_`."""
    return ''.join(ch if ord(ch) < 128 else f'_UU{ord(ch):04x}_' for ch in name.replace('.', '_'))

def hyg(s): return re.sub(r'inst____at___[A-Za-z_]*?\d+__hygCtx__hyg(\d+)', r'inst_\1', s)

LEAN_AXIOMS = ('propext', 'Quot_sound', 'Classical_choice')

def categories(summary_path):
    summ = json.load(open(summary_path))
    cats = {'prop_sprop_foundation': set(), 'importer_foundation': set(), 'rocq_sprop_definitional_uip': set()}
    base = lambda x: x if x.startswith(('PrimInt63', 'PropSPropFoundation')) else x.split('.')[-1]
    for c in summ['certificates'].values():
        for k in cats: cats[k] |= {base(y) for y in c.get(k, [])}
    return {k: sorted(v) for k, v in cats.items()}

# ---------------------------------------------------------------- stage one pipeline file
def stage(slug):
    s = SPECS[slug]; src = s['source']; NS = s['lean_namespace']; EN = s['export_name']
    run = V / f'.work/experiments/{slug}_final'; pub = V / f'imported/translation_order/{slug}'; cdir = V / s['cert_dir']
    rows = [r for r in INV if r['source_file'] == src]; names = [r['declaration_name'] for r in rows]
    comp = set(s.get('computational', []))
    F = OUT / 'files' / src[:-2]; C = CACHE / slug
    C.mkdir(parents=True, exist_ok=True)
    for sub in ('1_source_rocq', '2_translation_lean', '3_printed_declarations', '5_assumptions'):
        if (F / sub).exists(): shutil.rmtree(F / sub)
        (F / sub).mkdir(parents=True)

    shutil.copy2(OFFICIAL / src, F / '1_source_rocq' / Path(src).name)
    pats = list(s.get('extra_source_patches', [])) + list((s.get('official_closure') or {}).get('patches', [])) \
        + list(s.get('patches', [])) + list(s.get('closure_patches', []))
    hunks = [part for pp in pats for part in re.split(r'(?m)^(?=--- a/)', (V / pp).read_text()) if part.startswith(f'--- a/{src}\n')]
    if hunks: (F / '1_source_rocq' / (Path(src).stem + '_rocq93_compat.patch')).write_text(''.join(hunks))
    shutil.copy2(P / s['production'], F / '2_translation_lean' / Path(s['production']).name)

    # printed declarations
    L = ['From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.',
         f"From prosa Require Import {src[:-2].replace('/', '.')}.", 'Set Printing Width 110. Set Printing Implicit. Set Printing Coercions.']
    for r in rows:
        L += [f'Goal True. idtac "=== {r["declaration_name"]} ===". Abort.', f'About {r["qualified_name"]}.', f'Check @{r["qualified_name"]}.']
        if r['declaration_name'] in comp:
            L += [f'Goal True. idtac "=== body of {r["declaration_name"]} ===". Abort.', f'Print {r["qualified_name"]}.']
    probe = '\n'.join(L) + '\n'; (C / 'OfficialPrint.v').write_text(probe)
    out = cached(C / 'official.out', probe, lambda: rocq('prosa-0.6', '', C / 'OfficialPrint.v', C))
    if 'Error' in out and s.get('source_mode') == 'official_closure':
        out = cached(C / 'official_closure.out', probe + run.name + str(bool(s.get('coqeal'))), lambda: rocq('rocq93rc1', f'-R {run}/source prosa' + (f' -Q {run}/coqeal/CoqEAL CoqEAL' if s.get('coqeal') else ''),
                                C / 'OfficialPrint.v', C))
    if 'Error' in out: raise RuntimeError(f'{slug}: official print failed\n{out[-1500:]}')
    off = blocks(out)

    L = [f"import {s['production'][:-5].replace('/', '.')}"]
    for n in names:
        L.append(f'#check @{NS}.{n}')
        if n in comp: L.append(f'#print {NS}.{n}')
    probe = '\n'.join(L) + '\n'; (C / 'LeanPrint.lean').write_text(probe)
    def run_lean():
        r = subprocess.run(['lean', str(C / 'LeanPrint.lean')], cwd=P, capture_output=True, text=True,
                           env={**os.environ, 'LEAN_PATH': lean_path(run)})
        return ('LEAN_FAILED\n' if r.returncode else '') + r.stdout + r.stderr
    out = cached(C / 'lean.out', probe, run_lean)
    if out.startswith('LEAN_FAILED'): raise RuntimeError(f'{slug}: lean print failed\n{out[-1500:]}')
    lean = {}; cur = None
    for line in out.splitlines():
        m = re.match(r'^(?:@?(?:' + re.escape(NS) + r'\.)?([\w\'.]+)\.?\{?[^ ]* :|(?:noncomputable |@\[[^\]]*\] )*(def|theorem|instance|abbrev|structure|class|inductive|opaque) ' + re.escape(NS) + r'\.([\w\'.]+))', line)
        if m and not line.startswith(' '):
            nm = (m.group(1) or m.group(3)).split('.{')[0].rstrip('.')
            if nm.startswith(NS + '.'): nm = nm[len(NS) + 1:]
            if nm in names: cur = (nm, 'print' if m.group(2) else 'check'); lean.setdefault(cur, [])
        if cur: lean[cur].append(line)
    lean = {k: '\n'.join(v).strip() for k, v in lean.items()}

    IN = f'Imported{EN}'; pre = NS.replace('.', '_') + '_'
    L = ['From LeanImport Require Import Lean.', f'From FoundationImported Require Import {IN}.',
         'Set Printing Width 110. Set Printing Implicit. Set Printing Coercions.']
    for n in names:
        L += [f'Goal True. idtac "=== {n} ===". Abort.', f'Check @{IN}.{rq(pre + n)}.']
        if n in comp: L += [f'Goal True. idtac "=== body of {n} ===". Abort.', f'Print {IN}.{rq(pre + n)}.']
    probe = '\n'.join(L) + '\n'; (C / 'ImportedPrint.v').write_text(probe)
    out = cached(C / 'imported.out', probe, lambda: rocq('rocq93rc1', f'-Q {IMP} LeanImport -I {IMP} -Q {run}/imported FoundationImported', C / 'ImportedPrint.v', C))
    if 'Error' in out: raise RuntimeError(f'{slug}: imported print failed\n{out[-1500:]}')
    imp = blocks(out)

    principal = s.get('principal', {})
    certs = {n: ', '.join(principal.get(n, [f'{n}_correspondence'])) for n in names}
    for r in rows:
        n = r['declaration_name']
        parts = [f'# `{n}`', '', f"- Kind (Rocq): {r['kind']}", f"- Rocq: `{r['qualified_name']}`", f'- Lean: `{NS}.{n}`',
                 f'- Certificate: `{certs[n]}`', '', '## Official Rocq', '', '```coq', off.get(n, '(not printed)'), '```']
        if f'body of {n}' in off: parts += ['', 'Body:', '', '```coq', off[f'body of {n}'], '```']
        parts += ['', '## Lean', '', '```lean', lean.get((n, 'check'), '(not printed)'), '```']
        if (n, 'print') in lean: parts += ['', 'Body:', '', '```lean', lean[(n, 'print')], '```']
        parts += ['', '## Lean, imported into Rocq', ''] + \
                 ['```coq', hyg(imp.get(n, '(not printed)')), '```']
        if f'body of {n}' in imp: parts += ['', 'Body:', '', '```coq', hyg(imp[f'body of {n}']), '```']
        (F / f'3_printed_declarations/{n}.md').write_text('\n'.join(parts) + '\n')

    shutil.copy2(pub / 'assumption_summary.json', F / '5_assumptions/assumption_summary.json')
    if (C / 'chain').exists(): shutil.rmtree(C / 'chain')
    (C / 'chain').mkdir()
    for m in s['chain']: shutil.copy2(cdir / f'{m}.v', C / 'chain' / f'{m}.v')
    ifaces = [fx for fx in s.get('fixtures', []) if fx != f'{EN}ComputationInterface'
              and (V / f'fixtures/translation_order/{fx}.lean').exists()]
    meta = {'src': src, 'rank': s['rank'], 'ns': NS, 'imported': IN, 'chain': s['chain'], 'interfaces': ifaces,
            'decls': [{'name': r['declaration_name'], 'kind': r['kind'], 'cert': certs[r['declaration_name']]} for r in rows],
            'cats': categories(pub / 'assumption_summary.json'), 'roles': {}}
    json.dump(meta, open(C / 'meta.json', 'w'), indent=1)
    print(f'staged {slug}: {len(rows)} declarations, {len(s["chain"])} chain modules', flush=True)

AUDIT = re.compile(r'(Assumption|Type|Source|Imported|Adapter)Audit$|SourceGuard$|TypeGuard$')

def order_chain(chain):
    names = {m for m, _ in chain}
    deps = {m: set(re.findall(r'\b(\w+)\b', ' '.join(re.findall(r'Require Import([^.]*)\.', f.read_text())))) & names - {m}
            for m, f in chain}
    ordered = []
    while deps:
        ready = sorted(m for m, d in deps.items() if d <= set(ordered))
        if not ready: raise RuntimeError('cyclic chain')
        ordered += ready; [deps.pop(m) for m in ready]
    path = dict(chain)
    return [(m, path[m]) for m in ordered]

_BY_RAW = {}
def by_raw():
    if not _BY_RAW:
        for f in list((V / 'certificates').glob('**/*.v')) + list((V / '.work/experiments').glob('*/certificates/*.v')) \
                 + list((V / '.work/experiments').glob('*/*.v')) + list((V / 'imported').glob('**/*.vo')) \
                 + list((V / '.work/experiments').glob('*/*.vo')) + list((V / '.work/experiments').glob('*/imported/*.vo')) \
                 + list((V / 'imported').glob('**/assumption_summary.json')) + list((V / '.work/experiments').glob('*/assumption_summary.json')):
            _BY_RAW.setdefault(sha(f.read_bytes()), f)
    return _BY_RAW

SKIP_KEYS = re.compile(r'^(assumption_audit|export|imported|production|source_type|target_type|source_slice|source_metadata|'
                       r'type_audit|lean_audit|exact_type_guards|source_type_guard|tooling|compatibility|source_copy|source_file)')

def require_closure(roots, IN, folders):
    """Follow `From FoundationCertificates Require Import` from the root certificates, resolving each module the way the
    run did: next to the requiring file, in the run's certificate folders, else a unique text bound to the same import."""
    pool = None
    out, todo = {}, list(roots)
    while todo:
        f = todo.pop()
        if f.stem in out: continue
        out[f.stem] = f
        for grp in re.findall(r'From\s+FoundationCertificates\s+Require\s+(?:Import|Export)?([^.]*)\.', f.read_text()):
            for n in grp.split():
                if n in COMMONS or n in out or n.startswith('Imported'): continue
                cands = [d / f'{n}.v' for d in [f.parent, *folders] if (d / f'{n}.v').exists()]
                if not cands:
                    if pool is None:
                        pool = {}
                        for g in list((V / 'certificates').glob('*/*.v')) + list((V / '.work/experiments').glob('*/certificates/*.v')):
                            pool.setdefault(g.stem, []).append(g)
                    texts = {sha(norm(g.read_text(), False)): g for g in pool.get(n, []) if imported_name(g.read_text()) in (IN, None)} \
                        or {sha(g.read_bytes()): g for g in pool.get(n, [])}   # a dependency's own certificate, used as is
                    if len(texts) != 1: raise LookupError(f'module {n} required by {f.name}: {len(texts)} candidate texts')
                    cands = list(texts.values())
                todo.append(cands[0])
    return [(m, f) for m, f in out.items() if not AUDIT.search(m)]

def early_record_by_hash(src, man):
    """No published folder: the manifest's SHA-256 values identify the run folder's certificate sources and import."""
    hs = {**{k: v for k, v in man.items() if isinstance(v, str)}, **man.get('artifact_hashes', {})}
    R = by_raw()
    chain, vos = [], []
    for k, h in hs.items():
        f = R.get(h) if isinstance(h, str) else None
        if f is None or k.startswith(('production', 'official', 'patched', 'source_file', 'compatibility')): continue
        if f.suffix == '.v' and f.parent.name != 'common' and not f.stem.startswith('Imported') and not AUDIT.search(f.stem) \
                and 'Inspection' not in f.stem and 'Scratch' not in f.stem and f.stem not in COMMONS:
            chain.append((f.stem, f))
        if f.suffix == '.vo' and f.stem.startswith('Imported') and f.stem != 'ImportedSubadditivity': vos.append(f)
    chain = list(dict(chain).items())
    vo = vos[0] if len({v.stem for v in vos}) == 1 else None
    summ = R.get(hs.get('assumption_summary_sha256'))
    folder = vo.parent if vo else (summ.parent if summ else None)
    if folder is not None:
        if vo is None:
            c = [g for g in folder.glob('Imported*.vo') if g.stem != 'ImportedSubadditivity'] or \
                [g for g in folder.glob('imported/Imported*.vo') if g.stem != 'ImportedSubadditivity']
            vo = c[0] if len({g.stem for g in c}) == 1 else None
        if vo is None and (folder / 'imported_vo.vo').exists():   # published under a generic name: find the real module
            h = sha((folder / 'imported_vo.vo').read_bytes())
            c = [g for g in list((V / '.work/experiments').glob('*/*/Imported*.vo')) + list((V / '.work/experiments').glob('*/Imported*.vo'))
                 if g.stat().st_size == (folder / 'imported_vo.vo').stat().st_size and sha(g.read_bytes()) == h]
            vo = c[0] if len({g.stem for g in c}) == 1 else None
        if not chain and (folder / 'certificates').is_dir():   # exact copies published with the file
            chain = [(g.stem, g) for g in (folder / 'certificates').glob('*.v')
                     if not (g.stem.startswith('Imported') or g.stem in COMMONS or AUDIT.search(g.stem))]
        if not chain:   # only the import is recorded: the folder's certificate modules are the roots
            for g in folder.glob('*.vo'):
                if g.stem.startswith('Imported') or g.stem in COMMONS or AUDIT.search(g.stem) or not vo: continue
                for d in (V / 'certificates').glob(f'*/{g.stem}.v'):
                    if imported_name(d.read_text()) in (vo.stem, None): chain.append((g.stem, d)); break
        if summ is None and (folder / 'assumption_summary.json').exists(): summ = folder / 'assumption_summary.json'
        if summ is None and (folder.parent / 'assumption_summary.json').exists(): summ = folder.parent / 'assumption_summary.json'
        if summ is None:
            c = sorted(folder.glob('*assumption_summary.json'))
            if len(c) == 1: summ = c[0]
    if not chain or vo is None or summ is None:
        raise LookupError(f'{src}: hash lookup incomplete (chain {len(chain)}, import {vo}, summary {summ})')
    folders = [d for d in {vo.parent, vo.parent / 'certificates', vo.parent.parent / 'certificates', summ.parent / 'certificates'} if d.is_dir()]
    chain = require_closure([f for _, f in chain], vo.stem, folders)
    return man, vo.parent, vo.stem, order_chain(chain), summ

def early_record(src):
    """(manifest, published folder, imported module, chain [(module, .v path)]) for an early (non-spec) file."""
    mans = [json.load(open(m)) for m in glob.glob(str(V / 'planning/v06_pipeline/*_module_manifest.json'))]
    man = [j for j in mans if j.get('source_file') == src and j.get('declarations')]
    if len(man) != 1: raise RuntimeError(f'{src}: {len(man)} manifests with declarations')
    man = man[0]
    stem = src[:-2].replace('/', '_')
    pubs = [d for d in (V / 'imported/translation_order').iterdir() if d.is_dir() and
            (d.name == stem or stem.endswith('_' + d.name)) and list(d.glob('Imported*.vo'))]
    h = man.get('assumption_summary_sha256') or man.get('artifact_hashes', {}).get('assumption_summary_sha256')
    exact = [d for d in pubs if (d / 'assumption_summary.json').exists() and sha((d / 'assumption_summary.json').read_bytes()) == h]
    pubs = exact or ([d for d in pubs if d.name == stem] or pubs)
    try: return early_record_by_hash(src, man)
    except LookupError as e:
        if len(pubs) != 1: raise RuntimeError(str(e))
    pub = pubs[0]
    imps = sorted(g.stem for g in pub.glob('Imported*.vo'))
    spec_dirs = {V / sp['cert_dir'] for sp in SPECS.values() if sp.get('cert_dir')}
    pool = {}
    for f in list((V / 'certificates').glob('*/*.v')) + list((V / '.work/experiments').glob('*/certificates/*.v')):
        if f.parent in spec_dirs or f.parent.name in ('common',) or f.parent.parent.name.startswith('classic'): continue
        pool.setdefault(f.stem, []).append(f)
    hashes = {v for k, v in {**man, **man.get('artifact_hashes', {})}.items() if isinstance(v, str) and k.endswith('sha256')}
    chain = []
    if (pub / 'certificates').is_dir():   # exact copies published with the file
        chain = [(f.stem, f) for f in sorted((pub / 'certificates').glob('*.v'))
                 if not (f.stem.startswith('Imported') or f.stem in COMMONS or AUDIT.search(f.stem))]
    for vo in ([] if chain else sorted(pub.glob('*.vo'))):
        m = vo.stem
        if m.startswith('Imported') or m in COMMONS or AUDIT.search(m): continue
        cands = [f for f in pool.get(m, []) if imported_name(f.read_text()) in set(imps) | {None}]
        texts = {}
        for f in cands: texts.setdefault(sha(f.read_bytes()), f)
        pick = [f for h2, f in texts.items() if h2 in hashes] or list(texts.values())
        if len({sha(norm(f.read_text(), False)) for f in pick}) != 1:
            raise RuntimeError(f'{src}: module {m}: {len(pick)} differing sources {[str(f.relative_to(V)) for f in pick][:4]}')
        chain.append((m, pick[0]))
    IN = imps[0] if len(imps) == 1 else next((i for i in imps if i != 'ImportedSubadditivity'), imps[0])
    return man, pub, IN, order_chain(chain), pub / 'assumption_summary.json'

COMPUTATIONAL = ('Definition', 'Fixpoint', 'Instance', 'Let', 'Canonical', 'Coercion')

def stage_generic(src, slug, decls, prods, imports, imp_dirs, lean_dir, summ, chain, extra_commons=(), imported_note=''):
    """Folders 1, 2, 3, 5 and meta.json for a file whose records are not a pipeline spec.
    decls: dicts with source_declaration, lean_declaration, kind, certificate and optionally import (module stem)."""
    F = OUT / 'files' / src[:-2]; C = CACHE / slug
    C.mkdir(parents=True, exist_ok=True)
    for sub in ('1_source_rocq', '2_translation_lean', '3_printed_declarations', '5_assumptions'):
        if (F / sub).exists(): shutil.rmtree(F / sub)
        (F / sub).mkdir(parents=True)
    shutil.copy2(OFFICIAL / src, F / '1_source_rocq' / Path(src).name)
    hunks = [part for pp in V.glob('patches/**/*.patch') for part in re.split(r'(?m)^(?=--- a/)', pp.read_text())
             if part.startswith(f'--- a/{src}\n')]
    if hunks: (F / '1_source_rocq' / (Path(src).stem + '_rocq93_compat.patch')).write_text(''.join(dict.fromkeys(hunks)))
    for prod in prods: shutil.copy2(P / prod, F / '2_translation_lean' / Path(prod).name)
    comp = {d['source_declaration'] for d in decls if d['kind'] in COMPUTATIONAL}

    L = ['From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.',
         f"From prosa Require Import {src[:-2].replace('/', '.')}.", 'Set Printing Width 110. Set Printing Implicit. Set Printing Coercions.']
    for d in decls:
        q = d['source_declaration']; n = q.split('.')[-1]
        L += [f'Goal True. idtac "=== {n} ===". Abort.', f'About {q}.', f'Check @{q}.']
        if q in comp: L += [f'Goal True. idtac "=== body of {n} ===". Abort.', f'Print {q}.']
    probe = '\n'.join(L) + '\n'; (C / 'OfficialPrint.v').write_text(probe)
    out = cached(C / 'official.out', probe, lambda: rocq('prosa-0.6', '', C / 'OfficialPrint.v', C))
    if 'Error' in out: raise RuntimeError(f'{src}: official print failed\n{out[-1200:]}')
    off = blocks(out)

    L = [f"import {prod[:-5].replace('/', '.')}" for prod in prods]
    for d in decls:
        L.append(f"#check @{d['lean_declaration']}")
        if d['source_declaration'] in comp: L.append(f"#print {d['lean_declaration']}")
    probe = '\n'.join(L) + '\n'; (C / 'LeanPrint.lean').write_text(probe)
    def run_lean(d):
        r = subprocess.run(['lean', str(C / 'LeanPrint.lean')], cwd=P, capture_output=True, text=True,
                           env={**os.environ, 'LEAN_PATH': lean_path(d)})
        return ('LEAN_FAILED\n' if r.returncode else '') + r.stdout + r.stderr
    out = 'LEAN_FAILED'
    rel = [prod[:-5] + '.olean' for prod in prods]
    runs = [Path('/nonexistent'), lean_dir, lean_dir.parent] + \
           sorted({o.parents[len(Path(rel[0]).parts) - 1].parent for o in (V / '.work/experiments').glob(f'*/olean/{rel[0]}')})
    for d in [d for i, d in enumerate(runs) if d not in runs[:i]]:   # the project build first, then run folders
        out = cached(C / 'lean.out', probe + str(d), lambda: run_lean(d))
        if not out.startswith('LEAN_FAILED'): break
    if out.startswith('LEAN_FAILED'): raise RuntimeError(f'{src}: lean print failed\n{out[-1200:]}')
    full = {d['lean_declaration']: d['source_declaration'].split('.')[-1] for d in decls}
    lean, cur = {}, None
    for line in out.splitlines():
        if not line.startswith(' '):
            m = re.match(r'^@?([\w\'.]+?)\.?(?:\{[^}]*\})? :', line) or \
                re.match(r'^(?:noncomputable |@\[[^\]]*\] |private |protected )*(?:def|theorem|instance|abbrev|structure|class|inductive|opaque) ([\w\'.]+)', line)
            if m and m.group(1) in full:
                cur = (full[m.group(1)], 'check' if ' :' in line[:len(m.group(0))] else 'print'); lean.setdefault(cur, [])
        if cur: lean[cur].append(line)
    lean = {k: '\n'.join(v).strip() for k, v in lean.items()}

    L = ['From LeanImport Require Import Lean.', f"From FoundationImported Require Import {' '.join(imports)}.",
         'Set Printing Width 110. Set Printing Implicit. Set Printing Coercions.']
    for d in decls:
        n = d['source_declaration'].split('.')[-1]; c = rq(d['lean_declaration']); I = d.get('import') or imports[0]
        L += [f'Goal True. idtac "=== {n} ===". Abort.', f'Check @{I}.{c}.']
        if d['source_declaration'] in comp: L += [f'Goal True. idtac "=== body of {n} ===". Abort.', f'Print {I}.{c}.']
    probe = '\n'.join(L) + '\n'; (C / 'ImportedPrint.v').write_text(probe)
    qs = ' '.join(f'-Q {d} FoundationImported' for d in dict.fromkeys(imp_dirs))
    out = cached(C / 'imported.out', probe + qs, lambda: rocq('rocq93rc1', f'-Q {IMP} LeanImport -I {IMP} {qs}', C / 'ImportedPrint.v', C))
    if 'Error' in out: raise RuntimeError(f'{src}: imported print failed\n{out[-1200:]}')
    imp = blocks(out)

    for d in decls:
        q = d['source_declaration']; n = q.split('.')[-1]
        parts = [f'# `{n}`', '', f"- Kind (Rocq): {d['kind']}", f'- Rocq: `{q}`', f"- Lean: `{d['lean_declaration']}`",
                 f"- Certificate: `{d['certificate']}`", '', '## Official Rocq', '', '```coq', off.get(n, '(not printed)'), '```']
        if f'body of {n}' in off: parts += ['', 'Body:', '', '```coq', off[f'body of {n}'], '```']
        parts += ['', '## Lean', '', '```lean', lean.get((n, 'check'), '(not printed)'), '```']
        if (n, 'print') in lean: parts += ['', 'Body:', '', '```lean', lean[(n, 'print')], '```']
        parts += ['', '## Lean, imported into Rocq', ''] + ([imported_note, ''] if imported_note else []) + \
                 ['```coq', hyg(imp.get(n, '(not printed)')), '```']
        if f'body of {n}' in imp: parts += ['', 'Body:', '', '```coq', hyg(imp[f'body of {n}']), '```']
        (F / f'3_printed_declarations/{n}.md').write_text('\n'.join(parts) + '\n')

    if isinstance(summ, dict): (F / '5_assumptions/assumption_summary.json').write_text(json.dumps(summ, indent=1) + '\n')
    else: shutil.copy2(summ, F / '5_assumptions/assumption_summary.json')
    if (C / 'chain').exists(): shutil.rmtree(C / 'chain')
    (C / 'chain').mkdir()
    for m, f in chain: shutil.copy2(f, C / 'chain' / f'{m}.v')
    ifaces = sorted({fx for _, f in chain for fx in re.findall(r'\b(\w+ComputationInterface)\b', f.read_text())
                     if (V / f'fixtures/translation_order/{fx}.lean').exists()})
    meta = {'src': src, 'rank': ORDER[src], 'ns': '.'.join(decls[0]['lean_declaration'].split('.')[:-1]),
            'imported': imports[0], 'chain': [m for m, _ in chain], 'interfaces': ifaces,
            'decls': [{'name': d['source_declaration'].split('.')[-1], 'kind': d['kind'], 'cert': d['certificate'],
                       'lean': d['lean_declaration']} for d in decls],
            'cats': categories(F / '5_assumptions/assumption_summary.json'), 'roles': {},
            'commons': sorted({c for _, f in chain for c in commons_of(f.read_text())} | set(extra_commons))}
    json.dump(meta, open(C / 'meta.json', 'w'), indent=1)
    print(f'staged {src}: {len(decls)} declarations, {len(chain)} chain modules', flush=True)

def stage_early(src):
    man, pub, IN, chain, summ = early_record(src)
    cert_of = lambda d: d.get('certificate') or d.get('semantic_certificate') or \
        ', '.join(d.get('certificates') or d.get('certificate_bundle') or [])
    inv_kind = {r['qualified_name']: r['kind'] for r in INV if r['source_file'] == src}
    decls = []
    for d in man['declarations']:
        q = d.get('source_declaration') or d['rocq_declaration']
        decls.append({**d, 'source_declaration': q, 'certificate': cert_of(d),
                      'kind': d.get('kind') or d.get('source_kind') or inv_kind.get(q, '')})
    commons = {g.stem for g in [*pub.glob('*.vo'), *pub.glob('certificates/*.vo')] if g.stem in COMMONS}
    imp_dir = next((V / '.work/experiments').glob(f'*/*/{IN}.vo'), None) if not (pub / f'{IN}.vo').exists() else pub / f'{IN}.vo'
    imp_dir = imp_dir.parent if imp_dir else pub
    prod = man.get('production_file')
    if not prod:   # derive from the Lean namespace of the declarations
        ns = decls[0]['lean_declaration'].split('.')
        prod = next('/'.join(ns[:k]) + '.lean' for k in range(len(ns) - 1, 1, -1) if (P / ('/'.join(ns[:k]) + '.lean')).exists())
    slug = 'early_' + src[:-2].replace('/', '_')
    if not Path(summ).exists():   # a summary published under a variant name
        c = [f for f in Path(summ).parent.glob('*assumption_summary*.json') if 'adapter' not in f.name]
        if len(c) == 1: summ = c[0]
    if not Path(summ).exists():   # audits recorded per declaration in the manifest
        audits = {}
        for d in man['declarations']:
            a = d.get('assumption_audit')
            if isinstance(a, dict): audits[a.get('certificate') or d.get('certificate')] = a
        if not audits: raise RuntimeError(f'{src}: no assumption summary or per-declaration audit records')
        summ = {'audit_policy': 'fail_closed', 'certificates': audits}
    try:
        stage_generic(src, slug, decls, [prod], [IN], [imp_dir], pub, summ, chain, commons)
    except RuntimeError as e:
        if 'inconsistent assumptions' not in str(e): raise
        RI = reimport(src, {IN: imp_dir}, CACHE / slug / 'reimport')
        stage_generic(src, slug, decls, [prod], [IN], [RI], pub, summ, chain, commons)

FOUNDATION_MANIFESTS = ['foundation_slice_1_manifest', 'foundation_slice_2_manifest', 'foundation_slice_2_closure_manifest',
                        'utility_foundation_expansion_manifest']

def foundation_decls(src):
    """Per-declaration records of a foundation file; later manifests override earlier ones."""
    out = {}
    for name in FOUNDATION_MANIFESTS:
        j = json.load(open(V / f'planning/v06_pipeline/{name}.json'))
        rows = list(j.get('declarations', [])) + [d for c in j.get('clusters', []) for d in c.get('declarations', [])]
        for d in rows:
            fsrc = d.get('source_file') or ('behavior/time.v' if name == 'foundation_slice_1_manifest' else None)
            if fsrc != src: continue
            rec = dict(d, manifest=name)
            prev = out.get(d['rocq_declaration'])
            if prev is None or prev.get('acceptance') != 'ACCEPTED_V06_TRANSLATION' or d.get('acceptance') == 'ACCEPTED_V06_TRANSLATION':
                out[d['rocq_declaration']] = rec
    return list(out.values())

def reimport(src, imports, RI):
    """Import the published Lean exports again, unchanged, with the current importer (for printing only): some
    published .vo files were compiled with an earlier importer build and can no longer be loaded."""
    RI.mkdir(parents=True, exist_ok=True)
    for I, d in imports.items():
        d = next(x for x in (d, V / 'imported/foundation_slice_2', V / 'imported/utility_foundation') if (x / f'{I}.v').exists())
        wrapper = (d / f'{I}.v').read_text()
        for out_name in re.findall(r'Lean Import "([^"]+)"', wrapper): shutil.copy2(d / out_name, RI / Path(out_name).name)
        (RI / f'{I}.v').write_text(wrapper)
        if not (RI / f'{I}.vo').exists():
            r = rocq('rocq93rc1', f'-Q {IMP} LeanImport -I {IMP} -Q . FoundationImported', RI / f'{I}.v', RI)
            if not (RI / f'{I}.vo').exists(): raise RuntimeError(f'{src}: re-import of {I} failed\n{r[-800:]}')
    return RI

def stage_foundation(src):
    R = by_raw()
    recs = foundation_decls(src)
    if not recs: raise RuntimeError(f'{src}: no foundation records')
    decls, imports, roots, audits, prods = [], {}, {}, {}, []
    for d in recs:
        cert = d.get('certificate') or ', '.join(d.get('certificates', []) if isinstance(d.get('certificates'), list) else [])
        vo = R.get(d.get('imported_vo_sha256') or '')
        if vo is None and d['manifest'] == 'foundation_slice_1_manifest':
            vo = V / 'imported/foundation_slice_1/ImportedTime.vo'
        if vo is None: raise RuntimeError(f"{src}: {d['rocq_declaration']}: imported module not found")
        if not vo.stem.startswith('Imported'):   # a published copy under another name: find the module
            c = [g for g in (V / 'imported').glob('*/Imported*.vo') if sha(g.read_bytes()) == d.get('imported_vo_sha256')]
            vo = c[0]
        imports[vo.stem] = vo.parent
        cf = R.get(d.get('certificate_source_sha256') or '')
        if cf is not None and cf.suffix == '.v': roots[cf.stem] = cf
        a = d.get('assumption_audit')
        if isinstance(a, dict): audits[a.get('certificate') or cert] = a
        elif isinstance(a, str):   # behavior/time.v: a status plus the record's own foundation fields
            for c1 in (d.get('certificates') or [cert]):
                audits[c1] = {'certificate': c1, 'status': a, 'prop_sprop_foundation': d.get('prop_sprop_foundation', []),
                              'importer_foundation': d.get('allowed_importer_foundation', []),
                              'semantic_premises': d.get('semantic_premises', []), 'rocq_sprop_definitional_uip': []}
        elif isinstance(a, list):
            for x in a:
                if isinstance(x, dict): audits[x.get('certificate') or cert] = x
        lf = d.get('lean_file') or 'Prosa/Behavior/Time.lean'
        if lf not in prods: prods.append(lf)
        decls.append({'source_declaration': d['rocq_declaration'], 'lean_declaration': d['lean_declaration'],
                      'kind': d['kind'], 'certificate': cert, 'import': vo.stem})
    if src == 'behavior/time.v': roots['FoundationTimeCertificate'] = V / 'certificates/foundation_slice_1/FoundationTimeCertificate.v'
    if not roots: raise RuntimeError(f'{src}: no certificate sources found')
    main = next(iter(imports))
    chain = require_closure(list(roots.values()), main, [V / 'certificates/utility_foundation',
                            V / 'certificates/foundation_slice_2', V / 'certificates/foundation_slice_2_closure'])
    extra = {m for m, _ in chain if m in COMMONS}
    chain = [(m, f) for m, f in chain if m not in COMMONS]
    summ = {'audit_policy': 'fail_closed', 'certificates': audits}
    # The published .vo files predate the current importer build, so each published export is imported again,
    # unchanged, in the cache folder; only the printing uses these copies.
    slug = 'foundation_' + src[:-2].replace('/', '_')
    RI = reimport(src, imports, CACHE / slug / 'reimport')
    stage_generic(src, slug, decls, prods, list(imports), [RI], V / 'imported/utility_foundation', summ, chain, extra)

def stage_zero(src):
    """A file with no public declarations: it is accepted as a whole (notations, local instances, re-exports)."""
    mans = [(Path(m), json.load(open(m))) for m in glob.glob(str(V / 'planning/v06_pipeline/*_module_manifest.json'))]
    man_path, man = next((pth, j) for pth, j in mans if j.get('source_file') == src)
    F = OUT / 'files' / src[:-2]; C = CACHE / ('zero_' + src[:-2].replace('/', '_'))
    C.mkdir(parents=True, exist_ok=True)
    for sub in ('1_source_rocq', '2_translation_lean', '3_printed_declarations', '5_assumptions'):
        if (F / sub).exists(): shutil.rmtree(F / sub)
    for sub in ('1_source_rocq', '2_translation_lean'): (F / sub).mkdir(parents=True)
    shutil.copy2(OFFICIAL / src, F / '1_source_rocq' / Path(src).name)
    hunks = [part for pp in V.glob('patches/**/*.patch') for part in re.split(r'(?m)^(?=--- a/)', pp.read_text())
             if part.startswith(f'--- a/{src}\n')]
    if hunks: (F / '1_source_rocq' / (Path(src).stem + '_rocq93_compat.patch')).write_text(''.join(dict.fromkeys(hunks)))
    if man.get('production_file'): shutil.copy2(P / man['production_file'], F / '2_translation_lean' / Path(man['production_file']).name)
    chain, summ = [], None
    try: _, _, _, chain, summ = early_record_by_hash(src, man)
    except LookupError:   # no import or summary recorded: the certificates the manifest hashes, and their Requires
        R = by_raw(); hs = {**{k: v for k, v in man.items() if isinstance(v, str)}, **man.get('artifact_hashes', {})}
        roots = {R[h].stem: R[h] for k, h in hs.items() if isinstance(h, str) and h in R and R[h].suffix == '.v'
                 and not k.startswith(('production', 'official', 'source_file', 'compatibility'))
                 and R[h].parent.name != 'common' and not R[h].stem.startswith('Imported') and not AUDIT.search(R[h].stem)}
        if roots:
            IN = next((imported_name(f.read_text()) for f in roots.values() if imported_name(f.read_text())), None)
            chain = require_closure(list(roots.values()), IN, sorted({f.parent for f in roots.values()}))
        summ = R.get(hs.get('assumption_summary_sha256') or '')
    cats = None
    if summ is None and isinstance(man.get('assumption_audit'), dict) and chain:
        a = man['assumption_audit']
        summ = {'audit_policy': 'fail_closed',
                'certificates': a.get('certificates') if isinstance(a.get('certificates'), dict) else {a.get('certificate', 'module'): a}}
    if summ is not None:
        (F / '5_assumptions').mkdir(parents=True)
        if isinstance(summ, dict): (F / '5_assumptions/assumption_summary.json').write_text(json.dumps(summ, indent=1) + '\n')
        else: shutil.copy2(summ, F / '5_assumptions/assumption_summary.json')
        cats = categories(F / '5_assumptions/assumption_summary.json')
    if (C / 'chain').exists(): shutil.rmtree(C / 'chain')
    (C / 'chain').mkdir()
    for m, f in chain: shutil.copy2(f, C / 'chain' / f'{m}.v')
    helpers = [d.get('source_declaration', '').split('.')[-1] for d in man.get('declarations') or []]
    note = ('This file has no public declarations in the v0.6 declaration inventory: it declares notations, local '
            'instances or re-exports other modules. It was accepted as a whole file.')
    if helpers: note += ' Its local ' + ', '.join(f'`{h}`' for h in helpers) + ' is certified by the certificates below, as a helper that is not counted.'
    if man.get('goal_count'):
        n = man['goal_count']
        note = (f'This file declares no named objects: it contains {n} anonymous example goals. They are accepted in '
                'goal-only mode: the official module, unchanged, is compiled together with the official Prosa files it '
                f'depends on, and the Lean translations `goal_1` … `goal_{n}` are checked by compilation and by the audit '
                'of the axioms they use.')
    meta = {'src': src, 'rank': ORDER[src], 'ns': '', 'imported': '', 'chain': [m for m, _ in chain], 'interfaces': [],
            'decls': [], 'cats': cats, 'roles': {}, 'note': note,
            'commons': sorted({c for _, f in chain for c in commons_of(f.read_text())})}
    json.dump(meta, open(C / 'meta.json', 'w'), indent=1)
    print(f'staged {src}: no declarations, {len(chain)} chain modules', flush=True)

# ---------------------------------------------------------------- finalize
def finalize():
    metas = {}
    for mp in sorted(CACHE.glob('*/meta.json')):
        m = json.load(open(mp)); m['dir'] = mp.parent; m['rank'] = ORDER[m['src']]; metas[m['src']] = m   # one rank per file: the translation order
    # group module texts across files (strict = only imported module name differs; loose = also Require lines)
    groups = {}
    for src, m in metas.items():
        for mod in m['chain']:
            t = (m['dir'] / 'chain' / f'{mod}.v').read_text()
            groups.setdefault(sha(norm(t, True)), []).append((m['rank'], src, mod, t))
    sharedfile = {}
    if (OUT / 'shared/certificates').exists():
        for d in (OUT / 'shared/certificates').iterdir():
            if d.name != 'common': shutil.rmtree(d) if d.is_dir() else d.unlink()
    shared_rows = []
    PIDX = project_index()
    multi = []
    for h, members in groups.items():
        if len({x[1] for x in members}) < 2: continue
        members.sort()
        cands = PIDX.get(h) or []
        if cands:
            orank, osrc, opath = cands[0]
            if orank > members[0][0]: orank, osrc, opath = members[0][0], members[0][1], None
        else:
            orank, osrc, opath = members[0][0], members[0][1], None
        if opath: otext, omod = (V / opath).read_text(), Path(opath).stem
        else: otext, omod = members[0][3], members[0][2]
        multi.append((orank, osrc, omod, otext, members))
    multi.sort(key=lambda x: (x[0], x[2]))
    taken = {}
    (OUT / 'shared/certificates').mkdir(parents=True, exist_ok=True)
    for orank, osrc, omod, t0, members in multi:
        taken[omod] = taken.get(omod, 0) + 1
        name = f'{omod}.v' if taken[omod] == 1 else f'{omod}-{taken[omod]}.v'
        (OUT / 'shared/certificates' / name).write_text(t0)
        for _, src, mod, t in members:
            sub = []
            imps = lambda x: [w for g in re.findall(r'From\s+FoundationImported\s+Require\s+Import([^.]*)\.', x) for w in g.split()
                              if w != 'ImportedSubadditivity']
            certs = lambda x: re.sub(r'\s+', ' ', ' '.join(re.findall(r'From\s+FoundationCertificates\s+Require\s+(?:Import|Export)([^.]*)\.', x))).strip()
            a, b = imps(t0), imps(t)
            if a != b: sub.append(f"`{' '.join(a)}` → `{' '.join(b)}`")
            if certs(t0) != certs(t): sub.append('certificate module names in `Require` lines renamed')
            if mod != omod: sub.append(f'module named `{mod}`')
            sharedfile[(src, mod)] = (name, '; '.join(sub) or 'none')
        shared_rows.append({'shared file': f'certificates/{name}', 'origin': osrc,
                            'imported module in this copy': imported_name(t0) or '',
                            'used by': '; '.join(sorted({x[1] for x in members}, key=lambda s: metas[s]['rank'])),
                            'file names in using files': '; '.join(
                                f"{n}: " + ', '.join(sorted({x[1] for x in members if x[2] == n}, key=lambda q: metas[q]['rank']))
                                for n in sorted({x[2] for x in members},
                                                key=lambda n: (min(metas[x[1]]['rank'] for x in members if x[2] == n), n))),
                            'sha256': sha(t0), 'description': first_sentence(t0)})
    # common modules, interfaces
    used_common, used_iface = {}, {}
    for src, m in metas.items():
        for mod in m['chain']:
            for c in commons_of((m['dir'] / 'chain' / f'{mod}.v').read_text()): used_common.setdefault(c, set()).add(src)
        for c in m.get('commons', []): used_common.setdefault(c, set()).add(src)
        for c in m['chain']:   # a name the file's own chain defines refers to that copy, not the common module
            if c in used_common: used_common[c].discard(src)
        for x in m['interfaces']: used_iface.setdefault(x, set()).add(src)
    if (OUT / 'shared/lean_interfaces').exists(): shutil.rmtree(OUT / 'shared/lean_interfaces')
    (OUT / 'shared/lean_interfaces').mkdir(parents=True)
    for x in used_iface: shutil.copy2(V / f'fixtures/translation_order/{x}.lean', OUT / 'shared/lean_interfaces' / f'{x}.lean')
    for c in used_common: shutil.copy2(V / f'certificates/common/{c}.v', OUT / 'shared/certificates/common' / f'{c}.v')
    for f in (OUT / 'shared/certificates/common').iterdir():
        if f.stem not in used_common: f.unlink()

    fmt = lambda xs: ', '.join(f'`{x}`' for x in xs) or '—'
    for src, m in metas.items():
        F = OUT / 'files' / src[:-2]; R = '../' * (len(Path(src).parts) + 2) + 'shared/'
        if (F / '4_correspondence').exists(): shutil.rmtree(F / '4_correspondence')
        (F / '4_correspondence').mkdir(parents=True)
        own, shared = [], []
        for mod in m['chain']:
            t = (m['dir'] / 'chain' / f'{mod}.v').read_text()
            if (src, mod) in sharedfile: shared.append((mod,) + sharedfile[(src, mod)])
            else:
                (F / f'4_correspondence/{mod}.v').write_text(t)
                own.append((mod, first_sentence(t)))
        commons = sorted(c for c, users in used_common.items() if src in users)
        sm = ['# Shared modules used by this file', '', f'See [`shared/README.md`]({R}README.md).']
        if commons:
            sm += ['', '## Common certificates', '', '| Module | Shared file |', '|---|---|'] + \
                  [f'| `{c}` | [`certificates/common/{c}.v`]({R}certificates/common/{c}.v) |' for c in commons]
        if shared:
            sm += ['', '## Shared certificates', '', '| Module | Shared file | Differences in this file |', '|---|---|---|'] + \
                  [f'| `{mod}` | [`certificates/{name}`]({R}certificates/{name}) | {sub} |' for mod, name, sub in shared]
        if m['interfaces']:
            sm += ['', '## Lean interfaces', '', '| Interface | Shared file |', '|---|---|'] + \
                  [f'| `{x}` | [`lean_interfaces/{x}.lean`]({R}lean_interfaces/{x}.lean) |' for x in m['interfaces']]
        (F / '4_correspondence/shared.md').write_text('\n'.join(sm) + '\n')
        short = lambda x: x
        rd = [f'# `{src}`', '']
        if m['decls']:
            rd += ['| Rocq declaration | Kind | Lean declaration | Certificate | Printed |', '|---|---|---|---|---|']
            rd += [f"| `{d['name']}` | {d['kind']} | `{d.get('lean') or m['ns'] + '.' + d['name']}` | `{d['cert']}` | [view](3_printed_declarations/{d['name']}.md) |"
                   for d in m['decls']]
        else:
            rd += [m.get('note', 'This file has no public declarations.')]
        rd += ['', '## Certificates', '']
        if not m['chain'] and not m['decls'] and not commons:
            rd += ['None.']
        elif own:
            rd += ['| Module | Role |', '|---|---|'] + \
                  [f"| [`{mod}`](4_correspondence/{mod}.v) | {role.replace('|', chr(92) + '|')} |" for mod, role in own]
        else:
            rd += ['None: every certificate module this file uses is shared.']
        if m['chain'] or commons or m['interfaces']:
            rd += ['', 'Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).']
        if not (m['chain'] or commons or m['interfaces']): shutil.rmtree(F / '4_correspondence')
        if not m['cats']:
            (F / 'README.md').write_text('\n'.join(rd + ['', '## Assumptions', '', 'None: there is no certificate to audit.']) + '\n')
            continue
        rd += ['', '## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))', '', '| Category | Items |', '|---|---|']
        # Print Assumptions lists Lean's three axioms as axioms; everything else an audit filed as importer foundation
        # (eq, True, HEq, ...) is reported as "... relies on definitional UIP", so it belongs to that row.
        c = m['cats']; imp = c['importer_foundation']
        prim = [x for x in imp if x.startswith('PrimInt63')]
        axioms = [x for x in imp if x in LEAN_AXIOMS]
        uip = sorted({x.replace(' relies on definitional UIP', '') for x in imp if x not in LEAN_AXIOMS and not x.startswith('PrimInt63')}
                     | set(c['rocq_sprop_definitional_uip']))
        rd += [f"| Prop/SProp foundation | {fmt(c['prop_sprop_foundation'])} |", f"| Imported Lean axioms | {fmt(axioms)} |",
               f"| Definitional UIP | {fmt(uip)} |", f"| Rocq primitives | {'`PrimInt63.*`' if prim else '—'} |"]
        (F / 'README.md').write_text('\n'.join(rd) + '\n')

    def write_csv(path, rows, cols):
        with open(path, 'w', newline='') as f:
            w = csv.DictWriter(f, fieldnames=cols); w.writeheader(); w.writerows(rows)
    shared_rows.sort(key=lambda r: r['shared file'])
    write_csv(OUT / 'shared/certificates.csv', shared_rows,
              ['shared file', 'origin', 'imported module in this copy', 'used by', 'file names in using files', 'sha256', 'description'])
    write_csv(OUT / 'shared/lean_interfaces.csv',
              [{'interface': f'lean_interfaces/{x}.lean', 'used by': '; '.join(sorted(u, key=lambda s: metas[s]['rank'])),
                'description': lean_desc((V / f'fixtures/translation_order/{x}.lean').read_text())}
               for x, u in sorted(used_iface.items())], ['interface', 'used by', 'description'])
    common_desc = {'PropSPropFoundation': '`PropSPropRel`, which pairs a Rocq `Prop` with an imported Lean `SProp`, with maps in both directions; also the single foundation axiom `interpret_strict`',
                   'LogicalRelation': 'The introduction rule for `PropSPropRel`',
                   'SubadditivityNatCorrespondence': '`SubNatRel`, relating Rocq `nat` and Lean `Nat`, with `+`, `*`, `≤`, `<` and `=`'}
    def _names(r): return [part.split(':', 1) for part in r['file names in using files'].split('; ')]
    ex_row = max(shared_rows, key=lambda r: (-abs(len(_names(r)) - 3), len(r['used by'].split('; ')), r['shared file'])) \
        if shared_rows else None
    ex_lines = []
    if ex_row:
        for n, fs in _names(ex_row):
            fs = [f.strip() for f in fs.split(',')]
            ex_lines.append(f"{n}: {', '.join(fs[:3])}" + (f', … ({len(fs) - 3} more)' if len(fs) > 3 else '') + ';')
        ex_lines[-1] = ex_lines[-1].rstrip(';')
    L = ['# Shared modules', '', "Modules used by more than one file. Each file's `4_correspondence/shared.md` lists the ones it uses.", '',
         '## Common certificates: [`certificates/common/`](certificates/common/)', '',
         "These modules do not mention any particular file's Lean declarations, so every file uses them unchanged.", '',
         '| Module | Content |', '|---|---|']
    L += [f"| [`{c}.v`](certificates/common/{c}.v) | {common_desc.get(c) or first_sentence((V / f'certificates/common/{c}.v').read_text())} |"
          for c in sorted(used_common)]
    L += ['', '## Shared certificates: [`certificates/`](certificates/)', '',
          "These modules state relations about imported Lean definitions. A module is placed here **only if at least two "
          "files of this folder use it**; a module used by a single file stays in that file's `4_correspondence/` folder.", '',
          "Each translated file's Lean code is imported into Rocq as its own module, so a module used by several files "
          "mentions a different imported module in each. Each shared certificate has an **origin**: the first file, in the "
          "order of the file dependency graph (the translation order), whose certificates contain this text anywhere in "
          "the project. The text is stored once, as it appears in its origin. A file that uses it may differ only in the "
          "imported module name, the certificate module names in its `Require` lines, or the module's own name; "
          "that file's `shared.md` lists which. During validation "
          "each file's copy is compiled against that file's own import, so its proofs are checked again for every file.", '',
          '**Naming.** A shared file is named after its module (`ArrivalsSeqOperations.v`). The same module name can have '
          'several different texts: when a later file reused a module but had to edit it (for example, cut parts that '
          'mention definitions its export does not contain, or add a helper it needs), the edited copy kept the original '
          "name. Storing both under one name would overwrite one with the other, so a file would link to a text it was "
          'never compiled with. The text whose origin comes first in dependency order keeps the plain name; '
          'later different texts are numbered `-2`, `-3`, … (`FactsEdfOptCorrespondence-2.v`).', '',
          '[`certificates.csv`](certificates.csv) lists every shared certificate, one row per file:', '',
          '| Column | Meaning |', '|---|---|',
          '| `shared file` | Path of the stored module, relative to this folder |',
          '| `origin` | The first file, in dependency-graph order, whose certificates contain this text (across the whole project; it may be a file not yet in this folder) |',
          '| `imported module in this copy` | The Lean code this stored text is about: its line `From FoundationImported Require Import <module>` loads the origin file\'s Lean translation into Rocq, and the proofs relate to those definitions. A file that reuses the certificate replaces this name with its own imported module (e.g. `ImportedService` becomes `ImportedFinishTime` in `analysis/definitions/finish_time.v`); its `shared.md` shows the replacement |',
          '| `used by` | The files of this folder whose certificate chains use it, by rank, separated by `;` |',
          '| `file names in using files` | Under which file name (without `.v`) each using file keeps its copy, as `name: files`, separated by `;`. In Rocq a module is one `.v` file, and other files load it by its file name |',
          '| `sha256` | SHA-256 of the stored file, to check which exact text it is |',
          '| `description` | The first sentence of the module\'s own opening comment |',
          '',
          '**`used by` and `file names in using files`.** `used by` lists *which files* use the certificate; '
          '`file names in using files` says *what each of them calls its copy*. Each file keeps its own copy, and some '
          'saved it under another file name. The different names are only a naming convention from translation (a '
          'reusing file prefixed its copies with its own short name, e.g. `Jitter`, `Ps`), not a requirement: each file '
          'is validated in its own folder, so the original name would have worked as well. Example, the row of '
          f'[`{ex_row["shared file"]}`]({ex_row["shared file"]}) (origin `{ex_row["origin"]}`):', '',
          '```text'] + ex_lines + ['```', '',
          'The same pairing appears in each using file\'s `4_correspondence/shared.md`, in its `Module` column.',
          '', '## Lean interfaces: [`lean_interfaces/`](lean_interfaces/)', '',
          "Validation-only Lean equations and definitions, proved in Lean and exported with their proofs, that several files' "
          "exports include. Each interface used by at least one file of this folder is stored once.", '',
          '[`lean_interfaces.csv`](lean_interfaces.csv) lists them, one row per interface:', '',
          '| Column | Meaning |', '|---|---|',
          '| `interface` | Path of the Lean file, relative to this folder |',
          '| `used by` | The files of this folder whose exports include it, by rank, separated by `;` |',
          '| `description` | The interface\'s module comment; if it has none, its first doc comment; if it has neither, a '
          'generated summary: the Prosa module it is about, how many equations or definitions it contains, and their names |']
    (OUT / 'shared/README.md').write_text('\n'.join(L) + '\n')

    files = sorted(metas, key=lambda k: metas[k]['rank'])
    (OUT / 'FILES.md').write_text(
        '# Files\n\nRank is the position in the file dependency order (the translation order).\n\n'
        '| Rank | File | Declarations |\n|---|---|---|\n' +
        '\n'.join(f"| {metas[f]['rank']} | [`{f}`](files/{f[:-2]}/README.md) | {len(metas[f]['decls'])} |" for f in files) + '\n')
    p = OUT / 'README.md'; t = p.read_text()
    covered = (f'[`FILES.md`](FILES.md) lists all {len(files)} files, with links to their folders.' if len(files) == len(ORDER)
               else f'[`FILES.md`](FILES.md) lists the files covered so far ({len(files)}), with links to their folders.')
    t = re.sub(r'(?m)^\[`FILES\.md`\]\(FILES\.md\) lists .*$', covered, t)
    t = t.replace('the files covered so far, with links', 'every file, with links' if len(files) == len(ORDER) else 'the files covered so far, with links')
    p.write_text(t)
    a, b = '<!-- FILES_BEGIN -->', '<!-- FILES_END -->'
    if a in t:
        t = t[:t.index(a)] + f'[`FILES.md`](FILES.md) lists the files covered so far ({len(files)}), with links to their folders.\n' + \
            t[t.index(b) + len(b) + 1:]
        p.write_text(t)
    with open(OUT / 'SHA256SUMS', 'w') as f:
        for q in sorted(OUT.rglob('*')):
            if q.is_file() and q.name not in ('SHA256SUMS', '.DS_Store'):
                f.write(f'{sha(q.read_bytes())}  ./{q.relative_to(OUT)}\n')
    print(f'finalized: {len(metas)} files, {len(shared_rows)} shared certificate texts, {len(used_iface)} interfaces')

if __name__ == '__main__':
    args = sys.argv[1:]
    if args and args[0] in ('stage', 'early', 'foundation', 'zero'):
        fn = {'stage': stage, 'early': stage_early, 'foundation': stage_foundation, 'zero': stage_zero}[args[0]]
        for sl in args[1:]:
            if sl == 'finalize': continue
            try: fn(sl); print('STAGED', sl, flush=True)
            except Exception as e:
                import traceback; print('FAILED', sl, repr(e)[:300], flush=True); traceback.print_exc()
    if 'finalize' in args: finalize()
