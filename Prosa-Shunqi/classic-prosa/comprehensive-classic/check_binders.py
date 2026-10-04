#!/usr/bin/env python3
"""Compare the binder lists of every TRANSLATED Lean target with the Rocq contract.

For each declaration listed in `contracts/<file>.txt` (`Arguments` lines), the Lean declaration's binder names
(explicit `(x : T)` as `x`, implicit `{x : T}` as `{x}`, instance binders skipped) must be a prefix of the
contract's argument list (the contract may continue with the names of the statement's own universally quantified
variables); every other declaration printed by `Print Module` must exist by name.
Usage: python3 check_binders.py [SOURCE ...]   (default: all TRANSLATED files)

Documented exclusions (see README): Rocq's auto-generated eliminators (`_rect`, `_ind`, `_rec`, `_sind`) and
Hierarchy-Builder artifacts (`HB_unnamed_*`, `*__canonical__*`) are not restated; structure fields are matched by
name only; a Lean binder `x0` standing for a repeated Rocq binder name `x` (Rocq allows the duplicate, Lean does not)
is accepted.
"""
import csv, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
PAIRS = {'(': ')', '{': '}', '[': ']', '⟨': '⟩'}


def match_group(text, i):
    d = 0
    j = i
    while j < len(text):
        if text[j] in PAIRS:
            d += 1
        elif text[j] in PAIRS.values():
            d -= 1
        if d == 0:
            return j + 1
        j += 1
    return len(text)


def lean_binders(path):
    s = open(path).read()
    out = {}
    for m in re.finditer(r'^(theorem|def|abbrev|inductive|structure) (\S+)', s, re.M):
        i = m.end()
        names = []
        while i < len(s):
            while i < len(s) and s[i].isspace():
                i += 1
            if i < len(s) and s[i] in '({[':
                e = match_group(s, i)
                inner = s[i + 1:e - 1]
                if s[i] != '[' and ':' in inner:
                    ns = inner.split(':')[0].split()
                    names += [('{' + n + '}' if s[i] == '{' else n) for n in ns]
                i = e
            else:
                break
        out[m.group(2)] = names
    # structure fields (matched by name only)
    for m in re.finditer(r'^structure (\S+)[^\n]*where\n((?:  [^\n]*\n)+)', s, re.M):
        for f in re.finditer(r'^  (?:\(?)(\w+)\s*:', m.group(2), re.M):
            out.setdefault(f.group(1), None)
    return out


EXCLUDED = re.compile(r'(_rect|_ind|_rec|_sind)$|^HB_unnamed|__canonical__')


def same_modulo_renamed_duplicates(lean, contract):
    if len(contract) < len(lean):
        return False
    for i, (a, b) in enumerate(zip(lean, contract)):
        if a == b:
            continue
        if a == b + '0' and b in contract[:i]:
            continue
        return False
    return True


def contract_names(path):
    """Names of all declarations printed by `Print Module` (Parameter/Definition/Inductive/Record/...)."""
    names = []
    for line in open(path):
        m = re.match(r'^\s+(?:Parameter|Definition|Inductive|CoInductive|Record|Fixpoint) ([^\s:]+)', line)
        if m:
            names.append(m.group(1))
    return names


def contract_args(path):
    res = {}
    for line in open(path):
        if not line.startswith('Arguments'):
            continue
        line = re.sub(r'%[a-z_]+', '', line.strip())
        toks = line.split()[1:]
        name = toks[0].split('.')[-1]
        out = []
        for g in re.findall(r'\{[^}]*\}|\([^)]*\)|\S+', ' '.join(toks[1:])):
            if g.startswith('{'):
                out += ['{' + x + '}' for x in g[1:-1].split()]
            elif g.startswith('('):
                out += g[1:-1].split()
            else:
                out.append(g)
        res[name] = out
    return res


def main():
    rows = list(csv.DictReader(open(os.path.join(HERE, 'file_order.csv'))))
    wanted = set(sys.argv[1:])
    bad = checked = 0
    for r in rows:
        if wanted and r['source'] not in wanted:
            continue
        if not wanted and r['status'] != 'TRANSLATED':
            continue
        cname = r['source'][len('classic/'):-2].replace('/', '__') + '.txt'
        cpath = os.path.join(HERE, 'contracts', cname)
        lpath = os.path.join(ROOT, r['lean_target'])
        if not os.path.exists(cpath) or not os.path.exists(lpath):
            print('SKIP (no contract or target)', r['source'])
            continue
        L = lean_binders(lpath)
        args_of = contract_args(cpath)
        for name in contract_names(cpath):
            if name not in args_of and not EXCLUDED.search(name):
                checked += 1
                if name not in L:
                    print('MISSING', r['source'], name)
                    bad += 1
        for name, args in args_of.items():
            checked += 1
            if EXCLUDED.search(name):
                continue
            if name not in L:
                print('MISSING', r['source'], name)
                bad += 1
            elif L[name] is None:
                continue
            elif not same_modulo_renamed_duplicates(L[name], args):
                print('MISMATCH', r['source'], name)
                print('   lean    ', L[name])
                print('   contract', args)
                bad += 1
    print(f'CHECKED {checked} declarations, {bad} problems')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
