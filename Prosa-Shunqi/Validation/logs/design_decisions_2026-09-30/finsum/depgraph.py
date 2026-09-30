"""Parse a legacy lean4export .out and build a declaration dependency graph.
usage: depgraph.py OUT [--path FROM_PREFIX TO_NAME] [--entry PREFIX]"""
import sys, collections
sys.setrecursionlimit(100000)
out = sys.argv[1]
names = {0: ""}
exprs = {}
decls = {}  # name -> list of expr ids
kind = {}
ctor_of = {}
def nm(i): return names[int(i)]
with open(out) as f:
    for line in f:
        p = line.split()
        if not p: continue
        if p[0].startswith('#'):
            k = p[0]
            if k == '#DEF':
                n = nm(p[1]); decls[n] = [int(p[2]), int(p[3])]; kind[n] = 'DEF'
            elif k == '#AX':
                n = nm(p[1]); decls[n] = [int(p[2])]; kind[n] = 'AX'
            elif k == '#IND':
                nparams, n, ty, nc = int(p[1]), nm(p[2]), int(p[3]), int(p[4])
                es = [ty]
                for c in range(nc):
                    cn = nm(p[5 + 2 * c]); es.append(int(p[6 + 2 * c])); ctor_of[cn] = n
                decls[n] = es; kind[n] = 'IND'
            elif k == '#QUOT':
                pass
            continue
        i, k = int(p[0]), p[1]
        if k == '#NS': names[i] = (names[int(p[2])] + '.' if int(p[2]) else '') + p[3] if len(p) > 3 else names[int(p[2])] + '.'
        elif k == '#NI': names[i] = (names[int(p[2])] + '.' if int(p[2]) else '') + p[3]
        elif k == '#EC': exprs[i] = ('C', nm(p[2]))
        elif k == '#EA': exprs[i] = ('X', int(p[2]), int(p[3]))
        elif k in ('#EP', '#EL'): exprs[i] = ('X', int(p[4]), int(p[5]))
        elif k == '#EZ': exprs[i] = ('X', int(p[3]), int(p[4]), int(p[5]))
        elif k == '#EJ': exprs[i] = ('J', nm(p[2]), int(p[4]))
        else: exprs[i] = ('L',)
memo = {}
def consts(e):
    stack = [e]; order = []
    while stack:
        x = stack.pop()
        if x in memo: continue
        order.append(x)
        t = exprs[x]
        if t[0] == 'X': stack.extend(c for c in t[1:] if c not in memo)
        elif t[0] == 'J' and t[2] not in memo: stack.append(t[2])
    for x in reversed(order):
        if x in memo: continue
        t = exprs[x]
        if t[0] == 'C': memo[x] = frozenset([t[1]])
        elif t[0] == 'X':
            s = set()
            for c in t[1:]:
                if c not in memo: consts(c)
                s |= memo[c]
            memo[x] = frozenset(s)
        elif t[0] == 'J':
            if t[2] not in memo: consts(t[2])
            memo[x] = memo[t[2]] | {t[1]}
        else: memo[x] = frozenset()
    return memo[e]
deps = {}
for n, es in decls.items():
    s = set()
    for e in es: s |= consts(e)
    deps[n] = {ctor_of.get(c, c) for c in s} - {n}
import pickle
pickle.dump((deps, kind), open(out + '.deps.pkl', 'wb'))
print('decls', len(deps))
