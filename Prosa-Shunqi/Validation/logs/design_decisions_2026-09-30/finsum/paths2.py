import pickle, sys, collections
deps, kind = pickle.load(open(sys.argv[1], 'rb'))
pref = sys.argv[2]
bad = lambda n: n.startswith(pref) or n.startswith('_private.Init.Data.Nat.Internal.Linear') if pref=='Nat.Internal.Linear' else n.startswith(pref)
rev = collections.defaultdict(set)
for n, ds in deps.items():
    for d in ds: rev[d].add(n)
front = sorted(n for n in deps if not bad(n) and any(bad(d) for d in deps[n]))
print('frontier', front)
for t in sys.argv[3:]:
    prev = {t: None}; q = collections.deque([t]); hit = None
    while q:
        x = q.popleft()
        if bad(x): hit = x; break
        for d in sorted(deps.get(x, ())):
            if d not in prev: prev[d] = x; q.append(d)
    path = []
    while hit: path.append(hit); hit = prev[hit]
    print(t, '->', ' <- '.join(path) if path else 'CLEAN')
