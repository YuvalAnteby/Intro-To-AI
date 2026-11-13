import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # ex1.py, search.py and ex1_check.py are one folder up
"""Does prune_check notice a wrong effect? Inject one into ex1 in memory (never on disk) and count.
Every DRIVE lands on a wrong location. Profile D has several parts of the map, where the checker must
accept exactly one deviation (the reset of a finished part) and nothing else."""
import contextlib, io, random, sys
import ex1, prune_check
from validate import Ref, random_game, INF

orig = ex1.LogisticsProblem._truck_standing
cnt = [0]


def broken(self, st, t, l, kind, x, cont, lying, res):
    k = len(res)
    orig(self, st, t, l, kind, x, cont, lying, res)
    for i in range(k, len(res)):
        a, ns = res[i]
        if a.startswith("DRIVE") and self.n > 2:
            cnt[0] += 1
            ns = list(ns)
            ns[1 + t] = (ns[1 + t] + 1) % self.n
            res[i] = (a, tuple(ns))


stats = {}
for prof, lo in (("S", 60000), ("D", 63000)):
    for seed in range(lo, lo + int(sys.argv[1]) if len(sys.argv) > 1 else lo + 150):
        game = random_game(random.Random(seed), prof)
        ref = Ref(game)
        r = ref.explore(30000)
        if r is None or r[2][0] == INF:
            continue
        ids, states, hs, table = r
        ex1.LogisticsProblem._truck_standing = broken
        cnt[0] = 0
        v, bad = prune_check.analyse(game, ref, table, ids, states, 120000)
        ex1.LogisticsProblem._truck_standing = orig
        if v is None or cnt[0] == 0:
            continue                    # no DRIVE was generated, so nothing was injected
        with contextlib.redirect_stdout(io.StringIO()):
            pr = ex1.create_logistics_problem(game)
        key = "several parts" if pr.multi else "one part"
        c = stats.setdefault(key, [0, 0])
        c[1] += 1
        c[0] += bool(bad and any(b.startswith("P3") for b in bad))
for k, (c, t) in sorted(stats.items()):
    print("%s: injected fault caught in %d of %d games" % (k, c, t))
