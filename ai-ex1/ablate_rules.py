"""Time the supplied cases with the pruning rules on, each one off in turn, and all of a group off.

Put this file beside ex1.py, ex1_check.py, search.py and utils.py, then run for example:
    python3 ablate_rules.py y3 y4 y7                 history rules (H1-H4, corridor): all on, each off, all off
    python3 ablate_rules.py y4 --rules --limit 120   successor rules A-D: all on, each off, all off

Every run is a fresh process (no shared caches), timed from problem construction to the end of A*, like the
checker. The plan is validated with ex1_check.judge. A run that exceeds --limit seconds (default 60) is stopped.
This is a development tool, not a submission file.
"""
import argparse
import json
import subprocess
import sys

SWITCHES = ("OPT_EMPTY_SAIL", "OPT_EFFCAP", "OPT_USELESS", "OPT_TOWARD")
HISTORY = ("OPT_FOCUS", "OPT_UTURN", "OPT_FRESH", "OPT_NEEDBOARD", "OPT_CORRIDOR")


def configs(group):
    out = [("all on", {})] + [("%s off" % s[4:].lower(), {s: False}) for s in group]
    off = {s: False for s in group}
    if group is HISTORY:
        off["OPT_HISTORY"] = False
    return out + [("all off", off)]

CHILD = r"""
import contextlib, io, json, sys, time
import ex1, ex1_check, search
for name, value in json.loads(sys.argv[2]).items():
    setattr(ex1, name, value)
_, game, optimal = ex1_check.find_problem(sys.argv[1])
started = time.perf_counter()
with contextlib.redirect_stdout(io.StringIO()):
    problem = ex1.create_logistics_problem(game)
    result = search.astar_search(problem, problem.h_astar)
elapsed = time.perf_counter() - started
if result is None:
    print(json.dumps({"time": elapsed, "verdict": "no plan"}))
else:
    node, expanded = result
    plan = [str(n.action) for n in node.path()[::-1]][1:]
    verdict, explanation = ex1_check.judge(game, dict(plan=plan), optimal)
    print(json.dumps({"time": elapsed, "expanded": expanded, "cost": node.path_cost,
                      "verdict": "%s: %s" % (verdict, explanation)}))
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("cases", nargs="+")
    parser.add_argument("--limit", type=float, default=60)
    parser.add_argument("--rules", action="store_true", help="vary rules A-D instead of the history rules")
    args = parser.parse_args()
    CONFIGS = configs(SWITCHES if args.rules else HISTORY)
    for case in args.cases:
        print("== %s" % case)
        for label, overrides in CONFIGS:
            try:
                out = subprocess.run([sys.executable, "-c", CHILD, case, json.dumps(overrides)],
                                     capture_output=True, text=True, timeout=args.limit)
            except subprocess.TimeoutExpired:
                print("  %-16s over %g s" % (label, args.limit))
                continue
            lines = out.stdout.strip().splitlines()
            if out.returncode or not lines:
                print("  %-16s ERROR %s" % (label, (out.stderr.strip().splitlines() or ["?"])[-1]))
                continue
            r = json.loads(lines[-1])
            print("  %-16s %7.2f s  expanded %9s  cost %4s  %s" % (
                label, r["time"], "{:,}".format(r["expanded"]) if "expanded" in r else "-",
                r.get("cost", "-"), r["verdict"]))
            sys.stdout.flush()


if __name__ == "__main__":
    main()
