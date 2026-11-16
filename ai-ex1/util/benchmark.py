"""Replay optimal plans and enforce the five-second target, including initialization.

Usage: python3 util/benchmark.py [all | y3 y4 y7 | ...]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import ex1_check


def main():
    failed = []
    for name in ex1_check.expand(sys.argv[1:] or ["all"]):
        _, game, optimum = ex1_check.find_problem(name)
        result = ex1_check.solve(game, limit=5)
        verdict, explanation = ex1_check.judge(game, result, optimum)
        seconds = "%.3fs" % result["seconds"] if "seconds" in result else "-"
        print("%s: %s  %s  %s  %s expanded" %
              (name, verdict, explanation, seconds, result.get("expanded", "?")),
              flush=True)
        if verdict != "PASS":
            failed.append(name)
    if failed:
        raise SystemExit("Failed: " + ", ".join(failed))


if __name__ == "__main__":
    main()
