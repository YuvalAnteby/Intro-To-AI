"""Profile the existing solver without changing ex1.py, search.py, or utils.py.

Put this file beside ex1.py, ex1_check.py, search.py, and utils.py. Then run:
    python3 profile_ex1.py y7 --baseline
    python3 profile_ex1.py y4 --baseline

--baseline overrides just the three recent switches for this process:
incremental=False, occupancy=True, hash_cache=False. Without --baseline,
the flags in your ex1.py are used unchanged.

Outputs: CASE_profile.txt and CASE.prof. The text includes cumulative time,
self time, call counts, and the expansion count returned by search.py.
Imports and plan validation are outside the profile; construction and A* are
inside, matching the work timed by the checker. No checker child is launched.

The default diagnostic limit is 120 seconds on Unix. Increase it with
--seconds 300, or use --seconds 0 for no limit. On systems without SIGALRM,
use --seconds 0 and Ctrl+C to stop. Interruptions still save a partial profile.
Profiled times include instrumentation overhead, so use ex1_check.py for
ordinary runtime comparisons. This script is a development tool, not a
submission file or an admissibility/optimality proof.
"""

import argparse
import cProfile
import io
from pathlib import Path
import platform
import pstats
import signal
import time


class ProfileTimeout(Exception):
    pass


def stop_profile(signum, frame):
    raise ProfileTimeout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", help="one problem, e.g. p2, y4, or y7")
    parser.add_argument("--baseline", action="store_true",
                        help="use occupancy only among the three recent switches")
    parser.add_argument("--seconds", type=float, default=120,
                        help="diagnostic limit; 0 disables it (default: 120)")
    parser.add_argument("--top", type=int, default=40,
                        help="rows per profile table (default: 40)")
    parser.add_argument("--out", help="output prefix (default: the case name)")
    args = parser.parse_args()
    if args.seconds < 0 or args.top < 1:
        parser.error("--seconds must be nonnegative and --top must be positive")
    if args.seconds and not hasattr(signal, "SIGALRM"):
        parser.error("this system has no SIGALRM; use --seconds 0 and Ctrl+C")

    import ex1
    import ex1_check
    import search

    if args.baseline:
        overrides = dict(OPT_INCREMENTAL_CANON=False,
                         OPT_OCCUPANCY_REUSE=True, OPT_HASH_CACHE=False)
        for name, value in overrides.items():
            if not hasattr(ex1, name):
                parser.error(f"ex1.py has no {name}; use the latest file")
            setattr(ex1, name, value)

    _, game, optimal = ex1_check.find_problem(args.case)
    prefix = Path(args.out or args.case)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    profile_path = Path(str(prefix) + ".prof")
    report_path = Path(str(prefix) + "_profile.txt")
    flags = ", ".join(f"{name}={getattr(ex1, name)}" for name in sorted(vars(ex1))
                      if name.startswith("OPT_"))
    heading = [f"Case: {args.case}", f"Python: {platform.python_version()}",
               f"Solver: {Path(ex1.__file__).resolve()}", f"Flags: {flags}"]
    print("\n".join(heading), flush=True)
    print("Profiling construction + A*; Ctrl+C saves a partial report.", flush=True)

    profiler = cProfile.Profile()
    result = None
    status = "finished"
    problem = None
    error = None
    old_handler = None
    started = time.perf_counter()
    try:
        if args.seconds:
            old_handler = signal.signal(signal.SIGALRM, stop_profile)
            signal.setitimer(signal.ITIMER_REAL, args.seconds)
        profiler.enable()
        problem = ex1.create_logistics_problem(game)
        result = search.astar_search(problem, problem.h_astar)
    except ProfileTimeout:
        status = f"PARTIAL: diagnostic limit of {args.seconds:g} seconds"
    except KeyboardInterrupt:
        status = "PARTIAL: interrupted with Ctrl+C"
    except BaseException as exc:
        status = f"ERROR: {type(exc).__name__}: {exc}"
        error = exc
    finally:
        profiler.disable()
        if args.seconds:
            signal.setitimer(signal.ITIMER_REAL, 0)
            if old_handler is not None:
                signal.signal(signal.SIGALRM, old_handler)
        elapsed = time.perf_counter() - started
        profiler.dump_stats(str(profile_path))

    summary = heading + [f"Status: {status}",
                         f"Profiled wall time: {elapsed:.3f} s (includes profiler overhead)"]
    if status == "finished" and result is not None:
        node, expanded = result
        plan = [str(n.action) for n in node.path()[::-1]][1:]
        verdict, explanation = ex1_check.judge(game, dict(plan=plan), optimal)
        summary += [f"Plan check: {verdict}: {explanation}",
                    f"Returned path cost: {node.path_cost}",
                    f"Expanded: {expanded:,}", f"Plan actions: {len(plan)}"]
    elif status == "finished":
        summary.append("Search exhausted: no plan returned")
    else:
        summary.append("Partial profile: not a completed solve or a checker timeout result.")

    report = io.StringIO()
    report.write("\n".join(summary) + "\n")
    stats = pstats.Stats(profiler, stream=report).strip_dirs()
    report.write("\nCUMULATIVE TIME (function plus callees; nested rows overlap)\n")
    stats.sort_stats("cumulative").print_stats(args.top)
    report.write("\nSELF TIME (time inside the function, excluding callees)\n")
    stats.sort_stats("tottime").print_stats(args.top)
    report.write("\nEX1 FUNCTIONS BY CUMULATIVE TIME\n")
    stats.sort_stats("cumulative").print_stats(r"ex1\.py:", args.top)
    report_path.write_text(report.getvalue(), encoding="utf-8")
    print(report.getvalue())
    print(f"Saved: {report_path.resolve()}\nSaved: {profile_path.resolve()}")
    if error is not None:
        raise error


if __name__ == "__main__":
    main()
