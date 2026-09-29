"""
Benchmarks the tinkr compiler under different combinations of optimizations, and optionally
compares against equivalent Racket and Python programs.

WARNING: this script was written entirely by Claude

Each benchmark lives in its own directory (by default under bench/programs):

    programs/<name>/<name>.ti     tinkr version (built once per optimization config)
    programs/<name>/<name>.rkt    Racket version (optional)
    programs/<name>/<name>.py     Python version (optional)
    programs/<name>/answer        expected stdout (optional; used to check correctness)

Must be run in the same environment the compiler normally runs in (e.g. WSL/Linux), since the
compiler writes its build output to /tmp/ti.

Examples:
    python3 bench/bench.py                              # every benchmark, every config, all languages
    python3 bench/bench.py -b fib closures -n 10        # two benchmarks, 10 timed runs each
    python3 bench/bench.py -c none all                  # only no-opts vs all-opts
    python3 bench/bench.py -c inlining well-known+inlining --langs tinkr
    python3 bench/bench.py --plot bench/results/<run>/results.json   # re-plot old results
"""

import argparse
import csv
import itertools
import json
import os
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from datetime import datetime

PATH = os.path.abspath(os.path.dirname(__file__))
REPO_ROOT = os.path.dirname(PATH)
DEFAULT_PROGRAMS_DIR = os.path.join(PATH, "programs")
DEFAULT_RESULTS_DIR = os.path.join(PATH, "results")
PATH_TO_TESTER_FILE = os.path.join(REPO_ROOT, "test", "test.rkt")
PATH_TO_TI_DIR = os.path.join("/tmp", "ti")
PATH_TO_BINARY = os.path.join(PATH_TO_TI_DIR, "out.bin")
PATH_TO_ERROR_LOG = os.path.join(PATH_TO_TI_DIR, "error.log")

# Optimization name -> the test.rkt flag that turns it *off* (both are on by default).
# Add new optimizations here.
OPTIMIZATIONS = {
    "inlining": "--no-inlining",
    "well-known": "--no-well-known",
}

LANGS = ["tinkr", "racket", "python"]
LANG_EXTS = {"tinkr": "ti", "racket": "rkt", "python": "py"}

BUILD_TIMEOUT = 600
RUN_TIMEOUT = 300


# ---------------------------------------------------------------------------------------------
# Optimization configs

def all_configs():
    """Every combination of optimizations, from none to all."""
    names = list(OPTIMIZATIONS)
    return [frozenset(c) for r in range(len(names) + 1) for c in itertools.combinations(names, r)]


def parse_config(spec):
    """
    Parses a config like "none", "all", "inlining", or "inlining+well-known" into the set of
    enabled optimizations.
    """
    if spec == "none":
        return frozenset()
    if spec == "all":
        return frozenset(OPTIMIZATIONS)

    opts = frozenset(s.strip() for s in spec.split("+") if s.strip())
    unknown = opts - set(OPTIMIZATIONS)
    if unknown:
        raise argparse.ArgumentTypeError(
            f"unknown optimization(s) {', '.join(sorted(unknown))} in config '{spec}' "
            f"(known: {', '.join(OPTIMIZATIONS)}, or 'none'/'all')"
        )
    return opts


def config_name(config):
    """Canonical name for a config (order follows OPTIMIZATIONS)."""
    if not config:
        return "none"
    if config == frozenset(OPTIMIZATIONS):
        return "all"
    return "+".join(o for o in OPTIMIZATIONS if o in config)


def config_flags(config):
    return [flag for opt, flag in OPTIMIZATIONS.items() if opt not in config]


# ---------------------------------------------------------------------------------------------
# Running things

def run(cmd, timeout, cwd=REPO_ROOT, env=None):
    """Runs cmd (a list), returning (stdout+stderr as str, exit code, elapsed seconds)."""
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout,
        )
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode("utf-8", errors="replace")
        return out + f"\n[timed out after {timeout}s]", None, time.perf_counter() - start
    elapsed = time.perf_counter() - start
    return proc.stdout.decode("utf-8", errors="replace"), proc.returncode, elapsed


def normalize_output(s):
    return "\n".join(line.rstrip() for line in s.replace("\r\n", "\n").strip().split("\n"))


def time_command(cmd, runs, warmup, timeout):
    """
    Runs cmd warmup + runs times, timing the last `runs`. Returns a dict with the timings and the
    output of the first run, or an "error" key if any run failed.
    """
    times = []
    first_output = None
    for i in range(warmup + runs):
        out, code, elapsed = run(cmd, timeout, cwd=os.path.dirname(cmd[-1]))
        if first_output is None:
            first_output = out
        if code != 0:
            return {"error": f"exit code {code}", "output": out}
        if i >= warmup:
            times.append(elapsed)

    return {
        "times": times,
        "median": statistics.median(times),
        "mean": statistics.mean(times),
        "min": min(times),
        "stdev": statistics.stdev(times) if len(times) > 1 else 0.0,
        "output": first_output,
    }


def stripped_size(binary):
    """Size of the binary with debug info/symbols stripped (tinkr builds with -g)."""
    if not shutil.which("strip"):
        return None
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, "stripped.bin")
        _, code, _ = run(["strip", "-o", out, binary], 60)
        return os.path.getsize(out) if code == 0 else None


def build_tinkr(source, config, args, bin_dir, bench_name):
    """
    Builds source with the given optimization config and copies the binary into bin_dir.
    Returns (binary path or None, build seconds, build log).
    """
    # The compiler's build cache doesn't take optimization flags into account, so always
    # clean unless told otherwise (otherwise every config may silently get the same binary).
    clean = [] if args.no_clean else ["-c"]
    cmd = [args.racket, PATH_TO_TESTER_FILE, *clean, *config_flags(config), *args.tinkr_flag, source]

    if os.path.exists(PATH_TO_BINARY):
        os.remove(PATH_TO_BINARY)

    log, code, elapsed = run(cmd, BUILD_TIMEOUT)

    if code != 0 or not os.path.exists(PATH_TO_BINARY):
        if os.path.exists(PATH_TO_ERROR_LOG):
            with open(PATH_TO_ERROR_LOG, "r", errors="replace") as f:
                log += "\n--- error.log ---\n" + f.read()
        return None, elapsed, log

    dest = os.path.join(bin_dir, f"{bench_name}__{config_name(config)}.bin")
    shutil.copy2(PATH_TO_BINARY, dest)
    return dest, elapsed, log


# ---------------------------------------------------------------------------------------------
# Benchmark discovery

def find_benchmarks(programs_dir, names):
    """Returns {name: {lang: path}} for the requested (or all) benchmarks."""
    if not os.path.isdir(programs_dir):
        sys.exit(f"Error: benchmark directory {programs_dir} does not exist.")

    available = sorted(
        d for d in os.listdir(programs_dir)
        if os.path.isdir(os.path.join(programs_dir, d)) and not d.startswith(".")
    )
    if names:
        missing = [n for n in names if n not in available]
        if missing:
            sys.exit(f"Error: unknown benchmark(s): {', '.join(missing)} "
                     f"(available: {', '.join(available)})")
        available = names

    benchmarks = {}
    for name in available:
        d = os.path.join(programs_dir, name)
        files = {lang: os.path.join(d, f"{name}.{ext}") for lang, ext in LANG_EXTS.items()}
        files = {lang: p for lang, p in files.items() if os.path.exists(p)}
        answer = os.path.join(d, "answer")
        if os.path.exists(answer):
            files["answer"] = answer
        benchmarks[name] = files
    return benchmarks


# ---------------------------------------------------------------------------------------------
# Main benchmarking loop

def variant_label(lang, config=None):
    return f"tinkr [{config_name(config)}]" if lang == "tinkr" else lang


def run_benchmarks(args):
    benchmarks = find_benchmarks(args.dir, args.benchmarks)
    configs = args.configs or all_configs()
    # De-duplicate while keeping the user's order
    configs = list(dict.fromkeys(configs))

    started = datetime.now()
    run_dir = os.path.join(args.out, started.strftime("%Y-%m-%d_%H-%M-%S"))
    bin_dir = os.path.join(run_dir, "bin")
    os.makedirs(bin_dir, exist_ok=True)

    if "racket" in args.langs or "tinkr" in args.langs:
        if not shutil.which(args.racket):
            sys.exit(f"Error: racket executable '{args.racket}' not found (use --racket).")
    if "python" in args.langs and not shutil.which(args.python):
        sys.exit(f"Error: python executable '{args.python}' not found (use --python).")

    print(f"Benchmarks: {', '.join(benchmarks)}")
    if "tinkr" in args.langs:
        print(f"Configs:    {', '.join(config_name(c) for c in configs)}")
    print(f"Languages:  {', '.join(args.langs)}")
    print(f"Runs:       {args.runs} timed (+{args.warmup} warmup)")
    print(f"Results:    {run_dir}\n")

    results = []

    for name, files in benchmarks.items():
        print(f"=== {name}")
        expected = None
        if "answer" in files:
            with open(files["answer"], "r") as f:
                expected = normalize_output(f.read())

        def record(entry, timing):
            if "error" in timing:
                entry["error"] = timing["error"]
                print(f"    FAILED ({timing['error']})")
                print("    " + timing["output"].strip().replace("\n", "\n    "))
            else:
                entry.update({k: timing[k] for k in ("times", "median", "mean", "min", "stdev")})
                output = normalize_output(timing["output"])
                entry["correct"] = None if expected is None else output == expected
                mark = {None: "", True: "", False: "  (WRONG OUTPUT)"}[entry["correct"]]
                print(f"    median {fmt_time(entry['median'])}  "
                      f"min {fmt_time(entry['min'])}  stdev {fmt_time(entry['stdev'])}{mark}")
                if entry["correct"] is False:
                    print(f"    expected: {expected!r}\n    got:      {output!r}")
            results.append(entry)

        for lang in args.langs:
            if lang not in files:
                continue

            if lang == "tinkr":
                for config in configs:
                    label = variant_label(lang, config)
                    entry = {"benchmark": name, "lang": lang, "config": config_name(config),
                             "variant": label}
                    print(f"  {label}: building...", flush=True)
                    binary, build_time, log = build_tinkr(files[lang], config, args, bin_dir, name)
                    entry["build_time"] = build_time
                    if binary is None:
                        entry["error"] = "build failed"
                        print("    BUILD FAILED")
                        print("    " + log.strip()[-3000:].replace("\n", "\n    "))
                        results.append(entry)
                        continue

                    entry["size"] = os.path.getsize(binary)
                    entry["stripped_size"] = stripped_size(binary)
                    print(f"    built in {build_time:.1f}s, size {fmt_size(entry['size'])}"
                          + (f" ({fmt_size(entry['stripped_size'])} stripped)"
                             if entry["stripped_size"] else ""))
                    record(entry, time_command([binary], args.runs, args.warmup, args.timeout))

            elif lang == "racket":
                entry = {"benchmark": name, "lang": lang, "config": None, "variant": lang}
                print(f"  {lang}:", flush=True)
                # Compile ahead of time so we don't time Racket's own compilation
                raco = os.path.join(os.path.dirname(shutil.which(args.racket)), "raco")
                if os.path.exists(raco):
                    run([raco, "make", files[lang]], BUILD_TIMEOUT)
                record(entry, time_command([args.racket, files[lang]],
                                           args.runs, args.warmup, args.timeout))

            elif lang == "python":
                entry = {"benchmark": name, "lang": lang, "config": None, "variant": lang}
                print(f"  {lang}:", flush=True)
                record(entry, time_command([args.python, files[lang]],
                                           args.runs, args.warmup, args.timeout))
        print()

    meta = {
        "date": started.isoformat(timespec="seconds"),
        "runs": args.runs,
        "warmup": args.warmup,
        "configs": [config_name(c) for c in configs],
        "langs": args.langs,
        "git_commit": git_commit(),
    }
    data = {"meta": meta, "results": results}

    with open(os.path.join(run_dir, "results.json"), "w") as f:
        json.dump(data, f, indent=2)
    write_csv(results, os.path.join(run_dir, "results.csv"))

    print_summary(results)
    if not args.no_plot:
        plot(data, run_dir, args.log)
    print(f"\nResults written to {run_dir}")

    # Keep the binaries only if asked (they're large-ish and not usually needed)
    if not args.keep_bins:
        shutil.rmtree(bin_dir, ignore_errors=True)


def git_commit():
    out, code, _ = run(["git", "rev-parse", "--short", "HEAD"], 10)
    if code != 0:
        return None
    dirty, _, _ = run(["git", "status", "--porcelain", "--untracked-files=no"], 10)
    return out.strip() + ("-dirty" if dirty.strip() else "")


# ---------------------------------------------------------------------------------------------
# Reporting

def fmt_time(s):
    if s is None:
        return "-"
    if s < 1e-3:
        return f"{s * 1e6:.0f}us"
    if s < 1:
        return f"{s * 1e3:.1f}ms"
    return f"{s:.3f}s"


def fmt_size(b):
    if b is None:
        return "-"
    if b < 1024:
        return f"{b}B"
    if b < 1024 * 1024:
        return f"{b / 1024:.1f}KiB"
    return f"{b / (1024 * 1024):.2f}MiB"


def write_csv(results, path):
    fields = ["benchmark", "lang", "config", "variant", "median", "mean", "min", "stdev",
              "size", "stripped_size", "build_time", "correct", "error"]
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        for r in results:
            w.writerow(r)


def baseline_for(results, benchmark):
    """The tinkr entry with the fewest optimizations enabled, used for relative numbers."""
    tinkr = [r for r in results if r["benchmark"] == benchmark and r["lang"] == "tinkr"
             and "median" in r]
    if not tinkr:
        return None
    return min(tinkr, key=lambda r: len(parse_config(r["config"])))


def print_summary(results):
    print("=" * 94)
    print(f"{'benchmark':<14} {'variant':<26} {'median':>10} {'vs base':>9} "
          f"{'size':>10} {'stripped':>10} {'vs base':>9}")
    print("-" * 94)
    for bench in dict.fromkeys(r["benchmark"] for r in results):
        base = baseline_for(results, bench)
        for r in (r for r in results if r["benchmark"] == bench):
            if "error" in r:
                print(f"{bench:<14} {r['variant']:<26} {r['error']:>10}")
                continue
            rel_t = rel_s = ""
            if base and r["lang"] == "tinkr":
                rel_t = f"{r['median'] / base['median']:.3f}x"
                if r.get("stripped_size") and base.get("stripped_size"):
                    rel_s = f"{r['stripped_size'] / base['stripped_size']:.3f}x"
            elif base:
                rel_t = f"{r['median'] / base['median']:.2f}x"
            wrong = "  WRONG OUTPUT" if r.get("correct") is False else ""
            print(f"{bench:<14} {r['variant']:<26} {fmt_time(r['median']):>10} {rel_t:>9} "
                  f"{fmt_size(r.get('size')):>10} {fmt_size(r.get('stripped_size')):>10} "
                  f"{rel_s:>9}{wrong}")
        print("-" * 94)
    print("'vs base' is relative to the tinkr config with the fewest optimizations "
          "(lower is better).")


def plot(data, out_dir, log_scale=False):
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        print("\nmatplotlib not installed, skipping graphs (pip install matplotlib).")
        return

    results = [r for r in data["results"] if "median" in r]
    if not results:
        return
    benches = list(dict.fromkeys(r["benchmark"] for r in results))
    variants = list(dict.fromkeys(r["variant"] for r in results))
    lookup = {(r["benchmark"], r["variant"]): r for r in results}
    subtitle = f"{data['meta'].get('git_commit') or ''}  {data['meta'].get('date', '')}".strip()

    def grouped_bars(ax, variants, value, err=None):
        width = 0.8 / len(variants)
        for i, v in enumerate(variants):
            xs, ys, es = [], [], []
            for j, b in enumerate(benches):
                r = lookup.get((b, v))
                y = value(r) if r else None
                if y is None:
                    continue
                xs.append(j + (i - (len(variants) - 1) / 2) * width)
                ys.append(y)
                es.append(err(r) if err else 0)
            ax.bar(xs, ys, width, yerr=es if err else None, capsize=2, label=v)
        ax.set_xticks(range(len(benches)))
        ax.set_xticklabels(benches, rotation=20 if len(benches) > 4 else 0)
        ax.legend(fontsize="small")
        ax.grid(axis="y", alpha=0.3)

    written = []

    # Absolute runtime of every variant
    fig, ax = plt.subplots(figsize=(max(6, 1.6 * len(benches) * max(1, len(variants) / 3)), 4.5))
    grouped_bars(ax, variants, lambda r: r["median"], lambda r: r["stdev"])
    ax.set_ylabel("median runtime (s)")
    ax.set_title(f"Runtime  ({subtitle})", fontsize="medium")
    if log_scale:
        ax.set_yscale("log")
    fig.tight_layout()
    fig.savefig(os.path.join(out_dir, "runtime.png"), dpi=150)
    written.append("runtime.png")
    plt.close(fig)

    tinkr_variants = [v for v in variants if v.startswith("tinkr")]
    bases = {b: baseline_for(results, b) for b in benches}

    if len(tinkr_variants) > 1:
        # Runtime relative to the least-optimized config, so small differences are visible
        fig, ax = plt.subplots(figsize=(max(6, 1.4 * len(benches) * max(1, len(tinkr_variants) / 3)), 4.5))
        grouped_bars(ax, tinkr_variants,
                     lambda r: r["median"] / bases[r["benchmark"]]["median"],
                     lambda r: r["stdev"] / bases[r["benchmark"]]["median"])
        ax.axhline(1.0, color="gray", linewidth=0.8, linestyle="--")
        ax.set_ylabel("runtime relative to baseline (lower is better)")
        ax.set_title(f"tinkr runtime vs. baseline config  ({subtitle})", fontsize="medium")
        fig.tight_layout()
        fig.savefig(os.path.join(out_dir, "runtime_relative.png"), dpi=150)
        written.append("runtime_relative.png")
        plt.close(fig)

    if tinkr_variants:
        # Binary sizes (full and stripped)
        fig, axes = plt.subplots(1, 2, figsize=(max(10, 2.4 * len(benches) * max(1, len(tinkr_variants) / 3)), 4.5))
        grouped_bars(axes[0], tinkr_variants, lambda r: r.get("size") and r["size"] / 1024)
        axes[0].set_ylabel("binary size (KiB)")
        axes[0].set_title("Binary size", fontsize="medium")
        grouped_bars(axes[1], tinkr_variants,
                     lambda r: r.get("stripped_size") and r["stripped_size"] / 1024)
        axes[1].set_ylabel("stripped size (KiB)")
        axes[1].set_title("Stripped binary size", fontsize="medium")
        # Sizes differ only slightly between configs, so don't start the axis at 0
        for ax in axes:
            lo, hi = ax.get_ylim()
            vals = [p.get_height() for p in ax.patches]
            if vals:
                span = max(vals) - min(vals)
                ax.set_ylim(max(0, min(vals) - max(span, max(vals) * 0.02) * 2), hi)
        fig.suptitle(subtitle, fontsize="small")
        fig.tight_layout()
        fig.savefig(os.path.join(out_dir, "size.png"), dpi=150)
        written.append("size.png")
        plt.close(fig)

    print(f"\nGraphs: {', '.join(written)}")


# ---------------------------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Benchmark tinkr optimization configs (and compare with Racket/Python).",
        epilog="Configs are 'none', 'all', or optimizations joined with '+' "
               f"(optimizations: {', '.join(OPTIMIZATIONS)}). Default: every combination.",
    )
    parser.add_argument("--list", "-l", action="store_true", help="List available benchmarks")
    parser.add_argument("--benchmarks", "-b", nargs="+", metavar="NAME",
                        help="Benchmarks to run (default: all)")
    parser.add_argument("--configs", "-c", nargs="+", type=parse_config, metavar="CONFIG",
                        help="Optimization configs to build tinkr programs with")
    parser.add_argument("--langs", nargs="+", choices=LANGS, default=LANGS,
                        help="Which language versions to run (default: all)")
    parser.add_argument("--runs", "-n", type=int, default=5, help="Timed runs per variant (default: 5)")
    parser.add_argument("--warmup", "-w", type=int, default=1, help="Untimed warmup runs (default: 1)")
    parser.add_argument("--timeout", type=int, default=RUN_TIMEOUT,
                        help=f"Timeout per run in seconds (default: {RUN_TIMEOUT})")
    parser.add_argument("--dir", default=DEFAULT_PROGRAMS_DIR, help="Directory of benchmarks")
    parser.add_argument("--out", default=DEFAULT_RESULTS_DIR, help="Directory for results")
    parser.add_argument("--racket", default="racket", help="Path to the racket binary")
    parser.add_argument("--python", default=sys.executable or "python3",
                        help="Python used to run the Python benchmarks (default: this one)")
    parser.add_argument("--tinkr-flag", action="append", default=[], metavar="FLAG",
                        help="Extra flag passed to test.rkt (repeatable, e.g. --tinkr-flag=--no-lto)")
    parser.add_argument("--no-clean", action="store_true",
                        help="Don't wipe /tmp/ti before each build (faster, but the build cache "
                             "ignores optimization flags so configs may get stale binaries)")
    parser.add_argument("--keep-bins", action="store_true", help="Keep the built binaries")
    parser.add_argument("--no-plot", action="store_true", help="Don't generate graphs")
    parser.add_argument("--log", action="store_true", help="Use a log scale for the runtime graph")
    parser.add_argument("--plot", metavar="RESULTS_JSON",
                        help="Only (re)generate graphs and the summary from a results.json")
    args = parser.parse_args()

    # Show progress immediately even when piped (e.g. into tee)
    sys.stdout.reconfigure(line_buffering=True)

    if args.list:
        for name, files in find_benchmarks(args.dir, None).items():
            langs = [l for l in LANGS if l in files]
            print(f"{name:<20} {', '.join(langs)}" + ("" if "answer" in files else "  (no answer)"))
        return

    if args.plot:
        with open(args.plot) as f:
            data = json.load(f)
        print_summary(data["results"])
        plot(data, os.path.dirname(os.path.abspath(args.plot)), args.log)
        return

    if args.runs < 1:
        parser.error("--runs must be at least 1")

    run_benchmarks(args)


if __name__ == "__main__":
    main()
