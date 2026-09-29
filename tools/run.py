#!/usr/bin/env python3
"""Run TLC on a list of configs, one at a time, stopping at the first failure.

Usage:
    run.py --tlc "<tlc command>" --spec SPEC.tla [--workers N|auto]
           [--fpmem X] [--checkpoint N] [--interval N] [--witness] CFG...

The TLC command is whatever starts TLC on this machine, for example
    "java -XX:+UseParallelGC -cp /Library/Java/Extensions/tla2tools.jar tlc2.TLC"
Aliases are not visible to a subprocess, so pass the expanded command. The
script appends "-workers W -config <cfg> <spec>" and runs in the spec's
directory. --fpmem and --checkpoint are forwarded as TLC's -fpmem and
-checkpoint when given, and left out otherwise, so TLC's own defaults apply.
Arguments which are not .cfg files are skipped, so a glob over a directory
holding the outputs too is fine.

By default every config must pass. With --witness every config is a
reachability witness: it must end with TLC violating the invariant or action
property named after the config - WitnessDataFork.cfg ends with "Invariant
WitnessDataFork is violated", and the trace is the scenario reached. A pass
means the scenario is unreachable; another invariant, a failed Assert, a
deadlock or a TLC error are failures like anywhere else. Either way the run
stops at the first unexpected outcome.

The complete TLC output of every run goes next to its config, as
<name>_out.txt, with a footer giving the command and the wall time - TLC
itself reports the state counts and the depth at the end. Every N seconds
(default 60) the last TLC progress line is checked, and printed with the
config's name and position when it differs from the last printed one.
"""
import argparse
import os
import re
import shlex
import subprocess
import sys
import time

PASS_MARK = "Model checking completed. No error has been found."
VIOLATION_RE = re.compile(r"^Error: (?:Invariant|Action property) (\S+) is violated\.",
                          re.MULTILINE)


def last_progress(path):
    try:
        with open(path) as f:
            lines = f.readlines()
    except OSError:
        return ""
    for line in reversed(lines):
        if line.startswith("Progress(") or line.startswith("Computing initial states"):
            return line.strip()
    return lines[-1].strip() if lines else ""


def run_one(cmd, cwd, out_path, interval, label):
    started = time.time()
    reported = None
    with open(out_path, "w") as out:
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        next_report = started + interval
        while proc.poll() is None:
            time.sleep(1)
            if time.time() < next_report:
                continue
            next_report += interval
            line = last_progress(out_path)
            if line == reported:
                continue
            reported = line
            print("%s %s" % (label, line), flush=True)
    elapsed = time.time() - started
    with open(out_path) as f:
        text = f.read()
    passed = proc.returncode == 0 and PASS_MARK in text
    with open(out_path, "a") as out:
        out.write("\n=== run.py: %s\n=== run.py: %s in %d seconds, exit code %d\n"
                  % (" ".join(cmd), "PASS" if passed else "FAIL", elapsed,
                     proc.returncode))
    return passed, elapsed, text


def print_failure(text, out_path):
    for line in text.splitlines():
        if line.startswith("Error:") or line.startswith("\""):
            print("  " + line)
    print("  output: %s" % out_path)
    tool = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tlatrace.py")
    if os.path.exists(tool) and "State 1:" in text:
        print("  trace actions:")
        subprocess.run([sys.executable, tool, out_path, "actions"])


def verdict(name, passed, text, witness):
    """The outcome against the expectation: (is_expected, description)."""
    if not witness:
        return passed, "PASS" if passed else "FAIL"
    if passed:
        return False, "NOT REACHED, the model never violates %s" % name
    violated = VIOLATION_RE.findall(text)
    if violated == [name]:
        return True, "REACHED, %s is violated" % name
    if violated:
        return False, "FAIL, %s is violated instead of %s" % (", ".join(violated), name)
    return False, "FAIL, not by an invariant or property"


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--tlc", required=True, help="the TLC command")
    parser.add_argument("--spec", required=True, help="the .tla module to check")
    parser.add_argument("--workers", default="auto", help="TLC worker count, default auto")
    parser.add_argument("--fpmem", help="TLC -fpmem: fingerprint set memory, "
                        "a fraction of the heap or a size in MB")
    parser.add_argument("--checkpoint", help="TLC -checkpoint: minutes between "
                        "checkpoints")
    parser.add_argument("--interval", type=int, default=60,
                        help="progress report period, seconds")
    parser.add_argument("--witness", action="store_true",
                        help="the configs are reachability witnesses: each must "
                        "violate the invariant or property of its name")
    parser.add_argument("cfgs", nargs="+", help="the .cfg files to run, in order")
    args = parser.parse_args()

    spec = os.path.abspath(args.spec)
    cwd = os.path.dirname(spec)
    cfgs = [os.path.abspath(c) for c in args.cfgs if c.endswith(".cfg")]
    if not cfgs:
        print("no .cfg files given")
        return 2
    tlc_opts = ["-workers", args.workers]
    if args.fpmem is not None:
        tlc_opts += ["-fpmem", args.fpmem]
    if args.checkpoint is not None:
        tlc_opts += ["-checkpoint", args.checkpoint]
    total_started = time.time()
    for i, cfg in enumerate(cfgs, 1):
        name = os.path.basename(cfg)[:-len(".cfg")]
        out_path = cfg[:-len(".cfg")] + "_out.txt"
        cmd = shlex.split(args.tlc) + tlc_opts + [
            "-config", os.path.relpath(cfg, cwd),
            os.path.relpath(spec, cwd),
        ]
        label = "[%d/%d] %s" % (i, len(cfgs), name)
        print("%s START" % label, flush=True)
        passed, elapsed, text = run_one(cmd, cwd, out_path, args.interval, label)
        expected, outcome = verdict(name, passed, text, args.witness)
        print("%s %s in %ds" % (label, outcome, elapsed), flush=True)
        if expected:
            continue
        if not passed:
            print_failure(text, out_path)
        return 1
    print("ALL AS EXPECTED in %ds" % (time.time() - total_started))
    return 0


if __name__ == "__main__":
    sys.exit(main())
