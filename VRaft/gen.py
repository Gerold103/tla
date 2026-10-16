#!/usr/bin/env python3
"""Generate the TLC configs, and the modules of the scripts, into <out dir>.

Usage: gen.py <matrix.yaml> <out dir>
       gen.py <scripts dir> <out dir>

A matrix (test/test.yaml, test/test_witness.yaml) names the module its
configs check, `spec`, relative to this dir, and lists the configs: each
entry becomes <out dir>/<name>.cfg from test/template.cfg. A scripts dir
(test/scripted) holds one scripted scenario per .tla file: each becomes
<out dir>/<name>.cfg and <out dir>/<name>.tla, the module TLC runs, from
test/template_script.tla. Every generated config names its module in a header
line, `\\* spec: <path>`, relative to the config, which run.py reads. The
output dir holds the generated files and the run outputs - runtime files
to be deleted when the matrix is done. Give every source its own dir.

Every config checks TotalInvariant. An entry may add one more check:
`invariant: Name` or `property: Name`, both defined in the module the run
is given (VRaftWitness.tla for the witnesses; a script sees the witness
operators too). An optional `max_promotes: N` caps the PROMOTEs the cluster
writes (MaxPromotes); the default 999 never binds.

An entry is checked exhaustively unless it has
    simulate:
      traces: N
      depth: D
which makes run.py run TLC's random simulation on it instead: N behaviors
of up to D steps (D is optional, TLC's default is 100). `traces` is
required - it is what bounds the run. The generated config carries run.py's
options for it in a header comment, written only when there are any:
    \\* run: {"simulate": {"traces": N, "depth": D}}
run.py reads the JSON after `run:`, so one run goes through a mixed matrix.

Node ids are n1..nN: the data nodes first, the voters after them. The limbo
owner at start is n1. Transactions are single letters a, b, c, ...

A script is a .tla file with the config above its module line and the
steps below it:
    data_nodes: 3
    ...
    ---- MODULE <name> ----
    NodeBumpTerm(n1)
    ...
    ====
The text above the module line is YAML, the keys of a matrix entry; TLA+
tools ignore everything outside the module, and the editors highlight the
inside, so the file reads as TLA+ although it isn't a module TLC could run.
The module's name is the file's. The steps are the spec's actions, or the
pinning helpers of VRaftScript.tla, one call per line in the order they
happen - the i-th such line is step i. A line `Expect(predicate)` is a
checkpoint, not a step: the predicate must hold in the state after the step
above it; together they are the Checkpoints invariant. Comments and blank
lines are free, the end line `====` is optional. The generated module
declares the node and transaction names as constants, so the steps can name
them, and the config assigns them, which is why a script runs with no
symmetry.

After its last step a script stops and the run ends by the deadlock, unless
the header says to go on with the spec's own Next:
    explore:
      depth: D
the exhaustive search D steps deep from the script's end, bounded by a
constraint on the step; or `simulate` as above, random walks of D steps
from the script's end. Both together bound the walks by the constraint too.
"""
import json
import os
import string
import sys

import yaml

COMMENT = "\\*"
REQUIRED = ("data_nodes", "voters", "quorum", "max_term", "transactions")


def is_call(text):
    """Whether the line is one call: a name and its arguments in parens -
    an action, a helper, or Expect."""
    name, paren, _ = text.partition("(")
    return paren != "" and name.isidentifier() and text.endswith(")")


def tla_set(items):
    return "{" + ", ".join(items) + "}"


def names(cfg):
    """The node ids and the transaction names of the config."""
    total = cfg["data_nodes"] + cfg["voters"]
    nodes = ["n%d" % i for i in range(1, total + 1)]
    txns = list(string.ascii_lowercase[:cfg["transactions"]])
    return nodes, txns


def checks(cfg, extra=()):
    """The INVARIANTS and PROPERTIES sections of the config."""
    lines = ["INVARIANTS", "    TotalInvariant"]
    lines += ["    " + name for name in extra]
    if "invariant" in cfg:
        lines.append("    " + cfg["invariant"])
    if "property" in cfg:
        lines += ["", "PROPERTIES", "    " + cfg["property"]]
    return "\n".join(lines)


def simulate_options(cfg, script_len=0):
    """The validated `simulate` options of the entry, None without them. For
    a script the depth counts from the script's end."""
    sim = cfg.get("simulate")
    if sim is None:
        return None
    if not isinstance(sim, dict) or "traces" not in sim or \
            not set(sim) <= {"traces", "depth"} or \
            not all(isinstance(v, int) for v in sim.values()):
        sys.exit("%s: simulate takes traces (required) and depth, integers"
                 % cfg["name"])
    sim = dict(sim)
    if script_len:
        sim["depth"] = sim.get("depth", 100) + script_len
    return sim


def explore_depth(cfg):
    """The `explore` depth of a script, None without it."""
    explore = cfg.get("explore")
    if explore is None:
        return None
    if not isinstance(explore, dict) or set(explore) != {"depth"} or \
            not isinstance(explore["depth"], int):
        sys.exit("%s: explore takes depth, an integer" % cfg["name"])
    return explore["depth"]


def header_lines(spec=None, sim=None):
    """The `\\* spec:` and `\\* run:` lines of the config, the ones given."""
    lines = []
    if spec is not None:
        lines.append("%s spec: %s\n" % (COMMENT, spec))
    if sim is not None:
        lines.append("%s run: %s\n" % (COMMENT, json.dumps({"simulate": sim})))
    return "".join(lines)


def render_cfg(template, source, cfg, spec, header, model_values, checks_text,
               reductions):
    nodes, txns = names(cfg)
    return template.format(
        source=source,
        note=cfg.get("note", ""),
        header_lines=header,
        spec=spec,
        node_ids=tla_set(nodes),
        voter_ids=tla_set(nodes[cfg["data_nodes"]:]),
        transactions=tla_set(txns),
        max_term=cfg["max_term"],
        max_promotes=cfg.get("max_promotes", 999),
        quorum=cfg["quorum"],
        model_values=model_values,
        checks=checks_text,
        reductions=reductions,
    )


def module_name(line):
    """The name of a `---- MODULE name ----` line, None for any other."""
    if not line.startswith("----"):
        return None
    words = line.strip("- ").split()
    if len(words) != 2 or words[0] != "MODULE":
        return None
    return words[1]


def parse_script(path):
    """The config of the script, its steps as (line, text) and its
    checkpoints as (the step it follows, text)."""
    name = os.path.basename(path)[:-len(".tla")]
    with open(path) as f:
        lines = f.read().split("\n")
    i = 0
    while i < len(lines) and module_name(lines[i]) is None:
        i += 1
    if i == len(lines):
        sys.exit("%s: no module line: the config above it, the steps below"
                 % path)
    if module_name(lines[i]) != name:
        sys.exit("%s:%d: the module is named after the file, %s"
                 % (path, i + 1, name))
    try:
        cfg = yaml.safe_load("\n".join(lines[:i]))
    except yaml.YAMLError as e:
        sys.exit("%s: the config above the module line is not valid YAML: %s"
                 % (path, e))
    if not isinstance(cfg, dict):
        sys.exit("%s: the config above the module line must be a YAML mapping"
                 % path)
    missing = [k for k in REQUIRED if k not in cfg]
    if missing:
        sys.exit("%s: the config lacks %s" % (path, ", ".join(missing)))
    steps, expects = [], []
    for n, line in enumerate(lines[i + 1:], i + 2):
        if line.startswith("===="):
            break
        text = line.split(COMMENT)[0].strip()
        if not text:
            continue
        if not is_call(text):
            sys.exit("%s:%d: a step is one call of an action or a helper: %r"
                     % (path, n, text))
        if text.startswith("Expect("):
            expects.append((len(steps), text))
        else:
            steps.append((n, text))
    if not steps:
        sys.exit("%s: no steps" % path)
    return cfg, steps, expects


def render_module(template, source, name, cfg, steps, expects, goes_on, depth):
    nodes, txns = names(cfg)
    cases = []
    for i, (line, text) in enumerate(steps, 1):
        prefix = "" if i == 1 else "      [] "
        cases.append("%si = %d -> %s  %s line %d" % (prefix, i, text, COMMENT, line))
    checkpoints = ["    /\\ step = %d => %s" % (after + 1, text)
                   for after, text in expects] or ["    TRUE"]
    run = "ScriptRun ==\n    \\/ ScriptNext(ScriptLength, Step)\n"
    if goes_on:
        run += "    \\/ ExploreNext(ScriptLength)\n"
    bound = ""
    if depth is not None:
        bound = ("\n%s The explore depth of the header: states past the "
                 "script's end.\nStepBound == step <= ScriptLength + 1 + %d\n"
                 % (COMMENT, depth))
    return template.format(
        name=name,
        source=source,
        constants=", ".join(nodes + txns),
        length=len(steps),
        cases="\n".join(cases),
        checkpoints="\n".join(checkpoints),
        run=run,
        bound=bound,
    )


def gen_matrix(matrix_path, out_dir, template, here):
    with open(matrix_path) as f:
        matrix = yaml.safe_load(f)
    source = os.path.basename(matrix_path)
    if "spec" not in matrix:
        sys.exit("%s: the matrix must name the module to check in `spec`, "
                 "relative to %s" % (matrix_path, here))
    spec = os.path.relpath(os.path.join(here, matrix["spec"]), out_dir)
    for cfg in matrix["configs"]:
        text = render_cfg(template, source, cfg, "Spec",
                          header_lines(spec, simulate_options(cfg)), "",
                          checks(cfg), "SYMMETRY Perms\n\n")
        path = os.path.join(out_dir, cfg["name"] + ".cfg")
        with open(path, "w") as f:
            f.write(text)
        print(path)


def gen_scripts(scripts_dir, out_dir, template, module_template):
    for fname in sorted(os.listdir(scripts_dir)):
        if not fname.endswith(".tla"):
            continue
        name = fname[:-len(".tla")]
        source = os.path.join(os.path.basename(scripts_dir), fname)
        cfg, steps, expects = parse_script(os.path.join(scripts_dir, fname))
        cfg["name"] = name
        if "spec" in cfg:
            sys.exit("%s: a script's module is generated, it names none" % fname)
        sim = simulate_options(cfg, len(steps))
        depth = explore_depth(cfg)
        goes_on = sim is not None or depth is not None
        nodes, txns = names(cfg)
        module = render_module(module_template, source, name, cfg, steps,
                               expects, goes_on, depth)
        module_path = os.path.join(out_dir, fname)
        with open(module_path, "w") as f:
            f.write(module)
        print(module_path)
        model_values = "".join("    %s = %s\n" % (v, v) for v in nodes + txns)
        reductions = "CONSTRAINT StepBound\n\n" if depth is not None else ""
        text = render_cfg(template, source, cfg, "ScriptSpec",
                          header_lines(fname, sim), model_values,
                          checks(cfg, ["Checkpoints"]), reductions)
        path = os.path.join(out_dir, name + ".cfg")
        with open(path, "w") as f:
            f.write(text)
        print(path)


def main(argv):
    if len(argv) != 3:
        print(__doc__.strip())
        return 2
    here = os.path.dirname(os.path.abspath(__file__))
    source, out_dir = argv[1], argv[2]
    templates = os.path.join(here, "test")
    with open(os.path.join(templates, "template.cfg")) as f:
        template = f.read()
    os.makedirs(out_dir, exist_ok=True)
    if os.path.isdir(source):
        with open(os.path.join(templates, "template_script.tla")) as f:
            module_template = f.read()
        gen_scripts(source, out_dir, template, module_template)
    else:
        gen_matrix(source, out_dir, template, here)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
