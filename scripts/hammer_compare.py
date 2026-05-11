#!/usr/bin/env python3
"""
Side-by-side hammer capture: regenerates TPTP dumps and selected-premise lists
from LeanHammer (Lean + Lean-Auto + Zipperposition) and Sledgehammer (Isabelle
+ MePo + Zipperposition) for a fixed list of cases. Capture only — no ATP
execution.

Usage:
    python3 scripts/hammer_compare.py                         # all cases
    python3 scripts/hammer_compare.py add_zero_succ           # filter by name
    python3 scripts/hammer_compare.py --keep-tmp --only=lean  # debugging
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

# ---------- repo layout helpers ----------------------------------------------

def find_repo_root(start: Path) -> Path:
    for p in [start, *start.parents]:
        if (p / "case_study").is_dir() and (p / "scripts").is_dir():
            return p
    raise SystemExit(f"could not locate repo root from {start}")

REPO = find_repo_root(Path(__file__).resolve().parent)

def resolve_isabelle() -> str:
    env = os.environ.get("ISABELLE_BIN")
    if env:
        return env
    on_path = shutil.which("isabelle")
    if on_path:
        return on_path
    mac = "/Applications/Isabelle2025-2.app/bin/isabelle"
    if Path(mac).exists():
        return mac
    return "isabelle"  # let the error surface later
LEAN_PROJECT = REPO / "case_study" / "lean"
ISABELLE_CASES = REPO / "case_study" / "isabelle" / "cases"
TPTP_OUT = REPO / "case_study" / "tptp_files"
TMP_ROOT = REPO / "tmp" / "isabelle"


# ---------- config ------------------------------------------------------------

@dataclass
class Case:
    name: str
    auto_premises: int
    pool_cap: int
    lean_file: Path     # absolute
    isabelle_file: Path # absolute

def load_cases(cfg_path: Path) -> list[Case]:
    with cfg_path.open("rb") as f:
        data = tomllib.load(f)
    out = []
    for c in data.get("case", []):
        out.append(Case(
            name = c["name"],
            auto_premises = int(c["auto_premises"]),
            pool_cap = int(c["pool_cap"]),
            lean_file = (REPO / c["lean_file"]).resolve(),
            isabelle_file = (REPO / c["isabelle_file"]).resolve(),
        ))
    return out


# ---------- Lean pass --------------------------------------------------------

# The full premise list is emitted on the third [hammer.premises] line. Match
# the opening `[` after the anchor and balance-count brackets to find its end.
PREMISE_ANCHOR = "[hammer.premises] premises from premise selector after removing duplicates in user input terms:"
TPTP_ANCHOR = "[auto.tptp.printQuery]"

IMPORT_LINE_RE = re.compile(r"^\s*import\s+\S+", re.MULTILINE)
SET_LIB_SUGG_RE = re.compile(r"^\s*set_library_suggestions\b", re.MULTILINE)

def lean_source_with_selector(src: str, selector: str) -> str:
    selector = selector.strip()
    if not selector:
        raise SystemExit("--lean-selector cannot be empty")
    if "\n" in selector:
        raise SystemExit("--lean-selector must be a single line")
    if SET_LIB_SUGG_RE.search(src):
        raise SystemExit(
            "case .lean already contains set_library_suggestions; remove it "
            "(the convention is: case files are pure theorems, selector via CLI)"
        )
    imports = list(IMPORT_LINE_RE.finditer(src))
    if not imports:
        raise SystemExit("case .lean has no import lines to anchor selector after")
    eol = src.find("\n", imports[-1].end())
    cut = eol + 1 if eol >= 0 else len(src)
    injected = (
        "\nopen Lean LibrarySuggestions in\n"
        f"set_library_suggestions {selector}\n"
    )
    return src[:cut] + injected + src[cut:]

def extract_premises(buf: str) -> list[str]:
    i = buf.find(PREMISE_ANCHOR)
    if i < 0:
        # Fallback: pre-dedup line.
        alt = "[hammer.premises] premises from premise selector:"
        i = buf.find(alt)
        if i < 0:
            raise SystemExit("could not find a hammer.premises anchor in lean output")
        i += len(alt)
    else:
        i += len(PREMISE_ANCHOR)
    # find next '['
    j = buf.find("[", i)
    if j < 0:
        raise SystemExit("found premises anchor but no opening '[' afterward")
    depth = 0
    k = j
    while k < len(buf):
        ch = buf[k]
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                break
        k += 1
    if depth != 0:
        raise SystemExit("unterminated '[...]' in premise list")
    raw = buf[j+1:k]
    items = [t.strip() for t in raw.split(",")]
    return [t for t in items if t]

def extract_tptp_body(buf: str) -> str:
    i = buf.find(TPTP_ANCHOR)
    if i < 0:
        raise SystemExit("could not find [auto.tptp.printQuery] in lean output")
    # advance past the rest of the anchor line
    eol = buf.find("\n", i)
    if eol < 0:
        return ""
    start = eol + 1
    # collect indented lines (the trace continuation block)
    out_lines = []
    for line in buf[start:].splitlines():
        if not line:
            out_lines.append("")
            continue
        if line.startswith("    ") or line.startswith("\t"):
            # strip 4-space indent
            if line.startswith("    "):
                out_lines.append(line[4:])
            else:
                out_lines.append(line.lstrip("\t"))
            continue
        # non-indented line: end of block
        break
    # trim leading/trailing blank lines
    while out_lines and out_lines[0].strip() == "":
        out_lines.pop(0)
    while out_lines and out_lines[-1].strip() == "":
        out_lines.pop()
    return "\n".join(out_lines) + "\n"

def lean_relpath(case: Case) -> str:
    """Path of lean_file relative to LEAN_PROJECT (forward slashes)."""
    rel = case.lean_file.relative_to(LEAN_PROJECT)
    return str(rel).replace(os.sep, "/")

STDIN_ERROR_RE = re.compile(r"^<stdin>:\d+:\d+: error: (.+)", re.MULTILINE)
# Errors we expect from hammer when it can't close the goal — these are
# benign and don't indicate an injection failure.
BENIGN_ERROR_PREFIXES = (
    "tactic 'aesop' failed",
    "unsolved goals",
)

def run_lean(case: Case, lake: str, selector: str) -> tuple[str, str]:
    """Returns (combined stdout+stderr, effective selector string)."""
    src = lean_source_with_selector(case.lean_file.read_text(), selector)
    cmd = [
        lake, "env", "lean",
        "-D", f"hammer.autoPremisesDefault={case.auto_premises}",
        "-D", "trace.auto.tptp.printQuery=true",
        "-D", "trace.hammer.premises=true",
        "--stdin",
    ]
    print(f"  $ (cd {LEAN_PROJECT.relative_to(REPO)} && {' '.join(cmd)} <<< <injected:{selector}>)",
          file=sys.stderr)
    proc = subprocess.run(
        cmd, cwd=LEAN_PROJECT, input=src, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    out = proc.stdout
    # If the injected `set_library_suggestions` fails to elaborate (e.g. type
    # mismatch because the user passed `mepoSelector` instead of `mepoSelector
    # (useRarity := false)`), Lean continues and `hammer` runs with the
    # built-in default selector — silently mis-reporting which selector we
    # used. Detect non-benign `<stdin>` errors and abort.
    real_errors = [
        m.group(1) for m in STDIN_ERROR_RE.finditer(out)
        if not m.group(1).startswith(BENIGN_ERROR_PREFIXES)
    ]
    if real_errors:
        sys.stderr.write(out)
        first = real_errors[0]
        # Most common cause is a bad selector expression — e.g. `mepoSelector`
        # which has type `Bool -> Selector`, not `Selector`. But other things
        # can go wrong too (Cloud returning a name the kernel can't resolve,
        # etc.), so report the verbatim error rather than guessing.
        raise SystemExit(
            f"--lean-selector {selector!r}: elaboration produced a non-benign "
            f"error: {first!r}. Full lean output written to stderr above. "
            "If the error mentions a type mismatch, the selector must be a "
            "`Selector`-typed expression (e.g. `mepoSelector (useRarity := false)`, "
            "not bare `mepoSelector`)."
        )
    # Non-zero exit code itself is expected (hammer rarely closes the goal).
    return out, selector

def write_lean_output(case: Case, premises: list[str], tptp_body: str, selector: str) -> Path:
    lines = [
        f"% LeanHammer capture for {case.name}",
        f"% premise selector: {selector}",
        f"% cap = {case.auto_premises}; selector premises (full list, in order):",
    ]
    for idx, name in enumerate(premises, 1):
        marker = "<-- sent" if idx <= case.auto_premises else "(over cap)"
        lines.append(f"%   {idx:>3}. {name:<40} {marker}")
    if not premises:
        lines.append("%   (selector returned no premises)")
    lines.append("%")
    header = "\n".join(lines) + "\n"
    out_path = TPTP_OUT / f"lean_{case.name}_zipperposition_{case.auto_premises}premises.p"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(header + tptp_body)
    return out_path


# ---------- Isabelle pass ----------------------------------------------------

HC_PLACEHOLDER = re.compile(r"\d+\s*\(\*\s*HC_MAX_FACTS\s*\*\)")

# Trailing-comment fact-name extraction. thf(...) clauses span multiple lines;
# match non-greedily up to the closing `). %`.
FACT_RE = re.compile(
    r"thf\(\s*fact_(\d+)_[^,]*,\s*axiom,.*?\)\.\s*%\s*([^\n]+)",
    re.DOTALL,
)

def prepare_isabelle_pass(case: Case, label: str, n_pass: int) -> Path:
    """Return path to the per-pass tmp dir (containing the .thy + ROOT)."""
    pass_dir = TMP_ROOT / case.name / label
    if pass_dir.exists():
        shutil.rmtree(pass_dir)
    pass_dir.mkdir(parents=True)

    thy_text = case.isabelle_file.read_text()
    if not HC_PLACEHOLDER.search(thy_text):
        raise SystemExit(
            f"{case.isabelle_file}: missing '<N> (* HC_MAX_FACTS *)' placeholder"
        )
    thy_text = HC_PLACEHOLDER.sub(f"{n_pass} (* HC_MAX_FACTS *)", thy_text, count=1)
    (pass_dir / case.isabelle_file.name).write_text(thy_text)

    # Copy the ROOT next to the theory.
    root_src = ISABELLE_CASES / "ROOT"
    if not root_src.exists():
        raise SystemExit(f"missing {root_src}")
    shutil.copy(root_src, pass_dir / "ROOT")
    return pass_dir

def run_isabelle_pass(case: Case, pass_dir: Path, isabelle: str) -> Path:
    """Run isabelle build for this pass, return path to the dumped TPTP."""
    # Isabelle computes ISABELLE_HOME_USER as $USER_HOME/.isabelle/$VERSION at
    # startup; setting ISABELLE_HOME_USER directly is ignored. Override
    # USER_HOME instead. The overlord dump lands in
    # <USER_HOME>/.isabelle/<version>/prob_zipperposition_*.p.
    iso_home = pass_dir / "iso_home"
    iso_home.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["USER_HOME"] = str(iso_home)
    cmd = [isabelle, "build", "-d", str(pass_dir), "HammerCases"]
    print(f"  $ USER_HOME={iso_home.relative_to(REPO)} {' '.join(cmd)}", file=sys.stderr)
    proc = subprocess.run(
        cmd, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    # find the dump
    dumps = sorted(iso_home.rglob("prob_zipperposition_*.p"))
    # filter out _proof.p variants — we want the full query
    full = [p for p in dumps if not p.name.endswith("_proof.p")]
    if not full:
        sys.stderr.write(proc.stdout)
        raise SystemExit(
            f"isabelle build for case '{case.name}' produced no "
            f"prob_zipperposition_*.p in {iso_home}"
        )
    # prefer prob_zipperposition_1.p if present
    chosen = next((p for p in full if p.name == "prob_zipperposition_1.p"), full[0])
    return chosen

def parse_pool_premises(pool_dump: Path) -> list[tuple[int, str]]:
    text = pool_dump.read_text()
    out = []
    for m in FACT_RE.finditer(text):
        idx = int(m.group(1))
        name = m.group(2).strip()
        out.append((idx, name))
    out.sort(key=lambda x: x[0])
    return out

def write_isabelle_output(case: Case, sent_dump: Path, ranking: list[tuple[int, str]],
                          selector: str) -> Path:
    n = case.auto_premises
    pool_size = len(ranking)
    lines = [
        f"% Sledgehammer capture for {case.name}",
        f"% premise selector: {selector}",
        f"% auto_premises (sent) = {n}; pool_cap = {case.pool_cap}; observed pool = {pool_size}",
        f"% MePo ranking from pool pass (max_facts = {case.pool_cap}):",
    ]
    for rank_idx, src in ranking:
        marker = "<-- within sent cap" if rank_idx < n else "(over cap)"
        # rank_idx is 0-indexed in fact_N; display as 1-indexed
        lines.append(f"%   {rank_idx+1:>3}. {src:<40} {marker}")
    if not ranking:
        lines.append("%   (no facts found in pool dump)")
    lines.append(
        "% NOTE: MePo's relevance threshold scales with the cap, so the body's "
        "fact set may not be the strict prefix of the pool ranking above."
    )
    lines.append("%")
    header = "\n".join(lines) + "\n"

    body = sent_dump.read_text()
    out_path = TPTP_OUT / f"isabelle_{case.name}_zipperposition_{n}sent_of_{pool_size}.p"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(header + body)
    return out_path


# ---------- driver -----------------------------------------------------------

def run_case(case: Case, *, only: str, lake: str, isabelle: str, keep_tmp: bool,
             lean_selector: str) -> None:
    print(f"=== {case.name} (cap={case.auto_premises}, pool_cap={case.pool_cap}) ===")

    if only in ("lean", "both"):
        print("[lean]")
        out, effective = run_lean(case, lake, lean_selector)
        premises = extract_premises(out)
        body = extract_tptp_body(out)
        path = write_lean_output(case, premises, body, effective)
        print(f"  -> {path.relative_to(REPO)}  ({len(premises)} premises)")

    if only in ("isabelle", "both"):
        print("[isabelle pool pass]")
        pool_dir = prepare_isabelle_pass(case, "pool", case.pool_cap)
        pool_dump = run_isabelle_pass(case, pool_dir, isabelle)
        ranking = parse_pool_premises(pool_dump)

        print("[isabelle sent pass]")
        sent_dir = prepare_isabelle_pass(case, "sent", case.auto_premises)
        sent_dump = run_isabelle_pass(case, sent_dir, isabelle)

        path = write_isabelle_output(case, sent_dump, ranking,
                                     "MePo (Sledgehammer relevance filter)")
        print(f"  -> {path.relative_to(REPO)}  ({len(ranking)} pool facts)")

        if not keep_tmp:
            shutil.rmtree(TMP_ROOT / case.name, ignore_errors=True)
            for parent in (TMP_ROOT, TMP_ROOT.parent):
                try:
                    parent.rmdir()  # only succeeds if empty
                except OSError:
                    break


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("names", nargs="*", help="case names to run (default: all)")
    ap.add_argument("--config", default=str(REPO / "scripts" / "tests.toml"))
    ap.add_argument("--keep-tmp", action="store_true",
                    help="don't delete tmp/isabelle/<case>/")
    ap.add_argument("--only", choices=("lean", "isabelle", "both"), default="both")
    ap.add_argument("--lake", default=os.environ.get("LAKE", "lake"))
    ap.add_argument("--isabelle",
                    default=resolve_isabelle())
    ap.add_argument("--lean-selector", default="mepoSelector (useRarity := false)",
                    metavar="EXPR",
                    help="Lean selector expression to inject (must have type `Selector`, "
                         "not a function — bare `mepoSelector` is `Bool -> Selector` and "
                         "won't elaborate). Examples: "
                         "'mepoSelector (useRarity := false)', "
                         "'mepoSelector (useRarity := true)', "
                         "'Cloud.premiseSelector', "
                         "'Cloud.premiseSelector <|> sineQuaNonSelector.intersperse currentFile'. "
                         "Default: 'mepoSelector (useRarity := false)', matching Isabelle's MePo.")
    args = ap.parse_args()

    cases = load_cases(Path(args.config))
    if args.names:
        wanted = set(args.names)
        cases = [c for c in cases if c.name in wanted]
        missing = wanted - {c.name for c in cases}
        if missing:
            raise SystemExit(f"no such case(s): {', '.join(sorted(missing))}")
    if not cases:
        raise SystemExit("no cases to run")

    for case in cases:
        run_case(case,
                 only=args.only, lake=args.lake, isabelle=args.isabelle,
                 keep_tmp=args.keep_tmp, lean_selector=args.lean_selector)
    return 0


if __name__ == "__main__":
    sys.exit(main())
