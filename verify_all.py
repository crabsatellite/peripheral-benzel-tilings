#!/usr/bin/env python3
"""Fail-closed audit for the combined manuscript and both Lean tracks."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
LEAN_ROOT = ROOT / "lean4"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LABEL = re.compile(r"\\label\{([^}]+)\}")
FORBIDDEN_SOURCE = re.compile(
    r"(?m)^\s*(?:axiom|opaque)\b|"
    r"\b(?:sorry|admit|native_decide|Lean\.trustCompiler|implemented_by|"
    r"extern|unsafe|Lean\.ofReduceBool|sorryAx)\b"
)

EXPECTED_D4_LABELS = [
    "thm:main", "eq:main-formula", "eq:benzel", "eq:uvw",
    "eq:difference-table", "lem:owner-domain", "eq:potential",
    "eq:energy-table", "thm:defects", "eq:region-energy",
    "eq:bone-counts", "eq:defect-cores", "lem:three-paths",
    "eq:path-monotonicity", "eq:core-separation", "prop:bijection",
    "eq:R", "eq:R-coeff", "thm:d4-sum", "eq:A", "eq:C", "eq:H",
    "eq:ballot-sum", "eq:phi", "eq:determinant", "eq:good-expansion",
    "eq:q", "eq:diag-delta", "eq:A-good", "eq:C-good", "eq:H-good",
    "eq:three-components",
]

REQUIRED_D4_AUDIT = {
    "FiniteDefects.d4LiteralBoundaryFactorizationStatement_proved",
    "FiniteDefects.d4ConwayLagariasStatement_proved",
    "FiniteDefects.offsetD4LiteralTilingEquiv",
    "FiniteDefects.d4OneDefect_from_generalFiniteDefect",
    "FiniteDefects.d4OneDefectKernelOnly",
    "FiniteDefects.d4LiteralTilingEquivPathData_kernelOnly",
    "FiniteDefects.d4LiteralTilingEquivSigmaArmTriple_kernelOnly",
    "FiniteDefects.d4SpecializedTilingCount_eq_literal",
    "FiniteDefects.d4LiteralTilingCount_ballot_formula_kernelOnly",
    "FiniteDefects.d4GeneratingFunctionKernelOnly",
    "FiniteDefects.d4Good_generating_function_literal_kernelOnly",
    "FiniteDefects.generalBoneCountKernelOnly",
    "FiniteDefects.generalFiniteDefectKernelOnly",
}


def fail(message: str) -> None:
    raise SystemExit(f"[combined-audit:error] {message}")


def run(command: list[str], *, cwd: Path = ROOT) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode:
        fail(f"command failed ({' '.join(command)}):\n{completed.stdout}")
    return completed.stdout


def strip_lean_comments_and_strings(source: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    string = False
    escaped = False
    while index < len(source):
        pair = source[index:index + 2]
        character = source[index]
        if line_comment:
            if character == "\n":
                line_comment = False
                output.append("\n")
            index += 1
        elif block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                if character == "\n":
                    output.append("\n")
                index += 1
        elif string:
            if character == '"' and not escaped:
                string = False
            escaped = character == "\\" and not escaped
            if character != "\\":
                escaped = False
            index += 1
        elif pair == "--":
            line_comment = True
            index += 2
        elif pair == "/-":
            block_depth = 1
            index += 2
        elif character == '"':
            string = True
            escaped = False
            index += 1
        else:
            output.append(character)
            index += 1
    if block_depth or string:
        fail("unterminated Lean comment or string")
    return "".join(output)


def source_policy() -> int:
    count = 0
    roots = [
        LEAN_ROOT / "BenzelProblem6Kernel",
        LEAN_ROOT / "FiniteDefects",
        LEAN_ROOT / "D4KernelOnly",
    ]
    paths = [LEAN_ROOT / "PeripheralBenzelPublication.lean"]
    for source_root in roots:
        paths.extend(source_root.rglob("*.lean"))
    for path in sorted(paths):
        executable = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        match = FORBIDDEN_SOURCE.search(executable)
        if match:
            line = executable.count("\n", 0, match.start()) + 1
            fail(f"forbidden proof escape in {path.relative_to(LEAN_ROOT)}:{line}")
        count += 1
    return count


def manuscript_labels() -> tuple[int, int]:
    problem6 = LABEL.findall(
        (ROOT / "peripheral_benzel_tilings.tex").read_text(encoding="utf-8")
    )
    d4_prefixed = LABEL.findall((ROOT / "d4_extension.tex").read_text(encoding="utf-8"))
    d4 = [label.removeprefix("d4:") for label in d4_prefixed]
    if d4 != EXPECTED_D4_LABELS:
        fail("first-defect manuscript label order or identity drifted")
    combined = problem6 + d4_prefixed
    duplicates = sorted({label for label in combined if combined.count(label) > 1})
    if duplicates:
        fail(f"duplicate combined labels: {duplicates}")
    return len(problem6), len(d4)


def audit_d4_axioms(output: str) -> set[str]:
    observed = set(re.findall(r"'([^']+)' depends on axioms", output))
    missing = sorted(REQUIRED_D4_AUDIT - observed)
    if missing:
        fail(f"missing d4 axiom-audit endpoints: {missing}")
    axioms: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.S):
        axioms.update(item.strip() for item in body.split(",") if item.strip())
    unexpected = sorted(axioms - ALLOWED_AXIOMS)
    if unexpected:
        fail(f"unexpected d4 axioms: {unexpected}")
    return axioms


def main() -> int:
    problem6_labels, d4_labels = manuscript_labels()
    sources = source_policy()
    problem6_receipt = run([sys.executable, "verify_formula_map.py"])
    if "formula_map_kernel_audit=passed" not in problem6_receipt:
        fail("missing Problem 6 audit receipt")
    run(["lake", "build", "PeripheralBenzelPublication"], cwd=LEAN_ROOT)
    d4_audit = run(
        [
            "lake", "env", "lean", "--trust=0", "-M", "16384", "-q",
            "D4KernelOnly/D4KernelOnlyFinalAudit.lean",
        ],
        cwd=LEAN_ROOT,
    )
    axioms = audit_d4_axioms(d4_audit)
    print(
        "combined_kernel_audit=passed "
        f"problem6_labels={problem6_labels} d4_labels={d4_labels} "
        f"lean_sources={sources} trust=0 axioms={','.join(sorted(axioms))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
