#!/usr/bin/env python3
"""Fail-closed exact manuscript-map and trust-zero kernel audit."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent
LEAN_ROOT = ROOT / "lean4"
SOURCE_ROOT = LEAN_ROOT / "BenzelProblem6Kernel"
PAPER = ROOT / "peripheral_benzel_tilings.tex"

PUBLICATION_ROOT = Path("BenzelProblem6Kernel/PublicationRoot.lean")
THEOREM_MAP = Path("BenzelProblem6Kernel/KernelTheoremMap.lean")
FORMULA_MAP = Path("BenzelProblem6Kernel/ManuscriptFormulaMap.lean")
PUBLICATION_AXIOM_AUDIT = Path("BenzelProblem6Kernel/AxiomAudit.lean")
MANUSCRIPT_AXIOM_AUDIT = Path("BenzelProblem6Kernel/ManuscriptAxiomAudit.lean")

LEAN_MEMORY_MB = "30000"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LABEL_PATTERN = re.compile(r"\\label\{((?:thm|lem|prop|cor|eq):[^}]+)\}")
MAP_LABEL_PATTERN = re.compile(r"^-- ((?:thm|lem|prop|cor|eq):\S+)\s*$")
CHECK_PATTERN = re.compile(
    r"^#check\s+(BenzelProblem6Kernel\.[A-Za-z0-9_]+)\s*$"
)
AXIOM_LINE_PATTERN = re.compile(
    r"^#print axioms\s+(BenzelProblem6Kernel\.[A-Za-z0-9_]+)\s*$"
)


def fail(message: str) -> None:
    raise SystemExit(f"[formula-map-kernel-audit:error] {message}")


def run(command: list[str], *, cwd: Path = LEAN_ROOT) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    output = completed.stdout + completed.stderr
    if completed.returncode:
        fail(f"command failed ({' '.join(command)}):\n{output}")
    return output


def run_lean(source: Path) -> str:
    return run(
        [
            "lake",
            "env",
            "lean",
            "--trust=0",
            "-M",
            LEAN_MEMORY_MB,
            "-q",
            str(source),
        ]
    )


def strip_lean_comments_and_strings(source: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    string = False
    escaped = False
    while index < len(source):
        pair = source[index : index + 2]
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


def check_source_policy() -> int:
    declaration_escape = re.compile(r"(?m)^\s*(?:axiom|opaque)\b")
    proof_escape = re.compile(
        r"\b(?:sorry|admit|native_decide|Lean\.trustCompiler|"
        r"implemented_by|extern|unsafe|Lean\.ofReduceBool|sorryAx)\b"
    )
    scanned = 0
    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        executable = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        for pattern, category in (
            (declaration_escape, "hidden declaration"),
            (proof_escape, "proof escape"),
        ):
            match = pattern.search(executable)
            if match:
                line = executable.count("\n", 0, match.start()) + 1
                fail(f"{category} in {path.relative_to(LEAN_ROOT)}:{line}")
        scanned += 1
    return scanned


def paper_labels() -> set[str]:
    labels = LABEL_PATTERN.findall(PAPER.read_text(encoding="utf-8"))
    duplicates = sorted({label for label in labels if labels.count(label) > 1})
    if duplicates:
        fail(f"duplicate manuscript labels: {duplicates}")
    if not labels:
        fail("manuscript contains no theorem/formula labels")
    return set(labels)


def formula_map_contract() -> tuple[set[str], set[str]]:
    labels: list[str] = []
    endpoints_by_label: dict[str, list[str]] = {}
    current: str | None = None
    for raw_line in (LEAN_ROOT / FORMULA_MAP).read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        label_match = MAP_LABEL_PATTERN.fullmatch(line)
        if label_match:
            current = label_match.group(1)
            labels.append(current)
            endpoints_by_label.setdefault(current, [])
            continue
        check_match = CHECK_PATTERN.fullmatch(line)
        if check_match:
            if current is None:
                fail(f"unlabelled #check endpoint: {check_match.group(1)}")
            endpoints_by_label[current].append(check_match.group(1))

    duplicates = sorted({label for label in labels if labels.count(label) > 1})
    if duplicates:
        fail(f"duplicate formula-map labels: {duplicates}")
    empty = sorted(label for label, endpoints in endpoints_by_label.items() if not endpoints)
    if empty:
        fail(f"formula-map labels without endpoints: {empty}")
    endpoints = {endpoint for values in endpoints_by_label.values() for endpoint in values}
    if not endpoints:
        fail("formula map contains no Lean endpoints")
    return set(labels), endpoints


def axiom_entries(source: Path) -> set[str]:
    entries = {
        match.group(1)
        for line in (LEAN_ROOT / source).read_text(encoding="utf-8").splitlines()
        if (match := AXIOM_LINE_PATTERN.fullmatch(line.strip()))
    }
    if not entries:
        fail(f"axiom audit contains no entries: {source}")
    return entries


def publication_endpoints() -> set[str]:
    text = (LEAN_ROOT / PUBLICATION_ROOT).read_text(encoding="utf-8")
    names = set(
        re.findall(
            r"(?m)^\s*(?:noncomputable\s+)?def\s+(publication_[A-Za-z0-9_]+)",
            text,
        )
    )
    if not names:
        fail("PublicationRoot.lean contains no publication endpoints")
    return {f"BenzelProblem6Kernel.{name}" for name in names}


def audit_axiom_output(output: str, expected: set[str], source: Path) -> set[str]:
    receipts = {
        match.group(1): match.group(2)
        for match in re.finditer(
            r"(?ms)^'([^']+)' "
            r"(does not depend on any axioms|depends on axioms:\s*\[[^\]]*\])",
            output,
        )
    }
    observed = set(receipts)
    missing = sorted(expected - observed)
    extra = sorted(observed - expected)
    if missing or extra:
        fail(f"axiom receipt mismatch in {source}: missing={missing}, extra={extra}")

    all_axioms: set[str] = set()
    for endpoint, receipt in receipts.items():
        payload_match = re.search(r"\[([^\]]*)\]", receipt, re.S)
        if payload_match is None:
            continue
        axioms = {
            token.strip()
            for token in re.sub(r"\s+", " ", payload_match.group(1)).split(",")
            if token.strip()
        }
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            fail(f"unexpected axioms for {endpoint}: {sorted(unexpected)}")
        all_axioms.update(axioms)
    return all_axioms


def main() -> int:
    scanned = check_source_policy()
    labels = paper_labels()
    mapped_labels, mapped_endpoints = formula_map_contract()
    missing_labels = sorted(labels - mapped_labels)
    extra_labels = sorted(mapped_labels - labels)
    if missing_labels or extra_labels:
        fail(
            f"exact formula-map mismatch: missing={missing_labels}, extra={extra_labels}"
        )

    manuscript_audit_entries = axiom_entries(MANUSCRIPT_AXIOM_AUDIT)
    missing_manuscript_receipts = sorted(mapped_endpoints - manuscript_audit_entries)
    extra_manuscript_receipts = sorted(manuscript_audit_entries - mapped_endpoints)
    if missing_manuscript_receipts or extra_manuscript_receipts:
        fail(
            "manuscript axiom-audit mismatch: "
            f"missing={missing_manuscript_receipts}, extra={extra_manuscript_receipts}"
        )

    publication_expected = publication_endpoints()
    publication_audit_entries = axiom_entries(PUBLICATION_AXIOM_AUDIT)
    if publication_expected != publication_audit_entries:
        fail(
            "publication axiom-audit mismatch: "
            f"missing={sorted(publication_expected - publication_audit_entries)}, "
            f"extra={sorted(publication_audit_entries - publication_expected)}"
        )

    run(
        [
            "lake",
            "build",
            "BenzelProblem6Kernel.PublicationRoot",
        ]
    )
    run_lean(PUBLICATION_ROOT)
    run_lean(THEOREM_MAP)
    run_lean(FORMULA_MAP)
    publication_axioms = audit_axiom_output(
        run_lean(PUBLICATION_AXIOM_AUDIT),
        publication_audit_entries,
        PUBLICATION_AXIOM_AUDIT,
    )
    manuscript_axioms = audit_axiom_output(
        run_lean(MANUSCRIPT_AXIOM_AUDIT),
        manuscript_audit_entries,
        MANUSCRIPT_AXIOM_AUDIT,
    )

    all_axioms = publication_axioms | manuscript_axioms
    print(
        "formula_map_kernel_audit=passed "
        f"labels={len(labels)} endpoints={len(mapped_endpoints)} "
        f"publication_endpoints={len(publication_expected)} "
        f"sources={scanned} trust=0 axioms={','.join(sorted(all_axioms))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
