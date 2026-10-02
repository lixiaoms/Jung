"""Check the pinned proof inputs, build the libraries, and audit their axioms."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_COUNT = 151


def digest(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def fail(message):
    raise SystemExit(message)


def check_sources(root):
    manifest = json.loads((root / "verification/source_manifest.json").read_text(encoding="utf-8"))
    entries = manifest["files"]
    if len(entries) != 31 or len({item["path"] for item in entries}) != 31:
        fail("The source manifest must contain 31 distinct proof/configuration inputs.")
    for entry in entries:
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts:
            fail("The source manifest contains an invalid repository-relative file name.")
        file = root / relative
        if not file.is_file():
            fail("Missing source input: " + entry["path"])
        if digest(file) != entry["sha256"] or file.stat().st_size != entry["bytes"]:
            fail("Source-integrity check failed: " + entry["path"])
    sources = sorted(root.glob("Jung/*.lean")) + sorted(root.glob("Jung5/*.lean"))
    if len(sources) != 25:
        fail("Expected 25 proof modules.")
    recorded = {item["path"] for item in entries}
    for source in sources:
        if source.relative_to(root).as_posix() not in recorded:
            fail("A proof module is missing from the source manifest.")
        text = source.read_text(encoding="utf-8")
        if re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*axiom\s", text, re.MULTILINE):
            fail("An unaccepted proof construct occurs in " + source.relative_to(root).as_posix())
    return len(entries)


def check_audit(root, output):
    if "sorryAx" in output or "error:" in output or "PANIC" in output:
        fail("The axiom audit contains a proof or compilation error.")
    expected = set(re.findall(r"^#print axioms ([A-Za-z0-9_.]+)",
                              (root / "Audit.lean").read_text(encoding="utf-8"), re.MULTILINE))
    reports = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.MULTILINE)
    actual = [name for name, _ in reports]
    if len(expected) != EXPECTED_COUNT or len(actual) != EXPECTED_COUNT or set(actual) != expected:
        fail("The audit does not contain exactly the 151 expected declarations.")
    foundations = set()
    for name, axioms in reports:
        for axiom in filter(None, (item.strip() for item in axioms.split(","))):
            normalized = re.sub(r"\.\{[^}]*\}", "", axiom)
            if normalized not in ALLOWED:
                fail("Unexpected axiom in " + name + ": " + normalized)
            foundations.add(normalized)
    return len(reports), sorted(foundations)


def run(root, command):
    result = subprocess.run(command, cwd=root, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding="utf-8")
    if result.returncode:
        sys.stdout.write(result.stdout)
        fail("Command failed: " + " ".join(command))
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true",
                        help="Check source hashes and the archived audit without building Lean.")
    parser.add_argument("--audit-log", type=Path,
                        help="Use a specified audit log with --check-only.")
    args = parser.parse_args()
    if args.audit_log is not None and not args.check_only:
        parser.error("--audit-log requires --check-only")
    root = Path(__file__).resolve().parent
    inputs = check_sources(root)
    if args.check_only:
        log = args.audit_log if args.audit_log is not None else root / "verification/audit.log"
        output = log.read_text(encoding="utf-8")
        mode = "source integrity and existing audit"
    else:
        run(root, ["lake", "build", "Jung", "Jung5"])
        output = run(root, ["lake", "env", "lean", "-j1", "Audit.lean"])
        mode = "source integrity, Lean build, and fresh axiom audit"
    declarations, foundations = check_audit(root, output)
    if not args.check_only:
        (root / "audit.log").write_text(output, encoding="utf-8")
    print(json.dumps({"accepted": True, "mode": mode, "checked_inputs": inputs,
                      "proof_modules": 25, "audited_declarations": declarations,
                      "foundations": foundations}, indent=2))


if __name__ == "__main__":
    main()
