"""Compile the type audit and check every printed transitive axiom list."""
import re
import subprocess
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
source = (root / "Kusner5" / "Audit.lean").read_text(encoding="utf-8")
expected = re.findall(r"^#print axioms ([A-Za-z0-9_.]+)\s*$", source, re.MULTILINE)
if len(expected) != 48 or len(set(expected)) != 48:
    raise SystemExit("Unexpected audit declaration inventory")
result = subprocess.run(
    ["lake", "env", "lean", "Kusner5/Audit.lean"],
    cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    encoding="utf-8", errors="replace",
)
if result.returncode:
    print(result.stdout)
    sys.exit(result.returncode)
matches = re.findall(
    r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",
    result.stdout, re.MULTILINE,
)
observed = {}
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, body in matches:
    if name in observed:
        raise SystemExit("Duplicate audit record: " + name)
    axioms = set()
    for item in body.split(","):
        item = item.strip()
        if not item:
            continue
        parsed = re.fullmatch(
            r"([A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*)(?:\.\{[^{}]*\})?", item
        )
        if parsed is None:
            raise SystemExit("Unrecognized axiom display: " + item)
        axioms.add(parsed.group(1))
    if not axioms <= allowed:
        raise SystemExit("Unexpected axiom in " + name + ": " + ", ".join(sorted(axioms - allowed)))
    observed[name] = axioms
if set(observed) != set(expected):
    raise SystemExit("Missing or unexpected transitive axiom records")
for name in expected:
    print(name + ": " + ", ".join(sorted(observed[name])))
print(f"PASS: {len(observed)} declarations; only the stated standard foundations")
