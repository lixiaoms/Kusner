"""Check the SHA-256 manifest of the distribution."""
import hashlib
from pathlib import Path, PurePosixPath
import sys

root = Path(__file__).resolve().parents[1]
manifest = root / "SHA256SUMS"
expected = {}
for line in manifest.read_text(encoding="utf-8").splitlines():
    digest, name = line.split("  ", 1)
    path = PurePosixPath(name)
    if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
        raise SystemExit("Invalid digest in manifest")
    if path.is_absolute() or ".." in path.parts or name in expected:
        raise SystemExit("Invalid or duplicate file entry")
    expected[name] = digest

failures = []
for name, digest in expected.items():
    path = root.joinpath(*PurePosixPath(name).parts)
    if not path.is_file():
        failures.append("Missing: " + name)
    elif hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        failures.append("Changed: " + name)
if failures:
    print("\n".join(failures))
    sys.exit(1)
print(f"PASS: {len(expected)} distribution files match SHA256SUMS")
