"""Extract an isolated unchanged foundation and candidate overlay; no Lean."""
from pathlib import Path
import argparse
import hashlib
import io
import json
import subprocess
import tarfile

BASE = "09dfe94a1ef150e21d09df3013fbe09002ef139c"
FOUNDATION = "regularity-B-assembly/Singular-Axiomatic-closure"
OVERLAY = "Quasi-Fefferman-B"
p = argparse.ArgumentParser()
p.add_argument("--repository", required=True)
p.add_argument("--output", required=True)
args = p.parse_args()
repo, output = Path(args.repository).resolve(), Path(args.output).resolve()
if output.exists():
    raise SystemExit(f"Refusing to overwrite existing package: {output}")
def git(*a):
    return subprocess.check_output(["git", "-C", str(repo), *a])
head = git("rev-parse", "HEAD").decode().strip()
base_tree = git("rev-parse", f"{BASE}:{FOUNDATION}").decode().strip()
head_tree = git("rev-parse", f"{head}:{FOUNDATION}").decode().strip()
if head_tree != base_tree:
    raise SystemExit("Foundation tree differs from the audited pinned foundation")
output.mkdir(parents=True)
def extract(spec, dest):
    dest.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(git("archive", spec))) as archive:
        # Only git-tracked regular files/directories under the requested tree.
        for member in archive.getmembers():
            path = Path(member.name)
            if path.is_absolute() or ".." in path.parts or member.issym() or member.islnk():
                raise SystemExit(f"Unsafe archive member: {member.name}")
        archive.extractall(dest, filter="data")
extract(f"{head}:{FOUNDATION}", output)
extract(f"{head}:{OVERLAY}", output / "qfb")
evidence = output / "evidence"
evidence.mkdir(exist_ok=True)
files = {str(f.relative_to(output)).replace("\\", "/"): hashlib.sha256(f.read_bytes()).hexdigest()
         for f in sorted(output.rglob("*")) if f.is_file() and "evidence" not in f.parts}
(evidence / "source-snapshot.json").write_text(json.dumps({
    "commit": head, "foundation_commit": BASE, "foundation_tree": base_tree,
    "native_source_mutations": 0, "files": files}, indent=2) + "\n")
print(json.dumps({"commit": head, "foundation_tree": base_tree,
                  "native_source_mutations": 0, "files": len(files)}))
