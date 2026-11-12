#!/usr/bin/env python3
"""Store generated source blobs in the same repository; never update a branch.
The caller separately reviews compiler evidence before a leased ref update.
"""
from __future__ import annotations
import base64
import hashlib
import json
import os
from pathlib import Path
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
REPO = "randogelist/Methlib"
PREFIX = "regularity-B-assembly/Singular-Axiomatic-closure/H12_FRONTIER/"


def main() -> None:
    if os.environ.get("GITHUB_REPOSITORY") != REPO:
        raise RuntimeError("repository lock mismatch")
    token = os.environ["GH_TOKEN"]
    evidence = ROOT / "evidence/frontier"
    source = json.loads((evidence / "generated-source-manifest.json").read_text(encoding="utf-8"))
    result = []
    for item in source["generated"]:
        relative = item["path"]
        if not (relative.startswith("SingularClosure/H12Frontier/")
                or relative.startswith("ci/frontier_audits/")
                or relative == "ci/frontier_plan.json") or ".." in Path(relative).parts:
            raise RuntimeError("generated path outside allowlist")
        content = (ROOT / relative).read_bytes()
        if hashlib.sha256(content).hexdigest() != item["sha256"]:
            raise RuntimeError("generated source hash mismatch")
        request = urllib.request.Request(f"https://api.github.com/repos/{REPO}/git/blobs",
            data=json.dumps({"content": base64.b64encode(content).decode("ascii"),
                             "encoding": "base64"}).encode("utf-8"),
            headers={"Authorization": "Bearer " + token,
                     "Accept": "application/vnd.github+json", "Content-Type": "application/json",
                     "X-GitHub-Api-Version": "2022-11-28"}, method="POST")
        with urllib.request.urlopen(request, timeout=60) as response:
            data = json.load(response)
        if data["sha"] != item["git_blob_sha"]:
            raise RuntimeError("stored Git blob hash mismatch")
        result.append({"path": PREFIX + relative, "mode": "100644", "type": "blob", "sha": data["sha"]})
        print("STORED_SOURCE_BLOB:" + relative + ":" + data["sha"], flush=True)
    (evidence / "generated-blobs.json").write_text(json.dumps({"repository": REPO,
        "source_commit": os.environ.get("GITHUB_SHA"), "branch_updated": False,
        "tree_elements": result}, indent=2)+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
