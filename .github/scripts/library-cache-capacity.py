#!/usr/bin/env python3
# Copyright 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
# Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
# Released under Apache 2.0, as described in LICENSE.
"""Measure exactly the reusable artifact paths saved by library-stage.yml."""

import json
import os
from pathlib import Path
import shutil
import sys


def reusable_files(build):
    for directory in (build / "lib", build / "bin"):
        if directory.is_dir():
            yield from (p for p in directory.rglob("*") if p.is_file())
    ir = build / "ir"
    if ir.is_dir():
        for path in ir.rglob("*"):
            if path.is_file() and (
                path.name.endswith((".c", ".c.hash", ".bc", ".bc.hash", ".o"))
                or ".o." in path.name
            ):
                yield path


def measure(build, free_bytes):
    files = list(reusable_files(build))
    artifact_bytes = sum(p.stat().st_size for p in files)
    # Allow the whole uncompressed payload, tar headers, and 2 GiB working room.
    required_bytes = artifact_bytes + len(files) * 2048 + 2 * 1024**3
    setup_files = list((build / "ir").rglob("*.setup.json"))
    return {
        "reusable_files": len(files),
        "reusable_bytes": artifact_bytes,
        "excluded_setup_files": len(setup_files),
        "excluded_setup_bytes": sum(p.stat().st_size for p in setup_files),
        "free_bytes": free_bytes,
        "required_bytes": required_bytes,
        "save": bool(files) and free_bytes > required_bytes,
    }


def main():
    if (os.environ.get("GITHUB_ACTIONS") != "true"
            or os.environ.get("RUNNER_ENVIRONMENT") != "github-hosted"):
        raise SystemExit("This cache writer is restricted to ephemeral GitHub-hosted runners.")
    build = Path(".lake/build")
    free = min(shutil.disk_usage(p).free for p in
               (Path.cwd(), Path(os.environ["RUNNER_TEMP"]), Path("/")))
    result = measure(build, free)
    out = Path("tmp/ci-libraries")
    out.mkdir(parents=True, exist_ok=True)
    (out / "cache-capacity.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"save={str(result['save']).lower()}\n")
    if not result["save"]:
        print("::error::No reusable artifacts or insufficient cache archive headroom; "
              "see cache-capacity.json. Cache handoff was not completed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
