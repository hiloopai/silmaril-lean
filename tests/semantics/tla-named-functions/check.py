#!/usr/bin/env python3
"""Check the pinned vmem LET body and the semantic bridge's Lean examples."""

import os
from pathlib import Path
import runpy
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REVISION = "bc1b506bdcad80bb518bf3776a9161c34ff0fc4c"
SOURCE = "test-model/examples/SpecifyingSystems/CachingMemory/WriteThroughCache.tla"
SHA256 = "d63221a21377ee59c707dcf1ec05dd73be7616674343052a2b0d794b0c0526a2"


def main():
    lake = os.environ.get("LAKE", "lake")
    staging = runpy.run_path(str(HERE.parent / "tla-parser" / "check.py"))
    if staging["REVISION"] != REVISION:
        raise RuntimeError("review the vmem bridge after the parser fixture revision changes")
    subprocess.run(
        [lake, "build", "--wfail", "+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs",
         "+Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Examples"],
        cwd=ROOT,
        check=True,
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-tla-vmem-") as directory:
        path = Path(directory) / "WriteThroughCache.tla"
        staging["download"](f"{staging['RAW']}/{SOURCE}", path, SHA256)
        subprocess.run(
            [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
             str(HERE / "WriteThroughCache.lean"), str(path)],
            cwd=ROOT,
            check=True,
        )


if __name__ == "__main__":
    main()
