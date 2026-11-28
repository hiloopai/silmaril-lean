#!/usr/bin/env python3
"""Check the pinned vmem source profile and the semantic bridge's Lean examples."""

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
STANDARD = {
    "Naturals": "73f2a68412039aa86f37ad08f0d0fef50fa8327d0ad8806f515548c75e9d9d84",
    "Sequences": "f613cffe14133769f0972b6f6e0139aaf0773004a51bac88ada382426e3eb7f4",
}
MEMORY = {
    "MemoryInterface": "cb496258606d5323b1a8f1f4450460a676df68ca0f945764ac80e763078d2e5a",
    "InternalMemory": "8ba1a82a0f418b6b3c6c99ad06adfe808d604670d0d8c31ce05d53ed16d2aa73",
    "Memory": "5f8e923b62c0f67535a59374a092f502676f21eda378108f3b85caca447174e0",
}


def main():
    lake = os.environ.get("LAKE", "lake")
    staging = runpy.run_path(str(HERE.parent / "tla-parser" / "check.py"))
    if staging["REVISION"] != REVISION:
        raise RuntimeError("review the vmem bridge after the parser fixture revision changes")
    subprocess.run(
        [lake, "build", "--wfail", "+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs",
         "+Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Examples",
         "+Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Thms"],
        cwd=ROOT,
        check=True,
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-tla-vmem-") as directory:
        for name, sha256 in STANDARD.items():
            standard = f"src/tla2sany/StandardModules/{name}.tla"
            staging["download"](f"{staging['RAW']}/{standard}", Path(directory) / f"{name}.tla", sha256)
        for name, sha256 in {**MEMORY, "WriteThroughCache": SHA256}.items():
            source = Path(SOURCE).with_name(f"{name}.tla")
            staging["download"](f"{staging['RAW']}/{source}", Path(directory) / source.name, sha256)
        subprocess.run(
            [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
             str(HERE / "WriteThroughCache.lean"), directory, REVISION],
            cwd=ROOT,
            check=True,
        )


if __name__ == "__main__":
    main()
