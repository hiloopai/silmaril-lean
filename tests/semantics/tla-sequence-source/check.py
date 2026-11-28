#!/usr/bin/env python3
"""Check the pinned BoundedQueue denotations and safety theorem."""

import os
from pathlib import Path
import runpy
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PARSER = HERE.parent / "tla-parser"
QUEUE_SHA256 = "a92c8cfcb94e6a88b96d2d260def76c66bdffb45472c5df1a50c6223640ecccf"
STANDARD = {
    "Naturals.tla": "73f2a68412039aa86f37ad08f0d0fef50fa8327d0ad8806f515548c75e9d9d84",
    "Sequences.tla": "f613cffe14133769f0972b6f6e0139aaf0773004a51bac88ada382426e3eb7f4",
}


def main():
    lake = os.environ.get("LAKE", "lake")
    staging = runpy.run_path(str(PARSER / "check.py"))
    queue = PARSER / "BoundedQueue.tla"
    staging["verify"](queue, QUEUE_SHA256)
    subprocess.run(
        [lake, "build", "--wfail",
         "+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs",
         "+Silmaril.Logic.Temporal.TLA.DataElab.Sequences.Thms",
         "+Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Thms"],
        cwd=ROOT,
        check=True,
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-tla-sequences-") as directory:
        for name, digest in STANDARD.items():
            staging["download"](f"{staging['RAW']}/src/tla2sany/StandardModules/{name}",
                                Path(directory) / name, digest)
        subprocess.run(
            [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
             str(HERE / "BoundedQueue.lean")],
            cwd=ROOT,
            env={**os.environ, "SILMARIL_TLA_SEQUENCE_FIXTURES": directory,
                 "SILMARIL_TLA_SEQUENCE_REVISION": staging["REVISION"],
                 "SILMARIL_TLA_QUEUE_FIXTURE": str(queue)},
            check=True,
        )


if __name__ == "__main__":
    main()
