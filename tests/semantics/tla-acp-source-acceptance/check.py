#!/usr/bin/env python3
"""Check the Init, TypeInv and progN denotations from pinned ACP_SB."""

import os
from pathlib import Path
import runpy
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REVISION = "bc1b506bdcad80bb518bf3776a9161c34ff0fc4c"
ACP_SB = "test-model/examples/acp/ACP_SB.tla"


def main():
    lake = os.environ.get("LAKE", "lake")
    staging = runpy.run_path(str(HERE.parent / "tla-parser" / "check.py"))
    if staging["REVISION"] != REVISION:
        raise RuntimeError("review the ACP_SB pin after the parser fixture revision change")

    subprocess.run(
        [
            lake, "build", "--wfail",
            "+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs",
            "+Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs",
            "+Silmaril.Logic.Temporal.TLA.DataElab.Collections.Tagged",
            "+Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Thms",
            "+Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Thms",
            "+Silmaril.Logic.Temporal.TLA.DataBridge.Thms",
        ],
        cwd=ROOT,
        check=True,
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-acp-sb-") as directory:
        source = Path(directory) / "ACP_SB.tla"
        staging["download"](f"{staging['RAW']}/{ACP_SB}", source, staging["UPSTREAM"][ACP_SB])
        subprocess.run(
            [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
             str(HERE / "ACP_SB.lean")],
            cwd=ROOT,
            env={**os.environ, "SILMARIL_ACP_SB_SOURCE": str(source)},
            check=True,
        )


if __name__ == "__main__":
    main()
