"""Inspect original shared optional-Struct definitions and native Events."""

from importlib.metadata import version
from itertools import product
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-events-oracle/check.py"))
NATIVE = EVENTS["NATIVE"]
lst, page_term = NATIVE["lst"], NATIVE["page_term"]


LEAN = NATIVE["LEAN"].replace(
    "import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs\n",
    """import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Defs
""", 1) + """
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Stream.Events (declarations eraseBatch eraseRow)
open Parquet.Reader.Recursive (Selection)

private def checkEvents (input : Bytes) (fields : List (Option String × Field))
    (batches : List Observation) (ending : Arrow.Events.Termination Reader.Events.Error := .eos) :
    IO Unit := do
  for selection in [Selection.field, .empty] do
    let ⟨source, trace⟩ ← take (Reader.Events.readProjected {} {} input selection)
    let wanted := if selection = .field then fields else []
    let expected := batches.map selection.batch
    unless declarations source == wanted && trace.batches.map eraseBatch == expected &&
        trace.collect.table.rows.map eraseRow == expected.flatMap (·.rows) && trace.termination == ending do
      throw (IO.userError "selected declaration, complete observations or terminal result differs")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def fixtures():
    genuine = {"optional_" + "".join(str(int(flag)) for flag in flags): NATIVE["native"](flags, struct_nullable=True)
               for flags in product((False, True), repeat=4)}
    schema, groups, wire = genuine["optional_1111"]
    carrier = NATIVE["raw_chunks"](wire)
    both = (True,) * 4
    trace = NATIVE["trace"]
    slots = {key: trace(groups[key[0]], both, key[1], optional_element=True) for key in carrier}
    first_inner = len(groups[1][0][0])

    def frames(key, atoms, cuts):
        template = carrier[key][0]
        return [NATIVE["frame"](template, atoms[lo:hi], NATIVE["WIDTHS"][key[1]])
                for lo, hi in zip([0, *cuts], [*cuts, len(atoms)], strict=True)]

    cuts_left, cuts_right = [2, first_inner], [4, first_inner + 1]
    for side, cuts in enumerate((cuts_left, cuts_right)):
        assert [slots[1, side][cut][0] for cut in cuts] == [2, 1]
        carrier[1, side] = frames((1, side), slots[1, side], cuts)
    independent = NATIVE["repack"](wire, carrier)

    ceiling = NATIVE["steps"](both)[2] + 1
    left, right = slots[1, 0], slots[1, 1]
    assert left[0] == right[0] == (0, ceiling - 1, None)
    assert left[1] == right[1] == (2, ceiling, None)
    conflicts = [i for i in range(cuts_right[-1], len(right))
                 if right[i][1] == ceiling and right[i][2] is None]
    assert len(conflicts) >= 2
    changed, later = conflicts[0], conflicts[-1]
    bad = right.copy()
    for slot in (changed, later):
        assert min(left[slot][1], ceiling) == ceiling
        bad[slot] = right[slot][0], ceiling - 1, None
    rep = right[changed][0]
    damaged = NATIVE["repack"](wire, carrier | {(1, 1): frames((1, 1), bad, cuts_right)})
    point = NATIVE["point"]
    cause = (f".topology (.conflict {changed} {point(damaged, 1, 0, changed)} "
             f"{point(damaged, 1, 1, changed)} ({rep}, {ceiling}) ({rep}, {ceiling - 1}))")
    return genuine, independent, damaged, cause


def verify(folder):
    genuine, independent, damaged, cause = fixtures()
    schema, groups, _ = genuine["optional_1111"]
    positives = genuine | {"independent_optional_cuts": (schema, groups, independent)}
    authored = {"independent_optional_cuts": independent, "late_struct_presence": damaged}
    files = {label: wire for label, (_, _, wire) in genuine.items()} | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)

    code = [LEAN]
    pages_total = 0
    for label, (decl, values, wire) in positives.items():
        ceiling, chunks = NATIVE["inspect"](wire, decl, values)
        batches = EVENTS["pyarrow_groups"](wire, decl, values)
        for (group, side), ((lo, hi), pages) in chunks.items():
            terms = lst(page_term(page, NATIVE["WIDTHS"][side]) for page in pages)
            tag = ".left" if side == 0 else ".right"
            path = NATIVE["path_term"](NATIVE["PATH"] + (NATIVE["NAMES"][side],))
            code.append(f'  checkColumn (← load folder "{label}") {group} {tag} {path} '
                        f'{ceiling} ⟨{lo}, {hi}⟩ {terms}')
            pages_total += len(pages)
        expected = EVENTS["batches_term"](decl, batches)
        code.append(f'  checkRows (← load folder "{label}") {expected}')
        code.append(f'  checkEvents (← load folder "{label}") {EVENTS["fields_term"](decl)} {expected}')

    prefix = EVENTS["batches_term"](schema, [[{"items": row} for row in groups[0]]])
    code.extend([
        f'  inconsistent (← load folder "late_struct_presence") 1 ({cause})',
        f'  checkEvents (← load folder "late_struct_presence") {EVENTS["fields_term"](schema)} '
        f'{prefix} (.readError (.group 1 ({cause})))',
    ])
    driver = folder / "OptionalElement.lean"
    driver.write_text("\n".join(code) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)
    print(f"Checked {len(positives)} accepted inputs and {pages_total} original V1 pages, "
          "and the late shared presence refusal")
    fingerprint = NATIVE["fingerprints"]
    return {"genuine_parquet": fingerprint({label: case[2] for label, case in genuine.items()}),
            "authored_parquet": fingerprint(authored)}


def producer():
    assert platform.python_implementation() == "CPython"
    return {"cpython": platform.python_version(), "pyarrow": pa.__version__, "thrift": version("thrift")}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert producer() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == {key: data for key, data in pins.items() if key != "producer"}


if __name__ == "__main__":
    main()
