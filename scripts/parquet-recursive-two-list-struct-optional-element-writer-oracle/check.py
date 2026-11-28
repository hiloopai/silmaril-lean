"""Verify Lean-written optional Struct elements and both original slot streams."""

import json
from pathlib import Path
import runpy
import tempfile


HERE = Path(__file__).resolve().parent
WRITER = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-writer-oracle/check.py"))
NATIVE = WRITER["NATIVE"]
input_term = WRITER["input_term"]


EXTRA_LEAN = """\
private def sharedNull (input : Input) : Input :=
  { input with groups := [⟨1, [[some (.list [some (.list [none, some (.struct [none, none])])])]]⟩] }

private def checkSharedNullReadback (model : Input) : IO Unit := do
  let output ← take (emit { chunk.maxSlots := 2, maxTotalSlots := 4 } model)
  let altered : Arrow.RecursiveSchema.Batch.Rows.Row := [some (.list [some (.list [some (.struct [none, none]), none])])]
  deny .readbackMismatch (certify {} { model with groups := [⟨1, [altered]⟩] } output)
"""


def refusals(positives):
    cases = {label: (schema, groups) for label, schema, groups, _ in positives}
    schema, groups = cases["32_64_1111"]
    valid = input_term(schema, groups)
    required_left = input_term(*cases["32_64_1101"])
    required_right = input_term(*cases["32_64_1110"])
    first = [NATIVE["trace"](groups[0], (True,) * 4, side, optional_element=True) for side in (0, 1)]
    bodies = [8 + 4 * len(trace) + width * sum(word is not None for _, _, word in trace)
              for trace, width in zip(first, (4, 8), strict=True)]
    assert bodies[0] < bodies[1]
    slots = [len(NATIVE["trace"](group, (True,) * 4, 0, optional_element=True)) for group in groups]
    null_fields = '[⟨1, [[some (.list [some (.list [some (.struct [none, none])])])]]⟩]'
    bad_arity = '[⟨1, [[some (.list [some (.list [some (.struct [none])])])]]⟩]'
    bad_type = '[⟨1, [[some (.list [some (.list [some (.int32 1)])])]]⟩]'
    return [
        f'  refuse (.slotLimit 0 2) {{ chunk.maxSlots := 1 }} (sharedNull {valid})',
        f'  refuse (.totalSlotLimit 0 4) {{ maxTotalSlots := 3 }} (sharedNull {valid})',
        f'  checkSharedNullReadback (sharedNull {valid})',
        f'  refuse (.column 0 .left (.projection 0)) {{}} ({{ ({required_left} : Input) with groups := {null_fields} }})',
        f'  refuse (.column 0 .right (.projection 0)) {{}} ({{ ({required_right} : Input) with groups := {null_fields} }})',
        f'  refuse (.projection 0) {{}} ({{ ({valid} : Input) with groups := {bad_arity} }})',
        f'  refuse (.projection 0) {{}} ({{ ({valid} : Input) with groups := {bad_type} }})',
        f'  refuse (.column 0 .right (.bodyLimit 0)) {{ chunk.maxBodyBytes := {bodies[0]} }} {valid}',
        f'  refuse (.totalSlotLimit 1 {2 * sum(slots)}) {{ maxTotalSlots := {2 * slots[0]} }} {valid}',
        f'  refuse (.schema (.depth [])) {{ schema.snapshot.maxSchemaDepth := 6 }} {valid}',
        f'  refuse (.schema .fileLimit) {{ schema.maxFileBytes := 11 }} {valid}',
        f'  refuse (.groupLimit 2) {{ maxGroups := 1 }} {valid}',
    ]


def verify(folder):
    positives = list(WRITER["cases"](optional_element=True))
    source = WRITER["LEAN"].replace("public def main", EXTRA_LEAN + "\npublic def main")
    return WRITER["verify_cases"](folder, positives, refusals(positives), source)


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert WRITER["producer"]() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == pins["lean_parquet"], "optional Struct output pins changed"


if __name__ == "__main__":
    main()
