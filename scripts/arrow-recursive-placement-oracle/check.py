"""Compare schema-only descriptor positions with pinned PyArrow IPC."""

import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ORACLES = HERE.parent
BATCH = runpy.run_path(str(ORACLES / "arrow-recursive-batch-oracle/check.py"))
WRITER = runpy.run_path(str(ORACLES / "arrow-recursive-schema-writer-oracle/check.py"))
SCHEMA = BATCH["SCHEMA_ORACLE"]
fingerprint, kind_term = (SCHEMA[key] for key in ("fingerprint", "kind_term"))
raw_schema = WRITER["raw_schema"]

LEAN = """\
module

import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
meta import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement.Defs
meta import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs

open Silmaril Silmaril.Formats.Arrow.RecursiveSchema
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement (Plan ofSchema)

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal {repr cause}")

private def load (folder : System.FilePath) (label : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (folder / (label ++ ".arrow"))
  return .leaf bytes.size (KBytes.leVal bytes.data.toList)

private def check (input : KBytes) (limits : Limits) (next : Nat) (wanted : Plan) : IO Schema := do
  let (schema, actualNext, actual) ← take (Batch.Placement.read limits input)
  unless actualNext = next do throw (IO.userError "schema cursor differs")
  unless actual == wanted do throw (IO.userError s!"descriptor placement differs: {repr actual}")
  return schema

private def emit (folder : System.FilePath) (label : String) (next : Nat) (wanted : Plan) :
    IO Unit := do
  let schema ← check (← load folder label) {} next wanted
  let emitted ← take (Writer.emit {} schema)
  let (recovered, _, plan) ← take (Batch.Placement.read {} emitted)
  unless recovered == schema && plan == wanted do throw (IO.userError "emitted placement differs")
  IO.FS.writeBinFile (folder / (label ++ "-lean.arrow")) emitted.toByteArray

private def refuse {α : Type} (wanted : Batch.Placement.Error) (result : Except Batch.Placement.Error α) : IO Unit :=
  match result with
  | .error actual => unless actual = wanted do
      throw (IO.userError s!"expected {repr wanted}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"admitted input expected to fail with {repr wanted}")
"""


def pins(name):
    return json.loads((ORACLES / f"{name}-oracle/fixtures.json").read_text(encoding="utf-8"))


def plan_term(fields):
    """Number the schema tree using Arrow's flattened IPC descriptor order."""
    nodes, buffers = [], []

    def describe(field, path):
        name, nullable, tag, width, children = field
        now = len(nodes), len(buffers)
        nodes.append(path)
        buffers.append((path, "validity"))
        if tag == 12:
            assert len(children) == 1
            buffers.append((path, "offsets32"))
        elif tag == 2:
            assert not children
            buffers.append((path, f"values{width}"))
        else:
            assert tag == 13
        nested = [describe(item, path + (i,)) for i, item in enumerate(children)]
        label = "none" if name is None else f"(some {json.dumps(name, ensure_ascii=False)})"
        return (f".field {label} {str(nullable).lower()} {kind_term(tag, width)} "
                f"⟨{now[0]}, {now[1]}⟩ [{', '.join(nested)}]")

    declarations = [describe(field, (ordinal,)) for ordinal, field in enumerate(fields)]
    return f"⟨[{', '.join(declarations)}], ⟨{len(nodes)}, {len(buffers)}⟩⟩", nodes, buffers


def main():
    emitted_pins = pins("arrow-recursive-schema-writer")
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == emitted_pins["producer"]["cpython"]
    assert pa.__version__ == emitted_pins["producer"]["pyarrow"]

    writer_inputs, _ = WRITER["produce"](pa)
    emit = ("four_level", "repeated_children", "zero_width")
    inputs = {label: writer_inputs[label] for label in emit}
    assert {label: fingerprint(wire) for label, wire in inputs.items()} == {
        label: emitted_pins["genuine_ipc"][label] for label in emit}

    batch_inputs = BATCH["produce"](pa)
    inputs["populated"] = batch_inputs["populated"]
    assert fingerprint(inputs["populated"]) == pins("arrow-recursive-batch")["genuine_ipc"]["populated"]

    schema_inputs, edits = SCHEMA["fixtures"](pa)
    schema_pins = pins("arrow-recursive-schema")
    inputs["large_list"] = schema_inputs["large_list"]
    assert fingerprint(inputs["large_list"]) == schema_pins["genuine_ipc"]["large_list"]
    new_controls = {
        "fixed_size_list": pa.list_(pa.int32(), 2),
        "list_view": pa.list_view(pa.int32()),
    }
    for name, kind in new_controls.items():
        inputs[name] = SCHEMA["stream"](pa, pa.schema([
            pa.field("unsupported", pa.struct([pa.field("values", kind)]))]))
    control_pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert {name: fingerprint(inputs[name]) for name in new_controls} == control_pins["genuine_ipc"]
    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']

    for label in (*emit, "populated"):
        source = inputs[label]
        fields, end = raw_schema(source)
        reader = pa.ipc.open_stream(source)
        assert fields == [SCHEMA["pyarrow_field"](pa, field) for field in reader.schema]
        plan, nodes, buffers = plan_term(fields)
        if label == "populated":
            record = BATCH["read_record"](source, end)
            assert len(nodes) == len(record.nodes) and len(buffers) == len(record.buffers)
            BATCH["inspect"](pa, next(iter(reader)), record)
            code.append(f'  let _ ← check (← load folder "{label}") '
                        f'{{ depth := 4, ipc.fields := {len(nodes)} }} {end} {plan}')
        else:
            code.append(f'  emit folder "{label}" {end} {plan}')
        print(f"{label}: {len(nodes)} preorder nodes and {len(buffers)} buffers", flush=True)

    for label, expected_tag in (("large_list", 21), ("fixed_size_list", 16), ("list_view", 25)):
        data, _ = SCHEMA["metadata"](inputs[label])
        position = SCHEMA["descendant"](inputs[label])
        assert SCHEMA["read_scalar"](data, position, 2, "B") == expected_tag
        code.append(f'  refuse (.schema (.field {position} (.unsupported (.fieldType {expected_tag})))) '
                    f'(Batch.Placement.read {{}} (← load folder "{label}"))')

    for label in ("list_arity_zero", "list_arity_two", "child_slot_offset"):
        source, error = edits[label]
        assert fingerprint(source) == schema_pins["labeled_edits"][label]
        inputs[label] = source
        code.append(f'  refuse (.schema ({error})) (Batch.Placement.read {{}} (← load folder "{label}"))')

    original, _ = SCHEMA["metadata"](inputs["populated"])
    positions = list(SCHEMA["local_checks"](
        SCHEMA["original_fields"](original, *SCHEMA["root_vector"](original))))
    first_at_depth = next(pos for level, pos, _ in positions if level == 4)
    code.extend([
        f'  refuse (.schema (.depth {first_at_depth})) '
        '(Batch.Placement.read { depth := 3 } (← load folder "populated"))',
        f'  refuse (.schema (.fields {positions[-1][1]})) '
        '(Batch.Placement.read { ipc.fields := 10 } (← load folder "populated"))',
        '  refuse (.arity 0 .list 0) (ofSchema 2 ⟨[.node none true .list []]⟩)',
        '  let child := Field.node none false .int32 []',
        '  refuse (.arity 0 .list 2) (ofSchema 2 ⟨[.node none true .list [child, child]]⟩)',
    ])

    with tempfile.TemporaryDirectory() as directory:
        folder = Path(directory)
        for label, wire in inputs.items():
            (folder / f"{label}.arrow").write_bytes(wire)
        driver = folder / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)
        for label in emit:
            wire = (folder / f"{label}-lean.arrow").read_bytes()
            assert fingerprint(wire) == emitted_pins["lean_ipc"][label]
            fields, end = raw_schema(wire)
            assert fields == raw_schema(inputs[label])[0]
            assert wire[end:] == WRITER["STREAM"]["EOS"]
            reader = pa.ipc.open_stream(wire)
            assert fields == [SCHEMA["pyarrow_field"](pa, field) for field in reader.schema]
            assert list(reader) == []
    print("Verified three native Lean schema outputs and ten typed refusals")


if __name__ == "__main__":
    main()
