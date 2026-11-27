"""Check native Lean IPC against independently read ordered Hive partition paths and pages."""

from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
HIVE = runpy.run_path(str(HERE.parent / "hive-heterogeneous-parquet-events-oracle/check.py"))
IPC = runpy.run_path(str(HERE.parent / "parquet-timestamp-heterogeneous-ipc-oracle/check.py"))
OUTPUT = HIVE["OUTPUT"]
PHYSICAL = HIVE["PHYSICAL"]
OPEN_PARQUET = HIVE["P"]["open_parquet"]


def fixture_inputs():
    clean, corrupted, order, offset = HIVE["fixture_inputs"]()
    assembly = "rank=22/region=%E9%9B%AA/explicit-empty-group.parquet"
    framed, _ = IPC["fixture_inputs"]()
    all_files = {**clean, assembly: framed["assembled_framed_zero"]}
    return all_files, corrupted, order, order[:2] + [assembly] + order[2:], offset


def check_ipc(path, root, partition_cells, order, positions):
    fields = [OUTPUT[i] for i in positions]
    schema, batches = IPC["read_ipc"](path.read_bytes())
    assert list(schema) == fields, path.name
    expected_rows = []
    expected_cells = []
    for relative in order:
        pq = OPEN_PARQUET((root / relative).read_bytes())
        for group in range(pq.num_row_groups):
            rows = pq.metadata.row_group(group).num_rows
            expected_rows.append(rows)
            columns = []
            for position in positions:
                field = OUTPUT[position]
                if position >= len(PHYSICAL):
                    values = [partition_cells[relative].get(field.name)] * rows
                else:
                    column = pq.read_row_group(group, columns=[field.name]).column(0)
                    values = (column.cast(pa.int64()) if pa.types.is_timestamp(field.type) else column).to_pylist()
                assert len(values) == rows
                columns.append(values)
            expected_cells.append(columns)
    assert [batch.num_rows for batch in batches] == expected_rows, path.name
    for batch, expected in zip(batches, expected_cells, strict=True):
        for position, (field, values) in enumerate(zip(fields, expected, strict=True)):
            column = batch.column(position)
            assert (column.cast(pa.int64()) if pa.types.is_timestamp(field.type)
                    else column).to_pylist() == values, (path.name, position, field.name)
    return expected_rows


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, bad, native, extended, offset = fixture_inputs()
    hashes = {path: sha256(wire).hexdigest() for path, wire in files.items()}
    hashes["late:" + native[1]] = sha256(bad[native[1]]).hexdigest()
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="hive-heterogeneous-ipc-") as folder:
        out = Path(folder)
        root = out / "native"
        partition_cells = HIVE["stage"](root, files)
        damaged = HIVE["stage"](out / "late", bad)
        assert {path: partition_cells[path] for path in damaged} == damaged
        assert partition_cells[native[0]] == {"region": "café/東京", "rank": -17}
        assert partition_cells[native[1]] == {"region": None, "rank": 9}
        assert partition_cells[native[2]] == {"rank": 0}
        assert partition_cells[extended[2]] == {"region": "雪", "rank": 22}
        HIVE["observe"](out / "late", native, damaged, list(range(len(OUTPUT))), broken=native[1])
        (out / "native.txt").write_text("\n".join(native), encoding="utf-8")
        (out / "assembly.txt").write_text("\n".join(extended), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                        str(HERE / "Emit.lean"), str(out), str(offset)], cwd=ROOT, check=True)
        full = list(range(len(OUTPUT)))
        counts = {}
        for name, order, positions in [
            ("native", native, full),
            ("reordered", native, [5, 3, 6, 0, 5]),
            ("with_empty_group", extended, full),
            ("zero_width", extended, []),
            ("empty_manifest", [], full),
            ("empty_manifest_projected", [], []),
        ]:
            counts[name] = check_ipc(out / (name + ".arrow"), root, partition_cells, order, positions)
            print(f"{name}: batch rows {counts[name]}")
        assert counts["reordered"] == counts["native"]
        assert counts["zero_width"] == counts["with_empty_group"] and counts["zero_width"].count(0) == 1
    print("PyArrow verified six native IPC streams through exact EOS")


if __name__ == "__main__":
    main()
