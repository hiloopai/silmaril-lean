"""Compare Lean's supplied Hive manifest with genuine PyArrow directory files."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.dataset as ds

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
P = runpy.run_path(str(HERE.parent / "parquet-timestamp-heterogeneous-events-oracle/check.py"))
PARTITION_FIELDS = [pa.field("region", pa.string()), pa.field("rank", pa.int32(), nullable=False)]
PARTITIONING = ds.partitioning(pa.schema(PARTITION_FIELDS), flavor="hive")
PHYSICAL = [3, 0, 1, 2, 1]
OUTPUT = [P["FIELDS"][i] for i in PHYSICAL] + PARTITION_FIELDS


def fixture_inputs():
    existing, _, offset = P["fixtures"]()
    names = ["z%41.parquet", "middle.parquet", "a.parquet"]
    expressions = [
        (ds.field("rank") == -17) & (ds.field("region") == "café/東京"),
        (ds.field("rank") == 9) & ds.field("region").is_null(),
        ds.field("rank") == 0,
    ]
    expected = [{"rank": -17, "region": "café/東京"}, {"rank": 9, "region": None}, {"rank": 0}]
    paths = []
    for name, expression, cells in zip(names, expressions, expected, strict=True):
        parent, leaf = PARTITIONING.format(expression)
        assert not leaf and ds.get_partition_keys(PARTITIONING.parse(parent + "/")) == cells
        paths.append(f"{parent}/{name}")
    groups = P["GROUPS"]
    clean = {
        paths[0]: P["produce"]("2.0", [groups[2], groups[0]]),
        paths[1]: existing["native_v1"],
        paths[2]: P["produce"]("2.0", [groups[1]]),
    }
    bad = dict(clean)
    bad[paths[1]] = existing["mutated_late_timestamp_dictionary_magic"]
    ordered = [*paths, paths[0]]
    assert ordered[:3] != sorted(paths)
    return clean, bad, ordered, offset


def stage(directory, files):
    for path, wire in files.items():
        target = directory / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(wire)
    dataset = ds.dataset(directory, format="parquet", partitioning=PARTITIONING)
    return {Path(fragment.path).relative_to(directory).as_posix(): ds.get_partition_keys(fragment.partition_expression)
            for fragment in dataset.get_fragments()}


def field_label(field):
    if pa.types.is_timestamp(field.type):
        label = f"{field.type.unit},{field.type.tz or ''}"
    elif pa.types.is_string(field.type):
        label = "utf8"
    else:
        assert pa.types.is_int32(field.type)
        label = "int32"
    return f"{field.name},{label},{str(field.nullable).lower()}"


def cell(value):
    if value is None:
        return "null"
    return "text:" + value if isinstance(value, str) else str(value)


def observe(root, order, partition_cells, positions, *, broken=None):
    fields = [OUTPUT[i] for i in positions]
    lines = ["schema|" + "|".join(map(field_label, fields))]
    for path in order:
        parquet = P["open_parquet"]((root / path).read_bytes())
        stop = 1 if path == broken else parquet.num_row_groups
        for group in range(stop):
            rows = parquet.metadata.row_group(group).num_rows
            columns = []
            for position, field in zip(positions, fields, strict=True):
                if position >= len(PHYSICAL):
                    values = [partition_cells[path].get(field.name)] * rows
                else:
                    native = parquet.read_row_group(group, columns=[field.name]).column(0)
                    values = (native.cast(pa.int64()) if pa.types.is_timestamp(field.type) else native).to_pylist()
                assert len(values) == rows
                columns.append(",".join(map(cell, values)))
            lines.append("|".join([str(rows), *columns]))
        if path == broken:
            try:
                parquet.read_row_group(1, columns=["utc_ns"])
            except OSError as error:
                assert "ZSTD" in str(error).upper()
            else:
                raise AssertionError("PyArrow admitted the selected late error")
            break
    return "\n".join(lines)


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    clean, bad, ordered, offset = fixture_inputs()
    hashes = {path: sha256(wire).hexdigest() for path, wire in clean.items()}
    hashes["late:" + ordered[1]] = sha256(bad[ordered[1]]).hexdigest()
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="hive-heterogeneous-parquet-events-") as folder:
        out = Path(folder)
        good_root, bad_root = out / "native", out / "late"
        good_cells = stage(good_root, clean)
        bad_cells = stage(bad_root, bad)
        assert good_cells == bad_cells and set(good_cells) == set(ordered)
        assert good_cells[ordered[0]] == {"region": "café/東京", "rank": -17}
        assert good_cells[ordered[1]] == {"region": None, "rank": 9}
        assert good_cells[ordered[2]] == {"rank": 0}
        (out / "manifest.txt").write_text("\n".join(ordered), encoding="utf-8")
        full = list(range(len(OUTPUT)))
        observations = {
            "wide": observe(good_root, ordered, good_cells, full),
            "reordered": observe(good_root, ordered, good_cells, [5, 3, 6, 0, 5]),
            "zero_width": observe(good_root, ordered, good_cells, []),
            "virtual_only": observe(good_root, ordered, good_cells, [5, 6]),
            "late": observe(bad_root, ordered, bad_cells, full, broken=ordered[1]),
            "late_projected": observe(bad_root, ordered, bad_cells, [5, 6, 2], broken=ordered[1]),
            "late_narrow": observe(bad_root, ordered, bad_cells, [0, 1, 2, 4, 5, 6]),
        }
        for name, value in observations.items():
            (out / f"{name}.txt").write_text(value, encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Compare.lean"), str(out), str(offset)],
                       cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
