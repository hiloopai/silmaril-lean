#!/usr/bin/env python3
"""Check the literal Hive inventory and genuine native paired Parquet output."""

import sys
from pathlib import Path

import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq


DEFAULT_MARKER = "__HIVE_DEFAULT_PARTITION__"
CUSTOM_MARKER = "null/=%"
DATE = ("day", pa.date32())
TEXT = ("label", pa.string())
PHYSICAL = [("n", pa.int32()), ("blob", pa.binary())]
EXPECTED = [
    (19782, "café/blue", [[(-7, b"\xff\x00"), (None, b"")], [(11, None)]]),
    (None, "", [[(0, b"x"), (None, None)]]),
    (-719528, None, [[(9, b"y")]]),
]
PROFILES = {
    "date-first": (DEFAULT_MARKER, [DATE, TEXT], [
        "day=2024-02-29/label=caf%C3%A9%2Fblue/part-0.parquet",
        f"day={DEFAULT_MARKER}/label=/part-0.parquet",
        f"day=0000-01-01/label={DEFAULT_MARKER}/part-0.parquet",
    ]),
    "text-first": (CUSTOM_MARKER, [TEXT, DATE], [
        "label=caf%C3%A9%2Fblue/day=2024-02-29/part-0.parquet",
        "label=/day=null%2F%3D%25/part-0.parquet",
        "label=null%2F%3D%25/day=0000-01-01/part-0.parquet",
    ]),
}


def wire_cell(value):
    if value is None:
        return "null"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        value = value.encode("utf-8")
    return "b:" + ",".join(map(str, value))


def native_batches(path):
    lines = iter(path.read_text().splitlines())
    return [[next(lines).split("\t") for _ in range(int(size))] for size in lines]


def check_profile(root, marker, virtual, declared):
    assert (root / "inventory.txt").read_text().splitlines() == declared
    assert sorted(path.relative_to(root).as_posix() for path in root.rglob("*.parquet")) == sorted(declared)
    paths = [str(root / path) for path in declared]
    partitioning = ds.HivePartitioning(pa.schema(virtual), null_fallback=marker, segment_encoding="uri")
    dataset = ds.dataset(paths, format="parquet", partitioning=partitioning, partition_base_dir=str(root))
    assert dataset.schema.equals(pa.schema(PHYSICAL + virtual))
    fragments = list(dataset.get_fragments())
    assert [fragment.path for fragment in fragments] == paths
    batches = []
    for path, fragment, (day, label, groups) in zip(paths, fragments, EXPECTED, strict=True):
        with pq.ParquetFile(path) as file:
            assert file.schema_arrow.equals(pa.schema(PHYSICAL))
            assert file.num_row_groups == len(groups)
            for ordinal, group in enumerate(groups):
                physical = file.read_row_group(ordinal, use_threads=False)
                assert list(zip(physical["n"].to_pylist(), physical["blob"].to_pylist(), strict=True)) == group
        for ordinal, (part, group) in enumerate(zip(fragment.split_by_row_group(), groups, strict=True)):
            assert [info.id for info in part.row_groups] == [ordinal]
            table = part.to_table(schema=dataset.schema, use_threads=False)
            assert table["day"].cast(pa.int32()).to_pylist() == [day] * len(group)
            assert table["label"].to_pylist() == [label] * len(group)
            values = {"day": day, "label": label}
            batches.append([list(map(wire_cell, (number, payload, *(values[name] for name, _ in virtual))))
                            for number, payload in group])
    assert batches == native_batches(root / "batches.tsv")
    return len(batches)


def main():
    assert pa.__version__ == "26.0.1"
    root = Path(sys.argv[1]).resolve()
    groups = sum(check_profile(root / name, *profile) for name, profile in PROFILES.items())
    print(f"PyArrow matched both partition orders, six native Parquet files and {groups} row groups.")


if __name__ == "__main__":
    main()
