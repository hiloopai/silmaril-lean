#!/usr/bin/env python3
"""Compare typed Hive DATE/UTF-8 traces over pinned paired Parquet bytes."""

import hashlib
import sys
from pathlib import Path

import pyarrow as pa
import pyarrow.dataset as ds


FIRST = "label=caf%C3%A9%2fblue/%64ay=2024%2d02%2D29/A%2Eparquet"
PATHS = [
    FIRST,
    "day=__HIVE_DEFAULT_PARTITION__/label=/B.parquet",
    "day=0000-01-01/label=%5F%5FHIVE_DEFAULT_PARTITION__/C.parquet",
    FIRST,
]
CELLS = [(19782, "café/blue"), (None, ""), (-719528, None), (19782, "café/blue")]
PIN = "4417fe68ce84210af4979a2f7ef19d05764fc3ce3bf71f83b25b546658e76f48"


def wire_cell(value):
    if value is None:
        return "null"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        value = value.encode("utf-8")
    return "b:" + ",".join(map(str, value))


def lean_trace(path):
    lines = iter(path.read_text().splitlines())
    labels = next(lines).split("\t")
    batches = []
    for size in lines:
        batches.append([next(lines).split("\t") for _ in range(int(size))])
    return labels, batches


def arrow_trace(root, ordered_types):
    partitioning = ds.HivePartitioning(pa.schema(ordered_types),
                                       null_fallback="__HIVE_DEFAULT_PARTITION__", segment_encoding="uri")
    paths = [str(root / part) for part in PATHS]
    dataset = ds.dataset(paths, format="parquet", partitioning=partitioning, partition_base_dir=str(root))
    labels = dataset.schema.names
    assert labels == ["ordinal", "payload", *(name for name, _ in ordered_types)]
    assert dataset.schema.field("day").type == pa.date32()
    assert dataset.schema.field("label").type == pa.string()
    fragments = list(dataset.get_fragments())
    assert [fragment.path for fragment in fragments] == paths
    batches = []
    for fragment, (date, label) in zip(fragments, CELLS, strict=True):
        assert hashlib.sha256(Path(fragment.path).read_bytes()).hexdigest() == PIN
        groups = fragment.split_by_row_group()
        assert [group.row_groups[0].num_rows for group in groups] == [3, 0, 2]
        for group in groups:
            table = group.to_table(schema=dataset.schema, columns=labels, use_threads=False)
            columns = {key: table[key].to_pylist() for key in labels if key != "day"}
            columns["day"] = table["day"].cast(pa.int32()).to_pylist()
            assert columns["day"] == [date] * table.num_rows
            assert columns["label"] == [label] * table.num_rows
            batches.append([list(map(wire_cell, row))
                            for row in zip(*(columns[key] for key in labels), strict=True)])
    return labels, batches


def main():
    assert pa.__version__ == "26.0.1"
    root = Path(sys.argv[1]).resolve()
    assert (root / "inventory.txt").read_text().splitlines() == PATHS
    date = ("day", pa.date32())
    text = ("label", pa.string())
    ordered = arrow_trace(root, [date, text])
    reversed_keys = arrow_trace(root, [text, date])
    assert lean_trace(root / "date-first.tsv") == ordered
    assert lean_trace(root / "text-first.tsv") == reversed_keys
    indices = [3, 0, 2, 3]
    labels, batches = ordered
    assert lean_trace(root / "repeated.tsv") == (
        [labels[i] for i in indices], [[[row[i] for i in indices] for row in batch] for batch in batches])
    print("PyArrow matched both declared key orders and the repeated projection over four occurrences and 12 groups.")


if __name__ == "__main__":
    main()
