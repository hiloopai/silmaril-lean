#!/usr/bin/env python3
"""Compare native Hive DATE traces with explicit-inventory PyArrow reads."""

import sys
from pathlib import Path

import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq


DEFAULT = "__HIVE_DEFAULT_PARTITION__"
PARTITIONS = pa.schema([("day", pa.date32())])
WIRE_SCHEMA = pa.schema([("payload", pa.int32()), ("day", pa.date32())])

LEAP = ("%64ay=2024%2D02%2d29", 19782, [[1, None], [2]])
CASES = {
    "default": (DEFAULT, [
        LEAP,
        ("day=1969-12-31", -1, [[3]]),
        ("day=9999-12-31", 2932896, [[4]]),
        ("day=__HIVE_DEFAULT_PARTITION__", None, [[None]]),
        ("day=%5F%5FHIVE_DEFAULT_PARTITION__", None, [[5]]),
        ("day=1970-01-01", 0, [[6]]),
        LEAP,
        ("day=0000-01-01", -719528, [[7]]),
    ]),
    "custom": ("null/=", [
        ("day=null%2F%3D", None, [[None, 8]]),
        ("day=2000%2D02%2d29", 11016, [[9]]),
    ]),
    "date-marker": ("2000-02-29", [
        ("day=2000-02-29", None, [[None]]),
        ("day=2000%2D02%2d29", None, [[10]]),
        ("day=2000-03-01", 11017, [[11]]),
    ]),
}


def partitioning(marker):
    return ds.HivePartitioning(PARTITIONS, null_fallback=marker, segment_encoding="uri")


def read_trace(path):
    def cell(text):
        return None if text == "null" else int(text)

    result = []
    for line in path.read_text().splitlines():
        index, literal, ordinal, count, *rows = line.split("\t")
        values = [tuple(map(cell, row.split(","))) for row in rows]
        result.append((int(index), literal, int(ordinal), int(count), values))
    return result


def compare(root, marker, entries):
    paths = [f"{directory}/part-0.parquet" for directory, _, _ in entries]
    assert (root / "inventory.txt").read_text().splitlines() == paths
    inventory = [str(root / path) for path in paths]
    dataset = ds.dataset(inventory, format="parquet", partitioning=partitioning(marker),
                         partition_base_dir=str(root))
    assert dataset.schema.equals(WIRE_SCHEMA)
    fragments = list(dataset.get_fragments())
    assert [fragment.path for fragment in fragments] == inventory
    predicate = ds.field("day").is_null() | (ds.field("day") <= pa.scalar(20000, pa.date32()))
    retained_paths = [fragment.path for fragment in dataset.get_fragments(filter=predicate)]
    assert retained_paths == [path for path, (_, date, _) in zip(inventory, entries, strict=True)
                              if date is None or date <= 20000]
    retained = set(retained_paths)
    full, selected = [], []
    for index, (literal, fragment, (_, date, payload_groups)) in enumerate(zip(paths, fragments, entries, strict=True)):
        footer = pq.read_metadata(fragment.path)
        sizes = [len(group) for group in payload_groups]
        assert [footer.row_group(i).num_rows for i in range(footer.num_row_groups)] == sizes
        groups = fragment.split_by_row_group()
        assert len(groups) == len(payload_groups)
        for ordinal, (group, payload, size) in enumerate(zip(groups, payload_groups, sizes, strict=True)):
            assert [info.id for info in group.row_groups] == [ordinal]
            table = group.to_table(schema=dataset.schema, columns=["payload", "day"])
            rows = list(zip(table["payload"].to_pylist(), table["day"].cast(pa.int32()).to_pylist(), strict=True))
            assert rows == [(value, date) for value in payload]
            batch = (index, literal, ordinal, size, rows)
            full.append(batch)
            if fragment.path in retained:
                selected.append(batch)
    assert read_trace(root / "all.tsv") == full
    assert read_trace(root / "selected.tsv") == selected
    return len(full), len(selected)


def path_controls():
    hive = partitioning(DEFAULT)
    for path in [
        "%64ay=2024%2D02%2d30/", "day=1900-02-29/", "day=2024-2-9/",
        "day=2024-02-29%2f/", "%FF=2024-02-29/", "day=%FF/",
    ]:
        try:
            hive.parse(path)
        except pa.ArrowInvalid:
            pass
        else:
            raise AssertionError(f"PyArrow admitted {path!r}")

    # Divergences from Lean's strict key admission.
    for path in ["%6Gay=2024-02-29/", "d%61x=2024-02-29/"]:
        assert hive.parse(path).equals(ds.scalar(True)), path
    repeated = hive.parse("day=2024-02-29/%64ay=2024-03-01/")
    assert repeated.equals((ds.field("day") == pa.scalar(19782, pa.date32())) &
                           (ds.field("day") == pa.scalar(19783, pa.date32())))


def main():
    assert pa.__version__ == "26.0.1"
    root = Path(sys.argv[1]).resolve()
    counts = [compare(root / name, marker, entries) for name, (marker, entries) in CASES.items()]
    path_controls()
    print(f"PyArrow matched {sum(full for full, _ in counts)} full and "
          f"{sum(selected for _, selected in counts)} selected tagged groups across three marker policies.")
    print("PyArrow confirmed six malformed-path refusals and three strict-key policy differences.")


if __name__ == "__main__":
    main()
