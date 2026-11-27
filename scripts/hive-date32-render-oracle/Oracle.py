#!/usr/bin/env python3
"""Read Lean-rendered paths and native Parquet with PyArrow Hive DATE."""

import sys
from pathlib import Path

import pyarrow as pa
import pyarrow.dataset as ds


CASES = {
    "default": ("day", "__HIVE_DEFAULT_PARTITION__", [
        ("day=2024-02-29", 19782, [[1, None], [5]]),
        ("day=__HIVE_DEFAULT_PARTITION__", None, [[2, None]]),
        ("day=0000-01-01", -719528, [[3]]),
        ("day=9999-12-31", 2932896, [[4]]),
    ]),
    "escaped": ("d/é=%", "null/=%", [
        ("d%2F%C3%A9%3D%25=1969-12-31", -1, [[None]]),
        ("d%2F%C3%A9%3D%25=null%2F%3D%25", None, [[8]]),
        ("d%2F%C3%A9%3D%25=1970-01-01", 0, [[9]]),
    ]),
    "date-marker": ("day", "2000-02-29", [
        ("day=2000-02-29", None, [[10]]),
        ("day=2000-03-01", 11017, [[11]]),
    ]),
}


def compare(root, key, marker, entries):
    partitioning = ds.HivePartitioning(pa.schema([(key, pa.date32())]),
                                       null_fallback=marker, segment_encoding="uri")
    paths = [f"{directory}/part-0.parquet" for directory, _, _ in entries]
    assert (root / "inventory.txt").read_text().splitlines() == paths
    assert sorted(p.relative_to(root).as_posix() for p in root.rglob("*.parquet")) == sorted(paths)
    inventory = [str(root / path) for path in paths]
    dataset = ds.dataset(inventory, format="parquet", partitioning=partitioning, partition_base_dir=str(root))
    assert dataset.schema.equals(pa.schema([("payload", pa.int32()), (key, pa.date32())]))
    fragments = list(dataset.get_fragments())
    assert [fragment.path for fragment in fragments] == inventory

    groups_read = 0
    for fragment, (directory, epoch_day, payloads) in zip(fragments, entries, strict=True):
        groups = fragment.split_by_row_group()
        assert len(groups) == len(payloads)
        for ordinal, (group, payload) in enumerate(zip(groups, payloads, strict=True)):
            assert [info.id for info in group.row_groups] == [ordinal]
            table = group.to_table(schema=dataset.schema, columns=["payload", key])
            assert table["payload"].to_pylist() == payload
            assert table[key].cast(pa.int32()).to_pylist() == [epoch_day] * len(payload)
            groups_read += 1
        if key == "day":
            field = ds.field(key)
            predicate = field.is_null() if epoch_day is None else field == pa.scalar(epoch_day, pa.date32())
            assert partitioning.format(predicate) == (directory, "")
    return groups_read


def marker_collision():
    partitioning = ds.HivePartitioning(pa.schema([("day", pa.date32())]),
                                       null_fallback="2000-02-29", segment_encoding="uri")
    day = ds.field("day")
    as_value = day == pa.scalar(11016, pa.date32())
    path, _ = partitioning.format(as_value)
    assert path == "day=2000-02-29"
    assert partitioning.format(day.is_null()) == (path, "")
    assert partitioning.parse(path + "/").equals(day.is_null())


def main():
    assert pa.__version__ == "26.0.1"
    root = Path(sys.argv[1]).resolve()
    groups = sum(compare(root / name, *case) for name, case in CASES.items())
    marker_collision()
    print(f"PyArrow matched nine literal Parquet paths, {groups} groups, and six safe directory spellings.")
    print("PyArrow formats a present marker day and NULL identically; the matching path parses as NULL.")


if __name__ == "__main__":
    main()
