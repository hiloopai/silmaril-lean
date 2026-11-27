#!/usr/bin/env python3
"""Check native paired Parquet, selected groups, named import and BinaryView IPC."""

import argparse
from hashlib import sha256
from pathlib import Path

import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq


DEFAULT_MARKER = "__HIVE_DEFAULT_PARTITION__"
CUSTOM_MARKER = "null/=%"
DATE = ("day", pa.date32())
TEXT = ("label", pa.string())
PHYSICAL = [("n", pa.int32()), ("blob", pa.binary())]
IPC_SHA256 = {
    "selected": "e04c619b69d52e7984afd696e14a8798f30f02188249091020d6c842b35d65c4",
    "none-kept": "8370b07d9ed8a8cab381d7e3957533b8e41f32a515f4b0113ccb803c11ab7e78",
    "empty-group": "4ab98ff8d0e2fd0bbb82a046a5d9fb29beea225e16b9dfaa6c4edf9a201e68b9",
}
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


def check_binary_view(path, expected, case):
    wire = path.read_bytes()
    assert sha256(wire).hexdigest() == IPC_SHA256[case]
    source = pa.BufferReader(wire)
    with pa.ipc.open_stream(source) as reader:
        assert reader.schema.equals(pa.schema([pa.field("blob", pa.binary_view(), nullable=True)]))
        assert [batch.column(0).to_pylist() for batch in reader] == expected
        assert source.tell() == len(wire)
    assert wire.endswith(b"\xff\xff\xff\xff\x00\x00\x00\x00")


def check_ipc(root, dataset, paths, declared):
    retained = list(dataset.get_fragments(filter=ds.field("day").is_valid()))
    assert [fragment.path for fragment in retained] == [paths[0], paths[2]]
    expected = []
    # The supplied manifest repeats the first occurrence at the end.
    for fragment in retained + retained[:1]:
        with pq.ParquetFile(fragment.path) as file:
            for ordinal in range(file.num_row_groups):
                group = file.read_row_group(ordinal, columns=["blob"], use_threads=False)
                expected.append(group["blob"].to_pylist())
    check_binary_view(root / "selected.arrow", expected, "selected")
    check_binary_view(root / "none-kept.arrow", [], "none-kept")

    empty_root = root.with_name(root.name + "-empty")
    with pq.ParquetFile(empty_root / declared[0]) as file:
        assert file.num_row_groups == 1 and file.metadata.row_group(0).num_rows == 0
        slots = file.read_row_group(0, columns=["blob"], use_threads=False)["blob"].to_pylist()
    check_binary_view(empty_root / "selected.arrow", [slots], "empty-group")


def check_profile(root, marker, virtual, declared, opens=None, named=False, ipc=False):
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
            for i in range(len(PHYSICAL)):
                column = file.schema.column(i)
                assert column.max_definition_level == 1
                assert column.max_repetition_level == 0
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
    if ipc:
        check_ipc(root, dataset, paths, declared)
    if opens is not None:
        keep = ds.field("day") == pa.scalar(19782, pa.date32())
        chosen = list(dataset.get_fragments(filter=keep))
        retained = [Path(fragment.path).relative_to(root).as_posix() for fragment in chosen]
        assert retained == declared[:1]
        assert opens[root.name + "-strict"] == declared
        assert opens[root.name + "-pruned"] == retained
        positions = [3, 0, 2, 3]
        expected = []
        for fragment in chosen:
            for group in fragment.split_by_row_group():
                table = group.to_table(schema=dataset.schema, use_threads=False)
                columns = [table[name].cast(pa.int32()).to_pylist() if name == "day" else table[name].to_pylist()
                           for name in dataset.schema.names]
                expected.append([list(map(wire_cell, (row[i] for i in positions)))
                                 for row in zip(*columns, strict=True)])
        assert expected == native_batches(root / "pruned.tsv")
        if named:
            header, *rows = (root / "db.tsv").read_text().splitlines()
            assert header.split("\t") == [dataset.schema.names[i] for i in positions]
            assert [row.split("\t") for row in rows] == [row for batch in expected for row in batch]
            assert int((root / "db-zero-count.txt").read_text()) == sum(map(len, expected))
    return len(batches)


def main():
    assert pa.__version__ == "26.0.1"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("resolver_log", type=Path, nargs="?")
    parser.add_argument("--named", action="store_true")
    parser.add_argument("--ipc", action="store_true")
    args = parser.parse_args()
    if args.named and args.resolver_log is None:
        parser.error("--named requires the resolver log")
    root = args.root.resolve()
    opens = None
    if args.resolver_log is not None:
        opens = {}
        for line in args.resolver_log.read_text().splitlines():
            if line.startswith("open\t"):
                _, run, literal = line.split("\t")
                opens.setdefault(run, []).append(literal)
        assert set(opens) == {name + mode for name in PROFILES for mode in ("-strict", "-pruned")}
    groups = sum(check_profile(root / name, *profile, opens=opens, named=args.named, ipc=args.ipc)
                 for name, profile in PROFILES.items())
    print(f"PyArrow matched both partition orders, six native Parquet files and {groups} row groups.")
    if opens is not None:
        print("PyArrow matched projected retained groups. Lean resolver traces show three strict and one pruned open per order.")
    if args.named:
        print("PyArrow selected groups matched the imported labels, ordered rows and zero-column cardinality.")
    if args.ipc:
        print("PyArrow matched BinaryView fields and octets, repeated groups, empty groups and exact EOS.")


if __name__ == "__main__":
    main()
