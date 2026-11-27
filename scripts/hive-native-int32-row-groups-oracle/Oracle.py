"""Read every group of the actual Lean-emitted Hive files with PyArrow."""
from pathlib import Path
import sys

import numpy as np
import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq


EXPECTED = [
    (3, [[10, 11], [12]]),
    (1, [[1, None], [5, 6], [9]]),
    (None, [[4, None], [7]]),
    (2, [[8]]),
]


def check(root, marker, encoded_marker, events):
    expected_paths = [f"key={encoded_marker if key is None else key}/part-0.parquet"
                      for key, _ in EXPECTED]
    paths = []
    observed_batches = []
    manifest = (root / "manifest.tsv").read_text(encoding="utf-8").splitlines()
    files = zip(manifest, expected_paths, EXPECTED, strict=True)
    for occurrence, (line, expected_path, (key, groups)) in enumerate(files):
        path, total, vector = line.split("\t")
        assert path == expected_path
        counts = [len(group) for group in groups]
        assert [int(count) for count in vector.split(",")] == counts
        assert int(total) == sum(counts)
        paths.append(str(root / path))
        reader = pq.ParquetFile(root / path)
        assert reader.schema_arrow == pa.schema([pa.field("payload", pa.int32(), nullable=True)])
        assert reader.metadata.num_rows == int(total)
        assert reader.num_row_groups == len(groups)
        for index, slots in enumerate(groups):
            group = reader.metadata.row_group(index)
            assert group.num_rows == len(slots)
            assert group.column(0).compression == "UNCOMPRESSED"
            actual = reader.read_row_group(index)["payload"].to_pylist()
            assert actual == slots
            observed_batches.append((occurrence, path, index, group.num_rows, key, actual))
    assert sorted(path.relative_to(root).as_posix() for path in root.rglob("*.parquet")) == sorted(expected_paths)

    profile = ds.HivePartitioning(pa.schema([("key", pa.int32())]), null_fallback=marker)
    view = ds.dataset(paths, format="parquet", partitioning=profile, partition_base_dir=str(root))
    rows = [(value, key) for key, groups in EXPECTED for group in groups for value in group]
    full = view.to_table(columns=["payload", "key"], use_threads=False)
    assert list(zip(full["payload"].to_pylist(), full["key"].to_pylist(), strict=True)) == rows
    key = ds.field("key")
    predicate = (key == 3) | key.is_null()
    fragments = [fragment.path for fragment in view.get_fragments(filter=predicate)]
    assert fragments == [paths[0], paths[2]]
    selected = view.to_table(filter=predicate, columns=["payload", "key"], use_threads=False)
    expected = [(value, key) for value, key in rows if key in (3, None)]
    assert list(zip(selected["payload"].to_pylist(), selected["key"].to_pylist(), strict=True)) == expected
    rendered = ["\t".join("null" if value is None else str(value) for value in row) for row in expected]
    assert (root / "selected.tsv").read_text(encoding="utf-8").splitlines() == rendered
    if events:
        def cell(value):
            return "null" if value is None else str(value)

        selected_paths = set(fragments)
        lines = []
        for occurrence, path, group_index, count, key, slots in observed_batches:
            if str(root / path) in selected_paths:
                pairs = ",".join(f"{cell(slot)}:{cell(key)}" for slot in slots)
                lines.append(f"{occurrence}\t{path}\t{group_index}\t{count}\t{pairs}")
        assert (root / "events.tsv").read_text(encoding="utf-8").splitlines() == lines + ["eos"]


def main():
    assert sys.version_info[:3] == (3, 14, 7)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert np.__version__ == "2.5.5"
    root = Path(sys.argv[1]).resolve()
    default = "__HIVE_DEFAULT_PARTITION__"
    assert sys.argv[2:] in ([], ["--events"])
    events = sys.argv[2:] == ["--events"]
    check(root / "default", default, default, events)
    check(root / "custom", "null/=", "null%2F%3D", events)
    print("PyArrow matched eight files, sixteen groups, twenty-four ordered rows, and both pruned traces.")
    if events:
        print("PyArrow matched eight ordered tagged batches, their exact rows, and both EOS boundaries.")


if __name__ == "__main__":
    main()
