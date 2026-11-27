"""Check the actual Lean-emitted Hive manifest and Parquet rows."""
from pathlib import Path
import sys

import numpy as np
import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq

DEFAULT_MARKER = "__HIVE_DEFAULT_PARTITION__"
CUSTOM_MARKER = "null/="
KEY_SCHEMA = pa.schema([("key", pa.int32())])


def check_full(root, marker, encoded_marker):
    declared = (root / "manifest.txt").read_text(encoding="utf-8").splitlines()
    assert declared == [
        "key=3/part-0.parquet",
        "key=1/part-0.parquet",
        f"key={encoded_marker}/part-0.parquet",
        "key=2/part-0.parquet",
    ]
    assert sorted(path.relative_to(root).as_posix() for path in root.rglob("*.parquet")) == sorted(declared)
    payloads = [[10, 11, 10], [None, 5], [4, None], [8]]
    for path, expected in zip(declared, payloads, strict=True):
        file = pq.ParquetFile(root / path)
        assert file.schema_arrow == pa.schema([pa.field("payload", pa.int32(), nullable=True)])
        assert file.num_row_groups == 1
        assert file.metadata.row_group(0).num_rows == len(expected)
        assert file.metadata.row_group(0).column(0).compression == "UNCOMPRESSED"
        assert file.read()["payload"].to_pylist() == expected

    profile = ds.HivePartitioning(KEY_SCHEMA, null_fallback=marker)
    view = ds.dataset([str(root / path) for path in declared], format="parquet",
                      partitioning=profile, partition_base_dir=str(root))
    table = view.to_table(columns=["payload", "key"], use_threads=False)
    assert table["payload"].to_pylist() == [value for bucket in payloads for value in bucket]
    assert table["key"].to_pylist() == [3, 3, 3, 1, 1, None, None, 2]
    return view


def check_pruning(root, marker, encoded_marker):
    view = check_full(root, marker, encoded_marker)
    key = ds.field("key")
    predicate = (key == 3) | key.is_null()
    assert [Path(fragment.path).relative_to(root).as_posix()
            for fragment in view.get_fragments(filter=predicate)] == [
        "key=3/part-0.parquet", f"key={encoded_marker}/part-0.parquet"
    ]
    rows = view.to_table(filter=predicate, columns=["payload", "key"], use_threads=False).to_pylist()
    expected = [(10, 3), (11, 3), (10, 3), (4, None), (None, None)]
    assert [(row["payload"], row["key"]) for row in rows] == expected
    selected = (root / "selected.tsv").read_text(encoding="utf-8").splitlines()
    encoded = ["\t".join("null" if value is None else str(value) for value in row) for row in expected]
    assert selected == encoded
    assert view.to_table(filter=key == 99, use_threads=False).num_rows == 0


def main():
    assert sys.version_info[:3] == (3, 14, 7)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert np.__version__ == "2.5.5"
    root = Path(sys.argv[1])
    if sys.argv[2:] == ["--pruning"]:
        check_pruning(root / "default", DEFAULT_MARKER, DEFAULT_MARKER)
        check_pruning(root / "custom", CUSTOM_MARKER, "null%2F%3D")
        print("PyArrow matched selected fragments and five stable nullable rows in both marker profiles.")
    else:
        assert not sys.argv[2:]
        check_full(root, DEFAULT_MARKER, DEFAULT_MARKER)
        print("PyArrow matched four native files and eight ordered nullable rows using the explicit manifest.")


if __name__ == "__main__":
    main()
