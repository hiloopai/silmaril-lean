"""Check the actual Lean-emitted Hive manifest and Parquet rows."""
from pathlib import Path
import sys

import numpy as np
import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq

assert sys.version_info[:3] == (3, 14, 7)
assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
assert np.__version__ == "2.5.5"

root = Path(sys.argv[1])
declared = (root / "manifest.txt").read_text(encoding="utf-8").splitlines()
assert declared == [
    "key=3/part-0.parquet",
    "key=1/part-0.parquet",
    "key=__HIVE_DEFAULT_PARTITION__/part-0.parquet",
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

profile = ds.HivePartitioning(pa.schema([("key", pa.int32())]))
view = ds.dataset([str(root / path) for path in declared], format="parquet",
                  partitioning=profile, partition_base_dir=str(root))
table = view.to_table(columns=["payload", "key"], use_threads=False)
assert table["payload"].to_pylist() == [value for bucket in payloads for value in bucket]
assert table["key"].to_pylist() == [3, 3, 3, 1, 1, None, None, 2]
print("PyArrow matched four native files and eight ordered nullable rows using the explicit manifest.")
