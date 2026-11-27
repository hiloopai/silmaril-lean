"""Replay exact-arity positional file paths and PyArrow's broader behavior."""
import csv
import hashlib
from pathlib import Path
import sys
import tempfile
from urllib.parse import quote_from_bytes, unquote_to_bytes

import numpy as np
import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq

assert sys.version_info[:3] == (3, 14, 7)
assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
assert np.__version__ == "2.5.5"

fixture = Path(sys.argv[1])
payload = fixture.read_bytes()
digest = hashlib.sha256(payload).hexdigest()
assert digest == "4417fe68ce84210af4979a2f7ef19d05764fc3ce3bf71f83b25b546658e76f48"
metadata = pq.read_metadata(fixture)
assert [metadata.row_group(i).num_rows for i in range(metadata.num_row_groups)] == [3, 0, 2]

schema = pa.schema([("region", pa.string()), ("year", pa.int32())])
uri = ds.DirectoryPartitioning(schema, segment_encoding="uri")
literal = ds.DirectoryPartitioning(schema, segment_encoding="none")
marker = "__HIVE_DEFAULT_PARTITION__"
alias = "%5f_HIVE_DEFAULT_PARTITION__"
escaped = "caf%C3%A9%2fblue/7/A%2Eparquet"
assigned = "region=west/7/B.parquet"
rejected = "z/8/C.parquet"


def keys(profile, path):
    return ds.get_partition_keys(profile.parse(path))


def write_import_controls(directory, labels, arrow_rows, row_count, row_budget):
    def tagged(value):
        if value is None:
            return "N"
        if isinstance(value, int):
            return "T" + str(value)
        return "T" + quote_from_bytes(value, safe="-._~")

    def write(filename, records):
        with (directory / filename).open("w", encoding="utf-8", newline="") as output:
            csv.writer(output).writerows(records)

    directory.mkdir(parents=True, exist_ok=True)
    body = [[tagged(value) for value in row] for row in arrow_rows]
    write("projected.csv", [labels, *body])
    write("zero.csv", [[""]] * (row_count + 1))
    write("wrong-header.csv", [["wrong", *labels[1:]], *body])
    bad_bytes = [*body[0][:4], "T%ff%00"]
    write("bad-bytes.csv", [labels, bad_bytes, *body[1:]])
    bad_int = [*body[0][:2], "T+7", *body[0][3:]]
    write("bad-int.csv", [labels, bad_int, *body[1:]])
    write("bad-zero.csv", [[""], ["unexpected"]])
    print("CPython wrote two valid CSV inputs and four independent refusal controls.")
    if row_budget:
        bad_last_cell = [*body[-1][:2], "T+7", *body[-1][3:]]
        write("late-cell.csv", [labels, *body[:-1], bad_last_cell])
        write("late-wire.csv", [labels, *body[:-1]])
        with (directory / "late-wire.csv").open("ab") as output:
            output.write(b'"unterminated')
        print("CPython wrote two late corruption controls for the row budget.")


for profile, marker_alias in ((uri, marker), (literal, alias)):
    assert keys(profile, "west/") == {"region": "west"}
    assert keys(profile, "/") == {}
    assert keys(profile, "west/7/ignored/") == {"region": "west", "year": 7}
    assert keys(profile, f"{marker}/7/") == {"region": marker, "year": 7}
    assert keys(profile, f"{alias}/7/") == {"region": marker_alias, "year": 7}
    assert keys(profile, "%GG/7/") == {"region": "%GG", "year": 7}
    assert profile.format(ds.field("region").is_null()) == ("", "")
    assert profile.format((ds.field("region") == "west") & ds.field("year").is_null()) == ("west", "")
    for rejected_path in ("west//7/", f"west/{marker}/"):
        try:
            keys(profile, rejected_path)
        except pa.ArrowInvalid:
            pass
        else:
            raise AssertionError(f"expected an Int32 cast error: {rejected_path!r}")
    try:
        profile.format(ds.field("region").is_null() & (ds.field("year") == 7))
    except pa.ArrowInvalid:
        pass
    else:
        raise AssertionError("formatter accepted a later key after a null position")

assert keys(ds.DirectoryPartitioning(pa.schema([("region", pa.string()), ("label", pa.string())])),
            "west//extra/") == {"region": "west", "label": ""}
assert keys(literal, "%FF/7/") == {"region": "%FF", "year": 7}
try:
    keys(uri, "%FF/7/")
except pa.ArrowInvalid:
    pass
else:
    raise AssertionError("URI reader accepted invalid decoded UTF-8")

with tempfile.TemporaryDirectory() as temp:
    root = Path(temp)
    for path in (escaped, assigned, rejected):
        target = root / path
        target.parent.mkdir(parents=True)
        target.write_bytes(payload)
    (root / "_metadata").write_bytes(b"")
    listing = [rejected, assigned, "_metadata", escaped, escaped]
    ordered = sorted((path for path in listing if path != "_metadata"), key=str.encode)
    for profile, region in ((uri, "café/blue"), (literal, "caf%C3%A9%2fblue")):
        retained = [path for path in ordered if keys(profile, path)["year"] == 7]
        assert retained == [escaped, escaped, assigned]
        dataset = ds.dataset(
            [str(root / path) for path in retained], format="parquet", partitioning=profile,
            partition_base_dir=str(root),
        )
        table = dataset.to_table(columns=["ordinal", "region", "year"], use_threads=False)
        assert table["ordinal"].to_pylist() == [-2147483648, 0, 17, 2147483647, -1] * 3
        assert table["region"].to_pylist() == [region] * 10 + ["region=west"] * 5
        assert table["year"].to_pylist() == [7] * 15
        print(f"Retained {retained!r} with regions {region!r}, {region!r}, 'region=west'")

print("PyArrow also accepts missing and extra segments, malformed percent text, and empty string slots.")
print("Positional null formatting omits a trailing null and rejects a later key after a null.")
print(f"CPython {sys.version.split()[0]}, PyArrow {pa.__version__}, NumPy {np.__version__}, fixture {digest}")

if len(sys.argv) > 2:
    rendered = Path(sys.argv[2]).read_text(encoding="utf-8").splitlines()
    assert rendered[:4] == [
        "caf%C3%A9%2Fblue%3D%255F%3Awest%5Cx/7",
        "café=blue%5F_west/7",
        "__HIVE_DEFAULT_PARTITION__/7",
        "",
    ]
    for directory, profile, expected in zip(
        rendered[:4],
        (uri, literal, uri, ds.DirectoryPartitioning(pa.schema([]))),
        ("café/blue=%5F:west\\x", "café=blue%5F_west", marker, None),
        strict=True,
    ):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            target = root / directory / "part.parquet"
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)
            dataset = ds.dataset([str(target)], format="parquet", partitioning=profile,
                                 partition_base_dir=str(root))
            columns = ["ordinal", "payload"] + (["region", "year"] if expected is not None else [])
            table = dataset.to_table(columns=columns, use_threads=False)
            assert table.column_names == columns
            assert table["ordinal"].to_pylist() == [-2147483648, 0, 17, 2147483647, -1]
            assert table["payload"].to_pylist() == [None, b"", b"\xff\x00", b"\x80", b"xy"]
            if expected is not None:
                assert table["region"].to_pylist() == [expected] * 5
                assert table["year"].to_pylist() == [7] * 5
            print(f"Lean directory {directory!r}: five exact physical rows, region {expected!r}")

    if len(rendered) > 4:
        assert rendered[4:] == ["apart/8", "zebra/7"]
        canonical = rendered[0] + "/part.parquet"
        lower_escape = rendered[0].replace("%2F", "%2f") + "/B%2Eparquet"
        pruned = rendered[4] + "/skip.parquet"
        last = rendered[5] + "/z.parquet"
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for path in (canonical, lower_escape, pruned, last):
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(payload)

            # The explicit sorted data listing matches Lean admission. The
            # bad lookup and selected corruption controls belong to Lean.
            ordered = sorted([last, canonical, pruned, lower_escape, canonical], key=str.encode)
            assert ordered == [pruned, canonical, canonical, lower_escape, last]
            dataset = ds.dataset([str(root / path) for path in ordered], format="parquet",
                                 partitioning=uri, partition_base_dir=str(root))
            predicate = ds.field("year") == 7
            columns = ["region", "ordinal", "year", "region", "payload"]
            projected = dataset.to_table(columns=columns, filter=predicate, use_threads=False)
            assert projected.column_names == columns
            ordinals = [-2147483648, 0, 17, 2147483647, -1]
            values = [None, b"", b"\xff\x00", b"\x80", b"xy"]
            assert list(zip(*(column.to_pylist() for column in projected.columns))) == [
                (region, ordinal, 7, region, value)
                for region in ["café/blue=%5F:west\\x"] * 3 + ["zebra"]
                for ordinal, value in zip(ordinals, values, strict=True)
            ]
            zero = dataset.to_table(columns=[], filter=predicate, use_threads=False)
            assert zero.num_columns == 0 and zero.num_rows == 20
            print("Ordered positional scan: five data occurrences, four retained, twenty projected rows.")

            if len(sys.argv) > 3:
                projected_file, zero_file = (Path(arg) for arg in sys.argv[3:5])
                with projected_file.open(encoding="utf-8", newline="") as source:
                    header, *records = csv.reader(source, strict=True)
                assert header == columns

                def typed_cell(field, index):
                    if field == "N":
                        return None
                    assert field.startswith("T"), (index, field)
                    text = field[1:]
                    if index in (1, 2):
                        value = int(text)
                        assert str(value) == text
                        return value
                    value = unquote_to_bytes(text)
                    assert quote_from_bytes(value, safe="-._~") == text
                    return value

                assert all(len(record) == len(columns) for record in records)
                csv_rows = [tuple(typed_cell(field, i) for i, field in enumerate(record))
                            for record in records]
                arrow_rows = [
                    (region.encode("utf-8"), ordinal, year, repeated.encode("utf-8"), value)
                    for region, ordinal, year, repeated, value in
                    zip(*(column.to_pylist() for column in projected.columns), strict=True)
                ]
                assert csv_rows == arrow_rows
                with zero_file.open(encoding="utf-8", newline="") as source:
                    assert list(csv.reader(source, strict=True)) == [[""]] * (zero.num_rows + 1)
                print("CPython CSV readback matches PyArrow rows, duplicate headers, and zero-width count.")
                if len(sys.argv) > 5:
                    write_import_controls(Path(sys.argv[5]), columns, arrow_rows, zero.num_rows,
                                          row_budget=sys.argv[6:] == ["--row-budget"])
