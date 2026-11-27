#!/usr/bin/env python3
"""Read Lean-rendered DATE/UTF-8 directories with independent PyArrow Hive parsing."""

import sys
from pathlib import Path

import pyarrow as pa
import pyarrow.dataset as ds


DEFAULT = "__HIVE_DEFAULT_PARTITION__"
DATE = ("day", pa.date32())
TEXT = ("label", pa.string())
DATE_FIRST = [DATE, TEXT]
TEXT_FIRST = [TEXT, DATE]
ESCAPED = [("l=/%", pa.string()), ("d/é=%", pa.date32())]
CASES = {
    "date-first": (DEFAULT, DATE_FIRST, [19782, "café/=blue%"],
                   "day=2024-02-29/label=caf%C3%A9%2F%3Dblue%25"),
    "text-first": (DEFAULT, TEXT_FIRST, ["café/=blue%", 19782],
                   "label=caf%C3%A9%2F%3Dblue%25/day=2024-02-29"),
    "empty": (DEFAULT, DATE_FIRST, [None, ""], f"day={DEFAULT}/label="),
    "null": (DEFAULT, TEXT_FIRST, [None, -719528], f"label={DEFAULT}/day=0000-01-01"),
    "escaped-marker-and-keys": ("null/=%", ESCAPED, [None, None],
                                "l%3D%2F%25=null%2F%3D%25/d%2F%C3%A9%3D%25=null%2F%3D%25"),
    "date-marker": ("2000-02-29", DATE_FIRST, [None, "plain"], "day=2000-02-29/label=plain"),
    "plain-date-first": (DEFAULT, DATE_FIRST, [-1, "plain"], "day=1969-12-31/label=plain"),
    "plain-text-first": (DEFAULT, TEXT_FIRST, ["plain", -1], "label=plain/day=1969-12-31"),
}


def hive(fields, marker):
    return ds.HivePartitioning(pa.schema(fields), null_fallback=marker, segment_encoding="uri")


def constraint(field, value):
    name, kind = field
    ref = ds.field(name)
    return ref.is_null() if value is None else ref == pa.scalar(value, kind)


def marker_collisions():
    date = hive(DATE_FIRST, "2000-02-29")
    label = constraint(TEXT, "plain")
    date_null = constraint(DATE, None) & label
    date_present = constraint(DATE, 11016) & label
    spelling, _ = date.format(date_present)
    assert date.format(date_null) == (spelling, "")
    assert date.parse(spelling + "/").equals(date_null)

    text = hive(TEXT_FIRST, DEFAULT)
    day = constraint(DATE, -1)
    text_null = constraint(TEXT, None) & day
    text_present = constraint(TEXT, DEFAULT) & day
    spelling, _ = text.format(text_present)
    assert text.format(text_null) == (spelling, "")
    assert text.parse(spelling + "/").equals(text_null)


def main():
    assert pa.__version__ == "26.0.1"
    rows = [line.split("\t") for line in Path(sys.argv[1]).read_text().splitlines()]
    assert [name for name, _ in rows] == list(CASES)
    for name, actual in rows:
        marker, fields, values, directory = CASES[name]
        assert actual == directory, (name, actual, directory)
        partitioning = hive(fields, marker)
        left, right = [constraint(field, value) for field, value in zip(fields, values, strict=True)]
        parsed = partitioning.parse(actual + "/")
        assert parsed.equals(left & right), (name, parsed)
        if name.startswith("plain-"):
            assert partitioning.format(left & right) == (actual, ""), name
    marker_collisions()
    print("PyArrow matched eight rendered directories, both key orders, and both marker ambiguities.")


if __name__ == "__main__":
    main()
