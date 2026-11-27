"""Produce pinned CPython CSV controls for the bounded typed reader."""
import csv
from pathlib import Path
import sys

assert sys.version_info[:3] == (3, 14, 7)

directory = Path(sys.argv[1])
directory.mkdir(parents=True, exist_ok=True)

header = ["名前", "i32"]
body = [
    ['Tcafé, "first"\r\nsecond', "T7"],
    ["T", "T-1"],
    ["N", "N"],
]


def write(name, records):
    with (directory / name).open("w", encoding="utf-8", newline="") as output:
        csv.writer(output).writerows(records)


write("data.csv", [header, *body])
write("header.csv", [header])
write("late-cell.csv", [header, *body[:2], ["N", "T+1"]])
write("late-width.csv", [header, *body[:2], []])
write("markers.csv", [[""], [""], [], [""]])
write("marker-header.csv", [[""]])

prefix = directory / "prefix.csv"
write(prefix.name, [header, *body[:2]])
(directory / "late-wire.csv").write_bytes(prefix.read_bytes() + b'"unterminated')
prefix.unlink()
wire = (directory / "data.csv").read_bytes()
assert wire.endswith(b"\r\n")
(directory / "unterminated-record.csv").write_bytes(wire[:-2])
print("CPython wrote eight row-budget controls.")
