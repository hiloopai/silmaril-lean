#!/usr/bin/env python3
"""Read the pinned bitstruct projection bodies and pure object observations."""

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from export_bit_selection import INPUTS, export


BOOK = "projects/x86isa/utils/structures"
INPUT_FILES = (f"books/{BOOK}.lisp", "books/centaur/fty/bitstruct.lisp", *INPUTS)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    try:
        export(args.checkout, args.output, book=BOOK, inputs=INPUT_FILES,
               samples="prefixes-samples.lsp", metadata="prefixes-world.lsp", driver="export-prefixes")
    except ValueError as error:
        parser.exit(1, f"{error}\n")
