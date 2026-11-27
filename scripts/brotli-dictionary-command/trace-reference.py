"""Trace successful dictionary emission in the pinned libbrotli decoder."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-distance-switch/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()
anchor = "        pos += len;\n        s->meta_block_remaining_len -= len;"
if source.count(anchor) != 1:
    raise ValueError("unexpected pinned dictionary emission site")
source = source.replace(anchor, r'''
        fprintf(stderr, "dictionary_emit %d %d %d %d\n",
                address, transform_idx, i, len);
''' + anchor, 1)
path.write_text(source)
