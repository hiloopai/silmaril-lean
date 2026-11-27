"""Observe the active distance category run in the pinned native decoder."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-insert-copy-switch/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()
anchor = '  fprintf(stderr, "distance_end '
if source.count(anchor) != 1:
    raise ValueError("unexpected pinned distance trace site")
source = source.replace(anchor, r'''
  fprintf(stderr, "distance_run %u %u %u\n",
          (unsigned)s->block_type_rb[5], (unsigned)s->block_type_rb[4],
          (unsigned)s->block_length[2]);
''' + anchor, 1)
path.write_text(source)
