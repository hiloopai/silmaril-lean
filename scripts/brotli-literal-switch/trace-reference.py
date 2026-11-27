"""Observe the selected switched-literal mode, context, tree and code extents."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-insert-copy-switch/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()
for anchor, snippet in (
    ("      context = BROTLI_CONTEXT(p1, p2, s->context_lookup);", r"""
      const uint8_t prior1 = p1;
      const uint8_t prior2 = p2;
      const size_t literal_begin =
          8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br);
"""),
    ("      s->ringbuffer[pos] = p1;", r"""
      fprintf(stderr, "switched_literal %u %u %u %u %u %u %u %u %u %zu %zu\n",
              (unsigned)s->block_type_rb[1], (unsigned)s->block_type_rb[0],
              (unsigned)(s->block_length[0] - 1), (unsigned)s->context_modes[s->block_type_rb[1]],
              (unsigned)prior1, (unsigned)prior2, (unsigned)context,
              (unsigned)s->context_map_slice[context], (unsigned)p1, literal_begin,
              8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
"""),
):
    if source.count(anchor) != 1:
        raise ValueError(f"unexpected pinned literal decoder at {anchor!r}")
    source = source.replace(anchor, snippet + anchor, 1)
path.write_text(source)
