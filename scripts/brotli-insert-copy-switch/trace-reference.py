"""Observe category switches and command-run counters in pinned libbrotli."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-stream/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()
for anchor, snippet in (
    ("  brotli_reg_t block_type;", r"""
  size_t type_end;
  const size_t switch_begin =
      8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br);
"""),
    ("    block_type = ReadSymbol(type_tree, br);", r"""
    type_end = 8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br);
"""),
    ("    if (!SafeReadSymbol(type_tree, br, &block_type)) return BROTLI_FALSE;", r"""
    type_end = 8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br);
"""),
    ("  if (block_type == 1) {", r"""
  const unsigned type_symbol = (unsigned)block_type;
"""),
    ("  ringbuffer[1] = block_type;", r"""
  fprintf(stderr, "switch %d %u %u %u %u %zu %zu %zu\n",
          tree_type, type_symbol, (unsigned)ringbuffer[0], (unsigned)block_type,
          (unsigned)s->block_length[tree_type], switch_begin, type_end,
          8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
"""),
    ("  --s->block_length[1];", r"""
  fprintf(stderr, "command_run %u %u %u\n",
          (unsigned)s->block_type_rb[3], (unsigned)s->block_type_rb[2],
          (unsigned)(s->block_length[1] - 1));
"""),
):
    if source.count(anchor) != 1:
        raise ValueError(f"unexpected pinned block switch code at {anchor!r}")
    # The type boundary is after its symbol read. The other probes
    # observe state just before the anchor's update.
    if "ReadSymbol(type_tree" in anchor:
        replacement = anchor + snippet
    else:
        replacement = snippet + anchor
    source = source.replace(anchor, replacement, 1)
path.write_text(source)
