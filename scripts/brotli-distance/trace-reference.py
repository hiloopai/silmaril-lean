"""Observe native distance reads, classification and ring transitions."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-command/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()

for anchor, snippet in (
    ("/* Precondition: s->distance_code < 0. */", r"""
static void TraceDistanceRing(const char* tag, const BrotliDecoderState* s) {
  int index = s->dist_rb_idx;
  fprintf(stderr, "%s %d %d %d %d\n", tag,
          s->dist_rb[(index + 3) & 3], s->dist_rb[(index + 2) & 3],
          s->dist_rb[(index + 1) & 3], s->dist_rb[index & 3]);
}

"""),
    ("    TakeDistanceFromRingBuffer(s);\n    return BROTLI_TRUE;", r"""
    fprintf(stderr, "distance_code %u 0 %u\n",
            (unsigned)code, (unsigned)s->dist_htree_index);
"""),
    ("  s->distance_code =\n      (int)(b->dist_offset[code] + (bits << s->distance_postfix_bits));", r"""
  fprintf(stderr, "distance_code %u %u %u\n",
          (unsigned)code, (unsigned)bits, (unsigned)s->dist_htree_index);
"""),
    ("  if (s->distance_code >= 0) {\n    /* Implicit distance case. */", r"""
  fprintf(stderr, "distance_begin %zu %u %u\n",
          8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br),
          (unsigned)(s->distance_code < 0), (unsigned)s->distance_context);
  TraceDistanceRing("ring_before", s);
"""),
    ("  /* Apply copy of LZ77 back-reference, or static dictionary reference if", r"""
  fprintf(stderr, "distance_end %zu %d %d %d %d\n",
          8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br),
          pos, s->max_distance, s->distance_code, s->copy_length);
"""),
    ("      s->dist_rb_idx += s->distance_context;", ""),
    ("    ++s->dist_rb_idx;\n    s->meta_block_remaining_len -= i;", ""),
):
    if source.count(anchor) != 1:
        raise ValueError(f"unexpected pinned distance decoder at {anchor!r}")
    if anchor == "      s->dist_rb_idx += s->distance_context;":
        source = source.replace(anchor, anchor + r'''
      fprintf(stderr, "dictionary_id %d\n", address);
      TraceDistanceRing("dictionary", s);''', 1)
    elif anchor.startswith("    ++s->dist_rb_idx;"):
        source = source.replace(anchor, anchor.replace("\n", '\n    TraceDistanceRing("back", s);\n', 1), 1)
    else:
        source = source.replace(anchor, snippet + anchor, 1)
path.write_text(source)
