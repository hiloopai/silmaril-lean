"""Mark native compressed meta-block lengths in the distance trace."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-distance/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()
anchor = "        PrepareLiteralDecoding(s);"
if source.count(anchor) != 1:
    raise ValueError("unexpected pinned native meta-block code")
source = source.replace(anchor, r"""
        fprintf(stderr, "metablock %d\n", s->meta_block_remaining_len);
""" + anchor, 1)

anchor = "  if (BROTLI_PREDICT_FALSE(s->meta_block_remaining_len <= 0)) {"
if source.count(anchor) != 1:
    raise ValueError("unexpected pinned terminal-literal code")
source = source.replace(anchor, anchor + r"""
    fprintf(stderr, "terminal_command %zu %d\n",
            8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br), pos);
    TraceDistanceRing("terminal_ring", s);
""", 1)
path.write_text(source)
