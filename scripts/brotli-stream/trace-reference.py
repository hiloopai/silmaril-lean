"""Add observer records at completed native meta-block headers."""
from pathlib import Path
import runpy
import sys

scripts = Path(__file__).resolve().parents[1]
runpy.run_path(str(scripts / "brotli-execute/trace-reference.py"))
path = Path(sys.argv[1]) / "c/dec/decode.c"
source = path.read_text()
anchor = "        BROTLI_LOG_UINT(s->is_uncompressed);"
if source.count(anchor) != 1:
    raise ValueError("unexpected pinned native framing code")
source = source.replace(anchor, anchor + r"""
        fprintf(stderr, "envelope %d %d %d %d %zu\n",
                s->is_last_metablock, s->is_metadata, s->is_uncompressed,
                s->meta_block_remaining_len,
                8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
""", 1)
anchor = "      case BROTLI_STATE_METABLOCK_DONE:"
if source.count(anchor) != 1:
    raise ValueError("unexpected pinned native block end")
path.write_text(source.replace(anchor, anchor + r"""
        fprintf(stderr, "envelope_end %zu\n",
                8 * BrotliBitReaderGetAvailIn(br) + BrotliGetAvailableBits(br));
""", 1))
