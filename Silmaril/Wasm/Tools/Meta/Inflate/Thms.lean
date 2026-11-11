module

public import Silmaril.Wasm.Tools.Meta.Inflate.Defs
import Silmaril.Proofs.Wasm.Tools.Meta.Inflate

/-!
# Inflate: theorems

* `zlibInflate_stored`: **`zlibInflate` decodes the stored-block encoding of any data of at
  most 65535 bytes within the cap back to the data** (`zlibStored`: the zlib header, one final
  stored block with `LEN`/`NLEN`, the Adler-32 checksum). The proof (raw,
  `Silmaril/Proofs/Wasm/Tools/Meta/Inflate.lean`) runs the decoder through the header check, the bit
  reader on byte boundaries (`bits_byte`, `bits_have`), the stored block's copy loop
  (`copy_loop`, `copyN_eq`) and the checksum (`adler32_lt`: the checksum fits the 32-bit
  trailer).
* `adler32_lt`: Adler-32 is below `2^32`.

Huffman blocks (fixed and dynamic) are tested against flate2 (`depv0-cases.py`), not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Inflate

/-- **Inflate decodes a stored stream.** -/
theorem zlibInflate_stored (cap : Nat) (d : ByteArray) (hn : d.size < 65536) (hc : d.size ≤ cap) :
    zlibInflate cap (zlibStored d) = .ok (some d) :=
  Silmaril.Proofs.Wasm.Tools.Meta.Inflate.zlibInflate_stored_raw cap d hn hc

/-- **Adler-32 fits 32 bits.** -/
theorem adler32_lt (d : ByteArray) : adler32 d < 2 ^ 32 :=
  Silmaril.Proofs.Wasm.Tools.Meta.Inflate.adler32_lt d

end Silmaril.Wasm.Tools.Meta.Inflate

end
