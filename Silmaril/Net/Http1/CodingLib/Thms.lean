module

public import Silmaril.Net.Http1.CodingLib.Defs
public import Silmaril.Net.Http1.Codings.Thms

/-!
# Transfer codings from the compression library: laws

* `libDecoders_inverts`: the library's decoders invert its encoders, which discharges the
  assumption of `decodeTransfer_encodeTransfer` for `gzip` and `deflate`;
* `lib_roundTrip`: so any list of `gzip`/`deflate` transfer codings round-trips.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Formats.Compression

theorem libDecoders_inverts : libDecoders.Inverts libEncoders := by
  intro n f hf
  unfold libEncoders at hf
  unfold libDecoders
  split_ifs at hf ⊢ with h₁ h₂
  · cases hf; exact ⟨_, rfl, fun x => RoundTrip.whole Gzip.codec.roundTrip x⟩
  · cases hf; exact ⟨_, rfl, fun x => RoundTrip.whole Zlib.codec.roundTrip x⟩

theorem lib_roundTrip (cs : List Bytes) (x y : Bytes) (h : encodeTransfer libEncoders cs x = some y) :
    decodeTransfer libDecoders cs y = some x :=
  decodeTransfer_encodeTransfer libDecoders_inverts cs x y h

theorem libImplements_gzip : libImplements gzipName = true := by
  simp [libImplements, libDecoders]

theorem libImplements_compress : libImplements compressName = false := by
  simp [libImplements, libDecoders, gzipName, deflateName, compressName]
  decide

end Silmaril.Net.Http1
