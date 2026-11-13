module

public import Silmaril.Wasm.Perf.EncodeB.Defs
import Silmaril.Proofs.Wasm.Perf.EncodeB.Eq

/-!
# The `ByteArray` encoders are the list encoders

`toBA_append`; the section writers `secB_eq`, `secsB_eq` (and `secXB_eq`, `secsXB_eq` for the
async sections); **`encode_eq_encodeF : Binary.encode = encodeF`**, registered with
`@[csimp]`; `astXB_eq`, `astXB_some_iff`. The canonicity check is `Perf.CanonB`. The proofs
are in `Silmaril.Proofs.Wasm.Perf.EncodeB.Eq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.EncodeB

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync

theorem toBA_append (l l' : List UInt8) : toBA (l ++ l') = toBA l ++ toBA l' :=
  Silmaril.Proofs.Wasm.Perf.EncodeB.toBA_append l l'

theorem secB_eq (acc : ByteArray) (s : Section) :
    secB acc s = (Encode.section_ s).map (acc ++ toBA ·) :=
  Silmaril.Proofs.Wasm.Perf.EncodeB.secB_eq acc s

theorem secsB_eq (ss : List Section) (acc : ByteArray) :
    secsB ss acc = (Encode.sections ss).map (acc ++ toBA ·) :=
  Silmaril.Proofs.Wasm.Perf.EncodeB.secsB_eq ss acc

/-- **`encodeF` is `Binary.encode`**, used by the compiler in its place. -/
@[csimp] theorem encode_eq_encodeF : @encode = @encodeF :=
  Silmaril.Proofs.Wasm.Perf.EncodeB.encode_eq_encodeF

theorem secXB_eq (acc : ByteArray) (s : SectionX) :
    secXB acc s = (EncodeX.section_ s).map (acc ++ toBA ·) :=
  Silmaril.Proofs.Wasm.Perf.EncodeB.secXB_eq acc s

theorem secsXB_eq (ss : List SectionX) (acc : ByteArray) :
    secsXB ss acc = (EncodeX.sections ss).map (acc ++ toBA ·) :=
  Silmaril.Proofs.Wasm.Perf.EncodeB.secsXB_eq ss acc

theorem astXB_eq (a : AstX) : astXB a = (EncodeX.ast a).map toBA :=
  Silmaril.Proofs.Wasm.Perf.EncodeB.astXB_eq a

theorem astXB_some_iff (a : AstX) (b : ByteArray) :
    astXB a = some b ↔ EncodeX.ast a = some b.data.toList :=
  Silmaril.Proofs.Wasm.Perf.EncodeB.astXB_some_iff a b

end Silmaril.Wasm.Perf.EncodeB
