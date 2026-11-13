module

public import Silmaril.Wasm.Perf.XEncodeB.Defs
public import Silmaril.Wasm.Perf.EncodeB.Thms
import Silmaril.Proofs.Wasm.Perf.XEncodeB.Eq

/-!
# `xencodeF` is `XAst.encode`

`xsecB_eq`, `xsecsB_eq`, and `xencodeF_eq : XAst.encode = xencodeF` (`@[csimp]`: code compiled
in a module that imports this one calls `xencodeF` where its source says `XAst.encode`). The
proofs are in `Silmaril.Proofs.Wasm.Perf.XEncodeB.Eq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.XEncodeB

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Perf.EncodeB (toBA)

theorem xsecB_eq (acc : ByteArray) (s : XSection) :
    xsecB acc s = s.encode.map (acc ++ toBA ·) :=
  Silmaril.Proofs.Wasm.Perf.XEncodeB.xsecB_eq acc s

theorem xsecsB_eq (ss : List XSection) (acc : ByteArray) :
    xsecsB ss acc = (XSection.encodeAll ss).map (acc ++ toBA ·) :=
  Silmaril.Proofs.Wasm.Perf.XEncodeB.xsecsB_eq ss acc

/-- **`xencodeF` is `XAst.encode`**, used by the compiler in its place. -/
@[csimp] theorem xencodeF_eq : @XAst.encode = @xencodeF :=
  Silmaril.Proofs.Wasm.Perf.XEncodeB.xencodeF_eq

end Silmaril.Wasm.Perf.XEncodeB
