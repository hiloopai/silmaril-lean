module

public import Silmaril.Wasm.Perf.XEncodeB.Defs
public import Silmaril.Wasm.Perf.EncodeB.Thms

/-!
# `xencodeF` is `XAst.encode`: proofs

The statements are restated in `Silmaril.Wasm.Perf.XEncodeB.Thms`.

`xsecsB_eq`, and `xencodeF_eq : XAst.encode = xencodeF` (`@[csimp]`: code compiled in a module
that imports this one calls `xencodeF` where its source says `XAst.encode`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Perf.XEncodeB

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Perf.EncodeB (toBA toBA_append)
open Silmaril.Wasm.Perf.XEncodeB

private theorem ba_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

private theorem append_nil (acc : ByteArray) : acc ++ toBA [] = acc :=
  ba_ext (by simp only [toBA, ByteArray.data_append, Array.toList_append, List.append_nil])

theorem xsecB_eq (acc : ByteArray) (s : XSection) :
    xsecB acc s = s.encode.map (acc ++ toBA ·) := by
  cases s with
  | sec s => exact Silmaril.Wasm.Perf.EncodeB.secB_eq acc s
  | builtins bs => rfl

theorem xsecsB_eq : ∀ (ss : List XSection) (acc : ByteArray),
    xsecsB ss acc = (XSection.encodeAll ss).map (acc ++ toBA ·)
  | [], acc => by
    show some acc = some (acc ++ toBA [])
    rw [append_nil]
  | s :: ss, acc => by
    show (xsecB acc s).bind (fun acc => xsecsB ss acc) =
      (s.encode.bind fun a => (XSection.encodeAll ss).bind fun b => some (a ++ b)).map
        (acc ++ toBA ·)
    rw [xsecB_eq]
    cases s.encode with
    | none => rfl
    | some a =>
      show xsecsB ss (acc ++ toBA a) =
        ((XSection.encodeAll ss).bind fun b => some (a ++ b)).map (acc ++ toBA ·)
      rw [xsecsB_eq ss]
      cases XSection.encodeAll ss with
      | none => rfl
      | some b =>
        show some (acc ++ toBA a ++ toBA b) = some (acc ++ toBA (a ++ b))
        rw [toBA_append, ByteArray.append_assoc]

/-- **`xencodeF` is `XAst.encode`**, used by the compiler in its place. -/
theorem xencodeF_eq : @XAst.encode = @xencodeF := by
  funext c
  show (XSection.encodeAll c.sections).map (fun b => ⟨(preambleBytes ++ b).toArray⟩) =
    xsecsB c.sections (toBA preambleBytes)
  rw [xsecsB_eq]
  cases XSection.encodeAll c.sections with
  | none => rfl
  | some b =>
    show some (toBA (preambleBytes ++ b)) = some (toBA preambleBytes ++ toBA b)
    rw [toBA_append]

end Silmaril.Proofs.Wasm.Perf.XEncodeB
