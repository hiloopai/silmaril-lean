module

public import Silmaril.Wasm.Perf.Splice.Defs

/-!
# `spliceF` is `Splice.splice`: proofs

The statements are restated in `Silmaril.Wasm.Perf.Splice.Thms`.

`rawSecF_eq`, `rawSecsF_eq`, and `spliceF_eq : spliceF = Splice.splice`, registered with
`@[csimp]`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Perf.Splice

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wac.Splice (RawTable rawSec rawSecs splice)
open Silmaril.Wasm.Perf.Splice

private theorem ba_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

theorem toBA_append (l l' : List UInt8) : toBA (l ++ l') = toBA l ++ toBA l' :=
  ba_ext (by simp only [toBA, ByteArray.data_append, Array.toList_append, List.toList_toArray])

private theorem push_append (acc r : ByteArray) (len : List UInt8) :
    (acc.push 0x04 ++ toBA len) ++ r = acc ++ toBA (0x04 :: (len ++ r.data.toList)) :=
  ba_ext (by
    simp only [toBA, ByteArray.data_append, ByteArray.data_push, Array.toList_append,
      Array.toList_push, List.append_assoc, List.cons_append, List.nil_append])

theorem rawSecF_eq (raw : RawTable) (acc : ByteArray) (s : Section) :
    rawSecF raw acc s = (rawSec raw s).map (acc ++ toBA ·) := by
  unfold rawSecF rawSec
  split
  · rename_i n t
    cases h : raw.lookup n.name with
    | none => simp only [h]
    | some r =>
      have hs : r.data.toList.length = r.size := by
        simp only [Array.length_toList, ByteArray.size]
      simp only [h]
      rw [Silmaril.Parse.ByteParse.Enc.sized, hs]
      cases Silmaril.Parse.ByteParse.Enc.u32 r.size with
      | none => rfl
      | some len => exact congrArg some (push_append acc r len)
  · rename_i hne
    split
    · exact absurd rfl (hne _ _)
    · rfl

theorem rawSecsF_eq (raw : RawTable) :
    ∀ (ss : List Section) (acc : ByteArray), rawSecsF raw ss acc = (rawSecs raw ss).map (acc ++ toBA ·)
  | [], acc => by
    have h : acc ++ toBA [] = acc :=
      ba_ext (by simp only [toBA, ByteArray.data_append, Array.toList_append, List.append_nil])
    show some acc = some (acc ++ toBA [])
    rw [h]
  | s :: ss, acc => by
    show (rawSecF raw acc s).bind (fun acc => rawSecsF raw ss acc) =
      ((rawSec raw s).bind fun a => (rawSecs raw ss).bind fun b => some (a ++ b)).map (acc ++ toBA ·)
    rw [rawSecF_eq]
    cases rawSec raw s with
    | none => rfl
    | some a =>
      show rawSecsF raw ss (acc ++ toBA a) =
        ((rawSecs raw ss).bind fun b => some (a ++ b)).map (acc ++ toBA ·)
      rw [rawSecsF_eq raw ss]
      cases rawSecs raw ss with
      | none => rfl
      | some b =>
        show some (acc ++ toBA a ++ toBA b) = some (acc ++ toBA (a ++ b))
        rw [toBA_append, ByteArray.append_assoc]

/-- **`spliceF` is `Splice.splice`**, used by the compiler in its place. -/
theorem splice_eq_spliceF : @splice = @spliceF := by
  funext raw c
  show (rawSecs raw c.sections).map (fun b => toBA (preambleBytes ++ b)) =
    rawSecsF raw c.sections (toBA preambleBytes)
  rw [rawSecsF_eq]
  cases rawSecs raw c.sections with
  | none => rfl
  | some b => exact congrArg some (toBA_append _ _)

/-- `splice_eq_spliceF` the other way round, for the definitions that call `spliceF`
(`Wac.Emit.composeWasmRaw`). -/
theorem spliceF_eq : @spliceF = @splice := splice_eq_spliceF.symm

end Silmaril.Proofs.Wasm.Perf.Splice
