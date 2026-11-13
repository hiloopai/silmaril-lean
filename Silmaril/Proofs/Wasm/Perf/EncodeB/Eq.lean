module

public import Silmaril.Wasm.Perf.EncodeB.Defs

/-!
# The `ByteArray` encoders are the list encoders: proofs

The statements are restated in `Silmaril.Wasm.Perf.EncodeB.Thms`.

`toBA_append`, `secsB_eq`, `encode_eq_encodeF : Binary.encode = encodeF` (registered with
`@[csimp]` in the header), `astXB_eq`, `astXB_some_iff`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Perf.EncodeB

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync
open Silmaril.Wasm.Perf.EncodeB

private theorem ba_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

theorem toBA_append (l l' : List UInt8) : toBA (l ++ l') = toBA l ++ toBA l' :=
  ba_ext (by simp only [toBA, ByteArray.data_append, Array.toList_append, List.toList_toArray])

private theorem push_append (acc r : ByteArray) (len : List UInt8) (tag : UInt8) :
    (acc.push tag ++ toBA len) ++ r = acc ++ toBA (tag :: (len ++ r.data.toList)) :=
  ba_ext (by
    simp only [toBA, ByteArray.data_append, ByteArray.data_push, Array.toList_append,
      Array.toList_push, List.append_assoc, List.cons_append, List.nil_append])

private theorem append_nil (acc : ByteArray) : acc ++ toBA [] = acc :=
  ba_ext (by simp only [toBA, ByteArray.data_append, Array.toList_append, List.append_nil])

/-- The core module section, as `Encode.section_` writes it. -/
private theorem core_sec (acc m : ByteArray) :
    (do let len ← Silmaril.Parse.ByteParse.Enc.u32 m.size
        pure ((acc.push 0x01 ++ toBA len) ++ m)) =
      (Encode.section_ (.coreModule m)).map (acc ++ toBA ·) := by
  have hs : m.data.toList.length = m.size := by simp only [Array.length_toList, ByteArray.size]
  show _ = Option.map _ (do let s ← Silmaril.Parse.ByteParse.Enc.sized m.data.toList; pure (0x01 :: s))
  rw [Silmaril.Parse.ByteParse.Enc.sized, hs]
  cases Silmaril.Parse.ByteParse.Enc.u32 m.size with
  | none => rfl
  | some len => exact congrArg some (push_append acc m len 0x01)

theorem secB_eq (acc : ByteArray) (s : Section) :
    secB acc s = (Encode.section_ s).map (acc ++ toBA ·) := by
  cases s with
  | coreModule m => exact core_sec acc m
  | _ => rfl

theorem secsB_eq : ∀ (ss : List Section) (acc : ByteArray),
    secsB ss acc = (Encode.sections ss).map (acc ++ toBA ·)
  | [], acc => by
    show some acc = some (acc ++ toBA [])
    rw [append_nil]
  | s :: ss, acc => by
    show (secB acc s).bind (fun acc => secsB ss acc) =
      ((Encode.section_ s).bind fun a => (Encode.sections ss).bind fun b => some (a ++ b)).map
        (acc ++ toBA ·)
    rw [secB_eq]
    cases Encode.section_ s with
    | none => rfl
    | some a =>
      show secsB ss (acc ++ toBA a) =
        ((Encode.sections ss).bind fun b => some (a ++ b)).map (acc ++ toBA ·)
      rw [secsB_eq ss]
      cases Encode.sections ss with
      | none => rfl
      | some b =>
        show some (acc ++ toBA a ++ toBA b) = some (acc ++ toBA (a ++ b))
        rw [toBA_append, ByteArray.append_assoc]

/-- **`encodeF` is `Binary.encode`**, used by the compiler in its place. -/
theorem encode_eq_encodeF : @encode = @encodeF := by
  funext c
  cases c with
  | mk ss =>
    show (Encode.ast (.mk ss)).map (fun l => ⟨l.toArray⟩) = secsB ss (toBA preambleBytes)
    rw [secsB_eq]
    show (Encode.sections ss >>= fun b => some (preambleBytes ++ b)).map toBA = _
    cases Encode.sections ss with
    | none => rfl
    | some b => exact congrArg some (toBA_append _ _)

theorem secXB_eq (acc : ByteArray) (s : SectionX) :
    secXB acc s = (EncodeX.section_ s).map (acc ++ toBA ·) := by
  cases s with
  | coreModule m => exact core_sec acc m
  | _ => rfl

theorem secsXB_eq : ∀ (ss : List SectionX) (acc : ByteArray),
    secsXB ss acc = (EncodeX.sections ss).map (acc ++ toBA ·)
  | [], acc => by
    show some acc = some (acc ++ toBA [])
    rw [append_nil]
  | s :: ss, acc => by
    show (secXB acc s).bind (fun acc => secsXB ss acc) =
      ((EncodeX.section_ s).bind fun a => (EncodeX.sections ss).bind fun b => some (a ++ b)).map
        (acc ++ toBA ·)
    rw [secXB_eq]
    cases EncodeX.section_ s with
    | none => rfl
    | some a =>
      show secsXB ss (acc ++ toBA a) =
        ((EncodeX.sections ss).bind fun b => some (a ++ b)).map (acc ++ toBA ·)
      rw [secsXB_eq ss]
      cases EncodeX.sections ss with
      | none => rfl
      | some b =>
        show some (acc ++ toBA a ++ toBA b) = some (acc ++ toBA (a ++ b))
        rw [toBA_append, ByteArray.append_assoc]

theorem astXB_eq (a : AstX) : astXB a = (EncodeX.ast a).map toBA := by
  cases a with
  | mk ss =>
    show secsXB ss (toBA preambleBytes) = (EncodeX.sections ss >>= fun b => some (preambleBytes ++ b)).map toBA
    rw [secsXB_eq]
    cases EncodeX.sections ss with
    | none => rfl
    | some b => exact congrArg some (toBA_append _ _).symm

private theorem toBA_eq_iff (l : List UInt8) (b : ByteArray) : toBA l = b ↔ l = b.data.toList := by
  constructor
  · intro h
    rw [← h]
    rfl
  · intro h
    rw [h]
    exact ba_ext rfl

theorem astXB_some_iff (a : AstX) (b : ByteArray) :
    astXB a = some b ↔ EncodeX.ast a = some b.data.toList := by
  rw [astXB_eq]
  cases EncodeX.ast a with
  | none =>
    show none = some b ↔ none = some b.data.toList
    exact ⟨fun h => absurd h (Option.some_ne_none b).symm,
      fun h => absurd h (Option.some_ne_none b.data.toList).symm⟩
  | some l =>
    show some (toBA l) = some b ↔ some l = some b.data.toList
    rw [Option.some_inj, Option.some_inj, toBA_eq_iff]

end Silmaril.Proofs.Wasm.Perf.EncodeB
