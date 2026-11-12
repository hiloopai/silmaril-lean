module

public import Silmaril.Wasm.JcoTool.HelpersEnc.Defs

/-!
# `CMod`'s encoding pieces against silmaril's encoder

Each piece of `Silmaril.Wasm.JcoTool.CMod.encode` (LEB128 numbers, names, lists, vectors,
sections) agrees with the corresponding piece of silmaril's `Binaryen.Exe` encoder, read as an
`Option` (`Except.toOption`). Both sides use the same `encU`/`encS`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.HelpersEnc

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen.Exe
open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Parse.ByteParse.Enc (u32 sized)

theorem u32_eq (n : Nat) : u32 n = (encU32 n).toOption := by
  unfold u32 encU32
  split <;> rfl

theorem u32_of_lt {n : Nat} (h : n < 2 ^ 32) : u32 n = some (encU n) := by
  unfold u32
  simp only [h, ↓reduceIte]

theorem encU32_of_lt {n : Nat} (h : n < 2 ^ 32) : encU32 n = .ok (encU n) := by
  unfold encU32
  simp only [h, ↓reduceIte]
  rfl

theorem toOption_eq_some {α : Type} {x : Except String α} {a : α} :
    x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

theorem list_eq {α β : Type} {f : α → Option Bytes} {g : β → Except String (List UInt8)}
    {xs : List α} {ys : List β} (h : List.Forall₂ (fun x y => f x = (g y).toOption) xs ys) :
    Silmaril.Parse.ByteParse.Enc.list f xs = (encList g ys).toOption := by
  induction h with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
    show (do let b ← f x; let bs ← Silmaril.Parse.ByteParse.Enc.list f xs; pure (b ++ bs)) =
      (do pure ((← g y) ++ (← encList g ys)) : Except String _).toOption
    rw [hxy, ih]
    cases g y <;> cases encList g ys <;> rfl

theorem vec_eq {α β : Type} {f : α → Option Bytes} {g : β → Except String (List UInt8)}
    {xs : List α} {ys : List β} (h : List.Forall₂ (fun x y => f x = (g y).toOption) xs ys) :
    Silmaril.Parse.ByteParse.Enc.vec f xs = (encVec g ys).toOption := by
  have hl : xs.length = ys.length := h.length_eq
  show (do let n ← u32 xs.length; let b ← Silmaril.Parse.ByteParse.Enc.list f xs; pure (n ++ b)) =
    (do pure ((← encU32 ys.length) ++ (← encList g ys)) : Except String _).toOption
  rw [hl, u32_eq, list_eq h]
  cases encU32 ys.length <;> cases encList g ys <;> rfl

theorem name_eq (s : String) :
    Silmaril.Wasm.Component.Binary.Encode.name s = (encName s).toOption := by
  show (do let n ← u32 s.toUTF8.size; pure (n ++ s.toUTF8.data.toList)) =
    (do pure ((← encU32 s.toUTF8.data.toList.length) ++ s.toUTF8.data.toList) :
      Except String _).toOption
  have hs : s.toUTF8.size = s.toUTF8.data.toList.length := Array.length_toList.symm
  rw [hs, u32_eq]
  cases encU32 s.toUTF8.data.toList.length <;> rfl

/-- `encList` of `encInstr` is `encInstrs`. -/
theorem encInstrs_eq (is : List Instr) : encInstrs is = encList encInstr is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    show (do pure ((← encInstr i) ++ (← encInstrs is)) : Except String _) =
      (do pure ((← encInstr i) ++ (← encList encInstr is)))
    rw [ih]

theorem encList_append {α : Type} (g : α → Except String (List UInt8)) (xs ys : List α) :
    encList g (xs ++ ys) = (do pure ((← encList g xs) ++ (← encList g ys))) := by
  induction xs with
  | nil =>
    show encList g ys = (do pure ([] ++ (← encList g ys)) : Except String _)
    cases encList g ys <;> rfl
  | cons x xs ih =>
    show (do pure ((← g x) ++ (← encList g (xs ++ ys))) : Except String _) =
      (do pure ((← (do pure ((← g x) ++ (← encList g xs)) : Except String _)) ++ (← encList g ys)))
    rw [ih]
    cases g x <;> cases encList g xs <;> cases encList g ys <;> simp [bind, Except.bind, pure, Except.pure]

/-- A section of a non-empty vector. -/
theorem section_eq {id : UInt8} {count : Nat} (hc : count ≠ 0) (body : Bytes) :
    CMod.section_ id body = (encSection id count body).toOption := by
  show (id :: ·) <$> (do let n ← u32 body.length; pure (n ++ body)) = _
  rw [u32_eq]
  unfold encSection
  simp only [hc, ↓reduceIte]
  cases encU32 body.length <;> rfl

/-- **A vector section**: what `CMod.vecSec` writes is silmaril's section of the vector. -/
theorem vecSec_ok {α β : Type} {id : UInt8} {f : α → Option Bytes}
    {g : β → Except String (List UInt8)} {xs : List α} {ys : List β} {s : Bytes}
    (hfg : List.Forall₂ (fun x y => f x = (g y).toOption) xs ys)
    (h : CMod.vecSec id f xs = some s) :
    ∃ v, encVec g ys = .ok v ∧ encSection id ys.length v = .ok s := by
  unfold CMod.vecSec at h
  by_cases he : xs.isEmpty = true
  · have hx : xs = [] := List.isEmpty_iff.mp he
    have hy : ys = [] := by subst hx; exact List.forall₂_nil_left_iff.mp hfg
    have hs : s = [] := by simpa [he] using h.symm
    subst hy hs
    exact ⟨encU 0, by simp [encVec, encList, encU32, pure, Except.pure, bind, Except.bind],
      by simp [encSection, pure, Except.pure]⟩
  · have hne : ys.length ≠ 0 := by
      rw [← hfg.length_eq]; simpa [List.isEmpty_iff, List.length_eq_zero_iff] using he
    have h' : (Silmaril.Parse.ByteParse.Enc.vec f xs).bind (CMod.section_ id) = some s := by
      have h0 := h
      simp only [he, Bool.false_eq_true, ↓reduceIte] at h0
      exact h0
    rw [vec_eq hfg] at h'
    obtain ⟨v, hv, hs⟩ := Option.bind_eq_some_iff.mp h'
    exact ⟨v, toOption_eq_some.mp hv, toOption_eq_some.mp ((section_eq hne v).symm.trans hs)⟩

/-- **Silmaril's encoder, piece by piece**: when every vector and section of `m` encodes, the
module's bytes are the header and the sections in the Core 3.0 order. -/
theorem encodeModule?_eq {m : Module}
    {v1 v2 v3 v4 v5 v6 v7 v9 v10 v11 v13 dc s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 : List UInt8}
    (hc : ((true && !m.data.isEmpty) ||
      (Binary.Core.codesDataIdxs (m.funcs.map fun f => (f.locals, f.body))).isEmpty) = true)
    (h1 : encVec encRecType m.types = .ok v1) (h2 : encVec encImport m.imports = .ok v2)
    (h3 : encVec (fun f => pure (encIdx f.type)) m.funcs = .ok v3)
    (h5 : encVec encMemory m.memories = .ok v5)
    (h13 : encVec (fun t => pure (encTagType t)) m.tags = .ok v13)
    (h6 : encVec encGlobal m.globals = .ok v6) (h7 : encVec encExport m.exports = .ok v7)
    (h10 : encVec encCode m.funcs = .ok v10) (h11 : encVec encData m.data = .ok v11)
    (hdc : encU32 m.data.length = .ok dc) (h4 : encVec (encTableWith encExpr) m.tables = .ok v4)
    (h9 : encVec encElem m.elems = .ok v9)
    (g1 : encSection 1 m.types.length v1 = .ok s1) (g2 : encSection 2 m.imports.length v2 = .ok s2)
    (g3 : encSection 3 m.funcs.length v3 = .ok s3) (g4 : encSection 4 m.tables.length v4 = .ok s4)
    (g5 : encSection 5 m.memories.length v5 = .ok s5) (g13 : encSection 13 m.tags.length v13 = .ok s13)
    (g6 : encSection 6 m.globals.length v6 = .ok s6) (g7 : encSection 7 m.exports.length v7 = .ok s7)
    (g8 : encSection 8 (if m.start.isSome then 1 else 0) (encStart m.start) = .ok s8)
    (g9 : encSection 9 m.elems.length v9 = .ok s9)
    (g12 : encSection 12 (if true && !m.data.isEmpty then 1 else 0) dc = .ok s12)
    (g10 : encSection 10 m.funcs.length v10 = .ok s10) (g11 : encSection 11 m.data.length v11 = .ok s11) :
    encodeModule? m = .ok (header ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s13 ++ s6 ++ s7 ++ s8 ++ s9 ++
      s12 ++ s10 ++ s11) := by
  unfold encodeModule? encodeModuleWith?
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc), h3, h13]
  simp only [h1, h2, h5, h6, h7, h10, h11, hdc, h4, h9, g1, g2, g3, g4, g5, g13, g6, g7, g8,
    g9, g12, g10, g11, bind, Except.bind, pure, Except.pure]

end Silmaril.Wasm.JcoTool.HelpersEnc
