module

public import Silmaril.Wasm.Wac.Splice.Defs
public import Silmaril.Wasm.Wac.Embed.Thms
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# WAC: splicing package bytes is embedding their ASTs

`splice_eq_embed`: under `Agrees tbl raw`, the spliced bytes are the encoding of the embedded
composition; `parse_splice`: they parse back to it.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Splice

open Silmaril.Wasm.Component.Binary

theorem raw_none {tbl : Embed.PkgTable} {raw : RawTable} (h : Agrees tbl raw) {n : String}
    (ht : tbl.lookup n = none) : raw.lookup n = none := by
  have hs := (h n).2
  rw [ht] at hs
  cases hr : raw.lookup n with
  | none => rfl
  | some r => rw [hr] at hs; simp at hs

theorem raw_some {tbl : Embed.PkgTable} {raw : RawTable} (h : Agrees tbl raw) {n : String}
    {a : Ast} (ht : tbl.lookup n = some a) :
    ∃ r, raw.lookup n = some r ∧ Encode.ast a = some r.data.toList := by
  have ⟨he, hs⟩ := h n
  rw [ht] at he hs
  cases hr : raw.lookup n with
  | none => rw [hr] at hs; simp at hs
  | some r => rw [hr] at he; exact ⟨r, rfl, he⟩

theorem rawSec_imp {tbl : Embed.PkgTable} {raw : RawTable} (h : Agrees tbl raw) (n : ExternName)
    (t : Nat) : rawSec raw (.imports [⟨n, .component t⟩]) =
      Encode.section_ (Embed.embedSec tbl (.imports [⟨n, .component t⟩])) := by
  simp only [rawSec, Embed.embedSec]
  cases ht : tbl.lookup n.name with
  | none => rw [raw_none h ht]
  | some a =>
    obtain ⟨r, hr, he⟩ := raw_some h ht
    simp only [hr, Encode.section_, he]
    rfl

theorem rawSec_eq {tbl : Embed.PkgTable} {raw : RawTable} (h : Agrees tbl raw) (s : Section) :
    rawSec raw s = Encode.section_ (Embed.embedSec tbl s) := by
  rcases Embed.embedSec_eq tbl s with h' | ⟨n, t, d, rfl, _⟩
  · by_cases hi : ∃ n t, s = .imports [⟨n, .component t⟩]
    · obtain ⟨n, t, rfl⟩ := hi
      exact rawSec_imp h n t
    · rw [h']
      unfold rawSec
      split
      · exact absurd ⟨_, _, rfl⟩ hi
      · rfl
  · exact rawSec_imp h n t

theorem rawSecs_eq {tbl : Embed.PkgTable} {raw : RawTable} (h : Agrees tbl raw) (ss : List Section) :
    rawSecs raw ss = Encode.sections (ss.map (Embed.embedSec tbl)) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [rawSecs, List.map_cons, Encode.sections, rawSec_eq h, ih]

/-- **Splicing the bytes is encoding the embedded composition.** -/
theorem splice_eq_embed {tbl : Embed.PkgTable} {raw : RawTable} (h : Agrees tbl raw) (c : Ast) :
    splice raw c = encode (Embed.embed tbl c) := by
  cases c with
  | mk ss =>
    simp only [splice, encode, Embed.embed, Ast.sections, Encode.ast, rawSecs_eq h]
    cases Encode.sections (ss.map (Embed.embedSec tbl)) <;> rfl

/-- **The spliced bytes parse back to the embedded composition.** -/
theorem parse_splice {tbl : Embed.PkgTable} {raw : RawTable} (h : Agrees tbl raw) {c : Ast}
    {b : ByteArray} (hb : splice raw c = some b) : parse b = .ok (Embed.embed tbl c) :=
  parse_encode (by rw [← splice_eq_embed h]; exact hb)

end Silmaril.Wasm.Wac.Splice
