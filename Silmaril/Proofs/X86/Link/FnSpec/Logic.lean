module

public import Silmaril.X86.Link.FnSpec.Defs
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.X86.Safe.Thms

/-!
# Proofs: step-indexed triples, code regions and the laws of the `FnSpec` logic

* `SafeN`: monotonicity in the index, post weakening, runs (`safeN_of_run`), prefixes of
  runs (`safeN_prefix`) and sequencing (`safeN_bind`).
* `STriple`: frame, consequence, the bridges from total `Triple`s (`STriple.of_triple`,
  `triple_seq`, `seq_triple`) and strict progress (`progress_seq`), which is how one step of
  the caller pays for the step index of the callee.
* `Code`: splitting off the bytes of one function (`code_split`).
* The four laws `Contract.Logic` asks for: `safe_zero`, `safe_mono`, `safe_frame`,
  `safe_sub`. `safe_sub` follows A's `sub_mono` (`Silmaril.Proofs.X86.Sep.SysV`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Link.FnSpec

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.Process (addressLimit)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le)
open Silmaril.X86.Link.FnSpec

/-! ## `SafeN`, `STriple`, `Progress`: the generic lemmas (`Silmaril.X86.Safe`)

These lemmas are proved once, for every machine, in `Silmaril.X86.Safe` (`Safe/Thms.lean`);
this file opens that namespace. -/

open Silmaril.X86.Safe

variable {n : Nat}

/-! ## Code regions -/

variable {D D' : Nat → Prop} {bs : Nat → Byte}

theorem code_congr (h : ∀ x, D x ↔ D' x) : Code D bs = Code D' bs := by
  funext f
  simp only [Code, h]

theorem union_single_erase {f : Frag} {l : Loc} {v : Val} (hl : f l = some v) :
    f = union (Frag.single l v) (fun l' => if l' = l then none else f l') := by
  funext l'
  simp only [union, Frag.single]
  by_cases e : l' = l
  · subst e; simp [hl]
  · simp [e]

theorem single_disjoint_erase (l : Loc) (v : Val) (f : Frag) :
    Disjoint (Frag.single l v) (fun l' => if l' = l then none else f l') := by
  intro l'
  by_cases e : l' = l
  · exact .inr (by simp [e])
  · exact .inl (by simp [Frag.single, e])

/-- **Splitting one byte off a code region.** -/
theorem code_split_byte {a : Nat} (hD : D a) :
    Code D bs = (codeByte a (bs a) ∗ Code (fun x => D x ∧ x ≠ a) bs) := by
  funext f
  apply propext
  constructor
  · rintro ⟨hin, hout⟩
    obtain ⟨hlim, p, hp, hfa⟩ := hin a hD
    refine ⟨Frag.single (.mem a) (.cell ⟨some (bs a), p⟩), _, single_disjoint_erase _ _ f,
      union_single_erase hfa, ⟨hlim, p, hp, rfl⟩, ?_, ?_⟩
    · intro x ⟨hx, hxa⟩
      refine ⟨(hin x hx).1, ?_⟩
      obtain ⟨_, q, hq, hfx⟩ := hin x hx
      exact ⟨q, hq, by simp [hxa, hfx]⟩
    · intro l hl
      by_cases e : l = .mem a
      · simp [e]
      · simp only [e, ite_false]
        refine hout l fun x hx he => ?_
        subst he
        exact hl x ⟨hx, fun h => e (h ▸ rfl)⟩ rfl
  · rintro ⟨f₁, f₂, hd, rfl, ⟨hlim, p, hp, rfl⟩, hin, hout⟩
    refine ⟨fun x hx => ?_, fun l hl => ?_⟩
    · by_cases e : x = a
      · subst e
        exact ⟨hlim, p, hp, by simp [union, Frag.single]⟩
      · obtain ⟨hl, q, hq, hfx⟩ := hin x ⟨hx, e⟩
        refine ⟨hl, q, hq, ?_⟩
        have : Frag.single (.mem a) (.cell ⟨some (bs a), p⟩) (.mem x) = none := by
          simp [Frag.single, e]
        simp [union, this, hfx]
    · have h₁ : Frag.single (.mem a) (.cell ⟨some (bs a), p⟩) l = none := by
        simp [Frag.single, hl a hD]
      have h₂ : f₂ l = none := hout l fun x hx => hl x hx.1
      simp [union, h₁, h₂]

/-- **Splitting a function's bytes off a code region.** -/
theorem code_split : ∀ (code : List Byte) {D : Nat → Prop} (a : Nat),
    (∀ i (hi : i < code.length), D (a + i) ∧ bs (a + i) = code[i]) →
    Code D bs = (codePt a code ∗ Code (fun x => D x ∧ ¬ (a ≤ x ∧ x < a + code.length)) bs)
  | [], D, a, _ => by
    rw [show codePt a [] = emp from rfl, emp_sep]
    exact code_congr fun x => by simp
  | c :: cs, D, a, hD => by
    have h0 := hD 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [code_split_byte (a := a) h0.1, h0.2]
    have hD' : ∀ i (hi : i < cs.length), (D (a + 1 + i) ∧ a + 1 + i ≠ a) ∧
        bs (a + 1 + i) = cs[i] := by
      intro i hi
      have := hD (i + 1) (by simp; omega)
      rw [show a + (i + 1) = a + 1 + i by omega] at this
      exact ⟨⟨this.1, by omega⟩, by simpa using this.2⟩
    rw [code_split cs (a + 1) hD']
    show _ = ((codeByte a c ∗ codePt (a + 1) cs) ∗ _)
    have hc : Code (fun x => (D x ∧ x ≠ a) ∧ ¬ (a + 1 ≤ x ∧ x < a + 1 + cs.length)) bs =
        Code (fun x => D x ∧ ¬ (a ≤ x ∧ x < a + (c :: cs).length)) bs :=
      code_congr fun x => by
        simp only [List.length_cons]
        constructor
        · rintro ⟨⟨hx, h1⟩, h2⟩; exact ⟨hx, by omega⟩
        · rintro ⟨hx, h1⟩; exact ⟨⟨hx, by omega⟩, by omega⟩
    rw [sep_assoc, hc]

/-! ## The laws of the logic -/

open Silmaril.X86.Link.Contract (Extends Image)

variable {σ : Type} {I : Silmaril.X86.SegVC.Isa σ}

theorem safe_zero (a : Nat) (S : FnSpec) (ctx : Image) : SafeOn I 0 a S ctx :=
  fun _ _ _ _ _ _ _ _ => STriple.zero _ _

theorem safe_mono {a : Nat} {S : FnSpec} {ctx : Image} (h : SafeOn I (n + 1) a S ctx) :
    SafeOn I n a S ctx :=
  fun D bs hc x sp ret hA hst => STriple.mono (h D bs hc x sp ret hA hst)

theorem safe_frame {a : Nat} {S : FnSpec} {img big : Image} (hext : Extends img big)
    (h : SafeOn I n a S img) : SafeOn I n a S big :=
  fun D bs hc => h D bs fun a b ⟨f, hf, hcon⟩ => hc a b ⟨f, hf, hext a b f hcon⟩

/-- **Refinement**: a function safe for `S` is safe for every `T` with `S ⊑ T`. -/
theorem safe_sub {a : Nat} {S T : FnSpec} {ctx : Image} (hsub : S.Sub T)
    (h : SafeOn I n a S ctx) : SafeOn I n a T ctx := by
  intro D bs hc y sp ret hA hst
  obtain ⟨x, hargs, R, hpre, hpost⟩ := hsub.arg y
  have hle := hsub.stack
  have h' := STriple.frame (h D bs hc x sp ret hA (le_trans hle hst))
    (blockAny (sp.toNat - T.stack) (T.stack - S.stack) ∗ R)
  have split : ∀ k, blockAny (sp.toNat - T.stack) (T.stack + k) =
      (blockAny (sp.toNat - T.stack) (T.stack - S.stack) ∗
        blockAny (sp.toNat - S.stack) (S.stack + k)) := by
    intro k
    rw [← show sp.toNat - T.stack + (T.stack - S.stack) = sp.toNat - S.stack by omega,
      ← blockAny_add]
    congr 1; omega
  refine STriple.conseq ?_ h' ?_
  · simp only [FnSpec.SysVPre]
    refine entails_trans (sep_mono_right _ (sep_mono_right _ hpre)) (entails_of_eq ?_)
    simp only [FnSpec.SysVEntry]
    have split0 := split 0
    simp only [Nat.add_zero] at split0
    rw [hargs, split0]
    ac_rfl
  · simp only [FnSpec.SysVPost]
    rw [sep_sexists, sexists_sep, sep_sexists]
    refine sexists_elim fun v => sexists_intro v ?_
    refine entails_trans (entails_of_eq ?_) (sep_mono_right _ (sep_mono_right _ (hpost v)))
    simp only [FnSpec.SysVExit]
    rw [split 8]
    ac_rfl

end Silmaril.Proofs.X86.Link.FnSpec

namespace Silmaril.Proofs.X86.Link.FnSpec

open Silmaril.X86.Sep
open Silmaril.X86.Link.FnSpec

/-- **The `FnSpec` logic on the machine `step`** (`Spec := FnSpec`, `Sub := FnSpec.Sub`). -/
def logicOn {σ : Type} (I : Silmaril.X86.SegVC.Isa σ) :
    Silmaril.X86.Link.Contract.Logic FnSpec where
  Safe := SafeOn I
  zero := safe_zero
  mono := safe_mono
  frame := safe_frame
  Sub := FnSpec.Sub
  sub := safe_sub

/-- **The `FnSpec` logic** on the open machine. -/
abbrev logic : Silmaril.X86.Link.Contract.Logic FnSpec := logicOn Silmaril.X86.Open.isa

end Silmaril.Proofs.X86.Link.FnSpec
