module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms.Defs

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge: basic facts about `NoAtoms`

`VInv.NoAtoms A v` says that no `case` of an atom of `A` occurs in `v`. This file has the
structural facts the encoder lemmas use:

* `noAtoms_mono`: a smaller atom list keeps `NoAtoms`;
* `noAtoms_list_map`, `noAtoms_opt_map`, `noAtoms_case`: the value formers;
* `NH v`: `NoAtoms hAtoms v`, the predicate the encoder lemmas prove; `mem_hAtoms` and the
  tactic `nh_close` close goals about literal atoms.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open HStep (hAtoms)

/-! ## Monotonicity -/

mutual
/-- **A smaller atom list keeps `NoAtoms`.** -/
theorem noAtoms_mono {A B : List MixopS} (hBA : ∀ a ∈ B, a ∈ A) :
    ∀ v : Value, NoAtoms A v → NoAtoms B v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => noAtomsL_mono hBA vs h
  | .case a w, h => ⟨fun hb => h.1 (hBA a hb), noAtoms_mono hBA w h.2⟩
  | .struct gs, h => noAtomsF_mono hBA gs h
  | .list vs, h => noAtomsL_mono hBA vs h
  | .opt none, _ => trivial
  | .opt (some w), h => noAtoms_mono hBA w h

theorem noAtomsL_mono {A B : List MixopS} (hBA : ∀ a ∈ B, a ∈ A) :
    ∀ vs : List Value, NoAtomsL A vs → NoAtomsL B vs
  | [], _ => trivial
  | v :: vs, h => ⟨noAtoms_mono hBA v h.1, noAtomsL_mono hBA vs h.2⟩

theorem noAtomsF_mono {A B : List MixopS} (hBA : ∀ a ∈ B, a ∈ A) :
    ∀ gs : List (AtomS × Value), NoAtomsF A gs → NoAtomsF B gs
  | [], _ => trivial
  | (_, v) :: gs, h => ⟨noAtoms_mono hBA v h.1, noAtomsF_mono hBA gs h.2⟩
end

theorem msAtoms_sub_hAtoms : ∀ a ∈ msAtoms, a ∈ hAtoms := by
  intro a ha
  simp only [msAtoms, hAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  rcases ha with rfl | rfl | rfl | rfl <;> simp

/-- `NoAtoms hAtoms` gives `NoAtoms msAtoms`. -/
theorem noAtoms_ms_of_h {v : Value} (h : NoAtoms hAtoms v) : NoAtoms msAtoms v :=
  noAtoms_mono msAtoms_sub_hAtoms v h

/-! ## The value formers -/

variable {A : List MixopS}

theorem noAtomsL_of_forall : ∀ {vs : List Value}, (∀ v ∈ vs, NoAtoms A v) → NoAtomsL A vs
  | [], _ => trivial
  | v :: vs, h => ⟨h v (by simp), noAtomsL_of_forall fun w hw => h w (by simp [hw])⟩

theorem forall_of_noAtomsL : ∀ {vs : List Value}, NoAtomsL A vs → ∀ v ∈ vs, NoAtoms A v
  | [], _ => by simp
  | _ :: _, h => by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact h.1
      · exact forall_of_noAtomsL h.2 w hw

theorem noAtoms_list {vs : List Value} (h : ∀ v ∈ vs, NoAtoms A v) : NoAtoms A (.list vs) :=
  noAtomsL_of_forall h

theorem noAtoms_list_map {α : Type} {f : α → Value} {l : List α} (h : ∀ x ∈ l, NoAtoms A (f x)) :
    NoAtoms A (.list (l.map f)) :=
  noAtoms_list (by simpa using h)

theorem noAtoms_opt_map {α : Type} {f : α → Value} {o : Option α} (h : ∀ x, o = some x →
    NoAtoms A (f x)) : NoAtoms A (.opt (o.map f)) := by
  cases o with
  | none => trivial
  | some x => exact h x rfl

theorem noAtoms_case {a : MixopS} {w : Value} (ha : a ∉ A) (hw : NoAtoms A w) :
    NoAtoms A (.case a w) :=
  ⟨ha, hw⟩

theorem noAtoms_of_case {a : MixopS} {w : Value} (h : NoAtoms A (.case a w)) : NoAtoms A w :=
  h.2

theorem noAtoms_of_list {vs : List Value} (h : NoAtoms A (.list vs)) : ∀ v ∈ vs, NoAtoms A v :=
  forall_of_noAtomsL h

/-! ## A Boolean check (for closed values) -/

mutual
/-- `NoAtoms A v`, as a Boolean. -/
def atomsFreeB (A : List MixopS) : Value → Bool
  | .bool _ => true
  | .num _ => true
  | .text _ => true
  | .tuple vs => atomsFreeLB A vs
  | .case a w => !A.contains a && atomsFreeB A w
  | .struct gs => atomsFreeFB A gs
  | .list vs => atomsFreeLB A vs
  | .opt none => true
  | .opt (some w) => atomsFreeB A w

/-- `atomsFreeB` on a list of values. -/
def atomsFreeLB (A : List MixopS) : List Value → Bool
  | [] => true
  | v :: vs => atomsFreeB A v && atomsFreeLB A vs

/-- `atomsFreeB` on the fields of a record. -/
def atomsFreeFB (A : List MixopS) : List (AtomS × Value) → Bool
  | [] => true
  | (_, v) :: gs => atomsFreeB A v && atomsFreeFB A gs
end

mutual
theorem atomsFreeB_sound (A : List MixopS) : ∀ v : Value, atomsFreeB A v = true → NoAtoms A v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => atomsFreeLB_sound A vs (by simpa only [atomsFreeB] using h)
  | .case a w, h => by
      simp only [atomsFreeB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at h
      exact ⟨h.1, atomsFreeB_sound A w h.2⟩
  | .struct gs, h => atomsFreeFB_sound A gs (by simpa only [atomsFreeB] using h)
  | .list vs, h => atomsFreeLB_sound A vs (by simpa only [atomsFreeB] using h)
  | .opt none, _ => trivial
  | .opt (some w), h => atomsFreeB_sound A w (by simpa only [atomsFreeB] using h)

theorem atomsFreeLB_sound (A : List MixopS) : ∀ vs : List Value, atomsFreeLB A vs = true →
    NoAtomsL A vs
  | [], _ => trivial
  | v :: vs, h => by
      simp only [atomsFreeLB, Bool.and_eq_true] at h
      exact ⟨atomsFreeB_sound A v h.1, atomsFreeLB_sound A vs h.2⟩

theorem atomsFreeFB_sound (A : List MixopS) : ∀ gs : List (AtomS × Value),
    atomsFreeFB A gs = true → NoAtomsF A gs
  | [], _ => trivial
  | (_, v) :: gs, h => by
      simp only [atomsFreeFB, Bool.and_eq_true] at h
      exact ⟨atomsFreeB_sound A v h.1, atomsFreeFB_sound A gs h.2⟩
end

/-! ## `NoAtoms hAtoms` -/

/-- `NoAtoms hAtoms`: no memory SIMD atom and no `CALL_REF`. -/
abbrev NH (v : Value) : Prop := NoAtoms hAtoms v

theorem mem_hAtoms {a : MixopS} :
    a ∈ hAtoms ↔ a = "VLOAD" ∨ a = "VLOAD_LANE" ∨ a = "VSTORE" ∨ a = "VSTORE_LANE" ∨
      a = "CALL_REF" := by
  simp [hAtoms]

theorem nh_case_of {a : MixopS} {w : Value} (ha : a ∉ hAtoms) (hw : NH w) : NH (.case a w) :=
  ⟨ha, hw⟩

/-- Unfold `NoAtoms` on value formers in the goal and the hypotheses, and decide the literal
atoms. -/
syntax "nh_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| nh_close) =>
    `(tactic| (simp only [NH, VInv.NoAtoms, VInv.NoAtomsL, VInv.NoAtomsF] at *
               simp_all [mem_hAtoms, VInv.NoAtoms, VInv.NoAtomsL, VInv.NoAtomsF]))
  | `(tactic| nh_close [$ts,*]) =>
    `(tactic| (simp only [NH, VInv.NoAtoms, VInv.NoAtomsL, VInv.NoAtomsF] at *
               simp_all [mem_hAtoms, VInv.NoAtoms, VInv.NoAtomsL, VInv.NoAtomsF, $ts,*]))

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
