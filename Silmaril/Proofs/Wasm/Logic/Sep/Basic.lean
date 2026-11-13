module

public import Silmaril.Wasm.Logic.Sep.Defs

/-!
# Separation logic over the Core 3.0 store: heaps and the frame rule

The heap algebra (associativity of union, disjointness of unions) and the
structural rules of `STriple`: the **frame rule** `STriple.frame`, consequence
`STriple.conseq`, and `STriple.hwp`, which runs a triple without a frame.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Sep

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Heaps -/

theorem Heap.union_none {h₁ h₂ : Heap} {l : Loc} :
    h₁.union h₂ l = none ↔ h₁ l = none ∧ h₂ l = none := by
  unfold Heap.union
  cases h₁ l <;> simp

theorem Heap.union_assoc (a b c : Heap) : (a.union b).union c = a.union (b.union c) := by
  funext l
  unfold Heap.union
  cases a l <;> rfl

theorem Heap.Disj.symm {a b : Heap} (h : Heap.Disj a b) : Heap.Disj b a :=
  fun l => (h l).symm

theorem Heap.disj_union_left {a b c : Heap} :
    Heap.Disj (a.union b) c ↔ Heap.Disj a c ∧ Heap.Disj b c := by
  constructor
  · intro h
    refine ⟨fun l => ?_, fun l => ?_⟩ <;> rcases h l with h | h
    · exact .inl (Heap.union_none.mp h).1
    · exact .inr h
    · exact .inl (Heap.union_none.mp h).2
    · exact .inr h
  · rintro ⟨h₁, h₂⟩ l
    rcases h₁ l with h₁ | h₁
    · rcases h₂ l with h₂ | h₂
      · exact .inl (Heap.union_none.mpr ⟨h₁, h₂⟩)
      · exact .inr h₂
    · exact .inr h₁

theorem Heap.disj_union_right {a b c : Heap} :
    Heap.Disj a (b.union c) ↔ Heap.Disj a b ∧ Heap.Disj a c := by
  have h₁ : Heap.Disj a (b.union c) ↔ Heap.Disj (b.union c) a := ⟨Heap.Disj.symm, Heap.Disj.symm⟩
  rw [h₁, Heap.disj_union_left]
  exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

theorem Heap.union_left {a b : Heap} {l : Loc} {c : Cell} (h : a l = some c) :
    a.union b l = some c := by
  unfold Heap.union
  rw [h]

theorem Heap.union_right {a b : Heap} {l : Loc} {c : Cell} (ha : a l = none) (h : b l = some c) :
    a.union b l = some c := by
  unfold Heap.union
  rw [ha, h]

theorem Heap.union_some {a b : Heap} {l : Loc} {c : Cell} (h : a.union b l = some c) :
    a l = some c ∨ (a l = none ∧ b l = some c) := by
  unfold Heap.union at h
  cases ha : a l with
  | none => rw [ha] at h; exact .inr ⟨rfl, h⟩
  | some c' => rw [ha] at h; exact .inl h

theorem Heap.Sat.right {s : Store H} {a b : Heap} (hd : Heap.Disj a b) (h : Heap.Sat s (a.union b)) :
    Heap.Sat s b := fun l c hl => by
  rcases hd l with ha | hb
  · exact h l c (Heap.union_right ha hl)
  · rw [hb] at hl; cases hl

theorem Heap.Sat.left {s : Store H} {a b : Heap} (h : Heap.Sat s (a.union b)) : Heap.Sat s a :=
  fun l c hl => h l c (Heap.union_left hl)

/-! ## The frame rule -/

/-- **The frame rule.** -/
theorem STriple.frame {Pre : Frame → Assn} {code : List Admin} {Post : Frame → Outcome → Assn}
    (R : Assn) (h : STriple P host Pre code Post) :
    STriple P host (fun f => Pre f ∗ R) code (fun f o => Post f o ∗ R) := by
  rintro s f _ hF hd hsat ⟨h₁, h₂, hd₁₂, rfl, hp, hr⟩
  have hd' : Heap.Disj h₁ (h₂.union hF) :=
    Heap.disj_union_right.mpr ⟨hd₁₂, (Heap.disj_union_left.mp hd).1⟩
  have hsat' : Heap.Sat s (h₁.union (h₂.union hF)) := Heap.union_assoc h₁ h₂ hF ▸ hsat
  refine (h s f h₁ (h₂.union hF) hd' hsat' hp).mono fun s' f' o ⟨hQ, hdQ, hsQ, hq⟩ => ?_
  have hdQ₂ : Heap.Disj hQ h₂ := (Heap.disj_union_right.mp hdQ).1
  have hdQF : Heap.Disj (hQ.union h₂) hF :=
    Heap.disj_union_left.mpr ⟨(Heap.disj_union_right.mp hdQ).2, (Heap.disj_union_left.mp hd).2⟩
  exact ⟨hQ.union h₂, hdQF, (Heap.union_assoc hQ h₂ hF).symm ▸ hsQ, hQ, h₂, hdQ₂, rfl, hq, hr⟩

/-- **Consequence.** -/
theorem STriple.conseq {Pre Pre' : Frame → Assn} {code : List Admin}
    {Post Post' : Frame → Outcome → Assn} (hpre : ∀ f h, Pre' f h → Pre f h)
    (hpost : ∀ f o h, Post f o h → Post' f o h) (h : STriple P host Pre code Post) :
    STriple P host Pre' code Post' := fun s f hP hF hd hs hp =>
  (h s f hP hF hd hs (hpre f hP hp)).mono fun _ _ _ ⟨hQ, hdQ, hsQ, hq⟩ =>
    ⟨hQ, hdQ, hsQ, hpost _ _ _ hq⟩

theorem Heap.disj_empty (h : Heap) : Heap.Disj h Heap.empty := fun _ => .inr rfl

theorem Heap.union_empty (h : Heap) : h.union Heap.empty = h := by
  funext l
  unfold Heap.union
  cases h l <;> rfl

/-- **Running a triple** on a store that satisfies the precondition's heap. -/
theorem STriple.hwp {Pre : Frame → Assn} {code : List Admin} {Post : Frame → Outcome → Assn}
    (h : STriple P host Pre code Post) {s : Store H} {f : Frame} {hP : Heap}
    (hs : Heap.Sat s hP) (hp : Pre f hP) :
    HWP P host s f code fun s' f' o => ∃ hQ, Heap.Sat s' hQ ∧ Post f' o hQ := by
  refine (h s f hP Heap.empty (Heap.disj_empty hP) ((Heap.union_empty hP).symm ▸ hs) hp).mono ?_
  rintro s' f' o ⟨hQ, -, hsQ, hq⟩
  exact ⟨hQ, (Heap.union_empty hQ) ▸ hsQ, hq⟩

/-- **Sequencing**: after `c₁` falls through with `vs`, `c₂` runs on `vs`; every
other outcome of `c₁` must already satisfy the final postcondition. -/
theorem STriple.seq {Pre : Frame → Assn} {Mid Post : Frame → Outcome → Assn} {c₁ c₂ : List Admin}
    (h₁ : STriple P host Pre c₁ Mid)
    (h₂ : ∀ vs, STriple P host (fun f => Mid f (.normal vs)) (vals vs ++ c₂) Post)
    (hab : ∀ f o h, (∀ vs, o ≠ .normal vs) → Mid f o h → Post f o h) :
    STriple P host Pre (c₁ ++ c₂) Post := by
  intro s f hP hF hd hs hp
  refine Silmaril.Wasm.Logic.Hoare.HWP.seq ((h₁ s f hP hF hd hs hp).mono fun s' f' o hm => ?_)
  obtain ⟨hQ, hdQ, hsQ, hq⟩ := hm
  cases o with
  | normal vs => exact h₂ vs s' f' hQ hF hdQ hsQ hq
  | _ => exact ⟨hQ, hdQ, hsQ, hab _ _ _ (fun _ h => Outcome.noConfusion h) hq⟩

end Silmaril.Wasm.Logic.Sep
