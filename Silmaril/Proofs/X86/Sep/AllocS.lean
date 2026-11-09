module

public import Silmaril.X86.Sep.AllocS.Defs
public import Silmaril.X86.Sep.Extra.Thms
public import Silmaril.X86.Sep.SysV.Thms

/-!
# Proofs: the availability layer

* `FnSpec.SubH`: `sub_subH` (every `Sub` is a `SubH`), `subH_trans`, and `subH_satWith`
  (satisfaction transfers along `SubH`, through one `Sub` per hidden choice and
  `SPEC.sexists`).
* `mallocSpecS_subH`: `mallocSpecS B ⊑ₕ mallocSpec B.toIface`.
* `mallocS_post_avail`: under `avail`, the postcondition gives the `Fresh` block.
* `toIface_toS`, `mallocSpec_sub_toS`: every loose allocator is a strong one.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepAllocS

open Silmaril.X86 (Word)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep

variable {σ : Type} {I : Isa σ}
open Silmaril.X86.Sep.Alloc

/-! ## Heap-dependent refinement -/

theorem sub_subH {S T : FnSpec} (h : S.Sub T) : S.SubH T :=
  ⟨h.stack, fun y f hp => by
    obtain ⟨x, hx, R, hpre, hpost⟩ := h.arg y
    exact ⟨x, hx, R, hpre f hp, hpost⟩⟩

theorem subH_trans {S T U : FnSpec} (h₁ : S.SubH T) (h₂ : T.SubH U) : S.SubH U := by
  refine ⟨le_trans h₁.stack h₂.stack, fun z f hz => ?_⟩
  obtain ⟨y, hy, R₂, hT, hpost₂⟩ := h₂.arg z f hz
  obtain ⟨a, b, hd, he, ha, hb⟩ := hT
  obtain ⟨x, hx, R₁, hS, hpost₁⟩ := h₁.arg y a ha
  refine ⟨x, hx.trans hy, R₁ ∗ R₂, ?_, fun v => ?_⟩
  · rw [← sep_assoc]
    exact ⟨a, b, hd, he, hS, hb⟩
  · refine entails_trans (entails_of_eq (sep_assoc _ _ _).symm) ?_
    exact entails_trans (sep_mono_left R₂ (hpost₁ v)) (hpost₂ v)

/-- **Satisfaction transfers along `SubH`.** -/
theorem subH_satWith {A : Word → Prop} {S T : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith I A C entry) (hsub : S.SubH T) : T.SatWith I A C entry := by
  intro y sp ret hA hst
  let Z := {p : S.Arg × SProp // S.args p.1 = T.args y ∧ ∀ v, (S.post p.1 v ∗ p.2) ⊢ₛ T.post y v}
  have hpre : T.pre y ⊢ₛ sexists fun z : Z => S.pre z.1.1 ∗ z.1.2 := fun f hp => by
    obtain ⟨x, hx, R, hR, hpost⟩ := hsub.arg y f hp
    exact ⟨⟨(x, R), hx, hpost⟩, hR⟩
  refine SPEC.conseq (sep_mono_right _ hpre) ?_ (entails_refl _)
  rw [sep_sexists]
  refine SPEC.sexists fun z => ?_
  let T' : FnSpec :=
    { Arg := Unit, args := fun _ => T.args y, stack := T.stack,
      pre := fun _ => S.pre z.1.1 ∗ z.1.2, post := fun _ v => T.post y v }
  have hsub' : S.Sub T' := ⟨hsub.stack, fun _ => ⟨z.1.1, z.2.1, z.1.2, entails_refl _, z.2.2⟩⟩
  exact (FnSpec.SatWith.mono hS hsub') () sp ret hA hst

/-! ## `mallocSpecS` -/

theorem mallocSpecS_subH (B : IfaceS) : (mallocSpecS B).SubH (mallocSpec B.toIface) := by
  refine ⟨le_refl _, fun n f hp => ?_⟩
  obtain ⟨s, hs⟩ := hp
  refine ⟨(s, n), rfl, emp, ?_, fun v => ?_⟩
  · rw [sep_emp]; exact hs
  · refine entails_trans (entails_of_eq (sep_emp _)) ?_
    exact sep_mono_right _ (spure_sep_elim fun _ => entails_refl _)

theorem mallocS_post_avail (B : IfaceS) {s : B.St} {n v : Word} (ha : B.avail s n.toNat) :
    (mallocSpecS B).post (s, n) v ⊢ₛ (B.toIface.mm ∗ B.toIface.Fresh v n.toNat) := by
  refine sep_mono_right _ (spure_sep_elim fun hv => ?_)
  refine sor_elim (fun f hf => ?_) (entails_refl _)
  exact absurd ((spure_sep_apply _ emp f).mp (by rw [sep_emp]; exact hf)).1 (hv ha)

/-- Under `avail`, the postcondition with result `NULL` is unsatisfiable (so `mallocSpecS` is
strictly stronger than `mallocSpec` whenever `avail` holds somewhere). -/
theorem mallocS_post_null_false (B : IfaceS) {s : B.St} {n : Word} (ha : B.avail s n.toNat) :
    ∀ h, ¬ (mallocSpecS B).post (s, n) 0 h := by
  rintro h ⟨_, _, -, -, -, g, _, -, -, ⟨-, hv⟩, -⟩
  exact hv ha rfl

/-! ## Loose allocators are strong ones -/

theorem toIface_toS (A : Iface) : A.toS.toIface = A := by
  cases A with
  | mk mm tok align stack =>
    show ({ mm := sexists fun _ : Unit => mm, tok := tok, align := align, stack := stack } :
      Iface) = _
    congr 1
    funext f
    exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

theorem mallocSpec_sub_toS (A : Iface) : (mallocSpec A).Sub (mallocSpecS A.toS) := by
  refine ⟨le_refl _, fun y => ⟨y.2, rfl, emp, entails_of_eq (sep_emp _).symm, fun v => ?_⟩⟩
  refine entails_trans (entails_of_eq (sep_emp _)) ?_
  show (A.mm ∗ sor ⌜v = 0⌝ (A.Fresh v y.2.toNat)) ⊢ₛ
    (A.toS.toIface.mm ∗ ⌜False → v ≠ 0⌝ ∗ sor ⌜v = 0⌝ (A.toS.toIface.Fresh v y.2.toNat))
  rw [toIface_toS]
  exact sep_mono_right _ (spure_sep_intro (fun h => h.elim) (entails_refl _))

end Silmaril.Proofs.X86.SepAllocS
