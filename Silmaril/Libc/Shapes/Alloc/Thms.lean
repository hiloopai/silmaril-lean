module

public import Silmaril.Libc.Shapes.Alloc.Defs
public import Silmaril.Libc.X86Alloc.Spec.Thms

/-!
# Allocator shapes: the strengths, and what a client gets

* `Functional.live`: a functional row gives a live row for every capacity model it simulates
  (`RefModel.Sim`, with an invariant holding initially), at the image of the initial state; `Functional.live_self` for `R.toCap`.
* `Live.safe`: a live row gives a safe row.
* `Safe.client`: **client non-vacuity**: a property `Φ` proved for every `Iface` meeting the
  loose specs with this alignment and stack budget holds of an interface that this executable's
  code meets and its loaded image establishes.
* `Live.serves`: **success non-vacuity**: under `C.avail s0 n` the postcondition of the row's
  `malloc` is a fresh block (no failure branch).
-/

@[expose] public section

namespace Silmaril.Libc.Shapes.Alloc

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Project.Shapes (Loader Model)
open Silmaril.Libc.X86Alloc

variable {L : Loader} {M : Model} {V : Type} {exe : Silmaril.Project.Value V} {lay : Layout}
  {align stack : Nat}

theorem Functional.live {R : RefModel} {C : CapModel} {α : R.St → C.St} {Inv : R.St → Prop}
    {s0 : R.St} (hsim : R.Sim C α Inv) (h0 : Inv s0)
    (h : Functional L M exe lay R s0 align stack) :
    Live L M exe lay C (α s0) align stack := by
  obtain ⟨hl, B, ha, hs, hi, hm, hf⟩ := h
  exact ⟨hl, B.along α Inv, ha, hs,
    entails_trans hi (sexists_intro s0 (spure_sep_intro ⟨rfl, h0⟩ (entails_refl _))),
    (mallocSpecF_subH_along hsim B).sat hm, (freeSpecL_subH_along hsim B).sat hf⟩

theorem Functional.live_self {R : RefModel} {s0 : R.St}
    (h : Functional L M exe lay R s0 align stack) :
    Live L M exe lay R.toCap s0 align stack :=
  h.live (RefModel.sim_self R) trivial

theorem Live.safe {C : CapModel} {s0 : C.St} (h : Live L M exe lay C s0 align stack) :
    Safe L M exe lay align stack := by
  obtain ⟨hl, B, ha, hs, hi, hm, hf⟩ := h
  exact ⟨hl, B.toIface, ha, hs, entails_trans hi (sexists_intro s0 (entails_refl _)),
    (mallocSpecL_subH B).sat hm, (freeSpecL_subH B).sat hf⟩

/-- **Client non-vacuity.** -/
theorem Safe.client (h : Safe L M exe lay align stack) {Φ : Iface → Prop}
    (hΦ : ∀ A : Iface, A.align = align → A.stack = stack →
      (mallocSpec A).Sat M lay.C lay.mallocAt → (freeSpec A).Sat M lay.C lay.freeAt → Φ A) :
    ∃ A : Iface, (lay.Init ⊢ₛ A.mm) ∧ Φ A := by
  obtain ⟨-, A, ha, hs, hi, hm, hf⟩ := h
  exact ⟨A, hi, hΦ A ha hs hm hf⟩

/-- **Success non-vacuity.** -/
theorem Live.serves {C : CapModel} {s0 : C.St} (h : Live L M exe lay C s0 align stack) :
    ∃ B : IfaceL C, (lay.Init ⊢ₛ B.mmS s0) ∧ (mallocSpecL B).Sat M lay.C lay.mallocAt ∧
      ∀ (n v : Word), C.avail s0 n.toNat →
        ((mallocSpecL B).post (s0, n) v ⊢ₛ
          (B.toIface.Fresh v n.toNat ∗ B.mmS (C.alloc s0 n.toNat v))) := by
  obtain ⟨-, B, -, -, hi, hm, -⟩ := h
  exact ⟨B, hi, hm, fun _ _ ha => mallocSpecL_post_avail B ha⟩

end Silmaril.Libc.Shapes.Alloc
