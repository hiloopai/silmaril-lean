module

public import Silmaril.Wasm.FnInst.Models.Entry.Defs
public import Silmaril.Wasm.FnInst.Models.Base.Thms

/-!
# From function-level equations to module equivalence

* `moduleEquiv_of_sol_eq`: modules over the same context with the same solutions are
  `Equiv.ModuleEquiv`-equivalent for every reflexive behaviour relation;
* `moduleEquiv_replace`: **replacement**: if the partial-body model of `B` satisfies `b ≐ b'`,
  the modules with `b` and with `b'` at the focus are module-equivalent;
* `entry_valid_replace`: the same as validity of the equation `m ⊑ m'` in the existing entry
  logic `Entry.entryEquiv` at every interface.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models

open Silmaril.Wasm Silmaril.Wasm.Institution

variable {L : FnSyntax}

theorem moduleEquiv_of_sol_eq (S : FnSem L) {V : Type}
    (obs : S.Den → List V → Set (Behaviour V)) {R : Behaviour V → Behaviour V → Prop}
    (hR : ∀ β, R β β) (Γ : Ctx L) (B B' : PBodies Γ) (h : Sol S B ∅ = Sol S B' ∅) :
    Equiv.ModuleEquiv (entryPoints S obs) R ⟨Γ, B⟩ ⟨Γ, B'⟩ := by
  have hbeh : ∀ a vs, (entryPoints S obs).beh ⟨Γ, B⟩ a vs = (entryPoints S obs).beh ⟨Γ, B'⟩ a vs :=
    fun a vs => by simp only [entryPoints, h]
  refine ⟨fun a vs _ β hβ => ⟨β, ?_, hR β⟩, fun a vs _ β hβ => ⟨β, ?_, hR β⟩⟩
  · rw [← hbeh]
    exact hβ
  · rw [hbeh]
    exact hβ

/-- **Replacement** into module equivalence. -/
theorem moduleEquiv_replace (S : FnSem L) {V : Type}
    (obs : S.Den → List V → Set (Behaviour V)) {R : Behaviour V → Behaviour V → Prop}
    (hR : ∀ β, R β β) {T : Sig L} (B : PBodies T.toCtx) (b b' : L.Body T.n)
    (h : SemSat S ((PMod.ofBodies B).den S) (.eq b b')) :
    Equiv.ModuleEquiv (entryPoints S obs) R (Closed.replace T B b) (Closed.replace T B b') :=
  moduleEquiv_of_sol_eq S obs hR T.toCtx _ _ (sol_replace_of_sat S B b b' h)

/-- **Replacement** as validity in the existing entry logic `Entry.entryEquiv`. -/
theorem entry_valid_replace (S : FnSem L) {V : Type}
    (obs : S.Den → List V → Set (Behaviour V)) {R : Behaviour V → Behaviour V → Prop}
    (hR : ∀ β, R β β) {T : Sig L} (B : PBodies T.toCtx) (b b' : L.Body T.n)
    (h : SemSat S ((PMod.ofBodies B).den S) (.eq b b')) (X : Set ℕ) :
    (Entry.entryEquiv (entryPoints S obs) R).Valid
      ((Entry.entryEquiv (entryPoints S obs) R).leSen X
        (Closed.replace T B b) (Closed.replace T B b')) := by
  have hm := moduleEquiv_replace S obs hR B b b' h
  exact (ObsSemantics.valid_leSen_iff _ _ _ _).2
    ⟨fun x vs hok => hm.1 x.1 vs hok, fun x vs hok => hm.2 x.1 vs hok⟩

end Silmaril.Wasm.FnInst.Models
