module

public import Silmaril.Wasm.Institution.Components.Defs
public import Silmaril.Wasm.Institution.Games.Thms

@[expose] public section

/-!
# Modules versus components: proofs

Validity in the component logics is refinement of `denU`; component passes are uniformly valid
families; fusion and dead-export elimination give valid equations, which are borrowed into the
component game logic. Summary in `Silmaril.Wasm.Institution.Components.Thms`.
-/

namespace Silmaril.Wasm.Institution.Components

open CategoryTheory ObsSemantics Silmaril.Wasm.Institution.Games
open Silmaril.Wasm.Component

/-- `ιU'` is a left inverse of `ιU`. -/
theorem restrict_ιU_ιU' (σ : Silmaril.Games.Strategy sigU sigU) : (top σ).restrict ιU' = σ := by
  have h := Silmaril.Games.Strategy.restrict_comp (X := sigU) σ ιU' ιU
  exact h.symm.trans (Silmaril.Games.Strategy.restrict_id σ)

/-- Passing to the top component interface reflects and preserves refinement. -/
theorem top_le_iff {σ τ : Silmaril.Games.Strategy sigU sigU} : top σ ≤ top τ ↔ σ ≤ τ := by
  constructor
  · intro h
    have := Silmaril.Games.Strategy.restrict_mono h ιU'
    rwa [restrict_ιU_ιU', restrict_ιU_ιU'] at this
  · intro h
    exact Silmaril.Games.Strategy.restrict_mono h ιU

/-- In a component logic, validity at the top interface is refinement over `sigU`. -/
theorem valid_top_iff {P : Type} (d : P → Silmaril.Games.Strategy sigU sigU) (p q : P) :
    (compIfaces.stratSem sigU P fun x => top (d x)).Valid
        ((compIfaces.stratSem sigU P fun x => top (d x)).leSen compIfaces.top p q) ↔
      d p ≤ d q :=
  (Games.valid_top_iff compIfaces sigU _ p q).trans top_le_iff

/-- Equal denotations give a valid equation at every interface. -/
theorem valid_eqSen_of_eq {P : Type} (s : P → Silmaril.Games.Strategy sigU (compSig Set.univ))
    {p q : P} (h : s p = s q) (X : Set Nat) :
    (compIfaces.stratSem sigU P s).Valid ((compIfaces.stratSem sigU P s).eqSen X p q) := by
  refine ((compIfaces.stratSem sigU P s).valid_eqSen_iff X p q).2 ?_
  have e : compIfaces.res sigU (compIfaces.toTop X) (s p) =
      compIfaces.res sigU (compIfaces.toTop X) (s q) := congrArg _ h
  exact ⟨e.le, e.ge⟩

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- **Validity in the component logic is refinement of denotations.** -/
theorem valid_comp_iff (c c' : Comp M) :
    (compSem C).Valid ((compSem C).leSen compIfaces.top c' c) ↔ c'.denU C ≤ c.denU C :=
  valid_top_iff (fun c => c.denU C) c' c

theorem valid_program_iff (p p' : Program M) :
    (programSem C).Valid ((programSem C).leSen compIfaces.top p' p) ↔ p'.denU C ≤ p.denU C :=
  valid_top_iff (fun p => p.denU C) p' p

theorem valid_linked_iff (l l' : Linked M) :
    (linkedSem C).Valid ((linkedSem C).leSen compIfaces.top l' l) ↔ l'.denU C ≤ l.denU C :=
  valid_top_iff (fun l => l.denU C) l' l

open Silmaril.Compile.PassAPI in
/-- **A verified component pass is exactly a size-preserving transformation `f` such that
every sentence `f c ⊑ c` is valid in the component logic.** -/
def passEquivValid :
    Pass (contract C) ≃
      {f : Comp M → Comp M // ∀ c, (f c).imports.length = c.imports.length ∧
        (f c).exports.length = c.exports.length ∧
        (compSem C).Valid ((compSem C).leSen compIfaces.top (f c) c)} where
  toFun p := ⟨p.run, fun c => let h := p.sound (x := c) trivial
    ⟨h.1, h.2.1, (valid_comp_iff C _ _).2 h.2.2⟩⟩
  invFun f := ⟨f.1, fun _ => trivial, fun {c} _ =>
    ⟨(f.2 c).1, (f.2 c).2.1, (valid_comp_iff C _ _).1 (f.2 c).2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Silmaril.Compile.PassAPI in
/-- The same for programs. -/
def programPassEquivValid :
    Pass (programIR C).contract ≃
      {f : Program M → Program M // ∀ p, (f p).comp.imports.length = p.comp.imports.length ∧
        (f p).width = p.width ∧
        (programSem C).Valid ((programSem C).leSen compIfaces.top (f p) p)} where
  toFun q := ⟨q.run, fun p => let h := q.sound (x := p) trivial
    ⟨h.1, h.2.1, (valid_program_iff C _ _).2 h.2.2⟩⟩
  invFun f := ⟨f.1, fun _ => trivial, fun {p} _ =>
    ⟨(f.2 p).1, (f.2 p).2.1, (valid_program_iff C _ _).1 (f.2 p).2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Adapter fusion** gives valid equations `fuse c ≐ c` at every interface. -/
theorem valid_fuse (c : Comp M) (X : Set Nat) :
    (compSem C).Valid ((compSem C).eqSen X (fuseComponent c) c) :=
  valid_eqSen_of_eq (fun c : Comp M => top (c.denU C)) (congrArg top (denU_fuseComponent C c)) X

/-- **Dead-export elimination** gives valid equations `deadExports p ≐ p` at every
interface. -/
theorem valid_deadExports (p : Program M) (X : Set Nat) :
    (programSem C).Valid ((programSem C).eqSen X (deadExports p) p) :=
  valid_eqSen_of_eq (fun p : Program M => top (p.denU C)) (congrArg top (denU_deadExports C p)) X

/-- Flattening gives valid equations (conditional on `PairLaws`). -/
theorem valid_flatten (L : PairLaws) (c : Comp M) (X : Set Nat) :
    (compSem C).Valid ((compSem C).eqSen X (flatten c).toComponent c) := by
  refine valid_eqSen_of_eq (fun c : Comp M => top (c.denU C)) ?_ X
  show top ((flatten c).toComponent.denU C) = top (c.denU C)
  rw [Linked.denU_toComponent, denU_flatten L]

/-- **Borrowed into the component game logic**: the fusion equation holds between the
strategies of the two components. -/
theorem valid_game_fuse (c : Comp M) (X : Set Nat) :
    (compGameSem).Valid ((compToGame C).sen ((compSem C).eqSen X (fuseComponent c) c)) :=
  ((compToGame C).valid_iff (stratT_surjective compIfaces sigU _ _) _).1 (valid_fuse C c X)

end Silmaril.Wasm.Institution.Components
