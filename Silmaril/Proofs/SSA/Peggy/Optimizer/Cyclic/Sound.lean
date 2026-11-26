module

public import Silmaril.SSA.Peggy.Optimizer.Cyclic.Defs
import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy
open Silmaril.SSA.Peggy.Optimizer.Cyclic
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n : Nat}
variable {g : Graph P params results (n + 1) 1} {site : Fin (n + 1)}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}

private theorem leaf_noTheta {L : Type} {out : Ty Data}
    (row : Node P params L g.sort out) (empty : row.inputs = []) : row.label.thetaLoop = none := by
  obtain ⟨ins, label, args⟩ := row
  change ins = [] at empty
  subst ins
  cases label <;> rfl

private theorem leaf_invariant {v : Fin (n + 1)} {loop : Fin 1}
    (empty : (g.node v).inputs = []) : Rules.InvariantAt g loop v := by
  apply Rules.invariantAt_largest (fun i => (g.node i).inputs = []) _ _ empty
  · intro a leaf
    rw [leaf_noTheta (g.node a) leaf]
    intro impossible
    cases impossible
  · rintro a b kind ⟨⟨slot, _, _⟩, _⟩ leaf
    have bound := slot.isLt
    simp [leaf] at bound

theorem rule_holds (found : Match g site) (wf : WellFounded g.Demand) :
    found.rule.Holds (g.denote m env wf) := by
  intro guards
  have feedback : EPEG.StreamEq (g.denote m env wf) found.feedback.id site :=
    guards ⟨found.feedback.id, site, congrArg g.sort found.self⟩ List.mem_cons_self
  have equal := (Rules.streamEq_iff_vertex found.feedback (Ref.ofId g.sort site)).mpr feedback
  have invariant := Rules.denote_invariant (m := m) (env := env) wf (r := found.init)
    (loop := found.loop) (leaf_invariant found.leaf)
  exact (Rules.streamEq_iff_vertex (Ref.ofId g.sort site) found.init).mp
    (Rules.theta_self (g.denote_solves m env wf) found.shape equal invariant)

theorem classes_valid (found : Match g site) (wf : WellFounded g.Demand) :
    found.classes.Valid (g.denote m env wf) := by
  apply EPEG.Saturation.run_denote_sound 1 [found.obligation] wf EPEG.Classes.discrete_valid
  intro reason member
  have eq : reason = found.obligation := List.mem_singleton.mp member
  subst reason
  exact rule_holds found wf

end Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic
