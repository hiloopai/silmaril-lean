module

public import Silmaril.SSA.Peggy.Optimizer.Cyclic.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.Optimizer.Cyclic

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results ins : List (Ty Data)} {out : Ty Data} {n : Nat}
variable {g : Graph P params results n 1}

private theorem hasEdge {a b : Fin n} {ks : List (EdgeKind (Fin 1))}
    (walk : Walk g.Edge a ks b) {kind : EdgeKind (Fin 1)} (mem : kind ∈ ks) :
    ∃ x y, g.Edge x kind y := by
  induction walk with
  | nil => exact (List.not_mem_nil mem).elim
  | cons edge _ ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨_, _, edge⟩
    · exact ih tail

private theorem noObserver (label : Label P params (Fin 1) ins out)
    (ok : supported label = true) (slot : Fin ins.length) (loop : Fin 1) :
    ¬(label.kind slot).IsObserverAt loop := by
  cases label <;> simp_all [supported, Label.kind, EdgeKind.IsObserverAt]
  split <;> simp

theorem wellFormed (admitted : Admission g) : g.WellFormed := by
  constructor
  · intro i cycle
    have eq : i = 0 := Subsingleton.elim _ _
    subst i
    obtain ⟨ks, walk, nonempty⟩ := cycle
    cases walk with
    | nil => exact nonempty rfl
    | cons step _ =>
      have bad := admitted.noParent.symm.trans step
      cases bad
  · intro a ks walk nonempty
    by_contra absent
    apply Nat.lt_irrefl (admitted.phase a)
    apply walk.strictRank nonempty admitted.phase
    rintro x y k ⟨slot, rfl, rfl⟩ mem
    exact admitted.nonfeedback x slot (fun feedback => absent ⟨_, mem, feedback⟩)
  · intro a b ks start target walk sourceLoop targetLoop
    have eq : target = start := Subsingleton.elim _ _
    subst target
    exact .inl ⟨[], .nil start⟩
  · intro a ks walk kind mem inner observer
    obtain ⟨x, y, ⟨slot, rfl, rfl⟩⟩ := hasEdge walk mem
    exact (noObserver (g.node x).label (admitted.labels x) slot inner observer).elim

end Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic
