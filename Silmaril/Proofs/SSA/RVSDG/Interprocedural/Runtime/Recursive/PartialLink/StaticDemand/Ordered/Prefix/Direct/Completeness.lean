module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Proofs

open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {scope : Scope m} {actions : Actions m σ}
variable {imports entry outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
variable {inputsL inputsR : Tuple m.Val imports}
variable {checked : scope.Checked actions} {routes : Routes inputsL inputsR scope}
variable {source : ScopeBoundary imports entry scope.past past}

private theorem collect_complete {n : Nat} {P : Fin n → Prop} (check : (i : Fin n) → Option (PLift (P i)))
    (ready : ∀ i, (check i).isSome = true) : (collectArms n check).isSome = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have head := ready 0
    have tail := ih (fun i => check i.succ) (fun i => ready i.succ)
    simp [collectArms, Option.isSome_bind, head, tail]

private theorem site_complete {i : Fin scope.table.members.length} {target : Origin entry past (scope.table.at i).fn.port}
    {witnesses : Wires entry past (scope.table.at i).captures}
    (site : TrackedSite checked routes source i target witnesses) :
    (resolveSite checked routes source rfl i target witnesses).isSome = true := by
  obtain ⟨sources, route, projected, picked, same, left, right⟩ := site
  simp only [resolveSite, resolveSiteWith]
  split
  · simp_all
  · rename_i actual found
    have equal : actual = sources := Option.some.inj (found.symm.trans projected)
    subst actual
    simp [routeSources, picked, same, left, right]

private theorem bind_complete {A B : Type _} {head : Option A} {tail : A → Option B}
    (first : head.isSome = true) (later : ∀ a, (tail a).isSome = true) :
    (head.bind tail).isSome = true := by
  obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.mp first
  exact later a

theorem tracked_complete {code : Code Op entry past sigs outs true (some scope.table)}
    (tracked : Tracked checked routes source code) :
    (synthesizeAt checked routes source code rfl).isSome = true := by
  induction tracked with
  | ret => rfl
  | primitive _ ih => exact bind_complete ih (fun _ => rfl)
  | call site _ suffix =>
    exact bind_complete (site_complete site) (fun _ => bind_complete suffix (fun _ => rfl))
  | gamma _ _ arms suffix =>
    exact bind_complete (collect_complete _ arms) (fun _ => bind_complete suffix (fun _ => rfl))
  | theta _ _ body suffix =>
    exact bind_complete body (fun _ => bind_complete suffix (fun _ => rfl))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Proofs
