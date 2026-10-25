module

public import Silmaril.Logic.Metamath.Grammar.Derivation

@[expose] public section

/-!
# Checking well-formedness of tree assertions

`TAssertion.checkWF` decides the conditions of `TAssertion.WellFormed` with
the sort checker `Grammar.check`, reading the sort of each variable from its
first floating hypothesis. It is sound (`TAssertion.WellFormed.of_checkWF`),
so concrete assertions are shown well formed by evaluation.
-/

namespace Silmaril.Logic.Metamath.Grammar

universe u

variable {C V L : Type u} [DecidableEq C] [DecidableEq V] {G : Grammar L C V}

namespace TAssertion

/-- The sort of `v` given by its first floating hypothesis. -/
def sortOf (A : TAssertion L C V) (v : V) : Option C :=
  (A.floats.find? fun p => p.2 == v).map Prod.fst

omit [DecidableEq C] in
theorem ctx_of_sortOf {A : TAssertion L C V} {v : V} {s : C} (h : A.sortOf v = some s) :
    A.ctx v s := by
  simp only [sortOf, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hv : p.2 = v := by simpa using List.find?_some hp
  rw [← mem_floats, ← hv]
  exact List.mem_of_find?_eq_some hp

variable (G)

/-- Check that a tree expression is at a provable typecode and its tree has
the corresponding syntax sort. -/
def checkWellTyped (A : TAssertion L C V) (e : TExpr L C V) : Bool :=
  match G.prov e.tc with
  | some s => G.check A.sortOf e.tree s
  | none => false

variable {G} in
theorem wellTyped_of_check {A : TAssertion L C V} {e : TExpr L C V}
    (h : checkWellTyped G A e = true) : e.WellTyped G A.ctx := by
  unfold checkWellTyped at h
  split at h
  · rename_i s hs
    exact ⟨s, hs, ((check_iff _ _).1 h).mono fun _ _ => ctx_of_sortOf⟩
  · exact absurd h Bool.false_ne_true

variable [DecidablePred (· ∈ G.sorts)]

/-- Decide the conditions of `WellFormed`. -/
def checkWF (A : TAssertion L C V) : Bool :=
  decide (A.floats.map Prod.snd).Nodup &&
  A.floats.all (fun p => decide (p.1 ∈ G.sorts)) &&
  A.essentials.all (checkWellTyped G A) &&
  checkWellTyped G A A.concl &&
  A.dv.all fun p => p.1 != p.2 && (A.sortOf p.1).isSome && (A.sortOf p.2).isSome

variable {G}

/-- The check is sound. -/
theorem WellFormed.of_checkWF {A : TAssertion L C V} (h : checkWF G A = true) :
    A.WellFormed G := by
  simp only [checkWF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hnd, hsort⟩, hess⟩, hconcl⟩, hdv⟩ := h
  refine ⟨hnd, fun v s hv => ?_, fun e he => wellTyped_of_check (hess e he),
    wellTyped_of_check hconcl, fun x y hxy => ?_, fun x y hxy => ?_⟩
  · simpa using hsort _ (mem_floats.2 hv)
  · have := hdv _ hxy
    simp only [bne_iff_ne, ne_eq] at this
    exact this.1.1
  · have := hdv _ hxy
    simp only [Option.isSome_iff_exists] at this
    obtain ⟨⟨-, s, hs⟩, t, ht⟩ := this
    exact ⟨⟨s, ctx_of_sortOf hs⟩, ⟨t, ctx_of_sortOf ht⟩⟩

end TAssertion

end Silmaril.Logic.Metamath.Grammar
