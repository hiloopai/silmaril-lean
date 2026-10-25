module

public import Silmaril.Wasm.Execution.Runtime

/-! # Mapping scalar runtime carriers across source languages -/

@[expose] public section
namespace Silmaril.Wasm.Execution.Runtime

@[simp] theorem AdminInstr.mapList_eq_map {I J : Type*} (f : I → J) (xs : List (AdminInstr I)) :
    mapList f xs = xs.map (map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mapList, List.map_cons, ih]

@[simp] theorem AdminInstr.mapList_append {I J : Type*} (f : I → J)
    (xs ys : List (AdminInstr I)) : mapList f (xs ++ ys) = mapList f xs ++ mapList f ys := by
  simp only [mapList_eq_map, List.map_append]

@[simp] theorem Store.mapCode_funcs_getElem? {A B H : Type*} (f : A → B)
    (s : Store A H) (i : Nat) :
    (s.mapCode f).funcs[i]? = s.funcs[i]?.map (FuncInst.mapCode f) := by
  simp [mapCode]

def HostOutcome.mapCode {A B H : Type*} (f : A → B) : HostOutcome A H → HostOutcome B H
  | .returned s r => .returned (s.mapCode f) r
  | .diverged => .diverged

/-- Pointwise transport of host outcomes along a source-code map. -/
def HostSemantics.Compatible {A B H : Type*} (f : A → B)
    (source : HostSemantics A H) (target : HostSemantics B H) : Prop :=
  ∀ h s args out, source h s args out →
    target h (s.mapCode f) args (HostOutcome.mapCode f out)

/-- A canonical host relation on the image of a source-code embedding. -/
def HostSemantics.mapCode {A B H : Type*} (f : A → B) (source : HostSemantics A H) :
    HostSemantics B H :=
  fun h s args out => ∃ before result,
    s = before.mapCode f ∧ out = HostOutcome.mapCode f result ∧ source h before args result

theorem HostSemantics.compatible_mapCode {A B H : Type*} (f : A → B)
    (source : HostSemantics A H) : Compatible f source (source.mapCode f) := by
  intro h s args out proof
  exact ⟨s, out, rfl, rfl, proof⟩

end Silmaril.Wasm.Execution.Runtime
