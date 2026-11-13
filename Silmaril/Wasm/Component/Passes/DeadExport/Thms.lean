module

public import Silmaril.Wasm.Component.Passes.DeadExport.Defs
public import Silmaril.Wasm.Component.Contract.Defs

/-!
# Dead export elimination: soundness

`denU_deadExports`: the program after dead export elimination has the same
denotation (equality of strategies, same interface sizes), for every core
semantics: restricting the export handler to the observed exports
(`selectH`) is the handler of the kept exports (`ofHandler_comp`). Hence
`deadExportPass C : Pass (programIR C).contract`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Compile.PassAPI

variable {M : Type} [CoreModule M]

theorem selectH_exportsH (e : Nat) (xs : List Export) (obs : List Nat) :
    (exportsH e xs).comp (selectH obs) =
      exportsH e (obs.map fun j => xs[j]?.getD Export.trap) := by
  funext q
  simp only [Handler.comp, selectH]
  conv => rhs; simp only [exportsH, implsH, List.map_map, List.getElem?_map]
  cases obs[q.1]? with
  | none => rfl
  | some j =>
    show ((implsH e (xs.map Export.impl)) (j, q.2)).bind (fun n => (Prog.pure n).interp _) = _
    simp only [Prog.interp_pure, Prog.bind_pure, implsH, List.getElem?_map, Option.map_some]
    rcases h : xs[j]? with _ | x <;>
      first | simp [h, Function.comp, Export.trap, Impl.prog, runChain, Target.prog]

theorem denU_deadExports (C : CoreSem M) (p : Program M) :
    (deadExports p).denU C = p.denU C := by
  obtain ⟨⟨I, ns, xs⟩, obs⟩ := p
  cases obs with
  | none => rfl
  | some obs =>
    simp only [deadExports, Program.denU, Comp.denU]
    rw [Strategy.comp_assoc, ← Strategy.ofHandler_comp, selectH_exportsH]

omit [CoreModule M] in
theorem width_deadExports (p : Program M) : (deadExports p).width = p.width := by
  obtain ⟨⟨I, ns, xs⟩, obs⟩ := p
  cases obs <;> simp [deadExports, Program.width]

omit [CoreModule M] in
theorem imports_deadExports (p : Program M) :
    (deadExports p).comp.imports = p.comp.imports := by
  obtain ⟨⟨I, ns, xs⟩, obs⟩ := p
  cases obs <;> rfl

/-- The dead export elimination pass. -/
def deadExportPass (C : CoreSem M) : Pass (programIR C).contract where
  run := deadExports
  inv_run _ := trivial
  sound {p} _ := ⟨congrArg List.length (imports_deadExports p), width_deadExports p,
    (denU_deadExports C p).le⟩

end Silmaril.Wasm.Component
