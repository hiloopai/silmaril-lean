module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Rules
public import Silmaril.Proofs.Wasm.FnInst.Ground.Refute
public import Silmaril.Wasm.Binaryen.CodeSimRank.Thms

@[expose] public section

/-! # Grounding: equal runs of straight-line pairs give export equivalence in Wasm Core

Header of `Silmaril.Proofs.Wasm.FnInst.Ground.{Run,Steps,Inv,Sim,Rules,Refute}`. The bridge from the
straight-line semantics of segments (`Silmaril.Wasm.FnInst.Ground.Defs`) to silmaril-lean's
small-step Wasm Core semantics:

* `run_steps` (adequacy): a run of the interpreter `run` is a run of `Execution.Core.Step`;
  `step_inv`: at a stack-only instruction or `local.get` it is the only one;
* `gBaseSim` (**the bridge**): for every pair `Good a b` (equal runs `RunRef a b`, left side
  stack-only and not all constants, or one `local.get` then stack-only code that never gets
  stuck; right side any code of the fragment), silmaril's code-simulation obligation
  `BaseSim P closedHost F GBI GB gCodeRank` holds, at every numerical profile `P`;
* `exportEquiv_of_good` (**the generic transfer**): modules whose function bodies differ by
  good pairs, at any positions inside any blocks, loops, `if`s and `try_table`s
  (`ModuleBodiesRel GBI`), and that both validate, are export equivalent under the closed host
  at every deterministic profile (silmaril's closure through
  `CodeSimRank.exportEquiv_of_baseSim_rank`);
* rule lemmas (`good_dropGet`, `good_rseSet`, `good_rseTee`, `good_neutral`, `good_eqz3`,
  `good_fold`, `good_constDrop`), one `RunRef` computation each.

What the bridge does not cover, and why (`docs/projects/logic-inst.md`, Grounding): left
sides that write locals or read more than one local. `BaseSim` must hold in every frame,
and its runtime pairs cannot mention the frame; a left step that writes a local must be
matched by a right run reaching the same frame. `not_baseSim_twoSets` refutes the
unrestricted bridge: `i32.const 1; local.set 0; i32.const 2; local.set 0` and
`i32.const 2; local.set 0` have equal runs (`runRef_twoSets`) but are a `BaseSim` pair for no
runtime relation and no rank.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

/-- A good pair, lowered, is a source base pair. -/
theorem gbi_of_good {a b : List GInstr} (h : Good a b) : GBI (lower a) (lower b) :=
  ⟨a, b, h, rfl, rfl⟩

/-- The body relation is monotone in the source base relation. -/
theorem bodiesRel_mono {BI BI' : List Instr → List Instr → Prop}
    (h : ∀ x y, BI x y → BI' x y) {m m' : Module} (hr : ModuleBodiesRel BI m m') :
    ModuleBodiesRel BI' m m' :=
  ⟨hr.other, hr.funcs.imp fun _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, GuardSim.InstrsRel.mono h h₃⟩⟩

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool}

/-- **The generic transfer**: bodies differing by good pairs give export equivalence. -/
theorem exportEquiv_of_good {m m' : Module} (hrel : ModuleBodiesRel GBI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) m m' :=
  Silmaril.Wasm.Binaryen.CodeSimRank.exportEquiv_of_baseSim_rank gBaseSim g_noRedex hrel hm hm'

/-- The generic transfer for a family of rules whose pairs are all good. -/
theorem exportEquiv_of_rules {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → GBI x y) {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) m m' :=
  exportEquiv_of_good (bodiesRel_mono hBI hrel) hm hm'

/-- One rule: the pair itself as a source relation. -/
def Pair (a b : List GInstr) (x y : List Instr) : Prop := x = lower a ∧ y = lower b

/-- The generic transfer for one good pair. -/
theorem exportEquiv_of_pair {a b : List GInstr} (h : Good a b) {m m' : Module}
    (hrel : ModuleBodiesRel (Pair a b) m m') (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) m m' :=
  exportEquiv_of_rules (fun _ _ ⟨hx, hy⟩ => hx ▸ hy ▸ gbi_of_good h) hrel hm hm'

end Silmaril.Wasm.FnInst.Ground
