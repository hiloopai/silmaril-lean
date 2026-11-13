module

public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Defs
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Defs

/-!
# The SpecTec specification institution and the Wasm atlas, at wasm-2.0: definitions

The wasm-3.0 semi-comorphism (`Wasm30.toModel`) relates the Core step chart to the step chart of
the backend canonical model of the wasm-3.0 script. This header sets up the same picture at
wasm-2.0, with V2 (`Silmaril.Wasm.V2.Execution.Step`, the model `v20own`) in place of Core and the
wasm-2.0 script `Scripts.Wasm20.fixed` (`Sim20.simEnv20 B`) in place of the 3.0 script.

* `v2Obs`, `v2Chart`: the V2 step chart, observing the image (`Sim20.configV`) of each V2
  successor. It is `Atlas.SpecTec.coreChart` with V2's step relation.
* `stepModel20 B`: the backend canonical model of the wasm-2.0 script with primitives `B`,
  `canonB (simEnv20 B) (otherwiseB (simEnv20 B))`. Its step facts are
  `Round6.Reading.SStepB (simEnv20 B)`, the reading of `Sim20.Task.wholeStepBwdW`.
* `DomW`: the domain of `Task.wholeStepBwdW` (`Sim20.Whole.GoodW` unfolded: conversions V2
  defines, no vector operator, named resources exist).
* `storeOp20`, `NoStoreL`, `DomS`: the **scalar fragment**, `DomW` without table, store,
  `memory.size`, `memory.grow`, bulk-memory or drop instructions, at any depth. On it the
  backward half is proved unconditionally (`Wasm20.Thms`).
* `progress`, `stuckSen`, `nopCfg`: the sentences and the point that refute the forward half.

Unlike wasm-3.0 there is no two-sided statement: the 2.0 script has no `Step/ctxt-instrs` rule, so
`nop nop` is stuck in every model `stepModel20 B` while V2 reduces it
(`Sim20.Whole.not_wholeStepValid`). What survives is one direction for each sentence polarity.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Wasm20

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim20

variable {H : Type}

/-- **V2's observations** at `c`: the images of its successors. -/
def v2Obs (P : Profile) (host : HostSemantics H) (hn : H → String) (c : Config H) (_ : Unit) :
    Set Value :=
  {w | ∃ c', Step P host c c' ∧ w = Sim20.configV hn c'}

/-- **The V2 step chart** on the fragment `D`. -/
def v2Chart (P : Profile) (host : HostSemantics H) (hn : H → String) (D : Config H → Prop) :
    Chart :=
  BChart (Config H) Unit Value D (v2Obs P host hn)

/-- **The backend canonical model** of the wasm-2.0 script with primitives `B`. -/
noncomputable def stepModel20 (B : Builtins) : Model (sigOf (simEnv20 B)) :=
  canonB (simEnv20 B) (Round6.Reading.otherwiseB (simEnv20 B))

/-- **The domain of `Sim20.Task.wholeStepBwdW`**: conversions V2 defines, no vector operator, and
the named resources exist. It is `Sim20.Whole.GoodW` unfolded. -/
def DomW (c : Config H) : Prop :=
  CvtOkL c.code ∧ NoVecL c.code ∧ ResOkL c.store c.frame c.code

/-- The instructions whose `Step_read` or `Step` rules are not discharged by `Sim20.Whole`: table
instructions, `elem.drop`, scalar and vector stores, `memory.size`, `memory.grow`, the bulk-memory
instructions and `data.drop`. Loads are not among them: their rules never fire at the spec's
scalar builtins (`Sim20.Whole.inertRead20`). -/
def storeOp20 : V2.Instr → Bool
  | .tableGet .. | .tableSet .. | .tableSize .. | .tableGrow .. | .tableFill .. | .tableCopy ..
  | .tableInit .. | .elemDrop .. | .intStore .. | .floatStore .. | .vecStore .. | .vecStoreLane ..
  | .memorySize | .memoryGrow | .memoryFill | .memoryCopy | .memoryInit .. | .dataDrop .. => true
  | _ => false

mutual
/-- No active `storeOp20` instruction in an administrative instruction. -/
def NoStoreA : Admin → Prop
  | .plain i => storeOp20 i = false
  | .label _ _ b => NoStoreL b
  | .frame _ _ b => NoStoreL b
  | _ => True

/-- No active `storeOp20` instruction in a code sequence, at any depth of labels and frames. -/
def NoStoreL : List Admin → Prop
  | [] => True
  | a :: l => NoStoreA a ∧ NoStoreL l
end

/-- **The scalar fragment**: `DomW`, and no `storeOp20` instruction. -/
def DomS (c : Config H) : Prop := DomW c ∧ NoStoreL c.code

/-- The progress sentence: some successor exists. -/
def progress : BSen Unit Value := .may () fun _ => True

/-- The stuckness sentence: no successor exists. -/
def stuckSen : BSen Unit Value := .always () fun _ => False

/-- `nop nop` in the empty store and frame. -/
def nopCfg : Config H := ⟨{}, {}, [.plain .nop, .plain .nop]⟩

end Silmaril.Wasm.SpecTec.Institution.Wasm20
