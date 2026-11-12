module

public import Silmaril.Wasm.SpecTec.Sim.Defs
public import Silmaril.Wasm.SpecTec.Sim.Control.Defs
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Defs
public import Silmaril.Wasm.SpecTec.Sim.State.Defs
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Defs
public import Silmaril.Wasm.SpecTec.Sim.Exn.Defs

/-!
# SpecTec ↔ Core 3.0: the covered fragment of the whole-step simulation

`Task.wholeStep` (`Sim/Defs.lean`) is not proved. What the families prove is assembled here into
a forward simulation for an explicit **fragment** of Core's configurations, under an explicit
bundle of **undischarged interface assumptions**.

* `Instr.Uncovered` lists the source instructions whose steps the assembly does not simulate, and
  `Admin.Uncovered` adds the administrative `RETURN_CALL_REF dt`. Each entry is listed with its
  reason in `docs/projects/spectec/README.md` ("Whole-step assembly").
* `CoveredCode l` says that no instruction of the *active* code `l` is uncovered: the
  administrative sequence itself and, recursively, the bodies of its labels, handlers and frames.
  Instruction sequences that are not yet active (block bodies, label continuations, function
  bodies in the store) are not constrained, since a single step never reduces inside them.
* `Assumptions B hn host` collects the families' hypothesis structures; each is a fact about the
  encoding or about what SpecTec's auxiliary functions compute on encoded values (see the family
  sections of the doc). Its typing fields are proved by the typing track (`Typing.assumptions_of`,
  up to block types). Family V's float interfaces are not among them: `Vec.FloatTyping` holds in
  every `simEnv B` and `Vec.FloatAgree (simEnv B) P` follows from `Floats.FloatB P B`, which the
  forward assembly takes as a separate hypothesis (it depends on the profile). `Vec.VecTyping` and
  `Vec.VecAgree` are still open, which is why the SIMD operators are outside the fragment.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- The source instructions outside the forward fragment:
* every SIMD operator except `v128.const` (family V's results assume `VecTyping` and `VecAgree`,
  which are not discharged); the scalar float operators and the conversions are covered since the
  float track (`Floats.floatTyping_simEnv`, `Floats.floatAgree_simEnv`);
* the memory instructions other than `data.drop`, and the table instructions other than
  `table.get`, `table.set` and `elem.drop` (family M covered only some of their rules; the grow
  instructions are nondeterministic and only their failing rules are proved);
* the GC aggregate instructions (family R proved 24 of 42 `AggregateStep` constructors, none of
  them at `simEnv B`, and no instruction completely);
* `return_call_ref` (Core's `returnCallRefFrameAddr` resolves the annotation with
  `Admin.retToCallIn`, so `Forward.returnCallRefFrameAddr` is false as stated:
  `adminToV_retToCallIn_ne`). -/
def Instr.Uncovered : Instr → Bool
  | .vecUnOp _ | .vecBinOp _ | .vecTernOp _ | .vecTestOp _ | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
  | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
  | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => true
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. | .vecLoad .. | .vecLoadLane ..
  | .vecStore .. | .vecStoreLane .. | .memorySize _ | .memoryGrow _ | .memoryFill _
  | .memoryCopy .. | .memoryInit .. => true
  | .tableSize _ | .tableGrow _ | .tableFill _ | .tableCopy .. | .tableInit .. => true
  | .structNew _ | .structNewDefault _ | .structGet .. | .structSet .. | .arrayNew _
  | .arrayNewDefault _ | .arrayNewFixed .. | .arrayNewData .. | .arrayNewElem .. | .arrayGet ..
  | .arraySet _ | .arrayLen | .arrayFill _ | .arrayCopy .. | .arrayInitData .. | .arrayInitElem ..
    => true
  | .returnCallRef _ => true
  | _ => false

/-- The administrative instructions outside the forward fragment: an uncovered source
instruction, and `RETURN_CALL_REF dt` (see `Instr.Uncovered`). -/
def Admin.Uncovered : Admin → Bool
  | .plain i => Instr.Uncovered i
  | .returnCallRefType _ => true
  | _ => false

/-- The active code nested in an administrative instruction: the body of a label, handler or
frame. -/
def Admin.inner : Admin → List Admin
  | .label _ _ body | .handler _ _ body | .frame _ _ body => body
  | _ => []

/-- **The active code holds no uncovered instruction**, at any depth of labels, handlers and
frames. -/
inductive CoveredCode : List Admin → Prop where
  | nil : CoveredCode []
  | cons {a : Admin} {l : List Admin} (ha : Admin.Uncovered a = false)
      (hin : CoveredCode (Admin.inner a)) (hl : CoveredCode l) : CoveredCode (a :: l)

/-- A configuration in the forward fragment. -/
def Covered {H : Type} (c : Config H) : Prop := CoveredCode c.code

open Silmaril.Wasm.Execution.Core (HostSemantics) in
/-- **The families' undischarged interface assumptions**, in one place. Each field is a
hypothesis structure of one family (named in its docstring); the doc lists what each says and
who should discharge it. Nothing here is proved, and nothing proves that the fields can hold
together for one `B`; the two family structures already refuted (`Vec.FloatTyping`,
`Vec.VecTyping`) are deliberately absent. -/
structure Assumptions {H : Type} (B : Builtins) (hn : H → String) (host : HostSemantics H) :
    Prop where
  /-- Base: the encoding's typing facts (family E). -/
  typing : TypingFacts (simEnv B) hn
  /-- Family N: `B` interprets the integer primitives as `IntNumeric.intCall`. -/
  intB : IntNumeric.IntB B
  /-- Family M: typing of indices, address types, numerals and references. -/
  state : State.StateTyping (simEnv B)
  /-- Family R: typing of references, values and immediates. -/
  rTyping : RefsGC.RTyping (simEnv B)
  /-- Family R: `$wrap__` and `$extend__`. -/
  rFuns : RefsGC.RFuns (simEnv B)
  /-- Family R: the store accessors the reference rules call. -/
  rStore : RefsGC.RStoreFuns (simEnv B)
  /-- Family R: SpecTec's `Ref_ok` is Core's `RefOk`. -/
  refOk : RefsGC.RefOkBridge (simEnv B)
  /-- Family C: typing facts and `instr` inversions. -/
  ctrlTyping : CtrlTyping (simEnv B)
  /-- Family C: `$funcinst`, `$moduleinst`, `$blocktype_` on encoded states. -/
  ctrlState : CtrlState (simEnv B) hn
  /-- Family C: `Expand`, value-type typing and `$default_`. -/
  ctrlCall : CtrlCall (simEnv B)
  /-- Family C: `$hostcall`, `$lift_result` and result/funcinst typing. -/
  ctrlHost : CtrlHost (simEnv B) hn host
  /-- Family X: typing of addresses, indices, block types and exception instances. -/
  exnTyping : Exn.Typing (simEnv B)
  /-- Family X: the exception store helpers. -/
  exnHelpers : Exn.Helpers (simEnv B) hn

end Silmaril.Wasm.SpecTec.Sim.Whole
