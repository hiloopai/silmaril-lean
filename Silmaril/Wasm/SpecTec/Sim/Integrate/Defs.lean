module

public import Silmaril.Wasm.SpecTec.Sim.Whole.Defs
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms
public import Silmaril.Wasm.SpecTec.Sim.Aggregates.Thms
public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Defs
public import Silmaril.Wasm.SpecTec.Sim.BwdRead.Defs

/-!
# SpecTec ↔ Core 3.0, round 2 integration: the widened forward fragment

Round 1's `Whole.Covered` excluded every table, memory and aggregate instruction. Round 2's
memory and aggregates tracks proved forward lemmas for most of their constructors, under store
invariants Core's step does not record (`docs/projects/spectec/README.md`). This
file states the fragment those lemmas reach:

* `Instr.Open` lists the source instructions still outside it: every SIMD operator except
  `v128.const` and the bitwise ones (`v128.not`/`and`/`andnot`/`or`/`xor`/`bitselect`/`any_true`,
  round 3, `FwdSimdAgg`; the lane-wise operators need family V's `VecAgree`), every load and store
  (the value cases need a byte-encoding bridge, and the slice boundary is obstruction 2),
  `array.new_elem`, `array.new_data`, `array.init_data` (slices, obstruction 2; round 3 closed
  `struct.new_default`, `array.new_default`, `array.copy`, `array.init_elem`), and
  `return_call_ref` (obstruction 1).
* `CodeOk l`: no open instruction in the active code `l`, at any depth, and every frame in it
  names only aggregate types with unpacked fields (`Aggregates.Unpacked`).
* `StoreOk s`: tables, element and data segments and arrays have fewer than `2 ^ 32` entries,
  and memories are whole pages of fewer than `2 ^ 32` bytes. Without it the forward conjunct of
  `Task.wholeStep` is false (memory track: `memory.fill` at a full `2 ^ 32`-byte memory, `Wrap.lean`;
  aggregates track: `array.len` of an array with `2 ^ 32` or more fields).
* `Covered c`: `CodeOk c.code`, `Unpacked c.frame` and `StoreOk c.store`.
* `Extra env`: the memory and aggregates tracks' interface assumptions (`MemTyping`, `GrowFuns`,
  `InstTyping`, `AggTypes`), none of them discharged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Integrate

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation

/-- The source instructions outside the integrated forward fragment. -/
def Instr.Open : Instr → Bool
  | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
  | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
  | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => true
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. | .vecLoad .. | .vecLoadLane ..
  | .vecStore .. | .vecStoreLane .. => true
  | .arrayNewData .. | .arrayNewElem .. | .arrayInitData .. => true
  | .returnCallRef _ => true
  | _ => false

/-- The administrative instructions outside the fragment: an open source instruction, and
`RETURN_CALL_REF dt`. -/
def Admin.Open : Admin → Bool
  | .plain i => Instr.Open i
  | .returnCallRefType _ => true
  | _ => false

/-- **The active code holds no open instruction**, at any depth, and every frame in it names
only unpacked aggregate types. -/
inductive CodeOk : List Admin → Prop where
  | nil : CodeOk []
  | cons {a : Admin} {l : List Admin} (ha : Admin.Open a = false)
      (hf : ∀ n fi body, a = .frame n fi body → Aggregates.Unpacked fi)
      (hin : CodeOk (Whole.Admin.inner a)) (hl : CodeOk l) : CodeOk (a :: l)

/-- **The store invariants** the table, memory and aggregate forward lemmas need. -/
structure StoreOk {H : Type} (s : Store H) : Prop where
  /-- Tables and element segments have fewer than `2 ^ 32` entries. -/
  tables : Memory.TablesBounded s
  /-- Arrays, element and data segments have fewer than `2 ^ 32` entries. -/
  aggs : Aggregates.Bounded s
  /-- Memories are whole pages, of fewer than `2 ^ 32` bytes. -/
  mems : ∀ mi ∈ s.mems, mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0 ∧
    mi.bytes.size < 2 ^ 32

/-- A configuration in the integrated forward fragment. -/
def Covered {H : Type} (c : Config H) : Prop :=
  CodeOk c.code ∧ Aggregates.Unpacked c.frame ∧ StoreOk c.store

/-- **The memory and aggregates tracks' interface assumptions** (not discharged). -/
structure Extra (env : Env) : Prop where
  /-- Typing of table/memory types and memory immediates (family E). -/
  mem : Memory.MemTyping env
  /-- `$growtable`, `$growmem` are the images of Core's `grow?` (gap G3). -/
  grow : Memory.GrowFuns env
  /-- Grown table and memory instances are typed (family E). -/
  inst : Memory.InstTyping env
  /-- `Expand` on every composite type; storage-type, mutability and aggregate typing. -/
  agg : Aggregates.AggTypes env

open Silmaril.SpecTec.Equiv.Validation (tyV) in
/-- **What is still assumed of `Whole.Assumptions` for the concrete `Prims.builtins`**, after the
typing track's proofs (`TypingFacts`, `StateTyping`, `RTyping`, `CtrlTyping`, `Exn.Typing`) and
the builtins track's (`IntB`, `RFuns`, most of `RStoreFuns`, `CtrlState`, `CtrlCall.expand`,
`CtrlHost.hostcall`/`liftResult`, `Exn.Helpers`): the typing of the runtime type syntax
(`TypeTyping`, `valtypes`), of results and function instances, and two of the three fields of
`Prims.Residual` (`RefOkBridge`, `$inst_reftype`; `CtrlCall.default` is proved,
`Integrate.ctrlCallDefault_simEnv`). -/
structure Residue {H : Type} (env : Env) (hn : H → String) : Prop where
  /-- Images of closed types inhabit `deftype`, `comptype`, `final?`, `typeuse*`. -/
  types : Prims.TypeTyping env
  /-- Images of closed value types are `valtype*`. -/
  valtypes : ∀ ts : Ty (.list .val), TypedV env valtypesT (.list (ts.toList.map tyV))
  /-- A result whose instructions are typed is a typed `result`. -/
  result : ∀ r : Result, TypedV env instrsT (.list (adminsToV r.toAdmin)) →
    TypedV env resultT (resultV r)
  /-- Function instances of a typed store are typed. -/
  funcinst : ∀ (s : Store H) (a : Nat) (fi : FuncInst H), TypedV env storeT (storeV hn s) →
    s.funcs[a]? = some fi → TypedV env funcinstT (funcInstV hn fi)
  /-- SpecTec's `Ref_ok` is Core's `RefOk`. -/
  refOk : RefsGC.RefOkBridge env
  /-- `$inst_reftype(m, rt)` is `CT.elemType (m.instRef rt)`. -/
  instReftype : ∀ (ρ : VarEnv) (e₁ e₂ : Exp) (m : ModuleInst) (rt : RefType),
    ρ.findDef? "inst_reftype" = none → EvalExp env ρ e₁ (RefsGC.moduleInstToValue' m) →
    EvalExp env ρ e₂ (Encode.toValue rt) →
    EvalExp env ρ (.callE "inst_reftype" [.expA e₁, .expA e₂]) (CT.elemType (m.instRef rt))

/-- The `Step_pure` rules the float track inverts (`Floats.bwd_*`), beyond `Bwd.pureDone`. -/
def floatDone : List Nat := [46, 47, 48, 49, 51, 52, 53]

/-- **The open backward rules**, after the float track's and round 3's: `Bwd.Remaining` without
the float operator rules `floatDone`, the rules of track bwd-pure-step (`BwdPureStep.pureDone`,
`BwdPureStep.stepDone`) and the `Step_read` rules of track bwd-read (`BwdRead.readDone`). -/
structure RemainingW {H : Type} (env : Env) (hn : H → String) (P : Numerics.Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure` outside `pureDone`, `floatDone` and `BwdPureStep.pureDone`. -/
  pure : ∀ i, i ∉ Bwd.pureDone → i ∉ floatDone → i ∉ BwdPureStep.pureDone →
    ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value), Typed env hn ⟨s, f, is⟩ → Fires env "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read` outside `readDoneUpTo` and the bwd-read track's `BwdRead.readDone`. -/
  read : ∀ i, i ∉ Bwd.readDoneUpTo → i ∉ BwdRead.readDone → ∀ (c : Config H) (w : Value),
    Typed env hn c → Fires env "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩
  /-- `Step` (index `≥ 6`) outside `stepDone` and `BwdPureStep.stepDone`. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ Bwd.stepDone → i ∉ BwdPureStep.stepDone →
    ∀ (c : Config H) (w : Value), Typed env hn c → Fires env "Step" i (.tuple [configV hn c, w]) →
      Bwd.BwdUpTo hn P host c w

/-- **The backward structures still assumed for the concrete `B`**: the `exnFields` half of
family X's decoders (an inversion of store typing) and the open backward rules. -/
structure BwdOpen {H : Type} (B : Builtins) (hn : H → String) (P : Numerics.Profile)
    (host : HostSemantics H) : Prop where
  /-- The fields of the exceptions of a typed state are typed values (`Exn.Decoders.exnFields`). -/
  exnFields : ∀ (s : Store H) (f : Frame), TypedV (simEnv B) stateT (stateV hn s f) →
    ∀ (a : Nat) (e : ExnInst), s.exns[a]? = some e →
      TypedV (simEnv B) valsT (.list (e.fields.map valV))
  /-- The rules without a backward lemma. -/
  remaining : RemainingW (simEnv B) hn P host

open Silmaril.Wasm.Numerics in
/-- **The restated whole-step goal, the round-2 target** (frozen; **refuted** in round 3:
`Round3.not_wholeStepBounded`, whose backward conjunct fails at `i32.const 0; memory.grow 0`
with no memory, because `Step/memory.grow-fail` has no premise). It is
`Bwd.Task.wholeStepUpTo` with the store bounds `StoreOk c.store` added to the forward conjunct:

* `Task.wholeStep`'s forward conjunct, and `Bwd.Task.wholeStepUpTo`'s, fail (argued; a formal
  refutation needs a `Typed` instance) at reachable stores outside `StoreOk`: `memory.fill` at a
  full `2 ^ 32`-byte memory (memory track, `Memory/Wrap.lean`) and `array.len` of an array with
  `2 ^ 32` or more fields (aggregates track). `StoreOk` excludes both, and every `2 ^ |at|` wrap
  of the table, memory and array rules.
* Call annotations are compared up to `Bwd.ConfigEq` (obstruction 1, `return_call_ref`) until
  the Core option-(a) change lands.
* It is meant against the IL evaluator **with the slice bound fixed** (`i + n ≤ |vs|` in
  `Sem/Value.lean`'s `slice?`/`setSlice`, obstruction 2), which the port now uses (upstream item
  U2 in `docs/projects/spectec/README.md`). With `eval.ml`'s strict bound
  (`Broken.sliceEvalMl?`) the forward conjunct also failed at a load or store whose last byte is
  the memory's last byte; now the boundary access has its slice (`Memory.loadBoundary`).

`Task.wholeStep` and `Bwd.Task.wholeStepUpTo` are kept, frozen, as stated. -/
def Task.wholeStepBounded : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
      ∃ B : Builtins,
        (∀ c c' : Config H, StoreOk c.store → Typed (simEnv B) hn c →
          Typed (simEnv B) hn c' → Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
          SStep (simEnv B) (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧
            Step (Profile.spec nd r) host c c')

/-- The restated goal is weaker than `Bwd.Task.wholeStepUpTo`. -/
theorem Task.wholeStepBounded_of_upTo (h : Bwd.Task.wholeStepUpTo) : Task.wholeStepBounded := by
  intro H hn hinj host hfin nd r
  obtain ⟨B, hf, hb⟩ := h H hn hinj host hfin nd r
  exact ⟨B, fun c c' _ hc hc' hs => hf c c' hc hc' hs, hb⟩

end Silmaril.Wasm.SpecTec.Sim.Integrate
