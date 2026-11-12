module

public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms
public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Thms

/-!
# SpecTec ↔ Core 3.0, round 4, track r4-fwd: the forward direction with no coverage restriction

Rounds 2 and 3 proved the forward direction (Core → SpecTec) on a fragment of configurations
(`Integrate.Covered`, then `FwdMem.Covered3 true`) and left the rest as a hypothesis on the
configurations outside it. This file replaces that fragment by **per-instruction-class obligations**
(`Open4`): the forward recursion of `R4Fwd.forward_all` runs on **every** configuration with a
bounded store, and only the steps of the following classes are taken from `Open4`:

* `vector`: the SIMD operators other than `v128.const` and the bitwise ones (`VecArith`). Family V's
  `Vec.fwd_vector` proves these from `Vec.VecTyping` and `Vec.VecAgree` (`R4Fwd.open4Vector_of_agree`);
  neither interface is discharged for the concrete `B`.
* `vecMem`: the memory SIMD instructions (`VecMemI`). Their encoding (`schemaInstrV`) is provisional.
* `newDataNum`, `initDataZero`: two aggregate constructors, `array.new_data-num` and
  `array.init_data-zero` (stated as Core's constructors, `NewDataNumObl`, `InitDataZeroObl`).

Every other aggregate step is proved, **at every frame**, packed fields included
(`R4Fwd.fwd_aggregate_any`): rounds 2 and 3 needed `Aggregates.Unpacked` and left
`array.new_elem-alloc` open; this track removes both restrictions.

Each field is a forward obligation for a class of instructions, so a field that is later proved
removes that class without changing the statement of the others. Nothing here restricts the
configuration to a fragment: the recursion carries only `StoreOk` (bounded tables, memories and
aggregates), which the round-2/3 targets already assume.

`Forward B hn P host V` is the forward conjunct of a whole-step target whose source configurations
satisfy a validity predicate `V` (track r4-validity restates the target with Core validity; the
forward conjunct is proved here for `V := fun _ => True`, which implies every stronger `V`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Integrate (StoreOk)

variable {H : Type}

/-- The SIMD operators whose forward case is not proved for the concrete `B`: all but `v128.const`
and the bitwise ones (`v128.not`/`and`/`andnot`/`or`/`xor`/`bitselect`/`any_true`). -/
def VecArith : Instr → Bool
  | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
  | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
  | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => true
  | _ => false

/-- The memory SIMD instructions. -/
def VecMemI : Instr → Bool
  | .vecLoad .. | .vecLoadLane .. | .vecStore .. | .vecStoreLane .. => true
  | _ => false

/-- **SpecTec's `Expand` is functional on images**: an `Expand` derivation from the image of a
defined type ends at the image of Core's expansion. Proved for `Prims.builtins`
(`expandInv_builtins`). -/
def ExpandInv (env : Env) : Prop :=
  ∀ (O : ElseI) (d : DefType) (w : Value),
    DDerives env O "Expand" "%~~%" [] (.tuple [CT.defType d, w]) → ∃ ct, Expand d ct ∧ w = Silmaril.SpecTec.Equiv.Validation.tyV ct

/-- **`array.new_data-num`, forward** (Core's `AggregateStep.arrayNewDataNum`): the obligation
left open, since its premise needs `$concatn_` evaluated over `n` chunks. -/
def NewDataNumObl (B : Builtins) (hn : H → String) : Prop :=
  ∀ (s : Store H) (f : Frame) (x : TypeIdx) (y : DataIdx) (i n : BitVec 32) (d : DefType)
    (ft : CFieldType) (da : Nat) (di : DataInst) (vs : List Val),
    f.type? x = some d → Expand d (.array ft) → s.data? f y = some (da, di) →
    0 < storageSize (fieldStorage ft) →
    i.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size →
    (List.range n.toNat).mapM (fun k => readField? (fieldStorage ft) di.bytes
      (i.toNat + k * (storageSize (fieldStorage ft) / 8))) = some vs →
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩
      ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩

/-- **`array.init_data-zero`, forward** (Core's `AggregateStep.arrayInitDataZero`): left open,
since its `otherwise` premise must refute `-oob2` without Core's `Expand` premise. -/
def InitDataZeroObl (B : Builtins) (hn : H → String) : Prop :=
  ∀ (s : Store H) (f : Frame) (x : TypeIdx) (y : DataIdx) (i j : BitVec 32) (a da : Nat)
    (ai : ArrayInst) (di : DataInst), s.arrays[a]? = some ai → s.data? f y = some (da, di) →
    i.toNat ≤ ai.fields.length ∧ j.toNat ≤ di.bytes.size →
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
      .plain (.arrayInitData x y)]⟩ ⟨s, f, []⟩

/-- **What round 4's forward recursion takes as given**: one forward obligation per class of
instructions not yet proved for `B` (see the module docstring). -/
structure Open4 (B : Builtins) (hn : H → String) (P : Numerics.Profile) : Prop where
  /-- The non-bitwise SIMD operators. -/
  vector : ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
    (∃ i, Admin.plain i ∈ is ∧ VecArith i = true) →
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- The memory SIMD instructions. -/
  vecMem : ∀ c c' : Config H, MemoryStep P c c' →
    (∃ i, Admin.plain i ∈ c.code ∧ VecMemI i = true) → StoreOk c.store →
    FwdP (simEnv B) hn c c'
  /-- `array.new_data-num`. -/
  newDataNum : NewDataNumObl B hn
  /-- `array.init_data-zero`. -/
  initDataZero : InitDataZeroObl B hn

/-- **The forward conjunct of a whole-step target**, for source configurations satisfying `V`
(and with bounded stores, as in `Integrate.Task.wholeStepBounded`), up to call annotations. -/
def Forward (B : Builtins) (hn : H → String) (P : Numerics.Profile) (host : HostSemantics H)
    (V : Config H → Prop) : Prop :=
  ∀ c c' : Config H, V c → StoreOk c.store → Typed (simEnv B) hn c → Typed (simEnv B) hn c' →
    Step P host c c' → ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')

/-- A stronger validity predicate keeps the forward conjunct. -/
theorem Forward.mono {B : Builtins} {hn : H → String} {P : Numerics.Profile}
    {host : HostSemantics H} {V W : Config H → Prop} (hVW : ∀ c, W c → V c)
    (h : Forward B hn P host V) : Forward B hn P host W :=
  fun c c' hw => h c c' (hVW c hw)

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
