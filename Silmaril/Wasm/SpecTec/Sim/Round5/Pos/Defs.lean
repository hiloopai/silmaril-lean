module

public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track pos: definitions

Track pos found that the round-4 target `Round4.Task.wholeStepValid` is false, for a reason
unrelated to hosts (`Round5.Pos.not_wholeStepValid`, `docs/projects/spectec/README.md`): the first clause of SpecTec's `$utf8`, `def $utf8(ch*) = $concat_(byte, $utf8(ch)*)`,
matches its own recursive call, so `$utf8` of a non-empty list never evaluates, `name`'s premise
`|$utf8(char*)| < 2^32` never holds, and no module instance with an export (Core requires export
names to be distinct, so all but at most one are non-empty) is typed. SpecTec then cannot step
from a valid configuration whose frame exports something. Since `outOfFuel` is not `undef`, no
primitive `B` can repair it (upstream item U7, restated).

This header states, additively, the target with both known obstructions removed:

* `NoExports c`: no module instance of `c` (the frame's, a store function's, a frame's in the
  code) exports anything. This sidesteps `$utf8` until upstream fixes its definition;
* `Round5.Task.wholeStepValidOk`: the round-4 target for `HostOk` hosts (track pos also refutes
  `Parts.succTyped` for an ill-typed finite host) and for configurations that are valid, bounded
  and `NoExports`, the successor also `NoExports` in the forward conjunct (a host may return a
  store with exports, as it may return an unbounded one);
* `PosTypingNE`: `Round4.PosTyping` with `moduleinst` and `store` restricted to export-free
  modules (`Round4.PosTyping` itself is uninhabited, `Round5.Pos.not_posTyping`);
* `PartsOk`: what the restated target reduces to (`Round5.Pos.wholeStepValidOk_of_parts`).

The earlier targets are unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

namespace Pos

mutual
/-- No frame inside an administrative instruction has a module with exports. -/
def AdminNE : Admin → Prop
  | .label _ _ body => AdminsNE body
  | .handler _ _ body => AdminsNE body
  | .frame _ f body => f.module.exports = [] ∧ AdminsNE body
  | _ => True

/-- `AdminNE` on a sequence. -/
def AdminsNE : List Admin → Prop
  | [] => True
  | a :: l => AdminNE a ∧ AdminsNE l
end

/-- No function instance of the store has a module with exports. -/
def StoreNE (s : Store H) : Prop := ∀ fi ∈ s.funcs, fi.module.exports = []

/-- **No module instance of the configuration exports anything.** -/
structure NoExports (c : Config H) : Prop where
  /-- The store's function instances. -/
  store : StoreNE c.store
  /-- The frame. -/
  frame : c.frame.module.exports = []
  /-- The frames in the code, at every depth. -/
  code : AdminsNE c.code

/-- Bounded (`Round4.Bounded`) and export-free. -/
def BoundedNE (c : Config H) : Prop := Round4.Bounded c ∧ NoExports c

/-- Valid, bounded and export-free: the source predicate of `Task.wholeStepValidOk`. -/
def ValidNE (c : Config H) : Prop := Round4Int.Valid c ∧ NoExports c

/-- **`Round4.PosTyping` restricted to export-free modules and stores.** -/
structure PosTypingNE (B : Builtins) (hn : H → String) : Prop where
  /-- A valid instruction within SpecTec's syntax is a typed `instr`. -/
  instr : ∀ (C : Context) (i : Instr) (it : InstrType), InstrOk C i it →
    Round4.instrBnd i = true → TypedV (simEnv B) (.varT "instr" []) (instrToV i)
  /-- A valid, bounded `CALL_REF dt` is a typed `instr`. -/
  callRefType : ∀ d : DefType, TyOk {} d → Round4.tyBnd d = true →
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.callRefType d))
  /-- A valid, bounded `RETURN_CALL_REF dt` is a typed `instr`. -/
  returnCallRefType : ∀ d : DefType, TyOk {} d → Round4.tyBnd d = true →
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.returnCallRefType d))
  /-- A valid, bounded, export-free module instance is a typed `moduleinst`. -/
  moduleinst : ∀ (s : Store H) (m : ModuleInst) (C : Context), ModuleInstOk s m C →
    Round4.ModuleBnd m → m.exports = [] →
    TypedV (simEnv B) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT m)
  /-- A valid, bounded store whose function instances' modules export nothing is typed. -/
  store : ∀ s : Store H, StoreOk s → Integrate.StoreOk s → Round4.StoreBnd s → StoreNE s →
    TypedV (simEnv B) storeT (storeV hn s)

/-- **The `instr` field of `PosTypingNE`** (and of `Round4.PosTyping`): every valid instruction
within SpecTec's syntax is a typed `instr`. The other fields of `PosTypingNE` follow from it
(`Round5.Pos.posTypingNE_of_instr`). -/
def InstrTyping (B : Builtins) : Prop :=
  ∀ (C : Context) (i : Instr) (it : InstrType), InstrOk C i it → Round4.instrBnd i = true →
    TypedV (simEnv B) (.varT "instr" []) (instrToV i)

/-- **The instruction classes whose typing is still open**: the numeric operators
and conversions (`unop_`, `binop_`, `testop_`, `relop_`, `cvtop__`, dependent families with
premises), the scalar loads and stores (`loadop_`, `storeop_`), and the SIMD instructions other
than `v128.const`. -/
def InstrOpen : Instr → Bool
  | .intUnOp .. | .intBinOp .. | .intTestOp .. | .intRelOp .. | .floatUnOp .. | .floatBinOp ..
  | .floatRelOp .. | .convert _ => true
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. => true
  | .vecLoad .. | .vecLoadLane .. | .vecStore .. | .vecStoreLane .. => true
  | .vecUnOp _ | .vecBinOp _ | .vecTernOp _ | .vecTestOp _ | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
  | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
  | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => true
  | _ => false

/-- `InstrTyping` on the open classes only. -/
def OpenTyping (B : Builtins) : Prop :=
  ∀ (C : Context) (i : Instr) (it : InstrType), InstrOk C i it → Round4.instrBnd i = true →
    InstrOpen i = true → TypedV (simEnv B) (.varT "instr" []) (instrToV i)

/-- The SIMD instructions other than `v128.const` (a subclass of `InstrOpen`). -/
def InstrSimd : Instr → Bool
  | .vecLoad .. | .vecLoadLane .. | .vecStore .. | .vecStoreLane .. => true
  | .vecUnOp _ | .vecBinOp _ | .vecTernOp _ | .vecTestOp _ | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
  | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
  | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => true
  | _ => false

/-- `InstrTyping` on the SIMD instructions only. -/
def SimdTyping (B : Builtins) : Prop :=
  ∀ (C : Context) (i : Instr) (it : InstrType), InstrOk C i it → Round4.instrBnd i = true →
    InstrSimd i = true → TypedV (simEnv B) (.varT "instr" []) (instrToV i)

/-- **What `Task.wholeStepValidOk` reduces to**, at one encoding, host and profile, for
`B := Prims.builtins P hn host`: `Round4Int.Parts` without `succTyped` (it follows from
`HostOk`), with `PosTypingNE` for `PosTyping` and the forward conjunct on `ValidNE` sources. -/
structure PartsOk (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Positive typing of the leaves, export-free. -/
  pos : PosTypingNE (Round4Int.BI P hn host) hn
  /-- The forward conjunct on valid, bounded, export-free sources. -/
  fwd : R4Fwd.Forward (Round4Int.BI P hn host) hn P host ValidNE
  /-- The family rules of rounds 1–3, backward, under `ReadValid`. -/
  fam : Round4Int.FamBwdV (simEnv (Round4Int.BI P hn host)) hn P host
  /-- The backward rules no track has dispatched, under `ReadValid`. -/
  rem : Round4Read.RemainingV (simEnv (Round4Int.BI P hn host)) hn P host

end Pos

/-- **The restated round-5 target** (frozen; track pos): `Round4.Task.wholeStepValid` for
`HostOk` hosts and for valid, bounded configurations none of whose module instances exports
anything (`Pos.NoExports`). Both restrictions are forced: the round-4 target is false without
them (`Round5.Pos.not_wholeStepValid`, `Round5.Pos.not_wholeStepValid_hostOk`,
`Round5.Pos.not_succTyped`). -/
def Task.wholeStepValidOk : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Pos.BoundedNE c →
          Pos.BoundedNE c' → Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → Pos.BoundedNE c →
          SStep (simEnv B) (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round5
