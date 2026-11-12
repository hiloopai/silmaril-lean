module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdStoreVac

/-!
# The forward 1.0 half: what is left after round 3, pass 2

`FwdRestQ10 B hn host` is `FwdRestP10` without the ten numeric steps (`FwdNum.fwdAt10_num`, from
`NumAgree10` at the spec profile) and without the four store leaves (vacuous,
`FwdStoreVac`). Twelve obligations remain: `br_table`, the four `call_indirect` cases,
`call_addr` of a wasm function (`invokeWasm`), the four load cases, `memory.size` and
`memory.grow`.

* `fwdRestP10_of_restQ`: `NumAgree10 (simEnv10 B) (Profile.spec nd r)` and `FwdRestQ10` give
  `FwdRestP10`;
* **`wholeStepFwd10_of_restQ`**: under `FwdRestQ10`, at the spec's builtins
  `floatIntB (Profile.spec nd r)`, every V1 step between configurations whose images are typed,
  from one satisfying `Plain10` and `GSetOk`, is a step of the wasm-1.0 script.

Successful loads and `memory.grow-succeed` cannot fire at `floatIntB` (1.0's `$bytes_` has no
clauses and `$growmemory` fails, round 2): those fields of `FwdRestQ10` are expected to be false
at `floatIntB` and need builtins that answer them. That is not done.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  result frameMemory frameTable setGlobal setMemory loadInt loadFloat storeInt storeFloat
  effectiveAddress expression)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst GlobalAddr FuncAddr MemAddr MemInst
  TableInst FuncInst ModuleInst Result)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- **The forward obligations still open after pass 2** (12 of them). -/
structure FwdRestQ10 (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  brTable : ∀ (s : Store H) (f : Frame) (ls : List LabelIdx) (d : LabelIdx) (c : BitVec 32),
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.brTable ls d)]⟩
      ⟨s, f, [.source (.br (ls[c.toNat]?.getD d))]⟩
  callIndirect : ∀ (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32) (table : TableInst)
    (a : FuncAddr) (fn : FuncInst V1.Func H) (ft : V1.FuncType), frameTable s f = some table →
      f.module.types[i.toNat]? = some ft → table.refs[c.toNat]? = some (some a) →
      s.funcs[a.value]? = some fn → fn.type = ft →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.invoke a]⟩
  callIndirectBounds : ∀ (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32)
    (table : TableInst), frameTable s f = some table → table.refs[c.toNat]? = none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  callIndirectNull : ∀ (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32)
    (table : TableInst), frameTable s f = some table → table.refs[c.toNat]? = some none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  callIndirectType : ∀ (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32) (table : TableInst)
    (a : FuncAddr) (fn : FuncInst V1.Func H) (ft : V1.FuncType), frameTable s f = some table →
      f.module.types[i.toNat]? = some ft → table.refs[c.toNat]? = some (some a) →
      s.funcs[a.value]? = some fn → fn.type ≠ ft →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  invokeWasm : ∀ (s : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType) (module : ModuleInst)
    (fn : V1.Func) (args : List Execution.Runtime.Value),
      s.funcs[a.value]? = some (.wasm ft module fn) → args.length = ft.params.length →
      ft.results.length ≤ 1 →
      FwdAt10 B hn ⟨s, f, values args ++ [.invoke a]⟩
        ⟨s, f, [.frame ft.results.length ⟨args ++ fn.locals.map Execution.Runtime.Value.zero,
          module⟩ [.label ft.results.length [] (expression fn.body)]]⟩
  intLoad : ∀ (s : Store H) (f : Frame) (t : IntType) (packed : Option (V1.PackSize × Signedness))
    (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value),
      frameMemory s f = some (a, m) → loadInt t packed m.data (effectiveAddress c arg) = some v →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ ⟨s, f, [value v]⟩
  intLoadTrap : ∀ (s : Store H) (f : Frame) (t : IntType)
    (packed : Option (V1.PackSize × Signedness)) (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr)
    (m : MemInst), frameMemory s f = some (a, m) →
      loadInt t packed m.data (effectiveAddress c arg) = none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ ⟨s, f, [.trap]⟩
  floatLoad : ∀ (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
    (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value), frameMemory s f = some (a, m) →
      loadFloat t m.data (effectiveAddress c arg) = some v →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [value v]⟩
  floatLoadTrap : ∀ (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
    (a : MemAddr) (m : MemInst), frameMemory s f = some (a, m) →
      loadFloat t m.data (effectiveAddress c arg) = none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [.trap]⟩
  memorySize : ∀ (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst),
    frameMemory s f = some (a, m) → FwdAt10 B hn ⟨s, f, [.source .memorySize]⟩
      ⟨s, f, [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩
  memoryGrow : ∀ (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst) (c r : BitVec 32)
    (bytes : Execution.Memory.Bytes), frameMemory s f = some (a, m) →
      Execution.Memory.Grow m.data m.max c.toNat bytes r →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
        ⟨setMemory s a {m with data := bytes}, f, [value (.int .i32 r)]⟩

/-- `NumAgree10` at the spec profile and `FwdRestQ10` give `FwdRestP10`. -/
theorem fwdRestP10_of_restQ {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (Q : FwdRestQ10 B hn host) :
    FwdRestP10 B hn host where
  brTable := Q.brTable
  numeric s f _ _ h := fwdAt10_num A s f h
  callIndirect := Q.callIndirect
  callIndirectBounds := Q.callIndirectBounds
  callIndirectNull := Q.callIndirectNull
  callIndirectType := Q.callIndirectType
  invokeWasm := Q.invokeWasm
  intLoad := Q.intLoad
  intLoadTrap := Q.intLoadTrap
  floatLoad := Q.floatLoad
  floatLoadTrap := Q.floatLoadTrap
  intStore s f t p arg c x _ _ _ _ _ := fwdAt10_intStore s f t p arg c x _ _
  intStoreTrap s f t p arg c x _ _ _ _ := fwdAt10_intStore s f t p arg c x _ _
  floatStore s f t arg c x _ _ _ _ _ := fwdAt10_floatStore s f t arg c x _ _
  floatStoreTrap s f t arg c x _ _ _ _ := fwdAt10_floatStore s f t arg c x _ _
  memorySize := Q.memorySize
  memoryGrow := Q.memoryGrow

/-- **The forward 1.0 half at the spec's builtins, from the twelve open obligations.** -/
theorem wholeStepFwd10_of_restQ {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    (Q : FwdRestQ10 (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) {c c' : Config H}
    (hc : Typed10 (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c)
    (hc' : Typed10 (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c')
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (h : Step host c c') :
    SStepB (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) (configV hn c) (configV hn c') :=
  wholeStepFwd10_of_restP (fwdRestP10_of_restQ numAgree10_floatIntB Q) hc hc' hpl hg h

end Silmaril.Wasm.SpecTec.Sim10.Whole
