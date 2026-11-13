module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreCtx10T

/-!
# Stores nested anywhere, forward in `simEnv10T`

* `StoreLeaf10`: V1's six scalar store steps at the top of the code (`intStore` with and without
  a pack size, `floatStore`, and their traps). `StoreLeaf10.step`: each is a V1 step.
* `fwdAt10T_storeLeaf`: each is a step of `simEnv10T (bytesB10 P)` between the images, from a
  state typed in `simEnv10T` (`StoreTop10T` for the traps, `StoreVal10T` for the writes). V1's
  `storeInt`/`storeFloat` failing is the trap premise (`storeInt_none_lt`, `storeFloat_none_lt`).
* **`fwd10T_storeNest`**: a store nested under V1's contexts, labels and frames
  (`Nest10 StoreLeaf10`), from and to configurations typed in `simEnv10T`, is a step of
  `simEnv10T (bytesB10 P)` between the images. No other hypothesis: the store may hold
  functions that contain stores, and so may the code around the redex.
* **`wholeStepFwd10T_stores`**: the forward 1.0 whole step in `simEnv10T`, on the union 's
  fragment (typed in `simEnv10`, which excludes every `STORE`) and the nested stores.
* `sstep10T_memStoreNest`: the general theorem at an earlier trapping store `memStoreCfg10`
  (`StoreFix.sstep10T_memStoreCfg` was the same step checked by evaluation).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress setMemory storeInt storeFloat)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (bytesB10 fwdB10 Nest10 FwdAt10T Plain10 MemsAligned10)

variable {H : Type} {hn : H → String}

/-! ## The leaves -/

/-- **V1's scalar store steps at the top of the code.** -/
inductive StoreLeaf10 : Config H → Config H → Prop where
  | intStore (s : Store H) (f : Frame) (t : IntType) (arg : V1.MemArg) (c : BitVec 32)
      (x : BitVec t.width) (a : Execution.Runtime.MemAddr) (m : MemInst)
      (bytes : Execution.Memory.Bytes) (hm : frameMemory s f = some (a, m))
      (hs : storeInt t none m.data (effectiveAddress c arg) x = some bytes) :
      StoreLeaf10 ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t none arg)]⟩
        ⟨setMemory s a {m with data := bytes}, f, []⟩
  | intStorePack (s : Store H) (f : Frame) (t : IntType) (sz : V1.PackSize) (arg : V1.MemArg)
      (c : BitVec 32) (x : BitVec t.width) (a : Execution.Runtime.MemAddr) (m : MemInst)
      (bytes : Execution.Memory.Bytes) (hm : frameMemory s f = some (a, m))
      (hs : storeInt t (some sz) m.data (effectiveAddress c arg) x = some bytes) :
      StoreLeaf10 ⟨s, f, [value (.int .i32 c), value (.int t x),
        .source (.intStore t (some sz) arg)]⟩ ⟨setMemory s a {m with data := bytes}, f, []⟩
  | intStoreTrap (s : Store H) (f : Frame) (t : IntType) (p : Option V1.PackSize)
      (arg : V1.MemArg) (c : BitVec 32) (x : BitVec t.width) (a : Execution.Runtime.MemAddr)
      (m : MemInst) (hm : frameMemory s f = some (a, m))
      (hs : storeInt t p m.data (effectiveAddress c arg) x = none) :
      StoreLeaf10 ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t p arg)]⟩
        ⟨s, f, [.trap]⟩
  | floatStore (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
      (x : BitVec t.width) (a : Execution.Runtime.MemAddr) (m : MemInst)
      (bytes : Execution.Memory.Bytes) (hm : frameMemory s f = some (a, m))
      (hs : storeFloat t m.data (effectiveAddress c arg) x = some bytes) :
      StoreLeaf10 ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩
        ⟨setMemory s a {m with data := bytes}, f, []⟩
  | floatStoreTrap (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
      (x : BitVec t.width) (a : Execution.Runtime.MemAddr) (m : MemInst)
      (hm : frameMemory s f = some (a, m))
      (hs : storeFloat t m.data (effectiveAddress c arg) x = none) :
      StoreLeaf10 ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩
        ⟨s, f, [.trap]⟩

/-- Every store leaf is a V1 step. -/
theorem StoreLeaf10.step {host : HostSemantics H} {c c' : Config H} (h : StoreLeaf10 c c') :
    Step host c c' := by
  cases h with
  | intStore s f t arg c x a m bytes hm hs => exact .intStore s f t none arg c x a m bytes hm hs
  | intStorePack s f t sz arg c x a m bytes hm hs =>
    exact .intStore s f t (some sz) arg c x a m bytes hm hs
  | intStoreTrap s f t p arg c x a m hm hs => exact .intStoreTrap s f t p arg c x a m hm hs
  | floatStore s f t arg c x a m bytes hm hs => exact .floatStore s f t arg c x a m bytes hm hs
  | floatStoreTrap s f t arg c x a m hm hs => exact .floatStoreTrap s f t arg c x a m hm hs

/-! ## Failing stores are out of bounds -/

theorem lt_of_writeBytes_none {mem w : Execution.Memory.Bytes} {st : Nat}
    (h : Execution.Memory.writeBytes mem st w = none) : mem.size < st + w.size := by
  unfold Execution.Memory.writeBytes at h
  split at h
  · cases h
  · omega

theorem storeInt_none_lt {t : IntType} {p : Option V1.PackSize} {mem : Execution.Memory.Bytes}
    {st : Nat} {x : BitVec t.width} (h : storeInt t p mem st x = none) :
    mem.size < st + ((p.map V1.PackSize.width).getD t.width) / 8 := by
  have h' := lt_of_writeBytes_none h
  simpa [Execution.Memory.encodeLE_size] using h'

theorem storeFloat_none_lt {t : FloatType} {mem : Execution.Memory.Bytes} {st : Nat}
    {x : BitVec t.width} (h : storeFloat t mem st x = none) : mem.size < st + t.width / 8 := by
  have h' := lt_of_writeBytes_none h
  simpa [Execution.Memory.encodeLE_size] using h'

/-! ## The leaves, forward -/

/-- **Every store leaf is a step of `simEnv10T (bytesB10 P)`**, from a state typed there. -/
theorem fwdAt10T_storeLeaf {P : Profile} {c c' : Config H} (h : StoreLeaf10 c c') :
    FwdAt10T (bytesB10 P) hn c c' := by
  intro hz _ _ _
  cases h with
  | intStore s f t arg c x a m bytes hm hs =>
    exact sstepB10T_of_fires (fires10T_storeNumVal (v := ⟨.int t, x⟩) (ao := arg) (st := .intStore t none arg) rfl hz hm
      ((storeInt_eq_write10 t _ _ x).symm.trans hs))
  | intStorePack s f t sz arg c x a m bytes hm hs =>
    exact sstepB10T_of_fires (fires10T_storePackVal hz hm
      ((storeIntPack_eq_write10 t sz _ _ x).symm.trans hs))
  | intStoreTrap s f t p arg c x a m hm hs =>
    cases p with
    | none => exact sstepB10T_of_fires (fires10T_storeNumTrap (v := ⟨.int t, x⟩) (ao := arg)
        (st := .intStore t none arg) rfl hz hm (storeInt_none_lt hs))
    | some sz => exact sstepB10T_of_fires (fires10T_storePackTrap hz hm (storeInt_none_lt hs))
  | floatStore s f t arg c x a m bytes hm hs =>
    exact sstepB10T_of_fires (fires10T_storeNumVal (v := ⟨.float t, x⟩) (ao := arg)
      (st := .floatStore t arg) rfl hz hm ((storeFloat_eq_write10 t _ _ x).symm.trans hs))
  | floatStoreTrap s f t arg c x a m hm hs =>
    exact sstepB10T_of_fires (fires10T_storeNumTrap (v := ⟨.float t, x⟩) (ao := arg) (st := .floatStore t arg) rfl hz hm
      (storeFloat_none_lt hs))

/-! ## Nested stores, and the whole step -/

/-- **A store nested anywhere is a step of `simEnv10T (bytesB10 P)`** between configurations
typed there. -/
theorem fwd10T_storeNest {P : Profile} {c c' : Config H} (h : Nest10 StoreLeaf10 c c')
    (hc : Typed10 (simEnv10T (bytesB10 P)) hn c) (hc' : Typed10 (simEnv10T (bytesB10 P)) hn c') :
    SStepB (simEnv10T (bytesB10 P)) (configV hn c) (configV hn c') :=
  Whole.fwd10_nest_typedT (fun _ _ hl => fwdAt10T_storeLeaf hl) hc hc' h

/-- **The forward 1.0 whole step in `simEnv10T`, stores included**: on an earlier fragment (typed
in `simEnv10`, hence free of stores), and on stores nested anywhere between configurations typed
in `simEnv10T`. -/
theorem wholeStepFwd10T_stores {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (h : Step host c c')
    (hg : (Typed10 (simEnv10 (fwdB10 nd r)) hn c ∧ Plain10 c.code ∧
        GSetOk c.store c.frame c.code ∧ MemsAligned10 c.store) ∨
      (Nest10 StoreLeaf10 c c' ∧ Typed10 (simEnv10T (fwdB10 nd r)) hn c ∧
        Typed10 (simEnv10T (fwdB10 nd r)) hn c')) :
    SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) (configV hn c') := by
  rcases hg with ⟨hc, hpl, hgs, hal⟩ | ⟨hn', hc, hc'⟩
  · exact (wholeStepFwd10T hc hpl hgs hal h).2
  · exact fwd10T_storeNest hn' hc hc'

/-! ## The trapping store , as an instance -/

/-- **`memStoreCfg10` steps in `simEnv10T`**, by the general theorem. -/
theorem sstep10T_memStoreNest (P : Profile) :
    SStepB (simEnv10T (bytesB10 P)) (configV Empty.elim StoreFix.memStoreCfg10)
      (configV Empty.elim StoreFix.memStoreCfg10') :=
  fwd10T_storeNest (.leaf (.intStoreTrap _ _ _ _ _ _ _ ⟨0⟩ ⟨ByteArray.empty, none⟩ rfl
    (by decide))) (StoreFix.typed10T_memStoreCfg _) (StoreFix.typed10T_memStoreCfg' _)

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
