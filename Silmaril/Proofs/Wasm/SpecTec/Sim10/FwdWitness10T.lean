module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdRun10T

/-!
# Witnesses with a function in the store for the 1.0 invocation theorems

Round 4's `Task.wholeRunFwd10Inv` (proved) assumes a valid Core store (`StoreOk`, Core 3.0's
`Store_ok`). Until now no store with a function was shown to satisfy its hypotheses. This module
builds, for any body, the store `storeW10 body`: one function of type `[] → []` whose module has
one type and one memory, and one empty memory. Then:

* **`storeOk_W10`**: the Core image of `storeW10 body` is `StoreOk` as soon as Core's function
  checker accepts the body (`funcCheck_sound`); every other field is checked by the kernel
  (`decide +kernel` on Core's `TyOk.check` and `MemTypeOk.check`). `invokeOk_W10`, `storeWF_W10`:
  the other hypotheses of the invocation theorem hold.
* **`nopDrop`** (`i32.const 0; drop`): the image of the invocation is typed in `simEnv10`
  (`typed10_nopDrop`), so **`wholeRunFwd10Inv_nopDrop`**: round 4's `Task.wholeRunFwd10Inv` has
  all its hypotheses at a store with a function, and applies to its first step
  (`step_invoke_W10`).
* **`storeBody`** (`i32.const 0; i32.const 0; i32.store`): a storing function. Its Core store is
  valid (`storeOk_storeBody`), the image of the invocation is typed in `simEnv10T`
  (`typed10T_storeBody`) and **not** in `simEnv10` (`not_typed10_storeBody`), so round 4's
  theorem says nothing there, while **`wholeRunFwd10InvT_storeBody`** (an earlier
  `wholeRunFwd10InvT`) applies to every run, in particular the first step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Witness10T

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.Execution.Core (StoreOk FuncInstOk ModuleInstOk ExternAddrOk)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Step Steps expression)
open Silmaril.Wasm.SpecTec.Sim (TypedV typedV_list_iff)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10 wholeRunFwd10Inv wholeRunFwd10InvT)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)

/-! ## The store -/

/-- The module instance of the function: one type `[] → []`, one memory. -/
def modW10 : Execution.Runtime.ModuleInst := { types := [⟨[], []⟩], memories := [⟨0⟩] }

/-- A function of type `[] → []` with body `body`. -/
def fnW10 (body : V1.Expr) : V1.Func := ⟨⟨0⟩, [], body⟩

/-- **One function (body `body`) and one empty memory.** -/
def storeW10 (body : V1.Expr) : Store Empty :=
  { funcs := [.wasm ⟨[], []⟩ modW10 (fnW10 body)], memories := [⟨ByteArray.empty, none⟩] }

/-- Its Core image. -/
abbrev cW10 (body : V1.Expr) : Execution.Core.Store Empty := coreStore10 (storeW10 body)

variable (body : V1.Expr)

theorem len_funcs_cW10 : (cW10 body).funcs.length = 1 := rfl
theorem len_mems_cW10 : (cW10 body).mems.length = 1 := rfl

/-- The Core function instance. -/
abbrev fiW10 : Execution.Core.FuncInst Empty :=
  (cW10 body).funcs[0]'(by rw [len_funcs_cW10]; exact Nat.zero_lt_one)

/-- The Core memory instance. -/
abbrev miW10 : Execution.Core.MemInst :=
  (cW10 body).mems[0]'(by rw [len_mems_cW10]; exact Nat.zero_lt_one)

theorem funcs_cW10 : (cW10 body).funcs = [fiW10 body] := rfl
theorem mems_cW10 : (cW10 body).mems = [miW10 body] := rfl

/-- The Core context of the function's module. -/
def ctxW10 : Context :=
  { types := (fiW10 []).module.types, recs := [], tags := [], globals := [],
    mems := [(miW10 []).type], tables := [], funcs := [], datas := [], elems := [],
    refs := List.range 0 }

theorem module_cW10 : (fiW10 body).module = (fiW10 []).module := rfl
theorem type_cW10 : (fiW10 body).type = (fiW10 []).type := rfl
theorem mem_cW10 : miW10 body = miW10 [] := rfl

theorem tyCheck_W10 : TyOk.check {} (fiW10 []).type = true := by decide +kernel
theorem memCheck_W10 : MemTypeOk.check (miW10 []).type = true := by decide +kernel

/-- The function's module instance is typed against `ctxW10`. -/
theorem moduleOk_W10 : ModuleInstOk (cW10 body) (fiW10 body).module ctxW10 := by
  have ht : (fiW10 body).module.types = [(fiW10 []).type] := rfl
  refine ModuleInstOk.mk (tags := []) (globals := []) (funcs := []) (tables := []) (elems := [])
    (k := 0) ?_ .nil .nil .nil (.cons (.mem rfl) .nil) .nil ?_ .nil ?_ .nil ?_ (Nat.zero_le _)
  · rw [ht]
    intro d hd
    rw [List.mem_singleton.1 hd]
    exact TyOk.check_sound tyCheck_W10
  · intro a ha
    simp [show (fiW10 body).module.datas = [] from rfl] at ha
  · intro xi hx
    simp [show (fiW10 body).module.exports = [] from rfl] at hx
  · intro xi hx
    simp [show (fiW10 body).module.exports = [] from rfl] at hx

/-- The memory of `storeW10 body` is valid. -/
theorem memsOk_W10 : ∀ mi ∈ (cW10 body).mems, Execution.Core.MemInstOk mi := by
  intro mi h
  have hmi : mi = miW10 body := List.mem_singleton.1 (mems_cW10 body ▸ h)
  rw [hmi, mem_cW10]
  exact ⟨MemTypeOk.check_iff.1 memCheck_W10, rfl⟩

/-- The function of `storeW10 body` is valid when Core's checker accepts its body. -/
theorem funcsOk_W10 {c : Func} (hc : (fiW10 body).code = .wasm c)
    (hf : funcCheck tyOkC exprC ctxW10 c (fiW10 []).type = true) :
    ∀ fi ∈ (cW10 body).funcs, FuncInstOk (cW10 body) fi := by
  intro fi h
  have hfi : fi = fiW10 body := List.mem_singleton.1 (funcs_cW10 body ▸ h)
  rw [hfi]
  exact .wasm (TyOk.check_sound (type_cW10 body ▸ tyCheck_W10)) (moduleOk_W10 body) hc
    (funcCheck_sound tyOkC_sound' exprC_sound (type_cW10 body ▸ hf))
    (Sub.refl (k := .def) _ trivial _)

/-- **The Core image of `storeW10 body` is valid** when Core's checker accepts the body. -/
theorem storeOk_W10 {c : Func} (hc : (fiW10 body).code = .wasm c)
    (hf : funcCheck tyOkC exprC ctxW10 c (fiW10 []).type = true) :
    StoreOk (cW10 body) where
  tags _ h := absurd (show _ ∈ ([] : List Execution.Core.TagInst) from h) List.not_mem_nil
  globals _ h := absurd (show _ ∈ ([] : List Execution.Core.GlobalInst) from h) List.not_mem_nil
  mems := memsOk_W10 body
  tables _ h := absurd (show _ ∈ ([] : List Execution.Core.TableInst) from h) List.not_mem_nil
  funcs := funcsOk_W10 body hc hf
  elems _ h := absurd (show _ ∈ ([] : List Execution.Core.ElemInst) from h) List.not_mem_nil
  structs _ h := absurd (show _ ∈ ([] : List Execution.Core.StructInst) from h) List.not_mem_nil
  arrays _ h := absurd (show _ ∈ ([] : List Execution.Core.ArrayInst) from h) List.not_mem_nil
  exns _ h := absurd (show _ ∈ ([] : List Execution.Core.ExnInst) from h) List.not_mem_nil
  acyclicStructs a h := absurd (show a < 0 from h) (Nat.not_lt_zero a)
  acyclicArrays a h := absurd (show a < 0 from h) (Nat.not_lt_zero a)
  acyclicExns a h := absurd (show a < 0 from h) (Nat.not_lt_zero a)
  structsClosed _ h := absurd (show _ ∈ ([] : List Execution.Core.StructInst) from h)
    List.not_mem_nil
  arraysClosed _ h := absurd (show _ ∈ ([] : List Execution.Core.ArrayInst) from h)
    List.not_mem_nil

/-- The invocation of function `0` without arguments fits (`$invoke`'s premise). -/
theorem invokeOk_W10 : Execution.Core.InvokeOk (cW10 body) 0 [] :=
  ⟨_, .nil, .nil, rfl, Expand.iff.mpr rfl, .nil⟩

/-- The function slots of `storeW10 body`, as Lime1 sees them. -/
theorem funcs_lime_W10 : ((storeW10 body).mapCode V1.Func.toLime).funcs =
    [.wasm ⟨[], []⟩ modW10 (fnW10 body).toLime] := rfl

/-- The memory slots of `storeW10 body`, as Lime1 sees them. -/
theorem mems_lime_W10 : ((storeW10 body).mapCode V1.Func.toLime).memories =
    [⟨ByteArray.empty, none⟩] := rfl

/-- `storeW10 body` is well formed for the Lime1 simulation. -/
theorem storeWF_W10 : Lime1.Execution.StoreWF ((storeW10 body).mapCode V1.Func.toLime) := by
  refine ⟨fun i t m c h a ha => ?_, fun i mi h => ?_⟩
  · have hm := List.mem_of_getElem? h
    rw [funcs_lime_W10] at hm
    have e : m = modW10 := by
      simp only [List.mem_singleton, Execution.Runtime.FuncInst.wasm.injEq] at hm
      exact hm.2.1
    rw [e] at ha
    exact absurd ha (by simp [modW10])
  · have hm := List.mem_of_getElem? h
    rw [mems_lime_W10] at hm
    have e : mi = ⟨ByteArray.empty, none⟩ := List.mem_singleton.1 hm
    rw [e]
    exact ⟨by decide, fun j hj => by cases hj⟩

/-- **The first step of the invocation**: V1 opens the function's frame. -/
theorem step_invoke_W10 (host : HostSemantics Empty) :
    Step host (invokeCfg10 (storeW10 body) [] ⟨0⟩)
      ⟨storeW10 body, Valid.frame0, [.frame 0 ⟨[], modW10⟩ [.label 0 [] (expression body)]]⟩ :=
  .invokeWasm _ _ ⟨0⟩ ⟨[], []⟩ modW10 (fnW10 body) [] rfl rfl (by decide)

/-! ## A function that does not store: round 4's theorem, with all its hypotheses -/

/-- `i32.const 0; drop`. -/
def nopDrop : V1.Expr := [.intConst .i32 0, .drop]

theorem funcCheck_nopDrop : funcCheck tyOkC exprC ctxW10
    ⟨⟨0⟩, [], [.intConst .i32 0, .drop]⟩ (fiW10 []).type = true := by
  decide +kernel

/-- **A valid Core store with a function.** -/
theorem storeOk_nopDrop : StoreOk (cW10 nopDrop) := storeOk_W10 nopDrop rfl funcCheck_nopDrop

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem typed10_nopDrop (B : Builtins) :
    Typed10 (simEnv10 B) Empty.elim (invokeCfg10 (storeW10 nopDrop) [] ⟨0⟩) :=
  ⟨300, by with_unfolding_all rfl⟩

/-- **Round 4's `Task.wholeRunFwd10Inv` at a store with a function**: every hypothesis holds, and
every V1 run from the invocation (for instance its first step) is a run of the 1.0 script. -/
theorem wholeRunFwd10Inv_nopDrop (host : HostSemantics Empty) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Empty} (h : Steps host (invokeCfg10 (storeW10 nopDrop) [] ⟨0⟩) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) Empty.elim c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV Empty.elim (invokeCfg10 (storeW10 nopDrop) [] ⟨0⟩)) (configV Empty.elim c') :=
  wholeRunFwd10Inv Empty Empty.elim host nd r _ [] ⟨0⟩ c' (typed10_nopDrop _) storeOk_nopDrop
    (invokeOk_W10 nopDrop) (storeWF_W10 nopDrop) h

/-! ## A function that stores: an earlier theorem in `simEnv10T` -/

/-- `i32.const 0; i32.const 0; i32.store`. -/
def storeBody : V1.Expr := [.intConst .i32 0, .intConst .i32 0, .intStore .i32 none ⟨0, 0⟩]

theorem funcCheck_storeBody : funcCheck tyOkC exprC ctxW10
    ⟨⟨0⟩, [], [.intConst .i32 0, .intConst .i32 0, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]⟩
    (fiW10 []).type = true := by
  decide +kernel

/-- **A valid Core store whose function stores.** -/
theorem storeOk_storeBody : StoreOk (cW10 storeBody) :=
  storeOk_W10 storeBody rfl funcCheck_storeBody

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem typed10T_storeBody (B : Builtins) :
    Typed10 (simEnv10T B) Empty.elim (invokeCfg10 (storeW10 storeBody) [] ⟨0⟩) :=
  ⟨300, by with_unfolding_all rfl⟩

/-- **In `simEnv10` the invocation's image is not typed**: the store's function stores. -/
theorem not_typed10_storeBody (B : Builtins) :
    ¬ Typed10 (simEnv10 B) Empty.elim (invokeCfg10 (storeW10 storeBody) [] ⟨0⟩) := by
  intro h
  have hst := (Whole.typedV_stV_iff10.1 (Whole.typedV_state_of_typed10 h)).1
  have hfn := Whole.typedV_funcV_of_store10 (i := 0) hst rfl
  have hb := Whole.typedV_bodyOfFunc10 hfn
  rw [Whole.instrsToV_map10] at hb
  have hi := typedV_list_iff.1 hb (instrToV (.intStore .i32 none ⟨0, 0⟩)) (by simp [fnW10, storeBody])
  exact Whole.not_typedV_store10 _ (Whole.typedV_admin_of_instr10 hi)

/-- **an earlier `wholeRunFwd10InvT` at a store whose function stores**: every hypothesis holds,
so every V1 run from the invocation is a run of `simEnv10T`, while round 4's theorem (stated in
`simEnv10`) does not apply. -/
theorem wholeRunFwd10InvT_storeBody (host : HostSemantics Empty) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Empty} (h : Steps host (invokeCfg10 (storeW10 storeBody) [] ⟨0⟩) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) Empty.elim c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV Empty.elim (invokeCfg10 (storeW10 storeBody) [] ⟨0⟩)) (configV Empty.elim c') :=
  wholeRunFwd10InvT (typed10T_storeBody _) storeOk_storeBody (invokeOk_W10 storeBody)
    (storeWF_W10 storeBody) h

/-- **Non-vacuity**: the first step of the storing invocation is a step of `simEnv10T`. -/
theorem sstep10T_invoke_storeBody (host : HostSemantics Empty) (nd : Bool) (r : RelaxedChoice) :
    Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
      (configV Empty.elim (invokeCfg10 (storeW10 storeBody) [] ⟨0⟩))
      (configV Empty.elim ⟨storeW10 storeBody, Valid.frame0,
        [.frame 0 ⟨[], modW10⟩ [.label 0 [] (expression storeBody)]]⟩) :=
  (wholeRunFwd10InvT_storeBody host nd r
    (Relation.ReflTransGen.single (step_invoke_W10 storeBody host))).2

end Silmaril.Wasm.SpecTec.Sim10.Witness10T
