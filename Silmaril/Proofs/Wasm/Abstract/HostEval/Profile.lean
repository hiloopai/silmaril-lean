module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Invoke
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Interp.Thms

/-!
# The backward simulation of an invocation at every profile (proofs)

`back_invoke` is proved at the deterministic profile. For a store whose Wasm functions are
native-profile code (`Interp.NativeWasmFuncs`) and a host satisfying the explicit side condition
`Interp.HostNative` (its answers keep that, and never throw), Core steps of native configurations
do not depend on the profile (`Interp.step_profile`, `Interp.NHConfig.step`). A counted run and
its stuck end at any profile `P` are then the same at the deterministic profile
(`stepsN_profileH`, `stuck_profileH`), so `back_invoke_profile` holds at every profile.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- **Counted runs transfer between profiles** on native-profile configurations with host
functions; the end is again such a configuration. -/
theorem stepsN_profileH {P P' : Numerics.Profile} (hN : Interp.HostNative host) {n : Nat}
    {c c' : Config H} (h : StepsN P host n c c') (hc : Interp.NHConfig c) :
    StepsN P' host n c c' ∧ Interp.NHConfig c' := by
  induction h with
  | refl => exact ⟨.refl _, hc⟩
  | head hs _ ih =>
    obtain ⟨h', hc'⟩ := ih (hc.step hN hs)
    exact ⟨.head (Interp.step_profile hs hc.1) h', hc'⟩

/-- A stuck native configuration is stuck at every profile. -/
theorem stuck_profileH {P P' : Numerics.Profile} {c : Config H} (hc : Interp.NHConfig c)
    (hend : ∀ c', ¬ Step P host c c') : ∀ c', ¬ Step P' host c c' :=
  fun c' h => hend c' (Interp.step_profile h hc.1)

/-- **The backward simulation of an invocation, every profile**, for a store with native-profile
Wasm functions and a host satisfying `Interp.HostNative`. -/
theorem back_invoke_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    Pending host c.store c.code ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) := by
  obtain ⟨hrun', hc⟩ := stepsN_profileH (P' := profile (fun _ _ _ _ => false)) hN hrun
    (Interp.nhConfig_invoke hW a vs)
  exact back_invoke hT hH hs hS hok hrun' (stuck_profileH hc hend)

/-- `back_invoke_profile` for an uncounted run. -/
theorem back_invoke_steps_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : Steps P host (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    Pending host c.store c.code ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) :=
  let ⟨_, h⟩ := stepsN_of_steps hrun
  back_invoke_profile hT hH hN hs hS hW hok h hend

/-- **`back_invoke_reach` at every profile**, for a store with native-profile Wasm functions
and a host satisfying `Interp.HostNative`. -/
theorem back_invoke_reach_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    (∃ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (hh : H),
        (y = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ y) ∧ y.2.2 = c.store ∧
        c.store.funcs[y.1]? = some fi ∧ fi.code = .host hh ∧ (∀ o, ¬ host hh c.store y.2.1 o) ∧
        AtCall c.store y.1 y.2.1 c.code) ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) := by
  obtain ⟨hrun', hc⟩ := stepsN_profileH (P' := profile (fun _ _ _ _ => false)) hN hrun
    (Interp.nhConfig_invoke hW a vs)
  exact back_invoke_reach hT hH hs hS hok hrun' (stuck_profileH hc hend)

end Silmaril.Proofs.Wasm.Abstract.HostEval
