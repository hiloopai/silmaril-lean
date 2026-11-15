module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Profile
public import Silmaril.Wasm.Abstract.Recursion.Defs

/-!
# The backward simulation of an invocation, by exit flows (proofs)

`back_invoke` states the answered end through `Flow.retVals`; the invocation-level
packaging (`exitFlow`, as in `ClosedOutcome`) hands back `exitFlow rs.length bfl`
instead. `exitFlow_of_retVals` and `exitFlow_trap` relate the two, and
`back_invoke_exit`/`back_invoke_exit_profile` restate the backward simulation with
the exit flow: a stuck end is blocked, or the callee's exit flow `.normal ws` with
`c` the values `ws`, or a trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

theorem exitFlow_of_retVals {n : Nat} {fl : Binaryen.Flow} {ws : List Val}
    (h : fl.retVals = some ws) : exitFlow n fl = some (.normal (ws.take n).reverse) := by
  rcases fl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp_all [Binaryen.Flow.retVals, exitFlow]

/-- The end of `back_invoke`, by the exit flow. -/
theorem exit_of_end {rs : List Validation.CValType} {s₂ : Store H} {fl : Binaryen.Flow}
    {c : Config H}
    (h : (∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
      (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) :
    ∃ fl', exitFlow rs.length fl = some fl' ∧
      ((∃ ws, fl' = .normal ws ∧ c = ⟨s₂, {}, vals ws⟩) ∨ (fl' = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) := by
  rcases h with ⟨ws, hw, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, exitFlow_of_retVals hw, .inl ⟨_, rfl, rfl⟩⟩
  · exact ⟨.trap, rfl, .inr ⟨rfl, rfl⟩⟩

/-- **`back_invoke` by exit flows** (deterministic profile). -/
theorem back_invoke_exit {o : GrowOracle} (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {n : Nat} {s : Store H} {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (profile o) host c c') :
    Pending host c.store c.code ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H)
        (bfl fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, bfl) ∧ exitFlow rs.length bfl = some fl ∧
        ((∃ ws, fl = .normal ws ∧ c = ⟨s₂, {}, vals ws⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) := by
  rcases back_invoke hT hH hs hS hok hrun hend with hp | ⟨fi, ps, rs, s₂, bfl, hfi, hty, hc, he⟩
  · exact .inl hp
  · obtain ⟨fl, hx, hfl⟩ := exit_of_end he
    exact .inr ⟨fi, ps, rs, s₂, bfl, fl, hfi, hty, hc, hx, hfl⟩

/-- **`back_invoke_profile` by exit flows** (every profile, native side conditions). -/
theorem back_invoke_exit_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    Pending host c.store c.code ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H)
        (bfl fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, bfl) ∧ exitFlow rs.length bfl = some fl ∧
        ((∃ ws, fl = .normal ws ∧ c = ⟨s₂, {}, vals ws⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) := by
  rcases back_invoke_profile hT hH hN hs hS hW hok hrun hend with
    hp | ⟨fi, ps, rs, s₂, bfl, hfi, hty, hc, he⟩
  · exact .inl hp
  · obtain ⟨fl, hx, hfl⟩ := exit_of_end he
    exact .inr ⟨fi, ps, rs, s₂, bfl, fl, hfi, hty, hc, hx, hfl⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
