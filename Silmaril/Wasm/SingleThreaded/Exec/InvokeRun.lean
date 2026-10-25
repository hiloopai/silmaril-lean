module

public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
public import Silmaril.Wasm.Execution.Core.Soundness.Headline

@[expose] public section

/-! # Interpreting `$invoke`

`runInvoke? o n s a vs` runs the interpreter for `n` steps from `invoke s a vs`
and returns the final configuration, the stop flag and the classified outcome.
Parallel to `EndToEnd.runModule?`, but with no decidability check: the
precondition `InvokeOk s a vs` is a hypothesis of the theorems.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-- Interpret `$invoke(s, a, vs)` with fuel `n`. -/
def runInvoke? (o : GrowOracle) (n : Nat) (s : Store H) (a : Nat) (vs : List Val) :
    Option (Config H × Bool × Option Result) :=
  let r := runI o n (invoke s a vs)
  some (r.1, r.2, r.1.outcome?)

namespace InvokeRun

variable {o : GrowOracle}

theorem runInvoke?_eq_some {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c' : Config H} {b : Bool} {r : Option Result}
    (h : runInvoke? o n s a vs = some (c', b, r)) :
    runI o n (invoke s a vs) = (c', b) ∧ r = c'.outcome? := by
  unfold runInvoke? at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [← h1, ← h2], by rw [← h3, h1]⟩

/-- The host-free part of soundness. -/
theorem runInvoke?_steps_noHost {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {b : Bool} {r : Option Result}
    (h : runInvoke? o n s a vs = some (c', b, r)) :
    Steps (profile o) noHost (invoke s a vs) c' := by
  obtain ⟨hrun, -⟩ := runInvoke?_eq_some h
  obtain ⟨_, _, _, _, _, hc⟩ := invoke_ok hs hi
  have := runI_steps_typed (o := o) n hc
  rw [hrun] at this
  exact this

/-- **Soundness** of interpreting `$invoke`. -/
theorem runInvoke?_sound {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {b : Bool} {r : Option Result}
    (h : runInvoke? o n s a vs = some (c', b, r)) :
    Steps (profile o) divHost (invoke s a vs) c' ∧
      (∃ fi ps rs, s.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
        ConfigOk c' rs.toList) ∧
      (∀ res, r = some res → c'.code = res.toAdmin) := by
  obtain ⟨-, rfl⟩ := runInvoke?_eq_some h
  have hst := EndToEnd.Steps.of_noHost divHost (runInvoke?_steps_noHost hs hi h)
  obtain ⟨fi, ps, rs, hfi, hexp, hok, -⟩ := invoke_safe divHost_ok hs hi hst
  exact ⟨hst, ⟨fi, ps, rs, hfi, hexp, hok⟩, fun _ hr => Config.outcome?_sound hr⟩

/-- A stopped result is terminal or can only step through the host. -/
theorem runInvoke?_stopped {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {r : Option Result}
    (h : runInvoke? o n s a vs = some (c', true, r)) :
    (c'.Terminal ∨ ∃ c'', Step (profile o) divHost c' c'') ∧
      ∀ c'', ¬ Step (profile o) noHost c' c'' := by
  obtain ⟨hrun, -⟩ := runInvoke?_eq_some h
  have hst := EndToEnd.Steps.of_noHost divHost (runInvoke?_steps_noHost hs hi h)
  obtain ⟨_, _, _, _, _, -, hprog⟩ := invoke_safe divHost_ok hs hi hst
  obtain ⟨_, _, _, _, _, hc⟩ := invoke_ok hs hi
  refine ⟨hprog, fun c'' hst' => ?_⟩
  have := runI_stopped_no_step_typed (o := o) (n := n) hc (by rw [hrun]) c''
  rw [hrun] at this
  exact this hst'

/-- **Completeness**: a host-free normal form reachable from `invoke s a vs` is
found by `runInvoke?` with enough fuel. -/
theorem runInvoke?_complete {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H}
    (h : Steps (profile o) noHost (invoke s a vs) c')
    (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, runInvoke? o n s a vs = some (c', true, c'.outcome?) := by
  obtain ⟨_, _, _, _, _, hc⟩ := invoke_ok hs hi
  obtain ⟨n, hn⟩ := runI_complete_typed hc h hnf
  exact ⟨n, by simp [runInvoke?, hn]⟩

end InvokeRun

end Silmaril.Wasm.SingleThreaded.Exec
