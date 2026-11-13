module

public import Silmaril.Wasm.Replace.Defs

/-!
# Function replacement on reachable stores (Wasm 1.0): theorems

* `Reachable.stepClosed`, `StepClosed.steps`: `Reachable` is closed under reduction, and every
  step-closed predicate is closed under finite runs.
* `HostRespectsReplace.empty`: the closed host (`H := Empty`) respects every replacement.
* `stepClosed_eq_of_fixed`: over the closed host, a store with no globals and no memories is
  never written, so `(· = s)` is step-closed. This gives a simple `Reach` for examples.
* `CallSimOn.mono`: shrinking `Reach` weakens the hypothesis.
* `eq_of_callSimOn_true`: at the total predicate the hypothesis forces `a = b`
  (silmaril-lean's `eq_of_forall_callSim`). A contentful `CallSimOn` needs a proper `Reach`.
* **`behaviours_replace_at`**: `CallSim host a b s` alone makes the replacement invisible at
  the replaced address: `behaviours host s a vs = behaviours host (s.replaceFunc a b) a vs`. A
  run out of an invocation ends at the frame it started from (`Sealed.steps`), so its terminal
  configurations have the shape `CallSim` speaks about. `behaviours_replace_at_reach` is the
  `CallSimOn` form.

Ported from an earlier development `Silmaril/Wasm/Equiv/Reach.lean`. The source's
`StepClosed.invoke` (a restatement of `StepClosed.steps`) and `callSimOn_true_iff` (an unfolding)
are folded into the statements above; `behaviours_replace_at` is split into its two inclusions.
-/

@[expose] public section

namespace Silmaril.Wasm.Replace

open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type}

/-- `Reachable` is closed under reduction, by its `step` constructor. -/
theorem Reachable.stepClosed (host : HostSemantics H) (s₀ : Store H)
    (m : Silmaril.Wasm.V1.Module) (imports : List ExternVal) :
    StepClosed host (Reachable host s₀ m imports) :=
  fun _ _ _ _ _ _ hs hstep => Reachable.step hs hstep

/-- A step-closed predicate is closed under finite runs. -/
theorem StepClosed.steps {host : HostSemantics H} {Reach : Store H → Prop}
    (hcl : StepClosed host Reach) {c c' : Config H} (h : Steps host c c')
    (hs : Reach c.store) : Reach c'.store := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact hcl ih hstep

/-- The closed host respects every replacement. -/
theorem HostRespectsReplace.empty (host : HostSemantics Empty) (a b : FuncAddr) :
    HostRespectsReplace host a b where
  forward := fun fn => fn.elim
  backward := fun fn => fn.elim
  diverges := fun fn => fn.elim

/-- Over the closed host, reduction does not write a store without globals and memories: the
only store-writing rules are `global.set`, the stores, `memory.grow` and host calls. -/
theorem step_store_eq_of_closed {host : HostSemantics Empty} :
    ∀ {c c' : Config Empty}, Step host c c' →
      c.store.globals = [] → c.store.memories = [] → c'.store = c.store := by
  intro c c' h
  induction h with
  | context _ vs tail ih => exact ih
  | label _ n cont ih => exact ih
  | frame _ n outer ih => exact ih
  | _ =>
    intro hg hm
    first
      | rfl
      | exact Empty.elim (by assumption)
      | simp_all [frameMemory]

/-- Equality with a store that reduction cannot write is step-closed. -/
theorem stepClosed_eq_of_fixed {host : HostSemantics Empty} (s : Store Empty)
    (hg : s.globals = []) (hm : s.memories = []) : StepClosed host (· = s) := by
  rintro t t' f f' X X' rfl hstep
  exact step_store_eq_of_closed hstep hg hm

/-- Shrinking `Reach` weakens `CallSimOn`. -/
theorem CallSimOn.mono {Reach Reach' : Store H → Prop} (hle : ∀ s, Reach' s → Reach s)
    {host : HostSemantics H} {a b : FuncAddr} (h : CallSimOn Reach host a b) :
    CallSimOn Reach' host a b :=
  fun s hs => h s (hle s hs)

/-- At the total predicate, `CallSimOn` admits only the identity replacement. -/
theorem eq_of_callSimOn_true {host : HostSemantics H} {a b : FuncAddr}
    (h : CallSimOn (fun _ => True) host a b) : a = b :=
  eq_of_forall_callSim fun s => h s trivial

/-- A run out of an invocation ends at the invocation's empty frame. -/
theorem steps_invoke_frame {host : HostSemantics H} {t : Store H} {a : FuncAddr}
    {vs : List Runtime.Value} {c : Config H} (h : Steps host (invoke t a vs) c) :
    c = ⟨c.store, ⟨[], {}⟩, c.code⟩ := by
  have hf : c.frame = (invoke t a vs).frame :=
    (Sealed.steps h (by simpa using sealed_invoke vs a)).1
  obtain ⟨st, fr, cd⟩ := c
  have hfr : fr = ⟨[], {}⟩ := by simpa using hf
  rw [hfr]

/-- Under `CallSim`, every behaviour of `a` before the replacement is one after it. -/
theorem behaviours_replace_sub {host : HostSemantics H} {a b : FuncAddr} {s : Store H}
    (hsim : CallSim host a b s) (vs : List Runtime.Value) :
    behaviours host s a vs ⊆ behaviours host (s.replaceFunc a b) a vs := by
  obtain ⟨hfwd, -, hdiv⟩ := hsim
  rintro x (⟨c, r, hsteps, hcode, rfl⟩ | ⟨rfl, hd⟩)
  · have hrun : Steps host (invoke s a vs) ⟨c.store, ⟨[], {}⟩, result r⟩ := by
      rw [← hcode, ← steps_invoke_frame hsteps]
      exact hsteps
    exact Or.inl ⟨_, r, hfwd vs c.store r hrun, rfl, rfl⟩
  · exact Or.inr ⟨rfl, (hdiv vs).mp hd⟩

/-- Under `CallSim`, every behaviour of `a` after the replacement is one before it. -/
theorem behaviours_replace_sup {host : HostSemantics H} {a b : FuncAddr} {s : Store H}
    (hsim : CallSim host a b s) (vs : List Runtime.Value) :
    behaviours host (s.replaceFunc a b) a vs ⊆ behaviours host s a vs := by
  obtain ⟨-, hbwd, hdiv⟩ := hsim
  rintro x (⟨c, r, hsteps, hcode, rfl⟩ | ⟨rfl, hd⟩)
  · have hrun : Steps host (invoke (s.replaceFunc a b) a vs)
        ⟨c.store, ⟨[], {}⟩, result r⟩ := by
      rw [← hcode, ← steps_invoke_frame hsteps]
      exact hsteps
    obtain ⟨s₂, -, horig⟩ := hbwd vs c.store r hrun
    exact Or.inl ⟨_, r, horig, rfl, rfl⟩
  · exact Or.inr ⟨rfl, (hdiv vs).mpr hd⟩

/-- **The replacement is invisible at the replaced address**, from `CallSim` alone. -/
theorem behaviours_replace_at {host : HostSemantics H} {a b : FuncAddr} {s : Store H}
    (hsim : CallSim host a b s) (vs : List Runtime.Value) :
    behaviours host s a vs = behaviours host (s.replaceFunc a b) a vs :=
  Set.Subset.antisymm (behaviours_replace_sub hsim vs) (behaviours_replace_sup hsim vs)

/-- The `CallSimOn` form of `behaviours_replace_at`. -/
theorem behaviours_replace_at_reach {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hsim : CallSimOn Reach host a b) {s : Store H} (hs : Reach s)
    (vs : List Runtime.Value) :
    behaviours host s a vs = behaviours host (s.replaceFunc a b) a vs :=
  behaviours_replace_at (hsim s hs) vs

end Silmaril.Wasm.Replace
