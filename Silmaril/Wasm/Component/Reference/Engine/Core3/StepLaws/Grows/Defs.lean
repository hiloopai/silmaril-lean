module

public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs

/-!
# Interpreter steps grow the store

Without any typing hypothesis, every step of the computable interpreter grows the store
(`Grows`, Engine/Core3/Grows.lean):

* `interpHead_grows`: the head step `SingleThreaded.Exec.interpHead o`. For the families whose
  head-step soundness lemmas need no `StoreOk`, through those lemmas and `Det.Head.grows`;
  directly for the reference family (which keeps the store) and the control family (which
  changes it only by allocating an exception at `throw`, `Store.addExn`, `Grows.addExn`);
* `stepI_grows`: the interpreter step `stepI o = step? (interpHead o)`, by well-founded
  induction on the driver (`step?_cons`, `Drv.layer`): the trap and `throw_ref` bubbling
  branches keep the store, the head branch is `interpHead_grows`, and the `label`, `handler`
  and `frame` branches are the induction hypothesis;
* `internal_grows`: an internal step of the concrete engine, `internalC (stepI o)`.

With `Grows.extends` this is the `internal_extends` law of `CoreEngine.Lawful`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

namespace StepLaws

/-! ## The reference and control families -/

/-- The reference family keeps the store. -/
theorem refStepRev?_store {s : Store H} {f : Frame} {rvs : List Val} {e : Admin} {k : Nat}
    {c : Config H} (h : SingleThreaded.Exec.refStepRev? s f rvs e = some (k, c)) :
    c.store = s := by
  unfold SingleThreaded.Exec.refStepRev? at h
  split at h <;> (try split at h) <;> first | (cases h; rfl) | cases h

theorem referenceStep?_store {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame}
    {vs : List Val} {e : Admin} {k : Nat} {c : Config H}
    (h : SingleThreaded.Exec.referenceStep? o s f vs e = some (k, c)) : c.store = s :=
  refStepRev?_store h

/-- `call_ref` at the head keeps the store. -/
theorem callRef?_store {s : Store H} {f : Frame} {vs : List Val} {k : Nat} {c : Config H}
    (h : SingleThreaded.Exec.Ctl.callRef? s f vs = some (k, c)) : c.store = s := by
  unfold SingleThreaded.Exec.Ctl.callRef? at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

theorem block?_store {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {mk : List Validation.CValType → List Validation.CValType → List Val → Admin} {k : Nat}
    {c : Config H} (h : SingleThreaded.Exec.Ctl.block? s f vs bt mk = some (k, c)) :
    c.store = s := by
  obtain ⟨_, _, _, _, _, rfl⟩ := SingleThreaded.Exec.Ctl.block?_sound h
  rfl

/-- Plain control instructions keep the store, except `throw`, which allocates an exception. -/
theorem plainStep?_grows {cast : Store H → Ref → Validation.CRefType → Bool} {s : Store H}
    {f : Frame} {vs : List Val} {i : Instr} {k : Nat} {c : Config H}
    (h : SingleThreaded.Exec.Ctl.plainStep? cast s f vs i = some (k, c)) : Grows s c.store := by
  unfold SingleThreaded.Exec.Ctl.plainStep? at h
  split at h
  all_goals try first
    | (rw [block?_store h]; exact Grows.refl _)
  all_goals repeat' split at h
  all_goals first
    | (cases h; exact Grows.refl _)
    | (cases h; exact Grows.addExn _ _)
    | cases h

theorem controlStep?_grows {cast : Store H → Ref → Validation.CRefType → Bool}
    {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {k : Nat} {c : Config H}
    (h : SingleThreaded.Exec.controlStep? cast o s f vs e = some (k, c)) : Grows s c.store := by
  unfold SingleThreaded.Exec.controlStep? at h
  split at h
  · rw [callRef?_store h]; exact Grows.refl _
  · split at h
    · exact plainStep?_grows h
    · cases h

end StepLaws

/-- The interpreter's head step grows the store. -/
theorem interpHead_grows {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame}
    {vs : List Val} {e : Admin} {k : Nat} {c : Config H}
    (h : SingleThreaded.Exec.interpHead o s f vs e = some (k, c)) : Grows s c.store := by
  unfold SingleThreaded.Exec.interpHead at h
  split at h
  · exact Head.grows (SingleThreaded.Exec.parametricStep?_sound h).2
  · exact Head.grows (SingleThreaded.Exec.numericStep?_sound h).2
  · exact Head.grows (SingleThreaded.Exec.vectorStep?_sound h).2
  · exact Head.grows (SingleThreaded.Exec.variableStep?_sound h).2
  · exact Head.grows (SingleThreaded.Exec.tableStep?_sound h).2
  · exact Head.grows (SingleThreaded.Exec.memoryStep?_sound h).2
  · rw [StepLaws.referenceStep?_store h]; exact Grows.refl _
  · rcases SingleThreaded.Exec.Interp.orElse_some h with h | h
    · exact Head.grows (SingleThreaded.Exec.aggNewStep?_sound h).2
    · exact Head.grows (SingleThreaded.Exec.aggAccessStep?_sound h).2
  · rcases SingleThreaded.Exec.Interp.orElse_some h with h | h
    · exact StepLaws.controlStep?_grows h
    · exact Head.grows (SingleThreaded.Exec.adminStep?_sound h).2

namespace StepLaws

/-! ## The driver -/

/-- A driver step on a smaller body `c₀` under the same store, wrapped by `g`, which keeps the
store: the third case of `step?_store`. -/
theorem step?_store_body {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
    {c c' c₀ : Config H} {g : Config H → Config H}
    (h : (SingleThreaded.Exec.step? head c₀).map g = some c')
    (hg : ∀ c₁, (g c₁).store = c₁.store) (hc₀ : c₀.store = c.store)
    (hlt : sizeOf c₀.code < sizeOf c.code) :
    c'.store = c.store ∨
      (∃ f vs e k c₀, head c.store f vs e = some (k, c₀) ∧ c'.store = c₀.store) ∨
      ∃ c₀ c₁ : Config H, sizeOf c₀.code < sizeOf c.code ∧ c₀.store = c.store ∧
        SingleThreaded.Exec.step? head c₀ = some c₁ ∧ c'.store = c₁.store := by
  obtain ⟨c₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
  exact .inr (.inr ⟨c₀, c₁, hlt, hc₀, h₁, hg c₁⟩)

open SingleThreaded.Exec in
/-- Where the store after one driver step comes from: the bubbling branches keep it, the head
branch takes it from the head step, and the `label`, `handler` and `frame` branches take it
from a driver step on a smaller body under the same store. -/
theorem step?_store {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
    {c c' : Config H} (h : SingleThreaded.Exec.step? head c = some c') :
    c'.store = c.store ∨
      (∃ f vs e k c₀, head c.store f vs e = some (k, c₀) ∧ c'.store = c₀.store) ∨
      ∃ c₀ c₁ : Config H, sizeOf c₀.code < sizeOf c.code ∧ c₀.store = c.store ∧
        SingleThreaded.Exec.step? head c₀ = some c₁ ∧ c'.store = c₁.store := by
  rcases hs : SingleThreaded.splitVals c.code with ⟨vs, _ | ⟨e, rest⟩⟩
  · rw [SingleThreaded.Exec.step?_nil hs] at h; cases h
  have hlt : sizeOf e < sizeOf c.code := SingleThreaded.Exec.Drv.sizeOf_lt_of_split hs
  simp only [step?_cons hs, Drv.layer] at h
  split at h
  · split at h <;> cases h
    exact .inl rfl
  split at h
  · split at h <;> cases h
    exact .inl rfl
  split at h
  · rename_i k c₀ hh
    cases h
    exact .inr (.inl ⟨_, _, _, k, c₀, hh, rfl⟩)
  split at h
  · exact step?_store_body h (fun _ => rfl) rfl (lt_trans Drv.sizeOf_label_body hlt)
  · exact step?_store_body h (fun _ => rfl) rfl (lt_trans Drv.sizeOf_handler_body hlt)
  · exact step?_store_body h (fun _ => rfl) rfl (lt_trans Drv.sizeOf_frame_body hlt)
  · cases h

/-- The driver grows the store whenever its head step does. -/
theorem step?_grows_aux {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
    (hhead : ∀ s f vs e k c, head s f vs e = some (k, c) → Grows s c.store) :
    ∀ (n : Nat) (c c' : Config H), sizeOf c.code = n →
      SingleThreaded.Exec.step? head c = some c' → Grows c.store c'.store := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c c' hn h
  rcases step?_store h with e | ⟨f, vs, e, k, c₀, hh, e'⟩ | ⟨c₀, c₁, hlt, hs, h₁, e'⟩
  · rw [e]; exact Grows.refl _
  · rw [e']; exact hhead _ _ _ _ _ _ hh
  · rw [e', ← hs]; exact ih _ (hn ▸ hlt) c₀ c₁ rfl h₁

end StepLaws

/-- The interpreter step grows the store. -/
theorem stepI_grows {o : SingleThreaded.GrowOracle} {c c' : Config H}
    (h : SingleThreaded.Exec.stepI o c = some c') : Grows c.store c'.store :=
  StepLaws.step?_grows_aux (fun _ _ _ _ _ _ hh => interpHead_grows hh) _ c c' rfl h

/-- An internal step of the concrete engine grows the store. -/
theorem internal_grows {o : SingleThreaded.GrowOracle} {s s' : Store H}
    {t t' : SingleThreaded.Thread}
    (h : SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some (s', t')) :
    Grows s s' := by
  unfold SingleThreaded.internalC at h
  obtain ⟨c', hc', e⟩ := Option.map_eq_some_iff.mp h
  cases e
  have := stepI_grows hc'
  rwa [SingleThreaded.Thread.config_store] at this

end Silmaril.Wasm.Component.Engine.Core3
