module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Extends.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Agreement.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Store.Defs

/-!
# Typed statuses of the single-threaded machine

Facts about the status `SingleThreaded.status o s t` of a typed thread
(`SingleThreaded.ThreadOk s t ts`, the spec's `Config_ok`) that the typed laws of the concrete
engine need:

* `returned_values_flat`: returned values of a thread typed at numeric result types are flat,
  of those types (as in `SingleThreaded.status_flat`);
* `callout_args_typed`: the arguments of a callout are typed by the parameter types of a host
  function of the store with the callout's host code. The proof runs Core progress
  (`Config.progress`) with the host semantics `argHost`, which diverges exactly on arguments
  typed by the parameters of such a function; `argHost` satisfies the host contract `HostOk`,
  so a typed callout steps by the host rule, whose premise is the claim;
* `resume_trap_typed`, `resume_trap_extend`: resuming a callout with a trap gives a typed thread.
  The resumed code is the result of the host rule for the host semantics `trapHost`, which
  returns a trap; `trapHost` satisfies `HostOk`, so Core preservation (`Step.preservation`) types
  it; store extension (`configOk_extend`) then moves it to any extended typed store;
* `flatStatus_eq_returned_values`, `flatStatus_eq_callout'`: inversion of the flat view.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3.Typed

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-! ## Flat values -/

/-! ## Callout arguments -/

/-- The host semantics that diverges exactly on arguments typed by the parameter types of a
function of the store with the given host code. -/
def argHost : HostSemantics H := fun h s vs out =>
  out = .diverged ∧ ∃ fi ∈ s.funcs, fi.code = .host h ∧ ∃ ps rs, Expand fi.type (.func ps rs) ∧
    List.Forall₂ (ValOk s) vs ps.toList

/-! ## Trap resumption -/

/-- The host semantics that returns a trap and leaves the store unchanged. -/
def trapHost : HostSemantics H := fun _ s _ out => out = .returned s .trap

/-! ## The flat view -/

end Silmaril.Wasm.Component.Engine.Core3.Typed

namespace Silmaril.Wasm.Component.Engine.Core3.Typed

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
variable {H : Type}

/-- Values typed at numeric types are flat, of those types. -/
theorem mapM_toFlat?_of_forall₂ {s : Store H} {vs : List Val} {ns : List NumType}
    (h : List.Forall₂ (ValOk s) vs (ns.map Silmaril.Wasm.Validation.Ty.num)) :
    ∃ fvs, vs.mapM SingleThreaded.toFlat? = some fvs ∧ fvs.map (·.type) = ns :=
  SingleThreaded.flat_of_typed (Δ := {}) h (ResultSub.refl _ _)

/-- Returned values of a thread typed at numeric result types are flat, of those types. -/
theorem returned_values_flat {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {ns : List NumType} {vs : List Val} (_hs : StoreOk s)
    (ht : SingleThreaded.ThreadOk s t (ns.map Silmaril.Wasm.Validation.Ty.num))
    (h : SingleThreaded.status o s t = .returned (.values vs)) :
    ∃ fvs, vs.mapM SingleThreaded.toFlat? = some fvs ∧ fvs.map (·.type) = ns := by
  obtain ⟨C, -, hadm⟩ := ht
  rw [SingleThreaded.status_returned_values h] at hadm
  obtain ⟨ts', hvs, hsub⟩ := SingleThreaded.AdminsOk.vals_num_aux hadm _ rfl (ns.map Silmaril.Wasm.Validation.Ty.num)
    (fun u hu => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hu
      exact .inl ⟨n, rfl⟩)
    (List.forall₂_same.mpr fun _ _ => .inl rfl)
  exact SingleThreaded.flat_of_typed (Δ := {}) hvs
    (SingleThreaded.botLe_resultSub (by simpa using hsub))

theorem argHost_ok : HostOk (argHost (H := H)) := by
  intro s fi h vs ps rs _ hfi hc he hvs
  refine ⟨⟨.diverged, rfl, fi, hfi, hc, ps, rs, he, hvs⟩, fun out hout => ?_⟩
  obtain ⟨rfl, -⟩ := hout
  trivial

/-- A thread at a callout is not terminal. -/
theorem status_callout_not_terminal {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {hc : H} {args : List Val}
    (h : SingleThreaded.status o s t = .callout hc args) {r : Result}
    (hr : (t.config s).code = r.toAdmin) : False := by
  unfold SingleThreaded.status at h
  dsimp only at h
  by_cases h1 : ∃ vs, (t.config s).code = vals vs
  · rw [dite_eq_left h1] at h
    cases h
  rw [dite_eq_right h1] at h
  by_cases h2 : (t.config s).code = [.trap]
  · rw [ite_eq_left h2] at h
    cases h
  by_cases h3 : ∃ a, (t.config s).code = throwing a
  · rw [ite_eq_right h2, ite_eq_left h3] at h
    cases h
  cases r with
  | values vs => exact h1 ⟨vs, hr⟩
  | throw a => exact h3 ⟨a, hr⟩
  | trap => exact h2 hr

/-- The arguments of a callout of a typed thread are typed by the parameter types of a host
function of the store with the callout's host code. -/
theorem callout_args_typed {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {ts : List CValType} {hc : H} {args : List Val}
    (_hs : StoreOk s) (ht : SingleThreaded.ThreadOk s t ts)
    (h : SingleThreaded.status o s t = .callout hc args) :
    ∃ fi ∈ s.funcs, fi.code = .host hc ∧ ∃ ps rs, Expand fi.type (.func ps rs) ∧
      List.Forall₂ (ValOk s) args ps.toList := by
  rcases Config.progress (P := SingleThreaded.profile o) argHost_ok ht with ⟨r, hr⟩ | ⟨c', hc'⟩
  · exact (status_callout_not_terminal h hr).elim
  · rcases (SingleThreaded.step_iff o argHost s t c').mp hc' with
      ⟨s', f', code', -, hi⟩ | ⟨E, a, h', args', hd, hh⟩
    · exact absurd hi (SingleThreaded.callout_no_internal h _)
    · obtain ⟨E₀, a₀, hd₀⟩ := SingleThreaded.status_callout_inv h
      rw [hd₀] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hd
      rcases hh with ⟨s'', r, ⟨hout, -⟩, -⟩ | ⟨⟨-, hfi⟩, -⟩
      · cases hout
      · exact hfi

theorem trapHost_ok : HostOk (trapHost (H := H)) := by
  intro s fi h vs ps rs hs _ _ _ _
  refine ⟨⟨_, rfl⟩, fun out hout => ?_⟩
  subst hout
  exact ⟨hs, Extend.refl hs, trivial⟩

/-- Resuming a callout of a typed thread with a trap gives a typed thread. -/
theorem resume_trap_typed {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {ts : List CValType} {hc : H} {args : List Val}
    (ht : SingleThreaded.ThreadOk s t ts) (h : SingleThreaded.status o s t = .callout hc args) :
    SingleThreaded.ThreadOk s (SingleThreaded.resume s t .trap) ts := by
  obtain ⟨E, a, hd⟩ := SingleThreaded.status_callout_inv h
  have hst : Step (SingleThreaded.profile o) trapHost (t.config s)
      ((SingleThreaded.resumeResult s t .trap).config s) :=
    (SingleThreaded.step_iff o trapHost s t _).mpr
      (.inr ⟨E, a, hc, args, hd, .inl ⟨s, .trap, rfl, rfl⟩⟩)
  have hok := (Step.preservation trapHost_ok ht hst).1
  have e : SingleThreaded.resume s t .trap = SingleThreaded.resumeResult s t .trap := by
    simp only [SingleThreaded.resume, SingleThreaded.resumeResult, hd,
      SingleThreaded.CallResult.toAdmin, Result.toAdmin]
  rw [e]
  exact hok

/-- Resuming a callout of a typed thread with a trap, at an extended typed store, gives a typed
thread. -/
theorem resume_trap_extend {o : SingleThreaded.GrowOracle} {s s' : Store H}
    {t : SingleThreaded.Thread} {ts : List CValType} {hc : H} {args : List Val}
    (hs : StoreOk s) (ht : SingleThreaded.ThreadOk s t ts)
    (h : SingleThreaded.status o s t = .callout hc args) (he : Extend s s') (hs' : StoreOk s') :
    SingleThreaded.ThreadOk s' (SingleThreaded.resume s' t .trap) ts := by
  obtain ⟨E, a, hd⟩ := SingleThreaded.status_callout_inv h
  have h₁ := resume_trap_typed ht h
  have hr : SingleThreaded.resume s t .trap = .active (t.config s).frame (E.fill [.trap]) := by
    simp only [SingleThreaded.resume, hd, SingleThreaded.CallResult.toAdmin]
  have hr' : SingleThreaded.resume s' t .trap = .active (t.config s).frame (E.fill [.trap]) := by
    have hc' := SingleThreaded.Thread.config_extend he t hd
    have hd' := SingleThreaded.decompose?_extend he _ hd
    simp only [SingleThreaded.resume, hc', hd', SingleThreaded.CallResult.toAdmin]
  rw [hr] at h₁
  rw [hr']
  exact configOk_extend hs he hs' h₁

theorem flatStatus_eq_returned_values {st : SingleThreaded.Status H} {vs : List FlatValue}
    (h : flatStatus st = .returned (.values vs)) :
    ∃ vs', st = .returned (.values vs') ∧ vs'.mapM SingleThreaded.toFlat? = some vs := by
  rcases st with _ | (vs' | _) | ⟨hc', args'⟩ | _
  · cases h
  · simp only [flatStatus] at h
    split at h
    · rename_i fvs e
      cases h
      exact ⟨vs', rfl, e⟩
    · cases h
  · cases h
  · simp only [flatStatus] at h
    split at h <;> cases h
  · cases h

theorem flatStatus_eq_callout' {st : SingleThreaded.Status H} {hc : H} {args : List FlatValue}
    (h : flatStatus st = .callout hc args) :
    ∃ args', st = .callout hc args' ∧ args'.mapM SingleThreaded.toFlat? = some args := by
  rcases st with _ | (vs' | _) | ⟨hc', args'⟩ | _
  · cases h
  · simp only [flatStatus] at h
    split at h <;> cases h
  · cases h
  · simp only [flatStatus] at h
    split at h
    · rename_i fargs e
      cases h
      exact ⟨args', rfl, e⟩
    · cases h
  · cases h

end Silmaril.Wasm.Component.Engine.Core3.Typed
