module

public import Silmaril.Wasm.Spec.Component.RefMulti.Defs

@[expose] public section

/-!
# Several export calls on one reference instance: proofs

* `refTraces_sub_refMulti`: every one-call trace of `refSem` is a multi-call trace;
* `refMulti_short`: a multi-call trace with at most two events is a one-call trace;
* `refTraces_eq_short`: `refSem` is exactly the restriction of `refMultiSem` to traces of
  length at most two (the per-call `exportBehaviours` are the one-call prefixes);
* `doneEvents_mem`, `RunCalls.append`: the resolved calls of a multi-call run are traces, and
  runs compose.

New proofs.
-/

namespace Silmaril.Wasm.Spec.Component

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component (Calls)
open Silmaril.Wasm.Component.Runtime (FuncId CallId)
open Silmaril.Wasm.Component.Machine (Config)

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}
variable {prof : Silmaril.Wasm.Component.ProfileKind} {h : Host E σ} {σ0 : σ} {X : CIface}

/-- A prefix of length at most `n` is a prefix of the first `n` elements. -/
theorem prefix_take_of_length {α : Type} {t l : List α} {n : ℕ} (ht : t <+: l)
    (hn : t.length ≤ n) : t <+: l.take n := by
  have e : t = l.take t.length := List.prefix_iff_eq_take.1 ht
  have e' : l.take t.length = (l.take n).take t.length := by
    rw [List.take_take, Nat.min_eq_left hn]
  exact e ▸ e' ▸ List.take_prefix _ _

/-- A one-call trace of `refSem` is a multi-call trace. -/
theorem refTraces_sub_refMulti (p : RefProg E X) {t : List (CEvent X)}
    (ht : t ∈ refTraces prof h σ0 p) : t ∈ refMultiTraces prof h σ0 p := by
  rcases ht with rfl | ⟨j, a, rfl⟩ | ⟨j, a, b, hb, rfl⟩
  · exact ⟨[], .inl rfl, List.prefix_refl _⟩
  · exact ⟨_, .inr (.inl ⟨j, a, rfl⟩), List.prefix_refl _⟩
  · refine ⟨_, ?_, List.prefix_refl _⟩
    rcases hb with ⟨m₁, inst, es, f, hi, hf, hc⟩ | ⟨rfl, hi⟩ | ⟨rfl, hi⟩
    · have hu : [Event.call j a, Event.ret j b] ∈ lastWords prof h p.names es m₁ 0 :=
        .inr (.inr ⟨j, a, f, b, hf, hc, rfl⟩)
      exact .inr (.inr (.inl ⟨m₁, inst, es, [], m₁, _, hi, .nil _ _, hu, rfl⟩))
    · exact .inr (.inr (.inr (.inl ⟨j, a, hi, rfl⟩)))
    · exact .inr (.inr (.inr (.inr ⟨j, a, hi, rfl⟩)))

/-- The first resolved call of a run is a one-call trace. -/
theorem runCalls_first (p : RefProg E X) {m₀ : Config E σ} {inst} {es : List (String × FuncId)}
    (hi : InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args)
    {d : DoneCall X} {ds : List (DoneCall X)} {mₙ : Config E σ}
    (hr : RunCalls prof h p.names es m₀ 0 (d :: ds) mₙ) :
    d.events ∈ refTraces prof h σ0 p := by
  cases hr with
  | cons hf hc _ =>
    have hb : Outcome.returns d.res ∈ callBehaviours prof h m₀ ⟨0⟩ _ d.args :=
      .inl ⟨_, _, hc, rfl⟩
    exact .inr (.inr ⟨d.exp, d.args, _, .inl ⟨m₀, inst, es, _, hi, hf, hb⟩, rfl⟩)

/-- The words after the instantiation, at most two events long, are one-call traces. -/
theorem lastWords_short (p : RefProg E X) {m₀ : Config E σ} {inst} {es : List (String × FuncId)}
    (hi : InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args)
    {u : List (CEvent X)} (hu : u ∈ lastWords prof h p.names es m₀ 0) :
    u ∈ refTraces prof h σ0 p := by
  rcases hu with rfl | ⟨j, a, rfl⟩ | ⟨j, a, f, b, hf, hb, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨j, a, rfl⟩)
  · exact .inr (.inr ⟨j, a, b, .inl ⟨m₀, inst, es, f, hi, hf, hb⟩, rfl⟩)

/-- The instantiation case of `refMulti_short`. -/
theorem refMulti_short_inst (p : RefProg E X) {m₀ : Config E σ} {inst}
    {es : List (String × FuncId)}
    (hi : InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args)
    {ds : List (DoneCall X)} {mₙ : Config E σ} (hr : RunCalls prof h p.names es m₀ 0 ds mₙ)
    {u t : List (CEvent X)} (hu : u ∈ lastWords prof h p.names es mₙ ds.length)
    (ht : t <+: doneEvents ds ++ u) (hl : t.length ≤ 2) : t ∈ refTraces prof h σ0 p := by
  cases ds with
  | nil =>
    have hm : mₙ = m₀ := by cases hr; rfl
    have hu' : u ∈ refTraces prof h σ0 p := lastWords_short p hi (hm ▸ hu)
    exact (refTraces_good prof h σ0 p).of_prefix hu' ht
  | cons d ds =>
    have hd : d.events ∈ refTraces prof h σ0 p := runCalls_first p hi hr
    have ht' : t <+: (doneEvents (d :: ds) ++ u).take 2 := prefix_take_of_length ht hl
    have e : (doneEvents (d :: ds) ++ u).take 2 = d.events := by
      simp [doneEvents, DoneCall.events]
    exact (refTraces_good prof h σ0 p).of_prefix hd (e ▸ ht')

/-- A multi-call trace with at most two events is a one-call trace. -/
theorem refMulti_short (p : RefProg E X) {t : List (CEvent X)}
    (ht : t ∈ refMultiTraces prof h σ0 p) (hl : t.length ≤ 2) : t ∈ refTraces prof h σ0 p := by
  obtain ⟨w, hw, hp⟩ := ht
  have G := refTraces_good prof h σ0 p
  rcases hw with rfl | ⟨j, a, rfl⟩ | ⟨m₀, inst, es, ds, mₙ, u, hi, hr, hu, rfl⟩ |
      ⟨j, a, hi, rfl⟩ | ⟨j, a, hi, rfl⟩
  · exact G.of_prefix G.nil_mem hp
  · exact G.of_prefix (.inr (.inl ⟨j, a, rfl⟩)) hp
  · exact refMulti_short_inst p hi hr hu hp hl
  · exact G.of_prefix (.inr (.inr ⟨j, a, _, .inr (.inl ⟨rfl, hi⟩), rfl⟩)) hp
  · exact G.of_prefix (.inr (.inr ⟨j, a, _, .inr (.inr ⟨rfl, hi⟩), rfl⟩)) hp

/-- **`refSem` is the one-call restriction of `refMultiSem`.** -/
theorem refTraces_eq_short (p : RefProg E X) :
    refTraces prof h σ0 p = {t | t ∈ refMultiTraces prof h σ0 p ∧ t.length ≤ 2} := by
  ext t
  constructor
  · intro ht
    have hl : t.length ≤ 2 := by
      rcases ht with rfl | ⟨j, a, rfl⟩ | ⟨j, a, b, -, rfl⟩ <;> simp
    exact ⟨refTraces_sub_refMulti p ht, hl⟩
  · exact fun ⟨ht, hl⟩ => refMulti_short p ht hl

/-- Runs of resolved calls compose. -/
theorem RunCalls.append {names : X.Exp → String} {es : List (String × FuncId)}
    {m₁ m₂ m₃ : Config E σ} {k : ℕ} {ds₁ ds₂ : List (DoneCall X)}
    (h₁ : RunCalls prof h names es m₁ k ds₁ m₂)
    (h₂ : RunCalls prof h names es m₂ (k + ds₁.length) ds₂ m₃) :
    RunCalls prof h names es m₁ k (ds₁ ++ ds₂) m₃ := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hf hc _ ih =>
    exact .cons hf hc (ih (by simpa [Nat.add_assoc, Nat.add_comm 1] using h₂))

/-- The events of the resolved calls of a multi-call run are a trace. -/
theorem doneEvents_mem (p : RefProg E X) {m₀ : Config E σ} {inst}
    {es : List (String × FuncId)}
    (hi : InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args)
    {ds : List (DoneCall X)} {mₙ : Config E σ} (hr : RunCalls prof h p.names es m₀ 0 ds mₙ) :
    doneEvents ds ∈ refMultiTraces prof h σ0 p :=
  ⟨doneEvents ds ++ [], .inr (.inr (.inl ⟨m₀, inst, es, ds, mₙ, [], hi, hr, .inl rfl, rfl⟩)),
    by simp⟩

end Silmaril.Wasm.Spec.Component
