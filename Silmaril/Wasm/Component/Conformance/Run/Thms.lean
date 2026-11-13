module

public import Silmaril.Wasm.Component.Conformance.Run.Defs
import Silmaril.Raw.Wasm.Component.Reference

/-!
# The runner's call driver is sound for the machine relation

`untilLoop_sound`: the labels `untilLoop` adds to its accumulator form a run of the copied
machine's relation `Steps` (at the oracle's profile) from the start configuration to the final
one. `callUntil_sound`: the trace of `callUntil` (the `invoke` host event, then `untilLoop`) is
a run from the configuration the call was issued in. These are the statements of the copied
`Machine.runTopLoop_sound` and `Embedder.callTop_sound` for the driver that stops at the call's
result (and may run a host program `resolve`, a `HostEvent.run`, for deferred host calls), so every verdict the runner derives from a call's trace is about a real run of the
reference machine (the oracle fixes one run among the admissible ones; nothing is claimed
about the others).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}
  (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)
  (pend : σ → Bool) (resolve : P E σ (Ret E))

/-- One more step in front of a sound remainder. -/
theorem steps_snoc_labels {prof : ProfileKind} {m m' m'' : Config E σ} {l : Label E σ}
    {acc tr ls : List (Label E σ)} (hl : ls = (l :: acc).reverse ++ tr)
    (hs : Step prof hr dispatch m l m') (htr : Steps prof hr dispatch m' tr m'') :
    ls = acc.reverse ++ (l :: tr) ∧ Steps prof hr dispatch m (l :: tr) m'' := by
  have h : (l :: acc).reverse ++ tr = acc.reverse ++ (l :: tr) := by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
  exact ⟨hl.trans h, .cons hs htr⟩

/-- The labels `untilLoop` adds to `acc` form a run from `m` to its final configuration. -/
def LoopSound (c : CallId) (n : Nat) (st : o.State) (m : Config E σ)
    (acc : List (Label E σ)) : Prop :=
  ∃ tr, (untilLoop hr dispatch X o pend resolve c n st m acc).labels = acc.reverse ++ tr ∧
    Steps o.prof hr dispatch m tr (untilLoop hr dispatch X o pend resolve c n st m acc).config

/-- A loop iteration that stops: nothing is added and the configuration is kept. -/
theorem loopSound_stop {c : CallId} {n : Nat} {st : o.State} {m : Config E σ}
    {acc : List (Label E σ)}
    (hl : (untilLoop hr dispatch X o pend resolve c n st m acc).labels = acc.reverse)
    (hc : (untilLoop hr dispatch X o pend resolve c n st m acc).config = m) :
    LoopSound hr dispatch X o pend resolve c n st m acc := by
  have hs : Steps o.prof hr dispatch m [] m := .refl _
  exact ⟨[], by rw [hl, List.append_nil], by rw [hc]; exact hs⟩

/-- A loop iteration that takes the step `l` to `m'` (a machine step or a host event) and
continues with a sound remainder. -/
theorem loopSound_cons {c : CallId} {n : Nat} {st st' : o.State} {m m' : Config E σ}
    {acc : List (Label E σ)} {l : Label E σ}
    (hu : untilLoop hr dispatch X o pend resolve c (n + 1) st m acc =
      untilLoop hr dispatch X o pend resolve c n st' m' (l :: acc))
    (hs : Step o.prof hr dispatch m l m')
    (ih : LoopSound hr dispatch X o pend resolve c n st' m' (l :: acc)) :
    LoopSound hr dispatch X o pend resolve c (n + 1) st m acc := by
  obtain ⟨tr, h₁, h₂⟩ := ih
  unfold LoopSound
  rw [hu]
  exact ⟨l :: tr, steps_snoc_labels hr dispatch h₁ hs h₂⟩

/-- A host event `ev` in front of a sound remainder (the tick and the deferred-resolution
arms of `untilLoop`); `none` from `hostStep?` stops the loop. -/
theorem loopSound_host {c : CallId} {n : Nat} {st : o.State} {m : Config E σ}
    {acc : List (Label E σ)} (ev : HostEvent E σ)
    (hu : ∀ l m', hostStep? hr ev m = some (l, m') →
      untilLoop hr dispatch X o pend resolve c (n + 1) st m acc =
        untilLoop hr dispatch X o pend resolve c n st m' (l :: acc))
    (hn : hostStep? hr ev m = none →
      (untilLoop hr dispatch X o pend resolve c (n + 1) st m acc).labels = acc.reverse ∧
      (untilLoop hr dispatch X o pend resolve c (n + 1) st m acc).config = m)
    (ih : ∀ m' acc', LoopSound hr dispatch X o pend resolve c n st m' acc') :
    LoopSound hr dispatch X o pend resolve c (n + 1) st m acc := by
  cases e : hostStep? hr ev m with
  | none =>
    have h : _ ∧ _ := hn e
    exact loopSound_stop hr dispatch X o pend resolve h.1 h.2
  | some p =>
    obtain ⟨l, m'⟩ := p
    have hs : Step o.prof hr dispatch m l m' := hostStep?_sound o.prof hr dispatch e
    exact loopSound_cons hr dispatch X o pend resolve (hu l m' e) hs (ih m' (l :: acc))

/-- **Soundness of `untilLoop`**. -/
theorem untilLoop_sound (c : CallId) (n : Nat) (st : o.State) (m : Config E σ)
    (acc : List (Label E σ)) : LoopSound hr dispatch X o pend resolve c n st m acc := by
  induction n generalizing st m acc with
  | zero => exact loopSound_stop hr dispatch X o pend resolve (by simp [untilLoop]) rfl
  | succ n ih =>
    show LoopSound hr dispatch X o pend resolve c (n + 1) st m acc
    by_cases hd : callDone c m = true
    · show LoopSound hr dispatch X o pend resolve c (n + 1) st m acc
      exact loopSound_stop hr dispatch X o pend resolve (by simp [untilLoop, hd])
        (by simp [untilLoop, hd])
    cases e : step? dispatch X (o.at st) m with
    | some p =>
      show LoopSound hr dispatch X o pend resolve c (n + 1) st m acc
      obtain ⟨l, st', m'⟩ := p
      have hu : untilLoop hr dispatch X o pend resolve c (n + 1) st m acc =
          untilLoop hr dispatch X o pend resolve c n st' m' (l :: acc) := by
        simp [untilLoop, hd, e]
      exact loopSound_cons hr dispatch X o pend resolve hu
        (step?_sound hr dispatch X (o.at st) e) (ih st' m' (l :: acc))
    | none =>
      show LoopSound hr dispatch X o pend resolve c (n + 1) st m acc
      by_cases w : wantsTick hr m = true
      · show LoopSound hr dispatch X o pend resolve c (n + 1) st m acc
        exact loopSound_host hr dispatch X o pend resolve .tick
          (fun l m' e' => by simp [untilLoop, hd, e, w, e'])
          (fun e' => by simp [untilLoop, hd, e, w, e']) (ih st)
      · show LoopSound hr dispatch X o pend resolve c (n + 1) st m acc
        by_cases hp : pend m.host = true
        · show LoopSound hr dispatch X o pend resolve c (n + 1) st m acc
          exact loopSound_host hr dispatch X o pend resolve (.run resolve)
            (fun l m' e' => by simp [untilLoop, hd, e, w, hp, e'])
            (fun e' => by simp [untilLoop, hd, e, w, hp, e']) (ih st)
        · show LoopSound hr dispatch X o pend resolve c (n + 1) st m acc
          exact loopSound_stop hr dispatch X o pend resolve (by simp [untilLoop, hd, e, w, hp])
            (by simp [untilLoop, hd, e, w, hp])

/-- **Soundness of `callUntil`**: its trace is a run of the machine from `m`. -/
theorem callUntil_sound {fuel : Nat} {c : CallId} {f : FuncId} {args : List Value.Val}
    {m : Config E σ} {r : RunResult E σ o.State}
    (h : callUntil hr dispatch X o pend resolve fuel c f args m = some r) :
    Steps o.prof hr dispatch m r.labels r.config := by
  unfold callUntil at h
  cases e : hostStep? hr (.invoke c f args) m with
  | none => simp [e] at h
  | some p =>
    obtain ⟨l, m'⟩ := p
    have hr' : untilLoop hr dispatch X o pend resolve c fuel o.state m' [l] = r := by simpa [e] using h
    obtain ⟨tr, h₁, h₂⟩ := untilLoop_sound hr dispatch X o pend resolve c fuel o.state m' [l]
    have hl : r.labels = l :: tr := by simpa [hr'] using h₁
    rw [hl, ← hr']
    exact .cons (hostStep?_sound o.prof hr dispatch e) h₂

end Silmaril.Wasm.Component.Conformance
