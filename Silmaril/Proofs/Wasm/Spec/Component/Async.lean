module

public import Silmaril.Wasm.Spec.Component.Async.Defs
public import Silmaril.Wasm.Spec.Temporal.Thms

@[expose] public section

/-!
# Streams and async calls: proofs

Synchronous events read as async events carry no stream traffic (`mapP_not_closes`,
`mapP_not_writes`), so synchronous programs satisfy the stream logics
(`syncToAsync_streamSafe`, `syncToAsync_closedExactlyOnce`). Summary in
`Silmaril.Wasm.Spec.Component.Async.Thms`.
-/

namespace Silmaril.Wasm.Spec.Component

variable {X : CIface}

/-- An embedded synchronous event closes no end. -/
theorem mapP_not_closes (ev : CEvent X) (e : ℕ) :
    ¬ AEvent.Closes e (Event.mapP id AMsg.args AOut.out ev) := by
  rcases ev with (⟨i, a⟩ | ⟨i, r⟩) | (⟨i, a⟩ | ⟨i, r⟩) <;>
    simp [Event.mapP, SideEv.mapP, AEvent.Closes, AEvent.msg?, AMsg.closeEnd?]

/-- An embedded synchronous event writes no end. -/
theorem mapP_not_writes (ev : CEvent X) (e : ℕ) :
    ¬ AEvent.Writes e (Event.mapP id AMsg.args AOut.out ev) := by
  rcases ev with (⟨i, a⟩ | ⟨i, r⟩) | (⟨i, a⟩ | ⟨i, r⟩) <;>
    simp [Event.mapP, SideEv.mapP, AEvent.Writes, AEvent.msg?, AMsg.writeEnd?]

/-- The traces of an embedded synchronous program are embedded synchronous traces. -/
theorem mem_syncToAsync {S : Semantics CFn (List RVal) Outcome} {Y : CIface} (p : S.Prog Y)
    {t : List (AEvent (Y.map id))}
    (ht : t ∈ (syncToAsync S).traces (PushProg.ofProg (τ := id) p)) :
    ∃ u ∈ S.traces p, t = u.map (Event.mapP id AMsg.args AOut.out) := by
  obtain ⟨u, hu, rfl⟩ := ht
  exact ⟨u, hu, rfl⟩

/-- **Synchronous programs are stream safe.** -/
theorem syncToAsync_streamSafe (S : Semantics CFn (List RVal) Outcome) {Y : CIface}
    (p : S.Prog Y) : Models streamSafe (syncToAsync S) (PushProg.ofProg p) () := by
  rw [models_iff]
  intro t ht h ev r hsplit e he
  obtain ⟨u, -, rfl⟩ := mem_syncToAsync p ht
  have hmem : ev ∈ u.map (Event.mapP id AMsg.args AOut.out) := by rw [hsplit]; simp
  obtain ⟨ev₀, -, rfl⟩ := List.mem_map.1 hmem
  exact absurd he (not_or.2 ⟨mapP_not_closes ev₀ e, mapP_not_writes ev₀ e⟩)

/-- **Synchronous programs satisfy "closed exactly once"** (vacuously: they write no end). -/
theorem syncToAsync_closedExactlyOnce (S : Semantics CFn (List RVal) Outcome) {Y : CIface}
    (p : S.Prog Y) : Models closedExactlyOnce (syncToAsync S) (PushProg.ofProg p) () := by
  rw [models_iff]
  rintro t ⟨ht, -⟩ e ⟨ev, hev, hw⟩
  obtain ⟨u, -, rfl⟩ := mem_syncToAsync p ht
  obtain ⟨ev₀, -, rfl⟩ := List.mem_map.1 hev
  exact absurd hw (mapP_not_writes ev₀ e)

end Silmaril.Wasm.Spec.Component
