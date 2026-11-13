module

public import Silmaril.Wasm.Jco.Async.Frame.Defs
public import Silmaril.Wasm.Jco.Async.Thms
import Silmaril.Proofs.Wasm.Jco.Async.Frame

/-!
# A closed form of the async specification: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.Frame`.

* **`specCall_withStore`**, `spec_withStore` (the frame lemma): next to the async store, the C
  convention is `RM.liftFst` of the C convention over `M`. `M`'s calls, its allocator and its
  memory leave the store as it was.
* `asyncStore_result`: in `asyncStore st ws` the fresh task `st.next` holds the values `ws`. The
  fallback in its definition is never taken (`asyncStore_step`).
* **`aspecCall_sync`**, **`aspecCall_async`**, `aspec_closed`: the closed form of `aspec`. A
  synchronous function is the lifted C convention. An async one is the C convention over `M`
  alongside the store update `asyncPost`: the runtime's task is started, its `task.return`
  succeeds on the fresh task, and the caller reads back exactly `M`'s result.
* **`awrap_closed`**: so, for a conforming module, the async construction behaves as
  `aspecClosed`. `awrap_ok`: every value it returns is a value of `M`'s own C convention, from
  the first component of the state, ending in the state `M` ends in. `awrap_store`: after an
  async function the store is `asyncStore` of the values returned.
* `aspecCall_async_inMem`: an async function with a `string` or `list<u8>` result never returns.
  It traps once `M` has returned, since `task.return` of the async fragment carries no memory
  results.

Divergence is not covered (`RM` relates states to terminating outcomes).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store startSync)

variable (M : CoreInst)

/-- **The frame lemma**: next to the store, the C convention is the lifted C convention. -/
theorem specCall_withStore (md : Meta) (sig : Sig) (vs : List PVal) :
    md.specCall M.withStore sig vs = RM.liftFst (md.specCall M sig vs) :=
  Silmaril.Proofs.Wasm.Jco.Async.Frame.specCall_withStore M md sig vs

/-- The frame lemma, by name. -/
theorem spec_withStore (md : Meta) (name : String) (vs : List PVal) :
    md.spec M.withStore name vs = RM.liftFst (md.spec M name vs) := by
  unfold Meta.spec
  cases md.world.find? (·.name == name) with
  | none => exact (Silmaril.Proofs.Wasm.Jco.Async.Frame.liftFst_fail).symm
  | some sig => exact specCall_withStore M md sig vs

/-- `task.return` on the fresh task succeeds; the store it leaves is `asyncStore`. -/
theorem asyncStore_step (st : Store) (ws : List Val) :
    Silmaril.Wasm.Component.Async.step (startSync st).1 (.taskReturn st.next ws) =
      some (asyncStore st ws, .unit) := by
  obtain ⟨st', h, -, e⟩ := Silmaril.Proofs.Wasm.Jco.Async.Frame.step_fresh st ws
  rw [h, e]

/-- In `asyncStore st ws` the fresh task holds the values `ws`. -/
theorem asyncStore_result (st : Store) (ws : List Val) :
    ((asyncStore st ws).tasks st.next).result = some ws := by
  obtain ⟨st', -, h, e⟩ := Silmaril.Proofs.Wasm.Jco.Async.Frame.step_fresh st ws
  rw [e, h]

/-- What `RM.alongside` returns. -/
theorem alongside_ok {σ τ α : Type} (m : RM σ α) (f : α → τ → Option τ) (s s' : σ × τ) (a : α) :
    RM.alongside m f s (.ok a s') ↔ m s.1 (.ok a s'.1) ∧ f a s.2 = some s'.2 := Iff.rfl

/-- **A synchronous function**: the lifted C convention. -/
theorem aspecCall_sync (md : AMeta) (sig : Sig) (vs : List PVal) :
    aspecCall M md ⟨sig, none⟩ vs = RM.liftFst (md.sync.specCall M sig vs) :=
  Silmaril.Proofs.Wasm.Jco.Async.Frame.aspecCall_sync M md sig vs

/-- **An async function**: the C convention over `M`, alongside the runtime's update of the
store. -/
theorem aspecCall_async (md : AMeta) (sig : Sig) (sty : Style) (vs : List PVal) :
    aspecCall M md ⟨sig, some sty⟩ vs = RM.alongside (md.sync.specCall M sig vs) asyncPost :=
  Silmaril.Proofs.Wasm.Jco.Async.Frame.aspecCall_async M md sig sty vs

/-- **The closed form of `aspec`.** -/
theorem aspec_closed (md : AMeta) : aspec M md = aspecClosed M md :=
  Silmaril.Proofs.Wasm.Jco.Async.Frame.aspec_closed M md

/-- **The async construction in closed form.** -/
theorem awrap_closed (md : AMeta) (hC : md.sync.Conforms M) (name : String) (vs : List PVal) :
    (awrap md).callExport M name vs = aspecClosed M md name vs := by
  rw [awrap_correct M md hC, aspec_closed]

theorem find_sync (md : AMeta) (name : String) :
    md.sync.world.find? (·.name == name) = (md.world.find? (·.sig.name == name)).map (·.sig) := by
  simp only [AMeta.sync, List.find?_map]
  rfl

/-- **The caller of `awrap md` sees `M`'s own results.** -/
theorem awrap_ok (md : AMeta) (hC : md.sync.Conforms M) (name : String) (vs : List PVal)
    (s s' : M.withStore.St) (r : Option PVal)
    (h : (awrap md).callExport M name vs s (.ok r s')) :
    md.sync.spec M name vs s.1 (.ok r s'.1) := by
  rw [awrap_closed M md hC] at h
  unfold aspecClosed at h
  unfold Meta.spec
  rw [find_sync]
  cases hf : md.world.find? (·.sig.name == name) with
  | none =>
    rw [hf] at h
    cases h
  | some a =>
    rw [hf] at h
    rcases a with ⟨sig, _ | sty⟩
    · exact h.2
    · exact h.1

/-- **After an async function the store is `asyncStore` of the values returned.** -/
theorem awrap_store (md : AMeta) (hC : md.sync.Conforms M) (name : String) (sig : Sig)
    (sty : Style) (hf : md.world.find? (·.sig.name == name) = some ⟨sig, some sty⟩)
    (vs : List PVal) (s s' : M.withStore.St) (r : Option PVal)
    (h : (awrap md).callExport M name vs s (.ok r s')) :
    ∃ ws, resVals r = some ws ∧ s'.2 = asyncStore s.2 ws := by
  rw [awrap_closed M md hC] at h
  unfold aspecClosed at h
  rw [hf] at h
  obtain ⟨ws, h1, h2⟩ := Option.map_eq_some_iff.1 h.2
  exact ⟨ws, h1, h2.symm⟩

/-- **A synchronous function of `awrap md` leaves the store as it was.** -/
theorem awrap_store_sync (md : AMeta) (hC : md.sync.Conforms M) (name : String) (sig : Sig)
    (hf : md.world.find? (·.sig.name == name) = some ⟨sig, none⟩)
    (vs : List PVal) (s s' : M.withStore.St) (r : Option PVal)
    (h : (awrap md).callExport M name vs s (.ok r s')) : s'.2 = s.2 := by
  rw [awrap_closed M md hC] at h
  unfold aspecClosed at h
  rw [hf] at h
  exact h.1

/-- An async function with a `string` or `list<u8>` result never returns. -/
theorem aspecCall_async_inMem (md : AMeta) (sig : Sig) (sty : Style)
    (hm : inMem sig.result = true) (vs : List PVal) (s s' : M.withStore.St) (r : Option PVal) :
    ¬ aspecCall M md ⟨sig, some sty⟩ vs s (.ok r s') := by
  rw [aspecCall_async]
  rintro ⟨h1, h2⟩
  have hn := Silmaril.Proofs.Wasm.Jco.Async.Frame.specCall_inMem M md.sync sig hm vs _ _ _ h1
  simp [asyncPost, hn] at h2

end Silmaril.Wasm.Jco.Async
