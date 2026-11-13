module

public import Silmaril.Wasm.Jco.Async.SyncStream.Defs
public import Silmaril.Wasm.Jco.Async.XWorld.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.SyncStream

/-!
# Synchronous functions with stream or future results: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.SyncStream`. From a store whose channel `st.next` is fresh
(`st.chans st.next = {}`, true of every `Unused` store):

* **`syncStreamCall_ok`**: the caller of a synchronous stream function gets the readable end
  `st.next` and `M`'s state of its C convention, at the store `yS` (the write pending; no task).
  **`syncStream_read`**: the caller's `stream.read r m` delivers the first `min m |ws|` values,
  the same items as the async stream function (`sync_async_stream_read`, with `stream_read` of
  `Async/Early`). **`syncStream_read_again`**: a further read waits (pending): the writable end is
  never dropped, as nothing of the callee runs after the synchronous return.
* **`syncFutureCall_ok`**, **`syncFuture_read`**: the same for a future (one value);
  `syncFuture_read_again`: a second read traps.
* The wrapper: `xcallExportS_ofAMeta` and `xcallExportS_async`: on plain metadata and on async
  functions, `xcallExportS` is `xcallExport` of `Async/XWorld`. **`xcallExportS_stream_ok`**,
  **`xcallExportS_future_ok`**: a synchronous stream (future) export of conforming metadata
  returns the readable end.
* From WIT: **`ofWorldS_of_ofWorld`**: on every world `XMeta.ofWorld` reads, `XMeta.ofWorldS`
  gives the same metadata; `exSyncStream_ofWorldS`, `exSyncFuture_ofWorldS`: it reads the
  synchronous stream and future functions that `XMeta.ofWorld` refuses (by evaluation).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store step packCopy CopyResult blocked)
open Silmaril.Proofs.Wasm.Jco.Async.SyncStream

variable (M : CoreInst)

/-- **The caller of a synchronous stream function gets the readable end.** -/
theorem syncStreamCall_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hf : s.2.chans s.2.next = {}) (h : Nat) (s' : M.withStore.St) :
    syncStreamCall M R core sig vs s (.ok h s') ↔
      ∃ v x ws, m₀ s.1 (.ok v x) ∧ resVals v = some ws ∧ h = s.2.next ∧ s' = (x, yS s.2 ws) :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.syncStreamCall_ok M R core sig vs m₀ hc s hf h s'

/-- **The caller's read delivers the values.** -/
theorem syncStream_read (st : Store) (ws : List Val) (m : Nat) :
    step (yS st ws) (.streamRead st.next m) =
      some (yR st ws m, .read (packCopy .completed (min m ws.length)) (ws.take (min m ws.length))) :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.syncStream_read st ws m

/-- **A further read waits**: the writable end is never dropped. -/
theorem syncStream_read_again (st : Store) (ws : List Val) (m m' : Nat) :
    step (yR st ws m) (.streamRead st.next m') = some (yR2 st ws m m', .nat blocked) :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.syncStream_read_again st ws m m'

/-- **The first read of the synchronous and of the async stream function delivers the same
items.** -/
theorem sync_async_stream_read (st : Store) (ws : List Val) (m : Nat) :
    ∃ a b, step (yS st ws) (.streamRead st.next m) =
        some (a, .read (packCopy .completed (min m ws.length)) (ws.take (min m ws.length))) ∧
      step (Silmaril.Proofs.Wasm.Jco.Async.Early.sD st ws) (.streamRead (st.next + 1) m) =
        some (b, .read (packCopy .completed (min m ws.length)) (ws.take (min m ws.length))) :=
  ⟨_, _, syncStream_read st ws m, stream_read st ws m⟩

/-- **The caller of a synchronous future function gets the readable end.** -/
theorem syncFutureCall_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hf : s.2.chans s.2.next = {}) (h : Nat) (s' : M.withStore.St) :
    syncFutureCall M R core sig vs s (.ok h s') ↔
      ∃ v x y, m₀ s.1 (.ok v x) ∧ resVals v = some [y] ∧ h = s.2.next ∧ s' = (x, zS s.2 y) :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.syncFutureCall_ok M R core sig vs m₀ hc s hf h s'

/-- **The caller's read of the future delivers the value.** -/
theorem syncFuture_read (st : Store) (y : Val) :
    step (zS st y) (.futureRead st.next) = some (zR st y, .read CopyResult.completed.toNat [y]) :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.syncFuture_read st y

/-- A second read of the future traps. -/
theorem syncFuture_read_again (st : Store) (y : Val) : step (zR st y) (.futureRead st.next) = none :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.syncFuture_read_again st y

/-! ## The wrapper -/

/-- With every result plain, the new wrapper is `xcallExport` (hence `awrap`). -/
theorem xcallExportS_ofAMeta (md : AMeta) (name : String) (vs : List PVal) :
    xcallExportS M (XMeta.ofAMeta md) name vs = (awrap md).callExport M name vs :=
  (Silmaril.Proofs.Wasm.Jco.Async.SyncStream.xcallExportS_ofAMeta M md name vs).trans
    (xcallExport_ofAMeta M md name vs)

/-- On an async function the new wrapper is `xcallExport`. -/
theorem xcallExportS_async (md : XMeta) (name : String) (vs : List PVal) (l : Lift) (sty : Style)
    (hl : (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) = some ⟨l, some sty⟩) :
    xcallExportS M md name vs = xcallExport M md name vs :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.xcallExportS_async M md name vs l sty hl

/-- **The caller of a synchronous stream-result export gets the readable end.** -/
theorem xcallExportS_stream_ok (md : XMeta) (hC : md.toAMeta.sync.Conforms M) (name : String)
    (vs : List PVal) (s : ASig) (hs : md.toAMeta.world.find? (·.sig.name == name) = some s)
    (hsty : s.async = none) (hk : md.kindOf name = some .stream) (σ : M.withStore.St)
    (hf : σ.2.chans σ.2.next = {}) (r : Option PVal) (σ' : M.withStore.St) :
    xcallExportS M md name vs σ (.ok r σ') ↔
      ∃ v x ws, (md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧ resVals v = some ws) ∧
        r = handleRes σ.2.next ∧ σ' = (x, yS σ.2 ws) :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.xcallExportS_stream_ok M md hC name vs s hs hsty hk σ hf
    r σ'

/-- **The caller of a synchronous future-result export gets the readable end.** -/
theorem xcallExportS_future_ok (md : XMeta) (hC : md.toAMeta.sync.Conforms M) (name : String)
    (vs : List PVal) (s : ASig) (hs : md.toAMeta.world.find? (·.sig.name == name) = some s)
    (hsty : s.async = none) (hk : md.kindOf name = some .future) (σ : M.withStore.St)
    (hf : σ.2.chans σ.2.next = {}) (r : Option PVal) (σ' : M.withStore.St) :
    xcallExportS M md name vs σ (.ok r σ') ↔
      ∃ v x y, (md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧ resVals v = some [y]) ∧
        r = handleRes σ.2.next ∧ σ' = (x, zS σ.2 y) :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.xcallExportS_future_ok M md hC name vs s hs hsty hk σ hf
    r σ'

/-! ## From WIT -/

/-- **On every world `XMeta.ofWorld` reads, `XMeta.ofWorldS` gives the same metadata.** -/
theorem ofWorldS_of_ofWorld (w : Silmaril.Wasm.Wit.Binary.World) (alloc : String) (md : XMeta)
    (h : XMeta.ofWorld w alloc = .ok md) : XMeta.ofWorldS w alloc = .ok md :=
  Silmaril.Proofs.Wasm.Jco.Async.SyncStream.ofWorldS_of_ofWorld w alloc md h

/-- The synchronous stream function that `XMeta.ofWorld` refuses. -/
theorem exSyncStream_ofWorldS : XMeta.ofWorldS exSyncStreamWorld =
    .ok { world := [⟨⟨⟨"count", [], some (.val .u32)⟩, none⟩, .stream⟩] } := rfl

/-- A synchronous future function. -/
theorem exSyncFuture_ofWorldS : XMeta.ofWorldS exSyncFutureWorld =
    .ok { world := [⟨⟨⟨"once", [], some (.val .u32)⟩, none⟩, .future⟩] } := rfl

end Silmaril.Wasm.Jco.Async

/--
info: 'Silmaril.Wasm.Jco.Async.xcallExportS_stream_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.xcallExportS_stream_ok
