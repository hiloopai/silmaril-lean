module

public import Silmaril.Wasm.Jco.Async.XWorld.Defs
public import Silmaril.Wasm.Jco.Async.Future.Thms
public import Silmaril.Wasm.Jco.Example.Defs
public import Silmaril.Proofs.Wasm.Jco.Async.XWorld

/-!
# Stream and future results in the world syntax: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.XWorld`.

* `toAMeta_ofAMeta`, **`xcallExport_ofAMeta`**: with every result plain, the new wrapper is
  `awrap`, export by export. So the new variant extends the async construction.
* `xcallExport_stream`, `xcallExport_future`: an async function whose result is a stream (a
  future) runs its shim's core function with `streamSplit` (`futureSplit`) and returns the
  readable end.
* **`xcallExport_stream_ok`**, **`xcallExport_future_ok`**: for metadata whose C convention `M`
  conforms to, the caller of such an export gets the handle `st.next + 1` (as a `u32`), and the
  state of `M` is that of `M`'s C convention, at the store `sB` (`fB`) where the callee goes on
  as in `Async/Early` (`stream_rest`) and `Async/Future` (`future_rest`).
* From WIT: `exXWorld_ofWorld` reads a world with `stream<u32>` and `future<u32>` results;
  `exWorld_xofWorld`: on the litmus world of part (a) `XMeta.ofWorld` is `Meta.ofWorld` with
  every function synchronous and plain; `exSyncStream_rejected`: a synchronous function
  returning a stream is refused. All three by evaluation (`rfl`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val ValTy)
open Silmaril.Proofs.Wasm.Jco.Async.Early (sB)
open Silmaril.Proofs.Wasm.Jco.Async.Future (fB)

theorem toAMeta_ofAMeta (md : AMeta) : (XMeta.ofAMeta md).toAMeta = md :=
  Silmaril.Proofs.Wasm.Jco.Async.XWorld.toAMeta_ofAMeta md

variable (M : CoreInst)

/-- **With every result plain, the wrapper is `awrap`.** -/
theorem xcallExport_ofAMeta (md : AMeta) (name : String) (vs : List PVal) :
    xcallExport M (XMeta.ofAMeta md) name vs = (awrap md).callExport M name vs :=
  Silmaril.Proofs.Wasm.Jco.Async.XWorld.xcallExport_ofAMeta M md name vs

/-- An async function whose result is a stream returns the readable end of `asyncCallS`. -/
theorem xcallExport_stream (md : XMeta) (name : String) (vs : List PVal) (l : Lift) (sty : Style)
    (hk : md.kindOf name = some .stream)
    (hl : (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) = some ⟨l, some sty⟩) :
    xcallExport M md name vs =
      (asyncCallS M ((awrap md.toAMeta).base.callRef M.withStore l.realloc)
        ((awrap md.toAMeta).base.callRef M.withStore l.callee) l.sig vs >>= fun h =>
          pure (handleRes h)) :=
  Silmaril.Proofs.Wasm.Jco.Async.XWorld.xcallExport_stream M md name vs l sty hk hl

/-- An async function whose result is a future returns the readable end of `asyncCallF`. -/
theorem xcallExport_future (md : XMeta) (name : String) (vs : List PVal) (l : Lift) (sty : Style)
    (hk : md.kindOf name = some .future)
    (hl : (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) = some ⟨l, some sty⟩) :
    xcallExport M md name vs =
      (asyncCallF M ((awrap md.toAMeta).base.callRef M.withStore l.realloc)
        ((awrap md.toAMeta).base.callRef M.withStore l.callee) l.sig vs >>= fun h =>
          pure (handleRes h)) :=
  Silmaril.Proofs.Wasm.Jco.Async.XWorld.xcallExport_future M md name vs l sty hk hl

/-- **The caller of a stream-result export gets the readable end**, with `M`'s C convention. -/
theorem xcallExport_stream_ok (md : XMeta) (hC : md.toAMeta.sync.Conforms M) (name : String)
    (vs : List PVal) (s : ASig) (sty : Style)
    (hs : md.toAMeta.world.find? (·.sig.name == name) = some s) (hsty : s.async = some sty)
    (hk : md.kindOf name = some .stream) (σ : M.withStore.St) (hU : Unused σ.2)
    (hb : σ.2.next + 1 < 2 ^ 32) (r : Option PVal) (σ' : M.withStore.St) :
    xcallExport M md name vs σ (.ok r σ') ↔
      ∃ v x ws, (md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧ resVals v = some ws) ∧
        r = handleRes (σ.2.next + 1) ∧ σ' = (x, sB σ.2) :=
  Silmaril.Proofs.Wasm.Jco.Async.XWorld.xcallExport_stream_ok M md hC name vs s sty hs hsty hk σ hU
    hb r σ'

/-- **The caller of a future-result export gets the readable end**, with `M`'s C convention. -/
theorem xcallExport_future_ok (md : XMeta) (hC : md.toAMeta.sync.Conforms M) (name : String)
    (vs : List PVal) (s : ASig) (sty : Style)
    (hs : md.toAMeta.world.find? (·.sig.name == name) = some s) (hsty : s.async = some sty)
    (hk : md.kindOf name = some .future) (σ : M.withStore.St) (hU : Unused σ.2)
    (hb : σ.2.next + 1 < 2 ^ 32) (r : Option PVal) (σ' : M.withStore.St) :
    xcallExport M md name vs σ (.ok r σ') ↔
      ∃ v x ws, (md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧ resVals v = some ws) ∧
        r = handleRes (σ.2.next + 1) ∧ σ' = (x, fB σ.2) :=
  Silmaril.Proofs.Wasm.Jco.Async.XWorld.xcallExport_future_ok M md hC name vs s sty hs hsty hk σ hU
    hb r σ'

/-! ## From WIT -/

/-- The litmus world: `stream<u32>` and `future<u32>` results of async functions. -/
theorem exXWorld_ofWorld : XMeta.ofWorld exXWorld = .ok {
    world := [⟨⟨⟨"add", [.val .u32, .val .u32], some (.val .u32)⟩, none⟩, .plain⟩,
              ⟨⟨⟨"count", [.val .u32], some (.val .u32)⟩, some .callback⟩, .stream⟩,
              ⟨⟨⟨"once", [], some (.val .u32)⟩, some .callback⟩, .future⟩] } := rfl

/-- On the litmus world of part (a), the new reader is `Meta.ofWorld`, every function plain and
synchronous. -/
theorem exWorld_xofWorld :
    XMeta.ofWorld Example.exWorld = .ok (XMeta.ofAMeta (AMeta.ofMeta Example.exMeta)) := rfl

/-- A synchronous function returning a stream is refused. -/
theorem exSyncStream_rejected : (XMeta.ofWorld exSyncStreamWorld matches .error _) = true := rfl

end Silmaril.Wasm.Jco.Async

/--
info: 'Silmaril.Wasm.Jco.Async.xcallExport_stream_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.xcallExport_stream_ok
