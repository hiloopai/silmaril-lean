module

public import Silmaril.Wasm.Jco.Async.Defs
public import Silmaril.Wasm.Jco.Wrap.Thms
import Silmaril.Proofs.Wasm.Jco.Async.Basic

/-!
# Async lifts through the adaptor: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.Basic`.

* `callExport_ofComp`: a synchronous component, seen as a component with async lifts
  (`AComp.ofComp`), behaves as before (next to the async store, which it does not touch).
* **`awrap_sync`**, `awrap_ofMeta`: on async-free worlds the async construction **is** the
  synchronous construction: `awrap md = AComp.ofComp (wrap md.sync)`.
  `awrap_sync_callExport`, `awrap_sync_correct`: so it behaves as `wrap md.sync`, and (with
  `Conforms`) as the C convention.
* **`awrap_correct`**: for every module conforming to the C convention and every metadata with
  async styles, calling export `name` of `awrap md` is `aspec`: a synchronous function behaves as
  under `wrap`; an async one (stackful or callback) starts the task, computes the result under
  the C convention, stores it by `task.return` and returns what was stored. The callback loop
  ends at once, since a shim exits (`drive_exit`).
* `asyncCall_shim`: under `canon lift async`, an async shim is the synchronous lift followed by
  `task.return`, for every realloc, core function and callback.

Divergence is not covered (`RM` relates states to terminating outcomes).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Proofs.Wasm.Jco.Async

variable (M : CoreInst)

/-- A synchronous component seen with async lifts behaves as before. -/
theorem callExport_ofComp (c : Comp) (name : String) (vs : List PVal) :
    (AComp.ofComp c).callExport M name vs = c.callExport M.withStore name vs :=
  Silmaril.Proofs.Wasm.Jco.Async.callExport_ofComp M c name vs

/-- With every function synchronous, the async construction is the synchronous one. -/
theorem awrap_ofMeta (md : Meta) : awrap (AMeta.ofMeta md) = AComp.ofComp (wrap md) :=
  Silmaril.Proofs.Wasm.Jco.Async.awrap_ofMeta md

/-- **On async-free worlds the async construction is the synchronous one.** -/
theorem awrap_sync (md : AMeta) (h : md.asyncFree = true) :
    awrap md = AComp.ofComp (wrap md.sync) :=
  Silmaril.Proofs.Wasm.Jco.Async.awrap_sync md h

/-- On async-free worlds, `awrap` behaves as `wrap`. -/
theorem awrap_sync_callExport (md : AMeta) (h : md.asyncFree = true) (name : String)
    (vs : List PVal) :
    (awrap md).callExport M name vs = (wrap md.sync).callExport M.withStore name vs := by
  rw [awrap_sync md h, callExport_ofComp]

/-- On async-free worlds, `awrap` follows the C convention. -/
theorem awrap_sync_correct (md : AMeta) (h : md.asyncFree = true) (hC : md.sync.Conforms M)
    (name : String) (vs : List PVal) :
    (awrap md).callExport M name vs = md.sync.spec M.withStore name vs := by
  rw [awrap_sync_callExport M md h, wrap_correct _ _ (conforms_withStore M md.sync hC)]

/-- Under `canon lift async`, an async shim is the synchronous lift followed by `task.return`. -/
theorem asyncCall_shim (realloc core : List Flat → RM M.withStore.St (List Flat))
    (cb : List Flat → RM M.withStore.St (List Flat)) (st : Style) (sig : Sig) (vs : List PVal) :
    asyncCall M realloc (shimRun M core sig.result st) cb st sig vs =
      (startTask M >>= fun t => canonCall M.withStore realloc core sig vs >>= fun v =>
        RM.ofOption (resVals v) >>= fun ws => builtin M (.taskReturn t ws) >>= fun _ =>
          taskResult M t >>= fun ws' => RM.ofOption (valsRes sig.result ws')) :=
  Silmaril.Proofs.Wasm.Jco.Async.asyncCall_shim M realloc core cb st sig vs

/-- A shim's `EXIT` ends the callback loop at once. -/
theorem drive_exit (cb : List Flat → RM M.withStore.St (List Flat)) :
    @Eq (RM M.withStore.St Unit) (Drive M cb [i32n cbExit]) (pure ()) :=
  Silmaril.Proofs.Wasm.Jco.Async.drive_exit M cb

/-- **The behaviour theorem of the async construction.** -/
theorem awrap_correct (md : AMeta) (hC : md.sync.Conforms M) (name : String) (vs : List PVal) :
    (awrap md).callExport M name vs = aspec M md name vs := by
  unfold AComp.callExport aspec
  have hl : (awrap md).lifts = (liftsFrom 0 (md.world.map (·.sig))).zipWith
      (fun l s => (⟨l, s.async⟩ : ALift)) md.world := rfl
  rcases h : (awrap md).lifts.find? (·.lift.sig.name == name) with _ | al
  · rw [h, find_awrap_none name 0 md.world (hl ▸ h)]
  · obtain ⟨i, s, hi, hf, rfl⟩ := find_awrap name 0 md.world al (hl ▸ h)
    rw [h, hf]
    have e := lift_awrap M md hC i s hi vs
    rcases s with ⟨sig, _ | st⟩ <;> exact e

end Silmaril.Wasm.Jco.Async
