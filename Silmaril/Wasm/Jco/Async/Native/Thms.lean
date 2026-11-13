module

public import Silmaril.Wasm.Jco.Async.Native.Defs
public import Silmaril.Wasm.Jco.Async.Frame.Thms
public import Silmaril.Wasm.Jco.Thin.Canon.Thms
import Silmaril.Proofs.Wasm.Jco.Async.Native

/-!
# Natively async modules and thin async recognition: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.Native`.

* `thinA_callExport`: the thin async wrapper of a natively async module follows the native async
  convention `canonSpecA`. This holds for every natively async module, including one that waits
  or uses streams in its body.
* `drive_yield_exit`: in the callback loop, a `YIELD` whose callback answers `EXIT` ends at once.
* **`recognizeThinA_agrees`**: a recognized thin async wrapper of a module `N` that inlines the
  adaptor's epilogue (`NInst.Inlines`) behaves as `awrap md` over the synchronous core `M`, when
  `M` conforms and its `realloc` agrees with its allocator (`ReallocAgrees`). The epilogue may
  exit at once or yield once in the callback style. The adaptor is then behaviourally the
  identity. `recognizeThinA_agrees_memFree`: on memory-free worlds no condition on the
  `realloc` is needed.
* `recognizeThinA_closed`: so the thin async wrapper has the closed form `aspecClosed`.
* `inlined_inlines`, **`recognizeThinA_inlined`**: when the world's names are distinct, the
  module `NInst.inlined M md` (the adaptor's epilogue fused into `M`) inlines the epilogue. Its
  thin async wrapper is then `awrap md`.

Recognition looks only at the metadata. Whether a module inlines the epilogue is a semantic
condition, as `ReallocAgrees` is.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Proofs.Wasm.Jco.Async.Native

variable (M : CoreInst)

/-- The thin async wrapper follows the native async convention. -/
theorem thinA_callExport (N : NInst M) (md : AMeta) (r name : String) (vs : List PVal) :
    (thinA md r).callExport N name vs = canonSpecA N md r name vs :=
  Silmaril.Proofs.Wasm.Jco.Async.Native.thinA_callExport M N md r name vs

/-- A `YIELD` whose callback answers `EXIT` ends the callback loop. -/
theorem drive_yield_exit (cb : List Flat → RM M.withStore.St (List Flat))
    (hcb : ∀ a, cb a = pure [i32n cbExit]) :
    @Eq (RM M.withStore.St Unit) (Drive M cb [i32n cbYield]) (pure ()) :=
  Silmaril.Proofs.Wasm.Jco.Async.Native.drive_yield_exit M cb hcb

theorem recognizeThinA_eq {md : AMeta} {r : String} {c : NComp} (h : recognizeThinA md r = some c) :
    md.sync.thinOk = true ∧ c = thinA md r := by
  unfold recognizeThinA at h
  split at h
  · next hk => exact ⟨hk, (Option.some.inj h).symm⟩
  · cases h

/-- **Thin async recognition agrees with the async construction.** -/
theorem recognizeThinA_agrees (N : NInst M) {md : AMeta} {r : String} {c : NComp}
    (h : recognizeThinA md r = some c) (hC : md.sync.Conforms M)
    (hR : ReallocAgrees M md.sync r) (hN : N.Inlines md) :
    c.callExport N = (awrap md).callExport M := by
  obtain ⟨hk, rfl⟩ := recognizeThinA_eq h
  have hp : ∀ s ∈ md.world, ∀ vs, lowerParams M.withStore (M.withStore.call r) s.sig.params vs =
      md.sync.specParams M.withStore s.sig.params vs := fun s _ vs =>
    lowerParams_realloc M.withStore md.sync (reallocAgrees_withStore M md.sync r hR) s.sig.params vs
  funext name vs
  rw [thinA_callExport, canonSpecA_eq_aspec M N md r hN hk hp, awrap_correct M md hC]

/-- **The same on memory-free worlds**, with no condition on the `realloc`. -/
theorem recognizeThinA_agrees_memFree (N : NInst M) {md : AMeta} {r : String} {c : NComp}
    (h : recognizeThinA md r = some c) (hm : md.sync.memFree = true) (hC : md.sync.Conforms M)
    (hN : N.Inlines md) :
    c.callExport N = (awrap md).callExport M := by
  obtain ⟨hk, rfl⟩ := recognizeThinA_eq h
  have hp : ∀ s ∈ md.world, ∀ vs, lowerParams M.withStore (M.withStore.call r) s.sig.params vs =
      md.sync.specParams M.withStore s.sig.params vs := fun s hs vs =>
    lowerParams_memFree M.withStore md.sync _ s.sig.params vs
      (memFree_mem md.sync hm (sig_mem hs)).1
  funext name vs
  rw [thinA_callExport, canonSpecA_eq_aspec M N md r hN hk hp, awrap_correct M md hC]

/-- The thin async wrapper in closed form. -/
theorem recognizeThinA_closed (N : NInst M) {md : AMeta} {r : String} {c : NComp}
    (h : recognizeThinA md r = some c) (hC : md.sync.Conforms M)
    (hR : ReallocAgrees M md.sync r) (hN : N.Inlines md) :
    c.callExport N = aspecClosed M md := by
  funext name vs
  rw [recognizeThinA_agrees M N h hC hR hN, awrap_closed M md hC]

/-- The fused module inlines the epilogue, when the world's names are distinct. -/
theorem inlined_inlines (md : AMeta) (hn : (md.world.map (·.sig.name)).Nodup) :
    (NInst.inlined M md).Inlines md :=
  Silmaril.Proofs.Wasm.Jco.Async.Native.inlined_inlines M md hn

/-- **The thin async wrapper of the fused module is `awrap`.** -/
theorem recognizeThinA_inlined {md : AMeta} {r : String} {c : NComp}
    (h : recognizeThinA md r = some c) (hn : (md.world.map (·.sig.name)).Nodup)
    (hC : md.sync.Conforms M) (hR : ReallocAgrees M md.sync r) :
    c.callExport (NInst.inlined M md) = (awrap md).callExport M :=
  recognizeThinA_agrees M _ h hC hR (inlined_inlines M md hn)

end Silmaril.Wasm.Jco.Async
