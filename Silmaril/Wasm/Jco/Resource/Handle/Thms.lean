module

public import Silmaril.Wasm.Jco.Resource.Handle.Defs
public import Silmaril.Proofs.Wasm.Jco.Resource.Handle

/-!
# Handle-passing modules and their thin wrapper: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Resource.Handle`.

* **`thinR_fuseR`** (part (f) with resources): fuse the adaptor `adaptorR md` into `M` to get one
  handle-passing core module, `fuseR M md`. Its thin wrapper, which has only `canon lift`s, has the
  same behaviour relation as the adaptor-style `wrapR md` on every export, for every table
  implementation `H`. The only hypothesis is that no world function is named `cabi_realloc`.
  This is an equation, not a simulation: the two components make the same table operations.
* **`recognizeThinR_agrees`** (part (b) with resources): a recognized thin wrapper `c` of a
  module `N` that follows the handle-passing convention (`HMod.Follows`), and whose `realloc`
  export calls no built-in and agrees with the allocator (`ReallocAgrees`, as in
  `recognizeThin_agrees`), behaves exactly as `wrapR md` over `N`'s plain exports. The adaptor's
  resource code is then behaviourally the identity, because the module runs it itself.
* `recognizeThinR_correct`, `thinR_fuseR_correct`: hence, by `wrapR_correct`, both simulate
  the rep-passing convention `md.spec` up to the handle table, while the table has room.

`HMod.Follows` is stated against the fused shim, so it fixes the module's handle-passing code to
be the adaptor's code up to behaviour. That code is: `resource.rep` and `resource.drop` on each
`own` parameter, the rep-passing function, and `resource.new` on an `own` result. A module that
drops its `own` parameters later, or keeps them in the table across calls, does not follow it.
That case is the open part of `docs/projects/wasm-components.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco

/-- **The thin wrapper of the fused module is `wrapR md`.** -/
theorem thinR_fuseR (M : CoreInst) (H : HTab) (md : MetaR)
    (hr : md.world.all (·.name != fuseReallocName) = true) :
    (thinR md fuseReallocName).callExportH (fuseR M md) H = (wrapR md).callExport M H := by
  funext name vs
  exact Silmaril.Proofs.Wasm.Jco.Res.thinR_fuseR M H md hr name vs

theorem recognizeThinR_eq {md : MetaR} {r : String} {c : RComp} (h : recognizeThinR md r = some c) :
    md.world.all (·.name != r) = true ∧ c = thinR md r := by
  unfold recognizeThinR at h
  split at h
  · next hk => exact ⟨hk, (Option.some.inj h).symm⟩
  · cases h

/-- **Agreement of thin-wrapper recognition with the monadic construction, for handle-passing
modules.** -/
theorem recognizeThinR_agrees (N : HMod) (H : HTab) (md : MetaR) {r : String} {c : RComp}
    (h : recognizeThinR md r = some c) (hF : N.Follows md) (hP : N.PlainAt r)
    (hR : ReallocAgrees N.core md.erase r) :
    c.callExportH N H = (wrapR md).callExport N.core H := by
  obtain ⟨-, rfl⟩ := recognizeThinR_eq h
  funext name vs
  exact Silmaril.Proofs.Wasm.Jco.Res.thinR_follows H md N hF hP hR name vs

/-- The fused module's thin wrapper simulates the rep-passing convention. -/
theorem thinR_fuseR_correct (M : CoreInst) (H : HTab) (hH : H.Lawful) (md : MetaR)
    (hr : md.world.all (·.name != fuseReallocName) = true) (hC : md.erase.Conforms M)
    (name : String) (vs : List RVal) {t : H.T} (hI : H.Inv t) (hRm : md.Room H t name) :
    Sim ((thinR md fuseReallocName).callExportH (fuseR M md) H name vs) (md.spec M name vs) t
      fun a b t' => a = b ∧ H.Same t t' := by
  rw [thinR_fuseR M H md hr]
  exact wrapR_correct M H hH md hC name vs hI hRm

/-- A recognized thin wrapper of a module following the convention simulates the rep-passing
convention of its plain exports. -/
theorem recognizeThinR_correct (N : HMod) (H : HTab) (hH : H.Lawful) (md : MetaR) {r : String}
    {c : RComp} (h : recognizeThinR md r = some c) (hF : N.Follows md) (hP : N.PlainAt r)
    (hR : ReallocAgrees N.core md.erase r) (hC : md.erase.Conforms N.core) (name : String)
    (vs : List RVal) {t : H.T} (hI : H.Inv t) (hRm : md.Room H t name) :
    Sim (c.callExportH N H name vs) (md.spec N.core name vs) t
      fun a b t' => a = b ∧ H.Same t t' := by
  rw [recognizeThinR_agrees N H md h hF hP hR]
  exact wrapR_correct N.core H hH md hC name vs hI hRm

end Silmaril.Wasm.Jco.Res
