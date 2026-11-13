module

public import Silmaril.Wasm.Jco.Resource.Wrap.Defs
public import Silmaril.Proofs.Wasm.Jco.Resource.Wrap
public import Silmaril.Proofs.Wasm.Jco.Resource.Table

/-!
# The monadic construction with resources: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Resource.{Sim,Basic,Table,Lower,Lift,Wrap}`.

* `refTab_lawful`: the canonical handle tables (the reference machine's `Table`) are a lawful
  handle-table implementation.
* **`wrapR_correct`**: for every core instance `M`, lawful handle-table implementation `H`,
  metadata `md` whose erased metadata `M` conforms to (`Meta.Conforms`, as in `wrap_correct`),
  export `name`, boundary values `vs`, and table `t` satisfying the invariant with room for the
  call's handles (`md.Room`), calling export `name` of `wrapR md` from `(s, t)`:
  * has an outcome `ok a (s', t')` exactly when `md.spec M name vs` has `ok a s'` from `s`
    (the two directions of `Sim`);
  * traps exactly when `md.spec M name vs` traps;
  * every final table `t'` has the same entries and capacity as `t` and satisfies the invariant
    (`HTab.Same`): a rep-passing module leaves no handles behind.

  So the component's behaviour at its world is `M`'s under the rep-passing convention, up to the
  component's internal handle table. Handle indices are never observable at the boundary
  (boundary values of handle types are reps), which is why the table is only determined up to
  `HTab.Same`. The room hypothesis is needed: with a full table, `lower_own` traps where the
  convention does not.
* `wrapR_correct_ref`: the same with the canonical handle tables.

Divergence is not covered, as for `wrap_correct`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco

/-- The canonical handle tables are lawful. -/
theorem refTab_lawful : refTab.Lawful := Silmaril.Proofs.Wasm.Jco.Res.refTab_lawful

/-- **The behaviour theorem of the monadic construction with resources.** -/
theorem wrapR_correct (M : CoreInst) (H : HTab) (hH : H.Lawful) (md : MetaR)
    (hC : md.erase.Conforms M) (name : String) (vs : List RVal) {t : H.T} (hI : H.Inv t)
    (hR : md.Room H t name) :
    Sim ((wrapR md).callExport M H name vs) (md.spec M name vs) t
      fun a b t' => a = b ∧ H.Same t t' :=
  Silmaril.Proofs.Wasm.Jco.Res.wrapR_sim M H md hH hC name vs hI hR

/-- `wrapR_correct` with the canonical handle tables. -/
theorem wrapR_correct_ref (M : CoreInst) (md : MetaR) (hC : md.erase.Conforms M) (name : String)
    (vs : List RVal) {t : refTab.T} (hI : refTab.Inv t) (hR : md.Room refTab t name) :
    Sim ((wrapR md).callExport M refTab name vs) (md.spec M name vs) t
      fun a b t' => a = b ∧ refTab.Same t t' :=
  wrapR_correct M refTab refTab_lawful md hC name vs hI hR

end Silmaril.Wasm.Jco.Res
