module

public import Silmaril.Wasm.Jco.Resource.Scope.Defs
public import Silmaril.Proofs.Wasm.Jco.Resource.Scope.Lend

/-!
# Full handles: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Resource.Scope.{Keeps,Basic,Lend}`.

* **Borrow scopes** (`canonCallF_scope`). Take a `canon lift` call with full handles, from a
  state satisfying `FSt.Inv` (no entry at or above `next`, and `num_borrows` counts the live
  borrow entries), whose callee keeps the invariant. If it returns, the final state satisfies
  the invariant and `num_borrows = 0`, and every entry left in the table is an `own` entry. So
  every borrow handle that `lower_borrow` made for an imported resource was dropped by the
  callee before the call returned; otherwise the exit check traps.
  `canonCallF_scope_runB` drops the hypothesis on the callee when the callee is **any**
  adaptor function (`RFn`) run with the built-ins `fullB R`, as long as the destructors keep
  the invariant (`DtorsKeep`). This covers the shims of `wrapR`, run with full handles and
  destructors.
* **Lends** (`canonLowerF_lends`). A returning `canon lower` of an imported function, which
  lends the borrowed handles to the host, leaves every entry that was live before exactly as it
  was, including its `num_lends`, and does not change `num_borrows`. The only possible change
  is a new `own` entry for an `own` result.
* **Destructors.** `fDrop_lent`: dropping a lent handle (`num_lends ≠ 0`) traps, and the
  destructor does not run. `fDrop_dtor`: dropping an unlent `own` handle of a type with
  destructor `d` is `d` on its rep, run from the table without the entry.

So a rep-passing adaptor (`wrapR`) is not correct for a resource type with a destructor. Its
prologue's `resource.drop` would run the destructor before `M` sees the rep (`fDrop_dtor`).
For such types only the handle-passing convention of `Silmaril.Wasm.Jco.Resource.Handle` is
faithful, because there the module drops the handle when it is done. The relation of
`canonCallF` with `canonCallR` (the fragment without borrows of imported resources and
without destructors) is not proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res.Scope

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Component (Flat)

/-- The destructors keep the invariant. -/
abbrev DtorsKeep {σ : Type} (R : RTypes σ) : Prop := Silmaril.Proofs.Wasm.Jco.Res.Scope.DtorsKeep R

/-- A callee keeps the invariant: every returning run from a state satisfying it ends in one. -/
abbrev KeepsInv {σ α : Type} (m : RM (σ × FSt) α) : Prop :=
  Silmaril.Proofs.Wasm.Jco.Res.Scope.Keeps FSt.Inv m

/-- **The borrow-scope theorem.** -/
theorem canonCallF_scope (M : CoreInst) (R : RTypes M.St) (rw : List Flat → RM M.St (List Flat))
    {callee : List Flat → RM (withTab M FSt).St (List Flat)} (hc : ∀ xs, KeepsInv (callee xs))
    (sig : RSig) (vs : List RVal) {st : (withTab M FSt).St} {a : Option RVal}
    {st' : (withTab M FSt).St} (hI : st.2.Inv)
    (h : canonCallF R M (fun xs => (rw xs).onFst) callee sig vs st (.ok a st')) :
    st'.2.Inv ∧ st'.2.borrows = 0 ∧ ∀ j e, st'.2.tab j = some e → e.own = true :=
  Silmaril.Proofs.Wasm.Jco.Res.Scope.canonCallF_scope M R rw hc sig vs hI h

/-- The borrow-scope theorem for every adaptor function as the callee. -/
theorem canonCallF_scope_runB (M : CoreInst) (R : RTypes M.St) (hd : DtorsKeep R)
    (rw : List Flat → RM M.St (List Flat)) (fn : RFn) (sig : RSig) (vs : List RVal)
    {st : (withTab M FSt).St} {a : Option RVal} {st' : (withTab M FSt).St} (hI : st.2.Inv)
    (h : canonCallF R M (fun xs => (rw xs).onFst) (fn.runB M (fullB R)) sig vs st (.ok a st')) :
    st'.2.Inv ∧ st'.2.borrows = 0 ∧ ∀ j e, st'.2.tab j = some e → e.own = true :=
  Silmaril.Proofs.Wasm.Jco.Res.Scope.canonCallF_scope_runB M R hd rw fn sig vs hI h

/-- **Lends are released** by a returning `canon lower`. -/
theorem canonLowerF_lends (M : CoreInst) (host : List RVal → RM M.St (Option RVal)) (sig : RSig)
    (xs : List Flat) {st : (withTab M FSt).St} {ys : List Flat} {st' : (withTab M FSt).St}
    (h : canonLowerF M host sig xs st (.ok ys st')) :
    (∀ j, j < st.2.next → st'.2.tab j = st.2.tab j) ∧ st'.2.borrows = st.2.borrows :=
  Silmaril.Proofs.Wasm.Jco.Res.Scope.canonLowerF_lends M host sig xs h

/-- Dropping a lent handle traps. -/
theorem fDrop_lent {σ : Type} (R : RTypes σ) {r : RtId} {h : BitVec 32} {s : σ} {t : FSt}
    {e : FEntry} (he : t.tab h.toNat = some e) (hr : e.rt = r) (hl : e.lends ≠ 0) :
    fDrop R r h (s, t) = RM.fail (s, t.removed h.toNat) :=
  Silmaril.Proofs.Wasm.Jco.Res.Scope.fDrop_lent R he hr hl

/-- Dropping an unlent `own` handle runs the destructor on its rep. -/
theorem fDrop_dtor {σ : Type} (R : RTypes σ) {r : RtId} {h : BitVec 32} {s : σ} {t : FSt}
    {e : FEntry} {d : BitVec 32 → RM (σ × FSt) Unit} (he : t.tab h.toNat = some e)
    (hr : e.rt = r) (hl : e.lends = 0) (ho : e.own = true) (hd : R.dtor r = some d) :
    fDrop R r h (s, t) = d e.rep (s, t.removed h.toNat) :=
  Silmaril.Proofs.Wasm.Jco.Res.Scope.fDrop_dtor R he hr hl ho hd

end Silmaril.Wasm.Jco.Res.Scope
