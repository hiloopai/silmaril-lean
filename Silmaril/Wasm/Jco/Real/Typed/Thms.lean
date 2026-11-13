module

public import Silmaril.Wasm.Jco.Real.Typed.Defs
public import Silmaril.Proofs.Wasm.Jco.Real.Typed

/-!
# Typed locals: theorems

Proofs in `Silmaril.Proofs.Wasm.Jco.Real.Typed`.

* `ofX_run`: `XFnT.ofX` (all extra locals `i32`) runs as the `XFn`.
* **`mvShimT_run`**: the typed multi-value shim computes what `mvShim` computes, so
  `wrapW_correct` holds for the adaptor with typed locals (the shims are equal as relations).
* `exportShimWT_run`: the same for every export shim of the multi-value style.
* **`mvShimT_local_type`**: on every run of the wrapped function allowed by the convention, the
  `j`-th result has the declared type of the local it is popped into (local `n + 1 + j`). This is
  the property `local.set` needs to validate.
* **`mvShim_i32_mismatch`**, `mvShimT_i64`: the old encoding (`XFn.toLime`, all locals `i32`) of
  the shim of a record `{s64, u32}` declares an `i32` local for the `s64` field; the typed one
  declares `i64` (by evaluation). So the old `adaptorLime`-style encoding of `mvShim` is
  refuted as a valid encoding for `i64` fields, and `adaptorLimeW` fixes the declaration.

Validation of `adaptorLimeW md` as a whole is not proved (see `Silmaril.Wasm.Jco.Real.Valid` for
the first FFI style).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm.Component (Flat ValTy)

variable (M : CoreInst)

theorem ofX_run (fn : XFn) : (XFnT.ofX fn).run M = fn.run M := by
  funext xs
  have hz : (XFnT.ofX fn).tys.map zeroOf = List.replicate fn.locals (i32n 0) := by
    simp [XFnT.ofX, List.map_replicate, zeroOf]
    exact Or.inr rfl
  simp only [XFnT.run, XFn.run, hz]
  rfl

/-- **The typed multi-value shim computes what `mvShim` computes.** -/
theorem mvShimT_run (md : Meta) (s : Sig) {ts : List ValTy} {ns : List Nat}
    (hn : ts.mapM scalarSize = some ns) (xs : List Flat)
    (hx : xs.length = (flatParams s.params).length)
    (hR : RM.Returns (M.call s.name xs) fun rs => rs.map (·.type) = ValTy.flatList ts) :
    (mvShimT md s ts ns).run M xs = (mvShim md s ts ns).run M xs :=
  Silmaril.Proofs.Wasm.Jco.Real.mvShimT_run M md s hn xs hx hR

theorem wideOf_mapM {r : Option PTy} {ts : List ValTy} {ns : List Nat}
    (h : wideOf r = some (ts, ns)) : ts.mapM scalarSize = some ns := by
  unfold wideOf at h
  split at h
  · split at h
    · obtain ⟨ns', hns', he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact hns'
    · cases h
  · cases h

/-- Every typed export shim of the multi-value style computes what `exportShimW` computes. -/
theorem exportShimWT_run (md : Meta) (s : Sig) (xs : List Flat)
    (hx : xs.length = (flatParams s.params).length)
    (hR : ∀ ts ns, wideOf s.result = some (ts, ns) →
      RM.Returns (M.call s.name xs) fun rs => rs.map (·.type) = ValTy.flatList ts) :
    (exportShimWT md s).run M xs = (exportShimW md s).run M xs := by
  unfold exportShimWT exportShimW
  rcases hw : wideOf s.result with _ | ⟨ts, ns⟩
  · exact congrFun (ofX_run M _) xs
  · exact mvShimT_run M md s (wideOf_mapM hw) xs hx (hR ts ns hw)

/-- **The locals of the typed shim have the types of the results popped into them.** -/
theorem mvShimT_local_type (md : Meta) (s : Sig) (ts : List ValTy) (ns : List Nat)
    {rs : List Flat} (hrs : rs.map (·.type) = ValTy.flatList ts) (j : Nat) :
    (rs[j]?).map (·.type) = (mvShimT md s ts ns).tys[j + 1]? := by
  rw [← List.getElem?_map, hrs]
  rfl

/-- A record result `{s64, u32}`. -/
def exWideTs : List ValTy := [.s64, .u32]

/-- The old encoding declares an `i32` local for the `s64` field (local `n + 1`), whose result
is an `i64`: `local.set` would not validate. -/
theorem mvShim_i32_mismatch (md : Meta) (s : Sig) (ns : List Nat) (fi : String → Nat) (ty : Nat)
    (hs : s.params = []) :
    ((mvShim md s exWideTs ns).toLime fi ty).locals[1]? = some (.int .i32) ∧
      (ValTy.flatList exWideTs)[0]? = some (.int .i64) := by
  simp [mvShim, XFn.toLime, hs, flatParams, exWideTs, ValTy.flatList, ValTy.flat]

/-- The typed encoding declares the `i64` local. -/
theorem mvShimT_i64 (md : Meta) (s : Sig) (ns : List Nat) (fi : String → Nat) (ty : Nat) :
    ((mvShimT md s exWideTs ns).toLime fi ty).locals[1]? = some (.int .i64) := by
  simp [mvShimT, XFnT.toLime, exWideTs, ValTy.flatList, ValTy.flat]

end Silmaril.Wasm.Jco.Real
