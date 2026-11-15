module

public import Silmaril.Proofs.Wasm.Interp.Replace
public import Silmaril.Wasm.Execution.Core.Typing.Store

/-!
# Function-list extension and the arity check (proofs)

Core's store extension (`Extend`, part of `HostOk`) lets a host append
functions but never change an existing one: `ExtendsList ExtendFunc F F'`.
Since `ExtendFunc` fixes type, module and code, every existing address keeps
its function instance (`get_of_funcsExt`). So call arities are preserved
(`arities_of_funcsExt`), and every passing arity check still passes after the
extension (`chk_of_funcsExt`). The store check transfers too, given the new
functions pass it (`storeChk_of_funcsExt`, and `storeChk_of_funcsExtE` for a
stable extended check).

These are the facts that let the native arity invariants work up to function
extension rather than equality.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **A passing arity check still passes after function extension.** -/
theorem chk_of_funcsExt {F F' : List (FuncInst H)} (h : FuncsExt F F') {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {oh : Option Nat} {es : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk F mi nl ret labels oh es = some o) : chk F' mi nl ret labels oh es = some o :=
  chk_transfer (arities_of_funcsExt h mi) oh es hc

/-- **The store check after a function extension**: the old functions still
pass, so only the appended ones need checking. -/
theorem storeChk_of_funcsExt {F F' : List (FuncInst H)} (h : FuncsExt F F') (hS : StoreChk F)
    (hnew : ∀ (a : Nat) (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType),
      F.length ≤ a → F'[a]? = some fi → fi.code = .wasm fn →
      Validation.DefType.funcType? fi.type = some (ps, rs) →
      endsAt (chk F' fi.module (ps.length + fn.locals.length) rs.length [rs.length] (some 0)
        (Binaryen.liftInstrs fn.body)) rs.length = true) : StoreChk F' := by
  intro a fi fn ps rs ha hc ht
  by_cases hlt : a < F.length
  · obtain ⟨fi₀, h₀⟩ : ∃ fi₀, F[a]? = some fi₀ := ⟨F[a], List.getElem?_eq_getElem hlt⟩
    obtain rfl : fi₀ = fi := Option.some.inj ((get_of_funcsExt h h₀).symm.trans ha)
    exact endsAt_transfer (fun o ho => chk_of_funcsExt h ho) (hS a fi₀ fn ps rs h₀ hc ht)
  · exact hnew a fi fn ps rs (by omega) ha hc ht

/-- **The extended store check after a function extension**: with a stable
extension the old functions still pass, so only the appended ones need checking. -/
theorem storeChk_of_funcsExtE {ext : ExtArity H} [ExtStable ext] {F F' : List (FuncInst H)}
    (h : FuncsExt F F') (hS : StoreChkE ext F)
    (hnew : ∀ (a : Nat) (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType),
      F.length ≤ a → F'[a]? = some fi → fi.code = .wasm fn →
      Validation.DefType.funcType? fi.type = some (ps, rs) →
      endsAt (chkE ext F' fi.module (ps.length + fn.locals.length) rs.length [rs.length] (some 0)
        (Binaryen.liftInstrs fn.body)) rs.length = true) : StoreChkE ext F' := by
  intro a fi fn ps rs ha hc ht
  by_cases hlt : a < F.length
  · obtain ⟨fi₀, h₀⟩ : ∃ fi₀, F[a]? = some fi₀ := ⟨F[a], List.getElem?_eq_getElem hlt⟩
    obtain rfl : fi₀ = fi := Option.some.inj ((get_of_funcsExt h h₀).symm.trans ha)
    exact endsAt_transfer (fun o ho => chkE_ext h _ _ ho) (hS a fi₀ fn ps rs h₀ hc ht)
  · exact hnew a fi fn ps rs (by omega) ha hc ht

end Silmaril.Wasm.Interp
