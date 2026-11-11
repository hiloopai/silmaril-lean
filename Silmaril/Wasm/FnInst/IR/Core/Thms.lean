module

public import Silmaril.Wasm.FnInst.IR.Bodies.Thms
public import Silmaril.Wasm.SSA.CoreCert.Thms

/-!
# From a Binaryen-body equation to Core 3.0 behaviours

The Binaryen body institution `(bir H).inst F` reads bodies through silmaril's native
interpreter. `Silmaril.Wasm.SSA.CoreCert` (`behaviours_eq_run`) computes the Core 3.0 behaviours
of an invocation of a function whose code is a recognised, native-checked, folded fragment
body, in a typed store of native-profile, arity-checked functions: its fragment outcomes, and
divergence exactly when it has none, at every numeric profile.

* `core_behaviours_of_equiv`: two such functions at the same address of two such stores, with
  equivalent fragment functions, have the same Core 3.0 behaviours on every typed invocation,
  at every profile, divergence included. This generalises `invoke_replace` (where the second
  function is the optimiser's output) to any equivalence.
* `core_behaviours_of_sat`: the same from the satisfaction of `b ≐ b'` in any model of the
  Binaryen body institution, so an equation proved (or borrowed) in the body institution gives
  the Core-level replacement fact.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.IR

open CategoryTheory
open Silmaril.Inst
open Silmaril.Wasm.Institution (Formula)
open Silmaril.Wasm.SSA
open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **Equivalent native bodies have the same Core 3.0 behaviours.** -/
theorem core_behaviours_of_equiv {s s' : Store H} {a : Nat} {fi fi' : FuncInst H}
    {ft : FuncType} {bf bf' : BFunc} {f f' : FragFunc}
    (hs : StoreOk s) (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hf : ofBFunc? ft bf = some f) (hn : f.native = true)
    (hst : BExpr.structuredList bf.body = true)
    (hs' : StoreOk s') (hF' : NativeFuncsOk s'.funcs) (hS' : Silmaril.Wasm.Interp.StoreChk s'.funcs)
    (hfi' : s'.funcs[a]? = some fi') (hcode' : fi'.code = .wasm (coreFunc bf'))
    (hty' : Validation.DefType.funcType? fi'.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hf' : ofBFunc? ft bf' = some f') (hn' : f'.native = true)
    (hst' : BExpr.structuredList bf'.body = true)
    (heq : Beh.Equiv f.Run f'.Run) {vs : List Val} (hok : InvokeOk s a vs)
    (hok' : InvokeOk s' a vs) (P : Numerics.Profile) :
    behaviours P closedHost s a vs = behaviours P closedHost s' a vs := by
  obtain ⟨args, hvs, -, hb⟩ := behaviours_eq_run hs hF hS hfi hcode hty hf hn hst hok P
  obtain ⟨args', hvs', -, hb'⟩ := behaviours_eq_run hs' hF' hS' hfi' hcode' hty' hf' hn' hst' hok' P
  obtain rfl : args = args' := WVal.map_toVal_inj (hvs.symm.trans hvs')
  rw [hb, hb']
  ext b
  simp only [Set.mem_ofPred_eq, heq args]

/-- **An equation satisfied in the Binaryen body institution gives equal Core 3.0 behaviours.**
`b ≐ b'` at the focus hole `F.hole S`, satisfied in any model, for bodies `b` and `b'` whose
Core code sits at address `a` of two typed, native, arity-checked stores. -/
theorem core_behaviours_of_sat {Sig : Type} [Category.{0} Sig] (F : Frame Sig) {S : Sig}
    (b b' : BirBody (F.hole S)) (M : ((bir H).inst F).Mod S)
    (hM : M ⊨[(bir H).inst F] (Formula.eq b b' : ((bir H).inst F).Sen S))
    {s s' : Store H} {a : Nat} {fi fi' : FuncInst H}
    (hs : StoreOk s) (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (coreFunc b.1))
    (hty : Validation.DefType.funcType? fi.type = some ((F.hole S).funcType.params.map
      Validation.liftVal, (F.hole S).funcType.results.map Validation.liftVal))
    (hst : BExpr.structuredList b.1.body = true)
    (hs' : StoreOk s') (hF' : NativeFuncsOk s'.funcs) (hS' : Silmaril.Wasm.Interp.StoreChk s'.funcs)
    (hfi' : s'.funcs[a]? = some fi') (hcode' : fi'.code = .wasm (coreFunc b'.1))
    (hty' : Validation.DefType.funcType? fi'.type = some ((F.hole S).funcType.params.map
      Validation.liftVal, (F.hole S).funcType.results.map Validation.liftVal))
    (hst' : BExpr.structuredList b'.1.body = true)
    {vs : List Val} (hok : InvokeOk s a vs) (hok' : InvokeOk s' a vs) (P : Numerics.Profile) :
    behaviours P closedHost s a vs = behaviours P closedHost s' a vs := by
  have heq : Beh.Equiv b.recog.Run b'.recog.Run :=
    (equiv_bir_iff H M.2 b b').1 (((bir H).sat_eq_iff F M b b').1 hM)
  exact core_behaviours_of_equiv hs hF hS hfi hcode hty b.recog_spec b.recog_native hst
    hs' hF' hS' hfi' hcode' hty' b'.recog_spec b'.recog_native hst' heq hok hok' P

end Silmaril.Wasm.FnInst.IR
