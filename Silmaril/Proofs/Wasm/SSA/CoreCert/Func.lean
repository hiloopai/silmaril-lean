module

public import Silmaril.Proofs.Wasm.SSA.CoreCert.Invoke

@[expose] public section

/-!
# Replacing a function by its certified optimisation preserves Core 3.0 behaviours (proofs)

`invoke_setCode`: for a store typed before and after the replacement, whose functions are of
the native profile and pass the arity check, replacing the code of a fragment function by the
result of `optimizeFuncCore?` preserves the Core 3.0 behaviours (closed host, divergence
included) of every typed invocation of that function, at every profile. Route: Core
behaviours are the native ones on both stores (`Interp.native_adequacy`; the hypotheses for the
new store follow from `coreReady`, `Interp.storeChk_modify` and `Silmaril.Wasm.Interp.instrsNative_sound`),
the native behaviours are determined by the observations (`nbeh_congr`), and these are the
images of the fragment outcomes of the source and of the optimised function (`obs_iff_run`),
which are the same (`optimizeFuncNative?_spec`). New proofs.
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

variable {H : Type}

/-! ## The certified optimiser, unfolded -/

/-- What `optimizeFuncCore?` checked. -/
theorem optimizeFuncCore?_inv {ft : FuncType} {bf bf' : BFunc}
    (h : optimizeFuncCore? ft bf = some bf') :
    optimizeFuncNative? ft bf = some bf' ∧ coreReady ft bf = true ∧ coreReady ft bf' = true := by
  simp only [optimizeFuncCore?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bf'', ho, hc⟩ := h
  split at hc
  · rename_i hr
    obtain rfl : bf'' = bf' := Option.some.inj hc
    simp only [Bool.and_eq_true] at hr
    exact ⟨ho, hr.1, hr.2⟩
  · cases hc

/-- The three checks of `coreReady`. -/
theorem coreReady_inv {ft : FuncType} {bf : BFunc} (h : coreReady ft bf = true) :
    BExpr.structuredList bf.body = true ∧ Silmaril.Wasm.Interp.instrsNative (coreFunc bf).body = true ∧
      Silmaril.Wasm.Interp.endsAt (Silmaril.Wasm.Interp.chk ([] : List (FuncInst Empty)) {}
        (ft.params.length + (coreFunc bf).locals.length) ft.results.length [ft.results.length]
        (some 0) (liftInstrs (coreFunc bf).body)) ft.results.length = true := by
  simp only [coreReady, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## Arguments -/

/-- A typed value of an integer type is an integer value. -/
theorem int_of_valOk {s : Store H} {v : Val} {T : Validation.CValType} {t : IntType}
    (hv : ValOk s v T) (hT : T = Validation.liftVal (.num (.int t))) :
    ∃ w : WVal, v = w.toVal ∧ w.type = t := by
  cases hv with
  | num nv =>
    rcases nv with ⟨ty, x⟩
    have hty : ty = .int t := by simpa [Validation.liftVal] using hT
    subst hty
    cases t
    · exact ⟨.i32 x, rfl, rfl⟩
    · exact ⟨.i64 x, rfl, rfl⟩
  | vec b => simp [Validation.liftVal] at hT
  | ref h => simp [Validation.liftVal] at hT

/-- Typed values of integer types are integer values. -/
theorem args_of_valOk {s : Store H} :
    ∀ {ts : List IntType} {vs : List Val},
      List.Forall₂ (ValOk s) vs (ts.map fun t => Validation.liftVal (.num (.int t))) →
      ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = ts
  | [], vs, h => by
    cases h
    exact ⟨[], rfl, rfl⟩
  | t :: ts, vs, h => by
    cases h with
    | cons hv hr =>
      rename_i v vs'
      obtain ⟨args, rfl, hargs⟩ := args_of_valOk hr
      obtain ⟨w, hw, hwt⟩ : ∃ w : WVal, v = w.toVal ∧ w.type = t := int_of_valOk hv rfl
      exact ⟨w :: args, by rw [hw]; rfl, by simp [hwt, hargs]⟩

/-- Integer values are typed at their types, in any store. -/
theorem valOk_args (s : Store H) :
    ∀ args : List WVal, List.Forall₂ (ValOk s) (args.map WVal.toVal)
      (args.map fun w => Validation.liftVal (.num (.int w.type)))
  | [] => .nil
  | w :: args => .cons (by cases w <;> exact ValOk.num _) (valOk_args s args)

/-- **The arguments of a typed invocation** of a function of integer parameters. -/
theorem args_of_invokeOk {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {ts : List IntType} {rs : List Validation.CValType} (hok : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type =
      some (ts.map fun t => Validation.liftVal (.num (.int t)), rs)) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = ts := by
  obtain ⟨fi', ps, rs', hfi', hexp, hvals⟩ := hok
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  have hps : ps.toList = ts.map fun t => Validation.liftVal (.num (.int t)) := by
    unfold Validation.DefType.funcType? at hty
    rw [Validation.Expand.iff.mp hexp] at hty
    exact (Prod.mk.inj (Option.some.inj hty)).1
  rw [hps] at hvals
  exact args_of_valOk hvals

/-! ## The replaced store -/

section Replaced

variable {s : Store H} {a : Nat} {fi : FuncInst H} {fn' : Func}

theorem setCode_funcs_a (hfi : s.funcs[a]? = some fi) :
    (setCode s a fn').funcs[a]? = some { fi with code := .wasm fn' } := by
  simp [setCode, hfi]

/-- The replaced store is of the native profile when the new code is. -/
theorem nativeFuncsOk_setCode (hF : NativeFuncsOk s.funcs)
    (hn : Silmaril.Wasm.Interp.instrsNative fn'.body = true) :
    NativeFuncsOk (setCode s a fn').funcs := by
  intro fi' hmem
  obtain ⟨b, hb⟩ := List.getElem?_of_mem hmem
  simp only [setCode, List.getElem?_modify, Option.map_eq_map, Option.map_eq_some_iff] at hb
  obtain ⟨fi, hfi, hfi'⟩ := hb
  by_cases hab : a = b
  · simp only [hab, ite_true] at hfi'
    subst hfi'
    exact ⟨fn', rfl, Silmaril.Wasm.Interp.instrsNative_sound fn'.body hn⟩
  · simp only [hab, ite_false] at hfi'
    subst hfi'
    exact hF fi (List.mem_of_getElem? hfi)

/-- Integer arguments of the parameter types are a typed invocation. -/
theorem invokeOk_of_type {s' : Store H} {fi' : FuncInst H} {args : List WVal} {ts : List IntType}
    {rs : List Validation.CValType} (hfi' : s'.funcs[a]? = some fi')
    (hty : Validation.DefType.funcType? fi'.type =
      some (ts.map fun t => Validation.liftVal (.num (.int t)), rs))
    (hargs : args.map WVal.type = ts) : InvokeOk s' a (args.map WVal.toVal) := by
  unfold Validation.DefType.funcType? at hty
  split at hty
  · rename_i ps rs' hexp
    have hps : ps.toList = ts.map fun t => Validation.liftVal (.num (.int t)) :=
      (Prod.mk.inj (Option.some.inj hty)).1
    have hvals : List.Forall₂ (ValOk s') (args.map WVal.toVal) ps.toList := by
      rw [hps, ← hargs, List.map_map]
      exact valOk_args _ args
    exact ⟨fi', ps, rs', hfi', Validation.Expand.iff.mpr hexp, hvals⟩
  · cases hty

end Replaced

/-! ## The theorem -/

/-- **Replacing a function by its Core-certified optimisation preserves the Core 3.0 behaviours
of every typed invocation of it**, at every profile, divergence included: `s'` is any store,
typed, native and arity-checked, holding the optimised code at the same address and type. -/
theorem invoke_replace {H' : Type} {s : Store H} {s' : Store H'} {a : Nat} {fi : FuncInst H}
    {fi' : FuncInst H'} {ft : FuncType} {bf bf' : BFunc} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs) (hs' : StoreOk s')
    (hF' : NativeFuncsOk s'.funcs) (hS' : Silmaril.Wasm.Interp.StoreChk s'.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hfi' : s'.funcs[a]? = some fi') (hcode' : fi'.code = .wasm (coreFunc bf'))
    (hty' : Validation.DefType.funcType? fi'.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (ho : optimizeFuncCore? ft bf = some bf') {vs : List Val} (hok : InvokeOk s a vs)
    (P : Numerics.Profile) :
    behaviours P closedHost s a vs = behaviours P closedHost s' a vs := by
  obtain ⟨hon, hr, hr'⟩ := optimizeFuncCore?_inv ho
  obtain ⟨f, g, hf, hnf, hg, hng, gp, gr, hrun⟩ := optimizeFuncNative?_spec hon
  obtain ⟨hp, hres⟩ : ft.params = f.params.map (fun t => .num (.int t)) ∧
      ft.results = resultTypes f.result := ofBFunc?_types hf
  have hlift : ft.params.map Validation.liftVal =
      f.params.map fun t => Validation.liftVal (.num (.int t)) := by
    rw [hp, List.map_map]
    rfl
  obtain ⟨args, rfl, hargs⟩ := args_of_invokeOk hok hfi (hlift ▸ hty)
  have hok' : InvokeOk s' a (args.map WVal.toVal) := invokeOk_of_type hfi' (hlift ▸ hty') hargs
  have hrs : (ft.results.map Validation.liftVal).length = (resultTypes f.result).length := by
    rw [List.length_map, hres]
  rw [Silmaril.Wasm.Interp.native_adequacy hs hF hS hok,
    Silmaril.Wasm.Interp.native_adequacy hs' hF' hS' hok']
  apply nbeh_congr
  intro fl
  rw [obs_iff_run hfi hcode hty hrs hf hnf (coreReady_inv hr).1 hargs fl,
    obs_iff_run hfi' hcode' hty' (gr ▸ hrs) hg hng (coreReady_inv hr').1 (gp ▸ hargs) fl]
  exact exists_congr fun o => and_congr_left fun _ => hrun args o

/-- **The Core 3.0 behaviours of a native fragment function**, at every profile: on a typed,
native, arity-checked store, the behaviours of a typed invocation of a function whose code is
that of a recognised, arity-checked, folded fragment function are the function's outcomes,
and divergence exactly when it has none. -/
theorem behaviours_eq_run {s : Store H} {a : Nat} {fi : FuncInst H} {ft : FuncType} {bf : BFunc}
    {f : FragFunc} (hs : StoreOk s) (hF : NativeFuncsOk s.funcs)
    (hS : Silmaril.Wasm.Interp.StoreChk s.funcs) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hf : ofBFunc? ft bf = some f) (hn : f.native = true)
    (hst : BExpr.structuredList bf.body = true) {vs : List Val} (hok : InvokeOk s a vs)
    (P : Numerics.Profile) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
      behaviours P closedHost s a vs =
        {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} := by
  obtain ⟨hp, hres⟩ : ft.params = f.params.map (fun t => .num (.int t)) ∧
      ft.results = resultTypes f.result := ofBFunc?_types hf
  have hlift : ft.params.map Validation.liftVal =
      f.params.map fun t => Validation.liftVal (.num (.int t)) := by
    rw [hp, List.map_map]
    rfl
  obtain ⟨args, rfl, hargs⟩ := args_of_invokeOk hok hfi (hlift ▸ hty)
  have hrs : (ft.results.map Validation.liftVal).length = (resultTypes f.result).length := by
    rw [List.length_map, hres]
  refine ⟨args, rfl, hargs, ?_⟩
  rw [Silmaril.Wasm.Interp.native_adequacy hs hF hS hok]
  exact nbeh_eq_run hfi hcode hty hrs hf hn hst hargs

/-- **`invoke_replace` for `setCode`**: the replaced store is native and arity-checked by
`coreReady`; only its typing is assumed. -/
theorem invoke_setCode {s : Store H} {a : Nat} {fi : FuncInst H} {ft : FuncType}
    {bf bf' : BFunc} (hs : StoreOk s) (hs' : StoreOk (setCode s a (coreFunc bf')))
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (ho : optimizeFuncCore? ft bf = some bf') {vs : List Val} (hok : InvokeOk s a vs)
    (P : Numerics.Profile) :
    behaviours P closedHost s a vs = behaviours P closedHost (setCode s a (coreFunc bf')) a vs := by
  obtain ⟨-, -, hr'⟩ := optimizeFuncCore?_inv ho
  obtain ⟨-, hnat', hchk'⟩ := coreReady_inv hr'
  have hF' : NativeFuncsOk (setCode s a (coreFunc bf')).funcs := nativeFuncsOk_setCode hF hnat'
  have hS' : Silmaril.Wasm.Interp.StoreChk (setCode s a (coreFunc bf')).funcs := by
    refine Silmaril.Wasm.Interp.storeChk_modify hS fun fi₀ ps rs hfi₀ hty₀ => ?_
    obtain rfl : fi₀ = fi := Option.some.inj (hfi₀.symm.trans hfi)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty₀.symm.trans hty))
    simpa only [List.length_map] using hchk'
  exact invoke_replace hs hF hS hs' hF' hS' hfi hcode hty (setCode_funcs_a hfi) rfl hty ho hok P

end Silmaril.Proofs.Wasm.SSA.CoreCert
