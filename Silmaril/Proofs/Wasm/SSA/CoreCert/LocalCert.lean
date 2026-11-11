module

public import Silmaril.Proofs.Wasm.SSA.CoreCert.Module
public import Silmaril.Proofs.Wasm.SSA.CoreCert.Local

@[expose] public section

/-!
# The local run-time certificate (proofs)

`runCert_spec`: when `runCert m g ft bf` holds for a recognised, arity-checked fragment
function `bf` of a closed module `m`, the Core 3.0 behaviours of every typed invocation of `g`
in `m`'s allocated store are the function's fragment outcomes, and divergence exactly when it
has none, at every profile. The store of `m` need not be typed in any particular way beyond
what instantiation gives, and its other functions need not be native or arity-checked: the
behaviours are those in the allocated store of `stubModule m g` (`behaviours_local`), where
`behaviours_eq_run` applies. New proofs.
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA
open Silmaril.Wasm.SSA.CoreCert

theorem stub_lower_funcs {m : BModule} {g : Nat} {bf : BFunc} (h : m.funcs[g]? = some bf) :
    (stubModule m g).lower.funcs[g]? = some (coreFunc bf) := by
  simp [stubModule, BModule.lower, h]

/-- Same type, module instance and code: the same function instance. -/
theorem funcs_eq_of_same {H : Type} {s u : Store H} {g : Nat} (h : sameFuncAt s u g = true)
    {fi fj : FuncInst H} (hs : s.funcs[g]? = some fi) (hu : u.funcs[g]? = some fj)
    (hc : fi.code = fj.code) : u.funcs[g]? = s.funcs[g]? := by
  unfold sameFuncAt at h
  rw [hs, hu] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [hs, hu]
  obtain ⟨t, mi, c⟩ := fi
  obtain ⟨t', mi', c'⟩ := fj
  obtain ⟨rfl, rfl⟩ := h
  cases hc
  rfl

/-- Integer arguments are leaf values. -/
theorem valP_toVal (a : Nat) (args : List WVal) : ∀ v ∈ args.map WVal.toVal, ValP a v := by
  intro v hv
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
  cases w <;> trivial

theorem map_toVal_inj' {as bs : List WVal} (h : as.map WVal.toVal = bs.map WVal.toVal) :
    as = bs := by
  have e : ∀ w : WVal, WVal.ofVal? w.toVal = some w := fun w => by cases w <;> rfl
  have hi : Function.Injective WVal.toVal := fun a b hab =>
    Option.some.inj ((e a).symm.trans ((congrArg WVal.ofVal? hab).trans (e b)))
  exact (List.map_injective_iff.mpr hi) h

/-- What `runCert` checked. -/
theorem runCert_inv {m : BModule} {g : Nat} {ft : FuncType} {bf : BFunc}
    (h : runCert m g ft bf = true) :
    leafFunc (coreFunc bf) = true ∧ coreReady ft bf = true ∧ closedValid m = true ∧
      closedValid (stubModule m g) = true ∧ ∃ s u, allocStore? m = some s ∧
        allocStore? (stubModule m g) = some u ∧ storeReady u g ft = true ∧
        sameFuncAt s u g = true := by
  simp only [runCert, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hl, hr⟩, hv⟩, hv'⟩, hm⟩ := h
  refine ⟨hl, hr, hv, hv', ?_⟩
  split at hm
  · rename_i s u hs hu
    simp only [Bool.and_eq_true] at hm
    exact ⟨s, u, hs, hu, hm.1, hm.2⟩
  · cases hm

/-- **The local certificate**: the Core behaviours of function `g` of a closed module are its
fragment outcomes. -/
theorem runCert_spec {m : BModule} {g : Nat} {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (hbf : m.funcs[g]? = some bf) (hf : ofBFunc? ft bf = some f) (hn : f.native = true)
    (hc : runCert m g ft bf = true) :
    ∃ s : Store Empty, allocStore? m = some s ∧
      (∀ args : List WVal, args.map WVal.type = f.params → InvokeOk s g (args.map WVal.toVal)) ∧
      ∀ (P : Numerics.Profile) (vs : List Val), InvokeOk s g vs →
        ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
          behaviours P closedHost s g vs =
            {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} := by
  obtain ⟨hleaf, hr, hv, hvst, s, u, hs, hu, hready, hsame⟩ := runCert_inv hc
  obtain ⟨hokU, hSU, hFU, fj, hfj, hcodej, htyj⟩ := checked_store (stub_lower_funcs hbf) hu hvst hready
  obtain ⟨c, st, hp, rfl⟩ := allocStore?_inv hs
  obtain ⟨fi, hfi, hcodei⟩ := prepare_code hp (beq_iff_eq.mp hv) (lower_funcs hbf)
  have heq : u.funcs[g]? = c.store.funcs[g]? := funcs_eq_of_same hsame hfi hfj (hcodei.trans hcodej.symm)
  have hfij : fi = fj := Option.some.inj (hfi.symm.trans (heq.symm.trans hfj))
  have hL : LeafAt c.store g := ⟨fi, coreFunc bf, hfi, hcodei, hleaf⟩
  obtain ⟨hp', -⟩ : ft.params = f.params.map (fun t => .num (.int t)) ∧
      ft.results = resultTypes f.result := ofBFunc?_types hf
  have hlift : ft.params.map Validation.liftVal =
      f.params.map fun t => Validation.liftVal (.num (.int t)) := by
    rw [hp', List.map_map]
    rfl
  have htyi : Validation.DefType.funcType? fi.type = some
      (f.params.map fun t => Validation.liftVal (.num (.int t)),
        ft.results.map Validation.liftVal) := by
    rw [hfij, htyj, hlift]
  refine ⟨c.store, hs, fun args hargs => invokeOk_of_type hfi htyi hargs, fun P vs hok => ?_⟩
  obtain ⟨args, rfl, hargs⟩ := args_of_invokeOk hok hfi htyi
  have hokU' : InvokeOk u g (args.map WVal.toVal) :=
    invokeOk_of_type hfj (hfij ▸ htyi) hargs
  obtain ⟨args', hargs', -, hbeh⟩ :=
    behaviours_eq_run hokU hFU hSU hfj hcodej htyj hf hn (coreReady_inv hr).1 hokU' P
  have he : args' = args := map_toVal_inj' hargs'.symm
  refine ⟨args, rfl, hargs, ?_⟩
  rw [behaviours_local hL heq (valP_toVal g args), hbeh, he]

/-- What `optimizeFuncLocal` checked. -/
theorem optimizeFuncLocal_inv {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncLocal m g = some bf') :
    ∃ bf ft, m.funcs[g]? = some bf ∧ m.funcType? bf.type = some ft ∧
      optimizeFuncCore? ft bf = some bf' ∧ runCert m g ft bf = true := by
  simp only [optimizeFuncLocal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bf, hbf, ft, hft, bf'', ho, hif⟩ := h
  split at hif
  · obtain rfl : bf'' = bf' := Option.some.inj hif
    exact ⟨bf, ft, hbf, hft, ho, ‹_›⟩
  · cases hif

/-- Sets of outcome images agree for equivalent functions. -/
theorem outcome_set_eq {f g : FragFunc} {args : List WVal}
    (h : ∀ o, f.Run args o ↔ g.Run args o) :
    {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} =
      {b | (∃ o, g.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ g.Run args o)} := by
  ext b
  simp only [Set.mem_ofPred_eq, h]

/-- **The local certificate of a replacement**: if `optimizeFuncLocal m g = some bf'` and a
module `m''` holds `bf'` as function `g` with `runCert` at `g`'s source type, invocations of
`g` have the same Core 3.0 behaviours in the allocated stores of `m` and `m''`, every profile. -/
theorem optimizeFuncLocal_replace {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncLocal m g = some bf') {m'' : BModule} (hbf'' : m''.funcs[g]? = some bf')
    (hr : ∀ bf ft, m.funcs[g]? = some bf → m.funcType? bf.type = some ft →
      runCert m'' g ft bf' = true) :
    ∃ s s'' : Store Empty, allocStore? m = some s ∧ allocStore? m'' = some s'' ∧
      ∀ (P : Numerics.Profile) (vs : List Val), InvokeOk s g vs →
        behaviours P closedHost s g vs = behaviours P closedHost s'' g vs := by
  obtain ⟨bf, ft, hbf, hft, ho, hrc⟩ := optimizeFuncLocal_inv h
  obtain ⟨hon, -, -⟩ := optimizeFuncCore?_inv ho
  obtain ⟨f, f', hf, hnf, hf', hnf', gp, -, hrun⟩ := optimizeFuncNative?_spec hon
  obtain ⟨s, hs, -, hbeh⟩ := runCert_spec hbf hf hnf hrc
  obtain ⟨s'', hs'', hinv'', hbeh''⟩ := runCert_spec hbf'' hf' hnf' (hr bf ft hbf hft)
  refine ⟨s, s'', hs, hs'', fun P vs hok => ?_⟩
  obtain ⟨args, rfl, hargs, hb⟩ := hbeh P vs hok
  obtain ⟨args'', hargs'', -, hb''⟩ := hbeh'' P _ (hinv'' args (hargs.trans gp.symm))
  have he : args'' = args := map_toVal_inj' hargs''.symm
  rw [hb, hb'', he]
  exact outcome_set_eq (hrun args)

end Silmaril.Proofs.Wasm.SSA.CoreCert
