module

public import Silmaril.Wasm.Det.Shared.Stateless.Thms
public import Silmaril.Wasm.Det.Stateless.Litmus.Thms

/-!
# Statelessness under store-writing hosts: litmus

The module `slMod` of `Silmaril.Wasm.Det.Stateless.Litmus` (an import `h`, a counter `$cnt`, an
immutable `$k`, functions `twice` (1), `pure` (2, calls `twice` and `h`), `bump` (3),
`read` (4, reads `$cnt`), `readk` (5, reads `$k`)), against every host keeping the function
instances (`KeepFuncs`: it may write globals, including `$cnt` and `$k`), at every profile:

* `twice_statelessS`, `pure_statelessS`: `twice` and `pure` read no global, so they are
  stateless over **every** store holding the module's functions (`pure` calls the import);
* `readk_statelessS`: `readk` is stateless over the stores holding the functions and agreeing on
  `$k`;
* `read_not_statelessS`: `read` is not stateless over the stores holding the functions: from
  `slStore` it returns `0`, from `slStore₁` (`$cnt = 1`, the store after `bump`) it returns `1`.

The checks are `decide +kernel` evaluations of `statelessCheck` and `readsOf`. New.
-/

public section

namespace Silmaril.Wasm.Det.Shared.Litmus

open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Stateless Silmaril.Wasm.Det.Stateless.Litmus
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Det.Stateless.Litmus (sh_read invokeOk_nil' read_run sl_cnt cnt_value₁
  slStore₁)
open Silmaril.Wasm.Numerics (Profile)

theorem sl_checks : statelessCheck slStore 1 = true ∧ statelessCheck slStore 2 = true ∧
    statelessCheck slStore 5 = true ∧ readsOf slStore (closure slStore [1]) = [] ∧
    readsOf slStore (closure slStore [2]) = [] ∧ readsOf slStore (closure slStore [5]) = [1] := by
  decide +kernel

/-- A function whose call closure reads no global is stateless under every host keeping the
functions, over every store holding the module's functions. -/
theorem statelessS_of_noReads {P : Profile} {a : Nat} (hc : statelessCheck slStore a = true)
    (hr : readsOf slStore (closure slStore [a]) = []) :
    StatelessFnS P KeepFuncs (fun s => s.funcs = slStore.funcs) a :=
  (statelessFnS_of_check hc).anti fun _ h => ⟨h, fun _ hg => by rw [hr] at hg; simp at hg⟩

/-- **`twice` is stateless under every host keeping the functions**, over every store holding
the module's functions. -/
theorem twice_statelessS (P : Profile) :
    StatelessFnS P KeepFuncs (fun s => s.funcs = slStore.funcs) 1 :=
  statelessS_of_noReads sl_checks.1 sl_checks.2.2.2.1

/-- **`pure` is stateless under every host keeping the functions** (it calls the import `h`),
over every store holding the module's functions. -/
theorem pure_statelessS (P : Profile) :
    StatelessFnS P KeepFuncs (fun s => s.funcs = slStore.funcs) 2 :=
  statelessS_of_noReads sl_checks.2.1 sl_checks.2.2.2.2.1

/-- **`readk` is stateless under every host keeping the functions**, over the stores holding the
functions and agreeing on `$k`. -/
theorem readk_statelessS (P : Profile) :
    StatelessFnS P KeepFuncs
      (fun s => s.funcs = slStore.funcs ∧ s.globals[1]? = slStore.globals[1]?) 5 :=
  (statelessFnS_of_check sl_checks.2.2.1).anti fun _ h =>
    ⟨h.1, fun g hg => by
      rw [sl_checks.2.2.2.2.2] at hg
      have : g = 1 := by simpa using hg
      subst this
      exact h.2⟩

/-- **`read` is not stateless** over the stores holding the module's functions. -/
theorem read_not_statelessS (P : Profile) :
    ¬ StatelessFnS P KeepFuncs (fun s => s.funcs = slStore.funcs) 4 := by
  intro hS
  have hf₁ : slStore₁.funcs = slStore.funcs :=
    Silmaril.Proofs.Wasm.Det.Stateless.setGlobal_funcs slStore 0 (Val.i32 1)
  have hA := hS slStore slStore₁ [] rfl hf₁ (invokeOk_nil' (s := slStore) sh_read rfl)
    (invokeOk_nil' (s := slStore₁) sh_read hf₁)
  have h := hA [] _ _ _ _ (.stop (read_run P (s := slStore) rfl sl_cnt))
    (.stop (read_run P (s := slStore₁) hf₁ cnt_value₁))
    (.ret (r := .values [Val.i32 0]) (by simp) rfl)
    (.ret (r := .values [Val.i32 1]) (by simp) rfl)
  have h₂ : Val.i32 0 = Val.i32 1 := by simpa using h
  exact absurd h₂ (by decide)

end Silmaril.Wasm.Det.Shared.Litmus
