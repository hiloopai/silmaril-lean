module

public import Silmaril.Wasm.Det.Stateless.Litmus.Defs
public import Silmaril.Wasm.Det.Stateless.Thms
public import Silmaril.Wasm.Det.Core.Litmus.Thms
public import Silmaril.Proofs.Wasm.Det.Stateless.Litmus

/-!
# Litmus tests for stateless code: theorems

Every statement holds at **every** profile `P`.

**The module `slMod`** (`Silmaril.Wasm.Det.Stateless.Litmus.Defs`), with a counter, an immutable
global, a scratch global and an import:

* `twice_stateless`, `pure_stateless`: `twice` and `pure` (which calls `twice` and the import)
  are stateless over the call states of the module, for any entry functions (`wasm_stateless`);
* `readk_stateless`: `readk` reads the immutable global, which no function of the module
  writes, so it is stateless over the call states (`wasm_stateless`: the module check and the
  disjointness of reads and writes);
* `scratch_rejected`: the syntactic checks reject `scratch` (it reads the global it writes);
  `scratch_stateless`: it is stateless over the call states anyway, by its every-run Hoare-logic
  specification ("returns the argument plus one") and the frame property of the module;
* `sl_detModule`: the module is deterministic modulo traps and imports (`wasm_stateless`);
* `not_statelessModule`: the module is **not** stateless: `read` returns `0` initially and `1`
  after `bump`.

So `twice`, `pure`, `readk` and `scratch` are stateless where the module is not.

**The module `litMod`** of `Silmaril.Wasm.Det.Core.Litmus` (a NaN-producing function and a
mutable global with a setter and a getter):

* `lit_one_stateless`: function `0` is stateless over the call states (`wasm_stateless`), while
  the module is not (`Silmaril.Wasm.Det.Core.Litmus.not_statelessModule`);
* `lit_get_det`: function `3` (`global.get`) is deterministic at every call state
  (`wasm_stateless`), while the module is not deterministic at a profile with the
  specification's NaN semantics (`Silmaril.Wasm.Det.Core.Litmus.not_detModule`); `lit_get_rejected`:
  it is not stateless by the checks (and is not stateless).

Proofs: `Silmaril.Proofs.Wasm.Det.Stateless.Litmus`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Stateless.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
  Silmaril.Wasm.Det.Stateless
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Det.Stateless.Litmus (sh_bump sh_read invokeOk_nil' bump_run read_run
  sl_cnt cnt_value₁ slStore₁ sl_globals_length)

/-! ## `slMod` -/

/-- **`twice` is stateless** over the call states of the module. -/
theorem twice_stateless (P : Profile) (Entry : Nat → Prop) :
    StatelessFn P (CallReach P Entry slStore) 1 := by wasm_stateless

/-- **`pure` is stateless** over the call states of the module: its outputs depend only on its
argument and the answers of the import. -/
theorem pure_stateless (P : Profile) (Entry : Nat → Prop) :
    StatelessFn P (CallReach P Entry slStore) 2 := by wasm_stateless

/-- **`readk` is stateless** over the call states of the module: the global it reads is never
written. -/
theorem readk_stateless (P : Profile) (Entry : Nat → Prop) :
    StatelessFn P (CallReach P Entry slStore) 5 := by wasm_stateless

/-- The syntactic checks reject `scratch`, which reads the global it writes, and `read`. -/
theorem scratch_rejected : crCheck slStore 6 = false ∧ statelessCheck slStore 6 = false ∧
    crCheck slStore 4 = false := by
  decide +kernel

/-- **`scratch` is stateless** over the call states of the module, by its Hoare-logic
specification. -/
theorem scratch_stateless (P : Profile) (Entry : Nat → Prop) :
    StatelessFn P (CallReach P Entry slStore) 6 := by
  have hm : moduleCheck slStore = true := by decide +kernel
  refine StatelessFn.anti (fun s hs => ⟨CallReach.funcs_eq hs, ?_⟩)
    (Silmaril.Proofs.Wasm.Det.Stateless.Litmus.scratch_stateless P)
  have hl : s.globals.length = slStore.globals.length :=
    callReach_length (checkSet_sound hm)
      (fun _ _ _ hf => Silmaril.Proofs.Wasm.Det.Stateless.allAddrs_contains hf) hs
  rw [hl, sl_globals_length]
  decide

/-- **The module is deterministic** modulo traps and imports. -/
theorem sl_detModule (P : Profile) (Entry : Nat → Prop) : DetModule P Entry slStore := by
  wasm_stateless

/-- **The module is not stateless**: `read` returns `0` initially and `1` after `bump`. -/
theorem not_statelessModule (P : Profile) : ¬ StatelessModule P slEntry slStore := by
  intro hS
  have hf₁ : slStore₁.funcs = slStore.funcs :=
    Silmaril.Proofs.Wasm.Det.Stateless.setGlobal_funcs slStore 0 (Val.i32 1)
  have hr : CallReach P slEntry slStore slStore₁ :=
    CallReach.call (d := ⟨slStore₁, {}, vals []⟩) (r := .values []) .init
      (show slEntry 3 from ⟨by decide, by decide⟩) (invokeOk_nil' (s := slStore) sh_bump rfl)
      (.stop (bump_run P)) rfl
  have hA : ObsAgree P (invoke slStore 4 []) (invoke slStore₁ 4 []) :=
    hS 4 (show slEntry 4 from ⟨by decide, by decide⟩) slStore slStore₁ [] .init hr
      (invokeOk_nil' (s := slStore) sh_read rfl) (invokeOk_nil' (s := slStore₁) sh_read hf₁)
  have h₀ : Steps P Det.noHost (invoke slStore 4 []) ⟨slStore, {}, vals [Val.i32 0]⟩ :=
    read_run P (s := slStore) rfl sl_cnt
  have h₁ : Steps P Det.noHost (invoke slStore₁ 4 []) ⟨slStore₁, {}, vals [Val.i32 1]⟩ :=
    read_run P (s := slStore₁) hf₁ cnt_value₁
  have h := hA [] _ _ _ _ (.stop h₀) (.stop h₁)
    (.ret (r := .values [Val.i32 0]) (by simp) rfl)
    (.ret (r := .values [Val.i32 1]) (by simp) rfl)
  have h₂ : Val.i32 0 = Val.i32 1 := by simpa using h
  exact absurd h₂ (by decide)

/-! ## `litMod` -/

/-- **Function `0` of `litMod` is stateless** over the call states of the module, which is not
stateless. -/
theorem lit_one_stateless (P : Profile) :
    StatelessFn P (CallReach P Silmaril.Wasm.Det.Core.Litmus.litEntry
      Silmaril.Wasm.Det.Core.Litmus.litStore) 0 := by
  wasm_stateless

/-- **Function `3` of `litMod` (`global.get`) is deterministic** at every call state, although
the module is not deterministic under the specification's NaN semantics. -/
theorem lit_get_det (P : Profile) :
    ∀ s, CallReach P Silmaril.Wasm.Det.Core.Litmus.litEntry Silmaril.Wasm.Det.Core.Litmus.litStore s →
      DetFn P s 3 := by
  wasm_stateless

/-- The checks reject the getter as stateless code, and the NaN function as deterministic code. -/
theorem lit_get_rejected : crCheck Silmaril.Wasm.Det.Core.Litmus.litStore 3 = false ∧
    detCheck Silmaril.Wasm.Det.Core.Litmus.litStore 1 = false := by
  decide +kernel

end Silmaril.Wasm.Det.Stateless.Litmus
