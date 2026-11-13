module

public import Silmaril.Wasm.Det.Core.Litmus.Defs
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Proofs.Wasm.Det.Core.Litmus.Runs

/-!
# Litmus tests for determinism and statelessness: theorems

**Store-free native leaf functions** (`leafCheck`, an executable check):

* `detFn_of_leafCheck`: deterministic modulo traps and imports at **every** profile, in every
  store holding them;
* `statelessFn_of_leafCheck`: stateless over every store holding the same function, at every
  profile;
* the tactic `det_leaf` closes `DetFn P s a` and
  `StatelessFn P (fun t => t.funcs[a]? = s.funcs[a]?) a` for a concrete store by kernel
  evaluation of `leafCheck s a`.

**The litmus module** `litMod` (`one`: `i32.const 1`; `nan`: `f32.add` of two canonical NaNs;
`set`/`get`: write and read a mutable global), allocated by `prepare?` into `litStore`, with
entries `litEntry` (its four exports):

* `one_det`: function `0` is deterministic at every profile, in every call state of the module;
* `nan_not_det`, `not_detModule`: at every profile with the specification's NaN semantics
  (`P.nan = .spec`, e.g. `Profile.spec`), function `1` returns both the positive and the
  negative canonical NaN, so it is not deterministic, and neither is the module;
* `one_stateless`: function `0` is stateless over the call states of the module, at every
  profile;
* `not_statelessModule`: the module is not stateless, at **every** profile: `get` returns `0`
  in the initial store and `5` after `set`.

Hence per-function determinism and statelessness hold where the module-level properties fail.

Proofs: `Silmaril.Proofs.Wasm.Det.Core.Litmus.{Leaf,Runs}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Core.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Det.Core.Litmus (nan_run set_run get_run nanP_allowed nanN_allowed
  invokeOk_nil lit_shape1 lit_shape2 lit_shape3 f32v)

/-! ## Store-free native leaf functions -/

/-- **Leaf check ⇒ determinism modulo traps and imports**, at every profile. -/
theorem detFn_of_leafCheck {P : Profile} {s : Store Nat} {a : Nat} (h : leafCheck s a = true) :
    DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.Core.Leaf.detFn_of_leafCheck h

/-- **Leaf check ⇒ statelessness** over every store holding the same function, at every
profile. -/
theorem statelessFn_of_leafCheck {P : Profile} {s : Store Nat} {a : Nat}
    (h : leafCheck s a = true) : StatelessFn P (fun t => t.funcs[a]? = s.funcs[a]?) a :=
  Silmaril.Proofs.Wasm.Det.Core.Leaf.statelessFn_of_leafCheck h

/-- `leafCheck` only reads the function instances. -/
theorem leafCheck_congr {s t : Store Nat} (h : s.funcs = t.funcs) (a : Nat) :
    leafCheck s a = leafCheck t a := by
  simp only [leafCheck, h]

/-- Closes `DetFn P s a` or `StatelessFn P (fun t => t.funcs[a]? = s.funcs[a]?) a` for a
store-free native leaf function of a concrete store, by kernel evaluation of `leafCheck`. -/
macro "det_leaf" : tactic => `(tactic| first
  | exact Silmaril.Wasm.Det.Core.Litmus.detFn_of_leafCheck (by decide +kernel)
  | exact Silmaril.Wasm.Det.Core.Litmus.statelessFn_of_leafCheck (by decide +kernel))

/-! ## The litmus module -/

/-- Function `0` passes the leaf check. -/
theorem lit_leaf0 : leafCheck litStore 0 = true := by decide +kernel

/-- `det_leaf` on function `0` of the initial store. -/
example (P : Profile) : DetFn P litStore 0 := by det_leaf

/-- **Function `0` is deterministic** at every profile, in every call state of the module. -/
theorem one_det (P : Profile) {s : Store Nat} (hs : CallReach P litEntry litStore s) :
    DetFn P s 0 :=
  detFn_of_leafCheck ((leafCheck_congr (CallReach.funcs_eq hs) 0).trans lit_leaf0)

/-- **Function `0` is stateless** over the call states of the module, at every profile. -/
theorem one_stateless (P : Profile) : StatelessFn P (CallReach P litEntry litStore) 0 :=
  StatelessFn.anti (fun _ hs => by rw [CallReach.funcs_eq hs]) (statelessFn_of_leafCheck lit_leaf0)

/-- **Function `1` is not deterministic** at a profile with the specification's NaN semantics:
it returns the positive and the negative canonical NaN. -/
theorem nan_not_det {P : Profile} (hP : P.nan = .spec) : ¬ DetCall P litStore 1 [] := by
  intro hD
  have h := hD [] _ _ _ _ (.stop (nan_run hP nanP_allowed)) (.stop (nan_run hP nanN_allowed))
    (.ret (r := .values [f32v nanP]) (by simp) rfl)
    (.ret (r := .values [f32v nanN]) (by simp) rfl)
  have h₁ : Out.ret (.values [f32v nanP]) = Out.ret (.values [f32v nanN]) := h.1
  have h₂ : nanP.toNat = nanN.toNat := by
    simp only [Out.ret.injEq, Result.values.injEq, List.cons.injEq, and_true, f32v,
      Val.num.injEq] at h₁
    exact congrArg (fun v : NumVal => v.bits.toNat) h₁
  exact absurd h₂ (by decide)

/-- **The module is not deterministic** at a profile with the specification's NaN semantics. -/
theorem not_detModule {P : Profile} (hP : P.nan = .spec) : ¬ DetModule P litEntry litStore :=
  fun hD => nan_not_det hP
    (hD litStore .init 1 (show 1 < 4 by decide) [] (invokeOk_nil lit_shape1 rfl))

/-- **The module is not stateless**, at every profile: `get` returns `0` initially and `5`
after `set`. -/
theorem not_statelessModule (P : Profile) : ¬ StatelessModule P litEntry litStore := by
  intro hS
  have hr : CallReach P litEntry litStore (litStore.setGlobal 1 (Val.i32 5)) :=
    CallReach.call (d := ⟨litStore.setGlobal 1 (Val.i32 5), {}, vals []⟩) (r := .values [])
      .init (show 2 < 4 by decide) (invokeOk_nil lit_shape2 rfl) (.stop (set_run P)) rfl
  have hA : ObsAgree P (invoke litStore 3 []) (invoke (litStore.setGlobal 1 (Val.i32 5)) 3 []) :=
    hS 3 (show 3 < 4 by decide) _ _ [] .init hr (invokeOk_nil lit_shape3 rfl)
      (invokeOk_nil lit_shape3 rfl)
  have h := hA [] _ _ _ _ (.stop (get_run P).1) (.stop (get_run P).2)
    (.ret (r := .values [Val.i32 0]) (by simp) rfl)
    (.ret (r := .values [Val.i32 5]) (by simp) rfl)
  have h₁ : Val.i32 0 = Val.i32 5 := by simpa using h
  exact absurd h₁ (by decide)

end Silmaril.Wasm.Det.Core.Litmus
