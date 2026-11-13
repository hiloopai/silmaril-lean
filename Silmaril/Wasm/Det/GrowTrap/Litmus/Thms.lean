module

public import Silmaril.Wasm.Det.GrowTrap.Litmus.Defs
public import Silmaril.Wasm.Det.GrowTrap.Thms
public import Silmaril.Proofs.Wasm.Det.GrowTrap.Litmus

/-!
# Litmus tests for subset 2 (allocation failure traps): theorems

The module `growMod` (`Silmaril.Wasm.Det.GrowTrap.Litmus.Defs`), allocated into `growStore`, with
entries `growEntry` (its four exports):

| Theorem | Statement | Profiles |
| --- | --- | --- |
| `guarded_det` | function `0` (grow, `local.tee`, guard) is `DetFn` in every call state | every `P` |
| `plain_det` | function `1` (grow, guard without `local.tee`) likewise | every `P` |
| `caller_det` | function `3` (calls `0`, then stores and loads) likewise | every `P` |
| `check_unguarded` | the check rejects function `2` (unguarded `memory.grow`) | — |
| `unguarded_not_det` | `P.grow = .nondet → ¬ DetCall P growStore 2 []`: it returns `0` and `-1` | spec grow policy |
| `not_detModule`, `spec_not_detModule` | the module is not deterministic | spec grow policy, `Profile.spec` |

So functions `0`, `1` and `3` are deterministic modulo traps and imports where the module is
not: per-function results in a nondeterministic module. The checks are computed by
`decide +kernel` (the tactic `grow_trap`).

Proofs: `Silmaril.Proofs.Wasm.Det.GrowTrap.Litmus` (explicit runs of function `2`). New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.GrowTrap.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.GrowTrap
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Det.GrowTrap.Litmus (unguarded_runs invokeOk_unguarded)

/-! ## The check -/

theorem check_guarded : check growStore 0 = true := by decide +kernel
theorem check_plain : check growStore 1 = true := by decide +kernel
theorem check_caller : check growStore 3 = true := by decide +kernel
/-- The unguarded grow is rejected. -/
theorem check_unguarded : check growStore 2 = false := by decide +kernel

/-- `grow_trap` on function `0` of the initial store. -/
example (P : Profile) : DetFn P growStore 0 := by grow_trap

/-- `grow_trap` on function `3` (which calls function `0`). -/
example (P : Profile) : DetFn P growStore 3 := by grow_trap

/-! ## Per-function determinism in every call state -/

/-- A checked function of `growStore` is deterministic in every call state of the module. -/
theorem det_of_check {P : Profile} {a : Nat} (h : check growStore a = true) {s : Store Nat}
    (hs : CallReach P growEntry growStore s) : DetFn P s a :=
  detFn_of_check (by rw [check_congr (CallReach.funcs_eq hs)]; exact h)

/-- **Function `0` (grow behind the guard, with `local.tee`) is deterministic** modulo traps
and imports at every profile, in every call state of the module. -/
theorem guarded_det (P : Profile) {s : Store Nat} (hs : CallReach P growEntry growStore s) :
    DetFn P s 0 :=
  det_of_check check_guarded hs

/-- **Function `1` (grow behind the guard, without `local.tee`) is deterministic.** -/
theorem plain_det (P : Profile) {s : Store Nat} (hs : CallReach P growEntry growStore s) :
    DetFn P s 1 :=
  det_of_check check_plain hs

/-- **Function `3` (a call of function `0`, then a store and a load) is deterministic.** -/
theorem caller_det (P : Profile) {s : Store Nat} (hs : CallReach P growEntry growStore s) :
    DetFn P s 3 :=
  det_of_check check_caller hs

/-! ## The unguarded grow -/

/-- **Function `2` is not deterministic** at a profile with the specification's grow policy: it
returns `0` (the grow succeeds) and `-1` (it fails). -/
theorem unguarded_not_det {P : Profile} (hP : P.grow = .nondet) : ¬ DetCall P growStore 2 [] := by
  intro hD
  obtain ⟨⟨s', h₀⟩, h₁⟩ := unguarded_runs hP
  have h := hD [] _ _ _ _ (.stop h₀) (.stop h₁)
    (.ret (r := .values [Val.i32 0]) (by simp) rfl)
    (.ret (r := .values [Val.i32 (BitVec.allOnes 32)]) (by simp) rfl)
  have h₂ : Out.ret (.values [Val.i32 0]) = Out.ret (.values [Val.i32 (BitVec.allOnes 32)]) := h.1
  have h₃ : (0 : BitVec 32).toNat = (BitVec.allOnes 32).toNat := by
    simp only [Out.ret.injEq, Result.values.injEq, List.cons.injEq, and_true, Val.i32,
      Val.num.injEq] at h₂
    exact congrArg (fun v : NumVal => v.bits.toNat) h₂
  exact absurd h₃ (by decide)

/-- **The module is not deterministic** at a profile with the specification's grow policy. -/
theorem not_detModule {P : Profile} (hP : P.grow = .nondet) :
    ¬ DetModule P growEntry growStore :=
  fun hD => unguarded_not_det hP
    (hD growStore .init 2 (show 2 < 4 by decide) [] invokeOk_unguarded)

/-- The module is not deterministic at the specification profiles. -/
theorem spec_not_detModule (nd : Bool) (r : Numerics.RelaxedChoice) :
    ¬ DetModule (Profile.spec nd r) growEntry growStore :=
  not_detModule rfl

end Silmaril.Wasm.Det.GrowTrap.Litmus
