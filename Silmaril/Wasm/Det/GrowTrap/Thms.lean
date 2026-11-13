module

public import Silmaril.Wasm.Det.GrowTrap.Defs
public import Silmaril.Proofs.Wasm.Det.GrowTrap.Main

/-!
# Subset 2 (no floats, allocation failure traps): theorems

Every statement holds at an **arbitrary** profile `P`; in particular at `Profile.spec`, where
every `memory.grow` may fail.

* **`detCfg_of_inv`**: every configuration satisfying the runtime invariant `Inv G` of the
  subset is **deterministic modulo traps and imports** (`Silmaril.Wasm.Det.Core.DetCfg`): two runs
  with the same import calls and answers that both reach a non-trapping stop have the same
  output and the same store;
* **`grow_choice`** (`inv_detUpTo`): every host-free step from an `Inv G` configuration at `P`
  is a step of the deterministic profile `profile neverFail` (a valid grow succeeds), or it is
  `Doomed` (no host-free run from it reaches a non-trapping stop). The steps at `P` that are not
  `profile neverFail` steps are failures of a `memory.grow` that could have succeeded; the guard
  that follows them traps (or is stuck), so they are doomed. Grow success is the only
  non-trapping continuation;
* `inv_closed`: `Inv G` is closed under host-free steps and under resuming an import call with
  any answer;
* per function, per module: `detCall_of_funcsOk`, `detFn_of_funcsOk` (`G a` and every function
  of `G` has a body of the subset whose calls stay in `G`), `detModule_of_funcsOk`;
* the executable check: `detFn_of_check`, `detModule_of_check`; the tactic **`grow_trap`**
  closes `DetFn P s a` and `DetModule P Entry s` for concrete stores by kernel evaluation of
  `check`.

With `Silmaril.Wasm.Det.Core.DetFn.oracle` these give: from the same call state and against the same
import oracle, two Core runs of a checked function that both return without trapping return the
same result in the same store, whatever the profile chose for each `memory.grow`.

Proofs: `Silmaril.Proofs.Wasm.Det.GrowTrap.{Basic,Closure,Doom,Transfer,Main}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.GrowTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

/-- `Inv G` is closed under host-free steps and resumptions, at every profile. -/
theorem inv_closed {G : Nat → Prop} (P : Profile) : Closed P (Inv G) :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.inv_closed P

/-- **Grow choices**: every host-free step from an `Inv G` configuration, at any profile, is a
step of `profile neverFail` or is doomed. -/
theorem grow_choice {G : Nat → Prop} {P : Profile} {c : Config Nat} (hc : Inv G c) :
    DetUpTo P neverFail c :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.inv_detUpTo hc

/-- **Determinism modulo traps and imports of the subset**, at every profile. -/
theorem detCfg_of_inv {G : Nat → Prop} {P : Profile} {c : Config Nat} (hc : Inv G c) :
    DetCfg P c :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.detCfg_of_inv hc

/-- The invocation of a function in `G` satisfies the invariant. -/
theorem inv_invoke {G : Nat → Prop} {s : Store Nat} {a : Nat} (ha : G a)
    (hF : FuncsOk G s.funcs) (vs : List Val) : Inv G (invoke s a vs) :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.inv_invoke ha hF vs

/-- **Per call**: every invocation (typed or not) of a function in `G` is deterministic modulo
traps and imports. -/
theorem detCall_of_funcsOk {G : Nat → Prop} {P : Profile} {s : Store Nat} {a : Nat} (ha : G a)
    (hF : FuncsOk G s.funcs) (vs : List Val) : DetCall P s a vs :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.detCall_of_funcsOk ha hF vs

/-- **Per function.** -/
theorem detFn_of_funcsOk {G : Nat → Prop} {P : Profile} {s : Store Nat} {a : Nat} (ha : G a)
    (hF : FuncsOk G s.funcs) : DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.detFn_of_funcsOk ha hF

/-- **Per module**: every entry in `G`, every function of `G` in the subset. -/
theorem detModule_of_funcsOk {G : Nat → Prop} {P : Profile} {Entry : Nat → Prop}
    {s₀ : Store Nat} (hE : ∀ a, Entry a → G a) (hF : FuncsOk G s₀.funcs) :
    DetModule P Entry s₀ :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.detModule_of_funcsOk hE hF

/-- The executable check gives `FuncsOk` for its list. -/
theorem funcsOk_of_checkG {F : List (FuncInst Nat)} {L : List Nat} (h : checkG F L = true) :
    FuncsOk (· ∈ L) F :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.funcsOk_of_checkG h

/-- **Soundness of the check, per function**, at every profile. -/
theorem detFn_of_check {P : Profile} {s : Store Nat} {a : Nat} (h : check s a = true) :
    DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.detFn_of_check h

/-- **Soundness of the check, per module**, at every profile. -/
theorem detModule_of_check {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (h : ∀ a, Entry a → check s₀ a = true) : DetModule P Entry s₀ :=
  Silmaril.Proofs.Wasm.Det.GrowTrap.detModule_of_check h

/-- `check` only reads the function instances. -/
theorem check_congr {s t : Store Nat} (h : s.funcs = t.funcs) (a : Nat) :
    check s a = check t a := by
  simp only [check, h]

/-- **Same call state, same answers, same non-trapping result**, for a checked function: the
headline consequence through `Silmaril.Wasm.Det.Core.DetFn.oracle`. -/
theorem check_oracle {P : Profile} {s : Store Nat} {a : Nat} (h : check s a = true)
    {vs : List Val} (hok : InvokeOk s a vs) {F : Nat → List Val → Result} {d₁ d₂ : Config Nat}
    (h₁ : Steps P (oracleHost F) (invoke s a vs) d₁)
    (h₂ : Steps P (oracleHost F) (invoke s a vs) d₂) {r₁ r₂ : Result} (hr₁ : r₁ ≠ .trap)
    (hr₂ : r₂ ≠ .trap) (hd₁ : d₁.code = r₁.toAdmin) (hd₂ : d₂.code = r₂.toAdmin) :
    r₁ = r₂ ∧ d₁.store = d₂.store :=
  DetFn.oracle (detFn_of_check h) hok h₁ h₂ hr₁ hr₂ hd₁ hd₂

/-- Closes `DetFn P s a` or `DetModule P Entry s` (with a decidable, bounded `Entry`) for a
concrete store whose functions pass the executable check of subset 2, by kernel evaluation. -/
macro "grow_trap" : tactic => `(tactic| first
  | exact Silmaril.Wasm.Det.GrowTrap.detFn_of_check (by decide +kernel)
  | exact Silmaril.Wasm.Det.GrowTrap.detModule_of_check (by decide +kernel))

end Silmaril.Wasm.Det.GrowTrap
