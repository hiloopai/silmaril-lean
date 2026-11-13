module

public import Silmaril.Wasm.Det.NaN.Defs
public import Silmaril.Proofs.Wasm.Det.NaN.Runs

/-!
# Determinism up to NaN payloads: theorems

Every statement holds at an **arbitrary** profile `P` (NaN payload and sign choices, `$ND`,
relaxed choices and grow failures are all allowed by `P`).

**Headline** (`nanDetCfg_of_nCfg`): every configuration of the fragment (`NCfg set c`: float
code that never observes NaN bits, see `Silmaril.Wasm.Det.NaN.Defs`) is deterministic modulo traps,
imports and NaN payloads (`NaNDetCfg P c`): two runs with the same import calls and answers
that both reach non-trapping stops have outputs equal up to NaN payloads and stores equal up to
the NaN payloads of their globals. Per function and per module: `nanDetFn_of_nanCheck`,
`nanDetModule_of_nanCheck`, by the executable store check `nanCheck`; the tactic **`nan_det`**
closes these goals for concrete stores by kernel evaluation.

The proof: canonicalising every NaN (`canonCfg`) maps every step at `P` to a step of the
deterministic profile `profile neverFail` followed by canonicalisation
(`Silmaril.Proofs.Wasm.Det.NaN.step_good`), and those steps have silmaril-lean's one-step diamond,
hence unique normal forms.

**The output sink.** Outputs equal up to NaN payloads are equal as soon as one of them has no
NaN value (`eq_of_canonOut`). So under `NaNFreeOut P c` (every non-trapping output of `c` is
NaN-free):

* `obsAgree_of_nanDet`: output determinism `ObsAgree P c c` (the shared notion of
  `Silmaril.Wasm.Det.Core`);
* `detCall_of_nanCheck`, `detFn_of_nanCheck`: without `global.set` (`nanCheck false`), runs
  keep the store (`runs_store`), so this is full determinism modulo traps and imports
  (`DetCall`, `DetFn`).

`NaNFreeOut` is a verification condition on **one** run of the deterministic profile:
`nanFreeOut_of_canonical` (if a run of `c` at `profile neverFail` returns a NaN-free result,
every run at every profile only stops at NaN-free outputs). This is how a NaN guard (a
comparison `x == x` selecting a constant) or a float comparison returning an integer is
discharged (`Silmaril.Wasm.Det.NaN.Litmus`).

Proofs: `Silmaril.Proofs.Wasm.Det.NaN.{Float,Canon,Frag,Step,Runs}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NaN

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **Determinism modulo traps, imports and NaN payloads** of every configuration of the
fragment, at every profile. -/
theorem nanDetCfg_of_nCfg {P : Profile} {set : Bool} {c : Config Nat} (hc : NCfg set c) :
    NaNDetCfg P c :=
  Silmaril.Proofs.Wasm.Det.NaN.nanDetCfg_of_nCfg hc

/-- `nanCheck` decides that every Wasm function of the store is in the fragment. -/
theorem nFuncs_of_nanCheck {set : Bool} {s : Store Nat} (h : nanCheck set s = true) :
    NFuncs set s.funcs :=
  Silmaril.Proofs.Wasm.Det.NaN.nFuncs_of_nanCheck h

/-- **Per function**: in a store passing `nanCheck`, every invocation of every function is
deterministic modulo traps, imports and NaN payloads, at every profile. -/
theorem nanDetCall_of_nanCheck {P : Profile} {set : Bool} {s : Store Nat}
    (h : nanCheck set s = true) (a : Nat) (vs : List Val) : NaNDetCfg P (invoke s a vs) :=
  nanDetCfg_of_nCfg (Silmaril.Proofs.Wasm.Det.NaN.nCfg_invoke (nFuncs_of_nanCheck h) a vs)

/-- **Per function**, as `NaNDetFn`. -/
theorem nanDetFn_of_nanCheck {P : Profile} {set : Bool} {s : Store Nat}
    (h : nanCheck set s = true) (a : Nat) : NaNDetFn P s a :=
  fun vs _ => nanDetCall_of_nanCheck h a vs

/-- `nanCheck` only reads the function instances. -/
theorem nanCheck_congr {set : Bool} {s t : Store Nat} (h : s.funcs = t.funcs) :
    nanCheck set s = nanCheck set t := by
  simp only [nanCheck, h]

/-- **Per module**: if the initial store passes `nanCheck`, every entry is deterministic modulo
traps, imports and NaN payloads at every reachable call state, at every profile. -/
theorem nanDetModule_of_nanCheck {P : Profile} {set : Bool} {Entry : Nat → Prop}
    {s₀ : Store Nat} (h : nanCheck set s₀ = true) : NaNDetModule P Entry s₀ :=
  fun _ hs a _ => nanDetFn_of_nanCheck ((nanCheck_congr (CallReach.funcs_eq hs)).trans h) a

/-! ## The output sink -/

/-- **Outputs equal up to NaN payloads are equal when one of them is NaN-free.** -/
theorem eq_of_canonOut {o₁ o₂ : Out} (h : canonOut o₁ = canonOut o₂) (hf : OutNaNFree o₁) :
    o₂ = o₁ :=
  Silmaril.Proofs.Wasm.Det.NaN.eq_of_canonOut h hf

/-- **Output determinism** from determinism up to NaN payloads and NaN-free outputs. -/
theorem obsAgree_of_nanDet {P : Profile} {c : Config Nat} (hD : NaNDetCfg P c)
    (hF : NaNFreeOut P c) : ObsAgree P c c := fun tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂ =>
  (eq_of_canonOut (hD tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂).1 (hF tr d₁ o₁ h₁ ho₁)).symm

/-- Without `global.set`, runs of the fragment keep the store. -/
theorem runs_store {P : Profile} {c d : Config Nat} {tr : List Call} (hc : NCfg false c)
    (h : Runs P c tr d) : d.store = c.store :=
  Silmaril.Proofs.Wasm.Det.NaN.runs_store hc h

/-- Without `global.set`, the call states of a module are its initial store. -/
theorem callReach_eq {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (h₀ : nanCheck false s₀ = true) (h : CallReach P Entry s₀ s) : s = s₀ := by
  induction h with
  | init => rfl
  | @call s a vs tr d r hs _ _ hr _ ih =>
    have hs' : nanCheck false s = true := by rw [ih]; exact h₀
    have hc : NCfg false (invoke s a vs) :=
      Silmaril.Proofs.Wasm.Det.NaN.nCfg_invoke (nFuncs_of_nanCheck hs') a vs
    exact (runs_store hc hr).trans ih

/-- **Full determinism modulo traps and imports** of a fragment configuration without
`global.set` whose outputs are NaN-free. -/
theorem detCfg_of_nCfg {P : Profile} {c : Config Nat} (hc : NCfg false c)
    (hF : NaNFreeOut P c) : DetCfg P c := fun tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂ =>
  ⟨obsAgree_of_nanDet (nanDetCfg_of_nCfg hc) hF tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂,
    (runs_store hc h₁).trans (runs_store hc h₂).symm⟩

/-- **Per call**: a function of a store passing `nanCheck false` whose outputs are NaN-free is
deterministic modulo traps and imports. -/
theorem detCall_of_nanCheck {P : Profile} {s : Store Nat} (h : nanCheck false s = true)
    {a : Nat} {vs : List Val} (hF : NaNFreeOut P (invoke s a vs)) : DetCall P s a vs :=
  detCfg_of_nCfg (Silmaril.Proofs.Wasm.Det.NaN.nCfg_invoke (nFuncs_of_nanCheck h) a vs) hF

/-- **Per function**, as `DetFn`. -/
theorem detFn_of_nanCheck {P : Profile} {s : Store Nat} (h : nanCheck false s = true) {a : Nat}
    (hF : ∀ vs, InvokeOk s a vs → NaNFreeOut P (invoke s a vs)) : DetFn P s a :=
  fun vs hok => detCall_of_nanCheck h (hF vs hok)

/-- **The output sink as a verification condition on one deterministic run**: if a run of a
fragment configuration at the deterministic profile `profile neverFail` returns a NaN-free
result, every run at every profile stops only at NaN-free outputs. -/
theorem nanFreeOut_of_canonical {P : Profile} {set : Bool} {c n : Config Nat} (hc : NCfg set c)
    (hn : Steps (profile neverFail) Det.noHost c n) {r : Result} (hr : OutAt n (.ret r))
    (hf : OutNaNFree (.ret r)) : NaNFreeOut P c :=
  Silmaril.Proofs.Wasm.Det.NaN.nanFreeOut_of_canonical hc hn hr hf

/-- Closes `NaNDetFn P s a`, `NaNDetCfg P (invoke s a vs)` or `NaNDetModule P Entry s` for a
concrete store by kernel evaluation of `nanCheck`. -/
macro "nan_det" : tactic => `(tactic| first
  | exact Silmaril.Wasm.Det.NaN.nanDetFn_of_nanCheck (set := true) (by decide +kernel) _
  | exact Silmaril.Wasm.Det.NaN.nanDetCall_of_nanCheck (set := true) (by decide +kernel) _ _
  | exact Silmaril.Wasm.Det.NaN.nanDetModule_of_nanCheck (set := true) (by decide +kernel))

end Silmaril.Wasm.Det.NaN
