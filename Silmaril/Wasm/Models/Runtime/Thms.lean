module

public import Silmaril.Wasm.Models.Runtime.Defs
public import Silmaril.Proofs.Wasm.Models.Runtime.Step
public import Silmaril.Proofs.Wasm.Models.Runtime.Mono
public import Silmaril.Wasm.Behaviour.Semantics.V3

/-!
# The runtime invariant of a feature set: preservation

* `step_rtInFeat`: **every Core 3.0 step keeps `Rt.InFeat S`**, at every profile `P` and for
  every host that keeps the store in `S` (`Rt.HostIn S`: the only way a step can change the
  store's functions is a host call);
* `steps_rtInFeat`, `trace_rtInFeat`: along finite runs and infinite traces;
* `invoke_rtInFeat`: invoking any function of a store in `S` starts in `Rt.InFeat S` (the
  configuration `$invoke` builds is `vals ++ [ref.func a, call_ref dt]`);
* `instrB_of_inFeatB`, `codeIn_expression`: source code of `S` is runtime code of `S`;
* `hostIn_of_keeps`: hosts that keep the functions (and throw only under `exn`) are `HostIn`;
* `instrB_mono`, `codeIn_mono`, `storeIn_mono`, `inFeat_mono`, `hostThrowsIn_mono`:
  monotone in `S`.

So a feature set `S` with decidable `Instr.InFeat S` (`Syntax`), closed under subterms
(`Syntax.Thms`), is a **well-behaved restriction**: the restricted Core chart `core|S`
(`Silmaril.Wasm.Models.Charts`) is the Core chart on the domain `StoreIn S ∧ HostIn S`, and every
run from that domain stays in it.

Proofs: `Silmaril.Proofs.Wasm.Models.Runtime.{Basic,Family,Step}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.Rt

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {S : FeatureSet} {H : Type}

/-- **Preservation**: every Core 3.0 step keeps the runtime invariant of `S`, at every profile,
for every host that keeps the store in `S`. -/
theorem step_rtInFeat {P : Profile} {host : HostSemantics H} (hh : HostIn S host)
    {c c' : Config H} (h : Step P host c c') (hc : InFeat S c) : InFeat S c' :=
  Silmaril.Proofs.Wasm.Models.Rt.step_inFeat hh h hc

theorem steps_rtInFeat {P : Profile} {host : HostSemantics H} (hh : HostIn S host)
    {c c' : Config H} (h : Steps P host c c') (hc : InFeat S c) : InFeat S c' := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact step_rtInFeat hh hs ih

/-- Along an infinite trace from a configuration of `S`, every configuration is of `S`. -/
theorem trace_rtInFeat {P : Profile} {host : HostSemantics H} (hh : HostIn S host)
    {tr : Nat → Config H} (ht : ∀ n, Step P host (tr n) (tr (n + 1))) (h0 : InFeat S (tr 0))
    (n : Nat) : InFeat S (tr n) := by
  induction n with
  | zero => exact h0
  | succ n ih => exact step_rtInFeat hh (ht n) ih

theorem codeIn_vals (vs : List Val) : CodeIn S (vals vs) :=
  Silmaril.Proofs.Wasm.Models.Rt.codeIn_vals vs

/-- Invoking a function of a store of `S` starts in the runtime invariant. -/
theorem invoke_rtInFeat {s : Store H} (hs : StoreIn S s) (a : Nat) (vs : List Val) :
    InFeat S (invoke s a vs) :=
  ⟨by simp [invoke, Silmaril.Proofs.Wasm.Models.Rt.codeIn_append], hs⟩

/-- Source instructions of `S` are runtime instructions of `S`. -/
theorem instrB_of_inFeatB {i : Instr} (h : Instr.inFeatB S i = true) : instrB S i = true :=
  Silmaril.Proofs.Wasm.Models.Rt.instrB_of_inFeatB h

theorem codeIn_expression {is : List Instr} (h : Instr.insInFeatB S is = true) :
    CodeIn S (expression is) :=
  Silmaril.Proofs.Wasm.Models.Rt.codeIn_expression h

/-- A host that keeps the functions and throws only under `exn` keeps the store in `S`. -/
theorem hostIn_of_keeps {host : HostSemantics H} (hk : HostKeeps host)
    (ht : HostThrowsIn S host) : HostIn S host := by
  intro h s vs s' r hr hs
  refine ⟨fun a fi fn ha hf => hs a fi fn ((hk h s vs s' r hr) ▸ ha) hf, ?_⟩
  rintro a rfl
  exact ht h s vs s' a hr

/-! ## Monotonicity in the feature set -/

theorem instrB_mono {T : FeatureSet} (h : S ≤ T) {i : Instr} (hs : instrB S i = true) :
    instrB T i = true :=
  Silmaril.Proofs.Wasm.Models.Rt.instrB_mono h i hs

theorem codeIn_mono {T : FeatureSet} (h : S ≤ T) {l : List Admin} (hs : CodeIn S l) :
    CodeIn T l :=
  Silmaril.Proofs.Wasm.Models.Rt.codeIn_mono h l hs

theorem storeIn_mono {T : FeatureSet} (h : S ≤ T) {s : Store H} (hs : StoreIn S s) :
    StoreIn T s :=
  Silmaril.Proofs.Wasm.Models.Rt.storeIn_mono h hs

theorem inFeat_mono {T : FeatureSet} (h : S ≤ T) {c : Config H} (hc : InFeat S c) :
    InFeat T c :=
  ⟨codeIn_mono h hc.1, storeIn_mono h hc.2⟩

theorem hostThrowsIn_mono {T : FeatureSet} (h : S ≤ T) {host : HostSemantics H}
    (hs : HostThrowsIn S host) : HostThrowsIn T host :=
  fun hh s vs s' a hr => Silmaril.Wasm.Models.has_of_le h (hs hh s vs s' a hr)

end Silmaril.Wasm.Models.Rt
