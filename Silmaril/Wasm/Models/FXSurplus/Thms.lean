module

public import Silmaril.Proofs.Wasm.Models.FXSurplus.Refute
public import Silmaril.Proofs.Wasm.Models.FXSurplus.Tight

/-!
# `suspend` with surplus operands, determinism of FX runs, preservation for `StepFX'`

Three open items of the WasmFX models (`docs/projects/wasm-wasi.md`), settled on one typed program
`surC` (`Defs`: `i32.const 7; i32.const 1; suspend $t` under a handler, `$t : [i32] → []`,
inside a label of arity `2` whose code resumes the continuation), and one general statement:

* **Surplus operands add behaviours** (refutation of "a longer payload is harmless" for
  `StepFX'` in general): `[1]` is a `StepFX'` result of `surC` (`beh_surplus`: payload `[7, 1]`,
  the branch drops `7` and the continuation has lost it), but not a `StepFXS` result
  (`not_behS_surplus`), whose result `[1, 7]` (`behS_tight`) is also a `StepFX'` result
  (`beh_tight`). Every profile, host and FX function table.
* **Determinism of FX runs.** Refuted for `StepFX'` in general: `surC` has the different
  results `[1]`, `[1, 7]` and `[7, 1]` (`not_subsingleton`; `[7, 1]` comes from `resume` passing
  the `1` to the continuation, `beh_arg`). Proved on the tight fragment of the asyncify
  encoding: at most one behaviour (`behFX_subsingleton_tight`, deterministic profile, no host
  calls), since there the behaviours are those of the deterministic kernel.
* **Preservation for `StepFX'`** (on `FXPresI.envP`, the environment of `preservationI`):
  refuted, `¬ PresV surM P host fx` (`not_presV`): `surC` is typed at `[i32, i32]` (`surC_ok`)
  and its surplus run reaches `[1]`, which is not (`end_one_not_ok`). `StepFXS`, the typed
  restriction, is the relation that preserves typing (`FXPresI.preservationI`).

Not decided: whether surplus operands add behaviours on the *encoded kernel fragment*
(`FXAsyncSus`: one-value function returns through frames, which check arity). There the
continuation that lost operands is resumed inside its function's frame, and a frame returns only
with exactly its result arity, so a lost operand can only make a run stuck; but no proof is
given.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXSurplus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (SCfg Ins Prog sstep beh)
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (TightSupported)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **The surplus program is typed** at `[i32, i32]` (no continuation slots). -/
theorem surC_ok : ConfigOk (envP surM) [] (surC H) [.val ti32, .val ti32] :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.surC_ok

/-- **A surplus payload gives the result `[1]`.** -/
theorem beh_surplus : .returns [Val.i32 1] ∈ behavioursFX' P host fx (surC H) :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.beh_surplus

/-- **The tight payload gives `[1, 7]`.** -/
theorem beh_tight : .returns [Val.i32 1, Val.i32 7] ∈ behavioursFX' P host fx (surC H) :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.beh_tight

/-- **`resume` with an argument gives `[7, 1]`.** -/
theorem beh_arg : .returns [Val.i32 7, Val.i32 1] ∈ behavioursFX' P host fx (surC H) :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.beh_arg

/-- `[1, 7]` is a typed (`StepFXS`) result. -/
theorem behS_tight : .returns [Val.i32 1, Val.i32 7] ∈ behavioursFXS P host fx (surC H) :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.behS_tight

/-- **`[1]` is not a typed result**: surplus operands add a behaviour. -/
theorem not_behS_surplus : .returns [Val.i32 1] ∉ behavioursFXS P host fx (surC H) :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.not_behS_surplus

/-- **`StepFX'` runs are not deterministic**: `surC` has more than one behaviour. -/
theorem not_subsingleton : ¬ (behavioursFX' P host fx (surC H)).Subsingleton :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.not_subsingleton

/-- **Preservation fails for `StepFX'`.** -/
theorem not_presV : ¬ PresV surM P host fx :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.not_presV

/-- **FX runs are deterministic on the tight fragment** of the asyncify encoding. -/
theorem behFX_subsingleton_tight (S : Setup H) {W : Prog (Ins Val)}
    {o : GrowKind → Nat → Nat → Nat → Bool} (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : TightSupported W x) :
    (behavioursFX' S.P S.host S.fx c).Subsingleton :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.behFX_subsingleton_tight S hP hH hok hR hsup

/-- A deterministic machine has at most one behaviour. -/
theorem beh_subsingleton {C V : Type} (step : C → Silmaril.Wasm.Models.FXAsync.Res C V) (c : C) :
    (beh step c).Subsingleton :=
  Silmaril.Proofs.Wasm.Models.FXSurplus.beh_subsingleton step c

/-- info: 'Silmaril.Wasm.Models.FXSurplus.not_behS_surplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_behS_surplus

/-- info: 'Silmaril.Wasm.Models.FXSurplus.not_presV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_presV

/-- info: 'Silmaril.Wasm.Models.FXSurplus.not_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_subsingleton

/-- info: 'Silmaril.Wasm.Models.FXSurplus.behFX_subsingleton_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms behFX_subsingleton_tight

end Silmaril.Wasm.Models.FXSurplus
