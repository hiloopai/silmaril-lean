module

public import Silmaril.Wasm.FX.Asyncify.Variants.Thms
public import Silmaril.Wasm.Models.FXAsyncFX.Thms
public import Silmaril.Wasm.Models.FXAsyncBack.Thms
public import Silmaril.Wasm.Models.FXAsyncSus.Thms

/-!
# Asyncify on WasmFX programs: from `StepFX'` to every asyncify target

The handler kernel `FXAsync.sstep` is the source of every asyncify instance; its relation to the
WasmFX semantics `StepFX'` is on main: `FXAsyncFX.kernel_in_fx` (kernel behaviours are `StepFX'`
behaviours of the encoding, on the fragment `Supported`), and `FXAsyncSus.beh_eq_tight` (the
converse, so equality, on the tight fragment in the deterministic profile without host calls).
Composing these with the correctness of an instance relates a WasmFX program directly to its
asyncified target:

* **`instance_in_fx`**: for every correct instance `A` and program `W` of its fragment, every
  behaviour of the asyncified call is a `StepFX'` behaviour of the WasmFX program
  `fxInit S f args` (through `obsB`);
* **`instance_eq_fx`**: on the tight fragment, the `StepFX'` behaviours of the WasmFX program
  are exactly the images of the asyncified call's behaviours;
* `variant_in_fx`, `variant_eq_fx`: the same for every `Variants.Variant` (unwinding, dispatch,
  shadow stack with any sound optimization, the computed analysis, the state machine, CPS).

**The WasmFX examples** (the encodings of `FXAsyncFX`/`FXAsyncBack`, each with a proved `Ok`):

* `gen_variant`: the **generator** of the WasmFX explainer (`exW`: yield `1`, return `2`; the
  consumer resumes it under a second handler and adds): for every variant whose fragment
  contains it, the image of its target behaviours is `{returns [3]}`, the `StepFX'`
  behaviours of the WasmFX program; `gen_all`: every variant with whole-program instrumentation
  or none, and `gen_analyzed`: both unwinding strategies and the shadow stack with the computed
  analysis;
* `add_variant`, `res_variant`: a plain function (`1 + 2`) and a resumed fresh continuation
  (`5`), on the calm fragment.
* `gen_sm_run`, `gen_cps_run`: the generator's state-machine and CPS targets, run in closed form.

What this does **not** say: only programs of the encodable fragment of `FXAsyncFX` (one-clause,
argument-less `resume`, inlined handlers, `i32`) are covered, and the asyncify targets are
abstract machines, not Core 3.0 `Step`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Explainer

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.FX.Asyncify (Scheme Strategy)
open Silmaril.Wasm.FX.Asyncify.Variants
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (TightSupported)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- **Every behaviour of an asyncified WasmFX program is a `StepFX'` behaviour.** -/
theorem instance_in_fx {A : Scheme Val} (hA : A.Correct) (hW : A.dom W) (hok : Ok S W)
    (f : Nat) (args : List Val) (hsup : Supported W (sInit f (args.map .val))) :
    ∀ b ∈ A.run (A.compile W) i32Test f (args.map .val),
      obsB b ∈ behavioursFX' S.P S.host S.fx (fxInit S f args) := by
  rw [hA W hW i32Test f _]
  exact kernel_in_fx S hok (rel_init S f args) hsup

/-- **On the tight fragment, a WasmFX program and its asyncified form have the same
behaviours.** -/
theorem instance_eq_fx {o : GrowKind → Nat → Nat → Nat → Bool} (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) {A : Scheme Val} (hA : A.Correct) (hW : A.dom W) (hok : Ok S W)
    (f : Nat) (args : List Val) (hsup : TightSupported W (sInit f (args.map .val))) :
    behavioursFX' S.P S.host S.fx (fxInit S f args) =
      obsB '' A.run (A.compile W) i32Test f (args.map .val) := by
  rw [hA W hW i32Test f _]
  exact Silmaril.Wasm.Models.FXAsyncSus.beh_eq_tight S hP hH hok (rel_init S f args) hsup

theorem variant_in_fx (v : Variant) (hW : (variant Val v).dom W) (hok : Ok S W) (f : Nat)
    (args : List Val) (hsup : Supported W (sInit f (args.map .val))) :
    ∀ b ∈ (variant Val v).run ((variant Val v).compile W) i32Test f (args.map .val),
      obsB b ∈ behavioursFX' S.P S.host S.fx (fxInit S f args) :=
  instance_in_fx S (variant_correct v) hW hok f args hsup

theorem variant_eq_fx {o : GrowKind → Nat → Nat → Nat → Bool} (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (v : Variant) (hW : (variant Val v).dom W) (hok : Ok S W) (f : Nat)
    (args : List Val) (hsup : TightSupported W (sInit f (args.map .val))) :
    behavioursFX' S.P S.host S.fx (fxInit S f args) =
      obsB '' (variant Val v).run ((variant Val v).compile W) i32Test f (args.map .val) :=
  instance_eq_fx S hP hH (variant_correct v) hW hok f args hsup

/-! ## The examples -/

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (exW exS exOk) in
/-- **The generator, asyncified by any variant**: one behaviour, returning `[3]`, as the WasmFX
program under `StepFX'`. -/
theorem gen_variant (o : GrowKind → Nat → Nat → Nat → Bool) (v : Variant)
    (hW : (variant Val v).dom exW) :
    obsB '' (variant Val v).run ((variant Val v).compile exW) i32Test 1 [] =
      {.returns [Val.i32 3]} :=
  (variant_eq_fx (exS (Profile.deterministic o) noHost) rfl rfl v hW (exOk _ _) 1 []
    Silmaril.Proofs.Wasm.Models.FXAsyncSus.ex_tight).symm.trans
    (Silmaril.Wasm.Models.FXAsyncSus.ex_beh o)

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (exW) in
/-- The generator under every variant without optimization. -/
theorem gen_all (o : GrowKind → Nat → Nat → Nat → Bool) (v : Variant) :
    obsB '' (variant Val v.whole).run ((variant Val v.whole).compile exW) i32Test 1 [] =
      {.returns [Val.i32 3]} :=
  gen_variant o v.whole (whole_dom' v exW)

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (exW) in
/-- The generator with the computed analysis, under both unwinding strategies and the shadow
stack. -/
theorem gen_analyzed (o : GrowKind → Nat → Nat → Nat → Bool) (st : Strategy) (n : Nat) :
    obsB '' (variant Val (.family st (Selective.analyzed exW n))).run
        ((variant Val (.family st (Selective.analyzed exW n))).compile exW) i32Test 1 [] =
      {.returns [Val.i32 3]} ∧
    obsB '' (variant Val (.shadow (Selective.analyzed exW n))).run
        ((variant Val (.shadow (Selective.analyzed exW n))).compile exW) i32Test 1 [] =
      {.returns [Val.i32 3]} :=
  ⟨gen_variant o _ (analyzed_dom st exW n).1, gen_variant o _ (analyzed_dom st exW n).2⟩

open Silmaril.Proofs.Wasm.Models.FXAsyncBack (addW addS addOk add_calm) in
/-- `1 + 2` under any variant. -/
theorem add_variant (o : GrowKind → Nat → Nat → Nat → Bool) (v : Variant)
    (hW : (variant Val v).dom addW) :
    obsB '' (variant Val v).run ((variant Val v).compile addW) i32Test 0 [] =
      {.returns [Val.i32 3]} :=
  (variant_eq_fx (addS (Profile.deterministic o) noHost) rfl rfl v hW (addOk _ _) 0 []
    (Silmaril.Wasm.Models.FXAsyncSus.tight_of_calm add_calm)).symm.trans
    (Silmaril.Wasm.Models.FXAsyncBack.add_beh o)

open Silmaril.Proofs.Wasm.Models.FXAsyncBack (resW resS resOk res_calm) in
/-- A resumed fresh continuation returning `5`, under any variant. -/
theorem res_variant (o : GrowKind → Nat → Nat → Nat → Bool) (v : Variant)
    (hW : (variant Val v).dom resW) :
    obsB '' (variant Val v).run ((variant Val v).compile resW) i32Test 1 [] =
      {.returns [Val.i32 5]} :=
  (variant_eq_fx (resS (Profile.deterministic o) noHost) rfl rfl v hW (resOk _ _) 1 []
    (Silmaril.Wasm.Models.FXAsyncSus.tight_of_calm res_calm)).symm.trans
    (Silmaril.Wasm.Models.FXAsyncBack.res_beh o)

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (exW) in
/-- The generator's state-machine target, run in closed form. -/
theorem gen_sm_run :
    runN (SM.pstep exW 1 i32Test) 40 (SM.pInit []) = .stop (.done [.val (Val.i32 3)]) := by
  rfl

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (exW) in
/-- The generator's CPS target, run in closed form. -/
theorem gen_cps_run :
    runN (CPS.cstep (CPS.compK exW) 1 i32Test) 40 (CPS.cInit (CPS.compK exW) 1 []) =
      .stop (.done [.val (Val.i32 3)]) := by
  rfl

/-- info: 'Silmaril.Wasm.FX.Asyncify.Explainer.gen_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gen_variant

end Silmaril.Wasm.FX.Asyncify.Explainer
