module

public import Silmaril.Wasm.FX.Asyncify.CPS.Thms
public import Silmaril.Wasm.FX.Asyncify.Analysis.Thms

/-!
# All asyncify instances with a target machine

`Silmaril.Wasm.FX.Asyncify.scheme` indexes the family by `Strategy` (`unwind`, `unwindDispatch`)
and `Opt`. Further strategies have their own instances: the shadow stack
(`Shadow.shadowScheme o`), the whole-program state machine (`SM.smScheme`) and CPS
(`CPS.cpsScheme`). This module collects them into one index, `Variant`, without changing the
family:

* `Variant`, `variant V v`: the instance of a variant;
* **`variant_correct`**: every variant is correct on its fragment (`o.Dom` for the
  instrumenting strategies, every program for the state machine and CPS, which have no call-site
  checks, so the optimizations do not apply to them);
* `variant_comorphism`: its comorphism of behaviour charts;
* **`variants_agree`**: two variants have the same behaviours on every program in both fragments;
* `whole_dom'`, `analyzed_dom`: whole-program instrumentation and the computed analysis put every
  program in the fragment.

The relations between strategies proved directly (not through the kernel) are
`Asyncify.strategies` (unwind to dispatch), `Shadow.shadow_vs_dispatch` and `CPS.sm_vs_cps`, all
equal on every sentence for every target program; and the step bounds of
`Silmaril.Wasm.FX.Asyncify.Steps` (`SM.sm_no_slower_dispatch`, `CPS.cps_no_slower_dispatch`,
`Steps.analyze_no_slower`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Variants

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.Atlas

/-- An asyncify variant: a strategy with its optimization, when it has one. -/
inductive Variant where
  /-- Stack unwinding (`unwind` or `unwindDispatch`) with an optimization. -/
  | family (st : Strategy) (o : Opt)
  /-- Stack unwinding into one linear memory (shadow stack) with an optimization. -/
  | shadow (o : Opt)
  /-- The whole-program state machine with `br_table` dispatch at every step. -/
  | sm
  /-- Continuation-passing style with defunctionalized continuations. -/
  | cps

/-- The instance of a variant. -/
def variant (V : Type) : Variant → Scheme V
  | .family st o => scheme V st o
  | .shadow o => Shadow.shadowScheme V o
  | .sm => SM.smScheme V
  | .cps => CPS.cpsScheme V

variable {V : Type}

/-- **Every variant is correct on its fragment.** -/
theorem variant_correct : ∀ v, (variant V v).Correct
  | .family st o => scheme_correct st o
  | .shadow o => Shadow.shadow_correct o
  | .sm => SM.sm_correct
  | .cps => CPS.cps_correct

/-- The comorphism of a variant. -/
def variant_comorphism (v : Variant) :
    Transition (srcChart (variant V v).dom) (variant V v).tgtChart :=
  (variant V v).comorphism (variant_correct v)

/-- **Any two variants agree** on the programs of both fragments. -/
theorem variants_agree (v w : Variant) (P : Prog (Ins V)) (hv : (variant V v).dom P)
    (hw : (variant V w).dom P) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    (variant V v).run ((variant V v).compile P) test f args =
      (variant V w).run ((variant V w).compile P) test f args :=
  (variant_correct v P hv test f args).trans (variant_correct w P hw test f args).symm

/-- The fragment of a variant without optimization (whole-program instrumentation, or none):
every program. -/
def Variant.whole : Variant → Variant
  | .family st _ => .family st .whole
  | .shadow _ => .shadow .whole
  | .sm => .sm
  | .cps => .cps

theorem whole_dom' (v : Variant) (P : Prog (Ins V)) : (variant V v.whole).dom P := by
  cases v with
  | family st o => cases st <;> exact whole_dom P
  | shadow o => exact whole_dom P
  | sm => trivial
  | cps => trivial

/-- The computed analysis of `Selective` puts every program in the selective fragments. -/
theorem analyzed_dom (st : Strategy) (P : Prog (Ins V)) (n : Nat) :
    (variant V (.family st (Selective.analyzed P n))).dom P ∧
      (variant V (.shadow (Selective.analyzed P n))).dom P := by
  refine ⟨?_, Selective.analyze_sound P n⟩
  cases st <;> exact Selective.analyze_sound P n

/-- info: 'Silmaril.Wasm.FX.Asyncify.Variants.variant_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms variant_correct

end Silmaril.Wasm.FX.Asyncify.Variants
