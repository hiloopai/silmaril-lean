module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs

/-!
# Round 7, REH route 2: soundness of the flow check, stated

`Round7.NxTyped` checks the script statically (`NxTyped.flowItems_fixed`). This header states
what that check is for: the evaluator, run in the round-7 environment `utf8Env B`, preserves
conformance (`NxTyped.vtB`) at the types the check assigns.

* `ArgsVT S T ws pts`: evaluated arguments conform to parameter types; an argument passed for
  a definition parameter names a definition that may stand for it (`NxTyped.defSub`).
* `fillV S ws`: a generic definition's type parameters stand for `.base` when the evaluated
  type arguments are export-free, and for `.unk` otherwise (`NxTyped.tpFill`, read on
  evaluated arguments). `parV` and `resV` are the parameter and result types at such a call.
* `DefsVT S T env n`: at fuel `n`, every definition with a parameter entry in `T`, applied to
  conforming arguments, returns a conforming value, whether one of its clauses answers or, when
  none applies, the primitives do.
* `BuiltinsVT S T env`: the primitives of `env` return conforming values on conforming
  arguments.

**`Round7.NxSound.Task.flowSound`** (frozen, open): in `utf8Env B`, with primitives that
conform, `DefsVT sigX tsigFixed (utf8Env B) n` holds at every fuel. With it, every comparison
site that `NxSites` passes compares an export-free value at runtime, in every scope the
evaluator reaches from a `Step` rule whose quantifiers conform (route 2, part (a)). The proof
is an induction on fuel over the evaluator's 29 members, using the value lemmas of
`Round7/NxTyped/Ops.lean` at each operation and `NxTyped.flowItems_fixed` at each clause and
rule; it is not done.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxSound

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

/-- **Evaluated arguments conform to parameter types.** -/
def ArgsVT (S : Sig) (T : TSig) : List ArgV → List PT → Prop
  | [], [] => True
  | .val v :: ws, .exp a :: ps => vtB S a v = true ∧ ArgsVT S T ws ps
  | .defName g :: ws, .defn dps r :: ps => defSub S T g dps r = true ∧ ArgsVT S T ws ps
  | .typ _ :: ws, .other :: ps => ArgsVT S T ws ps
  | .gram _ :: ws, .other :: ps => ArgsVT S T ws ps
  | _, _ => False

/-- The evaluated type arguments are export-free. -/
def tyArgsNxV (S : Sig) (ws : List ArgV) : Bool :=
  ws.all fun w => match w with
    | .typ t => nxAT S.good (toAT t)
    | _ => true

/-- What a generic definition's type parameters stand for at a call with evaluated
arguments `ws`. -/
def fillV (S : Sig) (ws : List ArgV) : AT := if tyArgsNxV S ws then .base else .unk

/-- The parameter types of `f` at evaluated arguments `ws`. -/
def parV (S : Sig) (T : TSig) (f : String) (ws : List ArgV) : Option (List PT) :=
  (T.params.lookup f).map fun p => p.2.map (substPT p.1 (fillV S ws))

/-- The result type of `f` at evaluated arguments `ws`. -/
def resV (S : Sig) (T : TSig) (f : String) (ws : List ArgV) : AT :=
  match T.gres.lookup f with
  | some (tps, r) => substTP tps (fillV S ws) r
  | none => (S.results.lookup f).getD .unk

/-- **Definitions conform at fuel `n`**: a definition with a parameter entry in `T`, applied
to conforming arguments, returns a conforming value, from a clause or, when no clause applies,
from the primitives. -/
def DefsVT (S : Sig) (T : TSig) (env : Env) (n : Nat) : Prop :=
  ∀ (f : String) (d : DefDef) (pts : List PT) (ws : List ArgV) (v : Value),
    env.findDef? f = some d → parV S T f ws = some pts → ArgsVT S T ws pts →
    (tryClauses n env d.2.2 ws = .ok v ∨
      (tryClauses n env d.2.2 ws = .error .undef ∧ env.builtins.call f ws = some v)) →
    vtB S (resV S T f ws) v = true

/-- **The primitives conform**: on conforming arguments they return conforming values. -/
def BuiltinsVT (S : Sig) (T : TSig) (env : Env) : Prop :=
  ∀ (f : String) (pts : List PT) (ws : List ArgV) (v : Value),
    parV S T f ws = some pts → ArgsVT S T ws pts → env.builtins.call f ws = some v →
    vtB S (resV S T f ws) v = true

/-- **The flow check is sound** (frozen, open): in the round-7 environment, with conforming
primitives, definitions conform at every fuel. See the module docstring. -/
def Task.flowSound : Prop :=
  ∀ B : Builtins, BuiltinsVT sigX tsigFixed (utf8Env B) →
    ∀ n, DefsVT sigX tsigFixed (utf8Env B) n

end Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
