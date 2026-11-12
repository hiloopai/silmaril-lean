module

public import Silmaril.Wasm.SpecTec.Sim20.Whole.Defs

/-!
# A 2.0 erratum for `Step`, and the corrected forward whole-step target

`Sim20.Whole.not_wholeStepValid` refutes the 2.0 whole-step target for the wasm-2.0 script as
written, for two independent reasons (upstream notes 5 and 6 of track F4):

* `Step` has no `ctxt-instrs` rule, so `NOP NOP` is stuck (`Whole.stuck_nopNop`);
* `Step/pure`, `Step/read`, `Step/ctxt-label` and `Step/ctxt-frame` quantify their code as `instr*`
  where `admininstr*` is meant, so no administrative instruction is ever produced or consumed
  through them, and `UNREACHABLE` does not trap (`Whole.stuck_unreachable`).

V2 (`Silmaril.Wasm.V2.Execution.Step`) also departs from the script at `ctxt-frame`: the script keeps
the inner frame unchanged across the step, V2 lets the inner step change it (V2's deviation 2).

`stepErratum20` is an `IL.Erratum` for the definition `Step` (`Scripts.Wasm20.Original.d368`) that
repairs all three, in the shape of the wasm-3.0 script's rules:

* `pure` and `read` take `admininstr*` on both sides (no `instr <: admininstr` coercion);
* `ctxt-instrs` is added: `z; val* admininstr* admininstr_1* ~> z'; val* admininstr'* admininstr_1*`
  from `z; admininstr* ~> z'; admininstr'*`, if `val*` or `admininstr_1*` is non-empty;
* `ctxt-label` takes `admininstr*` bodies;
* `ctxt-frame` gives the inner frame a successor `f''`:
  `s; f; FRAME_ n {f'} admininstr* ~> s'; f; FRAME_ n {f''} admininstr'*` from
  `s; f'; admininstr* ~> s'; f''; admininstr'*`.

Rules 4–21 of `Step` (`local.set` … `data.drop`) are kept verbatim, after the five structural rules.
The erratum applies to `Scripts.Wasm20.fixed` (`Sim20.StepFix.stepErratum20_applies`, kernel `rfl`);
`fixedS20` is the result, `simEnv20S B` its environment with primitives `B`.

`Task.wholeStepValidS` is `Task.wholeStepValid` read in `simEnv20S` at the spec's builtins, on
configurations whose image is typed and whose conversions V2 defines: the corrected forward and
backward whole-step target. It is **stated, not proved**.

No upstream issue is filed; `issue := 0` marks that.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StepFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

/-! ## Building blocks -/

/-- `admininstr*`. -/
abbrev adminsTy : Typ := .iterT (.varT "admininstr" []) .list

/-- `x*`, the iteration of the variable `x` over the list bound to `xs`. -/
def iterV (x xs : IL.Id) : Exp := .iterE (.varE x) (.mk .list [.mk x (.varE xs)])

/-- `z; code`. -/
def cfgE (z code : Exp) : Exp := .caseE "%;%" (.tupE [z, code])

/-- `s; f`. -/
def stE (s f : Exp) : Exp := .caseE "%;%" (.tupE [s, f])

/-- A premise `rel: l ~> r`. -/
def premE (rel : IL.Id) (l r : Exp) : Prem := .rulePr rel [] "%~>%" (.tupE [l, r])

/-! ## The corrected structural rules -/

/-- `Step/pure` at `admininstr*`. -/
def pureFix : Rule :=
  .ruleD "pure" [.expP "z" (.varT "state" []), .expP "instr*" adminsTy, .expP "instr'*" adminsTy]
    "%~>%" (.tupE [cfgE (.varE "z") (iterV "instr" "instr*"),
      cfgE (.varE "z") (iterV "instr'" "instr'*")])
    [premE "Step_pure" (iterV "instr" "instr*") (iterV "instr'" "instr'*")]

/-- `Step/read` at `admininstr*`. -/
def readFix : Rule :=
  .ruleD "read" [.expP "z" (.varT "state" []), .expP "instr*" adminsTy, .expP "instr'*" adminsTy]
    "%~>%" (.tupE [cfgE (.varE "z") (iterV "instr" "instr*"),
      cfgE (.varE "z") (iterV "instr'" "instr'*")])
    [premE "Step_read" (cfgE (.varE "z") (iterV "instr" "instr*")) (iterV "instr'" "instr'*")]

/-- `val*` coerced to `admininstr*`. -/
def valsE : Exp :=
  .iterE (.subE (.varE "val") (.varT "val" []) (.varT "admininstr" []))
    (.mk .list [.mk "val" (.varE "val*")])

/-- `Step/ctxt-instrs`, the rule wasm-2.0 lacks. -/
def ctxtInstrsFix : Rule :=
  .ruleD "ctxt-instrs" [.expP "z" (.varT "state" []), .expP "val*" (.iterT (.varT "val" []) .list),
      .expP "instr*" adminsTy, .expP "instr_1*" adminsTy, .expP "z'" (.varT "state" []),
      .expP "instr'*" adminsTy]
    "%~>%" (.tupE [
      cfgE (.varE "z") (.catE valsE (.catE (iterV "instr" "instr*") (iterV "instr_1" "instr_1*"))),
      cfgE (.varE "z'") (.catE valsE (.catE (iterV "instr'" "instr'*") (iterV "instr_1" "instr_1*")))])
    [premE "Step" (cfgE (.varE "z") (iterV "instr" "instr*"))
      (cfgE (.varE "z'") (iterV "instr'" "instr'*")),
     .ifPr (.binE .orOp .boolT (.cmpE .neOp .boolT (iterV "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterV "instr_1" "instr_1*") (.listE [])))]

/-- `Step/ctxt-label` at `admininstr*` bodies. -/
def ctxtLabelFix : Rule :=
  .ruleD "ctxt-label" [.expP "z" (.varT "state" []), .expP "n" (.varT "n" []),
      .expP "instr_0*" (.iterT (.varT "instr" []) .list), .expP "instr*" adminsTy,
      .expP "z'" (.varT "state" []), .expP "instr'*" adminsTy]
    "%~>%" (.tupE [
      cfgE (.varE "z") (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", iterV "instr_0" "instr_0*",
        iterV "instr" "instr*"])]),
      cfgE (.varE "z'") (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n",
        iterV "instr_0" "instr_0*", iterV "instr'" "instr'*"])])])
    [premE "Step" (cfgE (.varE "z") (iterV "instr" "instr*"))
      (cfgE (.varE "z'") (iterV "instr'" "instr'*"))]

/-- `Step/ctxt-frame` with a successor inner frame `f''`. -/
def ctxtFrameFix : Rule :=
  .ruleD "ctxt-frame" [.expP "s" (.varT "store" []), .expP "f" (.varT "frame" []),
      .expP "n" (.varT "n" []), .expP "f'" (.varT "frame" []), .expP "instr*" adminsTy,
      .expP "s'" (.varT "store" []), .expP "f''" (.varT "frame" []), .expP "instr'*" adminsTy]
    "%~>%" (.tupE [
      cfgE (stE (.varE "s") (.varE "f")) (.listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n",
        .varE "f'", iterV "instr" "instr*"])]),
      cfgE (stE (.varE "s'") (.varE "f")) (.listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n",
        .varE "f''", iterV "instr'" "instr'*"])])])
    [premE "Step" (cfgE (stE (.varE "s") (.varE "f'")) (iterV "instr" "instr*"))
      (cfgE (stE (.varE "s'") (.varE "f''")) (iterV "instr'" "instr'*"))]

/-! ## The erratum -/

/-- The relation `Step` of the pinned wasm-2.0 script (`d368` is `rec { relation Step }`). -/
noncomputable def stepRel20 : Def :=
  match Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d368 with
  | .recD [d] => d
  | d => d

/-- The corrected `Step`: the five structural rules, then rules 4–21 of the original. -/
noncomputable def stepFix20 : Def :=
  match stepRel20 with
  | .relD x ps op t rules =>
      .relD x ps op t ([pureFix, readFix, ctxtInstrsFix, ctxtLabelFix, ctxtFrameFix] ++ rules.drop 4)
  | d => d

/-- **The erratum** (`IL.Erratum`, target `Step`). -/
noncomputable def stepErratum20 : Erratum where
  issue := 0
  summary := "Step (wasm-2.0): add ctxt-instrs, type the structural rules' code as admininstr*, \
    give ctxt-frame a successor inner frame"
  target := "Step"
  corrected := stepFix20

/-- The wasm-2.0 script with the errata of `Errata/Wasm20.lean` and `stepErratum20` applied. -/
noncomputable def fixedS20 : Script := replaceDefs stepFix20 Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed

/-- The lookup environment of `fixedS20`, with the primitives `B`. -/
noncomputable def simEnv20S (B : Builtins) : Env := (envOfScript fixedS20).withBuiltins B

/-! ## The corrected target -/

/-- **The 2.0 whole-step target on the corrected script** (frozen, open): `Task.wholeStepValid`
read in `simEnv20S` at the spec's builtins (`Sim.Floats.floatIntB`), on configurations whose image
is typed and whose active conversions V2 defines (`CvtOkL`). Fixing the builtins and asking for
`CvtOkL` is what `Whole.not_bwdLive20_floatB` forces: at builtins that interpret `$extend__` the
generic `$cvtop__` clauses compute where V2 traps, and builtins that do not interpret it leave
`$unop_ (EXTEND n)` (typed at every `n`) stuck where V2 steps. -/
def Task.wholeStepValidS : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
      (∀ c c' : Config H,
        Typed20 (simEnv20S (Sim.Floats.floatIntB (Profile.spec nd r))) hn c → CvtOkL c.code →
        Step (Profile.spec nd r) host c c' →
        ∃ c'', Step (Profile.spec nd r) host c c'' ∧
          ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
          Sim.Round6.Reading.SStepB (simEnv20S (Sim.Floats.floatIntB (Profile.spec nd r)))
            (configV hn c) (configV hn c'')) ∧
      (∀ (c : Config H) (w : Value),
        Typed20 (simEnv20S (Sim.Floats.floatIntB (Profile.spec nd r))) hn c → CvtOkL c.code →
        Sim.Round6.Reading.SStepB (simEnv20S (Sim.Floats.floatIntB (Profile.spec nd r)))
          (configV hn c) w →
        ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim20.StepFix
