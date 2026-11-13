module

public import Silmaril.Wasm.SpecTec.Institution.Typing30.Defs

/-!
# Instruction typing of the wasm-3.0 script against Core 3.0 validation: definitions

`Typing30` relates the script's type judgements (`Reftype_ok`, `Reftype_sub`, `Ref_ok`) to Core.
This header does the same for **instruction typing**: `Instr_ok` and `Instrs_ok`, read in the
backend canonical model `stepModel BI`, against Silmaril's Core 3.0 `InstrOk` and `InstrsOk`.

* `ISen`: a Core instruction-typing judgement in the empty context `{}`. `instr i it` is
  `{} ⊢ i : it`, `instrs is it` is `{} ⊢ is : it`.
* `ISen.Holds`: Core's reading (`InstrOk {}`, `InstrsOk {}`).
* `ISen.toSen`: the sentence translation, a fact sentence of `Instr_ok` or `Instrs_ok` at the
  images `instrToV` (the encoding of the step simulation) and `instrtypeV`, in the context value
  `{}` (`ctxEmptyV`).
* `frag i`: the instructions reached, `nop`, `unreachable` and `drop`.
* `FragOk is it`: a Core derivation of `{} ⊢ is : it` over reached instructions, built from
  `Instrs_ok/empty`, `instr`, `seq` and `frame` (no `sub`), without initialised locals, and with
  every value type bounded, including the intermediate stack of each `seq`.
* `ISen.Dom`: the domain of the satisfaction condition: reached instructions, and instruction
  types whose value types are bounded (`Round4.tyBnd`, so that their images are typed values).
  For `instrs`, a `FragOk` derivation.

**Modules.** No encoding of Core modules into SpecTec values exists yet, so `Module_ok` is
related to Core at the empty module only: `emptyModuleV` is its image (`MODULE` with eleven empty
components), `moduleSen mt` the `Module_ok` fact at it, and `Task.emptyModuleOk` the open target
that `stepModel BI` validates it. Core validates the empty module at `[] -> []`
(`emptyModule_ok`).

The results are in `Instr30.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Equiv.Validation (instrtypeV)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.SpecTec.Sim

/-- **A Core instruction-typing judgement in the empty context.** -/
inductive ISen where
  /-- `{} ⊢ i : it`. -/
  | instr (i : Instr) (it : InstrType)
  /-- `{} ⊢ is : it`. -/
  | instrs (is : List Instr) (it : InstrType)

/-- The instructions this comorphism reaches. -/
def frag : Instr → Bool
  | .nop | .unreachable | .drop => true
  | _ => false

/-- The value types of an instruction type are bounded. -/
def ItBnd (it : InstrType) : Prop :=
  (∀ t ∈ it.params, Round4.tyBnd t = true) ∧ ∀ t ∈ it.results, Round4.tyBnd t = true

/-- **Bounded Core derivations over the reached instructions**, in `{}`. -/
inductive FragOk : List Instr → InstrType → Prop where
  /-- `Instrs_ok/empty`. -/
  | nil : FragOk [] (.plain [] [])
  /-- `Instrs_ok/instr`. -/
  | instr {i : Instr} {ps rs : List CValType} (hf : frag i = true) (hb : ItBnd (.plain ps rs))
      (h : InstrOk {} i (.plain ps rs)) : FragOk [i] (.plain ps rs)
  /-- `Instrs_ok/seq`, without locals, at a bounded intermediate stack. -/
  | seq {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
      (hb : ∀ t ∈ t₂, Round4.tyBnd t = true) (h₁ : FragOk is₁ (.plain t₁ t₂))
      (h₂ : FragOk is₂ (.plain t₂ t₃)) : FragOk (is₁ ++ is₂) (.plain t₁ t₃)
  /-- `Instrs_ok/frame`, at a bounded, valid frame. -/
  | frame {is : List Instr} {ts t₁ t₂ : List CValType} (hb : ∀ t ∈ ts, Round4.tyBnd t = true)
      (hok : ResultOk {} ts) (h : FragOk is (.plain t₁ t₂)) :
      FragOk is (.plain (ts ++ t₁) (ts ++ t₂))

namespace ISen

/-- **Core's reading** of an instruction-typing judgement. -/
def Holds : ISen → Prop
  | instr i it => InstrOk {} i it
  | instrs is it => InstrsOk {} is it

/-- **The sentence translation**: a judgement as a fact of `Instr_ok` or `Instrs_ok`. -/
def toSen : ISen → SSen
  | instr i it =>
    .fact "Instr_ok" "%|-%:%" [] (.tuple [Round6.RefOkV.ctxEmptyV, instrToV i, instrtypeV it])
  | instrs is it =>
    .fact "Instrs_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .list (instrsToV is), instrtypeV it])

/-- **The domain** of the satisfaction condition. -/
def Dom : ISen → Prop
  | instr i it => frag i = true ∧ ItBnd it
  | instrs is it => FragOk is it

end ISen

/-! ## The empty module -/

/-- `%([])`. -/
def pctNil : Value := .case "%" (.tuple [.list []])

/-- **The image of the empty module**: `MODULE` with nine empty lists, no start function and no
exports, in the shape of `Module_ok`'s conclusion. -/
def emptyModuleV : Value :=
  .case "MODULE" (.tuple [pctNil, pctNil, pctNil, pctNil, pctNil, pctNil, pctNil, pctNil, pctNil,
    .opt none, pctNil])

/-- The `Module_ok` fact at the empty module and the module type `mt`. -/
def moduleSen (mt : Value) : SSen := .fact "Module_ok" "|-%:%" [] (.tuple [emptyModuleV, mt])

/-- **Open target** (frozen): `stepModel BI` validates the empty module at some module type.
Firing `Module_ok`'s one rule needs the evaluator on `$clos_moduletype`, `$funcidx_nonfuncs`,
`$tagsxt`, `$globalsxt`, `$memsxt`, `$tablesxt`, `$funcsxt` and `$disjoint_` at empty arguments,
and the context equations of the rule, none of which is evaluated in Lean yet. -/
def Task.emptyModuleOk : Prop :=
  ∀ (H : Type) (P : Profile) (hn : H → String) (host : HostSemantics H), ∃ mt : Value,
    (Wasm30.stepModel (Round4Int.BI P hn host)).D "Module_ok" "|-%:%" [] (.tuple [emptyModuleV, mt])

end Silmaril.Wasm.SpecTec.Institution.Instr30
