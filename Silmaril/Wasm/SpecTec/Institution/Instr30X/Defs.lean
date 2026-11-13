module

public import Silmaril.Wasm.SpecTec.Institution.Instr30.Defs

/-!
# Instruction typing of the wasm-3.0 script, extended: definitions

`Instr30` relates `Instr_ok`/`Instrs_ok` in `stepModel BI` to Core 3.0 validation at `nop`,
`unreachable` and `drop`, and froze `Task.emptyModuleOk`. This topic extends it.

* `fragX i`: the instructions reached, `Instr30.frag` (`nop`, `unreachable`, `drop`) and the
  integer numeric instructions (`const`, `unop`, `binop`, `testop`, `relop`).
* `FragOkX is it`: `Instr30.FragOk` over `fragX`: bounded Core derivations of `{} ⊢ is : it` by
  `Instrs_ok/empty`, `instr`, `seq` (without locals) and `frame`.
* `DomX`: the domain of the satisfaction condition over `fragX`: reached instructions at
  bounded types, and `FragOkX` derivations.
* `ModuleOkEmpty B`: `stepModel B` has no `Module_ok` fact at all. It holds at the concrete
  primitives (`Instr30X.stepModel_not_moduleOk`), which refutes `Instr30.Task.emptyModuleOk`
  (`Instr30X.not_emptyModuleOk`): `$clos_moduletype` never has a value there.
* The restatement: `withClosMod B` answers `$clos_moduletype(C, mt)` with `mt` (the closure at a
  context without defined types, such as `{}`); `FuncidxEmpty B`: `$funcidx_nonfuncs` gives `[]`
  on five empty lists. `Instr30X.moduleOk_withClosMod` shows that `stepModel (withClosMod B)`
  validates the empty module at `[] -> []` whenever `FuncidxEmpty (withClosMod B)`.
  `Task.funcidxEmpty` (that `FuncidxEmpty` holds in every evaluator) was frozen while its
  evaluation was too slow for the kernel in one piece, and is now proved
  (`Instr30X.funcidxEmpty`), so `Instr30X.emptyModuleOk_repaired` is unconditional.

The results are in `Instr30X.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Instr30 (ISen ItBnd frag)

/-- The integer numeric instructions. -/
def intNum : Instr → Bool
  | .intConst .. | .intUnOp .. | .intBinOp .. | .intTestOp .. | .intRelOp .. => true
  | _ => false

/-- The instructions this comorphism reaches: `Instr30`'s and the integer numeric ones. -/
def fragX (i : Instr) : Bool := frag i || intNum i

/-- **Bounded Core derivations over `fragX`**, in `{}` (`Instr30.FragOk` over `fragX`). -/
inductive FragOkX : List Instr → InstrType → Prop where
  /-- `Instrs_ok/empty`. -/
  | nil : FragOkX [] (.plain [] [])
  /-- `Instrs_ok/instr`. -/
  | instr {i : Instr} {ps rs : List CValType} (hf : fragX i = true) (hb : ItBnd (.plain ps rs))
      (h : InstrOk {} i (.plain ps rs)) : FragOkX [i] (.plain ps rs)
  /-- `Instrs_ok/seq`, without locals, at a bounded intermediate stack. -/
  | seq {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
      (hb : ∀ t ∈ t₂, Round4.tyBnd t = true) (h₁ : FragOkX is₁ (.plain t₁ t₂))
      (h₂ : FragOkX is₂ (.plain t₂ t₃)) : FragOkX (is₁ ++ is₂) (.plain t₁ t₃)
  /-- `Instrs_ok/frame`, at a bounded, valid frame. -/
  | frame {is : List Instr} {ts t₁ t₂ : List CValType} (hb : ∀ t ∈ ts, Round4.tyBnd t = true)
      (hok : ResultOk {} ts) (h : FragOkX is (.plain t₁ t₂)) :
      FragOkX is (.plain (ts ++ t₁) (ts ++ t₂))

/-- **The domain over `fragX`.** -/
def DomX : ISen → Prop
  | .instr i it => fragX i = true ∧ ItBnd it
  | .instrs is it => FragOkX is it

/-- The empty module type, `[] -> []`. -/
def mtNil : Value := .case "%->%" (.tuple [.list [], .list []])

/-- `B`, answering `$clos_moduletype(C, mt)` with `mt`: the closure of a module type at a context
whose `TYPES` are empty, such as `{}`. -/
def withClosMod (B : Builtins) : Builtins :=
  ⟨fun x ws => match x, ws with
    | "clos_moduletype", [_, .val m] => some m
    | x, ws => B.call x ws⟩

/-- `$funcidx_nonfuncs` gives `[]` on five empty lists. -/
def FuncidxEmpty (B : Builtins) : Prop :=
  Silmaril.SpecTec.Equiv.ExecNumeric.Applies (simEnv B) "funcidx_nonfuncs"
    [.val (.case "%%%%%" (.tuple [.list [], .list [], .list [], .list [], .list []]))] (.list [])

/-- `$funcidx_nonfuncs` gives `[]` on five empty lists in every evaluator `simEnv B` (proved:
`Instr30X.funcidxEmpty`). Its first clause applies, through `$funcidx_module(MODULE …)`, then
`$free_module`, ten compositions of `$free_list([])` and `$free_opt(eps)`, and the `FUNCS` field of
the result; no step consults `B`. -/
def Task.funcidxEmpty : Prop := ∀ B : Builtins, FuncidxEmpty B

/-- `stepModel B` has no `Module_ok` fact, at any argument and value. -/
def ModuleOkEmpty (B : Builtins) : Prop :=
  ∀ args v, ¬ (Wasm30.stepModel B).D "Module_ok" "|-%:%" args v

end Silmaril.Wasm.SpecTec.Institution.Instr30X
