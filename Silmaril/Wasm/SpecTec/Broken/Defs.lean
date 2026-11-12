module

public import Silmaril.Wasm.SpecTec.Scripts.Defs
public import Silmaril.Wasm.SpecTec.Defs

/-!
# SpecTec defects, as predicates on scripts

Each known defect of the pinned SpecTec specification is a predicate `X : Script → Prop`.
"The original is broken" is `X original`; "the fix repairs it" is `¬ X fixed` (or a positive
fact about `fixed`).  `Silmaril.Wasm.SpecTec.Broken.Thms` states both for the generated scripts of
`Silmaril.Wasm.SpecTec.Scripts`.

Issue numbers are those of the errata files (`Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata/*.lean`),
which are local erratum numbers; nothing here claims an upstream report.

The evaluator (`Sem.callDef`, `Sem.premsHold`) is fuel-indexed.  The failure predicates below are
stated for *every* fuel, so they mean "no amount of evaluation gives a value", not "fuel 100 was
too little".
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Broken

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Evaluation helpers -/

/-- The `byte`/`char` value `(% n)`, as the bridge writes it. -/
def numCaseV (n : Nat) : Value := .case "%" (.tuple [.num (.natN n)])

/-- The expression `(case "%" (tup (num (nat n))))`, which evaluates to `numCaseV n`. -/
def numCaseE (n : Nat) : Exp := .caseE "%" (.tupE [.numE (.natN n)])

/-- A scope binding the given variables to `numCaseV` values. -/
def scopeOf : List (IL.Id × Nat) → VarEnv
  | [] => VarEnv.empty
  | (x, n) :: xs => (scopeOf xs).bindVal x (numCaseV n)

/-- The premises of clause `k` of the function `f` in script `s`. -/
def clausePrems (s : Script) (f : IL.Id) (k : Nat) : Option (List Prem) :=
  match (envOfScript s).findDef? f with
  | some (_, _, cls) =>
      match cls[k]? with
      | some (.defD _ _ _ prems) => some prems
      | none => none
  | none => none

/-- The premises of production `k` of the grammar `g` in script `s`. -/
def prodPrems (s : Script) (g : IL.Id) (k : Nat) : Option (List Prem) :=
  match (envOfScript s).findGram? g with
  | some (_, _, ps) =>
      match ps[k]? with
      | some (.prodD _ _ _ prems) => some prems
      | none => none
  | none => none

/-- The premises `ps` hold at scope `ρ` in `s`: some fuel evaluates them all to true. -/
def PremsHold (s : Script) (ps : Option (List Prem)) (ρ : VarEnv) : Prop :=
  ∃ prems, ps = some prems ∧ ∃ N ρ', premsHold N (envOfScript s) ρ prems = .ok ρ'

/-- The premises `ps` exist and fail at scope `ρ` in `s`: no fuel evaluates them to true. -/
def PremsFail (s : Script) (ps : Option (List Prem)) (ρ : VarEnv) : Prop :=
  ∃ prems, ps = some prems ∧ ∀ N ρ', premsHold N (envOfScript s) ρ prems ≠ .ok ρ'

/-- `$f(args)` has no value in `s`, at any fuel. -/
def CallUndef (s : Script) (f : IL.Id) (args : List Arg) : Prop :=
  ∀ N v, callDef N (envOfScript s) VarEnv.empty f args ≠ .ok v

/-- `$f(args)` evaluates to `v` in `s`, at some fuel. -/
def CallIs (s : Script) (f : IL.Id) (args : List Arg) (v : Value) : Prop :=
  ∃ N, callDef N (envOfScript s) VarEnv.empty f args = .ok v

/-! ## Binary format, wasm-3.0 -/

/-- **#654.**  `Bi32` reads its bytes as *unsigned* LEB128: it is exactly the hand-written `U32`. -/
def Bi32Unsigned (s : Script) : Prop :=
  ∀ ρ bs v, gramRelSup (envOfScript s) ρ (.varG "Bi32" []) bs v ↔
    ∃ m, Silmaril.Wasm.Binary.U32 bs m ∧ v = Equiv.uNV m

/-- **#655.**  `$cont(0x80)` has no value: the continuation byte `0x80` is excluded. -/
def ContUndefAt80 (s : Script) : Prop := CallUndef s "cont" [.expA (numCaseE 0x80)]

/-- The scope of the four-byte `$utf8` clause at U+1F601 and its UTF-8 spelling `F0 9F 98 81`. -/
def grinScope : VarEnv :=
  scopeOf [("b_4", 0x81), ("b_3", 0x98), ("b_2", 0x9F), ("b_1", 0xF0), ("ch", 0x1F601)]

/-- **#656.**  The four-byte clause of the wasm-3.0 `$utf8` (clause 4; clause 0 is the list
case) rejects U+1F601 with its own encoding `F0 9F 98 81`. -/
def Utf8RejectsGrin (s : Script) : Prop := PremsFail s (clausePrems s "utf8" 4) grinScope

/-- **#803.**  The signed LEB128 grammar `BsN(32)` derives nothing from `FF 7E`, the encoding of
`-129`. -/
def BsNLosesFF7E (s : Script) : Prop :=
  ∀ ρ v, ¬ gramRelSup (envOfScript s) ρ (.varG "BsN" [.expA (.numE (.natN 32))]) [0xFF, 0x7E] v

/-! ## Text format, wasm-3.0 -/

/-- The scope of the `\u{n}` production of `Tstringchar` at `n = 0xE000`.  `n` is a `nat`. -/
def escapeE000Scope : VarEnv := VarEnv.empty.bindVal "n" (.num (.natN 0xE000))

/-- **#661.**  The side condition of the `\u{n}` production of `Tstringchar` (production 7)
fails at `n = 0xE000`, a valid scalar value. -/
def EscapeRejectsE000 (s : Script) : Prop :=
  PremsFail s (prodPrems s "Tstringchar" 7) escapeE000Scope

/-! ## Rules that never fire

A rule is *dead* in `s` when it is the `k`-th rule of relation `rel` in `s` and fires at no
value.  These are mismatches between the IL and its evaluation (`eval.ml` reads an `if` premise
as a side condition, so a variable it is meant to solve for stays unbound), not errata that the
fixed scripts address. -/

/-- Rule `r` is rule `k` of `rel` in `s`, and fires at nothing. -/
def RuleDead (s : Script) (rel : IL.Id) (k : Nat) (r : Rule) : Prop :=
  Equiv.Validation.HasRuleAt (envOfScript s) rel "%~>%" k r ∧
    ∀ v, ¬ Equiv.Validation.RuleFires (envOfScript s) "%~>%" [] [] v r

/-- `Step/table.grow-succeed` (rule 15 of `Step`) never fires. -/
def TableGrowNeverFires (s : Script) : Prop :=
  RuleDead s "Step" 15 Equiv.ExecStepRules.tableGrowSucceedRule

/-! ## Binary format, wasm-1.0 -/

/-- The wasm-1.0 four-byte `$utf8` clause (clause 3) at U+1F601 and `F0 9F 98 81`. -/
def Utf8RejectsGrin10 (s : Script) : Prop := PremsFail s (clausePrems s "utf8" 3) grinScope

/-- The scope of the two-byte `$utf8` clause at U+00C0 with the overlong-free but invalid
spelling `C2 C0` (`C0` is not a continuation byte). -/
def c2c0Scope : VarEnv := scopeOf [("b_2", 0xC0), ("b_1", 0xC2), ("ch", 0xC0)]

/-- **#685.**  The two-byte clause of the wasm-1.0 `$utf8` (clause 1) accepts `C2 C0` for
U+00C0, so `$utf8` is not a function (U+00C0 is also `C3 80`). -/
def Utf8AcceptsC2C0 (s : Script) : Prop := PremsHold s (clausePrems s "utf8" 1) c2c0Scope

/-! ## Binary format, wasm-2.0 -/

/-- **#673.**  `$dataidx_instrs` of `(block (memory.init 0))` is empty: the fold does not
descend into block bodies, so a nested `memory.init` is missed. -/
def DataidxMissesNested (s : Script) : Prop :=
  CallIs s "dataidx_instrs" [.expA IL.Wasm20.nestedMemoryInit] (.list [])

end Silmaril.Wasm.SpecTec.Broken
