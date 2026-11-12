module

public import Silmaril.Wasm.SpecTec.Sim20.StepFix.Defs

/-!
# The `STORE` erratum for wasm-2.0, as a documented restatement

The `STORE` case of wasm-2.0's `instr` (`Scripts.Wasm20.Original.d133`) and `admininstr`
(`Original.d295`) reads

  `STORE numtype sz? memarg -- (if numtype = Inn /\ sz < $sizenn(Inn))?`

and the frontend elaborates the premise as an option iteration over **both** `Inn?` and `sz?`
(`(if numtype = Inn /\ sz.0 < $sizenn(Inn))?{Inn <- Inn?, sz <- sz?}`), with `Inn?` a case
quantifier that nothing binds. Its domain never evaluates, so no value is a `STORE`
(`Sim20.Whole.not_typedV_store20`), no state whose store has a storing function is typed, and the
corrected script `simEnv20S` has no step at all from such a state
(`StoreFix.stuck_storeFn20S`, `StoreFixNeed`). wasm-3.0 avoids the problem by typing the pack size as
`storeop_(numtype)?`, a family indexed by the number type.

**The erratum** (`storeCaseFix`) keeps the case's payload and replaces the quantifier and the
premise by what the 2.0 prose means, `Inn` being `I32` or `I64`:

  `(if (numtype = I32 \/ numtype = I64) /\ sz.0 < $sizenn(numtype))?{sz <- sz?}`

so the premise iterates over `sz?` alone and refers only to the payload. A store without a pack
size is unconstrained, as before; a packed store needs an integer type and a pack size below its
width.

It is two `IL.Erratum`s, one per type (`storeInstrErratum20` on `instr`,
`storeAdminErratum20` on `admininstr`), each the original definition with the `STORE` case
replaced (`fixStoreTyp`). `fixedT20` applies both on top of `StepFix.fixedS20` (the `Step`
erratum), and `simEnv20T B` is its environment with primitives `B`.

It is **not** a `spectec_erratum` command of `Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata/Wasm20.lean`:
such a command would make `tools/spectec-gen` regenerate `Scripts/Wasm20/Fixed`, a `Raw` module
that most of the tree imports. Like `StepFix.stepErratum20`, it is a Lean-level erratum on top
of `Scripts.Wasm20.fixed`; `issue := 0` marks that no upstream issue is filed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## The corrected case -/

/-- `numtype = C`, for a nullary constructor `C` of `numtype`. -/
def numtypeIs (c : String) : Exp :=
  .cmpE .eqOp .boolT (.varE "numtype") (.caseE c (.tupE []))

/-- The corrected premise:
`(if (numtype = I32 \/ numtype = I64) /\ sz.0 < $sizenn(numtype))?{sz <- sz?}`. -/
def storePremFix : Prem :=
  .iterPr (.ifPr (.binE .andOp .boolT (.binE .orOp .boolT (numtypeIs "I32") (numtypeIs "I64"))
      (.cmpE .ltOp (.numT .natT) (.projE (.uncaseE (.varE "sz") "%") 0)
        (.callE "sizenn" [.expA (.varE "numtype")]))))
    (.mk .opt [.mk "sz" (.varE "sz?")])

/-- **The corrected `STORE` case**: the original payload, no quantifier, `storePremFix`. -/
def storeCaseFix : TypCase :=
  .mk "STORE" (.tupT [.mk "numtype" (.varT "numtype" []), .mk "sz?" (.iterT (.varT "sz" []) .opt),
    .mk "memarg" (.varT "memarg" [])]) [] [storePremFix]

/-- Replace the `STORE` case. -/
def fixCase : TypCase → TypCase
  | .mk "STORE" _ _ _ => storeCaseFix
  | c => c

/-- Replace the `STORE` case of a one-instance variant type. -/
def fixStoreTyp : Def → Def
  | .typD x ps [.instD bs xs (.variantT cs)] => .typD x ps [.instD bs xs (.variantT (cs.map fixCase))]
  | d => d

/-- The first member of a recursion group. -/
def recHead : Def → Def
  | .recD (d :: _) => d
  | d => d

/-! ## The errata -/

/-- The corrected `instr`. -/
noncomputable def instrFix20 : Def := fixStoreTyp (recHead Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d133)

/-- The corrected `admininstr`. -/
noncomputable def adminFix20 : Def :=
  fixStoreTyp (recHead Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d295)

/-- **The erratum on `instr`.** -/
noncomputable def storeInstrErratum20 : Erratum where
  issue := 0
  summary := "STORE (wasm-2.0 instr): the premise iterates over the unbound Inn?; \
    restate it over sz? alone, with Inn read as I32 or I64"
  target := "instr"
  corrected := instrFix20

/-- **The erratum on `admininstr`.** -/
noncomputable def storeAdminErratum20 : Erratum where
  issue := 0
  summary := "STORE (wasm-2.0 admininstr): the premise iterates over the unbound Inn?; \
    restate it over sz? alone, with Inn read as I32 or I64"
  target := "admininstr"
  corrected := adminFix20

/-- The wasm-2.0 script with the errata of `Errata/Wasm20.lean`, `stepErratum20` and both
`STORE` errata applied. -/
noncomputable def fixedT20 : Script :=
  replaceDefs adminFix20 (replaceDefs instrFix20 StepFix.fixedS20)

/-- The lookup environment of `fixedT20`, with the primitives `B`. -/
noncomputable def simEnv20T (B : Builtins) : Env := (envOfScript fixedT20).withBuiltins B

end Silmaril.Wasm.SpecTec.Sim20.StoreFix
