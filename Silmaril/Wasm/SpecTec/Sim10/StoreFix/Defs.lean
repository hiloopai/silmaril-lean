module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs
public import Silmaril.Wasm.SpecTec.Sim10.Encode.Defs

/-!
# The `STORE` erratum for wasm-1.0, as a documented restatement

The `STORE` case of wasm-1.0's `instr` (`Scripts.Wasm10.Original.d67`) and `admininstr`
(`Original.d170`) reads

  `STORE valtype sz? memarg -- (if valtype = Inn /\ sz < $size(Inn))?`

and, as in 2.0 (`Sim20.StoreFix`), the frontend elaborates the premise as an option iteration over
**both** `Inn?` and `sz?`, with `Inn?` a case quantifier that nothing binds. So no value is a 1.0
`STORE` (`Sim10.Whole.not_typedV_store10`), and the forward 1.0 half matches stores only
vacuously.

**The erratum** (`storeCaseFix10`) keeps the payload and replaces the quantifier and the premise
by what the prose means, `Inn` being `I32` or `I64`:

  `(if (valtype = I32 \/ valtype = I64) /\ sz.0 < $size(valtype))?{sz <- sz?}`

It is two `IL.Erratum`s (`storeInstrErratum10` on `instr`, `storeAdminErratum10` on
`admininstr`). `fixedT10` applies both to `Scripts.Wasm10.fixed`, and `simEnv10T B` is its
environment with primitives `B`. Like 2.0's, it is a Lean-level erratum, not a `spectec_erratum`
command (which would regenerate the widely imported `Raw` module `Scripts/Wasm10/Fixed`);
`issue := 0` marks that no upstream issue is filed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- `valtype = C`, for a nullary constructor `C` of `valtype`. -/
def valtypeIs (c : String) : Exp :=
  .cmpE .eqOp .boolT (.varE "valtype") (.caseE c (.tupE []))

/-- The corrected premise:
`(if (valtype = I32 \/ valtype = I64) /\ sz.0 < $size(valtype))?{sz <- sz?}`. -/
def storePremFix10 : Prem :=
  .iterPr (.ifPr (.binE .andOp .boolT (.binE .orOp .boolT (valtypeIs "I32") (valtypeIs "I64"))
      (.cmpE .ltOp (.numT .natT) (.projE (.uncaseE (.varE "sz") "%") 0)
        (.callE "size" [.expA (.varE "valtype")]))))
    (.mk .opt [.mk "sz" (.varE "sz?")])

/-- **The corrected `STORE` case**: the original payload, no quantifier, `storePremFix10`. -/
def storeCaseFix10 : TypCase :=
  .mk "STORE" (.tupT [.mk "valtype" (.varT "valtype" []), .mk "sz?" (.iterT (.varT "sz" []) .opt),
    .mk "memarg" (.varT "memarg" [])]) [] [storePremFix10]

/-- Replace the `STORE` case. -/
def fixCase10 : TypCase → TypCase
  | .mk "STORE" _ _ _ => storeCaseFix10
  | c => c

/-- Replace the `STORE` case of a one-instance variant type. -/
def fixStoreTyp10 : Def → Def
  | .typD x ps [.instD bs xs (.variantT cs)] =>
      .typD x ps [.instD bs xs (.variantT (cs.map fixCase10))]
  | d => d

/-- The corrected `instr`. -/
noncomputable def instrFix10 : Def :=
  fixStoreTyp10 (Sim20.StoreFix.recHead Silmaril.Wasm.SpecTec.Scripts.Wasm10.Original.d67)

/-- The corrected `admininstr`. -/
noncomputable def adminFix10 : Def :=
  fixStoreTyp10 (Sim20.StoreFix.recHead Silmaril.Wasm.SpecTec.Scripts.Wasm10.Original.d170)

/-- **The erratum on `instr`.** -/
noncomputable def storeInstrErratum10 : Erratum where
  issue := 0
  summary := "STORE (wasm-1.0 instr): the premise iterates over the unbound Inn?; \
    restate it over sz? alone, with Inn read as I32 or I64"
  target := "instr"
  corrected := instrFix10

/-- **The erratum on `admininstr`.** -/
noncomputable def storeAdminErratum10 : Erratum where
  issue := 0
  summary := "STORE (wasm-1.0 admininstr): the premise iterates over the unbound Inn?; \
    restate it over sz? alone, with Inn read as I32 or I64"
  target := "admininstr"
  corrected := adminFix10

/-- The wasm-1.0 script with the errata of `Errata/Wasm10.lean` and both `STORE` errata. -/
noncomputable def fixedT10 : Script :=
  replaceDefs adminFix10 (replaceDefs instrFix10 Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed)

/-- The lookup environment of `fixedT10`, with the primitives `B`. -/
noncomputable def simEnv10T (B : Builtins) : Env := (envOfScript fixedT10).withBuiltins B

end Silmaril.Wasm.SpecTec.Sim10.StoreFix
