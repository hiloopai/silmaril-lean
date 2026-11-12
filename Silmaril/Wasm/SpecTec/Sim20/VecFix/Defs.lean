module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs

/-!
# The vector errata for wasm-2.0, as a documented restatement

Two defects of the pinned wasm-2.0 script make vector instructions untyped (round 3's executable
check `Sim20.EncodeCheck.knownRejectedInstrs`; round 6's `Sim20.VecRefute`).

**1. The operator families select the integer instance at float shapes.** `vunop_`, `vbinop_`
and `vrelop_` (`Scripts.Wasm20.Original.d119`, `d120`, `d122`) each have two instances,

  `syntax vunop_(Jnn X M) = ABS | NEG | POPCNT -- if Jnn = I8`
  `syntax vunop_(Fnn X M) = ABS | NEG | SQRT | CEIL | FLOOR | TRUNC | NEAREST`

whose argument patterns are `(Jnn <: lanetype) X M` and `(Fnn <: lanetype) X M`. Instance
selection (`Sem.hasTypInsts`, after `reduce_typ_app`) tries the instances in order, and matching a
subtyping pattern nested inside a constructor does not check the subtype (`Sem.matchExp` at
`subE`; only a whole argument is checked, by `matchArg`), so `Jnn` also binds `F32` and `F64`. The float instance is never selected, and the float-only operators are untyped
(`VecRefute.not_typedA_floatOnly20`).

**The erratum** (`fixFamily`) prepends two instances, one per float lane type, each with the
float instance's cases and the constant pattern `F32 X M` (resp. `F64 X M`):

  `syntax vunop_(F32 X M) = ABS | NEG | SQRT | …`, `syntax vunop_(F64 X M) = …`, then the original two.

The float instance's cases have no premise and do not mention `Fnn`, so binding only `M` is
enough. At an integer shape neither new pattern matches, and selection proceeds as before.

**2. `VEXTRACT_LANE` quantifies a variable nothing binds.** Its case (in `instr`, `d133`, and
`admininstr`, `d295`) reads

  `VEXTRACT_LANE shape sx? laneidx -- if $lanetype(shape) = numtype <=> sx? = eps`

with `numtype` a case quantifier. `Sem.hasTypCase` solves quantifiers only from defining
equations (`bindQuants`), and this premise is not one, so no value is a `VEXTRACT_LANE`. The
intended reading (the W3C 2.0 text, and V2's `immediatesValid`: `sx?` is present exactly at the
packed lane types) is restated without the quantifier as

  `VEXTRACT_LANE shape sx? laneidx -- if ($lanetype(shape) = I8 \/ $lanetype(shape) = I16) <=> sx? =/= eps`

(`extractCaseFix`). The lane types are compared with the two packed constants, so the premise
calls only `$lanetype`.

`fixedV20` applies both on top of `StoreFix.fixedT20` (the `Step` and `STORE` errata): the two
`STORE`-corrected types get the `VEXTRACT_LANE` correction too, and the three families are
replaced. `simEnv20V B` is its environment with primitives `B`.

Like `StoreFix`, these are Lean-level errata, not `spectec_erratum` commands of
`Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata/Wasm20.lean`: such a command would make
`tools/spectec-gen` regenerate `Scripts/Wasm20/Fixed`, a `Raw` module that most of the tree
imports. `issue := 0` marks that no upstream issue is filed.

**Not changed.** The function definitions `$vunop_`, `$vbinop_` and `$vrelop_` have the same
pattern shape (their `Jnn` clauses come first and also match float shapes). Their clauses are
selected by premises as well as patterns, and a `Jnn` clause at a float shape fails in its
premises unless the primitives answer integer operators at float lanes; this restatement leaves
them as they are, and nothing here depends on them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## 1. The operator families -/

/-- The instance `C X M` with the cases `cs`, for a float lane type `C`. -/
def floatInst (c : String) (cs : List TypCase) : Inst :=
  .instD [.expP "M" (.varT "M" [])]
    [.expA (.caseE "%X%" (.tupE [.caseE c (.tupE []), .varE "M"]))] (.variantT cs)

/-- **Prepend the two float instances** to a two-instance family whose second instance is the
float one. -/
def fixFamily : Def → Def
  | .typD x ps [ji, .instD bs pats (.variantT fcs)] =>
      .typD x ps [floatInst "F32" fcs, floatInst "F64" fcs, ji, .instD bs pats (.variantT fcs)]
  | d => d

/-- The corrected `vunop_`. -/
noncomputable def vunopFix20 : Def := fixFamily Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d119

/-- The corrected `vbinop_`. -/
noncomputable def vbinopFix20 : Def := fixFamily Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d120

/-- The corrected `vrelop_`. -/
noncomputable def vrelopFix20 : Def := fixFamily Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d122

/-! ## 2. `VEXTRACT_LANE` -/

/-- `$lanetype(shape) = C`, for a nullary lane type `C`. -/
def laneIs (c : String) : Exp :=
  .cmpE .eqOp .boolT (.callE "lanetype" [.expA (.varE "shape")]) (.caseE c (.tupE []))

/-- `sx?`, as the original premise iterates it. -/
def sxOpt : Exp := .iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")])

/-- **The corrected premise**:
`($lanetype(shape) = I8 \/ $lanetype(shape) = I16) <=> sx? =/= eps`. -/
def extractPremFix : Prem :=
  .ifPr (.binE .equivOp .boolT (.binE .orOp .boolT (laneIs "I8") (laneIs "I16"))
    (.cmpE .neOp .boolT sxOpt (.optE none)))

/-- The payload of `VEXTRACT_LANE`, unchanged. -/
def extractPayT : Typ :=
  .tupT [.mk "shape" (.varT "shape" []), .mk "sx?" (.iterT (.varT "sx" []) .opt),
    .mk "laneidx" (.varT "laneidx" [])]

/-- **The corrected `VEXTRACT_LANE` case**: the original payload, no quantifier,
`extractPremFix`. -/
def extractCaseFix : TypCase := .mk "VEXTRACT_LANE" extractPayT [] [extractPremFix]

/-- Replace the `VEXTRACT_LANE` case. -/
def fixExtractCase : TypCase → TypCase
  | .mk "VEXTRACT_LANE" _ _ _ => extractCaseFix
  | c => c

/-- Replace the `VEXTRACT_LANE` case of a one-instance variant type. -/
def fixExtractTyp : Def → Def
  | .typD x ps [.instD bs xs (.variantT cs)] =>
      .typD x ps [.instD bs xs (.variantT (cs.map fixExtractCase))]
  | d => d

/-- The corrected `instr`: `STORE` and `VEXTRACT_LANE`. -/
noncomputable def instrFixV20 : Def := fixExtractTyp StoreFix.instrFix20

/-- The corrected `admininstr`: `STORE` and `VEXTRACT_LANE`. -/
noncomputable def adminFixV20 : Def := fixExtractTyp StoreFix.adminFix20

/-! ## The errata -/

/-- **The erratum on `vunop_`.** -/
noncomputable def vunopErratum20 : Erratum where
  issue := 0
  summary := "vunop_ (wasm-2.0): the Jnn instance also matches float shapes; \
    prepend the float instance at F32 X M and F64 X M"
  target := "vunop_"
  corrected := vunopFix20

/-- **The erratum on `vbinop_`.** -/
noncomputable def vbinopErratum20 : Erratum where
  issue := 0
  summary := "vbinop_ (wasm-2.0): the Jnn instance also matches float shapes; \
    prepend the float instance at F32 X M and F64 X M"
  target := "vbinop_"
  corrected := vbinopFix20

/-- **The erratum on `vrelop_`.** -/
noncomputable def vrelopErratum20 : Erratum where
  issue := 0
  summary := "vrelop_ (wasm-2.0): the Jnn instance also matches float shapes; \
    prepend the float instance at F32 X M and F64 X M"
  target := "vrelop_"
  corrected := vrelopFix20

/-- **The erratum on `instr`** (on top of the `STORE` erratum). -/
noncomputable def extractInstrErratum20 : Erratum where
  issue := 0
  summary := "VEXTRACT_LANE (wasm-2.0 instr): the premise quantifies the unbound numtype; \
    restate it as: sx? is present exactly at I8 and I16 lanes"
  target := "instr"
  corrected := instrFixV20

/-- **The erratum on `admininstr`** (on top of the `STORE` erratum). -/
noncomputable def extractAdminErratum20 : Erratum where
  issue := 0
  summary := "VEXTRACT_LANE (wasm-2.0 admininstr): the premise quantifies the unbound numtype; \
    restate it as: sx? is present exactly at I8 and I16 lanes"
  target := "admininstr"
  corrected := adminFixV20

/-- The wasm-2.0 script with the errata of `Errata/Wasm20.lean`, the `Step` and `STORE` errata,
and the five vector errata applied. -/
noncomputable def fixedV20 : Script :=
  replaceDefs vrelopFix20 (replaceDefs vbinopFix20 (replaceDefs vunopFix20
    (replaceDefs adminFixV20 (replaceDefs instrFixV20 StoreFix.fixedT20))))

/-- The lookup environment of `fixedV20`, with the primitives `B`. -/
noncomputable def simEnv20V (B : Builtins) : Env := (envOfScript fixedV20).withBuiltins B

end Silmaril.Wasm.SpecTec.Sim20.VecFix
