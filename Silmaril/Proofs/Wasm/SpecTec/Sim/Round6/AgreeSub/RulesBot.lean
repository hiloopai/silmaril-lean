module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeSub.Rules

/-!
# Round 6: the subtyping rules, located in `simEnv B` (continued)

`Heaptype_sub/none`, `nofunc`, `noexn`, `noextern`, `Deftype_sub/super` and
`Reftype_sub/nonnull`, each by a kernel `rfl` (split from `Rules.lean` to keep both modules
fast).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)

variable {B : Builtins}

/-- The rule `Heaptype_sub/none` and its siblings: `C ⊢ bot <: heaptype` when
`C ⊢ heaptype <: top` and `heaptype ≠ BOT`. -/
def botRule (nm : IL.Id) (bot top : MixopS) : Rule :=
  .ruleD nm [ctxP, heapP "heaptype"] "%|-%<:%" (.tupE [.varE "C", atomE bot, .varE "heaptype"])
    [subPrem (.varE "heaptype") (atomE top),
     .ifPr (.cmpE .neOp .boolT (.varE "heaptype") (atomE "BOT"))]

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/none`. -/
theorem ruleAt_none : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 16 (botRule "none" "NONE" "ANY") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/nofunc`. -/
theorem ruleAt_nofunc :
    HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 17 (botRule "nofunc" "NOFUNC" "FUNC") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/noexn`. -/
theorem ruleAt_noexn :
    HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 18 (botRule "noexn" "NOEXN" "EXN") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/noextern`. -/
theorem ruleAt_noextern :
    HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 19 (botRule "noextern" "NOEXTERN" "EXTERN") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `typeuse*` as an iteration. -/
def typeusesE : Exp := .iterE (.varE "typeuse") (.mk .list [.mk "typeuse" (.varE "typeuse*")])

/-- `SUB final? typeuse* ct`, as `Deftype_sub/super` writes it. -/
def superSubE : Exp :=
  .caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]), typeusesE,
    .varE "ct"])

set_option maxRecDepth 100000 in
/-- `Deftype_sub/super`. -/
theorem ruleAt_super : HasRuleAt (simEnv B) "Deftype_sub" "%|-%<:%" 1
    (.ruleD "super" [ctxP, defP "deftype_1", defP "deftype_2",
        .expP "final?" (.iterT (.varT "final" []) .opt),
        .expP "typeuse*" (.iterT (.varT "typeuse" []) .list), .expP "ct" (.varT "comptype" []),
        .expP "i" (.numT .natT)] "%|-%<:%"
      (.tupE [.varE "C", .varE "deftype_1", .varE "deftype_2"])
      [.ifPr (.cmpE .eqOp .boolT (.callE "unrolldt" [.expA (.varE "deftype_1")]) superSubE),
       subPrem (.subE (.idxE typeusesE (.varE "i")) (.varT "typeuse" []) (.varT "heaptype" []))
         (defHeapE "deftype_2")]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Reftype_sub/nonnull`. -/
theorem ruleAt_nonnull : HasRuleAt (simEnv B) "Reftype_sub" "%|-%<:%" 0
    (.ruleD "nonnull" [ctxP, heapP "ht_1", heapP "ht_2"] "%|-%<:%"
      (.tupE [.varE "C", .caseE "REF" (.tupE [.optE none, .varE "ht_1"]),
        .caseE "REF" (.tupE [.optE none, .varE "ht_2"])])
      [subPrem (.varE "ht_1") (.varE "ht_2")]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub
