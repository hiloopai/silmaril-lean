module

public import Silmaril.Wasm.SpecTec.Sim20.Encode.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs
public import Silmaril.Wasm.V2.Execution.Step
public import Silmaril.Wasm.SpecTec.Sim.Floats.Defs

/-!
# The 2.0 whole-step targets

`docs/projects/spectec/README.md` §1.5 item 3 asks for `Sim20.Task.wholeStepValid`, "in the shape of
`Round6.Task.wholeStepValidR`", relating the V2 model (`V2.Execution.Step`) to the wasm-2.0 script
`Scripts.Wasm20.fixed` under the Round 6 backend reading (`Round6.Reading.SStepB` on
`simEnv20 B`). This header states it, and the backward half on its own.

* `Task.wholeStepValid`: on configurations whose image is IL-typed (`Typed20`),
  - **forward, up to V2's choice**: each V2 step `c → c'` is matched by a SpecTec step from the
    image of `c` to the image of a V2 successor `c''`, which is `c'` when `c'` is the only one;
  - **backward**: each SpecTec step from the image of `c` is the image of a V2 step.
  The successor is matched exactly (2.0's encoding has no `CALL_REF` annotation, so no
  `Bwd.ConfigEq` is needed). Requiring `Typed20` is what covers the `STORE`/`VEXTRACT_LANE`
  obstruction (upstream note 1 of track F2): those instructions have no IL type, so a typed image
  contains neither, and the target says nothing about configurations that do.
* `Task.wholeStepBwd`: the backward half alone.

**The forward half is false for the script as written** (`Sim20.Whole.not_wholeStepValid`). The
2.0 script lacks `Step/ctxt-instrs` (V2's documented deviation 1), so `NOP NOP` has no SpecTec
step at all, while V2 reduces it. The backward half is the statement that survives.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

/-- **The 2.0 whole-step target, in Round 6's shape** (frozen). It is refuted by
`Sim20.Whole.not_wholeStepValid`. -/
def Task.wholeStepValid : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
      (∀ c c' : Config H, Typed20 (simEnv20 B) hn c → Step (Profile.spec nd r) host c c' →
        ∃ c'', Step (Profile.spec nd r) host c c'' ∧
          ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
          Sim.Round6.Reading.SStepB (simEnv20 B) (configV hn c) (configV hn c'')) ∧
      (∀ (c : Config H) (w : Value), Typed20 (simEnv20 B) hn c →
        Sim.Round6.Reading.SStepB (simEnv20 B) (configV hn c) w →
        ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c')

/-- **The backward half of the 2.0 whole-step target** (frozen, open): every step of the wasm-2.0
script under the backend reading, from the image of a configuration whose image is typed, is the
image of a V2 step. -/
def Task.wholeStepBwd : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
      ∀ (c : Config H) (w : Value), Typed20 (simEnv20 B) hn c →
        Sim.Round6.Reading.SStepB (simEnv20 B) (configV hn c) w →
        ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c'

/-! ## The structural rules of `Step`, verbatim

Rules 0–3 of `Step` in `Scripts.Wasm20.fixed` (`Scripts.Wasm20.Original.d368`; no erratum touches
them). Their provenance in `simEnv20 B` is a kernel `rfl` (`Sim20.Whole.hasRuleAt_*`). Note that
all four quantify their code as `instr*`, not `admininstr*`. -/

section Rules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

/-- `Step/pure`, rule 0 of `Step` in `Scripts.Wasm20.fixed` (verbatim). -/
def stepPureRule20 : Rule :=
    (Rule.ruleD "pure" [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "instr*"
  (Typ.iterT (Typ.varT "instr" []) Iter.list)), (Param.expP "instr'*" (Typ.iterT (Typ.varT "instr"
  []) Iter.list))] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.iterE (Exp.subE
  (Exp.varE "instr") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr"
  (Exp.varE "instr*"))]))])), (Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.iterE (Exp.subE (Exp.varE "instr'")
  (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr'" (Exp.varE "instr'*"))]))]))])
  [(Prem.rulePr "Step_pure" [] "%~>%" (Exp.tupE [(Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT "instr"
  []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr" (Exp.varE "instr*"))])),
  (Exp.iterE (Exp.subE (Exp.varE "instr'") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list
  [(Dom.mk "instr'" (Exp.varE "instr'*"))]))]))])

/-- `Step/read`, rule 1 of `Step` in `Scripts.Wasm20.fixed` (verbatim). -/
def stepReadRule20 : Rule :=
    (Rule.ruleD "read" [(Param.expP "z" (Typ.varT "state"
  [])), (Param.expP "instr*" (Typ.iterT (Typ.varT "instr" []) Iter.list)), (Param.expP "instr'*"
  (Typ.iterT (Typ.varT "instr" []) Iter.list))] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"),
  (Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list
  [(Dom.mk "instr" (Exp.varE "instr*"))]))])), (Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.iterE
  (Exp.subE (Exp.varE "instr'") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list
  [(Dom.mk "instr'" (Exp.varE "instr'*"))]))]))]) [(Prem.rulePr "Step_read" [] "%~>%" (Exp.tupE [(Exp.caseE "%;%"
  (Exp.tupE [(Exp.varE "z"), (Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT "instr" []) (Typ.varT "admininstr"
  [])) (IterExp.mk Iter.list [(Dom.mk "instr" (Exp.varE "instr*"))]))])), (Exp.iterE (Exp.subE (Exp.varE "instr'")
  (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr'" (Exp.varE "instr'*"))]))]))])

/-- `Step/ctxt-label`, rule 2 of `Step` in `Scripts.Wasm20.fixed` (verbatim). -/
def ctxtLabelRule20 : Rule :=
    (Rule.ruleD "ctxt-label" [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "n" (Typ.varT "n"
  [])), (Param.expP "instr_0*" (Typ.iterT (Typ.varT "instr" []) Iter.list)), (Param.expP "instr*"
  (Typ.iterT (Typ.varT "instr" []) Iter.list)), (Param.expP "z'" (Typ.varT "state" [])), (Param.expP "instr'*"
  (Typ.iterT (Typ.varT "instr" []) Iter.list))] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"),
  (Exp.listE [(Exp.caseE "LABEL_%{%}%" (Exp.tupE [(Exp.varE "n"), (Exp.iterE (Exp.varE "instr_0")
  (IterExp.mk Iter.list [(Dom.mk "instr_0" (Exp.varE "instr_0*"))])), (Exp.iterE (Exp.subE (Exp.varE "instr")
  (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr" (Exp.varE "instr*"))]))]))])])),
  (Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z'"), (Exp.listE [(Exp.caseE "LABEL_%{%}%" (Exp.tupE [(Exp.varE "n"),
  (Exp.iterE (Exp.varE "instr_0") (IterExp.mk Iter.list [(Dom.mk "instr_0" (Exp.varE "instr_0*"))])),
  (Exp.iterE (Exp.subE (Exp.varE "instr'") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list
  [(Dom.mk "instr'" (Exp.varE "instr'*"))]))]))])]))]) [(Prem.rulePr "Step" [] "%~>%" (Exp.tupE [(Exp.caseE "%;%"
  (Exp.tupE [(Exp.varE "z"), (Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT "instr" []) (Typ.varT "admininstr"
  [])) (IterExp.mk Iter.list [(Dom.mk "instr" (Exp.varE "instr*"))]))])), (Exp.caseE "%;%" (Exp.tupE
  [(Exp.varE "z'"), (Exp.iterE (Exp.subE (Exp.varE "instr'") (Typ.varT "instr" []) (Typ.varT "admininstr"
  [])) (IterExp.mk Iter.list [(Dom.mk "instr'" (Exp.varE "instr'*"))]))]))]))])

/-- `Step/ctxt-frame`, rule 3 of `Step` in `Scripts.Wasm20.fixed` (verbatim). -/
def ctxtFrameRule20 : Rule :=
    (Rule.ruleD "ctxt-frame"
  [(Param.expP "s" (Typ.varT "store" [])), (Param.expP "f" (Typ.varT "frame" [])), (Param.expP "n"
  (Typ.varT "n" [])), (Param.expP "f'" (Typ.varT "frame" [])), (Param.expP "instr*" (Typ.iterT (Typ.varT "instr"
  []) Iter.list)), (Param.expP "s'" (Typ.varT "store" [])), (Param.expP "instr'*" (Typ.iterT (Typ.varT "instr"
  []) Iter.list))] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "s"),
  (Exp.varE "f")])), (Exp.listE [(Exp.caseE "FRAME_%{%}%" (Exp.tupE [(Exp.varE "n"), (Exp.varE "f'"),
  (Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list
  [(Dom.mk "instr" (Exp.varE "instr*"))]))]))])])), (Exp.caseE "%;%" (Exp.tupE [(Exp.caseE "%;%"
  (Exp.tupE [(Exp.varE "s'"), (Exp.varE "f")])), (Exp.listE [(Exp.caseE "FRAME_%{%}%" (Exp.tupE [(Exp.varE "n"),
  (Exp.varE "f'"), (Exp.iterE (Exp.subE (Exp.varE "instr'") (Typ.varT "instr" []) (Typ.varT "admininstr"
  [])) (IterExp.mk Iter.list [(Dom.mk "instr'" (Exp.varE "instr'*"))]))]))])]))]) [(Prem.rulePr "Step"
  [] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "s"), (Exp.varE "f'")])),
  (Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list
  [(Dom.mk "instr" (Exp.varE "instr*"))]))])), (Exp.caseE "%;%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE
  [(Exp.varE "s'"), (Exp.varE "f'")])), (Exp.iterE (Exp.subE (Exp.varE "instr'") (Typ.varT "instr"
  []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr'" (Exp.varE "instr'*"))]))]))]))])

end Rules

/-- `instr*`, the type the structural rules of wasm-2.0 `Step` give their code. -/
abbrev instrsT20 : Silmaril.SpecTec.IL.Typ := .iterT (.varT "instr" []) .list

/-- `v` has the IL type `t` in some scope that binds term variables only (what a rule's
quantifiers provide). -/
def TypedSome (env : Env) (t : Silmaril.SpecTec.IL.Typ) (v : Value) : Prop :=
  ∃ ρ : VarEnv, Sim.ValsOnly ρ ∧ HasTyp env ρ t v

/-- **The per-rule obligations of the backward half**, at one encoding, host, profile and
primitives: every firing of a `Step_pure` rule, of a `Step_read` rule, and of a `Step` rule other
than the four structural ones (rules 0–3), at the image of V2 code or a V2 configuration, is the
image of the corresponding V2 step. For `Step_pure` and `Step_read` the obligation may use what
`Step/pure` and `Step/read` supply: both sides are `instr*`. -/
structure BwdParts20 {H : Type} (B : Builtins) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`. -/
  pure : ∀ (i : Nat) (code : List Admin) (w : List Value),
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Sim.Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep P code code'
  /-- `Step_read`. -/
  read : ∀ (i : Nat) (c : Config H) (w : List Value),
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Sim.Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  /-- The `Step` rules from `local.set` on. -/
  step : ∀ (i : Nat), 4 ≤ i → ∀ (c : Config H) (w : Value),
    Sim.Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-! ## The corrected backward target (pass 6)

`Task.wholeStepBwd` lets the primitives `B` be chosen, so builtins that interpret nothing make
every numeric rule inert and the statement weak. At the spec's builtins
(`Sim.Floats.floatIntB P`) the per-rule obligations are false (`Sim20.Whole.not_bwdLive20_floatB`):
the 2.0 script's `$cvtop__` has generic `EXTEND`/`WRAP`/`PROMOTE`/`DEMOTE` clauses, so a typed
`CVTOP I32 I64 (EXTEND S)` computes in SpecTec where V2 only traps. `Task.wholeStepBwdV` fixes
`B` to the spec's builtins and asks for code whose conversions V2 defines (`CvtOkL`), which V2's
and Wasm's validation require. -/

mutual
/-- Every active `cvtop` of an administrative instruction is a conversion V2 defines. -/
def CvtOkA : Admin → Prop
  | .plain (.cvtOp t₁ t₂ op) => (V2.CvtOp.toShared t₁ t₂ op).isSome
  | .label _ _ b => CvtOkL b
  | .frame _ _ b => CvtOkL b
  | _ => True

/-- Every active `cvtop` of a code sequence, at any depth of labels and frames, is a conversion
V2 defines. -/
def CvtOkL : List Admin → Prop
  | [] => True
  | a :: l => CvtOkA a ∧ CvtOkL l
end

/-- **The backward half at the spec's builtins, on code whose conversions V2 defines** (frozen,
open): every step of the wasm-2.0 script under the backend reading at `Sim.Floats.floatIntB`, from
the image of a configuration whose image is typed and whose active conversions V2 defines, is the
image of a V2 step. -/
def Task.wholeStepBwdV : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice) (c : Config H) (w : Value),
      Typed20 (simEnv20 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c → CvtOkL c.code →
      Sim.Round6.Reading.SStepB (simEnv20 (Sim.Floats.floatIntB (Profile.spec nd r)))
        (configV hn c) w →
      ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c'

/-! ## The corrected backward target (pass 7)

`Task.wholeStepBwdV` is false (`Sim20.Whole.not_wholeStepBwdV`): the spec's scalar builtins do not
interpret `$lanes_`, so `vtestop-false`, whose only premise is `otherwise`, fires at every
`all_true`. And rules with no premise on the resources they use (`Step/memory.grow-fail`,
`Step/table.grow-fail`), or whose `otherwise` is met because an earlier rule cannot evaluate a
missing table or memory (`table.fill-zero`, …), fire where the frame names no such resource, where
V2 is stuck (`Sim20.Whole.not_wholeStepBwd_noRes`). `Task.wholeStepBwdW` asks the backward half on
code with no vector operator (`NoVecL`) whose named resources exist (`ResOkL`), as Wasm validation
of the frame's module guarantees for the latter. -/

/-- A vector operator: a V2 instruction of the vector group other than `v128.const` and the vector
memory instructions. -/
def vecOp20 : V2.Instr → Bool
  | .vvUnOp .. | .vvBinOp .. | .vvTernOp .. | .vvTestOp .. | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecAllTrue .. | .vecIntRelOp .. | .vecFloatRelOp ..
  | .vecShiftOp .. | .vecBitmask .. | .vecSwizzle .. | .vecShuffle .. | .vecSplat ..
  | .vecExtractLane .. | .vecReplaceLane .. | .vecExtUnOp .. | .vecExtBinOp .. | .vecNarrow ..
  | .vecCvtOp .. => true
  | _ => false

mutual
/-- No active vector operator in an administrative instruction. -/
def NoVecA : Admin → Prop
  | .plain i => vecOp20 i = false
  | .label _ _ b => NoVecL b
  | .frame _ _ b => NoVecL b
  | _ => True

/-- No active vector operator in a code sequence, at any depth of labels and frames. -/
def NoVecL : List Admin → Prop
  | [] => True
  | a :: l => NoVecA a ∧ NoVecL l
end

section Res

variable {H : Type}

/-- The functions, tables, element and data segments, memory, globals and locals that an
instruction names exist in the state `z`. -/
def InstrResOk (z : State H) : V2.Instr → Prop
  | .call x | .refFunc x => (z.func? x).isSome
  | .callIndirect x y => (z.table? x).isSome ∧ (z.type? y).isSome
  | .localGet x | .localSet x | .localTee x => (z.local? x).isSome
  | .globalGet x | .globalSet x => (z.global? x).isSome
  | .tableGet x | .tableSet x | .tableSize x | .tableGrow x | .tableFill x => (z.table? x).isSome
  | .tableCopy x y => (z.table? x).isSome ∧ (z.table? y).isSome
  | .tableInit x y => (z.table? x).isSome ∧ (z.elem? y).isSome
  | .elemDrop x => (z.elem? x).isSome
  | .memoryInit x => (z.mem? memIdx0).isSome ∧ (z.data? x).isSome
  | .dataDrop x => (z.data? x).isSome
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. | .vecLoad .. | .vecLoadLane ..
  | .vecStore .. | .vecStoreLane .. | .memorySize | .memoryGrow | .memoryFill | .memoryCopy =>
      (z.mem? memIdx0).isSome
  | _ => True

mutual
/-- The resources an administrative instruction names exist, each in its own frame: the body of a
`FRAME_` is read in that frame. -/
def ResOkA (s : Store H) (f : Frame) : Admin → Prop
  | .plain i => InstrResOk ⟨s, f⟩ i
  | .label _ _ b => ResOkL s f b
  | .frame _ fi b => ResOkL s fi b
  | _ => True

/-- The resources a code sequence names exist, at any depth of labels and frames. -/
def ResOkL (s : Store H) (f : Frame) : List Admin → Prop
  | [] => True
  | a :: l => ResOkA s f a ∧ ResOkL s f l
end

end Res

/-- **The backward half at the spec's builtins, on vector-free code whose conversions V2 defines and
whose named resources exist** (frozen, open): every step of the wasm-2.0 script under the backend
reading at `Sim.Floats.floatIntB` from the image of such a configuration, whose image is typed, is
the image of a V2 step. -/
def Task.wholeStepBwdW : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice) (c : Config H) (w : Value),
      Typed20 (simEnv20 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c → CvtOkL c.code →
      NoVecL c.code → ResOkL c.store c.frame c.code →
      Sim.Round6.Reading.SStepB (simEnv20 (Sim.Floats.floatIntB (Profile.spec nd r)))
        (configV hn c) w →
      ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c'

end Silmaril.Wasm.SpecTec.Sim20
