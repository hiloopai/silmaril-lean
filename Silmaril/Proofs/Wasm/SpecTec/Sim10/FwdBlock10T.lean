module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdState10T

/-!
# `block`, `loop` and `if` forward in `simEnv10T`

Round 3's leaves at `FwdAt10T`. The bodies are read off the instruction's typing in
`simEnv10T` (`block_body10T`, `loop_body10T`, `if_bodies10T`), so they may contain stores.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV iterPat evalExp_iterPat)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly instrsT evalExp_case evalExp_tup2
  evalExp_tup3 evalExp_list1 typedV_list_iff)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_nil prems_one evalExp_list0
  evalExp_immCmp cmp_ne_zero cmp_eq_zero evalExp_caseNil)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- Every V1 block type is a typed `valtype?` in `simEnv10T`. -/
theorem typedV_blockType10T (bt : V1.BlockType) :
    TypedV (simEnv10T B) (.iterT (.varT "valtype" []) .opt) (blockTypeV bt) :=
  typedV10T (typedV_blockType10 bt)

/-- `admininstr` at `BLOCK`, `LOOP` and `IF%%ELSE%`, in `simEnv10T`. -/
theorem findTyp_admininstr10_ctrlT : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
    findCase cs "BLOCK" = some (.tupT [.mk "blocktype" (.varT "blocktype" []),
      .mk "instr*" (.iterT (.varT "instr" []) .list)], []) ∧
    findCase cs "LOOP" = some (.tupT [.mk "blocktype" (.varT "blocktype" []),
      .mk "instr*" (.iterT (.varT "instr" []) .list)], []) ∧
    findCase cs "IF%%ELSE%" = some (.tupT [.mk "blocktype" (.varT "blocktype" []),
      .mk "instr*" (.iterT (.varT "instr" []) .list),
      .mk "instr*" (.iterT (.varT "instr" []) .list)], []) :=
  let ⟨_, h, h₁, h₂, h₃⟩ := findTyp_admininstr10_ctrl (B := B)
  ⟨_, adminT_lift h, findCaseT h₁ (by decide), findCaseT h₂ (by decide),
    findCaseT h₃ (by decide)⟩

/-- The body of a typed `BLOCK`/`LOOP` payload is a typed `instr*`. -/
theorem body_of_pair10T {u : Value} {is : List Value}
    (h : HasTyp (simEnv10T B) VarEnv.empty (.tupT [.mk "blocktype" (.varT "blocktype" []),
      .mk "instr*" (.iterT (.varT "instr" []) .list)]) (.tuple [u, .list is])) :
    TypedV (simEnv10T B) instrsT (.list is) := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨-, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  exact typedV_list_of_scope ⟨rfl, rfl, rfl⟩ hy'

/-- **The body of a typed `BLOCK` is a typed `instr*`.** -/
theorem block_body10T {bt : V1.BlockType} {body : V1.Expr}
    (h : TypedV (simEnv10T B) adminT10 (instrToV (.block bt body))) :
    TypedV (simEnv10T B) instrsT (.list (instrsToV body)) := by
  obtain ⟨cs, htd, hb, -, -⟩ := findTyp_admininstr10_ctrlT (B := B)
  exact body_of_pair10T (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hb)

/-- **The body of a typed `LOOP` is a typed `instr*`.** -/
theorem loop_body10T {bt : V1.BlockType} {body : V1.Expr}
    (h : TypedV (simEnv10T B) adminT10 (instrToV (.loop bt body))) :
    TypedV (simEnv10T B) instrsT (.list (instrsToV body)) := by
  obtain ⟨cs, htd, -, hl, -⟩ := findTyp_admininstr10_ctrlT (B := B)
  exact body_of_pair10T (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hl)

/-- **The branches of a typed `IF` are typed `instr*`s.** -/
theorem if_bodies10T {bt : V1.BlockType} {b₁ b₂ : V1.Expr}
    (h : TypedV (simEnv10T B) adminT10 (instrToV (.if_ bt b₁ b₂))) :
    TypedV (simEnv10T B) instrsT (.list (instrsToV b₁)) ∧
      TypedV (simEnv10T B) instrsT (.list (instrsToV b₂)) := by
  obtain ⟨cs, htd, -, -, hi⟩ := findTyp_admininstr10_ctrlT (B := B)
  obtain ⟨-, h₁, h₂⟩ := hasTyp_tup3_inv
    (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hi)
    (fun hρ hv => typedV_list_of_scope hρ hv)
  exact ⟨h₁, h₂⟩

/-- **`block` forward**: V1's `PureStep.block`, by `Step_read/block`. -/
theorem fwdAt10T_block (s : Store H) (f : Frame) (bt : V1.BlockType) (body : V1.Expr) :
    FwdAt10T B hn ⟨s, f, [.source (.block bt body)]⟩
      ⟨s, f, [.label bt.toList.length [] (expression body)]⟩ := by
  refine fwdAt10T_of_sread fun hz hc => sread10T_of_fires (k := 0) ?_
  have hb : TypedV (simEnv10T B) instrsT (.list (instrsToV body)) :=
    block_body10T (typedV_head10T hc)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("t?", blockTypeV bt),
    ("instr*", .list (instrsToV body)), ("n", .num (.natN bt.toList.length))]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t?" = some (blockTypeV bt) := rfl
  have fb : (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (instrsToV body)) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN bt.toList.length)) := rfl
  have hrhs : adminsToV [.label bt.toList.length [] (expression body)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN bt.toList.length), .list [],
        .list (instrsToV body)])] := by
    rw [adminsToV_label10, adminsToV_expression]
    rfl
  rw [hrhs]
  exact fires_of_ruleAtT (hasRuleAt10_block B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons ft (typedV_blockType10T bt _
      ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fb (hb _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fn
        (typedV_n10T _ _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case
        (evalExp_tup2 (evalExp_optT10 ft) (evalExp_iterPat (by decide) fb))))))
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) evalExp_list0
        (evalExp_subIterPat (by decide) fb)))))
    (prems_one (.ifPr (evalExp_blockPrem10 ft fn)))

/-- **`loop` forward**: V1's `PureStep.loop`, by `Step_read/loop`. -/
theorem fwdAt10T_loop (s : Store H) (f : Frame) (bt : V1.BlockType) (body : V1.Expr) :
    FwdAt10T B hn ⟨s, f, [.source (.loop bt body)]⟩
      ⟨s, f, [.label 0 [.loop bt body] (expression body)]⟩ := by
  refine fwdAt10T_of_sread fun hz hc => sread10T_of_fires (k := 1) ?_
  have hb : TypedV (simEnv10T B) instrsT (.list (instrsToV body)) :=
    loop_body10T (typedV_head10T hc)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("t?", blockTypeV bt),
    ("instr*", .list (instrsToV body))]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t?" = some (blockTypeV bt) := rfl
  have fb : (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (instrsToV body)) := rfl
  have hloop : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) loopE
      (instrToV (.loop bt body)) :=
    evalExp_case (evalExp_tup2 (evalExp_optT10 ft) (evalExp_iterPat (by decide) fb))
  have hrhs : adminsToV [.label 0 [.loop bt body] (expression body)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN 0), .list [instrToV (.loop bt body)],
        .list (instrsToV body)])] := by
    rw [adminsToV_label10, adminsToV_expression]
    rfl
  rw [hrhs]
  exact fires_of_ruleAtT (hasRuleAt10_loop B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons ft (typedV_blockType10T bt _
      ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fb (hb _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 hloop)))
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_numE_iff.2 rfl) (evalExp_list1 hloop)
        (evalExp_subIterPat (by decide) fb)))))
    prems_nil

/-- `if` forward, for either branch. -/
theorem fwdAt10T_if (s : Store H) (f : Frame) (bt : V1.BlockType) (b₁ b₂ : V1.Expr)
    (c : BitVec 32) (k : Nat) (op : CmpOp) (nm br : IL.Id) (b : V1.Expr) (hbr : br ≠ "_")
    (hrule : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" k (ifRule10 nm br op))
    (hb : (VarEnv.empty.bindVals [("c", pctV c.toNat), ("t?", blockTypeV bt),
      ("instr_1*", .list (instrsToV b₁)), ("instr_2*", .list (instrsToV b₂))]).findVal?
        (br ++ "*") = some (.list (instrsToV b)))
    (hcmp : EvalExp (simEnv10 B) (VarEnv.empty.bindVals [("c", pctV c.toNat),
      ("t?", blockTypeV bt), ("instr_1*", .list (instrsToV b₁)),
      ("instr_2*", .list (instrsToV b₂))]) (immCmpE op "c") (.bool true)) :
    FwdAt10T B hn ⟨s, f, [value (.int .i32 c), .source (.if_ bt b₁ b₂)]⟩
      ⟨s, f, [.source (.block bt b)]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  have hci : TypedV (simEnv10T B) valI32T (pctV c.toNat) := typedV_valI32_of_const10T (by
    have h := typedV_head10T hc
    rwa [adminToV_value] at h)
  obtain ⟨h₁, h₂⟩ := if_bodies10T (typedV_second10T hc)
  let σ : List (IL.Id × Value) := [("c", pctV c.toNat), ("t?", blockTypeV bt),
    ("instr_1*", .list (instrsToV b₁)), ("instr_2*", .list (instrsToV b₂))]
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t?" = some (blockTypeV bt) := rfl
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "instr_1*" = some (.list (instrsToV b₁)) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "instr_2*" = some (.list (instrsToV b₂)) := rfl
  have hrhs : adminsToV [.source (.block bt b)] = [instrToV (.block bt b)] := rfl
  rw [adminsToV_if10, hrhs]
  exact spure10T_of_fires (fires_of_ruleAtT hrule σ
    (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons ft (typedV_blockType10T bt _
      ⟨rfl, rfl, rfl⟩) (QuantsOk.cons f₁ (h₁ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons f₂
        (h₂ _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))
    (evalExp_tup2 (Sim20.Pure.evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil
        (evalExp_var fc))) (evalExp_case (evalExp_tup3 (evalExp_optT10 ft)
          (evalExp_iterPat (x := "instr_1") (by decide) f₁)
          (evalExp_iterPat (x := "instr_2") (by decide) f₂))))
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_optT10 ft)
        (evalExp_iterPat hbr hb)))))
    (prems_one (.ifPr hcmp)) rfl)

/-- **`if-true` forward**: V1's `ifNonzero`. -/
theorem fwdAt10T_ifNonzero (s : Store H) (f : Frame) (bt : V1.BlockType) (b₁ b₂ : V1.Expr)
    (c : BitVec 32) (hc0 : c ≠ 0) :
    FwdAt10T B hn ⟨s, f, [value (.int .i32 c), .source (.if_ bt b₁ b₂)]⟩
      ⟨s, f, [.source (.block bt b₁)]⟩ :=
  fwdAt10T_if s f bt b₁ b₂ c 5 .neOp "if-true" "instr_1" b₁ (by decide) (hasRuleAt10_ifTrue B) rfl
    (evalExp_immCmp rfl (cmp_ne_zero hc0))

/-- **`if-false` forward**: V1's `ifZero`. -/
theorem fwdAt10T_ifZero (s : Store H) (f : Frame) (bt : V1.BlockType) (b₁ b₂ : V1.Expr) :
    FwdAt10T B hn ⟨s, f, [value (.int .i32 0), .source (.if_ bt b₁ b₂)]⟩
      ⟨s, f, [.source (.block bt b₂)]⟩ :=
  fwdAt10T_if s f bt b₁ b₂ 0 6 .eqOp "if-false" "instr_2" b₂ (by decide) (hasRuleAt10_ifFalse B)
    rfl (evalExp_immCmp rfl cmp_eq_zero)


end Silmaril.Wasm.SpecTec.Sim10.Whole
