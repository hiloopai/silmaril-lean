module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RegionFolding.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding.Thms
/-! The actual foldRegion lexical traversal and CFG composition preserve every
finite operational observation on the existing typed pure total arithmetic
fragment. Arbitrarily many actual internal CFG transfers are covered; totality
or divergence preservation of a CFG is not asserted. -/
@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.RegionFolding
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Machine.RTL (Opcode CallOracle packValues)
open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.Lir (Word)
open Folding

theorem EquivalentAt.symm {oracle : CallOracle} {env : Semantics.Env Word} {labels : List Nat}
    {source target : Old.Region} (agreement : EquivalentAt oracle env labels source target) :
    EquivalentAt oracle env labels target source := by
  intro before label value after
  exact ⟨(agreement before label value after).1.symm,
    fun evaluation => (agreement before label value after).2
      ((agreement before label value after).1.mpr evaluation)⟩

theorem exits_internal {internalWidths labels : List Nat} {label : Nat} {value : Value Word}
    (inside : label < internalWidths.length) (exited : Exits (internalWidths ++ labels) label value) :
    ∃ words, (Shape.tuple (internalWidths.getD label 0)).Holds value words := by
  induction internalWidths generalizing label with
  | nil => cases inside
  | cons width rest ih =>
    cases label with
    | zero =>
      obtain ⟨found, words, lookup, holds⟩ := exited
      have same : width = found := Option.some.inj lookup
      exact ⟨words, same ▸ holds⟩
    | succ label => exact ih (Nat.lt_of_succ_lt_succ inside) exited

theorem exits_external {internalWidths labels : List Nat} {label : Nat} {value : Value Word}
    (outside : internalWidths.length ≤ label) (exited : Exits (internalWidths ++ labels) label value) :
    Exits labels (label - internalWidths.length) value := by
  induction internalWidths generalizing label with
  | nil => exact exited
  | cons width rest ih =>
    cases label with
    | zero => cases outside
    | succ label =>
      simpa only [List.length_cons, Nat.add_sub_add_right] using
        ih (Nat.le_of_succ_le_succ outside) exited

/-- Composition through arbitrarily many actual internal CFG transfers. The
block contracts will be derived from the actual recursive foldRegion below. -/
theorem follow_transport {oracle : CallOracle} {env : Semantics.Env Word}
    {count : Nat} {source target : Fin count → Old.Region} {widths labels : List Nat}
    (length : widths.length = count)
    (blocks : ∀ (index : Fin count) (argument : Value Word),
      (∃ words, (Shape.tuple (widths.getD index 0)).Holds argument words) →
      EquivalentAt oracle (Semantics.extend env argument) (widths ++ labels)
        (source index) (target index))
    {first label : Nat} {initial value : Value Word} {before after : Memory}
    (evaluation : Semantics.Region.Follow (Opcode.step oracle) env source
      first initial before label value after) :
    Exits (widths ++ labels) first initial →
      Semantics.Region.Follow (Opcode.step oracle) env target first initial before label value after ∧
      Exits labels label value ∧ after = before := by
  induction evaluation using Semantics.Region.Follow.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside =>
    intro incoming
    refine ⟨.exit outside, ?_, rfl⟩
    simpa only [length] using exits_external (by omega) incoming
  | @step captured n first next out source initial middle value before intermediate after inside
      head tail ignored ih =>
    intro incoming
    have argumentShape : ∃ words, (Shape.tuple (widths.getD first 0)).Holds initial words :=
      exits_internal (by omega) incoming
    have contract := blocks ⟨first, inside⟩ initial argumentShape
    have headTarget : Semantics.Region.Eval (Opcode.step oracle) (Semantics.extend captured initial)
        (target ⟨first, inside⟩) before next middle intermediate :=
      (contract before next middle intermediate).1.mp head
    obtain ⟨nextShape, headMemory⟩ := (contract before next middle intermediate).2 head
    obtain ⟨tailTarget, resultShape, tailMemory⟩ := ih length blocks nextShape
    exact ⟨.step inside headTarget tailTarget, resultShape, tailMemory.trans headMemory⟩
  | _ => trivial

private theorem directions {first second post : Prop}
    (forward : first → second ∧ post) (backward : second → first ∧ post) :
    (first ↔ second) ∧ (first → post) :=
  ⟨⟨fun h => (forward h).1, fun h => (backward h).1⟩, fun h => (forward h).2⟩

private theorem cfg_forward {oracle : CallOracle} {env : Semantics.Env Word}
    {count : Nat} {source target : Fin count → Old.Region} {widths labels : List Nat}
    {sourceEntry targetEntry : Old.Region} (length : widths.length = count)
    (entry : EquivalentAt oracle env (widths ++ labels) sourceEntry targetEntry)
    (blocks : ∀ (index : Fin count) (argument : Value Word),
      (∃ words, (Shape.tuple (widths.getD index 0)).Holds argument words) →
      EquivalentAt oracle (Semantics.extend env argument) (widths ++ labels)
        (source index) (target index))
    {before after : Memory} {label : Nat} {value : Value Word}
    (evaluation : Semantics.Region.Eval (Opcode.step oracle) env (.cfg sourceEntry count source)
      before label value after) :
    Semantics.Region.Eval (Opcode.step oracle) env (.cfg targetEntry count target)
      before label value after ∧ Exits labels label value ∧ after = before := by
  cases evaluation with
  | cfg initial follow =>
    have initialTarget := (entry _ _ _ _).1.mp initial
    obtain ⟨initialShape, initialMemory⟩ := (entry _ _ _ _).2 initial
    obtain ⟨followTarget, exitShape, followMemory⟩ := follow_transport length blocks follow initialShape
    exact ⟨.cfg initialTarget followTarget, exitShape, followMemory.trans initialMemory⟩

theorem cfg_equivalent {oracle : CallOracle} {env : Semantics.Env Word}
    {count : Nat} {source target : Fin count → Old.Region} {widths labels : List Nat}
    {sourceEntry targetEntry : Old.Region} (length : widths.length = count)
    (entry : EquivalentAt oracle env (widths ++ labels) sourceEntry targetEntry)
    (blocks : ∀ (index : Fin count) (argument : Value Word),
      (∃ words, (Shape.tuple (widths.getD index 0)).Holds argument words) →
      EquivalentAt oracle (Semantics.extend env argument) (widths ++ labels)
        (source index) (target index)) :
    EquivalentAt oracle env labels (.cfg sourceEntry count source) (.cfg targetEntry count target) := by
  intro before label value after
  exact directions (cfg_forward length entry blocks)
    (cfg_forward length entry.symm (fun index argument shape => (blocks index argument shape).symm))

private theorem br_forward {oracle : CallOracle} {env : Semantics.Env Word}
    {source target : Old.Tm} {before after : Memory} {result value : Value Word}
    {labels : List Nat} {destination label : Nat}
    (pure : source.ForallInstr ArithmeticOpcode)
    (sourceArg : Semantics.Tm.Eval (Opcode.step oracle) env source before result before)
    (targetArg : Semantics.Tm.Eval (Opcode.step oracle) env target before result before)
    (resultShape : Exits labels destination result)
    (evaluation : Semantics.Region.Eval (Opcode.step oracle) env (.br destination source)
      before label value after) :
    Semantics.Region.Eval (Opcode.step oracle) env (.br destination target)
      before label value after ∧ Exits labels label value ∧ after = before := by
  cases evaluation with
  | br argument =>
    obtain ⟨rfl, rfl⟩ := eval_deterministic pure sourceArg argument
    exact ⟨.br targetArg, resultShape, rfl⟩

private theorem let₁_forward {oracle : CallOracle} {env : Semantics.Env Word}
    {source target : Old.Tm} {sourceBody targetBody : Old.Region}
    {before after : Memory} {result value : Value Word} {labels : List Nat} {label : Nat}
    (pure : source.ForallInstr ArithmeticOpcode)
    (sourceArg : Semantics.Tm.Eval (Opcode.step oracle) env source before result before)
    (targetArg : Semantics.Tm.Eval (Opcode.step oracle) env target before result before)
    (body : EquivalentAt oracle (Semantics.extend env result) labels sourceBody targetBody)
    (evaluation : Semantics.Region.Eval (Opcode.step oracle) env (.let₁ source sourceBody)
      before label value after) :
    Semantics.Region.Eval (Opcode.step oracle) env (.let₁ target targetBody)
      before label value after ∧ Exits labels label value ∧ after = before := by
  cases evaluation with
  | let₁ argument continuation =>
    obtain ⟨rfl, rfl⟩ := eval_deterministic pure sourceArg argument
    exact ⟨.let₁ targetArg ((body _ _ _ _).1.mp continuation), (body _ _ _ _).2 continuation⟩

private theorem let₂_forward {oracle : CallOracle} {env : Semantics.Env Word}
    {source target : Old.Tm} {sourceBody targetBody : Old.Region}
    {before after : Memory} {left right value : Value Word} {labels : List Nat} {label : Nat}
    (pure : source.ForallInstr ArithmeticOpcode)
    (sourceArg : Semantics.Tm.Eval (Opcode.step oracle) env source before (.pair left right) before)
    (targetArg : Semantics.Tm.Eval (Opcode.step oracle) env target before (.pair left right) before)
    (body : EquivalentAt oracle (Semantics.extend (Semantics.extend env left) right)
      labels sourceBody targetBody)
    (evaluation : Semantics.Region.Eval (Opcode.step oracle) env (.let₂ source sourceBody)
      before label value after) :
    Semantics.Region.Eval (Opcode.step oracle) env (.let₂ target targetBody)
      before label value after ∧ Exits labels label value ∧ after = before := by
  cases evaluation with
  | let₂ argument continuation =>
    obtain ⟨same, rfl⟩ := eval_deterministic pure sourceArg argument
    obtain ⟨rfl, rfl⟩ := Value.pair.inj same
    exact ⟨.let₂ targetArg ((body _ _ _ _).1.mp continuation), (body _ _ _ _).2 continuation⟩

/-- Actual recursive region traversal, including arbitrary finite CFG transfers.
Its only premises inspect the existing typing, syntax and input environments. -/
theorem foldRegion_equivalent (oracle : CallOracle)
    {context : List Shape} {region : Old.Region} {annotation : Silmaril.Machine.RTL.SSA.Ann}
    {labels : List Nat} (typed : RegionFits [] context region annotation labels)
    (pure : region.ForallInstr ArithmeticOpcode)
    {known : List Abstract} {env : Semantics.Env Word}
    (models : EnvironmentModels known env) (shapes : ShapeEnvironment context env) :
    EquivalentAt oracle env labels region (foldRegion known region).1 := by
  induction typed generalizing known env with
  | @br context labels destination width argument lookup typedArg =>
    show EquivalentAt oracle env labels (.br destination argument) _
    intro before label value after
    obtain ⟨result, words, sourceArg, foldedArg, modelsResult, shapeResult⟩ :=
      foldTm_total oracle before typedArg pure models shapes
    exact directions (br_forward pure sourceArg foldedArg ⟨_, words, lookup, shapeResult⟩)
      (br_forward (foldTm_pure pure known) foldedArg sourceArg ⟨_, words, lookup, shapeResult⟩)
  | @let₁ context labels argument continuation annotation shape typedValue typedBody ihBody =>
    show EquivalentAt oracle env labels (.let₁ argument continuation) _
    intro before label value after
    obtain ⟨result, words, sourceArg, foldedArg, modelsResult, shapeResult⟩ :=
      foldTm_total oracle before typedValue pure.1 models shapes
    have body : EquivalentAt oracle (Semantics.extend env result) labels continuation
        (foldRegion ((foldTm known argument).2.1 :: known) continuation).1 :=
      ihBody pure.2 (environment_cons models modelsResult) (shape_environment_cons shapes shapeResult)
    exact directions (let₁_forward pure.1 sourceArg foldedArg body)
      (let₁_forward (foldTm_pure pure.1 known) foldedArg sourceArg body.symm)
  | @let₂ context labels argument continuation annotation n typedValue typedBody ihBody =>
    show EquivalentAt oracle env labels (.let₂ argument continuation) _
    intro before label value after
    obtain ⟨result, words, sourceArg, foldedArg, modelsResult, shapeResult⟩ :=
      foldTm_total oracle before typedValue pure.1 models shapes
    obtain ⟨rfl, length⟩ := shapeResult
    cases words with
    | nil => cases length
    | cons word rest =>
      show (Semantics.Region.Eval (Opcode.step oracle) env (.let₂ argument continuation) before label value after ↔
        Semantics.Region.Eval (Opcode.step oracle) env (foldRegion known (.let₂ argument continuation)).1 before label value after) ∧
        (Semantics.Region.Eval (Opcode.step oracle) env (.let₂ argument continuation) before label value after →
          Exits labels label value ∧ after = before)
      have components :
          let components := match (foldTm known argument).2.1 with
            | .pair a b => (a, b)
            | _ => (.unknown, .unknown)
          Models components.1 (.atom word) ∧ Models components.2 (packValues rest) :=
        models_components modelsResult
      have body :
          let components := match (foldTm known argument).2.1 with
            | .pair a b => (a, b)
            | _ => (.unknown, .unknown)
          EquivalentAt oracle (Semantics.extend (Semantics.extend env (.atom word)) (packValues rest))
            labels continuation (foldRegion (components.2 :: components.1 :: known) continuation).1 :=
        ihBody pure.2 (environment_cons (environment_cons models components.1) components.2)
          (shape_environment_cons (shape_environment_cons shapes
            (shape := Shape.word) (words := [word]) ⟨word, rfl, rfl⟩)
            (shape := Shape.tuple _) (words := rest) ⟨rfl, Nat.succ.inj length⟩)
      exact directions (let₂_forward pure.1 sourceArg foldedArg body)
        (let₂_forward (foldTm_pure pure.1 known) foldedArg sourceArg body.symm)
  | case typedDiscr typedLeft typedRight ihLeft ihRight => cases pure.1.1
  | @cfg context labels entry count source widths entryAnn blockAnns length typedEntry typedBlocks ihEntry ihBlocks =>
    show EquivalentAt oracle env labels (.cfg entry count source) _
    have entryAgreement : EquivalentAt oracle env (widths ++ labels) entry (foldRegion known entry).1 :=
      ihEntry pure.1 models shapes
    apply cfg_equivalent length entryAgreement
    intro index argument argumentShape
    obtain ⟨words, holds⟩ := argumentShape
    exact ihBlocks index (pure.2 index) (environment_cons models (models_unknown argument))
      (shape_environment_cons shapes holds)

/-- The public actual finite-evaluation equation, with no execution premise. -/
theorem foldRegion_eval_iff (oracle : CallOracle)
    {context : List Shape} {region : Old.Region} {annotation : Silmaril.Machine.RTL.SSA.Ann}
    {labels : List Nat} (typed : RegionFits [] context region annotation labels)
    (pure : region.ForallInstr ArithmeticOpcode)
    {known : List Abstract} {env : Semantics.Env Word}
    (models : EnvironmentModels known env) (shapes : ShapeEnvironment context env)
    (before : Memory) (label : Nat) (value : Value Word) (after : Memory) :
    Semantics.Region.Eval (Opcode.step oracle) env (foldRegion known region).1 before label value after ↔
      Semantics.Region.Eval (Opcode.step oracle) env region before label value after :=
  ((foldRegion_equivalent oracle typed pure models shapes) before label value after).1.symm

/-- Every actual finite folded exit has its declared tuple shape and preserves
memory; a CFG may still loop forever instead of producing such an exit. -/
theorem foldRegion_exit (oracle : CallOracle)
    {context : List Shape} {region : Old.Region} {annotation : Silmaril.Machine.RTL.SSA.Ann}
    {labels : List Nat} (typed : RegionFits [] context region annotation labels)
    (pure : region.ForallInstr ArithmeticOpcode)
    {known : List Abstract} {env : Semantics.Env Word}
    (models : EnvironmentModels known env) (shapes : ShapeEnvironment context env)
    {before : Memory} {label : Nat} {value : Value Word} {after : Memory}
    (evaluation : Semantics.Region.Eval (Opcode.step oracle) env (foldRegion known region).1
      before label value after) : Exits labels label value ∧ after = before :=
  ((foldRegion_equivalent oracle typed pure models shapes).symm before label value after).2 evaluation

end Silmaril.Compiler.Native.Optimize.LambdaSSA.RegionFolding
