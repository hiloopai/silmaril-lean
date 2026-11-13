module

public import Silmaril.Proofs.Wasm.Models.V10Lime1Back.Inv

/-!
# Backward simulation of pure steps

`pure_back`: a Lime1 pure step from the image of 1.0 code is the image of a 1.0 pure step. On
the image, a Lime1 block type resolves to `[] → t?` (`blockType_toLime`), so `block` and `loop`
take no operands, and the Lime1 rules are the 1.0 rules read through `codeToLime`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Lime1Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution (codeToLime)

/-- The 1.0 preimage of a value prefix followed by one instruction. -/
theorem code_vals_source {A : List VAdmin} {vs : List Value} {j : Lime1.Instr} :
    codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ [.source j] ↔
      ∃ j₀, A = Silmaril.Wasm.V1.Execution.values vs ++ [.source j₀] ∧ j₀.toLime = j := by
  rw [code_values_append]
  constructor
  · rintro ⟨A₂, rfl, h⟩
    obtain ⟨a, A', rfl, ha, hA'⟩ := code_cons.mp h
    obtain ⟨j₀, rfl, hj⟩ := map_source.mp ha
    have hnil : A' = [] := code_nil.mp hA'
    exact ⟨j₀, by rw [hnil], hj⟩
  · rintro ⟨j₀, rfl, rfl⟩
    exact ⟨_, rfl, rfl⟩

/-- What a backward pure step provides. -/
def Back (A : List VAdmin) (after : List LAdmin) : Prop :=
  ∃ B, Silmaril.Wasm.V1.Execution.PureStep A B ∧ after = codeToLime B

/-- The common shape: the Lime1 rule is the image of a 1.0 rule at the same instruction. -/
theorem back_of_image {A : List VAdmin} {vs : List Value} {j : Silmaril.Wasm.V1.Instr}
    {after : List LAdmin}
    (hA : codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ [.source j.toLime])
    {B : List VAdmin}
    (hstep : Silmaril.Wasm.V1.Execution.PureStep
      (Silmaril.Wasm.V1.Execution.values vs ++ [.source j]) B)
    (hafter : after = codeToLime B) : Back A after := by
  obtain ⟨j₀, rfl, hj⟩ := code_vals_source.mp hA
  have hj' : j₀ = j := Silmaril.Wasm.V1.Instr.toLime_injective hj
  exact ⟨B, hj' ▸ hstep, hafter⟩

open Silmaril.Wasm.V1.Execution (PureStep) in
/-- A label's preimage. -/
theorem code_label {A : List VAdmin} {n : Nat} {cont : Lime1.Expr} {body : List LAdmin}
    (hA : codeToLime A = [.label n cont body]) :
    ∃ cont₀ body₀, A = [.label n cont₀ body₀] ∧
      Silmaril.Wasm.V1.Expr.toLime cont₀ = cont ∧ codeToLime body₀ = body := by
  obtain ⟨a, A', rfl, ha, hA'⟩ := code_cons.mp hA
  obtain ⟨cont₀, body₀, rfl, hc, hb⟩ := map_label.mp ha
  have hnil : A' = [] := code_nil.mp hA'
  exact ⟨cont₀, body₀, by rw [hnil], by rw [Silmaril.Wasm.V1.Expr.toLime_eq_map, hc], hb⟩

/-- A frame's preimage. -/
theorem code_frame {A : List VAdmin} {n : Nat} {fr : Frame} {body : List LAdmin}
    (hA : codeToLime A = [.frame n fr body]) :
    ∃ body₀, A = [.frame n fr body₀] ∧ codeToLime body₀ = body := by
  obtain ⟨a, A', rfl, ha, hA'⟩ := code_cons.mp hA
  obtain ⟨body₀, rfl, hb⟩ := map_frame.mp ha
  have hnil : A' = [] := code_nil.mp hA'
  exact ⟨body₀, by rw [hnil], hb⟩

/-- A value prefix, one instruction and a tail. -/
theorem code_vals_source_tail {A : List VAdmin} {vs : List Value} {j : Lime1.Instr}
    {tail : List LAdmin}
    (hA : codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ [.source j] ++ tail) :
    ∃ j₀ tail₀, A = Silmaril.Wasm.V1.Execution.values vs ++ [.source j₀] ++ tail₀ ∧
      j₀.toLime = j ∧ codeToLime tail₀ = tail := by
  rw [List.append_assoc] at hA
  obtain ⟨A₂, rfl, h₂⟩ := code_values_append.mp hA
  obtain ⟨a, A', rfl, ha, hA'⟩ := code_cons.mp h₂
  obtain ⟨j₀, rfl, hj⟩ := map_source.mp ha
  exact ⟨j₀, A', by simp, hj, hA'⟩

theorem back_block {types : List Lime1.FuncType} {A : List VAdmin} {bt : Lime1.BlockType}
    {body : Lime1.Expr} {ft : Lime1.FuncType} {vs : List Value}
    (resolved : Silmaril.Wasm.Lime1.Execution.blockType? types bt = some ft)
    (arity : vs.length = ft.params.length)
    (hA : codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ [.source (.block bt body)]) :
    Back A [.label ft.results.length []
      (Silmaril.Wasm.Lime1.Execution.values vs ++ Silmaril.Wasm.Lime1.Execution.expression body)] := by
  obtain ⟨j₀, rfl, hj⟩ := code_vals_source.mp hA
  cases j₀ <;> simp only [Silmaril.Wasm.V1.Instr.toLime, reduceCtorEq,
    Lime1.Instr.block.injEq] at hj
  obtain ⟨rfl, rfl⟩ := hj
  rename_i t b
  have hft : ft = ⟨[], t.toList⟩ := by
    rw [Silmaril.Wasm.V1.Execution.blockType_toLime] at resolved
    exact (Option.some.inj resolved).symm
  subst hft
  have hvs : vs = [] := List.eq_nil_of_length_eq_zero arity
  subst hvs
  exact ⟨_, .block t b, by simp [AdminInstr.map, Silmaril.Wasm.Lime1.Execution.values]⟩

theorem back_loop {types : List Lime1.FuncType} {A : List VAdmin} {bt : Lime1.BlockType}
    {body : Lime1.Expr} {ft : Lime1.FuncType} {vs : List Value}
    (resolved : Silmaril.Wasm.Lime1.Execution.blockType? types bt = some ft)
    (arity : vs.length = ft.params.length)
    (hA : codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ [.source (.loop bt body)]) :
    Back A [.label ft.params.length [.loop bt body]
      (Silmaril.Wasm.Lime1.Execution.values vs ++ Silmaril.Wasm.Lime1.Execution.expression body)] := by
  obtain ⟨j₀, rfl, hj⟩ := code_vals_source.mp hA
  cases j₀ <;> simp only [Silmaril.Wasm.V1.Instr.toLime, reduceCtorEq,
    Lime1.Instr.loop.injEq] at hj
  obtain ⟨rfl, rfl⟩ := hj
  rename_i t b
  have hft : ft = ⟨[], t.toList⟩ := by
    rw [Silmaril.Wasm.V1.Execution.blockType_toLime] at resolved
    exact (Option.some.inj resolved).symm
  subst hft
  have hvs : vs = [] := List.eq_nil_of_length_eq_zero arity
  subst hvs
  exact ⟨_, .loop t b, by simp [AdminInstr.map, Silmaril.Wasm.V1.Instr.toLime, Silmaril.Wasm.Lime1.Execution.values]⟩

theorem back_if {A : List VAdmin} {c : BitVec 32} {bt : Lime1.BlockType} {l r : Lime1.Expr}
    {pick : Lime1.Expr}
    (hpick : ∀ t l₀ r₀, Silmaril.Wasm.V1.Instr.toLime (.if_ t l₀ r₀) = .if_ bt l r →
      ∃ p₀, Silmaril.Wasm.V1.Execution.PureStep
        [Silmaril.Wasm.V1.Execution.value (.int .i32 c), .source (.if_ t l₀ r₀)]
        [.source (.block t p₀)] ∧ Silmaril.Wasm.V1.Expr.toLime p₀ = pick ∧ t.toLime = bt)
    (hA : codeToLime A = [Silmaril.Wasm.Lime1.Execution.value (.int .i32 c),
      .source (.if_ bt l r)]) :
    Back A [.source (.block bt pick)] := by
  obtain ⟨j₀, rfl, hj⟩ := (code_vals_source (vs := [.int .i32 c])).mp hA
  cases j₀ <;> simp only [Silmaril.Wasm.V1.Instr.toLime, reduceCtorEq] at hj
  rename_i t l₀ r₀
  obtain ⟨p₀, hstep, hp, ht⟩ := hpick t l₀ r₀ (by simpa only [Silmaril.Wasm.V1.Instr.toLime] using hj)
  exact ⟨_, hstep, by simp [AdminInstr.map, Silmaril.Wasm.V1.Instr.toLime, hp, ht]⟩

theorem if_inj {t : Silmaril.Wasm.V1.BlockType} {l₀ r₀ : Silmaril.Wasm.V1.Expr}
    {bt : Lime1.BlockType} {l r : Lime1.Expr}
    (h : Silmaril.Wasm.V1.Instr.toLime (.if_ t l₀ r₀) = .if_ bt l r) :
    t.toLime = bt ∧ Silmaril.Wasm.V1.Expr.toLime l₀ = l ∧ Silmaril.Wasm.V1.Expr.toLime r₀ = r := by
  simpa only [Silmaril.Wasm.V1.Instr.toLime, Lime1.Instr.if_.injEq] using h

theorem back_intUnary {A : List VAdmin} {t : IntType} {op : Lime1.IntUnOp} {x : BitVec t.width}
    (hA : codeToLime A = [Silmaril.Wasm.Lime1.Execution.value (.int t x), .source (.intUnOp t op)]) :
    Back A [Silmaril.Wasm.Lime1.Execution.value (.int t (Numerics.intUnOp t op.toCore x))] := by
  obtain ⟨j₀, rfl, hj⟩ := (code_vals_source (vs := [.int t x])).mp hA
  cases j₀ <;> simp only [Silmaril.Wasm.V1.Instr.toLime, reduceCtorEq,
    Lime1.Instr.intUnOp.injEq] at hj
  obtain ⟨rfl, rfl⟩ := hj
  exact ⟨_, .intUnary _ _ x, by simp⟩

theorem back_convert {A : List VAdmin} {op : ConvertOp} {x : Numerics.NumValue op.source}
    {after : List LAdmin}
    (hA : codeToLime A = [Silmaril.Wasm.Lime1.Execution.value ⟨op.source, x⟩, .source (.convert op)])
    (hrule : ∀ op₀ : Silmaril.Wasm.V1.ConvertOp, op₀.toCore = op → Back
      [Silmaril.Wasm.V1.Execution.value ⟨op.source, x⟩, .source (.convert op₀)] after) :
    Back A after := by
  obtain ⟨j₀, rfl, hj⟩ := (code_vals_source (vs := [⟨op.source, x⟩])).mp hA
  cases j₀ <;> simp only [Silmaril.Wasm.V1.Instr.toLime, reduceCtorEq,
    Lime1.Instr.convert.injEq] at hj
  exact hrule _ hj

theorem back_labelDone {A : List VAdmin} {n : Nat} {cont : Lime1.Expr} {vs : List Value}
    (hA : codeToLime A = [.label n cont (Silmaril.Wasm.Lime1.Execution.values vs)]) :
    Back A (Silmaril.Wasm.Lime1.Execution.values vs) := by
  obtain ⟨cont₀, body₀, rfl, -, hb⟩ := code_label hA
  have hb' : body₀ = Silmaril.Wasm.V1.Execution.values vs := code_values.mp hb
  rw [hb']
  exact ⟨_, .labelDone n cont₀ vs, by simp⟩

theorem back_labelTrap {A : List VAdmin} {n : Nat} {cont : Lime1.Expr}
    (hA : codeToLime A = [.label n cont [.trap]]) : Back A [.trap] := by
  obtain ⟨cont₀, body₀, rfl, -, hb⟩ := code_label hA
  obtain ⟨a, A', rfl, ha, hA'⟩ := code_cons.mp hb
  have h₁ : a = .trap := map_trap.mp ha
  have h₂ : A' = [] := code_nil.mp hA'
  subst h₁ h₂
  exact ⟨_, .labelTrap n cont₀, rfl⟩

theorem back_frameDone {A : List VAdmin} {n : Nat} {fr : Frame} {vs : List Value}
    (arity : vs.length = n)
    (hA : codeToLime A = [.frame n fr (Silmaril.Wasm.Lime1.Execution.values vs)]) :
    Back A (Silmaril.Wasm.Lime1.Execution.values vs) := by
  obtain ⟨body₀, rfl, hb⟩ := code_frame hA
  have hb' : body₀ = Silmaril.Wasm.V1.Execution.values vs := code_values.mp hb
  rw [hb']
  exact ⟨_, .frameDone n fr vs arity, by simp⟩

theorem back_frameTrap {A : List VAdmin} {n : Nat} {fr : Frame}
    (hA : codeToLime A = [.frame n fr [.trap]]) : Back A [.trap] := by
  obtain ⟨body₀, rfl, hb⟩ := code_frame hA
  obtain ⟨a, A', rfl, ha, hA'⟩ := code_cons.mp hb
  have h₁ : a = .trap := map_trap.mp ha
  have h₂ : A' = [] := code_nil.mp hA'
  subst h₁ h₂
  exact ⟨_, .frameTrap n fr, rfl⟩

theorem back_trapTail {A : List VAdmin} {i : LAdmin} {tail : List LAdmin}
    (hA : codeToLime A = .trap :: i :: tail) : Back A [.trap] := by
  obtain ⟨a, A', rfl, ha, hA'⟩ := code_cons.mp hA
  obtain ⟨b, A'', rfl, -, -⟩ := code_cons.mp hA'
  have h₁ : a = .trap := map_trap.mp ha
  subst h₁
  exact ⟨_, .trapTail b A'', rfl⟩

theorem back_trapValues {A : List VAdmin} {v : Value} {vs : List Value} {tail : List LAdmin}
    (hA : codeToLime A = Silmaril.Wasm.Lime1.Execution.values (v :: vs) ++ [.trap] ++ tail) :
    Back A [.trap] := by
  rw [List.append_assoc] at hA
  obtain ⟨A₂, rfl, h₂⟩ := code_values_append.mp hA
  obtain ⟨a, A', rfl, ha, -⟩ := code_cons.mp h₂
  have h₁ : a = .trap := map_trap.mp ha
  exact ⟨_, by simpa [h₁] using Silmaril.Wasm.V1.Execution.PureStep.trapValues v vs A', rfl⟩

theorem back_labelBranchOuter {A : List VAdmin} {n : Nat} {cont : Lime1.Expr} {vs : List Value}
    {tail : List LAdmin} {l : LabelIdx} (outer : l.toNat ≠ 0)
    (hA : codeToLime A = [.label n cont
      (Silmaril.Wasm.Lime1.Execution.values vs ++ [.source (.br l)] ++ tail)]) :
    Back A (Silmaril.Wasm.Lime1.Execution.values vs ++
      [.source (.br (Silmaril.Wasm.Lime1.Execution.lowerLabel l))]) := by
  obtain ⟨cont₀, body₀, rfl, -, hb⟩ := code_label hA
  obtain ⟨j₀, tail₀, rfl, hj, -⟩ := code_vals_source_tail hb
  have hj' : j₀ = .br l := Silmaril.Wasm.V1.Instr.toLime_injective (a₂ := .br l) hj
  subst hj'
  exact ⟨_, .labelBranchOuter n cont₀ vs tail₀ l outer, by simp [AdminInstr.map,
    Silmaril.Wasm.V1.Instr.toLime]⟩

theorem back_labelReturn {A : List VAdmin} {n : Nat} {cont : Lime1.Expr} {vs : List Value}
    {tail : List LAdmin}
    (hA : codeToLime A = [.label n cont
      (Silmaril.Wasm.Lime1.Execution.values vs ++ [.source .return_] ++ tail)]) :
    Back A (Silmaril.Wasm.Lime1.Execution.values vs ++ [.source .return_]) := by
  obtain ⟨cont₀, body₀, rfl, -, hb⟩ := code_label hA
  obtain ⟨j₀, tail₀, rfl, hj, -⟩ := code_vals_source_tail hb
  have hj' : j₀ = .return_ := Silmaril.Wasm.V1.Instr.toLime_injective (a₂ := .return_) hj
  subst hj'
  exact ⟨_, .labelReturn n cont₀ vs tail₀, by simp [AdminInstr.map,
    Silmaril.Wasm.V1.Instr.toLime]⟩

theorem back_labelBranch {A : List VAdmin} {n : Nat} {cont : Lime1.Expr} {extra vs : List Value}
    {tail : List LAdmin} (arity : vs.length = n)
    (hA : codeToLime A = [.label n cont (Silmaril.Wasm.Lime1.Execution.values extra ++
      Silmaril.Wasm.Lime1.Execution.values vs ++ [.source (.br ⟨0⟩)] ++ tail)]) :
    Back A (Silmaril.Wasm.Lime1.Execution.values vs ++
      Silmaril.Wasm.Lime1.Execution.expression cont) := by
  obtain ⟨cont₀, body₀, rfl, hc, hb⟩ := code_label hA
  have hb' : codeToLime body₀ = Silmaril.Wasm.Lime1.Execution.values extra ++
      (Silmaril.Wasm.Lime1.Execution.values vs ++ [.source (.br ⟨0⟩)] ++ tail) := by
    simpa only [List.append_assoc] using hb
  obtain ⟨B, rfl, hB⟩ := code_values_append.mp hb'
  obtain ⟨j₀, tail₀, rfl, hj, -⟩ := code_vals_source_tail hB
  have hj' : j₀ = .br ⟨0⟩ := Silmaril.Wasm.V1.Instr.toLime_injective (a₂ := .br ⟨0⟩) hj
  refine ⟨_, by simpa [List.append_assoc, hj'] using
    Silmaril.Wasm.V1.Execution.PureStep.labelBranch n cont₀ extra vs tail₀ arity, ?_⟩
  simp [← hc]

theorem back_frameReturn {A : List VAdmin} {n : Nat} {fr : Frame} {extra vs : List Value}
    {tail : List LAdmin} (arity : vs.length = n)
    (hA : codeToLime A = [.frame n fr (Silmaril.Wasm.Lime1.Execution.values extra ++
      Silmaril.Wasm.Lime1.Execution.values vs ++ [.source .return_] ++ tail)]) :
    Back A (Silmaril.Wasm.Lime1.Execution.values vs) := by
  obtain ⟨body₀, rfl, hb⟩ := code_frame hA
  have hb' : codeToLime body₀ = Silmaril.Wasm.Lime1.Execution.values extra ++
      (Silmaril.Wasm.Lime1.Execution.values vs ++ [.source .return_] ++ tail) := by
    simpa only [List.append_assoc] using hb
  obtain ⟨B, rfl, hB⟩ := code_values_append.mp hb'
  obtain ⟨j₀, tail₀, rfl, hj, -⟩ := code_vals_source_tail hB
  have hj' : j₀ = .return_ := Silmaril.Wasm.V1.Instr.toLime_injective (a₂ := .return_) hj
  refine ⟨_, by simpa [List.append_assoc, hj'] using
    Silmaril.Wasm.V1.Execution.PureStep.frameReturn n fr extra vs tail₀ arity, ?_⟩
  simp

/-- **Backward simulation of pure steps.** -/
theorem pure_back {types : List Lime1.FuncType} {before after : List LAdmin}
    (hp : Silmaril.Wasm.Lime1.Execution.PureStep types before after) (A : List VAdmin)
    (hA : codeToLime A = before) : Back A after := by
  cases hp with
  | nop => exact back_of_image (vs := []) (j := .nop) hA .nop rfl
  | unreachable => exact back_of_image (vs := []) (j := .unreachable) hA .unreachable rfl
  | drop v => exact back_of_image (vs := [v]) (j := .drop) hA (.drop v) rfl
  | selectZero a b ht =>
    exact back_of_image (vs := [a, b, .int .i32 0]) (j := .select) hA (.selectZero a b ht)
      (by simp)
  | selectNonzero a b ht c hc =>
    exact back_of_image (vs := [a, b, .int .i32 c]) (j := .select) hA
      (.selectNonzero a b ht c hc) (by simp)
  | block bt body ft resolved vs arity => exact back_block resolved arity hA
  | loop bt body ft resolved vs arity => exact back_loop resolved arity hA
  | ifZero bt left right =>
    exact back_if (fun t l₀ r₀ h => ⟨r₀, .ifZero t l₀ r₀, (if_inj h).2.2, (if_inj h).1⟩) hA
  | ifNonzero bt left right c hc =>
    exact back_if (fun t l₀ r₀ h => ⟨l₀, .ifNonzero t l₀ r₀ c hc, (if_inj h).2.1, (if_inj h).1⟩) hA
  | brIfZero l => exact back_of_image (vs := [.int .i32 0]) (j := .brIf l) hA (.brIfZero l) rfl
  | brIfNonzero l c hc =>
    exact back_of_image (vs := [.int .i32 c]) (j := .brIf l) hA (.brIfNonzero l c hc) rfl
  | brTable ls d c =>
    exact back_of_image (vs := [.int .i32 c]) (j := .brTable ls d) hA (.brTable ls d c) rfl
  | labelDone n cont vs => exact back_labelDone hA
  | labelBranch n cont extra vs tail arity => exact back_labelBranch arity hA
  | labelBranchOuter n cont vs tail l outer => exact back_labelBranchOuter outer hA
  | labelReturn n cont vs tail => exact back_labelReturn hA
  | frameDone n f vs arity => exact back_frameDone arity hA
  | frameReturn n f extra vs tail arity => exact back_frameReturn arity hA
  | trapValues v vs tail => exact back_trapValues hA
  | trapTail i tail => exact back_trapTail hA
  | labelTrap n cont => exact back_labelTrap hA
  | frameTrap n f => exact back_frameTrap hA
  | localTee i v =>
    exact back_of_image (vs := [v]) (j := .localTee i) hA (.localTee i v) (by simp [AdminInstr.map,
      Silmaril.Wasm.V1.Instr.toLime])
  | intUnary t op x valid => exact back_intUnary hA
  | intBinary t op x y z h =>
    exact back_of_image (vs := [.int t x, .int t y]) (j := .intBinOp t op) hA
      (.intBinary t op x y z h) (by simp)
  | intBinaryTrap t op x y err h =>
    exact back_of_image (vs := [.int t x, .int t y]) (j := .intBinOp t op) hA
      (.intBinaryTrap t op x y err h) rfl
  | intTest t op x =>
    exact back_of_image (vs := [.int t x]) (j := .intTestOp t op) hA (.intTest t op x) (by simp)
  | intRel t op x y =>
    exact back_of_image (vs := [.int t x, .int t y]) (j := .intRelOp t op) hA (.intRel t op x y)
      (by simp)
  | floatUnary t op x y h =>
    exact back_of_image (vs := [.float t x]) (j := .floatUnOp t op) hA (.floatUnary t op x y h)
      (by simp)
  | floatBinary t op x y z h =>
    exact back_of_image (vs := [.float t x, .float t y]) (j := .floatBinOp t op) hA
      (.floatBinary t op x y z h) (by simp)
  | floatRel t op x y =>
    exact back_of_image (vs := [.float t x, .float t y]) (j := .floatRelOp t op) hA
      (.floatRel t op x y) (by simp)
  | convert op x y h =>
    exact back_convert hA fun op₀ hop => by subst hop; exact ⟨_, .convert op₀ x y h, by simp⟩
  | convertTrap op x err h =>
    exact back_convert hA fun op₀ hop => by subst hop; exact ⟨_, .convertTrap op₀ x err h, rfl⟩

end Silmaril.Proofs.Wasm.Models.V10Lime1Back
