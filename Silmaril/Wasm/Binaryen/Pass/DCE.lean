module

public import Silmaril.Wasm.Binaryen.UniformWf
public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.DCECutTyping
public import Silmaril.Wasm.Binaryen.DCESim
public import Silmaril.Wasm.Binaryen.UniformWfH

@[expose] public section

/-! # P3: Dead-code elimination

Binaryen's `DeadCodeElimination` (`src/passes/DeadCodeElimination.cpp`,
version_133) drops code after an expression of type `unreachable`, and replaces
an expression with an unreachable operand by its operands up to that one. Here
the bottom check is the syntactic `BExpr.isBot` (`Binaryen/Typing.lean`).

The same truncation is what `BinaryenIRWriter` does while writing
(`visitPossibleBlockContents`, `src/wasm-stack.h:293`, and the
`sawUnreachable` loops of `visit`/`visitBlock`), so `irWriter_sound` proves the
writer's skip-after-unreachable sound: it is this pass followed by the exact
lowering.

Typing is preserved by `DceSafe` and `TyRepl`. The observational proof must use
an open-code simulation: `dceL_cut` describes the recursive primitive bottom
cuts in the lowered code. Closed-host `JoinableBot` cannot cross imports, and
the original `joinableBot_seqEquiv` bridge is false; neither supplies the
observational proof.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

mutual
/-- Eliminate dead code in a tree; the result is spliced into the enclosing list. -/
def dceE : BExpr → List BExpr
  | .op i args =>
      let a := dceL args
      if BExpr.listBot a then a else [.op i a]
  | .block bt b => [.block bt (dceL b)]
  | .loop bt b => [.loop bt (dceL b)]
  | .if_ bt c t e =>
      let c' := dceL c
      if BExpr.listBot c' then c' else [.if_ bt c' (dceL t) (dceL e)]
  | .tryTable bt cs b => [.tryTable bt cs (dceL b)]
/-- Eliminate dead code in a list: stop after the first bottom element. -/
def dceL : List BExpr → List BExpr
  | [] => []
  | e :: es =>
      let e' := dceE e
      if BExpr.listBot e' then e' else e' ++ dceL es
end

/-- The pass on a module. -/
def dceModule (m : BModule) : BModule := m.mapBodies dceL

/-! ## A syntactic typing condition for the existing splice algorithm

`DceSafe` checks only the cuts actually made by DCE. A cut must retain a
stack-polymorphic prefix, and may not erase a local initialization. A bottom
block with a fixed Core result type does not satisfy this condition. Import
calls are allowed: this is a typing condition, not a closed-host execution claim.
-/

mutual
/-- The recursive typing condition for DCE on one tree. -/
def DceSafeE : BExpr → Prop
  | .op i args => DceSafe args ∧
      (BExpr.listBot (dceL args) = true →
        EndsInBot (BExpr.lowerList (dceL args)) ∧ initsLocal i = false)
  | .block _ b | .loop _ b | .tryTable _ _ b => DceSafe b
  | .if_ _ c t e => DceSafe c ∧
      if BExpr.listBot (dceL c) then EndsInBot (BExpr.lowerList (dceL c))
      else DceSafe t ∧ DceSafe e
/-- The recursive typing condition for DCE on a sequence. No condition is
imposed on a suffix which DCE does not visit, except its local initializations. -/
def DceSafe : List BExpr → Prop
  | [] => True
  | e :: es => DceSafeE e ∧
      if BExpr.listBot (dceE e) then
        es = [] ∨ (EndsInBot (BExpr.lowerList (dceE e)) ∧
          ∀ i ∈ BExpr.lowerList es, initsLocal i = false)
      else DceSafe es
end

/-- The safety condition admits actual deletion, including a dead suffix that
contains imports. Calls before the cut remain in the retained prefix. -/
theorem dceSafe_unreachable_suffix {es : List BExpr}
    (hs : ∀ i ∈ BExpr.lowerList es, initsLocal i = false) :
    DceSafe (.op .unreachable [] :: es) := by
  refine ⟨?_, ?_⟩
  · simp [DceSafeE, DceSafe, dceL, BExpr.listBot]
  · change es = [] ∨ (EndsInBot [.unreachable] ∧ _)
    exact Or.inr ⟨(endsInBot_singleton _).2 rfl, hs⟩

mutual
/-- Every recursive DCE splice satisfying the syntactic cut condition preserves
all typings in well-formed contexts. -/
theorem dceE_tyRepl : ∀ e : BExpr, DceSafeE e → TyRepl e.lower (BExpr.lowerList (dceE e))
  | .op i args, hs => by
      obtain ⟨ha, hcut⟩ := hs
      have h := TyRepl.append_right (dceL_tyRepl args ha) [i]
      by_cases hb : BExpr.listBot (dceL args) = true
      · obtain ⟨hend, hi⟩ := hcut hb
        simpa [dceE, hb, BExpr.lower] using
          h.trans (TyRepl.drop_bot_suffix hend (by simpa using hi))
      · simpa [dceE, hb, BExpr.lower] using h
  | .block bt b, hs => by
      simpa [dceE, BExpr.lower] using TyRepl.block (dceL_tyRepl b hs) bt
  | .loop bt b, hs => by
      simpa [dceE, BExpr.lower] using TyRepl.loop (dceL_tyRepl b hs) bt
  | .tryTable bt cs b, hs => by
      simpa [dceE, BExpr.lower] using TyRepl.tryTable (dceL_tyRepl b hs) bt cs
  | .if_ bt c t e, hs => by
      obtain ⟨hc, hs⟩ := hs
      by_cases hb : BExpr.listBot (dceL c) = true
      · simp only [hb, ite_true] at hs
        have h := TyRepl.append_right (dceL_tyRepl c hc)
          [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]
        simpa [dceE, hb, BExpr.lower] using
          h.trans (TyRepl.drop_bot_suffix hs (by simp [initsLocal]))
      · simp only [hb, Bool.false_eq_true, ite_false] at hs
        simpa [dceE, hb, BExpr.lower] using
          TyRepl.append (dceL_tyRepl c hc)
            (TyRepl.if_ (dceL_tyRepl t hs.1) (dceL_tyRepl e hs.2) bt)
/-- DCE preserves every typing when every performed cut meets `DceSafe`. -/
theorem dceL_tyRepl : ∀ es : List BExpr, DceSafe es →
    TyRepl (BExpr.lowerList es) (BExpr.lowerList (dceL es))
  | [], _ => TyRepl.refl _
  | e :: es, hs => by
      obtain ⟨he, hs⟩ := hs
      have h := TyRepl.append_right (dceE_tyRepl e he) (BExpr.lowerList es)
      by_cases hb : BExpr.listBot (dceE e) = true
      · simp only [hb, ite_true] at hs
        rcases hs with rfl | ⟨hend, htail⟩
        · simpa [dceL, hb] using h
        · simpa [dceL, hb] using h.trans (TyRepl.drop_bot_suffix hend htail)
      · simp only [hb, Bool.false_eq_true, ite_false] at hs
        simpa [dceL, hb] using TyRepl.append (dceE_tyRepl e he) (dceL_tyRepl es hs)
end

mutual
/-- Safe DCE lowering is generated by primitive bottom cuts and congruence.
No execution or Joinable bridge is used here. -/
theorem dceE_cut : ∀ e : BExpr, DceSafeE e →
    DceCut e.lower (BExpr.lowerList (dceE e))
  | .op i args, hs => by
      obtain ⟨ha, hcut⟩ := hs
      have h := DceCut.append (dceL_cut args ha) (.refl [i])
      by_cases hb : BExpr.listBot (dceL args) = true
      · simpa [dceE, hb, BExpr.lower] using
          h.trans (.cut [i] (hcut hb).1)
      · simpa [dceE, hb, BExpr.lower] using h
  | .block bt b, hs => by
      simpa [dceE, BExpr.lower] using DceCut.block bt (dceL_cut b hs)
  | .loop bt b, hs => by
      simpa [dceE, BExpr.lower] using DceCut.loop bt (dceL_cut b hs)
  | .tryTable bt cs b, hs => by
      simpa [dceE, BExpr.lower] using DceCut.tryTable bt cs (dceL_cut b hs)
  | .if_ bt c t e, hs => by
      obtain ⟨hc, hs⟩ := hs
      by_cases hb : BExpr.listBot (dceL c) = true
      · simp only [hb, ite_true] at hs
        have h := DceCut.append (dceL_cut c hc)
          (.refl [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)])
        simpa [dceE, hb, BExpr.lower] using
          h.trans (.cut [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)] hs)
      · simp only [hb, Bool.false_eq_true, ite_false] at hs
        simpa [dceE, hb, BExpr.lower] using
          DceCut.append (dceL_cut c hc)
            (DceCut.if_ bt (dceL_cut t hs.1) (dceL_cut e hs.2))
/-- The recursive code relation covers every cut made by safe DCE, including
cuts after prefixes containing imports. -/
theorem dceL_cut : ∀ es : List BExpr, DceSafe es →
    DceCut (BExpr.lowerList es) (BExpr.lowerList (dceL es))
  | [], _ => .refl _
  | e :: es, hs => by
      obtain ⟨he, hs⟩ := hs
      have h := DceCut.append (dceE_cut e he) (.refl (BExpr.lowerList es))
      by_cases hb : BExpr.listBot (dceE e) = true
      · simp only [hb, ite_true] at hs
        rcases hs with rfl | ⟨hend, _⟩
        · simpa [dceL, hb] using h
        · simpa [dceL, hb] using h.trans (.cut (BExpr.lowerList es) hend)
      · simp only [hb, Bool.false_eq_true, ite_false] at hs
        simpa [dceL, hb] using DceCut.append (dceE_cut e he) (dceL_cut es hs)
end

/-! ## Closing the `local.set`/`local.tee` gap

Real Binaryen's `dce` deletes dead suffixes that contain `local.set`/`local.tee`.
`DceSafe` forbids that, because the deleted code may initialize a non-defaultable
local claimed by the sequence's instruction type (`⟨ps, xs, rs⟩` with `xs ≠ []`).

That claim never escapes a body: `block`, `loop`, `if` and `try_table` type their
bodies at `⟨t₁, xs, t₂⟩` for some `xs` and forget it (`InstrOk.block`, ...), and a
function body is typed at `.plain [] ts` (`ExprOk`). Every DCE cut propagates to the
end of the innermost enclosing body: a bottom operand list deletes its operator, and
a bottom element of a list deletes the rest of the list. So the widened condition
`DceSafeW` keeps only the stack-polymorphism condition (`EndsInBot`), and typing is
preserved at `.plain` types (`dce_typed_body`). At a type claiming initializations it
is not (`dce_typed_inits_false`: `unreachable; local.set 0` for an unset local).
-/

mutual
/-- The widened recursive typing condition for DCE on one tree: only the retained
prefix of a cut must end in a stack-polymorphic instruction. -/
def DceSafeWE : BExpr → Prop
  | .op _ args => DceSafeW args ∧
      (BExpr.listBot (dceL args) = true → EndsInBot (BExpr.lowerList (dceL args)))
  | .block _ b | .loop _ b | .tryTable _ _ b => DceSafeW b
  | .if_ _ c t e => DceSafeW c ∧
      if BExpr.listBot (dceL c) then EndsInBot (BExpr.lowerList (dceL c))
      else DceSafeW t ∧ DceSafeW e
/-- The widened recursive typing condition for DCE on a sequence. The deleted
suffix is unrestricted. -/
def DceSafeW : List BExpr → Prop
  | [] => True
  | e :: es => DceSafeWE e ∧
      if BExpr.listBot (dceE e) then es = [] ∨ EndsInBot (BExpr.lowerList (dceE e))
      else DceSafeW es
end

mutual
/-- `DceSafeE` is the widened condition plus "no deleted local initialization". -/
theorem DceSafeE.toW : ∀ e : BExpr, DceSafeE e → DceSafeWE e
  | .op _ args, hs => ⟨DceSafe.toW args hs.1, fun hb => (hs.2 hb).1⟩
  | .block _ b, hs => DceSafe.toW b hs
  | .loop _ b, hs => DceSafe.toW b hs
  | .tryTable _ _ b, hs => DceSafe.toW b hs
  | .if_ _ c t e, hs => by
      refine ⟨DceSafe.toW c hs.1, ?_⟩
      have h2 := hs.2
      by_cases hb : BExpr.listBot (dceL c) = true
      · simp only [hb, ite_true] at h2 ⊢
        exact h2
      · simp only [hb, Bool.false_eq_true, ite_false] at h2 ⊢
        exact ⟨DceSafe.toW t h2.1, DceSafe.toW e h2.2⟩
/-- `DceSafe` is the widened condition plus "no deleted local initialization". -/
theorem DceSafe.toW : ∀ es : List BExpr, DceSafe es → DceSafeW es
  | [], _ => trivial
  | e :: es, hs => by
      refine ⟨DceSafeE.toW e hs.1, ?_⟩
      have h2 := hs.2
      by_cases hb : BExpr.listBot (dceE e) = true
      · simp only [hb, ite_true] at h2 ⊢
        rcases h2 with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      · simp only [hb, Bool.false_eq_true, ite_false] at h2 ⊢
        exact DceSafe.toW es h2
end

/-- Real `dce` on a dead suffix, including `local.set`/`local.tee`: the widened
condition admits every suffix after `unreachable`. -/
theorem dceSafeW_unreachable_suffix (es : List BExpr) :
    DceSafeW (.op .unreachable [] :: es) := by
  refine ⟨?_, ?_⟩
  · simp [DceSafeWE, DceSafeW, dceL, BExpr.listBot]
  · change es = [] ∨ EndsInBot [.unreachable]
    exact Or.inr ((endsInBot_singleton _).2 rfl)

mutual
/-- Widened DCE lowering is generated by primitive bottom cuts and congruence. -/
theorem dceE_cutW : ∀ e : BExpr, DceSafeWE e →
    DceCut e.lower (BExpr.lowerList (dceE e))
  | .op i args, hs => by
      obtain ⟨ha, hcut⟩ := hs
      have h := DceCut.append (dceL_cutW args ha) (.refl [i])
      by_cases hb : BExpr.listBot (dceL args) = true
      · simpa [dceE, hb, BExpr.lower] using
          h.trans (.cut [i] (hcut hb))
      · simpa [dceE, hb, BExpr.lower] using h
  | .block bt b, hs => by
      simpa [dceE, BExpr.lower] using DceCut.block bt (dceL_cutW b hs)
  | .loop bt b, hs => by
      simpa [dceE, BExpr.lower] using DceCut.loop bt (dceL_cutW b hs)
  | .tryTable bt cs b, hs => by
      simpa [dceE, BExpr.lower] using DceCut.tryTable bt cs (dceL_cutW b hs)
  | .if_ bt c t e, hs => by
      obtain ⟨hc, hs⟩ := hs
      by_cases hb : BExpr.listBot (dceL c) = true
      · simp only [hb, ite_true] at hs
        have h := DceCut.append (dceL_cutW c hc)
          (.refl [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)])
        simpa [dceE, hb, BExpr.lower] using
          h.trans (.cut [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)] hs)
      · simp only [hb, Bool.false_eq_true, ite_false] at hs
        simpa [dceE, hb, BExpr.lower] using
          DceCut.append (dceL_cutW c hc)
            (DceCut.if_ bt (dceL_cutW t hs.1) (dceL_cutW e hs.2))
/-- The recursive code relation covers every cut made by widened DCE. -/
theorem dceL_cutW : ∀ es : List BExpr, DceSafeW es →
    DceCut (BExpr.lowerList es) (BExpr.lowerList (dceL es))
  | [], _ => .refl _
  | e :: es, hs => by
      obtain ⟨he, hs⟩ := hs
      have h := DceCut.append (dceE_cutW e he) (.refl (BExpr.lowerList es))
      by_cases hb : BExpr.listBot (dceE e) = true
      · simp only [hb, ite_true] at hs
        rcases hs with rfl | hend
        · simpa [dceL, hb] using h
        · simpa [dceL, hb] using h.trans (.cut (BExpr.lowerList es) hend)
      · simp only [hb, Bool.false_eq_true, ite_false] at hs
        simpa [dceL, hb] using DceCut.append (dceE_cutW e he) (dceL_cutW es hs)
end

/-! ### Typing of widened cuts

`TyReplP X Y`: every typing `⟨ps, xs, rs⟩` of `X` gives the initialization-free
typing `.plain ps rs` of `Y`. A cut gives only this weaker replacement; code without
a top-level cut keeps the full typing (`TyRepl`), because the bodies of structured
instructions forget their initialization claims.
-/

/-- `Y` replaces `X` up to forgetting initialization claims. -/
def TyReplP (X Y : List Instr) : Prop :=
  ∀ (C : Context) (ps rs : List CValType) (xs : List Nat), C.Wf →
    InstrsOk C X ⟨ps, xs, rs⟩ → InstrsOk C Y (.plain ps rs)

/-- Forgetting initialization claims is a subsumption. -/
theorem instrsOk_plain {C : Context} {X : List Instr} {ps rs : List CValType} {xs : List Nat}
    (hC : C.Wf) (h : InstrsOk C X ⟨ps, xs, rs⟩) : InstrsOk C X (.plain ps rs) := by
  have hr := InstrsOk.regular hC h
  exact .sub h ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun x hx _ => by simp at hx⟩
    ⟨hr.1, hr.2.1, by simp⟩

theorem TyRepl.toP {X Y : List Instr} (h : TyRepl X Y) : TyReplP X Y :=
  fun C _ _ _ hC hX => instrsOk_plain hC (h C _ hC hX)

/-- A cut after a stack-polymorphic retained prefix. -/
theorem TyReplP.cut {A A' : List Instr} (h : TyReplP A A') (hb : EndsInBot A')
    (B : List Instr) : TyReplP (A ++ B) A' := by
  intro C ps rs xs hC hX
  obtain ⟨m, xs₁, xs₂, h₁, -, -⟩ := InstrsOk.split hC hX rfl
  have hr := InstrsOk.regular hC hX
  exact hb.retype hC (h C ps m xs₁ hC h₁) ⟨hr.1, hr.2.1, by simp⟩

/-- Concatenation with an exactly replaced left part. -/
theorem TyReplP.append_exact {E E' S S' : List Instr} (hE : TyRepl E E') (hS : TyReplP S S') :
    TyReplP (E ++ S) (E' ++ S') := by
  intro C ps rs xs hC hX
  obtain ⟨m, xs₁, xs₂, h₁, h₂, -⟩ := InstrsOk.split hC hX rfl
  have r₁ := InstrsOk.regular hC h₁
  exact instrsOk_plain hC
    (InstrsOk.seq (hE C _ hC h₁) r₁.2.2 (hS _ m rs xs₂ (hC.initLocals _) h₂))

theorem TyRepl.blockP {B B' : List Instr} (h : TyReplP B B') (bt : BlockType) :
    TyRepl [.block bt B] [.block bt B'] :=
  TyRepl.of_instr fun C it hC hi => by
    cases hi with
    | block hbt hb =>
      exact .instr (.block hbt (h _ _ _ _ (wf_withLabel hC (hbt.regular hC).2) hb))
    | _ => rename_i h; cases h

theorem TyRepl.loopP {B B' : List Instr} (h : TyReplP B B') (bt : BlockType) :
    TyRepl [.loop bt B] [.loop bt B'] :=
  TyRepl.of_instr fun C it hC hi => by
    cases hi with
    | loop hbt hb =>
      exact .instr (.loop hbt (h _ _ _ _ (wf_withLabel hC (hbt.regular hC).1) hb))
    | _ => rename_i h; cases h

theorem TyRepl.ifP {B₁ B₁' B₂ B₂' : List Instr} (h₁ : TyReplP B₁ B₁') (h₂ : TyReplP B₂ B₂')
    (bt : BlockType) : TyRepl [.if_ bt B₁ B₂] [.if_ bt B₁' B₂'] :=
  TyRepl.of_instr fun C it hC hi => by
    cases hi with
    | if_ hbt hb₁ hb₂ =>
      have hW := wf_withLabel hC (hbt.regular hC).2
      exact .instr (.if_ hbt (h₁ _ _ _ _ hW hb₁) (h₂ _ _ _ _ hW hb₂))
    | _ => rename_i h; cases h

theorem TyRepl.tryTableP {B B' : List Instr} (h : TyReplP B B') (bt : BlockType)
    (cs : List Catch) : TyRepl [.tryTable bt cs B] [.tryTable bt cs B'] :=
  TyRepl.of_instr fun C it hC hi => by
    cases hi with
    | tryTable hbt hb hc =>
      exact .instr (.tryTable hbt (h _ _ _ _ (wf_withLabel hC (hbt.regular hC).2) hb) hc)
    | _ => rename_i h; cases h

theorem dce_listBot_append (a b : List BExpr) :
    BExpr.listBot (a ++ b) = (BExpr.listBot a || BExpr.listBot b) := by
  induction a with
  | nil => simp [BExpr.listBot]
  | cons e es ih => simp [BExpr.listBot, ih, Bool.or_assoc]

mutual
/-- Typing of widened DCE on one tree: exact without a top-level cut. -/
theorem dceE_tyP : ∀ e : BExpr, DceSafeWE e →
    TyReplP e.lower (BExpr.lowerList (dceE e)) ∧
      (BExpr.listBot (dceE e) = false → TyRepl e.lower (BExpr.lowerList (dceE e)))
  | .op i args, hs => by
      obtain ⟨ha, hcut⟩ := hs
      have hA := dceL_tyP args ha
      by_cases hb : BExpr.listBot (dceL args) = true
      · rw [show dceE (.op i args) = dceL args by simp [dceE, hb]]
        refine ⟨?_, fun h => absurd (hb.symm.trans h) (by decide)⟩
        show TyReplP (BExpr.lowerList args ++ [i]) _
        exact hA.1.cut (hcut hb) [i]
      · rw [show dceE (.op i args) = [.op i (dceL args)] by simp [dceE, hb]]
        have h : TyRepl (BExpr.op i args).lower (BExpr.lowerList [.op i (dceL args)]) := by
          simpa [BExpr.lower] using TyRepl.append_right (hA.2 (by simpa using hb)) [i]
        exact ⟨h.toP, fun _ => h⟩
  | .block bt b, hs => by
      have h : TyRepl (BExpr.block bt b).lower (BExpr.lowerList (dceE (.block bt b))) := by
        simpa [dceE, BExpr.lower] using TyRepl.blockP (dceL_tyP b hs).1 bt
      exact ⟨h.toP, fun _ => h⟩
  | .loop bt b, hs => by
      have h : TyRepl (BExpr.loop bt b).lower (BExpr.lowerList (dceE (.loop bt b))) := by
        simpa [dceE, BExpr.lower] using TyRepl.loopP (dceL_tyP b hs).1 bt
      exact ⟨h.toP, fun _ => h⟩
  | .tryTable bt cs b, hs => by
      have h : TyRepl (BExpr.tryTable bt cs b).lower
          (BExpr.lowerList (dceE (.tryTable bt cs b))) := by
        simpa [dceE, BExpr.lower] using TyRepl.tryTableP (dceL_tyP b hs).1 bt cs
      exact ⟨h.toP, fun _ => h⟩
  | .if_ bt c t e, hs => by
      obtain ⟨hc, hs⟩ := hs
      have hC := dceL_tyP c hc
      by_cases hb : BExpr.listBot (dceL c) = true
      · simp only [hb, ite_true] at hs
        rw [show dceE (.if_ bt c t e) = dceL c by simp [dceE, hb]]
        refine ⟨?_, fun h => absurd (hb.symm.trans h) (by decide)⟩
        show TyReplP (BExpr.lowerList c ++ [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]) _
        exact hC.1.cut hs _
      · simp only [hb, Bool.false_eq_true, ite_false] at hs
        rw [show dceE (.if_ bt c t e) = [.if_ bt (dceL c) (dceL t) (dceL e)] by simp [dceE, hb]]
        have h : TyRepl (BExpr.if_ bt c t e).lower
            (BExpr.lowerList [.if_ bt (dceL c) (dceL t) (dceL e)]) := by
          simpa [BExpr.lower] using TyRepl.append (hC.2 (by simpa using hb))
            (TyRepl.ifP (dceL_tyP t hs.1).1 (dceL_tyP e hs.2).1 bt)
        exact ⟨h.toP, fun _ => h⟩
/-- Typing of widened DCE on a sequence: exact without a top-level cut. -/
theorem dceL_tyP : ∀ es : List BExpr, DceSafeW es →
    TyReplP (BExpr.lowerList es) (BExpr.lowerList (dceL es)) ∧
      (BExpr.listBot (dceL es) = false →
        TyRepl (BExpr.lowerList es) (BExpr.lowerList (dceL es)))
  | [], _ => ⟨(TyRepl.refl _).toP, fun _ => TyRepl.refl _⟩
  | e :: es, hs => by
      obtain ⟨he, hs⟩ := hs
      have hE := dceE_tyP e he
      by_cases hb : BExpr.listBot (dceE e) = true
      · simp only [hb, ite_true] at hs
        rw [show dceL (e :: es) = dceE e by simp [dceL, hb]]
        refine ⟨?_, fun h => absurd (hb.symm.trans h) (by decide)⟩
        rcases hs with rfl | hend
        · simpa using hE.1
        · show TyReplP (e.lower ++ BExpr.lowerList es) _
          exact hE.1.cut hend _
      · simp only [hb, Bool.false_eq_true, ite_false] at hs
        rw [show dceL (e :: es) = dceE e ++ dceL es by simp [dceL, hb]]
        have hS := dceL_tyP es hs
        have hE2 := hE.2 (by simpa using hb)
        show TyReplP (e.lower ++ BExpr.lowerList es) (BExpr.lowerList (dceE e ++ dceL es)) ∧
          (BExpr.listBot (dceE e ++ dceL es) = false →
            TyRepl (e.lower ++ BExpr.lowerList es) (BExpr.lowerList (dceE e ++ dceL es)))
        rw [BExpr.lowerList_append]
        refine ⟨TyReplP.append_exact hE2 hS.1, fun h => TyRepl.append hE2 (hS.2 ?_)⟩
        rw [dce_listBot_append] at h
        simp only [Bool.or_eq_false_iff] at h
        exact h.2
end

/-- **Widened DCE preserves body typings.** Every typing `⟨ps, xs, rs⟩` of the
input gives the initialization-free typing `.plain ps rs` of the output. -/
theorem dce_typed_body {C : Context} {ps rs : List CValType} {xs : List Nat}
    {es : List BExpr} (hC : C.Wf) (hs : DceSafeW es) (h : SeqOk C es ⟨ps, xs, rs⟩) :
    SeqOk C (dceL es) (.plain ps rs) :=
  (dceL_tyP es hs).1 C ps rs xs hC h

/-- One unset `i32` local. -/
private def dceUnsetCtx : Context := { locals := [⟨.unset, .num (.int .i32)⟩] }

private theorem dceUnsetCtx_wf : dceUnsetCtx.Wf :=
  ⟨by simp [TypeCtx.Ok, dceUnsetCtx], by simp [dceUnsetCtx], by simp [dceUnsetCtx],
    by simp [dceUnsetCtx], by simp [dceUnsetCtx], by simp [dceUnsetCtx, TyOk.num'],
    by simp [dceUnsetCtx], by simp [dceUnsetCtx], by simp [dceUnsetCtx]⟩

/-- The `local.set` gap is genuine at initialization-claiming types: deleting
`local.set 0` after `unreachable` loses the claim that the unset local `0` is
initialized. -/
theorem dce_typed_inits_false :
    ¬ ∀ (C : Context) (it : InstrType) (es : List BExpr), C.Wf → DceSafeW es →
      SeqOk C es it → SeqOk C (dceL es) it := by
  intro hall
  have ht : SeqOk dceUnsetCtx [.op .unreachable [], .op (.localSet ⟨⟨0, by decide⟩⟩) []]
      ⟨[], [0], []⟩ := by
    show InstrsOk dceUnsetCtx [.unreachable, .localSet ⟨⟨0, by decide⟩⟩] _
    have hu : InstrOk dceUnsetCtx .unreachable (.plain [] [.num (.int .i32)]) :=
      .parametric (.unreachable ⟨by simp [ResultOk], by simp [ResultOk, TyOk.num'], by simp⟩)
    have hs : InstrsOk dceUnsetCtx [.localSet ⟨⟨0, by decide⟩⟩] ⟨[.num (.int .i32)], [0], []⟩ :=
      .instr (.variable (.localSet (i := .unset) rfl))
    simpa using InstrsOk.cons (xs₁ := []) hu (by simp) hs
  have h := hall dceUnsetCtx _ _ dceUnsetCtx_wf (dceSafeW_unreachable_suffix _) ht
  have he : dceL [.op .unreachable [], .op (.localSet ⟨⟨0, by decide⟩⟩) []] =
      [.op .unreachable []] := by
    simp [dceL, dceE, BExpr.listBot, BExpr.isBot, botInstr]
  rw [he] at h
  change InstrsOk dceUnsetCtx [.unreachable] _ at h
  obtain ⟨ts, it₀, -, hi, hsub⟩ := single_inv' dceUnsetCtx_wf h
  have h0 := InstrOk.inits_nil hi rfl
  obtain ⟨t, ht⟩ := hsub.2.2 0 (by simp) (by simp [h0])
  simp [dceUnsetCtx] at ht

/-- The trap-cut base case of the open simulation, under an arbitrary host.
Erasing the dead suffix may remove a trap-bubbling step, so the eventual
simulation needs stuttering for administrative erasure. -/
theorem dce_unreachable_steps {H : Type} {P : Profile} (host : HostSemantics H)
    (s : Store H) (f : Frame) (vs : List Val) (junk : List Admin) :
    Steps P host ⟨s, f, vals vs ++ [.plain .unreachable] ++ junk⟩ ⟨s, f, [.trap]⟩ := by
  by_cases hne : vs ≠ [] ∨ junk ≠ []
  · exact (Step.ctxtInstrs (Step.parametric .unreachable) hne).steps.trans
      (Step.trapInstrs hne).steps
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    exact (Step.parametric .unreachable).steps

-- FLAG(statement-change): add `C.Wf` and the syntactic `DceSafe es` condition.
-- The original is refuted below by `dce_typed_original_false`: semantic bottom
-- need not be stack polymorphic. Deleted code must also preserve local inits.
/-- DCE preserves typing for syntactically safe cuts. -/
theorem dce_typed {C : Context} {it : InstrType} {es : List BExpr}
    (hC : C.Wf) (hs : DceSafe es) (h : SeqOk C es it) :
    SeqOk C (dceL es) it :=
  dceL_tyRepl es hs C it hC h

-- FLAG(statement-change): `dce_joinableBot` (closed-host joinability up to a
-- control transfer, on the call-free fragment) is replaced. `dce_sound` no longer
-- goes through `JoinableBot`: it is proved by the code simulation (`DCESim.lean`).
-- The replacement is the local, open-host fact that the tooling gives: from every
-- configuration, under every code-parametric host, the code and its DCE have the
-- same behaviours. The original without `hfree` is refuted by
-- `DCEJoinableCex.dce_joinableBot_original_false` (an import call).
/-- **Local DCE equivalence.** From every configuration, for every
code-parametric host, safe DCE preserves the behaviours of the code. -/
theorem dce_codeConfig_behaviours_eq {P : Profile} {H : Type} {host : HostSemantics H}
    (hhost : Sim.HostParametric host) {es : List BExpr} (hs : DceSafeW es) (s : Store H)
    (f : Frame) (vs : List Val) :
    behavioursOf P host (codeConfig s f vs (dceL es)) =
      behavioursOf P host (codeConfig s f vs es) := by
  have hrel : Sim.InstrsRel Sim.dceBI (BExpr.lowerList (dceL es)) (BExpr.lowerList es) := by
    have := (dceL_cutW es hs).instrsRel.flip
    rwa [Sim.dceBI_flip] at this
  have hF' : ∀ fi gi : FuncInst H, Sim.FuncRel Sim.dceBI gi fi →
      Sim.FuncRel (fun a b => Sim.dceBI b a) fi gi :=
    fun _ _ h => h.flip
  have hhost' : Sim.HostRespects (fun g f : FuncInst H => Sim.FuncRel Sim.dceBI f g) host :=
    hhost.respects (fun f => Sim.FuncRel.refl f)
  have hB' : Sim.BaseSim P host (fun g f : FuncInst H => Sim.FuncRel Sim.dceBI f g)
      (fun a b => Sim.dceBI b a) (fun a b => Sim.dceB b a) := by
    rw [Sim.dceBI_flip, Sim.dceB_flip]
    exact Sim.dceBaseSim (fun _ _ h => h.dce_symm) hhost'
  have hhost₀ : Sim.HostRespects (Sim.FuncRel Sim.dceBI) host :=
    hhost.respects (fun f => Sim.FuncRel.refl f)
  exact Sim.closure_behavioursOf_eq (F := Sim.FuncRel Sim.dceBI) (BI := Sim.dceBI)
    (B := Sim.dceB) (fun _ _ h => h) hF' hhost₀ hhost' (Sim.dceBaseSim (fun _ _ h => h) hhost₀)
    hB' ⟨Sim.StoreRel.refl (fun f => Sim.FuncRel.refl f) s, rfl,
      .append (Sim.AdminsRel.vals vs) (.src hrel)⟩

-- FLAG(statement-change): require `C.Wf` and `DceSafe es`, as for `dce_typed`.
-- Imports remain permitted; the needed proof must match their interactions,
-- rather than attempt to cross them using closed-host `JoinableBot`.
/-- **DCE is an observational equivalence for safe cuts.** Derived from the code
simulation (`dceCut_seqEquivH`) and `dce_typed`. -/
theorem dce_sound {o : GrowKind → Nat → Nat → Nat → Bool} {C : Context} {it : InstrType}
    {es : List BExpr} (hC : C.Wf) (hs : DceSafe es) (h : SeqOk C es it) :
    SeqEquiv (· = ·) (Profile.deterministic o) C it (dceL es) es :=
  (dceCut_seqEquivH (dceL_cut es hs) h (dce_typed hC hs h)).toSeqEquiv

/-- **Widened DCE is an observational equivalence at body types.** Dead suffixes may
contain `local.set`/`local.tee`; the typing is then one without initialization
claims (`.plain`), which is how every body (block, loop, `if` arm, `try_table`,
function) is typed. -/
theorem dce_sound_body {P : Profile} {C : Context} {ps rs : List CValType} {es : List BExpr}
    (hC : C.Wf) (hs : DceSafeW es) (h : SeqOk C es (.plain ps rs)) :
    SeqEquivH HostsP (· = ·) P C (.plain ps rs) (dceL es) es :=
  dceCut_seqEquivH (dceL_cutW es hs) h (dce_typed_body hC hs h)

/-- Every defined body meets the recursive syntactic DCE typing condition. -/
def DceSafeModule (m : BModule) : Prop := ∀ f ∈ m.funcs, DceSafe f.body

/-- Safe DCE cuts preserve module validity, without any semantic bridge. -/
theorem dceModule_ok {m : BModule} (hm : m.Ok) (hs : DceSafeModule m) :
    (dceModule m).Ok :=
  BodyTransform.ok_of_rel hm rfl (by simp [dceModule, BModule.mapBodies]) fun i hi _ => by
    simp only [dceModule, BModule.mapBodies, List.getElem_map]
    exact ⟨rfl, rfl, fun C ts hC hb => dce_typed hC (hs _ (List.getElem_mem hi)) hb⟩

/-- Every defined body meets the widened DCE typing condition. -/
def DceSafeModuleW (m : BModule) : Prop := ∀ f ∈ m.funcs, DceSafeW f.body

theorem DceSafeModule.toW {m : BModule} (h : DceSafeModule m) : DceSafeModuleW m :=
  fun f hf => DceSafe.toW _ (h f hf)

/-- Widened DCE preserves module validity. -/
theorem dceModule_okW {m : BModule} (hm : m.Ok) (hs : DceSafeModuleW m) :
    (dceModule m).Ok :=
  BodyTransform.ok_of_rel hm rfl (by simp [dceModule, BModule.mapBodies]) fun i hi _ => by
    simp only [dceModule, BModule.mapBodies, List.getElem_map]
    exact ⟨rfl, rfl, fun C ts hC hb => dce_typed_body hC (hs _ (List.getElem_mem hi)) hb⟩

/-- **Widened DCE on modules**, for every code-parametric host (in particular every
`HostRespectsCode` host and every typed one). Dead `local.set`/`local.tee` are
deleted, as real Binaryen does. -/
theorem dce_module_soundW {P : Profile} {m : BModule} (hm : m.Ok) (hs : DceSafeModuleW m)
    {H : Type} (host : HostSemantics H) (hhost : Sim.HostParametric host) :
    ExportEquiv (· = ·) P host (dceModule m).lower m.lower :=
  BodyTransform.mapBodies_exportEquivH (Q := HostsP) hm
    (fun f hf _ _ hC hb => dce_sound_body hC (hs f hf) hb) host hhost

-- FLAG(statement-change): the original safe-cut API now retains every outcome
-- at the same arbitrary profile, using the wider open-code simulation above.
/-- Safe DCE preserves exact export equivalence at every numerical profile.
The original cut and host conditions suffice; numerical determinism is unnecessary. -/
theorem dce_module_sound {P : Profile} {m : BModule} (hm : m.Ok)
    (hs : DceSafeModule m)
    {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    ExportEquiv (· = ·) P host (dceModule m).lower m.lower :=
  dce_module_soundW hm hs.toW host hhost.hostParametric

/-- The previous grow-oracle specialization, retained for clients selecting an
oracle explicitly. The general theorem is `dce_module_sound`. -/
theorem dce_module_sound_deterministic {o : GrowKind → Nat → Nat → Nat → Bool}
    {m : BModule} (hm : m.Ok) (hs : DceSafeModule m)
    {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host (dceModule m).lower m.lower :=
  dce_module_sound hm hs host hhost

/-- `BinaryenIRWriter`'s emission: DCE, then the exact lowering. -/
def irWrite (m : BModule) : Module := (dceModule m).lower

-- FLAG(statement-change): propagate the input-body safety condition of DCE.
/-- The writer's skip-after-unreachable preserves every outcome at the same
arbitrary numerical profile, for the original safe cuts and hosts. -/
theorem irWriter_sound {P : Profile} {m : BModule} (hm : m.Ok)
    (hs : DceSafeModule m)
    {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    ExportEquiv (· = ·) P host (irWrite m) m.lower :=
  dce_module_sound hm hs host hhost

/-- The writer also supports the widened cuts (including dead local writes)
and every code-parametric host, independently of numerical determinism. -/
theorem irWriter_soundW {P : Profile} {m : BModule} (hm : m.Ok)
    (hs : DceSafeModuleW m)
    {H : Type} (host : HostSemantics H) (hhost : Sim.HostParametric host) :
    ExportEquiv (· = ·) P host (irWrite m) m.lower :=
  dce_module_soundW hm hs host hhost

/-- The original oracle-specialized writer contract. -/
theorem irWriter_sound_deterministic {o : GrowKind → Nat → Nat → Nat → Bool}
    {m : BModule} (hm : m.Ok) (hs : DceSafeModule m)
    {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host (irWrite m) m.lower :=
  irWriter_sound hm hs host hhost

/-! ## Typing obstruction for unrestricted folded operands

A bottom block retains its declared Core result type. Splicing its enclosing
constant removes that constant's result, although the original sequence is typed.
This refutes the original unrestricted `dce_typed` contract independently of the
open semantic proofs above; see `Silmaril.Wasm.Binaryen.Equiv` for repair options.
-/

private def dceTypingBlock : BExpr := .block .empty [.op .unreachable []]

private def dceTypingWitness : List BExpr := [.op (.intConst .i32 0) [dceTypingBlock]]

/-- The reviewer's fixed-result bottom-block witness is rejected by the
syntactic cut condition, independently of its typing counterexample. -/
theorem dceTypingWitness_not_safe :
    ¬ DceSafe [.op (.intConst .i32 0) [.block .empty [.op .unreachable []]]] := by
  change ¬ DceSafe dceTypingWitness
  have hl : instrLabels .unreachable = [] := by rw [instrLabels.eq_def]
  simp [DceSafe, DceSafeE, dceTypingWitness, dceTypingBlock, dceL, dceE,
    BExpr.listBot, BExpr.isBot, botInstr, BExpr.labelsList, instrsLabels, hl,
    initsLocal, BExpr.lower]

/-- DCE's bottom-operand splice does not preserve typing on all folded trees. -/
theorem dce_typed_original_false :
    ¬ ∀ (C : Context) (it : InstrType) (es : List BExpr), SeqOk C es it →
      SeqOk C (dceL es) it := by
  intro hall
  have hb : InstrOk ({} : Context) (.block .empty [.unreachable]) (.plain [] []) :=
    .block .empty (.instr (.parametric (.unreachable
      ⟨by simp [ResultOk], by simp [ResultOk], by simp⟩)))
  have ht : SeqOk {} dceTypingWitness (.plain [] [.num (.int .i32)]) := by
    change InstrsOk {} [.block .empty [.unreachable], .intConst .i32 0] _
    exact InstrsOk.cons hb (by simp) (.instr (.numeric (.intConst .i32 0)))
  have hl : instrLabels .unreachable = [] := by rw [instrLabels.eq_def]
  have he : dceL dceTypingWitness = [dceTypingBlock] := by
    simp [dceTypingWitness, dceTypingBlock, dceL, dceE, BExpr.listBot, BExpr.isBot,
      botInstr, BExpr.labelsList, instrsLabels, hl]
  have h := hall {} _ _ ht
  rw [he] at h
  change InstrsOk {} [.block .empty [.unreachable]] _ at h
  obtain ⟨k, it₀, hi, e1, e2⟩ := single_len wf_emptyContext h
  obtain ⟨t₁, t₂, hbt, rfl⟩ := instrOk_block_inv hi
  cases hbt
  simp at e1 e2
  omega

/-- The unrestricted DCE equivalence is false already in its typing component.
This does not rely on the open Joinable bridges or any execution assumption. -/
theorem dce_sound_original_false :
    ¬ ∀ (o : GrowKind → Nat → Nat → Nat → Bool) (C : Context) (it : InstrType)
      (es : List BExpr), SeqOk C es it →
      SeqEquiv (· = ·) (Profile.deterministic o) C it (dceL es) es := by
  intro hall
  apply dce_typed_original_false
  intro C it es ht
  exact (hall (fun _ _ _ _ => true) C it es ht).1.1

end Silmaril.Wasm.Binaryen

#print axioms Silmaril.Wasm.Binaryen.dce_typed
#print axioms Silmaril.Wasm.Binaryen.dceModule_ok
#print axioms Silmaril.Wasm.Binaryen.dce_module_sound
#print axioms Silmaril.Wasm.Binaryen.dce_module_soundW
#print axioms Silmaril.Wasm.Binaryen.irWriter_sound
