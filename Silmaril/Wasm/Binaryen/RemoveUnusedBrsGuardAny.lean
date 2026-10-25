module

public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSound
public import Silmaril.Wasm.Binaryen.EffectRank

@[expose] public section

/-! # Guard inversion at every numerical profile

The original block enters its runtime label while the transformed side stutters.
The body-aware rank pays for this entry. Both sides then read the local in the
same frame, so every later runtime pair remembers the same value without any
frame-dependent relation or numerical determinism hypothesis.
-/

namespace Silmaril.Wasm.Binaryen.GuardSim

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

set_option hygiene false in
local macro "fam_no" : tactic => `(tactic| first
  | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
  | (exfalso; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]))

/-- An inert first active instruction prevents every label-bubbling rule. -/
private theorem head_label_inert {s : Store H} {f : Frame} {args W : List Val}
    {n : Nat} {cont : List Instr} {e : Admin} {rest body : List Admin} {cfg : Config H}
    (he : e.val? = none) (hbr : ∀ l, e ≠ .plain (.br l)) (hret : e ≠ .plain .return_)
    (hrc : ¬ e.IsReturnCallRef) (htr : e ≠ .trap) (hth : e ≠ .plain .throwRef)
    (hb : body = vals W ++ e :: rest) (h : Det.Head P s f args (.label n cont body) cfg) :
    args = [] ∧ ∃ s' f' body', Step P closedHost ⟨s, f, body⟩ ⟨s', f', body'⟩ ∧
      cfg = ⟨s', f', [.label n cont body']⟩ := by
  have hno : ∀ {us k j}, Exit k → body = vals us ++ k ++ j → False := by
    intro us k j hk hh
    exact not_exit he hbr hret hrc htr hth hk (hb.symm.trans hh)
  cases h with
  | ctxtLabel hs => exact ⟨rfl, _, _, _, hs, rfl⟩
  | labelVals hv =>
    have hv' := Det.mem_vals (by rw [← hv, hb]; simp : e ∈ vals _)
    exact (hv' he).elim
  | brLabelZero hv =>
    rename_i vs' vs l r hl hn
    exact (hno (us := vs' ++ vs) (.br _) (by simpa only [vals_append, List.append_assoc] using hv)).elim
  | brLabelSucc hv => exact (hno (.br _) (by simpa using hv)).elim
  | returnCallRefLabel hv hc => exact (hno (.returnCallRef hc) hv).elim
  | returnLabel hv => exact (hno .return_ hv).elim
  | throwRefLabel => exact (hno (us := []) (j := []) (.throw _) rfl).elim
  | trapLabel => exact (hno (us := []) (j := []) .trap rfl).elim
  | _ => fam_no

private theorem head_brIf {s : Store H} {f : Frame} {args : List Val}
    {l : LabelIdx} {cfg : Config H} (h : Det.Head P s f args (.plain (.brIf l)) cfg) :
    ∃ c : BitVec 32, args = [Val.i32 c] ∧
      cfg = ⟨s, f, if c = 0 then [] else [.plain (.br l)]⟩ := by
  cases h with
  | brIfTrue hc => exact ⟨_, rfl, ite_eq_right hc ▸ rfl⟩
  | brIfFalse hc => exact ⟨_, rfl, ite_eq_left hc ▸ rfl⟩
  | _ => fam_no

private theorem label_step_inert {s : Store H} {f : Frame} {V W : List Val}
    {n : Nat} {cont : List Instr} {e : Admin} {rest tail : List Admin} {cfg : Config H}
    (he : e.val? = none) (hbr : ∀ l, e ≠ .plain (.br l)) (hret : e ≠ .plain .return_)
    (hrc : ¬ e.IsReturnCallRef) (htr : e ≠ .trap) (hth : e ≠ .plain .throwRef)
    (h : Step P closedHost ⟨s, f, vals V ++ [.label n cont (vals W ++ e :: rest)] ++ tail⟩ cfg) :
    ∃ s' f' body', Step P closedHost ⟨s, f, vals W ++ e :: rest⟩ ⟨s', f', body'⟩ ∧
      cfg = ⟨s', f', vals V ++ [.label n cont body'] ++ tail⟩ := by
  obtain ⟨pre, args, c₀, hV, hh, hc⟩ := head_inv (W := V) (e := .label n cont (vals W ++ e :: rest)) rfl (by simp) (by simp) (by simpa using h)
  obtain ⟨rfl, s', f', b', hb, rfl⟩ := head_label_inert he hbr hret hrc htr hth rfl hh
  simp only [List.append_nil] at hV
  subst pre
  exact ⟨s', f', b', hb, hc⟩

private theorem head_label_br_zero {s : Store H} {f : Frame} {args : List Val}
    {l : LabelIdx} {R body : List Admin} {cfg : Config H} (hl : l.toNat = 0)
    (hb : body = .plain (.br l) :: R)
    (h : Det.Head P s f args (.label 0 [] body) cfg) :
    args = [] ∧ cfg = ⟨s, f, []⟩ := by
  cases h with
  | ctxtLabel hs =>
    rw [hb] at hs
    exact (Det.not_step_blocked hs (W := []) (e := .plain (.br l)) (rest := R)
      (by simp [Det.fnv_cons_of_none (a := .plain (.br l)) rfl]) (Or.inl ⟨l, rfl⟩)).elim
  | labelVals hv =>
    have hv' := Det.mem_vals (by rw [← hv, hb]; simp : .plain (.br l) ∈ vals _)
    exact (hv' rfl).elim
  | brLabelZero hv hz hn =>
    have he : _ = ([] : List Val) := List.length_eq_zero_iff.mp hn
    subst he
    exact ⟨rfl, by simp [vals, expression]⟩
  | brLabelSucc hv hs =>
    have hc := congrArg Det.fnv (hb.symm.trans hv)
    simp [Det.fnv_cons_of_none (a := .plain (.br l)) rfl,
      Det.fnv_cons_of_none (a := .plain (.br _)) rfl] at hc
    obtain ⟨_, he, _⟩ := hc
    cases he
    omega
  | returnCallRefLabel hv hc =>
    have hi := vals_append_cons_inj (vs := []) (a := .plain (.br l)) rfl
      (Det.IsReturnCallRef.val_none hc) (by simpa [hb] using hv)
    exfalso
    simp [← hi.2.1, Admin.IsReturnCallRef] at hc
  | returnLabel hv =>
    have hi := vals_append_cons_inj (vs := []) (a := .plain (.br l)) rfl rfl (by simpa [hb] using hv)
    cases hi.2.1
  | throwRefLabel => simp at hb
  | trapLabel => simp at hb
  | _ => fam_no

/-- The transformed test selects the same empty-typed block as the guard. -/
private theorem finish_guard (s : Store H) (f : Frame) (c : BitVec 32) (R' : List Instr) :
    Relation.TransGen (Step P closedHost)
      ⟨s, f, [constI32 c, .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]⟩
      ⟨s, f, [.label 0 [] (expression (if c = 0 then R' else []))]⟩ := by
  have htest : Step P closedHost
      ⟨s, f, [constI32 c, .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]⟩
      ⟨s, f, [constI32 (intTestOp .i32 .eqz c), .plain (.if_ .empty R' [])]⟩ := by
    simpa [constI32, Val.i32, Val.toAdmin] using Step.append_right
      (Step.numeric (P := P) (host := closedHost) (s := s) (f := f)
        (NumericStep.intTestOp (t := .i32) (x := c) (op := .eqz))) [.plain (.if_ .empty R' [])]
  have hpick : Step P closedHost
      ⟨s, f, [constI32 (intTestOp .i32 .eqz c), .plain (.if_ .empty R' [])]⟩
      ⟨s, f, [.plain (.block .empty (if c = 0 then R' else []))]⟩ := by
    by_cases hc : c = 0
    · have hz : intTestOp .i32 .eqz c ≠ 0 := fun hz => (eqz_eq_zero c).mp hz hc
      simpa [hc] using Step.ifTrue (P := P) (host := closedHost) (s := s) (f := f)
        (bt := .empty) (b₁ := R') (b₂ := []) hz
    · have hz : intTestOp .i32 .eqz c = 0 := (eqz_eq_zero c).mpr hc
      rw [ite_eq_right hc, hz]
      exact Step.ifFalse
  have hentry : Step P closedHost
      ⟨s, f, [.plain (.block .empty (if c = 0 then R' else []))]⟩
      ⟨s, f, [.label 0 [] (expression (if c = 0 then R' else []))]⟩ := by
    simpa [vals] using Step.block (P := P) (host := closedHost) (s := s) (f := f)
      (bt := .empty) (body := if c = 0 then R' else []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  exact (Relation.TransGen.single htest).tail hpick |>.tail hentry

/-- Original-to-transformed phases. The entered phase deliberately leaves both
local reads pending, and therefore contains no frame-dependent value. -/
inductive SourceGS (l : LabelIdx) (R R' : List Instr) : List Admin → List Admin → Prop where
  | start (i : LocalIdx) :
      SourceGS l R R' [.plain (.block .empty (.localGet i :: .brIf l :: R))]
        [.plain (.localGet i), .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]
  | entered (i : LocalIdx) :
      SourceGS l R R' [.label 0 [] (expression (.localGet i :: .brIf l :: R))]
        [.plain (.localGet i), .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]
  | read (v : Val) :
      SourceGS l R R' [.label 0 [] (v.toAdmin :: .plain (.brIf l) :: expression R)]
        [v.toAdmin, .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]
  | exit : SourceGS l R R' [.label 0 [] (.plain (.br l) :: expression R)] [.label 0 [] []]

def guardSourceB (x y : List Admin) : Prop :=
  ∃ (l : LabelIdx) (R R' : List Instr), l.toNat = 0 ∧ InstrsRel guardBI R R' ∧ SourceGS l R R' x y

/-- The original guard simulates its transformed result without numerical
determinism, using a body-aware rank for block-entry stuttering. -/
theorem guardSourceBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F guardBI guardSourceB aszs where
  src := by
    rintro x y ⟨n, h⟩
    cases n with
    | zero => exact h.elim
    | succ n =>
      obtain ⟨i, l, R, R', hl, hR, rfl, rfl⟩ := h
      exact ⟨l, R, R', hl, instrsRel_guard hR, by simpa [expression] using SourceGS.start i⟩
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨l, R, R', hl, hR, hg⟩ := hxy
    cases hg with
    | start i =>
      obtain ⟨pre, args, cfg, hV, hh, he⟩ := head_inv
        (W := vs) (e := .plain (.block .empty (.localGet i :: .brIf l :: R)))
        rfl (by simp) (by simp) (by simpa using hstep)
      obtain ⟨rfl, rfl⟩ := head_block hh
      simp only [List.append_nil] at hV
      subst pre
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals vs ++ [.plain (.localGet i), .plain (.intTestOp .i32 .eqz),
        .plain (.if_ .empty R' [])] ++ rest', Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, ?_⟩
      · exact LawfulCodeRank.context_lt (vals vs) rest (aszs_block_entry _)
      · exact ((AdminsRel.vals vs).append
          (.base ⟨l, R, R', hl, hR, .entered i⟩)).append hrest
    | entered i =>
      obtain ⟨s₁, f₁, body', hin, he⟩ := label_step_inert
        (W := []) (e := .plain (.localGet i)) rfl (by simp) (by simp)
        (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
        (by simpa [expression, vals] using hstep)
      obtain ⟨pre, args, cfg, hV, hh, hc⟩ := head_inv
        (W := []) (e := .plain (.localGet i)) rfl (by simp) (by simp) hin
      obtain ⟨rfl, v, hv, rfl⟩ := head_localGet hh
      simp only [List.append_nil] at hV
      subst pre
      simp only [vals, Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals vs ++ [v.toAdmin, .plain (.intTestOp .i32 .eqz),
        .plain (.if_ .empty R' [])] ++ rest', Or.inl (.single ?_), hst, ?_⟩
      · simpa using Step.append_right (Step.vals_left
          (Step.append_right (Step.variable (P := P) (host := closedHost)
            (VariableStep.localGet (s := t) hv))
            [.plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]) vs) rest'
      · exact ((AdminsRel.vals vs).append
          (.base ⟨l, R, R', hl, hR, .read v⟩)).append hrest
    | read v =>
      obtain ⟨s₁, f₁, body', hin, he⟩ := label_step_inert
        (W := [v]) (e := .plain (.brIf l)) rfl (by simp) (by simp)
        (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
        (by simpa [vals] using hstep)
      obtain ⟨pre, args, cfg, hV, hh, hc⟩ := head_inv
        (W := [v]) (e := .plain (.brIf l)) rfl (by simp) (by simp) hin
      obtain ⟨c, rfl, rfl⟩ := head_brIf hh
      obtain ⟨rfl, rfl⟩ := (Det.append_singleton_inj (l₁ := [])).mp hV
      simp only [vals, Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      by_cases hz : c = 0
      · simp only [hz, ↓reduceIte]
        refine ⟨t, vals vs ++ [.label 0 [] (expression R')] ++ rest',
          Or.inl ?_, hst, ?_⟩
        · simpa [hz, constI32, Val.i32] using Closure.transGen_ctx
            (finish_guard (P := P) t f' c R') vs rest'
        · exact ((AdminsRel.vals vs).append
            (.cons (.label 0 .nil (.src hR)) .nil)).append hrest
      · simp only [hz, ↓reduceIte]
        refine ⟨t, vals vs ++ [.label 0 [] []] ++ rest', Or.inl ?_, hst, ?_⟩
        · have ht := finish_guard (P := P) t f' c R'
          rw [ite_eq_right hz] at ht
          simpa [constI32, Val.i32, expression] using Closure.transGen_ctx ht vs rest'
        · exact ((AdminsRel.vals vs).append (.base ⟨l, R, R', hl, hR, .exit⟩)).append hrest
    | exit =>
      obtain ⟨pre, args, cfg, hV, hh, he⟩ := head_inv
        (W := vs) (e := .label 0 [] (.plain (.br l) :: expression R))
        rfl (by simp) (by simp) (by simpa using hstep)
      obtain ⟨rfl, rfl⟩ := head_label_br_zero hl rfl hh
      simp only [List.append_nil] at hV
      subst pre
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals vs ++ rest', Or.inl (.single ?_), hst, by simpa using (AdminsRel.vals vs).append hrest⟩
      simpa [vals] using Step.append_right (Step.vals_left
        (Step.labelVals (P := P) (host := closedHost) (s := t) (f := f')
          (n := 0) (cont := []) (vs := [])) vs) rest'
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    obtain ⟨l, R, R', hl, hR, hg⟩ := hxy
    cases hg with
    | start i =>
      exact not_exit (W := vs) (e₀ := .plain (.block .empty (.localGet i :: .brIf l :: R)))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa using he)
    | entered i =>
      exact not_exit (W := vs) (e₀ := .label 0 [] (expression (.localGet i :: .brIf l :: R)))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa using he)
    | read v =>
      exact not_exit (W := vs) (e₀ := .label 0 [] (v.toAdmin :: .plain (.brIf l) :: expression R))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa using he)
    | exit =>
      exact not_exit (W := vs) (e₀ := .label 0 [] (.plain (.br l) :: expression R))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨l, R, R', hl, hR, hg⟩ := hxy
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact Det.mem_vals ha
    cases hg with
    | start i => exact hall (.plain (.block .empty (.localGet i :: .brIf l :: R))) (by simp) rfl
    | entered i => exact hall (.label 0 [] (expression (.localGet i :: .brIf l :: R))) (by simp) rfl
    | read v => exact hall (.label 0 [] (v.toAdmin :: .plain (.brIf l) :: expression R)) (by simp) rfl
    | exit => exact hall (.label 0 [] (.plain (.br l) :: expression R)) (by simp) rfl

/-- The full recursive raw guard pass is exactly equivalent at the same arbitrary
profile, retaining the original input-and-output-validity premises. -/
theorem invertGuards_sound_any {m : BModule} (hm : m.Ok) (hm' : (invertGuards m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (invertGuards m).lower m.lower :=
  ⟨exportRefines_of_bodiesRel guardBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (invertGuards_bodiesRel m) hm' hm,
    (exportRefines_of_bodiesRel guardSourceBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (invertGuards_bodiesRel m).flip hm hm').mono (fun _ _ h => h.symm)⟩

/-- The actual checked pass keeps its existing validator guard and accepts every
valid input already accepted before, at every numerical profile. -/
theorem invertGuardsChecked_sound_any {m : BModule} (hm : m.Ok) :
    (invertGuardsChecked m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (invertGuardsChecked m).lower m.lower := by
  unfold invertGuardsChecked
  split
  · next h =>
    have hok := Exe.validOk_sound h
    exact ⟨hok, invertGuards_sound_any hm hok⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Wasm.Binaryen.GuardSim
