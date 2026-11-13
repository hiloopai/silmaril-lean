module

public import Silmaril.Proofs.Wasm.LimeCompile.Select.Redex

/-!
# Erasing `select` annotations: one rule at a time

`Sim P host c c'`: the step `c ~> c'` is matched from every configuration `d` that erases like
`c`, by a step to a configuration that erases like `c'`. Every rule of Core 3.0's `Step` is
shown to have this property here, one lemma per rule (or per shape of rule); `Step.lean`
assembles them by induction on the step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Select

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.LimeCompile.Select

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- `c ~> c'` is matched from every configuration erasing like `c`. -/
def Sim (P : Profile) (host : HostSemantics H) (c c' : Config H) : Prop :=
  ∀ d, selC c = selC d → ∃ d', Step P host d d' ∧ selC c' = selC d'

theorem selC_iff {c d : Config H} :
    selC c = selC d ↔
      selS c.store = selS d.store ∧ c.frame = d.frame ∧ selAs c.code = selAs d.code := by
  rcases c with ⟨s, f, L⟩
  rcases d with ⟨t, g, D⟩
  simp only [selC, Config.mk.injEq]

/-! ## Shapes -/

theorem sim_intro {s s' : Store H} {f f' : Frame} {L R : List Admin}
    (h : ∀ (t : Store H) (D : List Admin), selS s = selS t → selAs D = selAs L →
      ∃ d', Step P host ⟨t, f, D⟩ d' ∧ selC ⟨s', f', R⟩ = selC d') :
    Sim P host ⟨s, f, L⟩ ⟨s', f', R⟩ := by
  rintro ⟨t, g, D⟩ hd
  obtain ⟨hst, hfg, hD⟩ := selC_iff.mp hd
  cases hfg
  exact h t D hst hD.symm

theorem sim_rig {s s' : Store H} {f f' : Frame} {L R : List Admin} (hL : AllRig L)
    (h : ∀ t : Store H, selS s = selS t → ∃ d', Step P host ⟨t, f, L⟩ d' ∧ selC ⟨s', f', R⟩ = selC d') :
    Sim P host ⟨s, f, L⟩ ⟨s', f', R⟩ :=
  sim_intro fun t D hst hD => by
    rw [eq_of_selAs_rig hL hD]
    exact h t hst

theorem sim_pure {s : Store H} {f f' : Frame} {L R : List Admin} (hL : AllRig L)
    (h : ∀ t : Store H, Step P host ⟨t, f, L⟩ ⟨t, f', R⟩) : Sim P host ⟨s, f, L⟩ ⟨s, f', R⟩ :=
  sim_rig hL fun t hst => ⟨_, h t, selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

theorem sim_funcs {s s' : Store H} {f f' : Frame} {L R : List Admin} (hL : AllRig L)
    (hs' : s'.funcs = s.funcs)
    (h : ∀ Fs : List (FuncInst H), Fs.map FuncInst.type = s.funcs.map FuncInst.type →
      Step P host ⟨{ s with funcs := Fs }, f, L⟩ ⟨{ s' with funcs := Fs }, f', R⟩) :
    Sim P host ⟨s, f, L⟩ ⟨s', f', R⟩ :=
  sim_rig hL fun t hst => by
    have ht : t = { s with funcs := t.funcs } := (selS_eq hst).1
    have hstep := h t.funcs (types_eq_of_selS hst)
    rw [← ht] at hstep
    exact ⟨_, hstep, selC_iff.mpr ⟨selS_with hst hs', rfl, rfl⟩⟩

/-- A rigid prefix followed by arbitrary code, at the top level. -/
theorem sim_top {s : Store H} {f : Frame} {A rest R : List Admin} (hA : AllRig A)
    (h : ∀ (t : Store H) (rest' : List Admin), selAs rest' = selAs rest →
      Step P host ⟨t, f, A ++ rest'⟩ ⟨t, f, R⟩) :
    Sim P host ⟨s, f, A ++ rest⟩ ⟨s, f, R⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨R', rfl, hR⟩ := rigid_prefix hA hD
    exact ⟨_, h t R' hR, selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

/-- A rigid prefix followed by arbitrary code, under a label. -/
theorem sim_label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {A rest R : List Admin}
    (hA : AllRig A)
    (h : ∀ (t : Store H) (cont' : List Instr) (rest' : List Admin),
      Step P host ⟨t, f, [.label n cont' (A ++ rest')]⟩ ⟨t, f, R⟩) :
    Sim P host ⟨s, f, [.label n cont (A ++ rest)]⟩ ⟨s, f, R⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨cont', B, rfl, -, hB⟩ := label_inv hD
    obtain ⟨R', rfl, -⟩ := rigid_prefix hA hB
    exact ⟨_, h t cont' R', selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

/-- A rigid prefix followed by arbitrary code, under a handler. -/
theorem sim_handler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {A rest R : List Admin}
    (hA : AllRig A)
    (h : ∀ (t : Store H) (rest' : List Admin), Step P host ⟨t, f, [.handler n cs (A ++ rest')]⟩ ⟨t, f, R⟩) :
    Sim P host ⟨s, f, [.handler n cs (A ++ rest)]⟩ ⟨s, f, R⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨B, rfl, hB⟩ := handler_inv hD
    obtain ⟨R', rfl, -⟩ := rigid_prefix hA hB
    exact ⟨_, h t R', selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

/-- A rigid prefix followed by arbitrary code, under a frame. -/
theorem sim_frame {s : Store H} {f fi : Frame} {n : Nat} {A rest R : List Admin} (hA : AllRig A)
    (h : ∀ (t : Store H) (rest' : List Admin), Step P host ⟨t, f, [.frame n fi (A ++ rest')]⟩ ⟨t, f, R⟩) :
    Sim P host ⟨s, f, [.frame n fi (A ++ rest)]⟩ ⟨s, f, R⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨B, rfl, hB⟩ := frame_inv hD
    obtain ⟨R', rfl, -⟩ := rigid_prefix hA hB
    exact ⟨_, h t R', selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

theorem rigP {i : Instr} (h₁ : i.bodies = []) (h₂ : ∀ ts, i ≠ .select ts) : Rig (.plain i) :=
  rig_plain ⟨h₁, h₂⟩

theorem allRig_one {a : Admin} (ha : Rig a) : AllRig [a] := allRig_cons ha allRig_nil

theorem allRig_two {a b : Admin} (ha : Rig a) (hb : Rig b) : AllRig [a, b] :=
  allRig_cons ha (allRig_one hb)

theorem allRig_three {a b c : Admin} (ha : Rig a) (hb : Rig b) (hc : Rig c) : AllRig [a, b, c] :=
  allRig_cons ha (allRig_two hb hc)

/-! ## Families -/

theorem sim_parametric {s : Store H} {f : Frame} {L R : List Admin} (h : ParametricStep L R) :
    Sim P host ⟨s, f, L⟩ ⟨s, f, R⟩ := by
  cases h with
  | unreachable =>
    exact sim_pure (allRig_one (rigP rfl fun _ h => nomatch h)) fun _ => .parametric .unreachable
  | nop => exact sim_pure (allRig_one (rigP rfl fun _ h => nomatch h)) fun _ => .parametric .nop
  | drop v =>
    exact sim_pure (allRig_two (rig_val v) (rigP rfl fun _ h => nomatch h))
      fun _ => .parametric (.drop v)
  | @selectTrue v₁ v₂ c ts hc =>
    exact sim_intro fun t D hst hD => by
      obtain ⟨j, rfl, hj⟩ := plain_inv (vs := [v₁, v₂, .i32 c]) (i := .select ts) hD
      obtain ⟨ts', rfl⟩ := selI_eq_select hj
      exact ⟨_, .parametric (.selectTrue (ts := ts') hc), selC_iff.mpr ⟨hst, rfl, rfl⟩⟩
  | selectFalse v₁ v₂ ts =>
    exact sim_intro fun t D hst hD => by
      obtain ⟨j, rfl, hj⟩ := plain_inv (vs := [v₁, v₂, .i32 0]) (i := .select ts) hD
      obtain ⟨ts', rfl⟩ := selI_eq_select hj
      exact ⟨_, .parametric (.selectFalse v₁ v₂ ts'), selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

theorem sim_variable {c c' : Config H} (h : VariableStep c c') : Sim P host c c' := by
  rcases c with ⟨s, f, L⟩
  rcases c' with ⟨s', f', R⟩
  exact sim_funcs (variable_rig h) (variableStep_funcs h []).2
    fun Fs _ => .variable (variableStep_funcs h Fs).1

theorem sim_table {c c' : Config H} (h : TableStep P c c') : Sim P host c c' := by
  rcases c with ⟨s, f, L⟩
  rcases c' with ⟨s', f', R⟩
  exact sim_funcs (table_rig h) (tableStep_funcs h []).2
    fun Fs _ => .table (tableStep_funcs h Fs).1

theorem sim_memory {c c' : Config H} (h : MemoryStep P c c') : Sim P host c c' := by
  rcases c with ⟨s, f, L⟩
  rcases c' with ⟨s', f', R⟩
  exact sim_funcs (memory_rig h) (memoryStep_funcs h []).2
    fun Fs _ => .memory (memoryStep_funcs h Fs).1

theorem sim_aggregate {c c' : Config H} (h : AggregateStep c c') : Sim P host c c' := by
  rcases c with ⟨s, f, L⟩
  rcases c' with ⟨s', f', R⟩
  exact sim_funcs (aggregate_rig h) (aggregateStep_funcs h []).2
    fun Fs _ => .aggregate (aggregateStep_funcs h Fs).1

theorem sim_reference {c c' : Config H} (h : RefStep c c') : Sim P host c c' := by
  rcases c with ⟨s, f, L⟩
  rcases c' with ⟨s', f', R⟩
  exact sim_funcs (reference_rig h) (refStep_funcs h (Fs := s.funcs) rfl).2
    fun Fs hF => .reference (refStep_funcs h hF).1

/-! ## Contexts -/

theorem sim_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (ih : Sim P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hne : vs ≠ [] ∨ rest ≠ []) :
    Sim P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨A, B, rfl, hA, hB⟩ := selAs_eq_append hD
    obtain ⟨A₂, rfl, hA₂⟩ := selAs_eq_vals_append hA
    obtain ⟨⟨t', g', A₂'⟩, hstep, hrel⟩ := ih ⟨t, f, A₂⟩ (selC_iff.mpr ⟨hst, rfl, hA₂.symm⟩)
    obtain ⟨hst', hfg, hA'⟩ := selC_iff.mp hrel
    have hne' : vs ≠ [] ∨ B ≠ [] := hne.imp id (selAs_ne_nil hB)
    refine ⟨⟨t', g', vals vs ++ A₂' ++ B⟩, .ctxtInstrs hstep hne', selC_iff.mpr ⟨hst', hfg, ?_⟩⟩
    simp only [selAs_append, selAs_vals, hA', hB]

theorem sim_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : Sim P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Sim P host ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨cont', B, rfl, hc, hB⟩ := label_inv hD
    obtain ⟨⟨t', g', B'⟩, hstep, hrel⟩ := ih ⟨t, f, B⟩ (selC_iff.mpr ⟨hst, rfl, hB.symm⟩)
    obtain ⟨hst', hfg, hB'⟩ := selC_iff.mp hrel
    refine ⟨⟨t', g', [.label n cont' B']⟩, .ctxtLabel hstep, selC_iff.mpr ⟨hst', hfg, ?_⟩⟩
    simp only [selAs_cons, selA_label, selAs_nil, hc, hB']

theorem sim_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : Sim P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Sim P host ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨B, rfl, hB⟩ := handler_inv hD
    obtain ⟨⟨t', g', B'⟩, hstep, hrel⟩ := ih ⟨t, f, B⟩ (selC_iff.mpr ⟨hst, rfl, hB.symm⟩)
    obtain ⟨hst', hfg, hB'⟩ := selC_iff.mp hrel
    refine ⟨⟨t', g', [.handler n cs B']⟩, .ctxtHandler hstep, selC_iff.mpr ⟨hst', hfg, ?_⟩⟩
    simp only [selAs_cons, selA_handler, selAs_nil, hB']

theorem sim_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : Sim P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Sim P host ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨B, rfl, hB⟩ := frame_inv hD
    obtain ⟨⟨t', g', B'⟩, hstep, hrel⟩ := ih ⟨t, fi, B⟩ (selC_iff.mpr ⟨hst, rfl, hB.symm⟩)
    obtain ⟨hst', hfg, hB'⟩ : selS s' = selS t' ∧ fi' = g' ∧ selAs is' = selAs B' :=
      selC_iff.mp hrel
    refine ⟨⟨t', f, [.frame n g' B']⟩, .ctxtFrame hstep, selC_iff.mpr ⟨hst', rfl, ?_⟩⟩
    simp only [selAs_cons, selA_frame, selAs_nil, hfg, hB']

/-! ## Blocks -/

theorem sim_block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) :
    Sim P host ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨j, rfl, hj⟩ := plain_inv hD
    obtain ⟨b', rfl, hb⟩ := selI_eq_block hj
    refine ⟨_, .block hbt hm, selC_iff.mpr ⟨hst, rfl, ?_⟩⟩
    simp only [selAs_cons, selA_label, selAs_append, selAs_vals, selAs_expression, hb]

theorem sim_loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) :
    Sim P host ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨j, rfl, hj⟩ := plain_inv hD
    obtain ⟨b', rfl, hb⟩ := selI_eq_loop hj
    refine ⟨_, .loop hbt hm, selC_iff.mpr ⟨hst, rfl, ?_⟩⟩
    simp only [selAs_cons, selA_label, selAs_append, selAs_vals, selAs_expression, selL_cons,
      selI_loop, selL_nil, hb]

theorem sim_tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
    Sim P host ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
      ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨j, rfl, hj⟩ := plain_inv hD
    obtain ⟨b', rfl, hb⟩ := selI_eq_tryTable hj
    refine ⟨_, .tryTable hbt hm, selC_iff.mpr ⟨hst, rfl, ?_⟩⟩
    simp only [selAs_cons, selA_handler, selA_label, selAs_append, selAs_vals, selAs_expression,
      selAs_nil, hb]

theorem sim_ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} (hc : c ≠ 0) :
    Sim P host ⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩ ⟨s, f, [.plain (.block bt b₁)]⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨j, rfl, hj⟩ := plain_inv (vs := [.i32 c]) (i := .if_ bt b₁ b₂) hD
    obtain ⟨b₁', b₂', rfl, h₁, -⟩ := selI_eq_if hj
    refine ⟨_, .ifTrue hc, selC_iff.mpr ⟨hst, rfl, ?_⟩⟩
    simp only [selAs_cons, selA_plain, selI_block, selAs_nil, h₁]

theorem sim_ifFalse {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr} :
    Sim P host ⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩ ⟨s, f, [.plain (.block bt b₂)]⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨j, rfl, hj⟩ := plain_inv (vs := [.i32 0]) (i := .if_ bt b₁ b₂) hD
    obtain ⟨b₁', b₂', rfl, -, h₂⟩ := selI_eq_if hj
    refine ⟨_, .ifFalse, selC_iff.mpr ⟨hst, rfl, ?_⟩⟩
    simp only [selAs_cons, selA_plain, selI_block, selAs_nil, h₂]

theorem sim_labelVals {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val} :
    Sim P host ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨cont', B, rfl, -, hB⟩ := label_inv hD
    rw [eq_vals_of_selAs hB]
    exact ⟨_, .labelVals, selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

theorem sim_trapLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} :
    Sim P host ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨cont', B, rfl, -, hB⟩ := label_inv hD
    rw [eq_of_selAs_rig (allRig_one rig_trap) hB]
    exact ⟨_, .trapLabel, selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

theorem sim_throwRefLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat} :
    Sim P host ⟨s, f, [.label n cont (throwing a)]⟩ ⟨s, f, throwing a⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨cont', B, rfl, -, hB⟩ := label_inv hD
    rw [eq_of_selAs_rig (allRig_two (rig_ref _) (rigP (i := .throwRef) rfl fun _ h => nomatch h)) hB]
    exact ⟨_, .throwRefLabel, selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

/-! ## Branches -/

theorem sim_brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} (hl : l.toNat = 0)
    (hn : vs.length = n) :
    Sim P host ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ expression cont⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨cont', B, rfl, hc, hB⟩ := label_inv hD
    obtain ⟨R', rfl, -⟩ := rigid_prefix (allRig_append (allRig_append (allRig_vals vs')
      (allRig_vals vs)) (allRig_one (rigP (i := .br l) rfl fun _ h => nomatch h))) hB
    refine ⟨_, .brLabelZero hl hn, selC_iff.mpr ⟨hst, rfl, ?_⟩⟩
    simp only [selAs_append, selAs_vals, selAs_expression, hc]

theorem sim_brLabelSucc {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
    {l : LabelIdx} {rest : List Admin} (hl : 0 < l.toNat) :
    Sim P host ⟨s, f, [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩ :=
  sim_label (allRig_append (allRig_vals vs) (allRig_one (rigP rfl fun _ h => nomatch h)))
    fun _ _ _ => .brLabelSucc hl

theorem sim_brHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
    {l : LabelIdx} {rest : List Admin} :
    Sim P host ⟨s, f, [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br l)]⟩ :=
  sim_handler (allRig_append (allRig_vals vs) (allRig_one (rigP rfl fun _ h => nomatch h)))
    fun _ _ => .brHandler

theorem sim_returnLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
    {rest : List Admin} :
    Sim P host ⟨s, f, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩ :=
  sim_label (allRig_append (allRig_vals vs) (allRig_one (rigP rfl fun _ h => nomatch h)))
    fun _ _ _ => .returnLabel

theorem sim_returnHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
    {rest : List Admin} :
    Sim P host ⟨s, f, [.handler n cs (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩ :=
  sim_handler (allRig_append (allRig_vals vs) (allRig_one (rigP rfl fun _ h => nomatch h)))
    fun _ _ => .returnHandler

theorem sim_returnFrame {s : Store H} {f fi : Frame} {n : Nat} {vs' vs : List Val}
    {rest : List Admin} (hn : vs.length = n) :
    Sim P host ⟨s, f, [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs⟩ :=
  sim_frame (allRig_append (allRig_append (allRig_vals vs') (allRig_vals vs))
    (allRig_one (rigP rfl fun _ h => nomatch h))) fun _ _ => .returnFrame hn

theorem sim_returnCallRefLabel {s : Store H} {f : Frame} {k : Nat} {cont : List Instr}
    {vs : List Val} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
    Sim P host ⟨s, f, [.label k cont (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩ :=
  sim_label (allRig_append (allRig_vals vs) (allRig_one (rig_isReturnCallRef hc)))
    fun _ _ _ => .returnCallRefLabel hc

theorem sim_returnCallRefHandler {s : Store H} {f : Frame} {k : Nat} {cs : List Catch}
    {vs : List Val} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
    Sim P host ⟨s, f, [.handler k cs (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩ :=
  sim_handler (allRig_append (allRig_vals vs) (allRig_one (rig_isReturnCallRef hc)))
    fun _ _ => .returnCallRefHandler hc

theorem sim_returnCallRefFrameNull {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val}
    {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
    Sim P host ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]⟩ ⟨s, f, [.trap]⟩ :=
  sim_frame (allRig_append (allRig_vals vs) (allRig_two (rig_ref _) (rig_isReturnCallRef hc)))
    fun _ _ => .returnCallRefFrameNull hc

theorem sim_trapInstrs {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) :
    Sim P host ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩ :=
  sim_top (allRig_append (allRig_vals vs) (allRig_one rig_trap))
    fun _ _ hr => .trapInstrs (hne.imp id (selAs_ne_nil hr))

theorem sim_throwRefInstrs {s : Store H} {f : Frame} {vs : List Val} {a : Nat}
    {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ []) :
    Sim P host ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩ :=
  sim_top (allRig_append (allRig_vals vs) (allRig_two (rig_ref _) (rigP rfl fun _ h => nomatch h)))
    fun _ _ hr => .throwRefInstrs (hne.imp id (selAs_ne_nil hr))

/-! ## Calls -/

theorem sim_call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
    Sim P host ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ :=
  sim_rig (allRig_one (rigP rfl fun _ h => nomatch h)) fun t hst => by
    obtain ⟨fi', hf', he⟩ := funcs_get_of_selS hst hf
    have hty : fi'.type = fi.type := (selFI_eq he).1
    exact ⟨_, .call hx hf', selC_iff.mpr ⟨hst, rfl, by rw [hty]⟩⟩

theorem sim_returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
    Sim P host ⟨s, f, [.plain (.returnCall x)]⟩
      ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩ :=
  sim_rig (allRig_one (rigP rfl fun _ h => nomatch h)) fun t hst => by
    obtain ⟨fi', hf', he⟩ := funcs_get_of_selS hst hf
    have hty : fi'.type = fi.type := (selFI_eq he).1
    exact ⟨_, .returnCall hx hf', selC_iff.mpr ⟨hst, rfl, by rw [hty]⟩⟩

theorem callRig {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef) :
    AllRig (vals vs ++ [.ref (.func a), c]) :=
  allRig_append (allRig_vals vs) (allRig_two (rig_ref _) (rig_isCallRef hc))

theorem sim_callRefFunc {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .wasm code) :
    Sim P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ :=
  sim_rig (callRig hc) fun t hst => by
    obtain ⟨fi', hf', hfe⟩ := funcs_get_of_selS hst hf
    obtain ⟨hty, hmod, hw, -⟩ := selFI_eq hfe
    obtain ⟨code', hcode', hloc, hbody⟩ := hw code hcode
    have he' : Expand fi'.type (.func ps rs) := by rw [hty]; exact he
    refine ⟨_, .callRefFunc hc hf' he' hn hcode', selC_iff.mpr ⟨hst, rfl, ?_⟩⟩
    simp only [selAs_cons, selA_frame, selA_label, selAs_nil, selAs_expression, hmod, hloc,
      hbody]

theorem sim_callRefHost (hh : HostResp host) {s s' : Store H} {f : Frame} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {r : Result}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .host h)
    (hhost : host h s vs (.returned s' r)) :
    Sim P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩ :=
  sim_rig (callRig hc) fun t hst => by
    obtain ⟨fi', hf', hfe⟩ := funcs_get_of_selS hst hf
    obtain ⟨hty, -, -, hho⟩ := selFI_eq hfe
    have he' : Expand fi'.type (.func ps rs) := by rw [hty]; exact he
    obtain ⟨o', ho', hsim⟩ := hh h s t vs _ hst hhost
    cases o' with
    | diverged => exact hsim.elim
    | returned t' r' =>
      obtain ⟨hst', rfl⟩ := hsim
      exact ⟨_, .callRefHost hc hf' he' hn (hho h hcode) ho', selC_iff.mpr ⟨hst', rfl, rfl⟩⟩

theorem sim_callRefHostDiv (hh : HostResp host) {s : Store H} {f : Frame} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .host h) (hhost : host h s vs .diverged) :
    Sim P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ :=
  sim_rig (callRig hc) fun t hst => by
    obtain ⟨fi', hf', hfe⟩ := funcs_get_of_selS hst hf
    obtain ⟨hty, -, -, hho⟩ := selFI_eq hfe
    have he' : Expand fi'.type (.func ps rs) := by rw [hty]; exact he
    obtain ⟨o', ho', hsim⟩ := hh h s t vs _ hst hhost
    cases o' with
    | returned _ _ => exact hsim.elim
    | diverged =>
      exact ⟨_, .callRefHostDiv hc hf' he' hn (hho h hcode) ho', selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

theorem sim_returnCallRefFrameAddr {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val}
    {a : Nat} {c : Admin} {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length) :
    Sim P host ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ :=
  sim_intro fun t D hst hD => by
    obtain ⟨B, rfl, hB⟩ := frame_inv hD
    obtain ⟨R', rfl, -⟩ := rigid_prefix (allRig_append (allRig_append (allRig_vals vs')
      (allRig_vals vs)) (allRig_two (rig_ref _) (rig_isReturnCallRef hc))) hB
    obtain ⟨fn', hf', hfe⟩ := funcs_get_of_selS hst hf
    have he' : Expand fn'.type (.func ps rs) := by rw [(selFI_eq hfe).1]; exact he
    exact ⟨_, .returnCallRefFrameAddr hc hf' he' hn, selC_iff.mpr ⟨hst, rfl, rfl⟩⟩

end Silmaril.Proofs.Wasm.LimeCompile.Select
