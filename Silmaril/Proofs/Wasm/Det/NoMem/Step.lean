module

public import Silmaril.Proofs.Wasm.Det.NoMem.Preserve

/-!
# The memory-free, float-free subset: closure under every Core 3.0 step

`step_seq`: for every profile and host, a step from subset code (`Seq`, in the frame's module
instance) leads to subset code and keeps the frame's module instance, provided every function
that may be entered has a subset body (`FunOk`) and indirect calls only occur when every
function may be entered (`Mode`). The proof is by induction on the step: the context rules use
the induction hypothesis and `step_lastS`, the call rules use `FunOk` (through `q_of_callRef`),
and every other rule rearranges values and subset instructions.

New proof.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Det.NoMem

variable {H : Type} {q : Nat → Bool} {ind : Bool}

theorem seq_ref_map {fs : List Nat} {p : Prop} (rs : List Ref) (l : List Admin) :
    Seq q ind fs p (rs.map Admin.ref ++ l) ↔ Seq q ind fs (lastS q p (rs.map Admin.ref)) l := by
  rw [seq_append]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  clear h
  induction rs generalizing p with
  | nil => trivial
  | cons r rs ih => exact ⟨fun hc => absurd hc isCRT_ref, trivial, ih⟩

/-- The body a call enters is of the subset. -/
theorem seq_callee {fs : List Nat} {p : Prop} {F : List (FuncInst H)} (hF : FunOk q ind F)
    {a n : Nat} {fi : FuncInst H} {code : Func} (ha : q a = true) (hf : F[a]? = some fi)
    (hcode : fi.code = .wasm code) (vs : List Val) :
    Seq q ind fs p [.frame n (Frame.forCall fi.module vs code.locals)
      [.label n [] (expression code.body)]] := by
  have hb := instrsB_iff.mp (hF a fi code ha hf hcode)
  exact seq_single isCRT_frame
    (seq_single isCRT_label ⟨fun _ h => absurd h List.not_mem_nil, seq_expression hb⟩)

/-- A body under a `block`, `loop` or `try_table`. -/
theorem seq_vals_expr {fs : List Nat} {p : Prop} (vs : List Val) {b : List Instr}
    (h : instrsB q ind fs b = true) : Seq q ind fs p (vals vs ++ expression b) :=
  (seq_vals_append vs _).mpr (seq_expression (instrsB_iff.mp h))

/-- The plain instruction at the end of subset code. -/
theorem plainOk_last {fs : List Nat} {p : Prop} {l : List Admin} {i : Instr}
    (h : Seq q ind fs p (l ++ [.plain i])) : PlainOk q ind fs i := by
  rw [seq_append] at h
  exact h.2.2.1

/-- A `PlainOk` instruction that is not a constant passes `instrB`. -/
theorem plainOk_instrB {fs : List Nat} {i : Instr} (h : PlainOk q ind fs i)
    (hf : (∃ t b, i = .floatConst t b) → False) (hv : (∃ b, i = .vecConst b) → False) :
    instrB q ind fs i = true := by
  rcases h with h | h | h
  · exact h
  · exact (hf h).elim
  · exact (hv h).elim

/-- Code made of references only. -/
theorem seq_of_refs {fs : List Nat} {p : Prop} {l : List Admin} (h : ∀ a ∈ l, ∃ r, a = .ref r) :
    Seq q ind fs p l := by
  induction l generalizing p with
  | nil => trivial
  | cons a as ih =>
    obtain ⟨r, rfl⟩ := h a (List.mem_cons_self ..)
    exact ⟨fun hc => absurd hc isCRT_ref, trivial, ih fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

@[simp] theorem seq_take_drop_ref {fs : List Nat} {p : Prop} (rs : List Ref) (i n : Nat) :
    Seq q ind fs p (List.take n (List.drop i (rs.map Admin.ref))) := by
  refine seq_of_refs fun a ha => ?_
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  exact ⟨r, rfl⟩

/-! ## The cases of the step theorem -/

section Cases

variable {fs : List Nat} {p : Prop}

theorem seq_ctxt {vs : List Val} {is is' rest : List Admin}
    (ih : ∀ {p : Prop}, Seq q ind fs p is → Seq q ind fs p is')
    (hl : ∀ {p : Prop}, lastS q p is → lastS q p is')
    (hc : Seq q ind fs p (vals vs ++ is ++ rest)) : Seq q ind fs p (vals vs ++ is' ++ rest) := by
  have h₀ := (seq_append3 _ _ _).mp hc
  exact (seq_append3 _ _ _).mpr ⟨h₀.1, ih h₀.2.1, seq_mono hl h₀.2.2⟩

theorem seq_label_ctxt {m m' : ModuleInst} {n : Nat} {cont : List Instr} {is is' : List Admin}
    (ih : Seq q ind m.funcs False is → Seq q ind m.funcs False is' ∧ m' = m)
    (hc : Seq q ind m.funcs p [.label n cont is]) :
    Seq q ind m.funcs p [.label n cont is'] ∧ m' = m := by
  have h₀ : (∀ i ∈ cont, instrB q ind m.funcs i = true) ∧ Seq q ind m.funcs False is :=
    aOk_label.mp (seq_cons.mp hc).2.1
  exact ⟨seq_single isCRT_label ⟨h₀.1, (ih h₀.2).1⟩, (ih h₀.2).2⟩

theorem seq_handler_ctxt {m m' : ModuleInst} {n : Nat} {cs : List Catch} {is is' : List Admin}
    (ih : Seq q ind m.funcs False is → Seq q ind m.funcs False is' ∧ m' = m)
    (hc : Seq q ind m.funcs p [.handler n cs is]) :
    Seq q ind m.funcs p [.handler n cs is'] ∧ m' = m := by
  have h₀ : Seq q ind m.funcs False is := aOk_handler.mp (seq_cons.mp hc).2.1
  exact ⟨seq_single isCRT_handler (ih h₀).1, (ih h₀).2⟩

theorem seq_frame_ctxt {fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : Seq q ind fi.module.funcs False is →
      Seq q ind fi.module.funcs False is' ∧ fi'.module = fi.module)
    (hc : Seq q ind fs p [.frame n fi is]) : Seq q ind fs p [.frame n fi' is'] := by
  have h₀ : Seq q ind fi.module.funcs False is := aOk_frame.mp (seq_cons.mp hc).2.1
  have h₁ : Seq q ind fi'.module.funcs False is' := (ih h₀).2 ▸ (ih h₀).1
  exact seq_single isCRT_frame h₁

theorem seq_block {vs : List Val} {bt : BlockType} {body : List Instr} {n : Nat}
    (hc : Seq q ind fs p (vals vs ++ [.plain (.block bt body)])) :
    Seq q ind fs p [.label n [] (vals vs ++ expression body)] := by
  have hb : instrB q ind fs (.block bt body) = true :=
    plainOk_instrB (plainOk_last hc) (by rintro ⟨_, _, ⟨⟩⟩) (by rintro ⟨_, ⟨⟩⟩)
  exact seq_single isCRT_label ⟨by simp, seq_vals_expr _ (by simpa [instrB] using hb)⟩

theorem seq_loop {vs : List Val} {bt : BlockType} {body : List Instr} {n : Nat}
    (hc : Seq q ind fs p (vals vs ++ [.plain (.loop bt body)])) :
    Seq q ind fs p [.label n [.loop bt body] (vals vs ++ expression body)] := by
  have hb : instrB q ind fs (.loop bt body) = true :=
    plainOk_instrB (plainOk_last hc) (by rintro ⟨_, _, ⟨⟩⟩) (by rintro ⟨_, ⟨⟩⟩)
  exact seq_single isCRT_label ⟨by simpa using hb, seq_vals_expr _ (by simpa [instrB] using hb)⟩

theorem seq_tryTable {vs : List Val} {bt : BlockType} {cs : List Catch} {body : List Instr}
    {n : Nat} (hc : Seq q ind fs p (vals vs ++ [.plain (.tryTable bt cs body)])) :
    Seq q ind fs p [.handler n cs [.label n [] (vals vs ++ expression body)]] := by
  have hb : instrB q ind fs (.tryTable bt cs body) = true :=
    plainOk_instrB (plainOk_last hc) (by rintro ⟨_, _, ⟨⟩⟩) (by rintro ⟨_, ⟨⟩⟩)
  exact seq_single isCRT_handler
    (seq_single isCRT_label ⟨by simp, seq_vals_expr _ (by simpa [instrB] using hb)⟩)

theorem seq_ref_crt {a : Nat} {c : Admin} (hok : AOk q ind fs c) (ha : q a = true) :
    Seq q ind fs p [.ref (.func a), c] :=
  ⟨fun h => absurd h isCRT_ref, trivial, fun _ b hb => by cases hb; exact ha, hok, trivial⟩

theorem seq_if {x : Admin} {bt : BlockType} {b₁ b₂ : List Instr}
    (hc : Seq q ind fs p [x, .plain (.if_ bt b₁ b₂)]) :
    Seq q ind fs p [.plain (.block bt b₁)] ∧ Seq q ind fs p [.plain (.block bt b₂)] := by
  have hb : instrB q ind fs (.if_ bt b₁ b₂) = true :=
    plainOk_instrB (plainOk_last (l := [x]) hc) (by rintro ⟨_, _, ⟨⟩⟩) (by rintro ⟨_, ⟨⟩⟩)
  have hb' : instrsB q ind fs b₁ = true ∧ instrsB q ind fs b₂ = true := by
    simpa [instrB] using hb
  exact ⟨seq_single isCRT_plain (Or.inl (by simpa [instrB] using hb'.1)),
    seq_single isCRT_plain (Or.inl (by simpa [instrB] using hb'.2))⟩

theorem q_of_call {x : FuncIdx} {a : Nat} (hx : fs[x.toNat]? = some a)
    (hc : Seq q ind fs p [.plain (.call x)]) : q a = true := by
  have hb : PlainOk q ind fs (.call x) := plainOk_last (l := []) hc
  simpa [PlainOk, instrB, callOk, hx] using hb

theorem q_of_returnCall {x : FuncIdx} {a : Nat} (hx : fs[x.toNat]? = some a)
    (hc : Seq q ind fs p [.plain (.returnCall x)]) : q a = true := by
  have hb : PlainOk q ind fs (.returnCall x) := plainOk_last (l := []) hc
  simpa [PlainOk, instrB, callOk, hx] using hb

theorem ind_of_plain {i : Instr} (hi : instrB q ind fs i = ind)
    (hc : Seq q ind fs p [.plain i]) (hf : (∃ t b, i = .floatConst t b) → False)
    (hv : (∃ b, i = .vecConst b) → False) : ind = true :=
  hi ▸ plainOk_instrB (plainOk_last (l := []) hc) hf hv

theorem seq_callIndirect {x : TableIdx} {y : TypeIdx}
    (hc : Seq q ind fs p [.plain (.callIndirect x y)]) :
    Seq q ind fs p [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.callRef y)] := by
  have hi : ind = true :=
    ind_of_plain (by simp [instrB]) hc (by rintro ⟨_, _, ⟨⟩⟩) (by rintro ⟨_, ⟨⟩⟩)
  simp [PlainOk, instrB, flatOk, hi]

theorem seq_returnCallIndirect {x : TableIdx} {y : TypeIdx}
    (hc : Seq q ind fs p [.plain (.returnCallIndirect x y)]) :
    Seq q ind fs p [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.returnCallRef y)] := by
  have hi : ind = true :=
    ind_of_plain (by simp [instrB]) hc (by rintro ⟨_, _, ⟨⟩⟩) (by rintro ⟨_, ⟨⟩⟩)
  simp [PlainOk, instrB, flatOk, hi]

theorem seq_returnFrameAddr (hM : Mode q ind) {fs' : List Nat} {fi : Frame} {k a : Nat}
    {vs' vs : List Val} {c : Admin} {rest : List Admin} (hcr : c.IsReturnCallRef)
    (hc : Seq q ind fs' p [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]) :
    Seq q ind fs p (vals vs ++ [.ref (.func a), c.retToCallIn fi.module]) := by
  have h₀ : Seq q ind fi.module.funcs False (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) :=
    aOk_frame.mp (seq_cons.mp hc).2.1
  have h₁ : Seq q ind fi.module.funcs (lastS q False (vals vs' ++ vals vs)) [.ref (.func a), c] :=
    ((seq_append _ _).mp ((seq_append _ _).mp h₀).1).2
  exact (seq_vals_append _ _).mpr (seq_retToCallIn _ hcr h₁ (q_of_returnCallRef hM hcr h₁))

end Cases

-- The family arms share one simp set across all rules of a family; not every rule uses every
-- lemma of it.
set_option linter.unusedSimpArgs false in
/-- **Closure**: a Core step (every profile, every host) keeps code of the subset in the subset
and keeps the frame's module instance. -/
theorem step_seq (hM : Mode q ind) {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hF : FunOk q ind c.store.funcs) {p : Prop}
    (hc : Seq q ind c.frame.module.funcs p c.code) :
    Seq q ind c.frame.module.funcs p c'.code ∧ c'.frame.module = c.frame.module := by
  induction h generalizing p with
  | parametric h =>
    cases h <;> exact ⟨by simp [PlainOk, instrB, flatOk, constI32, Val.i32], rfl⟩
  | numeric h =>
    cases h <;> exact ⟨by simp [PlainOk, instrB, flatOk, constI32, Val.i32], rfl⟩
  | vector h => cases h <;> exact absurd hc (by simp [PlainOk, instrB, flatOk])
  | «variable» h =>
    cases h <;> exact ⟨by simp [PlainOk, instrB, flatOk], rfl⟩
  | table h =>
    cases h <;> exact ⟨by simp [PlainOk, instrB, flatOk, constI32, Val.i32], rfl⟩
  | memory h => cases h <;> exact absurd hc (by simp [PlainOk, instrB, flatOk])
  | reference h =>
    cases h <;> exact ⟨by simp [PlainOk, instrB, flatOk, constI32, Val.i32], rfl⟩
  | aggregate h =>
    cases h <;> exact ⟨by simp [seq_append, lastS_append, PlainOk, instrB, flatOk, constI32,
      Val.i32, seq_ref_map], rfl⟩
  | ctxtInstrs h _ ih =>
    exact ⟨seq_ctxt (fun h' => (ih hF h').1) (step_lastS h) hc,
      (ih hF ((seq_append3 _ _ _).mp hc).2.1).2⟩
  | ctxtLabel _ ih => exact seq_label_ctxt (fun h' => ih hF h') hc
  | ctxtHandler _ ih => exact seq_handler_ctxt (fun h' => ih hF h') hc
  | ctxtFrame _ ih => exact ⟨seq_frame_ctxt (fun h' => ih hF h') hc, rfl⟩
  | block => exact ⟨seq_block hc, rfl⟩
  | loop => exact ⟨seq_loop hc, rfl⟩
  | tryTable => exact ⟨seq_tryTable hc, rfl⟩
  | call hx => exact ⟨seq_ref_crt aOk_crt (q_of_call hx hc), rfl⟩
  | returnCall hx => exact ⟨seq_ref_crt aOk_rcrt (q_of_returnCall hx hc), rfl⟩
  | ifTrue => exact ⟨(seq_if hc).1, rfl⟩
  | ifFalse => exact ⟨(seq_if hc).2, rfl⟩
  | callRefFunc hcr hf _ _ hcode =>
    exact ⟨seq_callee hF (q_of_callRef hM hcr ((seq_vals_append _ _).mp hc)) hf hcode _, rfl⟩
  | callRefHost => exact ⟨seq_toAdmin _, rfl⟩
  | callRefHostDiv => exact ⟨hc, rfl⟩
  | returnCallRefLabel =>
    exact ⟨seq_mono False.elim ((seq_append _ _).mp (aOk_label.mp (seq_cons.mp hc).2.1).2).1, rfl⟩
  | returnCallRefHandler =>
    exact ⟨seq_mono False.elim ((seq_append _ _).mp (aOk_handler.mp (seq_cons.mp hc).2.1)).1, rfl⟩
  | returnCallRefFrameAddr hcr => exact ⟨seq_returnFrameAddr hM hcr hc, rfl⟩
  | callIndirect => exact ⟨seq_callIndirect hc, rfl⟩
  | returnCallIndirect => exact ⟨seq_returnCallIndirect hc, rfl⟩
  | brLabelZero =>
    exact ⟨(seq_vals_append _ _).mpr (seq_expression (aOk_label.mp (seq_cons.mp hc).2.1).1), rfl⟩
  | _ =>
    exact ⟨by simp [seq_append, lastS_append, PlainOk, instrB, flatOk, constI32, Val.i32],
      rfl⟩

end Silmaril.Proofs.Wasm.Det.NoMem
