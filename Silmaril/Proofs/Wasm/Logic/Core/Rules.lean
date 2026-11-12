module

public import Silmaril.Proofs.Wasm.Logic.Core.Context

/-!
# The rules of the Core 3.0 weakest-precondition calculus

* structural: `WP.mono`, `WP.steps`, `WP.step`, `wp_vals`, `wp_seq`, `wp_prefix`;
* final forms: `wp_br`, `wp_return`, `wp_trap`, `wp_throwing`;
* control: `wp_brIf_true`, `wp_brIf_false`, `wp_brIf_bool32`, `wp_brTable_lt`,
  `wp_brTable_ge`, `wp_label`, `wp_block`, `wp_loop` (an invariant indexed by a
  measure), `wp_if_true`, `wp_if_false` and their `_cons` forms;
* exceptions (Wasm 3.0): `wp_throw`, `wp_throwRef_null`, `wp_handler`,
  `wp_tryTable`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Basic properties -/

/-- A normal outcome of `WP` is a run to values. -/
theorem WP.normal_steps {s : Store H} {f : Frame} {code : List Admin} {Q : Post H}
    (h : WP P host s f code fun s' f' o => ∃ vs, o = .normal vs ∧ Q s' f' o) :
    ∃ s' f' vs, Steps P host ⟨s, f, code⟩ ⟨s', f', vals vs⟩ ∧ Q s' f' (.normal vs) := by
  obtain ⟨s', f', c', o, hs, he, vs, rfl, hq⟩ := h
  have hc : c' = vals vs := he
  exact ⟨s', f', vs, hc ▸ hs, hq⟩

theorem WP.mono {s : Store H} {f : Frame} {code : List Admin} {Q Q' : Post H}
    (h : WP P host s f code Q) (hQ : ∀ s f o, Q s f o → Q' s f o) : WP P host s f code Q' := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  exact ⟨s', f', c', o, hs, he, hQ _ _ _ hq⟩

/-- Run some steps first. -/
theorem WP.steps {s s' : Store H} {f f' : Frame} {c c' : List Admin} {Q : Post H}
    (hs : Steps P host ⟨s, f, c⟩ ⟨s', f', c'⟩) (h : WP P host s' f' c' Q) :
    WP P host s f c Q := by
  obtain ⟨s'', f'', c'', o, hs', he, hq⟩ := h
  exact ⟨s'', f'', c'', o, hs.trans hs', he, hq⟩

/-- Take one step first. -/
theorem WP.step {s s' : Store H} {f f' : Frame} {c c' : List Admin} {Q : Post H}
    (hs : Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩) (h : WP P host s' f' c' Q) :
    WP P host s f c Q :=
  WP.steps (.single hs) h

/-! ## Final forms -/

/-- Values are a final form. -/
theorem wp_vals {s : Store H} {f : Frame} {vs : List Val} {Q : Post H}
    (h : Q s f (.normal vs)) : WP P host s f (vals vs) Q :=
  ⟨s, f, vals vs, .normal vs, .refl, rfl, h⟩

/-- `br x` is a final form. -/
theorem wp_br {s : Store H} {f : Frame} {vs : List Val} {x : LabelIdx} {rest : List Admin}
    {Q : Post H} (h : Q s f (.br x.toNat vs)) :
    WP P host s f (vals vs ++ .plain (.br x) :: rest) Q :=
  ⟨s, f, vals vs ++ .plain (.br x) :: rest, .br x.toNat vs, .refl,
    Exists.intro x (Exists.intro rest ⟨rfl, rfl⟩), h⟩

/-- `return` is a final form. -/
theorem wp_return {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin} {Q : Post H}
    (h : Q s f (.ret vs)) : WP P host s f (vals vs ++ .plain .return_ :: rest) Q :=
  ⟨s, f, vals vs ++ .plain .return_ :: rest, .ret vs, .refl, Exists.intro rest rfl, h⟩

/-- A trap among values and before other code collapses to `trap`. -/
theorem steps_trap (s : Store H) (f : Frame) (vs : List Val) (rest : List Admin) :
    Steps P host ⟨s, f, vals vs ++ .trap :: rest⟩ ⟨s, f, [.trap]⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · have e : vals vs ++ .trap :: rest = vals vs ++ [.trap] ++ rest := by simp
    rw [e]
    exact .single (Step.trapInstrs hne)
  · have hv : vs = [] ∧ rest = [] := by simpa only [ne_eq, not_or, Decidable.not_not] using hne
    rw [hv.1, hv.2]
    exact .refl

/-- A throw among values and before other code collapses to `throwing a`. -/
theorem steps_throwing (s : Store H) (f : Frame) (vs : List Val) (a : Nat) (rest : List Admin) :
    Steps P host ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact .single (Step.throwRefInstrs hne)
  · have hv : vs = [] ∧ rest = [] := by simpa only [ne_eq, not_or, Decidable.not_not] using hne
    rw [hv.1, hv.2]
    exact .refl

/-- A trap is a final form. -/
theorem wp_trap {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin} {Q : Post H}
    (h : Q s f .trap) : WP P host s f (vals vs ++ .trap :: rest) Q :=
  WP.steps (steps_trap s f vs rest) ⟨s, f, [.trap], .trap, .refl, rfl, h⟩

/-- A thrown exception is a final form. -/
theorem wp_throwing {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {rest : List Admin}
    {Q : Post H} (h : Q s f (.throw a)) : WP P host s f (vals vs ++ throwing a ++ rest) Q :=
  WP.steps (steps_throwing s f vs a rest) ⟨s, f, throwing a, .throw a, .refl, rfl, h⟩

/-! ## Sequencing and the value stack -/

/-- A final form followed by more code, for an outcome other than falling through. -/
theorem wp_append_abrupt {s : Store H} {f : Frame} {c c₂ : List Admin} {o : Outcome}
    {Q : Post H} (he : o.Ends c) (hn : ∀ vs, o ≠ .normal vs) (hq : Q s f o) :
    WP P host s f (c ++ c₂) Q := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact absurd rfl (hn vs)
  · obtain ⟨x, rest, hx, rfl⟩ := he
    exact ⟨_, _, _, .br l vs, .refl, ⟨x, rest ++ c₂, hx, by simp⟩, hq⟩
  · obtain ⟨rest, rfl⟩ := he
    exact ⟨_, _, _, .ret vs, .refl, ⟨rest ++ c₂, by simp⟩, hq⟩
  · have hc : c ++ c₂ = vals [] ++ .trap :: c₂ := by
      rw [show c = [.trap] from he]; rfl
    exact hc ▸ wp_trap hq
  · have hc : c ++ c₂ = vals [] ++ throwing a ++ c₂ := by
      rw [show c = throwing a from he]; rfl
    exact hc ▸ wp_throwing hq
  · obtain ⟨hr, rest, rfl⟩ := he
    exact ⟨_, _, _, .tail vs a r, .refl, ⟨hr, rest ++ c₂, by simp⟩, hq⟩

/-- **Sequencing** (Wasm Logic `[seq]`, Figure 10). -/
theorem wp_seq {s : Store H} {f : Frame} {c₁ c₂ : List Admin} {Q : Post H}
    (h : WP P host s f c₁ (seqPost P host c₂ Q)) : WP P host s f (c₁ ++ c₂) Q := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  refine WP.steps (Steps.append c₂ hs) ?_
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · have hc : c' = vals vs := he
    exact hc ▸ hq
  all_goals exact wp_append_abrupt he (fun _ h => by cases h) hq

/-- A final form with values below it. -/
theorem Outcome.Ends.prepend {vs₀ : List Val} {o : Outcome} {c : List Admin} (he : o.Ends c) :
    (o.prepend vs₀).Ends (vals vs₀ ++ c) ∨
      (∃ a, o = .throw a ∧ c = throwing a) ∨ (o = .trap ∧ c = [.trap]) := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · have hc : c = vals vs := he
    refine .inl ?_
    show vals vs₀ ++ c = vals (vs₀ ++ vs)
    rw [hc, vals_append]
  · obtain ⟨x, rest, hx, rfl⟩ := he
    exact .inl ⟨x, rest, hx, by simp⟩
  · obtain ⟨rest, rfl⟩ := he
    exact .inl ⟨rest, by simp⟩
  · exact .inr (.inr ⟨rfl, he⟩)
  · exact .inr (.inl ⟨a, rfl, he⟩)
  · obtain ⟨hr, rest, rfl⟩ := he
    exact .inl ⟨hr, rest, by simp⟩

/-- **Stack framing**: values below the code are carried along. -/
theorem wp_prefix {s : Store H} {f : Frame} {vs₀ : List Val} {c : List Admin} {Q : Post H}
    (h : WP P host s f c fun s' f' o => Q s' f' (o.prepend vs₀)) :
    WP P host s f (vals vs₀ ++ c) Q := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  have hs' : Steps P host ⟨s, f, vals vs₀ ++ c⟩ ⟨s', f', vals vs₀ ++ c'⟩ := by
    simpa only [List.append_nil] using Steps.ctx vs₀ [] hs
  refine WP.steps hs' ?_
  rcases he.prepend (vs₀ := vs₀) with he' | ⟨a, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨s', f', _, o.prepend vs₀, .refl, he', hq⟩
  · simpa only [List.append_nil] using wp_throwing (rest := []) hq
  · exact wp_trap (rest := []) hq

/-! ## Branches -/

/-- `br_if` taken. -/
theorem wp_brIf_true {s : Store H} {f : Frame} {vs : List Val} {c : BitVec 32} {l : LabelIdx}
    {rest : List Admin} {Q : Post H} (hc : c ≠ 0) (h : Q s f (.br l.toNat vs)) :
    WP P host s f (vals (vs ++ [Val.i32 c]) ++ .plain (.brIf l) :: rest) Q := by
  have e : vals (vs ++ [Val.i32 c]) ++ .plain (.brIf l) :: rest =
      vals vs ++ [constI32 c, .plain (.brIf l)] ++ rest := by simp [vals, constI32]
  rw [e]
  exact WP.step (Step.ctx vs rest (Step.brIfTrue hc))
    (by rw [List.append_assoc, List.singleton_append]; exact wp_br h)

/-- `br_if` not taken. -/
theorem wp_brIf_false {s : Store H} {f : Frame} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} {Q : Post H} (h : WP P host s f (vals vs ++ rest) Q) :
    WP P host s f (vals (vs ++ [Val.i32 0]) ++ .plain (.brIf l) :: rest) Q := by
  have e : vals (vs ++ [Val.i32 0]) ++ .plain (.brIf l) :: rest =
      vals vs ++ [constI32 0, .plain (.brIf l)] ++ rest := by simp [vals, constI32]
  rw [e]
  refine WP.step (Step.ctx vs rest Step.brIfFalse) ?_
  rw [List.append_nil]
  exact h

/-- `br_if` on a Boolean flag, the form comparisons produce (`intRelOp = bool32 _`). -/
theorem wp_brIf_bool32 {s : Store H} {f : Frame} {vs : List Val} {b : Bool} {l : LabelIdx}
    {rest : List Admin} {Q : Post H}
    (h : if b then Q s f (.br l.toNat vs) else WP P host s f (vals vs ++ rest) Q) :
    WP P host s f (vals (vs ++ [Val.i32 (bool32 b)]) ++ .plain (.brIf l) :: rest) Q := by
  cases b
  · exact wp_brIf_false h
  · exact wp_brIf_true (by decide) h

/-- `br_table` with an index inside the table. -/
theorem wp_brTable_lt {s : Store H} {f : Frame} {vs : List Val} {i : BitVec 32}
    {ls : List LabelIdx} {d l : LabelIdx} {rest : List Admin} {Q : Post H}
    (hi : ls[i.toNat]? = some l) (h : Q s f (.br l.toNat vs)) :
    WP P host s f (vals (vs ++ [Val.i32 i]) ++ .plain (.brTable ls d) :: rest) Q := by
  have e : vals (vs ++ [Val.i32 i]) ++ .plain (.brTable ls d) :: rest =
      vals vs ++ [constI32 i, .plain (.brTable ls d)] ++ rest := by simp [vals, constI32]
  rw [e]
  exact WP.step (Step.ctx vs rest (Step.brTableLt hi))
    (by rw [List.append_assoc, List.singleton_append]; exact wp_br h)

/-- `br_table` with an index past the table takes the default label. -/
theorem wp_brTable_ge {s : Store H} {f : Frame} {vs : List Val} {i : BitVec 32}
    {ls : List LabelIdx} {d : LabelIdx} {rest : List Admin} {Q : Post H}
    (hi : ls.length ≤ i.toNat) (h : Q s f (.br d.toNat vs)) :
    WP P host s f (vals (vs ++ [Val.i32 i]) ++ .plain (.brTable ls d) :: rest) Q := by
  have e : vals (vs ++ [Val.i32 i]) ++ .plain (.brTable ls d) :: rest =
      vals vs ++ [constI32 i, .plain (.brTable ls d)] ++ rest := by simp [vals, constI32]
  rw [e]
  exact WP.step (Step.ctx vs rest (Step.brTableGe hi))
    (by rw [List.append_assoc, List.singleton_append]; exact wp_br h)

/-! ## Labels -/

section Label

variable {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {Q : Post H}

theorem label_br_zero {x : LabelIdx} {vs : List Val} {rest : List Admin} (hx : x.toNat = 0)
    (hq : labelPost P host n cont Q s f (.br 0 vs)) :
    WP P host s f [.label n cont (vals vs ++ .plain (.br x) :: rest)] Q := by
  obtain ⟨vs₁, vs₂, rfl, hn, hw⟩ := hq
  have e : vals (vs₁ ++ vs₂) ++ .plain (.br x) :: rest =
      vals vs₁ ++ vals vs₂ ++ [.plain (.br x)] ++ rest := by simp
  rw [e]
  exact WP.step (Step.brLabelZero hx hn) hw

theorem label_br_succ {x : LabelIdx} {l : Nat} {vs : List Val} {rest : List Admin}
    (hx : x.toNat = l + 1) (hq : labelPost P host n cont Q s f (.br (l + 1) vs)) :
    WP P host s f [.label n cont (vals vs ++ .plain (.br x) :: rest)] Q := by
  have hl : (labelPred x).toNat = l := by
    show x.toNat - 1 = l
    omega
  have hq' : Q s f (.br (labelPred x).toNat vs) := by rw [hl]; exact hq
  have st : Step P host ⟨s, f, [.label n cont (vals vs ++ .plain (.br x) :: rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br (labelPred x))]⟩ := by
    simpa only [List.append_assoc, List.singleton_append] using
      Step.brLabelSucc (P := P) (host := host) (s := s) (f := f) (n := n) (cont := cont)
        (vs := vs) (l := x) (rest := rest) (by omega)
  exact WP.step st (wp_br (rest := []) hq')

theorem label_ret {vs : List Val} {rest : List Admin}
    (hq : labelPost P host n cont Q s f (.ret vs)) :
    WP P host s f [.label n cont (vals vs ++ .plain .return_ :: rest)] Q := by
  have st : Step P host ⟨s, f, [.label n cont (vals vs ++ .plain .return_ :: rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩ := by
    simpa only [List.append_assoc, List.singleton_append] using
      Step.returnLabel (P := P) (host := host) (s := s) (f := f) (n := n) (cont := cont)
        (vs := vs) (rest := rest)
  exact WP.step st (wp_return (rest := []) hq)

theorem label_trap (hq : labelPost P host n cont Q s f .trap) :
    WP P host s f [.label n cont [.trap]] Q :=
  WP.step .trapLabel ⟨s, f, [.trap], .trap, .refl, rfl, hq⟩

theorem label_throw {a : Nat} (hq : labelPost P host n cont Q s f (.throw a)) :
    WP P host s f [.label n cont (throwing a)] Q :=
  WP.step .throwRefLabel ⟨s, f, throwing a, .throw a, .refl, rfl, hq⟩

/-- The code of a tail call, with the function reference among the values. -/
theorem tail_code (vs : List Val) (a : Nat) (r : Admin) (rest : List Admin) :
    vals vs ++ .ref (.func a) :: r :: rest = vals (vs ++ [.ref (.func a)]) ++ [r] ++ rest := by
  simp [vals, Val.toAdmin]

/-- A tail call leaves the label. -/
theorem label_tail {vs : List Val} {a : Nat} {r : Admin} {rest : List Admin}
    (hr : r.IsReturnCallRef) (hq : labelPost P host n cont Q s f (.tail vs a r)) :
    WP P host s f [.label n cont (vals vs ++ .ref (.func a) :: r :: rest)] Q := by
  have st : Step P host ⟨s, f, [.label n cont (vals vs ++ .ref (.func a) :: r :: rest)]⟩
      ⟨s, f, vals (vs ++ [.ref (.func a)]) ++ [r]⟩ := by
    rw [tail_code]
    exact .returnCallRefLabel hr
  have he : (Outcome.tail vs a r).Ends (vals (vs ++ [.ref (.func a)]) ++ [r]) :=
    ⟨hr, [], by simp [vals, Val.toAdmin]⟩
  exact WP.step st ⟨s, f, _, _, .refl, he, hq⟩

/-- A final form inside a label. -/
theorem label_ends {c : List Admin} {o : Outcome} (he : o.Ends c)
    (hq : labelPost P host n cont Q s f o) : WP P host s f [.label n cont c] Q := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · have hc : c = vals vs := he
    exact hc ▸ WP.step .labelVals (wp_vals hq)
  · obtain ⟨x, rest, hx, rfl⟩ := he
    exact label_br_zero hx hq
  · obtain ⟨x, rest, hx, rfl⟩ := he
    exact label_br_succ hx hq
  · obtain ⟨rest, rfl⟩ := he
    exact label_ret hq
  · exact (show c = [.trap] from he) ▸ label_trap hq
  · exact (show c = throwing a from he) ▸ label_throw hq
  · obtain ⟨hr, rest, rfl⟩ := he
    exact label_tail hr hq

/-- **Labels**: the common core of `wp_block` and `wp_loop`. -/
theorem wp_label {code : List Admin} (h : WP P host s f code (labelPost P host n cont Q)) :
    WP P host s f [.label n cont code] Q := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  exact WP.steps (Steps.label n cont hs) (label_ends he hq)

end Label

/-! ## Blocks, loops and conditionals -/

/-- A block's postcondition, as the postcondition of its label. -/
theorem blockPost_labelPost {n : Nat} {Q : Post H} {s : Store H} {f : Frame} {o : Outcome}
    (hq : blockPost n Q s f o) : labelPost P host n [] Q s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact hq
  · obtain ⟨vs₁, vs₂, h₁, h₂, h₃⟩ := hq
    refine ⟨vs₁, vs₂, h₁, h₂, ?_⟩
    show WP P host s f (vals vs₂ ++ expression []) Q
    simpa only [expression, List.map_nil, List.append_nil] using wp_vals h₃
  all_goals exact hq

/-- **`block`** (Wasm Logic `[block]`): the label's postcondition is the block's. -/
theorem wp_block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List CValType} {Q : Post H} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length)
    (h : WP P host s f (vals vs ++ expression body) (blockPost t₂.length Q)) :
    WP P host s f (vals vs ++ [.plain (.block bt body)]) Q :=
  WP.step (Step.block hbt hm) (wp_label (h.mono fun _ _ _ => blockPost_labelPost))

/-- A loop body's postcondition, as the postcondition of the loop's label, given the
loop rule at smaller measures. -/
theorem loopPost_labelPost {bt : BlockType} {body : List Instr} {t₁ : List CValType}
    {Q : Post H} {Inv : Nat → Store H → Frame → List Val → Prop} {m : Nat}
    (ih : ∀ k < m, ∀ {s f vs}, Inv k s f vs →
      WP P host s f (vals vs ++ [.plain (.loop bt body)]) Q)
    {s : Store H} {f : Frame} {o : Outcome} (hq : loopPost t₁.length Inv m Q s f o) :
    labelPost P host t₁.length [.loop bt body] Q s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact hq
  · obtain ⟨vs₁, vs₂, k, h₁, h₂, hk, hinv⟩ := hq
    exact ⟨vs₁, vs₂, h₁, h₂, ih k hk hinv⟩
  all_goals exact hq

/-- **`loop`** (Wasm Logic `[loop]`, for total correctness): an invariant `Inv m`
indexed by a measure `m`; each iteration that branches back re-establishes it at
a smaller measure. -/
theorem wp_loop {bt : BlockType} {body : List Instr} {t₁ t₂ : List CValType} {Q : Post H}
    (Inv : Nat → Store H → Frame → List Val → Prop)
    (hbt : ∀ m s f vs, Inv m s f vs →
      f.module.blockType? bt = some (t₁, t₂) ∧ vs.length = t₁.length)
    (hbody : ∀ m s f vs, Inv m s f vs →
      WP P host s f (vals vs ++ expression body) (loopPost t₁.length Inv m Q))
    {m : Nat} {s : Store H} {f : Frame} {vs : List Val} (h : Inv m s f vs) :
    WP P host s f (vals vs ++ [.plain (.loop bt body)]) Q := by
  induction m using Nat.strong_induction_on generalizing s f vs with
  | _ m ih =>
  obtain ⟨hb, hm⟩ := hbt m s f vs h
  exact WP.step (Step.loop hb hm) (wp_label ((hbody m s f vs h).mono fun _ _ _ =>
    loopPost_labelPost fun k hk _ _ _ hinv => ih k hk hinv))

/-- `if` with a non-zero condition, followed by more code. -/
theorem wp_if_true_cons {s : Store H} {f : Frame} {vs : List Val} {c : BitVec 32}
    {bt : BlockType} {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H} (hc : c ≠ 0)
    (h : WP P host s f (vals vs ++ .plain (.block bt b₁) :: rest) Q) :
    WP P host s f (vals (vs ++ [Val.i32 c]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q := by
  have e : vals (vs ++ [Val.i32 c]) ++ .plain (.if_ bt b₁ b₂) :: rest =
      vals vs ++ [constI32 c, .plain (.if_ bt b₁ b₂)] ++ rest := by simp [vals, constI32]
  rw [e]
  exact WP.step (Step.ctx vs rest (Step.ifTrue hc))
    (by rw [List.append_assoc, List.singleton_append]; exact h)

/-- `if` with a zero condition, followed by more code. -/
theorem wp_if_false_cons {s : Store H} {f : Frame} {vs : List Val}
    {bt : BlockType} {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H}
    (h : WP P host s f (vals vs ++ .plain (.block bt b₂) :: rest) Q) :
    WP P host s f (vals (vs ++ [Val.i32 0]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q := by
  have e : vals (vs ++ [Val.i32 0]) ++ .plain (.if_ bt b₁ b₂) :: rest =
      vals vs ++ [constI32 0, .plain (.if_ bt b₁ b₂)] ++ rest := by simp [vals, constI32]
  rw [e]
  exact WP.step (Step.ctx vs rest Step.ifFalse)
    (by rw [List.append_assoc, List.singleton_append]; exact h)

/-- `if` with a non-zero condition runs the `then` branch as a block. -/
theorem wp_if_true {s : Store H} {f : Frame} {vs : List Val} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} {Q : Post H} (hc : c ≠ 0)
    (h : WP P host s f (vals vs ++ [.plain (.block bt b₁)]) Q) :
    WP P host s f (vals (vs ++ [Val.i32 c]) ++ [.plain (.if_ bt b₁ b₂)]) Q :=
  wp_if_true_cons (rest := []) hc h

/-- `if` with a zero condition runs the `else` branch as a block. -/
theorem wp_if_false {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {b₁ b₂ : List Instr} {Q : Post H}
    (h : WP P host s f (vals vs ++ [.plain (.block bt b₂)]) Q) :
    WP P host s f (vals (vs ++ [Val.i32 0]) ++ [.plain (.if_ bt b₁ b₂)]) Q :=
  wp_if_false_cons (rest := []) h

/-! ## The forms the tactics use

A block, loop or conditional is usually followed by more code. These forms put
the continuation `rest` into the label's postcondition (`seqPost`), so that the
tactics (`wasm_block`, `wasm_loop`, `wasm_if`) apply to the goal as it stands. -/

/-- `wp_block` followed by more code. -/
theorem wp_block_cons {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {rest : List Admin} {t₁ t₂ : List CValType} {Q : Post H}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (h : WP P host s f (vals vs ++ expression body)
      (blockPost t₂.length (seqPost P host rest Q))) :
    WP P host s f (vals vs ++ .plain (.block bt body) :: rest) Q := by
  have e : vals vs ++ .plain (.block bt body) :: rest =
      (vals vs ++ [.plain (.block bt body)]) ++ rest := by simp
  rw [e]
  exact wp_seq (wp_block hbt hm h)

/-- `wp_loop` followed by more code. -/
theorem wp_loop_cons {bt : BlockType} {body : List Instr} {rest : List Admin}
    {t₁ t₂ : List CValType} {Q : Post H}
    (Inv : Nat → Store H → Frame → List Val → Prop)
    (hbt : ∀ m s f vs, Inv m s f vs →
      f.module.blockType? bt = some (t₁, t₂) ∧ vs.length = t₁.length)
    (hbody : ∀ m s f vs, Inv m s f vs →
      WP P host s f (vals vs ++ expression body)
        (loopPost t₁.length Inv m (seqPost P host rest Q)))
    {m : Nat} {s : Store H} {f : Frame} {vs : List Val} (h : Inv m s f vs) :
    WP P host s f (vals vs ++ .plain (.loop bt body) :: rest) Q := by
  have e : vals vs ++ .plain (.loop bt body) :: rest =
      (vals vs ++ [.plain (.loop bt body)]) ++ rest := by simp
  rw [e]
  exact wp_seq (wp_loop (t₂ := t₂) Inv hbt hbody h)

/-- `if` on a Boolean flag, followed by more code. -/
theorem wp_if_bool32_cons {s : Store H} {f : Frame} {vs : List Val} {b : Bool} {bt : BlockType}
    {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H}
    (h : WP P host s f (vals vs ++ .plain (.block bt (if b then b₁ else b₂)) :: rest) Q) :
    WP P host s f (vals (vs ++ [Val.i32 (bool32 b)]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q := by
  cases b
  · exact wp_if_false_cons h
  · exact wp_if_true_cons (by decide) h

/-! ## Exceptions -/

/-- **`throw x`**: allocate the exception with the top values as fields and throw it. -/
theorem wp_throw {s : Store H} {f : Frame} {x : TagIdx} {vs₀ vs : List Val} {ta : Nat}
    {ti : TagInst} {ts : Ty (.list .val)} {rest : List Admin} {Q : Post H}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : vs.length = ts.length) (h : Q (s.addExn ⟨ta, vs⟩) f (.throw s.exns.length)) :
    WP P host s f (vals (vs₀ ++ vs) ++ .plain (.throw x) :: rest) Q := by
  have e : vals (vs₀ ++ vs) ++ .plain (.throw x) :: rest =
      vals vs₀ ++ (vals vs ++ [.plain (.throw x)]) ++ rest := by simp
  rw [e]
  refine WP.step (Step.ctx vs₀ rest (Step.throw (P := P) (host := host) ht he hn)) ?_
  exact wp_throwing h

/-- `throw_ref` on a null reference traps. -/
theorem wp_throwRef_null {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    {Q : Post H} (h : Q s f .trap) :
    WP P host s f (vals (vs ++ [.ref .null]) ++ .plain .throwRef :: rest) Q := by
  have e : vals (vs ++ [.ref .null]) ++ .plain .throwRef :: rest =
      vals vs ++ [.ref .null, .plain .throwRef] ++ rest := by simp [vals, Val.toAdmin]
  rw [e]
  refine WP.step (Step.ctx vs rest Step.throwRefNull) ?_
  simpa only [List.append_assoc, List.singleton_append] using wp_trap (vs := vs) (rest := rest) h

/-- An exception reaching the catch clauses `cs` of a handler. -/
theorem handler_throw {s : Store H} {f : Frame} {n : Nat} {a : Nat} {Q : Post H}
    (cs : List Catch) (hq : catchPost s f a Q cs) :
    WP P host s f [.handler n cs (throwing a)] Q := by
  induction cs with
  | nil => exact WP.step .throwRefHandlerEmpty ⟨s, f, throwing a, .throw a, .refl, rfl, hq⟩
  | cons c cs ih =>
    rcases hq with ⟨hm, hc⟩ | ⟨hm, hcs⟩
    · exact handler_caught c hm hc
    · exact WP.step (.throwRefHandlerNext hm) (ih hcs)
where
  /-- The first clause catches. -/
  handler_caught {cs : List Catch} (c : Catch) (hm : CatchMatches s f a c)
      (hc : caughtPost s f a Q c) : WP P host s f [.handler n (c :: cs) (throwing a)] Q := by
    rcases c with ⟨x, l⟩ | ⟨x, l⟩ | l | l
    · obtain ⟨e, ta, he, ht, rfl⟩ := hm
      obtain ⟨e', he', hq⟩ := hc
      have hee : e' = e := Option.some.inj (he'.symm.trans he)
      exact WP.step (.throwRefHandlerCatch he ht) (wp_br (rest := []) (hee ▸ hq))
    · obtain ⟨e, ta, he, ht, rfl⟩ := hm
      obtain ⟨e', he', hq⟩ := hc
      have hee : e' = e := Option.some.inj (he'.symm.trans he)
      have hcode : vals e.fields ++ [.ref (.exn a), .plain (.br l)] =
          vals (e.fields ++ [.ref (.exn a)]) ++ [.plain (.br l)] := by simp [vals, Val.toAdmin]
      exact WP.step (.throwRefHandlerCatchRef he ht) (hcode ▸ wp_br (rest := []) (hee ▸ hq))
    · exact WP.step .throwRefHandlerCatchAll (wp_br (vs := []) (rest := []) hc)
    · have hcode : [Admin.ref (.exn a), .plain (.br l)] =
          vals [.ref (.exn a)] ++ [.plain (.br l)] := rfl
      exact WP.step .throwRefHandlerCatchAllRef (hcode ▸ wp_br (rest := []) hc)

/-- A final form inside an exception handler. -/
theorem handler_ends {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {Q : Post H}
    {c : List Admin} {o : Outcome} (he : o.Ends c) (hq : handlerPost cs Q s f o) :
    WP P host s f [.handler n cs c] Q := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · have hc : c = vals vs := he
    exact hc ▸ WP.step .handlerVals (wp_vals hq)
  · obtain ⟨x, rest, hx, rfl⟩ := he
    have st : Step P host ⟨s, f, [.handler n cs (vals vs ++ .plain (.br x) :: rest)]⟩
        ⟨s, f, vals vs ++ [.plain (.br x)]⟩ := by
      simpa only [List.append_assoc, List.singleton_append] using
        Step.brHandler (P := P) (host := host) (s := s) (f := f) (n := n) (cs := cs)
          (vs := vs) (l := x) (rest := rest)
    exact WP.step st (wp_br (rest := []) (hx ▸ hq))
  · obtain ⟨rest, rfl⟩ := he
    have st : Step P host ⟨s, f, [.handler n cs (vals vs ++ .plain .return_ :: rest)]⟩
        ⟨s, f, vals vs ++ [.plain .return_]⟩ := by
      simpa only [List.append_assoc, List.singleton_append] using
        Step.returnHandler (P := P) (host := host) (s := s) (f := f) (n := n) (cs := cs)
          (vs := vs) (rest := rest)
    exact WP.step st (wp_return (rest := []) hq)
  · exact (show c = [.trap] from he) ▸ WP.step .trapHandler ⟨s, f, [.trap], .trap, .refl, rfl, hq⟩
  · exact (show c = throwing a from he) ▸ handler_throw cs hq
  · obtain ⟨hr, rest, rfl⟩ := he
    have st : Step P host ⟨s, f, [.handler n cs (vals vs ++ .ref (.func a) :: r :: rest)]⟩
        ⟨s, f, vals (vs ++ [.ref (.func a)]) ++ [r]⟩ := by
      rw [tail_code]
      exact .returnCallRefHandler hr
    have he : (Outcome.tail vs a r).Ends (vals (vs ++ [.ref (.func a)]) ++ [r]) :=
      ⟨hr, [], by simp [vals, Val.toAdmin]⟩
    exact WP.step st ⟨s, f, _, _, .refl, he, hq⟩

/-- **Exception handlers**: the code inside `handler n cs` ends with an outcome that,
when it is a throw, the clauses `cs` dispatch. -/
theorem wp_handler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {code : List Admin}
    {Q : Post H} (h : WP P host s f code (handlerPost cs Q)) :
    WP P host s f [.handler n cs code] Q := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  exact WP.steps (Steps.handler n cs hs) (handler_ends he hq)

/-- **`try_table`** (Wasm 3.0): the body runs as a block inside a handler for the
clauses `cs`; a branch from a clause targets a label outside the `try_table`. -/
theorem wp_tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType} {Q : Post H}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (h : WP P host s f (vals vs ++ expression body) (blockPost t₂.length (handlerPost cs Q))) :
    WP P host s f (vals vs ++ [.plain (.tryTable bt cs body)]) Q :=
  WP.step (Step.tryTable hbt hm)
    (wp_handler (wp_label (h.mono fun _ _ _ => blockPost_labelPost)))

/-- `wp_tryTable` followed by more code. -/
theorem wp_tryTable_cons {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {vs : List Val} {rest : List Admin} {t₁ t₂ : List CValType}
    {Q : Post H} (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (h : WP P host s f (vals vs ++ expression body)
      (blockPost t₂.length (handlerPost cs (seqPost P host rest Q)))) :
    WP P host s f (vals vs ++ .plain (.tryTable bt cs body) :: rest) Q := by
  have e : vals vs ++ .plain (.tryTable bt cs body) :: rest =
      (vals vs ++ [.plain (.tryTable bt cs body)]) ++ rest := by simp
  rw [e]
  exact wp_seq (wp_tryTable hbt hm h)

/-! ## Code as instructions -/

@[simp] theorem expression_append (is js : List Instr) :
    expression (is ++ js) = expression is ++ expression js := List.map_append

@[simp] theorem expression_cons (i : Instr) (is : List Instr) :
    expression (i :: is) = .plain i :: expression is := rfl

@[simp] theorem expression_nil : expression [] = [] := rfl

end Silmaril.Wasm.Logic.Core
