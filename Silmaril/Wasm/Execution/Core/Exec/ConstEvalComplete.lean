module

public import Silmaril.Wasm.Execution.Core.Exec.ConstEval

@[expose] public section

/-! # Completeness of the constant evaluator

If an expression of constant instructions (`Instr.IsConstI`) reduces to a
single value, then `evalConst?` computes exactly that store and value, and the
frame is unchanged (`evalConst?_complete`), for every profile and host.

Route: constant code only reduces by `ConstRedex` (`Step.const_redex`); each
such redex preserves the result of the evaluator's fold (`cfold_redex`), once
the leading value instructions of the expression are moved onto the value
stack (`cfold_normalize`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- The fold of `constExpr?` from an arbitrary stack. -/
def cfold (f : Frame) (s : Store H) (vs : List Val) (e : Expr) : Option (Store H × List Val) :=
  e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (s, vs)

theorem cfold_nil (f : Frame) (s : Store H) (vs : List Val) : cfold f s vs [] = some (s, vs) :=
  rfl

theorem cfold_cons (f : Frame) (s : Store H) (vs : List Val) (i : Instr) (e : Expr) :
    cfold f s vs (i :: e) = (constInstr? s f vs i).bind (fun st => cfold f st.1 st.2 e) := by
  simp [cfold, List.foldlM_cons]

theorem Val.toAdmin_inj {v w : Val} (h : v.toAdmin = w.toAdmin) : v = w := by
  have := congrArg Admin.val? h
  simpa using this

theorem vals_inj : ∀ {A B : List Val}, vals A = vals B → A = B
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [vals] at h
  | _ :: _, [], h => by simp [vals] at h
  | a :: A, b :: B, h => by
    simp only [vals_cons', List.cons.injEq] at h
    rw [Val.toAdmin_inj h.1, vals_inj h.2]

theorem not_mem_vals {x : Admin} (hx : x.val? = none) {ws : List Val} : x ∉ vals ws := by
  intro hm
  simp only [vals, List.mem_map] at hm
  obtain ⟨v, -, rfl⟩ := hm
  simp at hx

theorem vals_split_nonval {x y : Admin} (hx : x.val? = none) (hy : y.val? = none) :
    ∀ {A B : List Val} {X Y : List Admin},
      vals A ++ x :: X = vals B ++ y :: Y → A = B ∧ x = y ∧ X = Y
  | [], [], X, Y, h => by simpa using h
  | [], b :: B, X, Y, h => by
    simp only [vals_nil', List.nil_append, vals_cons', List.cons_append, List.cons.injEq] at h
    rw [h.1] at hx; simp at hx
  | a :: A, [], X, Y, h => by
    simp only [vals_nil', List.nil_append, vals_cons', List.cons_append, List.cons.injEq] at h
    rw [← h.1] at hy; simp at hy
  | a :: A, b :: B, X, Y, h => by
    simp only [vals_cons', List.cons_append, List.cons.injEq] at h
    obtain ⟨e₁, e₂⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := vals_split_nonval hx hy e₂
    exact ⟨by rw [Val.toAdmin_inj e₁], rfl, rfl⟩

theorem popN?_append (pre args : List Val) : popN? (pre ++ args) args.length = some (pre, args) := by
  unfold popN?
  simp

theorem pop1?_append (pre : List Val) (v : Val) : pop1? (pre ++ [v]) = some (pre, v) := by
  unfold pop1?
  have := popN?_append pre [v]
  simp only [List.length_singleton] at this
  simp [this]

theorem pop2?_append (pre : List Val) (v w : Val) : pop2? (pre ++ [v, w]) = some (pre, v, w) := by
  unfold pop2?
  have := popN?_append pre [v, w]
  simp only [List.length_cons, List.length_nil] at this
  simp [this]

theorem Val.int?_self (t : IntType) (x : BitVec t.width) : (Val.num ⟨.int t, x⟩).int? t = some x := by
  simp [Val.int?]

theorem Val.int?_i32 (b : BitVec 32) :
    Val.int? .i32 (.num ⟨.int .i32, b⟩ : Val) = some b := rfl

theorem expandStruct?_complete {d : DefType} {fs : Ty (.list .field)} (h : Expand d (.struct fs)) :
    expandStruct? d = some fs := by
  unfold expandStruct?; rw [Expand.iff.1 h]

theorem expandArray?_complete {d : DefType} {ft : CFieldType} (h : Expand d (.array ft)) :
    expandArray? d = some ft := by
  unfold expandArray?; rw [Expand.iff.1 h]

theorem constInstr?_of_val {s : Store H} {f : Frame} {vs : List Val} {a : Instr} {v : Val}
    (h : (Admin.plain a).val? = some v) :
    constInstr? s f vs a = some (s, vs ++ [v]) ∧ v.toAdmin = .plain a := by
  cases a <;> simp [Admin.val?] at h <;> subst h <;> exact ⟨rfl, rfl⟩

/-- Move the leading value instructions of an expression onto the stack. -/
theorem cfold_normalize (f : Frame) :
    ∀ (e : Expr) (s : Store H) (vs : List Val), (∀ i ∈ e, i.IsConstI) →
      ∃ vs' e', cfold f s vs e = cfold f s vs' e' ∧
        vals vs ++ expression e = vals vs' ++ expression e' ∧ (∀ i ∈ e', i.IsConstI) ∧
        (e' = [] ∨ ∃ i e₁, e' = i :: e₁ ∧ (Admin.plain i).val? = none)
  | [], s, vs, _ => ⟨vs, [], rfl, rfl, by simp, Or.inl rfl⟩
  | a :: e, s, vs, hc => by
    cases hv : (Admin.plain a).val? with
    | none => exact ⟨vs, a :: e, rfl, rfl, hc, Or.inr ⟨a, e, rfl, hv⟩⟩
    | some v =>
      obtain ⟨h₁, h₂⟩ := constInstr?_of_val (s := s) (f := f) (vs := vs) hv
      obtain ⟨vs', e', r₁, r₂, r₃, r₄⟩ :=
        cfold_normalize f e s (vs ++ [v]) (fun i hi => hc i (by simp [hi]))
      refine ⟨vs', e', ?_, ?_, r₃, r₄⟩
      · rw [cfold_cons, h₁, ← r₁]; rfl
      · rw [← r₂]; simp [expression, h₂]

theorem ConstRedex.not_val {s s₁ : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s₁ out) : (Admin.plain i).val? = none := by
  cases h <;> rfl

/-- A constant redex preserves the evaluator's fold. -/
theorem cfold_redex {s s₁ : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s₁ out) (hi : i.IsConstI) (pre : List Val)
    (e₁ : Expr) :
    ∃ ws₁ e₂, out = vals ws₁ ++ expression e₂ ∧ (∀ j ∈ e₂, j.IsConstI) ∧
      cfold f s (pre ++ w) (i :: e₁) = cfold f s₁ (pre ++ ws₁) (e₂ ++ e₁) := by
  cases h with
  | refNull ht =>
    refine ⟨[.ref .null], [], rfl, by simp, ?_⟩
    simp [cfold_cons, constInstr?]
  | refFunc ha =>
    refine ⟨[.ref (.func _)], [], rfl, by simp, ?_⟩
    simp [cfold_cons, constInstr?, ha]
  | refI31 b =>
    refine ⟨[.ref (.i31 (b.setWidth 31))], [], rfl, by simp, ?_⟩
    (simp [cfold_cons, constInstr?, pop1?_append, Val.i32, Val.int?_i32, Option.bind_some]); rfl
  | @structNew x d fs vs hd he hn hp =>
    refine ⟨[.ref (.struct s.structs.length)], [], rfl, by simp, ?_⟩
    simp [cfold_cons, constInstr?, structNew?, hd, expandStruct?_complete he, ← hn, popN?_append, List.all_eq_true.mpr hp]
  | @structNewDefault x d fs vs hd he hdef =>
    refine ⟨vs, [.structNew x], by simp [expression], by simp [Instr.IsConstI], ?_⟩
    simp [cfold_cons, constInstr?, hd, expandStruct?_complete he, hdef]
  | @arrayNew x v n =>
    refine ⟨List.replicate n.toNat v, [.arrayNewFixed x ⟨n.toNat, n.isLt⟩], by simp [expression],
      by simp [Instr.IsConstI], ?_⟩
    (simp [cfold_cons, constInstr?, pop2?_append, Val.i32, Val.int?_i32, Option.bind_some]); rfl
  | @arrayNewDefault x n d ft v hd he hv =>
    refine ⟨List.replicate n.toNat v, [.arrayNewFixed x ⟨n.toNat, n.isLt⟩], by simp [expression],
      by simp [Instr.IsConstI], ?_⟩
    (simp [cfold_cons, constInstr?, pop1?_append, Val.i32, Val.int?_i32, Option.bind_some, hd,
      expandArray?_complete he, hv]); rfl
  | @arrayNewFixed x n d ft vs hd he hn hp =>
    refine ⟨[.ref (.array s.arrays.length)], [], rfl, by simp, ?_⟩
    simp [cfold_cons, constInstr?, arrayNewFixed?, hd, expandArray?_complete he, ← hn, popN?_append]
    rw [ite_eq_left hp]; rfl
  | externConvertNull =>
    refine ⟨[.ref .null], [], rfl, by simp, ?_⟩
    simp [cfold_cons, constInstr?, pop1?_append]
  | @externConvertAddr r hr =>
    refine ⟨[.ref (.extern r)], [], rfl, by simp, ?_⟩
    simp [cfold_cons, constInstr?, pop1?_append, hr]
  | anyConvertNull =>
    refine ⟨[.ref .null], [], rfl, by simp, ?_⟩
    simp [cfold_cons, constInstr?, pop1?_append]
  | anyConvertAddr r =>
    refine ⟨[.ref r], [], rfl, by simp, ?_⟩
    simp [cfold_cons, constInstr?, pop1?_append]
  | @globalGet x a g hg =>
    refine ⟨[g.value], [], by simp [vals, expression], by simp, ?_⟩
    simp [cfold_cons, constInstr?, hg]
  | @binop t op x y z hz =>
    refine ⟨[.num ⟨.int t, z⟩], [], by simp [vals, Val.toAdmin, expression], by simp, ?_⟩
    have hop : constBinOp op = true := by
      simp only [Instr.IsConstI] at hi
      rcases hi with rfl | rfl | rfl <;> rfl
    simp [cfold_cons, constInstr?, hop, pop2?_append, Val.int?_self, hz]

section Complete

variable {P : Profile} {host : HostSemantics H}

theorem constOk_code {vs : List Val} {e : Expr} (hc : ∀ i ∈ e, i.IsConstI) :
    ∀ a ∈ vals vs ++ expression e, a.ConstOk := by
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · exact Admin.constOk_vals vs a ha
  · simp only [expression, List.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact hc i hi

theorem steps_cfold {c c' : Config H} (h : Steps P host c c') :
    ∀ {s : Store H} {f : Frame} {vs : List Val} {e : Expr},
      c = ⟨s, f, vals vs ++ expression e⟩ → (∀ i ∈ e, i.IsConstI) →
      ∀ {s' : Store H} {f' : Frame} {ws : List Val}, c' = ⟨s', f', vals ws⟩ →
        f' = f ∧ cfold f s vs e = some (s', ws) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f vs e hc₁ hc s' f' ws hc₂
    rw [hc₁] at hc₂
    simp only [Config.mk.injEq] at hc₂
    obtain ⟨rfl, rfl, hcode⟩ := hc₂
    refine ⟨rfl, ?_⟩
    obtain ⟨vs', e', r₁, r₂, -, r₄⟩ := cfold_normalize f e s vs hc
    rw [r₂] at hcode
    rcases r₄ with rfl | ⟨i, e₁, rfl, hi⟩
    · simp only [expression, List.map_nil, List.append_nil] at hcode
      rw [r₁, vals_inj hcode]; rfl
    · exfalso
      exact not_mem_vals hi (hcode ▸ (by simp [expression]) : Admin.plain i ∈ vals ws)
  | head hstep _ ih =>
    rename_i c c₁ _
    intro s f vs e hc₁ hc s' f' ws hc₂
    subst hc₁
    obtain ⟨hf, pre, w, i, post, out, e₁, e₂, hr⟩ := Step.const_redex hstep (constOk_code hc)
    obtain ⟨vs', e', r₁, r₂, r₃, r₄⟩ := cfold_normalize f e s vs hc
    simp only at e₁ hf
    rw [r₂] at e₁
    rcases r₄ with rfl | ⟨i', e₃, rfl, hi'⟩
    · exfalso
      simp only [expression, List.map_nil, List.append_nil] at e₁
      exact not_mem_vals hr.not_val (e₁ ▸ (by simp) : Admin.plain i ∈ vals vs')
    · have e₁' : vals vs' ++ Admin.plain i' :: expression e₃ =
          vals (pre ++ w) ++ Admin.plain i :: post := by
        simpa [expression, List.append_assoc] using e₁
      obtain ⟨rfl, hii, rfl⟩ := vals_split_nonval hi' hr.not_val e₁'
      cases hii
      have hi3 : ∀ j ∈ e₃, j.IsConstI := fun j hj => r₃ j (by simp [hj])
      obtain ⟨ws₁, e₄, ho, hc₄, hfold⟩ := cfold_redex hr (r₃ i (by simp)) pre e₃
      have hc₁ : c₁ = ⟨c₁.store, f, vals (pre ++ ws₁) ++ expression (e₄ ++ e₃)⟩ := by
        rcases c₁ with ⟨s₁, f₁, code₁⟩
        simp only at hf e₂ ⊢
        subst hf e₂ ho
        simp [expression, List.append_assoc]
      obtain ⟨hf', hres⟩ := ih hc₁ (by
        intro j hj; rcases List.mem_append.1 hj with hj | hj
        · exact hc₄ j hj
        · exact hi3 j hj) hc₂
      exact ⟨hf', by rw [r₁, hfold, hres]⟩

/-- **Completeness of `evalConst?`.** -/
theorem evalConst?_complete {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {e : Expr} {v : Val} (hc : ∀ i ∈ e, i.IsConstI)
    (h : EvalExpr P host s f e s' f' [v]) : f' = f ∧ evalConst? s f e = some (s', v) := by
  obtain ⟨hf, hr⟩ := steps_cfold (s := s) (f := f) (vs := []) (e := e) h (by simp) hc rfl
  refine ⟨hf, ?_⟩
  unfold evalConst? constExpr?
  have : e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (s, []) =
      some (s', [v]) := hr
  rw [this]

end Complete

end Silmaril.Wasm.Execution.Core
