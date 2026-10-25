module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic

@[expose] public section

/-! # Closure proof: `FRAME` heads

`tail_case`: the `return_call_ref-frame-*` bubbling, the related body lifted to the
same `return_call_ref` with the same arguments by `Closure.exit_lift`.
`frame_case`: a step at `val* (FRAME_n{fi} b) L`: `ctxt-frame` by `StepIH` in the
inner frame; `frame-vals`, `return-frame`, `trap-frame`, `throw_ref-frame` after
`Closure.exit_lift`; tail calls by `tail_case`.

The steps of a `FRAME` redex under values are classified by `FrameRedex`
(`Step.frame_redex_aux`). -/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type}

variable {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

variable {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

/-! ## Steps of a `FRAME` redex -/

/-- The steps of a `FRAME_n{fi} b` redex (`ctxt-frame`, `frame-vals`,
`return-frame`, `return_call_ref-frame-null/addr`, `throw_ref-frame`,
`trap-frame`), relating the store and frame before and after the step and the
result code. -/
inductive FrameRedex (P : Profile) (host : HostSemantics H) :
    Store H → Frame → Nat → Frame → List Admin → Store H → Frame → List Admin → Prop where
  | ctxt {s s' : Store H} {f fi fi' : Frame} {n : Nat} {b b' : List Admin}
      (h : Step P host ⟨s, fi, b⟩ ⟨s', fi', b'⟩) :
      FrameRedex P host s f n fi b s' f [.frame n fi' b']
  | values {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val} (hn : vs.length = n) :
      FrameRedex P host s f n fi (vals vs) s f (vals vs)
  | ret {s : Store H} {f fi : Frame} {n : Nat} {vs' vs : List Val} {rest : List Admin}
      (hn : vs.length = n) :
      FrameRedex P host s f n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest) s f (vals vs)
  | callNull {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val} {c : Admin}
      {rest : List Admin} (hc : c.IsReturnCallRef) :
      FrameRedex P host s f k fi (vals vs ++ [.ref .null, c] ++ rest) s f [.trap]
  | callAddr {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
      {c : Admin} {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
      (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
      (hn : vs.length = ps.length) :
      FrameRedex P host s f k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) s f
        (vals vs ++ [.ref (.func a), c.retToCallIn fi.module])
  | throw {s : Store H} {f fi : Frame} {n : Nat} {a : Nat} :
      FrameRedex P host s f n fi (throwing a) s f (throwing a)
  | trap {s : Store H} {f fi : Frame} {n : Nat} :
      FrameRedex P host s f n fi [.trap] s f [.trap]

theorem frame_eq {n n' : Nat} {fi fi' : Frame} {b b' : List Admin} {us : List Val}
    (hc : [Admin.frame n fi b] = vals us ++ [.frame n' fi' b']) :
    us = [] ∧ n = n' ∧ fi = fi' ∧ b = b' := by
  obtain ⟨h1, h2, -⟩ := vals_append_cons_inj (vs := []) (ws := us) (es := []) (fs := [])
    (a := .frame n fi b) (b := .frame n' fi' b') rfl rfl (by simpa [vals_nil'] using hc)
  simp only [Admin.frame.injEq] at h2
  exact ⟨h1.symm, h2⟩

theorem _root_.Silmaril.Wasm.Execution.Core.Admin.IsCallRef.not_isReturnCallRef {c : Admin}
    (h : c.IsCallRef) : ¬ c.IsReturnCallRef := by
  intro h'
  rcases Admin.isReturnCallRef_cases h' with ⟨x, rfl⟩ | ⟨d, rfl⟩ <;>
    simp [Admin.IsCallRef] at h

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- A step of `val* (FRAME_n{fi} b)` is a step of the `FRAME` redex under the values. -/
theorem Step.frame_redex_aux {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (n : Nat) (fi : Frame) (b : List Admin),
      c.code = vals us ++ [.frame n fi b] →
      ∃ is₀, c'.code = vals us ++ is₀ ∧
        FrameRedex P host c.store c.frame n fi b c'.store c'.frame is₀ := by
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us n fi b hc
    dsimp only at hc ⊢
    obtain ⟨u₁, e, is₁, he, rfl⟩ := exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ u₁) ++ e :: (is₁ ++ rest) = vals us ++ Admin.frame n fi b :: [] := by
      rw [← hc]; simp
    obtain ⟨h1, rfl, h3⟩ := vals_append_cons_inj he rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨is₀, his, hfr⟩ := ih u₁ n fi b (by simp)
    dsimp only at his hfr
    subst h1 his
    exact ⟨is₀, by simp, hfr⟩
  | @trapInstrs s f vs₀ rest hne =>
    intro us n fi b hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.frame n fi b :: [] := by
      rw [← hc]; simp
    exact absurd (vals_append_cons_inj val?_trap rfl hc').2.1 (by simp)
  | @throwRefInstrs s f vs₀ a rest hne =>
    intro us n fi b hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.frame n fi b :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    exact absurd (vals_append_cons_inj val?_throwRef rfl hc').2.1 (by simp)
  | ctxtFrame hs _ =>
    intro us n fi b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := frame_eq hc
    exact ⟨_, by simp [vals_nil'], .ctxt hs⟩
  | frameVals hn =>
    intro us n fi b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := frame_eq hc
    exact ⟨_, by simp [vals_nil'], .values hn⟩
  | returnFrame hn =>
    intro us n fi b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := frame_eq hc
    exact ⟨_, by simp [vals_nil'], .ret hn⟩
  | returnCallRefFrameNull hc₀ =>
    intro us n fi b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := frame_eq hc
    exact ⟨_, by simp [vals_nil'], .callNull hc₀⟩
  | returnCallRefFrameAddr hc₀ hf he hn =>
    intro us n fi b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := frame_eq hc
    exact ⟨_, by simp [vals_nil'], .callAddr hc₀ hf he hn⟩
  | throwRefFrame =>
    intro us n fi b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := frame_eq hc
    exact ⟨_, by simp [vals_nil'], .throw⟩
  | trapFrame =>
    intro us n fi b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := frame_eq hc
    exact ⟨_, by simp [vals_nil'], .trap⟩
  | _ =>
    intro us n fi b hc
    first
      | (have := congrArg List.getLast? hc; simp at this; done)
      | (have := congrArg List.getLast? hc; simp at this; subst this;
          simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]; done)
      | (rename_i hf; cases hf <;>
          (have := congrArg List.getLast? hc; simp [constI32, Val.i32, Val.toAdmin] at this) <;>
          done)

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `val* c` with `c` a `return_call_ref` does not step: the tail call bubbles only
through a `LABEL`, `HANDLER` or `FRAME`. -/
theorem Step.returnCallRef_stuck_aux {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (e : Admin), e.IsReturnCallRef → c.code = vals us ++ [e] → False := by
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us e he₀ hc
    dsimp only at hc
    obtain ⟨u₁, e', is₁, he', rfl⟩ := exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ u₁) ++ e' :: (is₁ ++ rest) = vals us ++ e :: [] := by
      rw [← hc]; simp
    obtain ⟨-, rfl, h3⟩ := vals_append_cons_inj he' (Admin.val?_of_isReturnCallRef he₀) hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    exact ih u₁ e' he₀ (by simp)
  | @trapInstrs s f vs₀ rest hne =>
    intro us e he₀ hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ e :: [] := by
      rw [← hc]; simp
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj val?_trap (Admin.val?_of_isReturnCallRef he₀) hc'
    exact he₀
  | @throwRefInstrs s f vs₀ a rest hne =>
    intro us e he₀ hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ e :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    obtain ⟨-, rfl, -⟩ :=
      vals_append_cons_inj val?_throwRef (Admin.val?_of_isReturnCallRef he₀) hc'
    exact he₀
  | _ =>
    intro us e he₀ hc
    first
      | (have := congrArg List.getLast? hc; simp at this; subst this;
          simp [Admin.IsReturnCallRef] at he₀; done)
      | (have := congrArg List.getLast? hc; simp at this; subst this;
          exact Admin.IsCallRef.not_isReturnCallRef ‹_› he₀)
      | (rename_i hf; cases hf <;>
          (have := congrArg List.getLast? hc; simp [constI32, Val.i32, Val.toAdmin] at this;
            subst this; simp [Admin.IsReturnCallRef] at he₀) <;>
          done)

/-! ## Lifting through contexts -/

theorem transGen_ctx {t t' : Store H} {f f' : Frame} {a b : List Admin}
    (h : Relation.TransGen (Step P host) ⟨t, f, a⟩ ⟨t', f', b⟩) (V : List Val)
    (L : List Admin) :
    Relation.TransGen (Step P host) ⟨t, f, vals V ++ a ++ L⟩ ⟨t', f', vals V ++ b ++ L⟩ :=
  Relation.TransGen.lift
    (fun c : Config H => (⟨c.store, c.frame, vals V ++ c.code ++ L⟩ : Config H))
    (fun a b (hs : Step P host a b) => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩
      exact Step.append_right (Step.vals_left hs V) L) _ _ h

theorem transGen_frame {t t' : Store H} {f fi fi' : Frame} {n : Nat} {a b : List Admin}
    (h : Relation.TransGen (Step P host) ⟨t, fi, a⟩ ⟨t', fi', b⟩) :
    Relation.TransGen (Step P host) ⟨t, f, [.frame n fi a]⟩ ⟨t', f, [.frame n fi' b]⟩ :=
  Relation.TransGen.lift
    (fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun a b (hs : Step P host a b) => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩
      exact Step.ctxtFrame hs) _ _ h

/-- An inner run to `x` followed by a `FRAME` exit step. -/
theorem exit_frame {t t' : Store H} {f fi : Frame} {n : Nat} {b x y : List Admin}
    (h₁ : Steps P host ⟨t, fi, b⟩ ⟨t', fi, x⟩)
    (h₂ : Step P host ⟨t', f, [.frame n fi x]⟩ ⟨t', f, y⟩) :
    Relation.TransGen (Step P host) ⟨t, f, [.frame n fi b]⟩ ⟨t', f, y⟩ :=
  Relation.TransGen.tail' (Steps.frame h₁) h₂

/-- A run to `val* k j`, with `k` a `trap` or a thrown exception, continues to `k`
by discarding the values and `j`. -/
theorem steps_discard {t t' : Store H} {fi : Frame} {b' : List Admin} {us : List Val}
    {k j : List Admin} (hk : k = [.trap] ∨ ∃ a, k = throwing a)
    (h : Steps P host ⟨t, fi, b'⟩ ⟨t', fi, vals us ++ k ++ j⟩) :
    Steps P host ⟨t, fi, b'⟩ ⟨t', fi, k⟩ := by
  by_cases hne : us ≠ [] ∨ j ≠ []
  · rcases hk with rfl | ⟨a, rfl⟩
    · exact h.tail (Step.trapInstrs hne)
    · exact h.tail (Step.throwRefInstrs hne)
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals_nil'] using h

theorem sizeOf_frame (n : Nat) (fi : Frame) (b : List Admin) :
    sizeOf (Admin.frame n fi b) = 1 + sizeOf n + sizeOf fi + codeSize b := by
  simp [codeSize]

theorem codeSize_frame_lt (V : List Val) (n : Nat) (fi : Frame) (b L : List Admin) :
    codeSize b < codeSize (vals V ++ [.frame n fi b] ++ L) := by
  have h1 := codeSize_append (vals V ++ [.frame n fi b]) L
  have h2 := codeSize_append (vals V) [.frame n fi b]
  have h3 := codeSize_cons (.frame n fi b) []
  have h4 := sizeOf_frame n fi b
  have h5 := codeSize_pos L
  have h6 := codeSize_pos (vals V)
  omega

theorem codeSize_frame_mono (V : List Val) (n : Nat) (fi : Frame) {b₁ b : List Admin}
    (L : List Admin) (h : codeSize b₁ < codeSize b) :
    codeSize (vals V ++ [.frame n fi b₁] ++ L) < codeSize (vals V ++ [.frame n fi b] ++ L) := by
  have h1 := codeSize_append (vals V ++ [.frame n fi b]) L
  have h2 := codeSize_append (vals V) [.frame n fi b]
  have h3 := codeSize_cons (.frame n fi b) []
  have h4 := sizeOf_frame n fi b
  have h1' := codeSize_append (vals V ++ [.frame n fi b₁]) L
  have h2' := codeSize_append (vals V) [.frame n fi b₁]
  have h3' := codeSize_cons (.frame n fi b₁) []
  have h4' := sizeOf_frame n fi b₁
  omega

/-- A related store has, at each function address, an instance of the same type. -/
theorem _root_.Silmaril.Wasm.Execution.Core.Sim.StoreRel.func_type {s t : Store H} (hst : StoreRel F s t)
    {a : Nat} {fn : FuncInst H}
    (hf : s.funcs[a]? = some fn) : ∃ fn', t.funcs[a]? = some fn' ∧ fn'.type = fn.type := by
  have h := congrArg (·[a]?) hst.types
  simp only [List.getElem?_map, hf, Option.map_some] at h
  cases ht : t.funcs[a]? with
  | none => simp [ht] at h
  | some fn' =>
    rw [ht] at h
    exact ⟨fn', rfl, (Option.some.inj h).symm⟩

/-! ## The cases -/

omit [LawfulCodeRank rank] in
/-- The tail-call bubbling through a `FRAME` (`return_call_ref-frame-*`): the
related body is lifted to the same `return_call_ref` with the same arguments. -/
theorem tail_case (hB : BaseFacts P host F BI B rank) {s t : Store H} {f fi : Frame}
    {k : Nat} {b b' es' : List Admin} (hst : StoreRel F s t)
    (hb : AdminsRel BI (WithCuts B) b b')
    (hexit : ∃ (vs : List Val) (c : Admin) (rest : List Admin), c.IsReturnCallRef ∧
      b = vals vs ++ [c] ++ rest)
    (h : Step P host ⟨s, f, [.frame k fi b]⟩ ⟨s, f, es'⟩) :
    ∃ t', Relation.TransGen (Step P host) ⟨t, f, [.frame k fi b']⟩ ⟨t', f, es'⟩ ∧
      StoreRel F s t' := by
  obtain ⟨vs, c, rest, hc, rfl⟩ := hexit
  have hcv : c.val? = none := Admin.val?_of_isReturnCallRef hc
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb
  -- the right body reaches the same `return_call_ref` after the same values
  obtain ⟨t', us', j', hrun, hst', hor⟩ := exit_lift hB hsegs hst (f := fi) []
    (Exit.returnCallRef hc) (us := vs) (j := rest) rfl
  obtain rfl : us' = vs := by
    rcases hor with h | h | ⟨a, h⟩
    · exact h
    · simp only [List.cons.injEq, and_true] at h; subst h; exact hc.elim
    · simp [throwing] at h
  have hrun' : Steps P host ⟨t, fi, b'⟩ ⟨t', fi, vals us' ++ [c] ++ j'⟩ :=
    steps_congr hrun (by simp [vals_nil']) (by simp [vals_nil'])
  obtain ⟨is₀, his, hfr⟩ := Step.frame_redex_aux h [] k fi (vals us' ++ [c] ++ rest) rfl
  dsimp only at his hfr
  rw [vals_nil', List.nil_append] at his
  subst his
  generalize hbd : vals us' ++ [c] ++ rest = bb at hfr
  have hbd' : vals us' ++ c :: rest = bb := by rw [← hbd]; simp
  cases hfr with
  | ctxt hs =>
    exfalso
    rw [← hbd'] at hs
    rcases Step.split_head hcv hs with ⟨ws, us, is', -, hs', -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Step.returnCallRef_stuck_aux hs' us c hc rfl
    · exact hc
    · exact hc
  | values hn =>
    exfalso
    have := congrArg (List.all · Admin.isVal) hbd'
    simp [Admin.isVal, hcv] at this
  | ret hn =>
    rename_i vs₁ vs₂ rest₂
    exfalso
    have e : vals us' ++ c :: rest = vals (vs₁ ++ vs₂) ++ Admin.plain .return_ :: rest₂ := by
      rw [hbd']; simp
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hcv rfl e
    exact hc
  | callNull hc₂ =>
    rename_i vs₂ c₂ rest₂
    have e : vals us' ++ c :: rest = vals (vs₂ ++ [.ref .null]) ++ c₂ :: rest₂ := by
      rw [hbd']; simp [vals, Val.toAdmin]
    obtain ⟨rfl, rfl, -⟩ := vals_append_cons_inj hcv (Admin.val?_of_isReturnCallRef hc₂) e
    refine ⟨t', exit_frame hrun' ?_, hst'⟩
    have := Step.returnCallRefFrameNull (P := P) (host := host) (s := t') (f := f) (fi := fi)
      (k := k) (vs := vs₂) (rest := j') hc
    simpa [vals, Val.toAdmin] using this
  | callAddr hc₂ hf he hn =>
    rename_i vs₁ vs₂ a c₂ rest₂ fn ps rs
    have e : vals us' ++ c :: rest = vals (vs₁ ++ vs₂ ++ [.ref (.func a)]) ++ c₂ :: rest₂ := by
      rw [hbd']; simp [vals, Val.toAdmin]
    obtain ⟨rfl, rfl, -⟩ := vals_append_cons_inj hcv (Admin.val?_of_isReturnCallRef hc₂) e
    obtain ⟨fn', hf', hty⟩ := hst'.func_type hf
    refine ⟨t', exit_frame hrun' ?_, hst'⟩
    have := Step.returnCallRefFrameAddr (P := P) (host := host) (s := t') (f := f) (fi := fi)
      (k := k) (vs' := vs₁) (vs := vs₂) (rest := j') hc hf' (hty ▸ he) hn
    simpa [vals, Val.toAdmin] using this
  | throw =>
    rename_i a
    exfalso
    have e : vals us' ++ c :: rest = vals [.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      rw [hbd']; simp [vals, throwing, Val.toAdmin]
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hcv rfl e
    exact hc
  | trap =>
    exfalso
    have e : vals us' ++ c :: rest = vals [] ++ Admin.trap :: [] := by
      rw [hbd']; simp [vals_nil']
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hcv rfl e
    exact hc

/-- A `FRAME` redex step, matched on the right. -/
theorem frame_redex_case_of_body (hB : BaseFacts P host F BI B rank) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {fi : Frame} {b b' L L' is₀ : List Admin}
    (ih : ∀ {c' : Config H}, Step P host ⟨s, fi, b⟩ c' →
      RankedMatched rank P host F BI B c' ⟨t, fi, b'⟩ (rank b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (hfr : FrameRedex P host s f n fi b s' f' is₀) :
    RankedMatched rank P host F BI B ⟨s', f', vals V ++ is₀ ++ L⟩ ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩
      (rank (vals V ++ [.frame n fi b] ++ L)) := by
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb
  cases hfr with
  | ctxt hs =>
    obtain ⟨d', hm, hrel⟩ := ih hs
    obtain ⟨t', g, b₂⟩ := d'
    obtain ⟨hst', hfg, hb₂⟩ := hrel
    dsimp only at hst' hfg hb₂ hm
    subst hfg
    refine ⟨⟨t', f, vals V ++ [.frame n _ b₂] ++ L'⟩, ?_, hst', rfl,
      ((AdminsRel.vals V).append (.cons (.frame n _ hb₂) .nil)).append hL⟩
    rcases hm with hT | ⟨heq, hlt⟩
    · exact Or.inl (transGen_ctx (transGen_frame hT) V L')
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact Or.inr ⟨rfl, LawfulCodeRank.frame_lt (vals V) L n _ hlt⟩
  | values hn =>
    rename_i vs
    obtain ⟨t', hrun, hst'⟩ := run_vals hB hsegs (by simp) (f := fi) [] hst
    have hrun' : Steps P host ⟨t, fi, b'⟩ ⟨t', fi, vals vs⟩ :=
      steps_congr hrun (by simp [vals_nil']) (by simp [vals_nil'])
    exact ⟨⟨t', f, vals V ++ vals vs ++ L'⟩,
      Or.inl (transGen_ctx (exit_frame hrun' (Step.frameVals hn)) V L'), hst', rfl,
      (AdminsRel.refl _).append hL⟩
  | ret hn =>
    rename_i vs₁ vs rest
    obtain ⟨t', us', j', hrun, hst', hor⟩ := exit_lift hB hsegs hst (f := fi) [] Exit.return_
      (us := vs₁ ++ vs) (j := rest) (by simp)
    obtain rfl : us' = vs₁ ++ vs := by
      rcases hor with h | h | ⟨a, h⟩
      · exact h
      · simp at h
      · simp [throwing] at h
    have hrun' : Steps P host ⟨t, fi, b'⟩
        ⟨t', fi, vals vs₁ ++ vals vs ++ [.plain .return_] ++ j'⟩ :=
      steps_congr hrun (by simp [vals_nil']) (by simp [vals_nil'])
    exact ⟨⟨t', f, vals V ++ vals vs ++ L'⟩,
      Or.inl (transGen_ctx (exit_frame hrun' (Step.returnFrame hn)) V L'), hst', rfl,
      (AdminsRel.refl _).append hL⟩
  | callNull hc =>
    rename_i vs c rest
    obtain ⟨t', hT, hst'⟩ := tail_case hB hst hb
      ⟨vs ++ [.ref .null], c, rest, hc, by simp [vals, Val.toAdmin]⟩
      (Step.returnCallRefFrameNull hc)
    exact ⟨_, Or.inl (transGen_ctx hT V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | callAddr hc hf he hn =>
    rename_i vs₁ vs a c rest fn ps rs
    obtain ⟨t', hT, hst'⟩ := tail_case hB hst hb
      ⟨vs₁ ++ vs ++ [.ref (.func a)], c, rest, hc, by simp [vals, Val.toAdmin]⟩
      (Step.returnCallRefFrameAddr hc hf he hn)
    exact ⟨_, Or.inl (transGen_ctx hT V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | throw =>
    rename_i a
    obtain ⟨t', us', j', hrun, hst', -⟩ := exit_lift hB hsegs hst (f := fi) [] (Exit.throw a)
      (us := []) (j := []) (by simp [vals_nil'])
    have hrun' : Steps P host ⟨t, fi, b'⟩ ⟨t', fi, vals us' ++ throwing a ++ j'⟩ :=
      steps_congr hrun (by simp [vals_nil']) (by simp [vals_nil'])
    exact ⟨⟨t', f, vals V ++ throwing a ++ L'⟩,
      Or.inl (transGen_ctx (exit_frame (steps_discard (Or.inr ⟨a, rfl⟩) hrun')
        Step.throwRefFrame) V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | trap =>
    obtain ⟨t', us', j', hrun, hst', -⟩ := exit_lift hB hsegs hst (f := fi) [] Exit.trap
      (us := []) (j := []) (by simp [vals_nil'])
    have hrun' : Steps P host ⟨t, fi, b'⟩ ⟨t', fi, vals us' ++ [.trap] ++ j'⟩ :=
      steps_congr hrun (by simp [vals_nil']) (by simp [vals_nil'])
    exact ⟨⟨t', f, vals V ++ [.trap] ++ L'⟩,
      Or.inl (transGen_ctx (exit_frame (steps_discard (Or.inl rfl) hrun')
        Step.trapFrame) V L'), hst', rfl, (AdminsRel.refl _).append hL⟩

/-- Compatibility form using the unrestricted rank induction hypothesis. -/
theorem frame_redex_case (hB : BaseSim P host F BI B rank) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {fi : Frame} {b b' L L' is₀ : List Admin}
    (ih : RankedStepIH rank P host F BI B (rank (vals V ++ [.frame n fi b] ++ L)))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (hfr : FrameRedex P host s f n fi b s' f' is₀) :
    RankedMatched rank P host F BI B ⟨s', f', vals V ++ is₀ ++ L⟩ ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩
      (rank (vals V ++ [.frame n fi b] ++ L)) := by
  apply frame_redex_case_of_body hB.toBaseFacts ?_ hst hb hL hfr
  intro c' hs
  exact ih (c := ⟨s, fi, b⟩) (d := ⟨t, fi, b'⟩) (LawfulCodeRank.frame_body_lt (vals V) L n fi b) ⟨hst, rfl, hb⟩ hs

theorem frame_case_of_body (_hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (_hhost : HostRespects F host) (hB : BaseFacts P host F BI B rank) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {fi : Frame} {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P host ⟨s, fi, b⟩ c' →
      RankedMatched rank P host F BI B c' ⟨t, fi, b'⟩ (rank b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ [.frame n fi b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩
      (rank (vals V ++ [.frame n fi b] ++ L)) := by
  have ha : (Admin.frame n fi b).val? = none := rfl
  rw [show vals V ++ [.frame n fi b] ++ L = vals V ++ .frame n fi b :: L by simp] at h
  rcases Step.split_head ha h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  · obtain ⟨is₀, his, hfr⟩ := Step.frame_redex_aux hs us n fi b rfl
    dsimp only at his hfr
    subst his hV
    have e : vals ws ++ (vals us ++ is₀) ++ L = vals (ws ++ us) ++ is₀ ++ L := by simp
    rw [e]
    exact frame_redex_case_of_body hB ih hst hb hL hfr
  · cases hc
  · cases hc


/-- Compatibility form using the unrestricted rank induction hypothesis. -/
theorem frame_case (_hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (_hhost : HostRespects F host) (hB : BaseSim P host F BI B rank) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {fi : Frame} {b b' L L' es' : List Admin}
    (ih : RankedStepIH rank P host F BI B (rank (vals V ++ [.frame n fi b] ++ L)))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ [.frame n fi b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩
      (rank (vals V ++ [.frame n fi b] ++ L)) := by
  apply frame_case_of_body _hF _hhost hB.toBaseFacts ?_ hst hb hL h
  intro c' hs
  exact ih (c := ⟨s, fi, b⟩) (d := ⟨t, fi, b'⟩) (LawfulCodeRank.frame_body_lt (vals V) L n fi b) ⟨hst, rfl, hb⟩ hs

end Closure

end Silmaril.Wasm.Execution.Core.Sim
