module

public import Silmaril.Proofs.Wasm.Logic.Core.Straight

/-!
# Function specifications and the call rules

* `FuncSpec.of_body` proves a specification from a `WP` of the body, in the frame
  `Frame.forCall` the call creates (Wasm Logic's `[call]`/`callcl` rules, Watt et
  al. 2019, Figure 11). The body may end by falling through, by `br 0`, by
  `return`, or by a tail call (`funcPost`).
* `wp_call` uses a specification at a `call x` site (the **call rule**): the
  caller never looks inside the callee again. `wp_callRef` is the same for
  Wasm 3.0's typed `call_ref y`, `wp_callRef_null` its trapping case, and
  `wp_callIndirect` unfolds `call_indirect` into `table.get`, `ref.cast` and
  `call_ref`.
* `wp_returnCall` and `funcPost_tail` are the tail-call rules (`return_call`).
* `FuncSpec.invoke` turns a specification into a run of the embedder's `$invoke`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem invoke_eq_callCode (s : Store H) (a : Nat) (args : List Val) :
    invoke s a args = ⟨s, {}, callCode s a args⟩ := rfl

/-- The `CALL_REF` a `RETURN_CALL_REF` turns into when it leaves its frame. -/
theorem Admin.isCallRef_retToCallIn {c : Admin} (m : ModuleInst) (h : c.IsReturnCallRef) :
    (c.retToCallIn m).IsCallRef := by
  unfold Admin.IsReturnCallRef at h
  split at h
  · rename_i y
    show (match m.types[y.toNat]? with
      | some d => Admin.callRefType d
      | none => Admin.plain (.callRef y)).IsCallRef
    split <;> trivial
  · trivial
  · exact h.elim

/-! ## Entering and leaving a function body -/

section Body

variable {s : Store H} {f F : Frame} {n : Nat} {K : Store H → List Val → Prop}

/-- A body that fell through. -/
theorem frame_normal {vs : List Val} (hq : funcPost P host n K s F (.normal vs)) :
    ∃ s' res, Steps P host ⟨s, f, [.frame n F [.label n [] (vals vs)]]⟩ ⟨s', f, vals res⟩ ∧
      K s' res := by
  obtain ⟨hn, hk⟩ : vs.length = n ∧ K s vs := hq
  exact ⟨s, vs, (Relation.ReflTransGen.single (Step.ctxtFrame Step.labelVals)).tail
    (Step.frameVals hn), hk⟩

/-- A body that branched to its own label. -/
theorem frame_br {x : LabelIdx} {vs : List Val} {rest : List Admin} (hx : x.toNat = 0)
    (hq : funcPost P host n K s F (.br 0 vs)) :
    ∃ s' res, Steps P host ⟨s, f, [.frame n F [.label n [] (vals vs ++ .plain (.br x) :: rest)]]⟩
      ⟨s', f, vals res⟩ ∧ K s' res := by
  obtain ⟨vs₁, res, rfl, hn, hk⟩ := hq
  have e : vals (vs₁ ++ res) ++ .plain (.br x) :: rest =
      vals vs₁ ++ vals res ++ [.plain (.br x)] ++ rest := by simp
  have h₁ : Step P host ⟨s, f, [.frame n F [.label n [] (vals (vs₁ ++ res) ++ .plain (.br x) :: rest)]]⟩
      ⟨s, f, [.frame n F (vals res)]⟩ := by
    rw [e]
    simpa only [expression_nil, List.append_nil] using
      Step.ctxtFrame (f := f) (Step.brLabelZero (cont := []) (vs' := vs₁) (rest := rest) hx hn)
  exact ⟨s, res, (Relation.ReflTransGen.single h₁).tail (Step.frameVals hn), hk⟩

/-- A body that returned. -/
theorem frame_ret {vs : List Val} {rest : List Admin} (hq : funcPost P host n K s F (.ret vs)) :
    ∃ s' res, Steps P host ⟨s, f, [.frame n F [.label n [] (vals vs ++ .plain .return_ :: rest)]]⟩
      ⟨s', f, vals res⟩ ∧ K s' res := by
  obtain ⟨vs₁, res, rfl, hn, hk⟩ := hq
  have h₁ : Step P host ⟨s, f, [.frame n F [.label n [] (vals (vs₁ ++ res) ++ .plain .return_ :: rest)]]⟩
      ⟨s, f, [.frame n F (vals (vs₁ ++ res) ++ [.plain .return_])]⟩ := by
    simpa only [List.append_assoc, List.singleton_append] using
      Step.ctxtFrame (f := f) (fi := F) (n := n)
        (Step.returnLabel (P := P) (host := host) (cont := []) (vs := vs₁ ++ res) (rest := rest))
  have h₂ : Step P host ⟨s, f, [.frame n F (vals (vs₁ ++ res) ++ [.plain .return_])]⟩
      ⟨s, f, vals res⟩ := by
    have e : vals (vs₁ ++ res) ++ [.plain .return_] =
        vals vs₁ ++ vals res ++ [.plain .return_] ++ [] := by simp
    rw [e]
    exact Step.returnFrame hn
  exact ⟨s, res, (Relation.ReflTransGen.single h₁).tail h₂, hk⟩

/-- A body that tail-called a function. -/
theorem frame_tail {vs : List Val} {a : Nat} {r : Admin} {rest : List Admin}
    (hr : r.IsReturnCallRef) (hq : funcPost P host n K s F (.tail vs a r)) :
    ∃ s' res, Steps P host
      ⟨s, f, [.frame n F [.label n [] (vals vs ++ .ref (.func a) :: r :: rest)]]⟩
      ⟨s', f, vals res⟩ ∧ K s' res := by
  obtain ⟨vs₁, args, fn, ps, rs, rfl, hf, he, hn, hrun⟩ := hq
  have h₁ : Step P host
      ⟨s, f, [.frame n F [.label n [] (vals (vs₁ ++ args) ++ .ref (.func a) :: r :: rest)]]⟩
      ⟨s, f, [.frame n F (vals (vs₁ ++ args ++ [.ref (.func a)]) ++ [r])]⟩ := by
    rw [tail_code]
    exact Step.ctxtFrame (Step.returnCallRefLabel hr)
  have h₂ : Step P host ⟨s, f, [.frame n F (vals (vs₁ ++ args ++ [.ref (.func a)]) ++ [r])]⟩
      ⟨s, f, vals args ++ [.ref (.func a), r.retToCallIn F.module]⟩ := by
    have e : vals (vs₁ ++ args ++ [.ref (.func a)]) ++ [r] =
        vals vs₁ ++ vals args ++ [.ref (.func a), r] ++ [] := by simp [vals, Val.toAdmin]
    rw [e]
    exact Step.returnCallRefFrameAddr hr hf he hn
  obtain ⟨s', res, hs, hk⟩ := hrun f
  exact ⟨s', res, (Relation.ReflTransGen.single h₁).tail h₂ |>.trans hs, hk⟩

/-- How a function body may end, seen from the caller. -/
theorem frame_ends {c : List Admin} {o : Outcome} (he : o.Ends c)
    (hq : funcPost P host n K s F o) :
    ∃ s' res, Steps P host ⟨s, f, [.frame n F [.label n [] c]]⟩ ⟨s', f, vals res⟩ ∧
      K s' res := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact (show c = vals vs from he) ▸ frame_normal hq
  · obtain ⟨x, rest, hx, rfl⟩ := he
    exact frame_br hx hq
  · exact hq.elim
  · obtain ⟨rest, rfl⟩ := he
    exact frame_ret hq
  · exact hq.elim
  · exact hq.elim
  · obtain ⟨hr, rest, rfl⟩ := he
    exact frame_tail hr hq

end Body

/-! ## Function specifications -/

/-- **A specification from the body.** -/
theorem FuncSpec.of_body {a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    {Pre : Store H → List Val → Prop}
    {Post : Store H → List Val → Store H → List Val → Prop}
    (hfi : ∀ s args, Pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hlen : ∀ s args, Pre s args → args.length = ps.length)
    (hbody : ∀ s args, Pre s args →
      WP P host s (Frame.forCall fi.module args code.locals) (expression code.body)
        (funcPost P host rs.length (Post s args))) :
    FuncSpec P host a Pre Post := by
  intro s args hp f c hc
  obtain ⟨s', F', c', o, hs, hE, hq⟩ := hbody s args hp
  have h₀ : Step P host ⟨s, f, vals args ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module args code.locals)
        [.label rs.length [] (expression code.body)]]⟩ :=
    Step.callRefFunc hc (hfi s args hp) he (hlen s args hp) hcode
  have h₁ := Steps.frame (f := f) rs.length (Steps.label rs.length [] hs)
  obtain ⟨s'', res, h₂, hk⟩ := frame_ends (f := f) hE hq
  exact ⟨s'', res, (Relation.ReflTransGen.single h₀).trans (h₁.trans h₂), hk⟩

/-- A specification gives a run of `$invoke`. -/
theorem FuncSpec.invoke {a : Nat} {Pre : Store H → List Val → Prop}
    {Post : Store H → List Val → Store H → List Val → Prop} (h : FuncSpec P host a Pre Post)
    {s : Store H} {args : List Val} (hpre : Pre s args) :
    ∃ s' res, Steps P host (invoke s a args) ⟨s', {}, vals res⟩ ∧ Post s args s' res :=
  h s args hpre {} _ trivial

/-- Weaken the precondition and strengthen the postcondition. -/
theorem FuncSpec.conseq {a : Nat} {Pre Pre' : Store H → List Val → Prop}
    {Post Post' : Store H → List Val → Store H → List Val → Prop}
    (h : FuncSpec P host a Pre Post) (hpre : ∀ s args, Pre' s args → Pre s args)
    (hpost : ∀ s args s' res, Pre' s args → Post s args s' res → Post' s args s' res) :
    FuncSpec P host a Pre' Post' := by
  intro s args hp f c hc
  obtain ⟨s', res, hs, hq⟩ := h s args (hpre s args hp) f c hc
  exact ⟨s', res, hs, hpost s args s' res hp hq⟩

/-! ## Call sites -/

/-- A call through any `CALL_REF` form, in context: values below and code after. -/
theorem wp_callWith {s : Store H} {f : Frame} {a : Nat} {c : Admin} {vs args : List Val}
    {rest : List Admin} {Pre : Store H → List Val → Prop}
    {Post : Store H → List Val → Store H → List Val → Prop}
    {Q : Store H → Frame → Outcome → Prop}
    (hc : c.IsCallRef) (hspec : FuncSpec P host a Pre Post) (hpre : Pre s args)
    (hk : ∀ s' res, Post s args s' res → WP P host s' f (vals (vs ++ res) ++ rest) Q) :
    WP P host s f (vals vs ++ (vals args ++ [.ref (.func a), c]) ++ rest) Q := by
  obtain ⟨s', res, hs, hp⟩ := hspec s args hpre f c hc
  have h₂ := Steps.ctx vs rest hs
  rw [← vals_append vs res] at h₂
  exact WP.steps h₂ (hk s' res hp)

/-- **The call rule.** At `call x`, with `x` resolving to address `a`, use the
callee's specification and continue after the call with its results. -/
theorem wp_call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {vs args : List Val}
    {rest : List Admin} {Pre : Store H → List Val → Prop}
    {Post : Store H → List Val → Store H → List Val → Prop}
    {Q : Store H → Frame → Outcome → Prop}
    (hx : f.module.funcs[x.toNat]? = some a) (ha : (s.funcs[a]?).isSome)
    (hspec : FuncSpec P host a Pre Post) (hpre : Pre s args)
    (hk : ∀ s' res, Post s args s' res → WP P host s' f (vals (vs ++ res) ++ rest) Q) :
    WP P host s f (vals (vs ++ args) ++ .plain (.call x) :: rest) Q := by
  obtain ⟨fi, hf⟩ := Option.isSome_iff_exists.mp ha
  have h₀ : Step P host ⟨s, f, vals (vs ++ args) ++ .plain (.call x) :: rest⟩
      ⟨s, f, vals vs ++ (vals args ++ [.ref (.func a), .callRefType fi.type]) ++ rest⟩ := by
    have := Step.ctx (vs ++ args) rest (Step.call (P := P) (host := host) (s := s) hx hf)
    simpa only [vals_append, List.append_assoc, List.singleton_append] using this
  exact WP.step h₀ (wp_callWith trivial hspec hpre hk)

/-- **`call_ref y`** (Wasm 3.0) on a function reference. -/
theorem wp_callRef {s : Store H} {f : Frame} {y : TypeIdx} {a : Nat} {vs args : List Val}
    {rest : List Admin} {Pre : Store H → List Val → Prop}
    {Post : Store H → List Val → Store H → List Val → Prop}
    {Q : Store H → Frame → Outcome → Prop}
    (hspec : FuncSpec P host a Pre Post) (hpre : Pre s args)
    (hk : ∀ s' res, Post s args s' res → WP P host s' f (vals (vs ++ res) ++ rest) Q) :
    WP P host s f (vals (vs ++ args ++ [.ref (.func a)]) ++ .plain (.callRef y) :: rest) Q := by
  have e : vals (vs ++ args ++ [.ref (.func a)]) ++ .plain (.callRef y) :: rest =
      vals vs ++ (vals args ++ [.ref (.func a), .plain (.callRef y)]) ++ rest := by
    simp [vals, Val.toAdmin]
  exact e ▸ wp_callWith trivial hspec hpre hk

/-- `call_ref y` on a null reference traps. -/
theorem wp_callRef_null {s : Store H} {f : Frame} {y : TypeIdx} {vs : List Val}
    {rest : List Admin} {Q : Post H} (h : Q s f .trap) :
    WP P host s f (vals (vs ++ [.ref .null]) ++ .plain (.callRef y) :: rest) Q := by
  have e : vals (vs ++ [.ref .null]) ++ .plain (.callRef y) :: rest =
      vals vs ++ [.ref .null, .plain (.callRef y)] ++ rest := by simp [vals, Val.toAdmin]
  rw [e]
  refine WP.step (Step.ctx vs rest (Step.callRefNull (c := .plain (.callRef y)) trivial)) ?_
  simpa only [List.append_assoc, List.singleton_append] using wp_trap (vs := vs) (rest := rest) h

/-- **`call_indirect x y`** unfolds to `table.get x; ref.cast (ref null y); call_ref y`. -/
theorem wp_callIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {vs : List Val} {rest : List Admin} {Q : Post H}
    (h : WP P host s f (vals vs ++ .plain (.tableGet x) ::
      .plain (.refCast ⟨true, .typeIdx y⟩) :: .plain (.callRef y) :: rest) Q) :
    WP P host s f (vals vs ++ .plain (.callIndirect x y) :: rest) Q := by
  have st := Step.ctx (P := P) (host := host) (s := s) (f := f) vs rest
    (Step.callIndirect (x := x) (y := y))
  simp only [List.append_assoc, List.cons_append, List.nil_append] at st
  exact WP.step st h

/-! ## Tail calls -/

/-- **`return_call x`**: the body ends with a tail call of the function `x` resolves
to. -/
theorem wp_returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    {vs : List Val} {rest : List Admin} {Q : Post H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : Q s f (.tail vs a (.returnCallRefType fi.type))) :
    WP P host s f (vals vs ++ .plain (.returnCall x) :: rest) Q := by
  have st := Step.ctx (P := P) (host := host) (s := s) (f := f) vs rest (Step.returnCall hx hf)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at st
  have he : (Outcome.tail vs a (.returnCallRefType fi.type)).Ends
      (vals vs ++ .ref (.func a) :: .returnCallRefType fi.type :: rest) := ⟨trivial, rest, rfl⟩
  exact WP.step st ⟨s, f, _, _, .refl, he, h⟩

/-- **`return_call_ref y`** on a function reference. -/
theorem wp_returnCallRef {s : Store H} {f : Frame} {y : TypeIdx} {a : Nat} {vs : List Val}
    {rest : List Admin} {Q : Post H} (h : Q s f (.tail vs a (.plain (.returnCallRef y)))) :
    WP P host s f (vals (vs ++ [.ref (.func a)]) ++ .plain (.returnCallRef y) :: rest) Q := by
  have e : vals (vs ++ [.ref (.func a)]) ++ .plain (.returnCallRef y) :: rest =
      vals vs ++ .ref (.func a) :: .plain (.returnCallRef y) :: rest := by
    simp [vals, Val.toAdmin]
  have he : (Outcome.tail vs a (.plain (.returnCallRef y))).Ends
      (vals vs ++ .ref (.func a) :: .plain (.returnCallRef y) :: rest) := ⟨trivial, rest, rfl⟩
  exact e ▸ ⟨s, f, _, _, .refl, he, h⟩

/-- **A tail call meets the callee's specification**: the body's postcondition
holds of a tail call of a function whose specification yields `K`. -/
theorem funcPost_tail {s : Store H} {F : Frame} {n : Nat} {K : Store H → List Val → Prop}
    {vs₁ args : List Val} {a : Nat} {r : Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    {Pre : Store H → List Val → Prop} {Post : Store H → List Val → Store H → List Val → Prop}
    (hr : r.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : args.length = ps.length) (hspec : FuncSpec P host a Pre Post) (hpre : Pre s args)
    (hk : ∀ s' res, Post s args s' res → K s' res) :
    funcPost P host n K s F (.tail (vs₁ ++ args) a r) := by
  refine ⟨vs₁, args, fn, ps, rs, rfl, hf, he, hn, fun g => ?_⟩
  obtain ⟨s', res, hs, hp⟩ := hspec s args hpre g _ (Admin.isCallRef_retToCallIn F.module hr)
  exact ⟨s', res, hs, hk s' res hp⟩

end Silmaril.Wasm.Logic.Core
