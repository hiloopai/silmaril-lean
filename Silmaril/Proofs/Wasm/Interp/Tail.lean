module

public import Silmaril.Proofs.Wasm.Interp.Control

/-!
# The tail-aware postcondition (proofs)

`MatchT P host n r` is `Match r` or a pending tail call that ends as `r` does
(`TailRun`). Basic facts:

* `matchT_eq_match`: on a result that is neither a return nor a trap,
  `MatchT` is `Match` (a pending tail needs a returning or trapping result);
* `wp_matchT_of_match`: `Match ≤ MatchT`;
* `run_of_wpT`: a `WP` for `MatchT` is the old matched run, or a run to a
  pending tail `vals vs ++ ref.func a :: c :: rest` with `TailRun`;
* `wp_tail`: a pending tail, in a value prefix and before more code, is a final
  form for `MatchT`;
* `label_step_tail`: a label around a pending tail steps to it
  (`return_call_ref-label`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {n : Nat}
  {s s₁ : Store H} {f f₁ : Frame}

theorem tailRun_flow {r : Store H × Frame × Binaryen.Flow} {vs : List Val} {a : Nat} {c : Admin}
    (h : TailRun P host n r s f vs a c) : (∃ ws, r.2.2 = .ret ws) ∨ r.2.2 = .trap := by
  obtain ⟨-, -, _, _, _, _, _, -, -, -, -, hg⟩ := h
  rcases hg f with ⟨ws, hw, -⟩ | ⟨ht, -⟩
  · exact .inl ⟨ws, hw⟩
  · exact .inr ht

/-- **On a result that neither returns nor traps, `MatchT` is `Match`.** -/
theorem matchT_eq_match {r : Store H × Frame × Binaryen.Flow} (hr : ∀ ws, r.2.2 ≠ .ret ws)
    (ht : r.2.2 ≠ .trap) : MatchT P host n r = Match r := by
  funext s f o
  apply propext
  constructor
  · rintro (h | ⟨vs, a, c, -, hT⟩)
    · exact h
    · rcases tailRun_flow hT with ⟨ws, hw⟩ | hw
      · exact absurd hw (hr ws)
      · exact absurd hw ht
  · exact .inl

theorem matchT_normal (s : Store H) (f : Frame) (vs : List Val) :
    MatchT P host n (s, f, .normal vs) = Match (s, f, .normal vs) :=
  matchT_eq_match (fun _ h => by cases h) (by simp)

theorem matchT_brk (s : Store H) (f : Frame) (l : Nat) (vs : List Val) :
    MatchT P host n (s, f, .brk l vs) = Match (s, f, .brk l vs) :=
  matchT_eq_match (fun _ h => by cases h) (by simp)

/-- `Match ≤ MatchT`. -/
theorem wp_matchT_of_match {c : List Admin} {r : Store H × Frame × Binaryen.Flow}
    (h : WP P host s f c (Match r)) : WP P host s f c (MatchT P host n r) :=
  WP.mono h fun _ _ _ hm => .inl hm

/-- **A `WP` for `MatchT`** is the matched run, or a run to a pending tail. -/
theorem run_of_wpT {c : List Admin} {r : Store H × Frame × Binaryen.Flow}
    (h : WP P host s f c (MatchT P host n r)) :
    (∃ c' o, Steps P host ⟨s, f, c⟩ ⟨r.1, r.2.1, c'⟩ ∧ o.Ends c' ∧ FlowMatch r.2.2 o) ∨
      ∃ s' f' vs a c' rest, Steps P host ⟨s, f, c⟩ ⟨s', f', vals vs ++ .ref (.func a) :: c' :: rest⟩ ∧
        TailRun P host n r s' f' vs a c' := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  rcases hq with ⟨rfl, rfl, hm⟩ | ⟨vs, a, c₀, rfl, hT⟩
  · exact .inl ⟨c', o, hs, he, hm⟩
  · obtain ⟨-, rest, rfl⟩ := he
    exact .inr ⟨s', f', vs, a, c₀, rest, hs, hT⟩

/-- **A pending tail is a final form for `MatchT`**, in a value prefix and before
more code. -/
theorem wp_tail {r : Store H × Frame × Binaryen.Flow} {vs : List Val} {a : Nat} {c : Admin}
    (hT : TailRun P host n r s f vs a c) (pre : List Val) (rest rest' : List Admin) :
    WP P host s f (vals pre ++ (vals vs ++ .ref (.func a) :: c :: rest) ++ rest')
      (MatchT P host n r) := by
  obtain ⟨hc, hf, vs₁, args, fn, ps, rs, rfl, hfn, hex, hlen, hg⟩ := hT
  refine ⟨s, f, _, .tail (pre ++ vs₁ ++ args) a c, .refl, ⟨hc, rest ++ rest', by simp⟩, ?_⟩
  exact .inr ⟨_, a, c, rfl, hc, hf, pre ++ vs₁, args, fn, ps, rs, by simp, hfn, hex, hlen, hg⟩

/-- **A label around a pending tail steps to it** (`return_call_ref-label`). -/
theorem label_step_tail {k : Nat} {cont : List Instr} {vs : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) :
    Step P host ⟨s, f, [.label k cont (vals vs ++ .ref (.func a) :: c :: rest)]⟩
      ⟨s, f, vals vs ++ .ref (.func a) :: c :: []⟩ := by
  have := Step.returnCallRefLabel (P := P) (host := host) (s := s) (f := f) (k := k)
    (cont := cont) (vs := vs ++ [.ref (.func a)]) (rest := rest) hc
  simpa [vals, Val.toAdmin] using this

theorem tail_flow_eq {fl fl' : Binaryen.Flow} {r : Store H × Frame × Binaryen.Flow}
    (hr : r.2.2 = fl) (hT : (∃ ws, r.2.2 = .ret ws) ∨ r.2.2 = .trap)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    fl' = fl := by
  rcases hfl with ⟨k, vs, rfl, -⟩ | ⟨-, h⟩
  · rcases hT with ⟨ws, hw⟩ | hw <;> rw [hr] at hw <;> cases hw
  · exact h

/-- **A sequence whose first part ends abruptly**, for `MatchT`. -/
theorem wp_append_abruptT {c rest : List Admin} {fl : Binaryen.Flow}
    (h : WP P host s f c (MatchT P host n (s₁, f₁, fl))) (hn : ¬ fl.IsNormal) :
    WP P host s f (c ++ rest) (MatchT P host n (s₁, f₁, fl)) := by
  rcases run_of_wpT h with ⟨c', o, hst, he, hm⟩ | ⟨s', f', vs, a, c', rest₀, hst, hT⟩
  · exact wp_matchT_of_match (wp_append_abrupt' ⟨_, _, c', o, hst, he, rfl, rfl, hm⟩ hn)
  · exact WP.steps (Steps.append rest hst) (by simpa [vals] using wp_tail hT [] rest₀ rest)

/-- **Leaving a label abruptly**, for `MatchT`: the body's result passes out of
the label (one label fewer for a branch); a pending tail leaves by
`return_call_ref-label`. -/
theorem wp_label_abruptT {code body rest : List Admin} {pre : List Val} {k : Nat}
    {cont : List Instr} {fl fl' : Binaryen.Flow}
    (enter : Steps P host ⟨s, f, code⟩ ⟨s, f, vals pre ++ [.label k cont body] ++ rest⟩)
    (hb : WP P host s f body (MatchT P host n (s₁, f₁, fl)))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    WP P host s f code (MatchT P host n (s₁, f₁, fl')) := by
  rcases run_of_wpT hb with ⟨c', o, hrun, he, hm⟩ | ⟨s', f', vs, a, c', rest₀, hrun, hT⟩
  · have inner := Steps.ctx (P := P) (host := host) pre rest (Steps.label k cont hrun)
    exact wp_matchT_of_match (WP.steps (enter.trans inner) (exit_abrupt he hm hfl pre rest))
  · obtain rfl := tail_flow_eq rfl (tailRun_flow hT) hfl
    have inner := Steps.ctx (P := P) (host := host) pre rest (Steps.label k cont hrun)
    have out := Steps.ctx (P := P) (host := host) pre rest
      (.single (label_step_tail (s := s') (f := f') (k := k) (cont := cont) (vs := vs) (a := a)
        (rest := rest₀) hT.1))
    exact WP.steps (enter.trans (inner.trans out)) (wp_tail hT pre [] rest)

variable {stk : List Val} {bt : BlockType} {B : List Instr} {np nr : Nat}

/-- **A block whose body branches out, returns, traps or tail-calls**, for `MatchT`. -/
theorem wp_block_abruptT {rest : List Admin} {fl fl' : Binaryen.Flow}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WP P host s f (vals (stk.take np).reverse ++ expression B)
      (MatchT P host n (s₁, f₁, fl)))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    WP P host s f (vals stk.reverse ++ .plain (.block bt B) :: rest)
      (MatchT P host n (s₁, f₁, fl')) :=
  wp_label_abruptT (steps_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_block har) rest) hb hfl

/-- **A loop whose body branches out, returns, traps or tail-calls**, for `MatchT`. -/
theorem wp_loop_abruptT {rest : List Admin} {fl fl' : Binaryen.Flow}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WP P host s f (vals (stk.take np).reverse ++ expression B)
      (MatchT P host n (s₁, f₁, fl)))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    WP P host s f (vals stk.reverse ++ .plain (.loop bt B) :: rest)
      (MatchT P host n (s₁, f₁, fl')) :=
  wp_label_abruptT (steps_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_loop har) rest) hb hfl

/-! ## Callees whose body ends in a tail call -/

section TailCallee

variable {s₂ : Store H} {f₂ : Frame} {fl : Binaryen.Flow} {vs : List Val}

/-- A pending tail of a returning result satisfies the function postcondition. -/
theorem funcPost_of_tailRun {ws vs' : List Val} {a : Nat} {c : Admin}
    (hT : TailRun P host n (s₂, f₂, .ret ws) s₁ f₁ vs' a c) :
    funcPost P host n (callPost s₂ ws n) s₁ f₁ (.tail vs' a c) := by
  obtain ⟨-, hf, vs₁, args, fn, ps, rs, rfl, hfn, hex, hlen, hg⟩ := hT
  dsimp only at hf
  subst hf
  refine ⟨vs₁, args, fn, ps, rs, rfl, hfn, hex, hlen, fun g => ?_⟩
  rcases hg g with ⟨ws', hw, hst⟩ | ⟨hw, -⟩
  · cases hw
    exact ⟨s₂, _, hst, rfl, rfl⟩
  · cases hw

/-- The frame of a callee whose body is at a pending tail call leaves it, in the
outer frame, at the callee's call. -/
theorem frame_tail_exit {k : Nat} {F : Frame} {vs₁ args : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} {fn : FuncInst H} {ps rs : Validation.Ty (.list .val)}
    (hc : c.IsReturnCallRef) (hfn : s.funcs[a]? = some fn)
    (hex : Validation.Expand fn.type (.func ps rs)) (hlen : args.length = ps.length) :
    Steps P host ⟨s, f, [.frame k F [.label k [] (vals (vs₁ ++ args) ++ .ref (.func a) :: c :: rest)]]⟩
      ⟨s, f, vals args ++ [.ref (.func a), c.retToCallIn F.module]⟩ := by
  have h₁ : Step P host
      ⟨s, f, [.frame k F [.label k [] (vals (vs₁ ++ args) ++ .ref (.func a) :: c :: rest)]]⟩
      ⟨s, f, [.frame k F (vals (vs₁ ++ args) ++ .ref (.func a) :: c :: [])]⟩ :=
    Step.ctxtFrame (label_step_tail hc)
  have h₂ : Step P host ⟨s, f, [.frame k F (vals (vs₁ ++ args) ++ .ref (.func a) :: c :: [])]⟩
      ⟨s, f, vals args ++ [.ref (.func a), c.retToCallIn F.module]⟩ := by
    have e : vals (vs₁ ++ args) ++ .ref (.func a) :: c :: [] =
        vals vs₁ ++ vals args ++ [.ref (.func a), c] ++ [] := by simp
    rw [e]
    exact Step.returnCallRefFrameAddr hc hfn hex hlen
  exact (Relation.ReflTransGen.single h₁).tail h₂

variable {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
  {stk : List Val}

/-- **A call whose callee hands back values**, the callee body under `MatchT`
(it may end in a tail call). -/
theorem wp_call_okT {rest : List Admin} {Q : Post H} (hfi : s.func? f x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : ps.length ≤ stk.length)
    (hb : WP P host s (calleeFrame fi fn stk ps.length)
      (vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body)))
      (MatchT P host rs.length (s₂, f₂, fl)))
    (hvs : fl.retVals = some vs) (hrs : rs.length ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length)
    (hk : WP P host s₂ f (vals (vs.take rs.length ++ stk.drop ps.length).reverse ++ rest) Q) :
    WP P host s f (vals stk.reverse ++ .plain (.call x) :: rest) Q := by
  rcases run_of_wpT hb with ⟨c', o, hrun, he, hm⟩ | ⟨s', f', vs', a', c', rest₀, hrun, hT⟩
  · exact wp_call_ok hfi hcode hty hp ⟨_, _, c', o, hrun, he, rfl, rfl, hm⟩ hvs hrs hnorm hk
  rcases tailRun_flow hT with ⟨ws, hw⟩ | hw <;> dsimp only at hw <;> subst hw
  · simp only [Binaryen.Flow.retVals, Option.some.injEq] at hvs
    subst hvs
    rw [Binaryen.lowerList_liftInstrs] at hrun
    have enter := (steps_call_enter (P := P) (host := host) hfi hcode hty hp rest).to_reflTransGen
    have inner := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest
      (Steps.frame (f := f) rs.length (Steps.label rs.length [] (by simpa [vals] using hrun)))
    have hf' : f' = f₂ := hT.2.1
    subst hf'
    have he : Outcome.Ends (.tail vs' a' c') (vals vs' ++ .ref (.func a') :: c' :: rest₀) :=
      ⟨hT.1, rest₀, rfl⟩
    obtain ⟨s'', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) (n := rs.length)
      he (funcPost_of_tailRun hT)
    obtain ⟨rfl, rfl⟩ := hK
    have exit := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest hret
    have hk' : WP P host s'' f (vals (stk.drop ps.length).reverse ++
        vals (ws.take rs.length).reverse ++ rest) Q := by
      rw [← vals_append, ← stack_after]
      exact hk
    exact WP.steps (enter.trans (inner.trans exit)) hk'
  · simp [Binaryen.Flow.retVals] at hvs

/-- **A call whose callee traps**, the callee body under `MatchT` (it may trap in
a tail-called function). -/
theorem wp_call_trapT {rest : List Admin} (hfi : s.func? f x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : ps.length ≤ stk.length)
    (hb : WP P host s (calleeFrame fi fn stk ps.length)
      (vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body)))
      (MatchT P host rs.length (s₂, f₂, .trap))) :
    WP P host s f (vals stk.reverse ++ .plain (.call x) :: rest) (Match (s₂, f, .trap)) := by
  rcases run_of_wpT hb with ⟨c', o, hrun, he, hm⟩ | ⟨s', f', vs', a', c', rest₀, hrun, hT⟩
  · exact wp_call_trap hfi hcode hty hp ⟨_, _, c', o, hrun, he, rfl, rfl, hm⟩
  obtain ⟨hc, hf', vs₁, args, fn', ps', rs', rfl, hfn, hex, hlen, hg⟩ := hT
  dsimp only at hf'
  subst hf'
  rcases hg f with ⟨ws, hw, -⟩ | ⟨-, htr⟩
  · cases hw
  rw [Binaryen.lowerList_liftInstrs] at hrun
  have enter := (steps_call_enter (P := P) (host := host) hfi hcode hty hp rest).to_reflTransGen
  have inner := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest
    (Steps.frame (f := f) rs.length (Steps.label rs.length [] (show Steps P host
      ⟨s, calleeFrame fi fn stk ps.length, expression fn.body⟩
      ⟨s', f', vals (vs₁ ++ args) ++ .ref (.func a') :: c' :: rest₀⟩ from hrun)))
  have exit := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest
    ((frame_tail_exit (f := f) (k := rs.length) (F := f') (vs₁ := vs₁) (rest := rest₀) hc hfn hex
      hlen).trans htr)
  have hw : WP P host s₂ f (vals (stk.drop ps.length).reverse ++ .trap :: rest)
      (Match (s₂, f, .trap)) := wp_trap ⟨rfl, rfl, trivial⟩
  exact WP.steps (enter.trans (inner.trans exit)) (by simpa using hw)

end TailCallee

/-! ## The tail-aware invariant -/

/-- The Core-run invariant with the tail-aware postcondition. -/
abbrev CoreGoodT (ext : ExtArity H) (P : Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) (r : Store H × Frame × Binaryen.Flow) :
    Prop :=
  CoreGoodQ ext P host (MatchT P host) s f stk es r

section TCases

set_option linter.unusedSectionVars false

variable {ext : ExtArity H} [ExtStable ext] {s₂ : Store H} {f₂ : Frame} {stk₁ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl fl' : Binaryen.Flow}
  {r : Store H × Frame × Binaryen.Flow}

/-- `CoreGoodE ≤ CoreGoodT`. -/
theorem coreT_of_core (h : CoreGoodE ext P host s f stk es r) : CoreGoodT ext P host s f stk es r :=
  fun hS hc => wp_matchT_of_match (h hS hc)

/-- **On a result that neither returns nor traps, `CoreGoodT` is `CoreGoodE`.** -/
theorem core_of_coreT (hr : ∀ ws, r.2.2 ≠ .ret ws) (ht : r.2.2 ≠ .trap)
    (h : CoreGoodT ext P host s f stk es r) : CoreGoodE ext P host s f stk es r := by
  intro labels ret out hS hc
  have := h hS hc
  rwa [matchT_eq_match hr ht] at this

theorem core_of_coreT_normal {vs : List Val}
    (h : CoreGoodT ext P host s f stk es (s₁, f₁, .normal vs)) :
    CoreGoodE ext P host s f stk es (s₁, f₁, .normal vs) :=
  core_of_coreT (fun _ h => by cases h) (by simp) h

theorem core_of_coreT_blockVals (hvs : fl.blockVals = some vs)
    (h : CoreGoodT ext P host s f stk es (s₁, f₁, fl)) : CoreGoodE ext P host s f stk es (s₁, f₁, fl) := by
  refine core_of_coreT ?_ ?_ h <;>
    rcases fl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp_all [Binaryen.Flow.blockVals]

theorem coreT_argsAbort (iha : CoreGoodT ext P host s f stk args (s₁, f₁, fl))
    (hfl : ¬ fl.IsNormal) : CoreGoodT ext P host s f stk (.op i args :: es) (s₁, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op]
  exact wp_append_abruptT (iha hS ha) hfl

theorem coreT_blockAbrupt (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE ext s f (stk.take np) body (s₁, f₁, fl))
    (ihb : CoreGoodT ext P host s f (stk.take np) body (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreGoodT ext P host s f stk (.block bt body :: es) (s₁, f₁, fl') := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  rw [code_block]
  exact wp_block_abruptT har hp (ihb hS hbc) hfl

theorem coreT_loopAbrupt (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE ext s f (stk.take np) body (s₁, f₁, fl))
    (ihb : CoreGoodT ext P host s f (stk.take np) body (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreGoodT ext P host s f stk (.loop bt body :: es) (s₁, f₁, fl') := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  rw [code_loop]
  exact wp_loop_abruptT har hp (ihb hS hbc) hfl

theorem coreT_ifAbrupt {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (hcond : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (ihc : CoreGoodE ext P host s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (harm : ArityGoodE ext s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (iharm : CoreGoodT ext P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreGoodT ext P host s f stk (.if_ bt c t el :: es) (s₂, f₂, fl') := by
  intro labels ret out hS hc
  obtain ⟨oc, ob, hco, hbc, -, -, inv1, -, hp, -⟩ := if_facts hS hcond har harm hc
  have hwb := wp_block_abruptT (rest := expression (Binaryen.BExpr.lowerList es)) har hp
    (iharm (storeChk_inv inv1 hS) hbc) hfl
  rw [code_if]
  exact wp_append_normal (ihc hS hco) (wp_if_arm hb hwb)

theorem coreT_ifAbort {c t el : List Binaryen.BExpr}
    (ihc : CoreGoodT ext P host s f stk c (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
    CoreGoodT ext P host s f stk (.if_ bt c t el :: es) (s₁, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  rw [code_if]
  exact wp_append_abruptT (ihc hS hco) hfl

section TCalls

variable {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
  {M : Nat → Store H × Frame × Binaryen.Flow → Post H}

/-- **A call whose callee hands back values**, the callee body under `CoreGoodT`
(it may end in a tail call). -/
theorem coreT_callOk (hargs : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : ArityGoodE ext s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, fl))
    (ihb : CoreGoodT ext P host s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, fl))
    (hvs : fl.retVals = some vs)
    (ihk : CoreGoodQ ext P host M s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    CoreGoodQ ext P host M s f stk (.op (.call x) args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨oa, ob, ha, hb', hob, hok, inv1, hfuncs, hp, h2⟩ :=
    call_facts hS hargs hfi hcode hty hbody hc
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
    rintro ws rfl
    exact length_of_ends hok hob
  have inv2 : EvalInvE ext s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE ext s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  have hwb := ihb (storeChk_inv inv1 hS) hb'
  rw [code_op]
  exact wp_append_normal (iha hS ha) (wp_call_okT hfi hcode hty hp hwb hvs hrs hnorm hk)

/-- **A call whose callee traps**, the callee body under `CoreGoodT` (it may trap
in a tail-called function). -/
theorem coreT_callTrap (hargs : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : ArityGoodE ext s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, .trap))
    (ihb : CoreGoodT ext P host s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, .trap)) :
    CoreGoodE ext P host s f stk (.op (.call x) args :: es) (s₂, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨oa, ob, ha, hb', -, -, inv1, -, hp, -⟩ := call_facts hS hargs hfi hcode hty hbody hc
  have hwb := ihb (storeChk_inv inv1 hS) hb'
  rw [code_op]
  exact wp_append_normal (iha hS ha) (wp_call_trapT hfi hcode hty hp hwb)

end TCalls

end TCases

end Silmaril.Wasm.Interp
