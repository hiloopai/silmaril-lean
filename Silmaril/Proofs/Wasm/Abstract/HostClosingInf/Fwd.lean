module

public import Silmaril.Wasm.Abstract.HostClosingInf.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Thms

/-!
# Logged native runs are Core runs with exactly their host events (proofs)

The **logged forward simulation** of finite native runs, every profile. `Interp.evalH_good`
makes every `EvalH host` run a Core run, but forgets which host events that run performs. Here
a logged run `EvalL`, its calls resolved by the closure `Shape.close wasmHOpen` to the import
calls `q`, consistently with the host, is a Core run whose host events (`EvRun`) are **exactly**
`q`:

* `RunL`, `CoreL`: the logged forms of `WP … (Match r)` and `Interp.CoreGood`;
* the logged combinators `runL_append_normal`, `runL_append_abrupt`, `runL_block_vals`,
  `runL_block_abrupt`, `runL_loop_normal`, `runL_loop_back`, `runL_loop_abrupt`, `runL_if_arm`,
  `evRun_oracle_call`, `evRun_callRef_of_good`: the Core glue around a logged inner run is
  host-free (the lemmas of `Interp.Control` at the empty host, `evRun_of_free`), the inner
  run is lifted through its context (`evRun_ctx`, `evRun_label`, `evRun_frame`);
* `GoodC`: the returning closed behaviours whose consistent log is the event log of the Core
  run of the call (with its `hostCall` outcome, for the arity invariants of `evalH_good`);
* `evalL_fwd`: the simulation of `EvalL`, by induction, the callees answered by `GoodC`;
* `close_le_goodC`: by least-fixpoint induction, every closed behaviour is in `GoodC`: a Wasm
  callee's body is `evalL_fwd` in its frame, a host callee's one import call is one event
  (`hEvStep_host_call`);
* `close_ret_evRun`, `wasmEvFun_evRun`: a returning closed behaviour with a consistent log is a
  Core run of the call, and of the invocation, with exactly that log.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (WP Outcome funcPost frame_ends)
open Silmaril.Wasm.Interp

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- The empty host: host-free steps. -/
abbrev NH : HostSemantics H := fun _ _ _ _ => False

/-! ## Logged runs to a matching final form -/

/-- **A logged Core run of `code` to a final form matching `r`**, its host events `q`. -/
def RunL (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (code : List Admin) (q : List (Call (wasmHostSig H))) (r : Store H × Frame × Binaryen.Flow) :
    Prop :=
  ∃ c' o, EvRun P host ⟨s, f, code⟩ q ⟨r.1, r.2.1, c'⟩ ∧ Outcome.Ends o c' ∧ FlowMatch r.2.2 o

/-- **The logged Core-run invariant**: `Interp.CoreGood` with the host events `q`. -/
def CoreL (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (stk : List Val) (es : List Binaryen.BExpr) (r : Store H × Frame × Binaryen.Flow)
    (q : List (Call (wasmHostSig H))) : Prop :=
  ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChk s.funcs →
    chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    RunL P host s f (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)) q r

section Comb

variable {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {c rest : List Admin}
  {q q₁ q₂ : List (Call (wasmHostSig H))} {r : Store H × Frame × Binaryen.Flow}
  {stk stk₁ vs : List Val} {fl fl' : Binaryen.Flow}

theorem runL_of_wp (h : WP P NH s f c (Match r)) : RunL P host s f c [] r := by
  obtain ⟨s', f', c', o, hs, he, rfl, rfl, hm⟩ := h
  exact ⟨c', o, evRun_of_free hs, he, hm⟩

theorem runL_evRun {c₁ : List Admin}
    (h₁ : EvRun P host ⟨s, f, c⟩ q₁ ⟨s₁, f₁, c₁⟩) (h₂ : RunL P host s₁ f₁ c₁ q₂ r) :
    RunL P host s f c (q₁ ++ q₂) r := by
  obtain ⟨c', o, h, he, hm⟩ := h₂
  exact ⟨c', o, evRun_trans h₁ h, he, hm⟩

theorem runL_free {c₁ : List Admin} (hs : Steps P NH ⟨s, f, c⟩ ⟨s₁, f₁, c₁⟩)
    (h : RunL P host s₁ f₁ c₁ q r) : RunL P host s f c q r := by
  simpa using runL_evRun (evRun_of_free hs) h

theorem evRun_append {c' : List Admin} (h : EvRun P host ⟨s, f, c⟩ q ⟨s₁, f₁, c'⟩) :
    EvRun P host ⟨s, f, c ++ rest⟩ q ⟨s₁, f₁, c' ++ rest⟩ := by
  simpa [vals] using evRun_ctx [] rest h

/-- A sequence whose first part completes normally. -/
theorem runL_append_normal (h : RunL P host s f c q₁ (s₁, f₁, .normal stk₁))
    (hk : RunL P host s₁ f₁ (vals stk₁.reverse ++ rest) q₂ r) :
    RunL P host s f (c ++ rest) (q₁ ++ q₂) r := by
  obtain ⟨c', o, hrun, he, hm⟩ := h
  have hc : c' = vals stk₁.reverse := ends_normal hm he
  subst hc
  exact runL_evRun (evRun_append hrun) hk

/-- A sequence whose first part ends abruptly. -/
theorem runL_append_abrupt (h : RunL P host s f c q (s₁, f₁, fl)) (hn : ¬ fl.IsNormal) :
    RunL P host s f (c ++ rest) q (s₁, f₁, fl) := by
  obtain ⟨c', o, hrun, he, hm⟩ := h
  have h2 : RunL P host s₁ f₁ (vals [] ++ c' ++ rest) [] (s₁, f₁, fl) :=
    runL_of_wp (wp_abrupt (P := P) (host := NH) he hm hn [] rest)
  simpa [vals] using runL_evRun (evRun_append hrun) h2

end Comb

/-! ## Blocks, loops and conditionals -/

section Blocks

variable {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {B : List Instr}
  {np nr : Nat} {fl fl' : Binaryen.Flow} {rest : List Admin}
  {q₁ q₂ : List (Call (wasmHostSig H))} {r : Store H × Frame × Binaryen.Flow}

/-- **A block whose body hands on values.** -/
theorem runL_block_vals (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : RunL P host s f (vals (stk.take np).reverse ++ expression B) q₁ (s₁, f₁, fl))
    (hvs : fl.blockVals = some vs) (hnr : nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr)
    (hk : RunL P host s₁ f₁ (vals (vs.take nr ++ stk.drop np).reverse ++ rest) q₂ r) :
    RunL P host s f (vals stk.reverse ++ .plain (.block bt B) :: rest) (q₁ ++ q₂) r := by
  obtain ⟨c', o, hrun, he, hm⟩ := hb
  have enter := steps_enter (P := P) (host := NH) (s := s) (f := f) (B := B) hp
    (step_block har) rest
  have inner := evRun_ctx (stk.drop np).reverse rest (evRun_label nr [] hrun)
  have exit := exit_blockVals (P := P) (host := NH) (s₁ := s₁) (f₁ := f₁) (pre := (stk.drop np).reverse) (rest := rest)
    he hm hvs hnr hnorm
  rw [stack_after] at hk
  exact runL_free enter (runL_evRun inner (runL_free exit hk))

/-- **A block whose body branches to an outer label, returns or traps.** -/
theorem runL_block_abrupt (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : RunL P host s f (vals (stk.take np).reverse ++ expression B) q₁ (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    RunL P host s f (vals stk.reverse ++ .plain (.block bt B) :: rest) q₁ (s₁, f₁, fl') := by
  obtain ⟨c', o, hrun, he, hm⟩ := hb
  have enter := steps_enter (P := P) (host := NH) (s := s) (f := f) (B := B) hp
    (step_block har) rest
  have inner := evRun_ctx (stk.drop np).reverse rest (evRun_label nr [] hrun)
  have hx : RunL P host s₁ f₁ (vals (stk.drop np).reverse ++ [.label nr [] c'] ++ rest) []
      (s₁, f₁, fl') := runL_of_wp (exit_abrupt (P := P) (host := NH) he hm hfl _ rest)
  simpa using runL_free enter (runL_evRun inner hx)

/-- **A loop whose body falls through.** -/
theorem runL_loop_normal (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : RunL P host s f (vals (stk.take np).reverse ++ expression B) q₁ (s₁, f₁, .normal vs))
    (hlen : vs.length = nr)
    (hk : RunL P host s₁ f₁ (vals (vs.take nr ++ stk.drop np).reverse ++ rest) q₂ r) :
    RunL P host s f (vals stk.reverse ++ .plain (.loop bt B) :: rest) (q₁ ++ q₂) r := by
  obtain ⟨c', o, hrun, he, hm⟩ := hb
  have enter := steps_enter (P := P) (host := NH) (s := s) (f := f) (B := B) hp
    (step_loop har) rest
  have inner := evRun_ctx (stk.drop np).reverse rest (evRun_label np [.loop bt B] hrun)
  have htake : vs.take nr = vs := List.take_of_length_le hlen.le
  have hk' : RunL P host s₁ f₁ (vals ((stk.drop np).reverse ++ vs.reverse) ++ rest) q₂ r := by
    rw [← htake, ← stack_after]
    exact hk
  exact runL_free enter (runL_evRun inner
    (runL_free (exit_normal (P := P) (host := NH) he hm _ rest) hk'))

/-- **A loop whose body branches back to it.** -/
theorem runL_loop_back (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : RunL P host s f (vals (stk.take np).reverse ++ expression B) q₁ (s₁, f₁, .brk 0 vs))
    (hnp : np ≤ vs.length)
    (hk : RunL P host s₁ f₁ (vals (vs.take np ++ stk.drop np).reverse ++ .plain (.loop bt B) ::
      rest) q₂ r) :
    RunL P host s f (vals stk.reverse ++ .plain (.loop bt B) :: rest) (q₁ ++ q₂) r := by
  obtain ⟨c', o, hrun, he, hm⟩ := hb
  have enter := steps_enter (P := P) (host := NH) (s := s) (f := f) (B := B) hp
    (step_loop har) rest
  have inner := evRun_ctx (stk.drop np).reverse rest (evRun_label np [.loop bt B] hrun)
  have hk' : RunL P host s₁ f₁ (vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++
      expression [.loop bt B] ++ rest) q₂ r := by
    rw [← stack_after (nr := np)]
    simpa [expression] using hk
  exact runL_free enter (runL_evRun inner
    (runL_free (exit_br0 (P := P) (host := NH) he hm hnp _ rest) hk'))

/-- **A loop whose body branches to an outer label, returns or traps.** -/
theorem runL_loop_abrupt (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : RunL P host s f (vals (stk.take np).reverse ++ expression B) q₁ (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    RunL P host s f (vals stk.reverse ++ .plain (.loop bt B) :: rest) q₁ (s₁, f₁, fl') := by
  obtain ⟨c', o, hrun, he, hm⟩ := hb
  have enter := steps_enter (P := P) (host := NH) (s := s) (f := f) (B := B) hp
    (step_loop har) rest
  have inner := evRun_ctx (stk.drop np).reverse rest (evRun_label np [.loop bt B] hrun)
  have hx : RunL P host s₁ f₁ (vals (stk.drop np).reverse ++ [.label np [.loop bt B] c'] ++ rest)
      [] (s₁, f₁, fl') := runL_of_wp (exit_abrupt (P := P) (host := NH) he hm hfl _ rest)
  simpa using runL_free enter (runL_evRun inner hx)

/-- An `if` steps, host-free, to the block of its chosen arm (every profile). -/
theorem step_if_armP {t el : List Binaryen.BExpr} {cv : Val} {b : Bool} (hb : Binaryen.truthy cv = some b) :
    Step P NH
      ⟨s, f, vals (cv :: stk).reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩
      ⟨s, f, vals stk.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest⟩ := by
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
  have e : vals (Val.i32 c₀ :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest =
      vals stk.reverse ++ [constI32 c₀,
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] ++ rest := by
    simp [vals, constI32]
  rw [e]
  by_cases h0 : c₀ = 0
  · subst h0
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifFalse (bt := bt) (b₁ := Binaryen.BExpr.lowerList t) (b₂ := Binaryen.BExpr.lowerList el))
  · have h1 : (c₀ != 0) = true := by simpa using h0
    simp only [h1, ↓reduceIte]
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifTrue (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
        (b₂ := Binaryen.BExpr.lowerList el) h0)

/-- An `if` runs the chosen arm as a block. -/
theorem runL_if_arm {t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {q : List (Call (wasmHostSig H))}
    (hb : Binaryen.truthy cv = some b)
    (h : RunL P host s f (vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest) q r) :
    RunL P host s f (vals (cv :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest) q r :=
  runL_free (.single (step_if_armP hb)) h

end Blocks

/-! ## Calls -/

section Calls

variable {s s₁ s₂ : Store H} {f f₁ : Frame} {stk₁ : List Val} {x : FuncIdx} {a : Nat}
  {fi : FuncInst H} {ps rs : List Validation.CValType} {rest fin : List Admin}
  {q : List (Call (wasmHostSig H))}

/-- **The Core run of a direct call answered by a logged callee run**, in context. -/
theorem evRun_oracle_call (hfi : s₁.func? f₁ x = some (a, fi))
    (hst : EvRun P host
      ⟨s₁, f₁, vals (stk₁.take ps.length).reverse ++ [.ref (.func a), .callRefType fi.type]⟩ q
      ⟨s₂, f₁, fin⟩) :
    EvRun P host ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ q
      ⟨s₂, f₁, vals (stk₁.drop ps.length).reverse ++ fin ++ rest⟩ := by
  have hsplit : vals stk₁.reverse =
      vals (stk₁.drop ps.length).reverse ++ vals (stk₁.take ps.length).reverse := by
    conv_lhs => rw [← List.take_append_drop ps.length stk₁]
    simp [vals]
  have h₁ := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
    ((stk₁.drop ps.length).reverse ++ (stk₁.take ps.length).reverse) rest
    (Step.call (s := s₁) (f := f₁) (module_of_func? hfi) (Silmaril.Wasm.Interp.funcs_of_func? hfi))
  have h₂ := evRun_ctx (stk₁.drop ps.length).reverse rest hst
  rw [hsplit]
  simp only [vals_append, List.append_assoc, List.singleton_append] at h₁ h₂ ⊢
  exact .silent (.inl h₁) h₂

end Calls

/-- **A logged callee body is a logged Core `call_ref` run** in any caller frame. -/
theorem evRun_callRef_of_good {s s' : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} {F' : Frame} {flb : Binaryen.Flow}
    {q : List (Call (wasmHostSig H))} (hS : StoreChk s.funcs) (hlen : vs.length = ps.length)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (aga : ArityGood s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s', F', flb))
    (cga : CoreL P host s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s', F', flb) q) (f : Frame) (ws : List Val) (hvs : flb.retVals = some ws) :
    EvRun P host ⟨s, f, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ q
      ⟨s', f, vals (ws.take rs.length).reverse⟩ := by
  have hlocals : (Frame.forCall fi.module vs fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hlen
  obtain ⟨ob, hb, hob⟩ := endsAt_eq (hS a fi fn ps rs hfi hcode hty)
  have hbc : chk s.funcs (Frame.forCall fi.module vs fn.locals).module
      (Frame.forCall fi.module vs fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [hlocals]
    exact hb
  obtain ⟨hok', -⟩ := aga hS hbc
  have hwp := cga hS hbc
  rw [Binaryen.lowerList_liftInstrs] at hwp
  obtain ⟨c', o, hbody, he, hm⟩ := hwp
  have enter : Steps P NH ⟨s, f, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ := by
    obtain ⟨ps', rs', he', hpl, hrl⟩ := expand_of_funcType hty
    rw [← hrl]
    exact .single (Step.callRefFunc trivial hfi he' (hlen.trans hpl.symm) hcode)
  have inner := evRun_frame (f := f) rs.length (evRun_label rs.length [] (by simpa [vals] using hbody))
  have hnorm : ∀ w, flb = .normal w → w.length = rs.length := by
    rintro w rfl
    exact length_of_ends hok' hob
  obtain ⟨s'', res, hret, hK⟩ := frame_ends (P := P) (host := NH) (f := f) he
    (funcPost_of_match (P := P) (host := NH) (s₂ := s') (F := F') hm hvs
      (retVals_length hok' hob hvs) hnorm)
  obtain ⟨rfl, rfl⟩ := hK
  simpa using evRun_trans (evRun_of_free enter) (evRun_trans inner (evRun_of_free hret))

/-! ## Resolved logs -/

/-- The host answers of a log are allowed. -/
abbrev Cons (host : HostSemantics H) (q : List (Call (wasmHostSig H))) : Prop :=
  (coreHostRel host).Consistent q

theorem cons_append {q₁ q₂ : List (Call (wasmHostSig H))} :
    Cons host (q₁ ++ q₂) ↔ Cons host q₁ ∧ Cons host q₂ :=
  List.forall_mem_append

theorem substPre_append {sh : Silmaril.Games.Abstract.Shape} {c : sh.ClosedMod} {u v : List (Call (sh.E ⊕ₛ sh.self))}
    {q : List (Call sh.E)} :
    Shape.SubstPre c (u ++ v) q ↔
      ∃ q₁ q₂, q = q₁ ++ q₂ ∧ Shape.SubstPre c u q₁ ∧ Shape.SubstPre c v q₂ := by
  induction u generalizing q with
  | nil => exact ⟨fun h => ⟨[], q, rfl, .nil, h⟩, fun ⟨q₁, q₂, e, h₁, h₂⟩ => by
      cases h₁; simpa [e] using h₂⟩
  | cons z u ih =>
    constructor
    · intro h
      cases h with
      | ext h =>
        obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := ih.1 h
        exact ⟨_, q₂, by simp, .ext h₁, h₂⟩
      | int hm h =>
        obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := ih.1 h
        exact ⟨_, q₂, by simp, .int hm h₁, h₂⟩
    · rintro ⟨q₁, q₂, rfl, h₁, h₂⟩
      cases h₁ with
      | ext h₁ => exact .ext (ih.2 ⟨_, _, rfl, h₁, h₂⟩)
      | int hm h₁ =>
        rw [List.append_assoc]
        exact Shape.SubstPre.int hm (ih.2 ⟨_, _, rfl, h₁, h₂⟩)

theorem substPre_mk {c : (wasmHShape H).ClosedMod} {a : Nat} {args : List Val} {s₁ s₂ : Store H}
    {b : List Val ⊕ Nat} {rest : List (HCall H)} {q : List (Call (wasmHostSig H))}
    (h : Shape.SubstPre c ((OCall.mk a args s₁ b s₂).lift :: rest) q) :
    ∃ c₁ q', q = c₁ ++ q' ∧ (c₁, .ret b s₂) ∈ c a s₁ args ∧ Shape.SubstPre c rest q' := by
  change Shape.SubstPre c (⟨.inr ⟨a, (args, s₁)⟩, (b, s₂)⟩ :: rest) q at h
  cases h with
  | int hm h => exact ⟨_, _, rfl, hm, h⟩

/-- A finished resolution ending in a return is a prefix resolution. -/
theorem subst_ret {sh : Silmaril.Games.Abstract.Shape} {c : sh.ClosedMod} {R : Type}
    {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {y : CallBeh sh.E sh.S R}
    (h : Shape.Subst c x e y) {b : R} {s : sh.S} (hy : y.2 = .ret b s) :
    Shape.SubstPre c x y.1 ∧ y.2 = e := by
  induction h with
  | nil e => exact ⟨.nil, rfl⟩
  | ext _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hy
    exact ⟨.ext h₁, h₂⟩
  | int hm _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hy
    exact ⟨.int hm h₁, h₂⟩
  | intTrap _ => cases hy
  | intDiv _ => cases hy

/-! ## The returning behaviours that are logged Core runs -/

/-- **Returning closed behaviours that are logged Core runs**: with a consistent log, a
`hostCall` outcome (read through the exit flow), and the event log of the Core run of the call
in any frame, for a checked store and typed arguments. -/
def GoodC (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    (wasmHShape H).ClosedMod := fun a s us =>
  {y | ∀ b s', y.2 = .ret b s' → Cons host y.1 →
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (bfl fl : Binaryen.Flow),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      hostCall host s a us (s', bfl) ∧ exitFlow rs.length bfl = some fl ∧
      endOfFlow fl s' = .ret b s' ∧
      (StoreChk s.funcs → us.length = ps.length → ∀ ws, fl = .normal ws → ∀ f : Frame,
        EvRun P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ y.1
          ⟨s', f, vals ws⟩)}

/-- A returned answer `inl ws` of `GoodC`. -/
theorem goodC_inl {a : Nat} {args : List Val} {s₁ s₂ : Store H} {ws : List Val}
    {c₁ : List (Call (wasmHostSig H))} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hm : (c₁, .ret (.inl ws) s₂) ∈ GoodC P host a s₁ args) (hc : Cons host c₁)
    (hfi : s₁.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    ∃ bfl w, hostCall host s₁ a args (s₂, bfl) ∧ bfl.retVals = some w ∧
      ws.reverse = w.take rs.length ∧
      (StoreChk s₁.funcs → args.length = ps.length → ∀ f : Frame,
        EvRun P host ⟨s₁, f, vals args ++ [.ref (.func a), .callRefType fi.type]⟩ c₁
          ⟨s₂, f, vals ws⟩) := by
  obtain ⟨fi', ps', rs', bfl, fl, hfi', hty', hC, hx, hend, hrun⟩ := hm _ _ rfl hc
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
  rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, End.ret.injEq, Sum.inl.injEq, reduceCtorEq, and_true] at hend
  all_goals subst hend
  all_goals exact ⟨_, w, hC, rfl, by simp, fun hS hn f => hrun hS hn _ rfl f⟩

/-- A returned answer `inr t` of `GoodC` is a thrown `hostCall` outcome. -/
theorem goodC_inr {a : Nat} {args : List Val} {s₁ s₂ : Store H} {t : Nat}
    {c₁ : List (Call (wasmHostSig H))} (hm : (c₁, .ret (.inr t) s₂) ∈ GoodC P host a s₁ args)
    (hc : Cons host c₁) : hostCall host s₁ a args (s₂, .throw t) := by
  obtain ⟨fi', ps', rs', bfl, fl, -, -, hC, hx, hend, -⟩ := hm _ _ rfl hc
  rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t' <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, End.ret.injEq, Sum.inr.injEq, reduceCtorEq, and_true] at hend
  subst hend
  exact hC

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
