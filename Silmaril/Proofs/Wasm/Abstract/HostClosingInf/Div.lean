module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Conv
public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Quiet
public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Log

/-!
# Divergence after a finite log: native to Core (proofs)

The converse of `evRun_div`, every profile: a behaviour `(cs, div)` of `wasmEvFunD` whose log
the host allows is a Core run of the invocation with exactly the host events `cs`, then
host-free divergence.

* `noDiv host`: `host` without its divergent outcomes. Running the logged forward simulation
  against it, every context it builds (`Lifts`) also lifts host-free steps, so host-free
  divergence is carried through the contexts (`diverges_wrap`); its runs are runs of `host`
  (`evRun_of_noDiv`);
* `evalO_quiet_evalL`: a terminating run with host-free callees (`EvalO quietCall`) that does
  not trap is a logged run (`EvalL`) whose calls resolve to no import call;
* `localDivO_fwd`: host-free local divergence (`LocalDivO quietCall`) of checked trees is Core
  host-free divergence. Each unfolding takes a Core step or continues with strictly smaller
  trees (`localDiv_progress`, by strong induction on their size); `InfiniteTrace.coinduct`
  iterates;
* `logDiv_fwd`, `ldlw_fwd`: logged local divergence is a logged Core run with exactly the
  resolved events, then host-free divergence;
* `divChain_fwd`: an infinite descent chain with finitely many import calls is a logged Core run
  through the descents carrying them, then infinitely many host-free descents nested ever
  deeper, each entering a callee in one step;
* `wasmEvFunD_div_evRun`: **the converse of quiescent adequacy**.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp
open Shape (SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Hosts without divergence -/

/-- `host` without its divergent outcomes. -/
def noDiv (host : HostSemantics H) : HostSemantics H := fun h s vs o =>
  host h s vs o ∧ o ≠ .diverged

theorem nativeHostSlice_noDiv (hH : NativeHostSlice host) : NativeHostSlice (noDiv host) where
  funcs h s vs s' r hr := hH.funcs h s vs s' r hr.1
  arity s a fi h ps rs vs ws s' hf hc hty hr := hH.arity s a fi h ps rs vs ws s' hf hc hty hr.1
  noThrow h s vs s' t hr := hH.noThrow h s vs s' t hr.1

theorem cons_noDiv {q : List (Call (wasmHostSig H))} (hc : Cons host q) : Cons (noDiv host) q :=
  fun e he => ⟨hc e he, fun h => nomatch h⟩

theorem evRun_of_noDiv {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P (noDiv host) c cs c') : EvRun P host c cs c' := by
  induction h with
  | refl => exact .refl _
  | silent hs _ ih =>
    rcases hs with hs | ⟨-, _, _, _, _, -, hd⟩
    · exact .silent (.inl hs) ih
    · exact absurd rfl hd.2
  | event hs _ ih =>
    obtain ⟨E, a, hdec, hst, hans, hc'⟩ := hs
    exact .event ⟨E, a, hdec, hst, hans.1, hc'⟩ ih

section Wrap

variable {host' : HostSemantics H} (hnd : ∀ h s vs, ¬ host' h s vs .diverged)
  {W : Config H → Config H} (hW : Lifts P host' W)
include hnd hW

/-- A context lifting the labelled steps of a host without divergence lifts host-free steps. -/
theorem step_wrap {c c' : Config H} (h : Step P NH c c') : Step P NH (W c) (W c') := by
  rcases hW c none c' (.inl h) with h' | ⟨-, _, _, _, _, -, hd⟩
  · exact h'
  · exact absurd hd (hnd _ _ _)

theorem tg_wrap {c c' : Config H} (h : Relation.TransGen (Step P NH) c c') :
    Relation.TransGen (Step P NH) (W c) (W c') := by
  induction h with
  | single st => exact .single (step_wrap hnd hW st)
  | tail _ st ih => exact ih.tail (step_wrap hnd hW st)

/-- **Host-free divergence lifts through such a context.** -/
theorem diverges_wrap {c : Config H} (h : Diverges P NH c) : Diverges P NH (W c) :=
  Silmaril.InfiniteTrace.map W (fun _ _ => step_wrap hnd hW) h

end Wrap

/-! ## Terminating runs with host-free callees -/

theorem exitFlow_retVals {fl : Binaryen.Flow} {vs : List Val} (h : fl.retVals = some vs)
    (n : Nat) : exitFlow n fl = some (.normal (vs.take n).reverse) := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | t <;>
    simp_all [Binaryen.Flow.retVals, exitFlow]

theorem ne_trap_of_blockVals {fl : Binaryen.Flow} {vs : List Val} (h : fl.blockVals = some vs) :
    fl ≠ .trap := by
  rintro rfl
  simp [Binaryen.Flow.blockVals] at h

/-- A host-free answer at a call is a closure behaviour with no import call. -/
theorem quiet_ans {s₁ s₂ : Store H} {f₁ : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {us : List Val} {fl fl' : Binaryen.Flow}
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : quietCall s₁ a us (s₂, fl)) (hx : exitFlow rs.length fl = some fl') :
    ([], endOfFlow fl' s₂) ∈ Shape.close wasmHOpen a s₁ us := by
  obtain ⟨fi', ps', rs', fl'', hf', hty', hx', hm⟩ := hcall
  have hfa := Silmaril.Wasm.Interp.funcs_of_func? hfi
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hfa)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
  obtain rfl : fl'' = fl' := Option.some.inj (hx'.symm.trans hx)
  exact hm

theorem sp_app {u v : List (OCall H)}
    (h₁ : SubstPre (Shape.close wasmHOpen) (u.map OCall.lift) [])
    (h₂ : SubstPre (Shape.close wasmHOpen) (v.map OCall.lift) []) :
    SubstPre (Shape.close wasmHOpen) ((u ++ v).map OCall.lift) [] := by
  rw [List.map_append]
  exact substPre_append.2 ⟨[], [], rfl, h₁, h₂⟩

/-- **A non-trapping terminating run with host-free callees is a logged run** whose calls
resolve to no import call. -/
theorem evalO_quiet_evalL {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalO quietCall s f stk es r) :
    r.2.2 ≠ .trap → ∃ l, EvalL s f stk es l r ∧
      SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) [] := by
  induction h with
  | nil => exact fun _ => ⟨[], .nil, .nil⟩
  | argsAbort _ hfl ih =>
    intro ht
    obtain ⟨l, hl, hq⟩ := ih ht
    exact ⟨l, .argsAbort hl hfl, hq⟩
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r hargs hfi hty hcall hvs hk ih₁ ih₂ =>
    intro ht
    obtain ⟨l₁, hl₁, hq₁⟩ := ih₁ nofun
    obtain ⟨l₂, hl₂, hq₂⟩ := ih₂ ht
    have hm := quiet_ans hfi hty hcall (exitFlow_retVals hvs rs.length)
    refine ⟨_, .callRet (ws := (vs.take rs.length).reverse) hl₁ hfi hty
      (by rw [List.reverse_reverse]; exact hl₂), ?_⟩
    rw [List.map_append]
    exact substPre_append.2 ⟨[], [], rfl, hq₁, .int (c₁ := []) (q := []) hm hq₂⟩
  | callTrap _ _ _ _ _ => exact fun ht => absurd rfl ht
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t hargs hfi hty hcall ih =>
    intro _
    obtain ⟨l₁, hl₁, hq₁⟩ := ih nofun
    have hm := quiet_ans hfi hty hcall
      (show exitFlow rs.length (.throw t) = some (.throw t) from rfl)
    refine ⟨_, .callThrow hl₁ hfi hty, ?_⟩
    rw [List.map_append]
    exact substPre_append.2 ⟨[], [], rfl, hq₁, .int (c₁ := []) (q := []) hm .nil⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro ht
    obtain ⟨l₁, hl₁, hq₁⟩ := ih₁ nofun
    obtain ⟨l₂, hl₂, hq₂⟩ := ih₂ ht
    exact ⟨_, .opOk hi hl₁ hflat hl₂, sp_app hq₁ hq₂⟩
  | opStop hi _ hflat hfl ih =>
    intro _
    obtain ⟨l, hl, hq⟩ := ih nofun
    exact ⟨l, .opStop hi hl hflat hfl, hq⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro ht
    obtain ⟨l₁, hl₁, hq₁⟩ := ih₁ (ne_trap_of_blockVals hvs)
    obtain ⟨l₂, hl₂, hq₂⟩ := ih₂ ht
    exact ⟨_, .blockOk har hl₁ hvs hl₂, sp_app hq₁ hq₂⟩
  | blockBrk har _ ih =>
    intro _
    obtain ⟨l, hl, hq⟩ := ih nofun
    exact ⟨l, .blockBrk har hl, hq⟩
  | blockEsc har _ hfl ih =>
    intro ht
    obtain ⟨l, hl, hq⟩ := ih ht
    exact ⟨l, .blockEsc har hl hfl, hq⟩
  | loopOk har _ _ ih₁ ih₂ =>
    intro ht
    obtain ⟨l₁, hl₁, hq₁⟩ := ih₁ nofun
    obtain ⟨l₂, hl₂, hq₂⟩ := ih₂ ht
    exact ⟨_, .loopOk har hl₁ hl₂, sp_app hq₁ hq₂⟩
  | loopBack har _ _ ih₁ ih₂ =>
    intro ht
    obtain ⟨l₁, hl₁, hq₁⟩ := ih₁ nofun
    obtain ⟨l₂, hl₂, hq₂⟩ := ih₂ ht
    exact ⟨_, .loopBack har hl₁ hl₂, sp_app hq₁ hq₂⟩
  | loopBrk har _ ih =>
    intro _
    obtain ⟨l, hl, hq⟩ := ih nofun
    exact ⟨l, .loopBrk har hl, hq⟩
  | loopEsc har _ hfl ih =>
    intro ht
    obtain ⟨l, hl, hq⟩ := ih ht
    exact ⟨l, .loopEsc har hl hfl, hq⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro ht
    obtain ⟨l₁, hl₁, hq₁⟩ := ih₁ nofun
    obtain ⟨l₂, hl₂, hq₂⟩ := ih₂ (ne_trap_of_blockVals hvs)
    obtain ⟨l₃, hl₃, hq₃⟩ := ih₃ ht
    exact ⟨_, .ifOk hl₁ hb har hl₂ hvs hl₃, sp_app (sp_app hq₁ hq₂) hq₃⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    intro _
    obtain ⟨l₁, hl₁, hq₁⟩ := ih₁ nofun
    obtain ⟨l₂, hl₂, hq₂⟩ := ih₂ nofun
    exact ⟨_, .ifBrk hl₁ hb har hl₂, sp_app hq₁ hq₂⟩
  | ifEsc _ hb har _ hfl ih₁ ih₂ =>
    intro ht
    obtain ⟨l₁, hl₁, hq₁⟩ := ih₁ nofun
    obtain ⟨l₂, hl₂, hq₂⟩ := ih₂ ht
    exact ⟨_, .ifEsc hl₁ hb har hl₂ hfl, sp_app hq₁ hq₂⟩
  | ifAbort _ hfl ih =>
    intro ht
    obtain ⟨l, hl, hq⟩ := ih ht
    exact ⟨l, .ifAbort hl hfl, hq⟩

/-! ## Host-free local divergence is Core divergence -/

/-- **A loop iteration branching back**, host-free, takes at least one Core step. -/
theorem loopBack_tg {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
    {body es : List Binaryen.BExpr} {np nr : Nat} {l : List (OCall H)}
    {labels : List Nat} {ret : Nat} {out : Option Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (h : EvalL s f (stk.take np) body l (s₁, f₁, .brk 0 vs))
    (hq : SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) [])
    (hS : StoreChk s.funcs)
    (hchk : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.loop bt body :: es) = some out) :
    Relation.TransGen (Step P NH) ⟨s, f, vals stk.reverse ++
        expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩
        ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ ∧
      StoreChk s₁.funcs ∧
      chk s₁.funcs f₁.module f₁.locals.length ret labels (some (vs.take np ++ stk.drop np).length)
        (.loop bt body :: es) = some out := by
  have hH : Interp.NativeHostSlice (NH : HostSemantics H) := nativeHostSlice_closedHost
  obtain ⟨-, hS', hchk'⟩ := loopBack_glue (P := P) hH har h hq (fun _ h => nomatch h) hS hchk
  refine ⟨?_, hS', hchk'⟩
  obtain ⟨d, cl⟩ := evalL_fwd (P := P) hH h [] (substPre_mono (close_le_goodC hH) hq)
    (fun _ h => nomatch h)
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hchk
  obtain ⟨_, _, hbc, hok, -⟩ := body_facts hS (evalH_good (P := P) hH d).1 hb
    (take_length_of_le hp)
  obtain ⟨m, hm', hle⟩ := hok
  have hnp : np ≤ vs.length := by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm'
    exact hm' ▸ hle
  obtain ⟨c', o, hrun, he, hm⟩ := cl hS hbc
  rw [code_loop, code_loop]
  exact tg_loop_back (P := P) (host := NH) har hp (evRun_nil_steps hrun rfl) he hm hnp

/-- One round of progress of host-free local divergence: a Core step, at least, to another
checked, locally divergent problem in a context. -/
def Adv (P : Silmaril.Wasm.Numerics.Profile) (c : Config H) : Prop :=
  ∃ (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
    (W : Config H → Config H), Lifts P NH W ∧
    Relation.TransGen (Step P NH) c
      (W ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) ∧
    LocalDivO quietCall s f stk es ∧ StoreChk s.funcs ∧
    ∃ (labels : List Nat) (ret : Nat) (out : Option Nat),
      chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out

/-- **Progress**: a checked, host-free locally divergent problem takes at least one Core step,
in any context, to another one. -/
theorem localDiv_progress : ∀ (n : Nat) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr}, sizeOf es = n → LocalDivO quietCall s f stk es →
    StoreChk s.funcs → ∀ {labels : List Nat} {ret : Nat} {out : Option Nat},
    chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    ∀ W : Config H → Config H, Lifts P NH W →
      Adv P (W ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s f stk es hn hd hS labels ret out hchk W hW
  have hH : Interp.NativeHostSlice (NH : HostSemantics H) := nativeHostSlice_closedHost
  have jump : ∀ {s' : Store H} {f' : Frame} {stk' : List Val} {es' : List Binaryen.BExpr}
      {V : Config H → Config H} {labels' : List Nat} {ret' : Nat} {out' : Option Nat},
      Lifts P NH V → sizeOf es' < n →
      Steps P NH ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩
        (V ⟨s', f', vals stk'.reverse ++ expression (Binaryen.BExpr.lowerList es')⟩) →
      LocalDivO quietCall s' f' stk' es' → StoreChk s'.funcs →
      chk s'.funcs f'.module f'.locals.length ret' labels' (some stk'.length) es' = some out' →
      Adv P (W ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) := by
    intro s' f' stk' es' V labels' ret' out' hV hlt hst hd' hS' hchk'
    rcases Relation.ReflTransGen.cases_head hst with heq | ⟨c₁, st, rest⟩
    · rw [heq]
      exact ih _ hlt rfl hd' hS' hchk' (fun c => W (V c)) (lifts_comp hW hV)
    · exact ⟨s', f', stk', es', fun c => W (V c), lifts_comp hW hV,
        tg_wrap (fun _ _ _ h => h) hW (Relation.TransGen.head' st rest), hd', hS', _, _, _, hchk'⟩
  have cont : ∀ {e : Binaryen.BExpr} {es₀ : List Binaryen.BExpr} {s₂ : Store H} {f₂ : Frame}
      {stk₂ : List Val}, es = e :: es₀ → EvalO quietCall s f stk [e] (s₂, f₂, .normal stk₂) →
      LocalDivO quietCall s₂ f₂ stk₂ es₀ →
      Adv P (W ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) := by
    rintro e es₀ s₂ f₂ stk₂ rfl d hk
    obtain ⟨l, hl, hq⟩ := evalO_quiet_evalL d nofun
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hl hq (fun _ h => nomatch h) hS hchk
    exact jump lifts_id (by rw [← hn]; simp) (evRun_nil_steps run rfl) hk hS' hchk'
  cases localDivO_iff_step.mp hd with
  | @args _ _ _ i args es₀ h =>
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    refine jump (lifts_ctx [] (.plain i :: expression (Binaryen.BExpr.lowerList es₀)))
      (by rw [← hn]; simp; omega) ?_ h hS ha
    rw [code_op]
    exact .refl
  | callee _ _ _ _ h => exact (h : False).elim
  | callRet hargs hfi hty hcall hvs h => exact cont rfl (.callOk hargs hfi hty hcall hvs .nil) h
  | opK hi hargs hflat h => exact cont rfl (.opOk hi hargs hflat .nil) h
  | blockK har hbody hvs h => exact cont rfl (.blockOk har hbody hvs .nil) h
  | loopK har hbody h => exact cont rfl (.loopOk har hbody .nil) h
  | ifK hc hb har harm hvs h => exact cont rfl (.ifOk hc hb har harm hvs .nil) h
  | @block _ _ _ bt body es₀ np nr har h =>
    obtain ⟨⟨ob, hbc⟩, enter⟩ := block_enter (P := P) har hchk
    exact jump (lifts_comp (lifts_ctx (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es₀))) (lifts_label nr []))
      (by rw [← hn]; simp; omega) enter h hS hbc
  | @loop _ _ _ bt body es₀ np nr har h =>
    obtain ⟨⟨ob, hbc⟩, enter⟩ := loop_enter (P := P) har hchk
    exact jump (lifts_comp (lifts_ctx (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es₀)))
      (lifts_label np [.loop bt (Binaryen.BExpr.lowerList body)]))
      (by rw [← hn]; simp; omega) enter h hS hbc
  | @loopBack _ s₁ _ f₁ _ vs bt body es₀ np nr har hbody h =>
    obtain ⟨l, hl, hq⟩ := evalO_quiet_evalL hbody nofun
    obtain ⟨tg, hS', hchk'⟩ := loopBack_tg (P := P) har hl hq hS hchk
    exact ⟨_, _, _, _, W, hW, tg_wrap (fun _ _ _ h => h) hW tg, h, hS', _, _, _, hchk'⟩
  | @cond _ _ _ bt c t el es₀ h =>
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oc, hco, -⟩ := chk1_ifE h1
    refine jump (lifts_ctx [] (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
      (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es₀)))
      (by rw [← hn]; simp; omega) ?_ h hS hco
    rw [code_if]
    exact .refl
  | @arm _ s₁ _ f₁ _ stk₁ cv b bt c t el es₀ np nr hc hb har h =>
    obtain ⟨l, hl, hq⟩ := evalO_quiet_evalL hc nofun
    obtain ⟨hS', ⟨ob, hbc⟩, run⟩ := arm_glue (P := P) hH hl hb har hq (fun _ h => nomatch h)
      hS hchk
    exact jump (lifts_comp (lifts_ctx (stk₁.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es₀))) (lifts_label nr []))
      (by rw [← hn]; cases b <;> simp <;> omega) (evRun_nil_steps run rfl) h hS' hbc

/-- **Host-free local divergence of checked trees is Core host-free divergence.** -/
theorem localDivO_fwd {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hd : LocalDivO quietCall s f stk es) (hS : StoreChk s.funcs)
    (hchk : chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out) :
    Diverges P NH ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ := by
  refine Silmaril.InfiniteTrace.coinduct (fun c => ∃ (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) (W : Config H → Config H), Lifts P NH W ∧
      Relation.ReflTransGen (Step P NH) c
        (W ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) ∧
      LocalDivO quietCall s f stk es ∧ StoreChk s.funcs ∧
      ∃ (labels : List Nat) (ret : Nat) (out : Option Nat),
        chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out) ?_
    ⟨s, f, stk, es, fun c => c, lifts_id, .refl, hd, hS, _, _, _, hchk⟩
  rintro c ⟨s, f, stk, es, W, hW, hp, hd, hS, labels, ret, out, hchk⟩
  rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨c₁, hstep, hp'⟩
  · obtain ⟨s', f', stk', es', W', hW', hc', hd', hS', hk⟩ :=
      localDiv_progress (P := P) _ rfl hd hS hchk W hW
    obtain ⟨c₁, hstep, hp'⟩ := Relation.TransGen.head'_iff.mp hc'
    exact ⟨c₁, hstep, s', f', stk', es', W', hW', hp', hd', hS', hk⟩
  · exact ⟨c₁, hstep, s, f, stk, es, W, hW, hp', hd, hS, labels, ret, out, hchk⟩

/-! ## Logged local divergence -/

/-- **Logged local divergence is a logged Core run, then host-free divergence**, with exactly
the events of its resolved prefix. -/
theorem logDiv_fwd (hH : Interp.NativeHostSlice host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {l : List (OCall H)} (h : LogDiv s f stk es l) :
    ∀ q, SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q → Cons host q →
      ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChk s.funcs →
      chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
      ∃ c', EvRun P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩
        q c' ∧ Diverges P NH c' := by
  induction h with
  | div hd =>
    intro q hq _ labels ret out hS hchk
    cases hq
    exact ⟨_, .refl _, localDivO_fwd hd hS hchk⟩
  | @args s f stk i args es l _ ih =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨c', run, hdv⟩ := ih q hq hc hS ha
    let rest : List Admin := .plain i :: expression (Binaryen.BExpr.lowerList es)
    refine ⟨_, ?_, diverges_wrap (host' := NH) (fun _ _ _ h => h) (lifts_ctx (P := P) [] rest) hdv⟩
    rw [code_op]
    exact evRun_wrap _ (lifts_ctx (P := P) (host := host) [] rest) run
  | @callK s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ hargs hfi hty _ ih =>
    intro q hq hc labels ret out hS hchk
    have e : (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂).map
        OCall.lift = (l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]).map
          OCall.lift ++ l₂.map OCall.lift := by simp
    rw [e] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH (.callRet hargs hfi hty .nil) h₁ hc.1 hS hchk
    obtain ⟨c', run', hdv⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨c', evRun_trans run run', hdv⟩
  | opK hi hargs hflat _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.opOk hi hargs hflat (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    obtain ⟨c', run', hdv⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨c', evRun_trans run run', hdv⟩
  | @block s f stk bt body es np nr l har _ ih =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := block_enter (P := P) har hchk
    obtain ⟨c', run, hdv⟩ := ih q hq hc hS hbc
    let rest : List Admin := expression (Binaryen.BExpr.lowerList es)
    refine ⟨_, ?_, diverges_wrap (host' := NH) (fun _ _ _ h => h)
      (lifts_comp (lifts_ctx (P := P) (stk.drop np).reverse rest) (lifts_label nr [])) hdv⟩
    have := evRun_wrap _ (lifts_ctx (P := P) (host := host) (stk.drop np).reverse rest)
      (evRun_wrap _ (lifts_label (P := P) (host := host) nr []) run)
    exact evRun_trans (evRun_of_free enter) this
  | blockK har hbody hvs _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.blockOk har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    obtain ⟨c', run', hdv⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨c', evRun_trans run run', hdv⟩
  | @loop s f stk bt body es np nr l har _ ih =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := loop_enter (P := P) har hchk
    obtain ⟨c', run, hdv⟩ := ih q hq hc hS hbc
    let rest : List Admin := expression (Binaryen.BExpr.lowerList es)
    let cont : List Instr := [.loop bt (Binaryen.BExpr.lowerList body)]
    refine ⟨_, ?_, diverges_wrap (host' := NH) (fun _ _ _ h => h)
      (lifts_comp (lifts_ctx (P := P) (stk.drop np).reverse rest) (lifts_label np cont)) hdv⟩
    have := evRun_wrap _ (lifts_ctx (P := P) (host := host) (stk.drop np).reverse rest)
      (evRun_wrap _ (lifts_label (P := P) (host := host) np cont) run)
    exact evRun_trans (evRun_of_free enter) this
  | loopK har hbody _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.loopOk har hbody (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    obtain ⟨c', run', hdv⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨c', evRun_trans run run', hdv⟩
  | loopBack har hbody _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨run, hS', hchk'⟩ := loopBack_glue (P := P) hH har hbody h₁ hc.1 hS hchk
    obtain ⟨c', run', hdv⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨c', evRun_trans run run', hdv⟩
  | @cond s f stk bt c t el es l _ ih =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oc, hco, -⟩ := chk1_ifE h1
    obtain ⟨c', run, hdv⟩ := ih q hq hc hS hco
    let rest : List Admin := .plain (.if_ bt (Binaryen.BExpr.lowerList t)
      (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)
    refine ⟨_, ?_, diverges_wrap (host' := NH) (fun _ _ _ h => h) (lifts_ctx (P := P) [] rest) hdv⟩
    rw [code_if]
    exact evRun_wrap _ (lifts_ctx (P := P) (host := host) [] rest) run
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr l₁ l₂ hcE hb har _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨hS', ⟨ob, hbc⟩, run⟩ := arm_glue (P := P) hH hcE hb har h₁ hc.1 hS hchk
    obtain ⟨c', run', hdv⟩ := ih q₂ h₂ hc.2 hS' hbc
    let rest : List Admin := expression (Binaryen.BExpr.lowerList es)
    refine ⟨_, ?_, diverges_wrap (host' := NH) (fun _ _ _ h => h)
      (lifts_comp (lifts_ctx (P := P) (stk₁.drop np).reverse rest) (lifts_label nr [])) hdv⟩
    exact evRun_trans run (evRun_wrap _ (lifts_ctx (P := P) (host := host) (stk₁.drop np).reverse rest)
      (evRun_wrap _ (lifts_label (P := P) (host := host) nr []) run'))
  | ifK hcE hb har harm hvs _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append, List.map_append] at hq
    obtain ⟨q₁₂, q₃, rfl, h₁₂, h₃⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.ifOk hcE hb har harm hvs (es := []) .nil
    rw [List.append_nil] at hE
    rw [← List.map_append] at h₁₂
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁₂ hc.1 hS hchk
    obtain ⟨c', run', hdv⟩ := ih q₃ h₃ hc.2 hS' hchk'
    exact ⟨c', evRun_trans run run', hdv⟩

/-- **A call diverging locally after a log** (`LDLw`) is a Core run of the call with exactly the
resolved events, then host-free divergence, inside the callee frame. -/
theorem ldlw_fwd (hH : Interp.NativeHostSlice host) {z : (wasmOShape H).self.Op}
    {u : List (HCall H)} {q : List (Call (wasmHostSig H))} (hz : InvC z) (h : LDLw z u)
    (hq : SubstPre (Shape.close wasmHOpen) u q) (hc : Cons host q) (g : Frame) :
    ∃ c', EvRun P host (callAt z g) q c' ∧ Diverges P NH c' := by
  obtain ⟨fi, fn, l, hf, hcode, hL, rfl⟩ := h
  obtain ⟨fi', ps, rs, hf', hty, hn, hS⟩ := hz
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  obtain ⟨ob, hbc⟩ := body_chk hS hf hcode hty hn
  obtain ⟨c', run, hdv⟩ := logDiv_fwd (P := P) hH hL q hq hc hS hbc
  refine ⟨_, evRun_trans (evRun_of_free (enter_body (P := P) hf hcode hty hn g))
    (evRun_wrap _ (lifts_frame (P := P) (host := host) rs.length g)
      (evRun_wrap _ (lifts_label (P := P) (host := host) rs.length []) run)), ?_⟩
  exact diverges_wrap (host' := NH) (fun _ _ _ h => h) (lifts_frame (P := P) (host := NH) rs.length g)
    (diverges_wrap (host' := NH) (fun _ _ _ h => h) (lifts_label (P := P) (host := NH) rs.length []) hdv)

/-! ## Infinite descent chains -/

/-- **Entering a Wasm callee is one host-free step.** -/
theorem enter_body_step {y : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hf : y.2.2.funcs[y.1]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hn : y.2.1.length = ps.length) (g : Frame) :
    Step P NH (callAt y g) ⟨y.2.2, g, [.frame rs.length (Frame.forCall fi.module y.2.1 fn.locals)
      [.label rs.length [] (vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body)))]]⟩ := by
  rw [callAt_code hf, Binaryen.lowerList_liftInstrs]
  obtain ⟨ps', rs', he', hpl, hrl⟩ := expand_of_funcType hty
  rw [← hrl]
  simpa [vals] using
    (Step.callRefFunc (P := P) (host := NH) (f := g)
      (show Admin.IsCallRef (.callRefType fi.type) from trivial) hf he' (hn.trans hpl.symm) hcode)

/-- **A descent, its first Core step separated**: entering the callee is one host-free step. -/
theorem descends_fwd1 (hH : Interp.NativeHostSlice host) {x y : (wasmHShape H).self.Op}
    {q : List (Call (wasmHostSig H))}
    (h : Shape.Descends wasmHOpen (Shape.close wasmHOpen) x q y) (hc : Cons host q)
    (hx : InvC x) :
    InvC y ∧ ∀ g : Frame, ∃ (F' : Frame) (V : Config H → Config H) (c₁ : Config H),
      Lifts P host V ∧ Step P NH (callAt x g) c₁ ∧ EvRun P host c₁ q (V (callAt y F')) := by
  obtain ⟨fi, fn, ps, rs, l, hf, hcode, hty, hr, hq⟩ := descends_unwrap h
  obtain ⟨fi', ps', rs', hf', hty', hn, hS⟩ := hx
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  obtain ⟨ob, hbc⟩ := body_chk hS hf hcode hty hn
  obtain ⟨hy, W, F', hW, run⟩ := reachL_fwd (P := P) hH hr q hq hc hS hbc
  refine ⟨hy, fun g => ⟨F', _, _, lifts_comp (lifts_frame rs.length g)
    (lifts_comp (lifts_label rs.length []) hW), enter_body_step (P := P) hf hcode hty hn g, ?_⟩⟩
  exact evRun_wrap _ (lifts_frame (P := P) (host := host) rs.length g)
    (evRun_wrap _ (lifts_label (P := P) (host := host) rs.length []) run)

/-- **An infinite descent chain with finitely many import calls** is a Core run with exactly
those events, then host-free divergence through the remaining descents, nested ever deeper. -/
theorem divChain_fwd (hH : Interp.NativeHostSlice host) {x : (wasmHShape H).self.Op}
    {qs : List (Call (wasmHostSig H))}
    (h : Shape.DivChain wasmHOpen (Shape.close wasmHOpen) x qs) (hc : Cons host qs)
    (hx : InvC x) (g₀ : Frame) :
    ∃ c', EvRun P host (callAt x g₀) qs c' ∧ Diverges P NH c' := by
  classical
  have hH₀ := nativeHostSlice_noDiv hH
  have hnd : ∀ h s vs, ¬ noDiv host h s vs .diverged := fun _ _ _ h => h.2 rfl
  obtain ⟨gs, q, N, rfl, hd, hz, rfl⟩ := h
  have hcq : ∀ n, Cons (noDiv host) (q n) := by
    intro n
    by_cases hn : N ≤ n
    · rw [hz n hn]
      exact fun _ h => nomatch h
    · exact cons_noDiv (fun e he =>
        hc e (List.mem_flatMap.2 ⟨n, List.mem_range.2 (by omega), he⟩))
  have inv : ∀ n, InvC (gs n) := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => exact (descends_fwd1 (P := P) hH₀ (hd n) (hcq n) ih).1
  have D := fun n => (descends_fwd1 (P := P) hH₀ (hd n) (hcq n) (inv n)).2
  let F : Nat → Frame := fun n =>
    Nat.rec (motive := fun _ => Frame) g₀ (fun n Fn => Classical.choose (D n Fn)) n
  have hV : ∀ n, ∃ (V : Config H → Config H) (c₁ : Config H), Lifts P (noDiv host) V ∧
      Step P NH (callAt (gs n) (F n)) c₁ ∧
        EvRun P (noDiv host) c₁ (q n) (V (callAt (gs (n + 1)) (F (n + 1)))) :=
    fun n => Classical.choose_spec (D n (F n))
  choose V c₁ hVl hst hrun using hV
  let O : Nat → Config H → Config H := fun n =>
    Nat.rec (motive := fun _ => Config H → Config H) (fun c => c)
      (fun n On => fun c => On (V n c)) n
  have hO : ∀ n, Lifts P (noDiv host) (O n) := by
    intro n
    induction n with
    | zero => exact lifts_id
    | succ n ih => exact lifts_comp ih (hVl n)
  let K : Nat → Config H := fun n => O n (callAt (gs n) (F n))
  have seg : ∀ n, EvRun P (noDiv host) (K n) (q n) (K (n + 1)) := fun n =>
    .silent (.inl (step_wrap hnd (hO n) (hst n))) (evRun_wrap (O n) (hO n) (hrun n))
  have pre : ∀ m, EvRun P (noDiv host) (K 0) ((List.range m).flatMap q) (K m) := by
    intro m
    induction m with
    | zero => exact .refl _
    | succ m ih =>
      rw [flatMap_range_add]
      simpa using evRun_trans ih (seg m)
  have div : Diverges P NH (K N) := by
    refine Silmaril.InfiniteTrace.coinduct
      (fun c => ∃ n, N ≤ n ∧ Relation.ReflTransGen (Step P NH) c (K n)) ?_ ⟨N, le_rfl, .refl⟩
    rintro c ⟨n, hn, hp⟩
    rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨c₂, st, hp'⟩
    · refine ⟨O n (c₁ n), step_wrap hnd (hO n) (hst n), n + 1, by omega, ?_⟩
      have r := evRun_wrap (O n) (hO n) (hrun n)
      rw [hz n hn] at r
      exact evRun_nil_steps r rfl
    · exact ⟨c₂, st, n, hn, hp'⟩
  exact ⟨K N, evRun_of_noDiv (pre N), div⟩

/-! ## The converse of quiescent adequacy -/

/-- **The converse of quiescent adequacy** (every profile, the native host slice, checked
stores, typed invocations): every divergent behaviour `(cs, div)` of `wasmEvFunD` whose log the
host allows is a Core run of the invocation with exactly the host events `cs`, then host-free
divergence. -/
theorem wasmEvFunD_div_evRun (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .div) ∈ wasmEvFunD s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    ∃ c', EvRun P host (invoke s a vs) cs c' ∧ Diverges P (fun _ _ _ _ => False) c' := by
  have hx := invC_of_invokeOk hS hok
  change ∃ c', EvRun P host (callAt ⟨a, (vs, s)⟩ {}) cs c' ∧ Diverges P NH c'
  rcases h with (hcl | ⟨-, hch⟩) | ⟨-, z, qs, u, q, hp, hz, hq, he⟩
  · exact (close_ne_div hcl).elim
  · exact divChain_fwd hH hch hc hx {}
  · have he' : cs = qs ++ q := he
    subst he'
    have hc' : Cons host (qs ++ q) := hc
    rw [cons_append] at hc'
    have hH₀ := nativeHostSlice_noDiv hH
    obtain ⟨hzI, D⟩ := descPath_fwd (P := P) hH₀ hp (cons_noDiv hc'.1) hx
    obtain ⟨F', V, hV, run⟩ := D {}
    obtain ⟨c', run', hdv⟩ := ldlw_fwd (P := P) hH₀ hzI hz hq (cons_noDiv hc'.2) F'
    exact ⟨V c', evRun_of_noDiv (evRun_trans run (evRun_wrap V hV run')),
      diverges_wrap (fun _ _ _ h => h.2 rfl) hV hdv⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
