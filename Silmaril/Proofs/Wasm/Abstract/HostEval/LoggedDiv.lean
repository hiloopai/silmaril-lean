module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.LoggedWhole
public import Silmaril.Proofs.Wasm.Abstract.HostEval.DivWhole
public import Silmaril.Wasm.Abstract.HostClosingInf.Defs

/-!
# Divergence after a logged prefix (proofs)

`div_wholeL`: in the deterministic profile `SingleThreaded.profile o`, for a host with typed
answers in the native host slice, a Core run of lowered, arity-checked, typed trees with the
host events `cs`, then host-free divergence (`HostCall.EvDiv`), diverges natively after a
logged prefix whose calls resolve to **exactly** `cs` (`LogDivOut Q`): within the function
(`LogDiv`), or in a callee reached after a resolved prefix, the callee diverging after the rest
of the log as `Q` says.

`Q` is closed under two hypotheses, discharged in `Silmaril.Wasm.Abstract.HostClosingInf`:
`hnat` reads host-free native divergence (`EvalDivO closedCall`) as `LogDivOut Q` with the empty
log, and `hfun` reads `LogDivOut Q` of a Wasm callee's body as `Q` of the call.

The induction is that of `back_wholeL`: on the measure of `EvDiv` (the length of the run to its
last event), then the tree size. At each tree the run is split (`HostCall.evDiv_seq_split`,
`evDiv_label_seq_split`, `evDiv_frame_seq_split`, `evDiv_host_call`): a part that diverges with
the remaining log is the next problem; a part that runs to a stuck end is read by `back_wholeL`
as a logged native run with its own part of the log. A callee body and a loop iteration are
entered by a unique host-free step, so with events left the measure decreases. With no event
left, `div_whole` at the closed host gives the host-free native divergence for `hnat`.

`invoke_divL`, `evRun_divL`: the same for an invocation, as `Q` of the invocation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H} {o : GrowOracle}

/-- The divergence of callees after a log. -/
abbrev CalleeDiv (H : Type) : Type :=
  (wasmOShape H).self.Op → List (Call (wasmHostSig H)) → Prop

/-- The statement for the measure `n` and the trees `es`. -/
def DivGoalL (o : GrowOracle) (host : HostSemantics H) (Q : CalleeDiv H) (n : Nat)
    (es : List Binaryen.BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (labels : List Nat) (ret : Nat) (out : Option Nat)
    (cs : List (Call (wasmHostSig H))), Interp.StoreChk s.funcs →
    Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ →
    EvDiv (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ cs →
    LogDivOut Q s f stk es cs

/-- Host-free native divergence, with the empty log. -/
def NatDiv (Q : CalleeDiv H) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr),
    EvalDivO closedCall s f stk es → LogDivOut Q s f stk es []

/-- The divergence of a Wasm callee's body is that of the call. -/
def FunDiv (Q : CalleeDiv H) : Prop :=
  ∀ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType)
    (cs : List (Call (wasmHostSig H))), y.2.2.funcs[y.1]? = some fi → fi.code = .wasm fn →
    Validation.DefType.funcType? fi.type = some (ps, rs) →
    LogDivOut Q y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body)
      cs → Q y cs

/-! ## Bookkeeping -/

theorem hostTyped_closedHostL : HostTyped (Binaryen.closedHost : HostSemantics H) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => False.elim h

theorem nativeHostSlice_closedHostL :
    Interp.NativeHostSlice (Binaryen.closedHost : HostSemantics H) :=
  ⟨fun _ _ _ _ _ h => False.elim h, fun _ _ _ _ _ _ _ _ _ _ _ _ h => False.elim h,
    fun _ _ _ _ _ h => h⟩

/-- **No event left**: host-free divergence, read natively by `div_whole` at the closed host. -/
theorem div_baseL {Q : CalleeDiv H} (hnat : NatDiv Q) {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {es : List Binaryen.BExpr} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩)
    (h : EvDiv (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ []) :
    LogDivOut Q s f stk es [] := by
  have hd := evDiv_nil h
  rcases div_whole (o := o) hostTyped_closedHostL nativeHostSlice_closedHostL s f stk es labels
      ret out hS hc ht hd with ⟨y, fi, hh, -, -, -, h3⟩ | hev
  · exact h3.elim
  · rw [hostCall_closedHost] at hev
    exact hnat _ _ _ _ hev

theorem stuck_of_vals {P : Silmaril.Wasm.Numerics.Profile} {host' : HostSemantics H}
    {c : Config H} {ws : List Val} (hw : c.code = vals ws) : ∀ c', ¬ Step P host' c c' := by
  intro c' h
  rcases c with ⟨_, _, _⟩
  dsimp only at hw
  subst hw
  exact Sim.Step.not_vals h

/-- A logged backward conclusion at values is a normal logged run. -/
theorem backOutL_vals {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {cs : List (Call (wasmHostSig H))} {c : Config H} {ws : List Val}
    (h : BackOutL host s f stk es cs c) (hw : c.code = vals ws) :
    ∃ stk₁ l, EvalH host s f stk es (c.store, c.frame, .normal stk₁) ∧
      EvalL s f stk es l (c.store, c.frame, .normal stk₁) ∧ Res l cs ∧ ws = stk₁.reverse := by
  rcases h with ⟨⟨s₁, f₁, fl⟩, hev, ⟨oc, he, hst, hfr, hm⟩, hlog⟩ | ⟨m, hat, -⟩
  · dsimp only at hst hfr hm hlog
    subst hst hfr
    rw [hw] at he
    obtain rfl := ends_vals he
    rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
    obtain ⟨l, d, hl⟩ := hlog nofun
    exact ⟨stk₁, l, hev, d, hl, hm⟩
  · exact (atHost_ne_vals hat ws hw).elim

/-- A logged backward conclusion at an end that is not at a host call is a native run. -/
theorem backOutL_end {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {cs : List (Call (wasmHostSig H))} {c : Config H}
    (h : BackOutL host s f stk es cs c) (hdc : decompose? c.store c.code = none) :
    ∃ (fl : Binaryen.Flow) (oc : Outcome), EvalH host s f stk es (c.store, c.frame, fl) ∧
      oc.Ends c.code ∧ Interp.FlowMatch fl oc ∧
      (fl ≠ .trap → ∃ l, EvalL s f stk es l (c.store, c.frame, fl) ∧ Res l cs) := by
  rcases h with ⟨⟨s₁, f₁, fl⟩, hev, ⟨oc, he, hst, hfr, hm⟩, hlog⟩ | ⟨m, hat, -⟩
  · dsimp only at hst hfr hm hlog
    subst hst hfr
    exact ⟨fl, oc, hev, he, hm, hlog⟩
  · have := atHost_isSome hat
    rw [hdc] at this
    cases this

theorem logDivOut_lift {Q : CalleeDiv H} {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List Binaryen.BExpr} {l₀ : List (OCall H)} {q₀ cs : List (Call (wasmHostSig H))}
    (hd : ∀ l, LogDiv s' f' stk' es' l → LogDiv s f stk es (l₀ ++ l))
    (hr : ∀ l y, ReachL s' f' stk' es' l y → ReachL s f stk es (l₀ ++ l) y) (h₀ : Res l₀ q₀)
    (h : LogDivOut Q s' f' stk' es' cs) : LogDivOut Q s f stk es (q₀ ++ cs) := by
  rcases h with ⟨l, hl, hres⟩ | ⟨l, y, q, q', hry, hres, hq, rfl⟩
  · exact .inl ⟨l₀ ++ l, hd l hl, res_append h₀ hres⟩
  · exact .inr ⟨l₀ ++ l, y, q₀ ++ q, q', hr l y hry, res_append h₀ hres, hq, by simp⟩

theorem logDivOut_lift₀ {Q : CalleeDiv H} {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List Binaryen.BExpr} {cs : List (Call (wasmHostSig H))}
    (hd : ∀ l, LogDiv s' f' stk' es' l → LogDiv s f stk es l)
    (hr : ∀ l y, ReachL s' f' stk' es' l y → ReachL s f stk es l y)
    (h : LogDivOut Q s' f' stk' es' cs) : LogDivOut Q s f stk es cs := by
  simpa using logDivOut_lift (l₀ := []) (q₀ := []) (fun l h => by simpa using hd l h)
    (fun l y h => by simpa using hr l y h) .nil h

/-- **An abrupt exit from a label does not diverge**, with or without events. -/
theorem evDiv_label_abrupt {n : Nat} {cs : List (Call (wasmHostSig H))} {s₁ : Store H}
    {f₁ : Frame} {pre : List Val} {code rest : List Admin} {k : Nat} {cont : List Instr}
    {oc : Outcome} {fl fl' : Binaryen.Flow}
    (he : oc.Ends code) (hm : Interp.FlowMatch fl oc)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl))
    (hn : ¬ fl'.IsNormal)
    (ht : Sim.ContextTyped ⟨s₁, f₁, vals pre ++ [.label k cont code] ++ rest⟩)
    (hd : EvDiv (profile o) host n ⟨s₁, f₁, vals pre ++ [.label k cont code] ++ rest⟩ cs) :
    False := by
  have hw := Interp.exit_abrupt (P := profile o) (host := Det.noHost) (s₁ := s₁) (f₁ := f₁)
    (n := k) (cont := cont) (fl' := fl') he hm hfl pre rest
  obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
  exact evDiv_stuck (ends_abrupt_stuck (P := profile o) (host := host) (s := s₁) (f := f₁)
    he'' hm'' hn) (evDiv_through_steps hst' ht hd)

/-- **Leaving a block's label**, with or without events: the body's flow hands values on.
A branch out, a return or a trap ends in a stuck form. -/
theorem evDiv_block_exit {n : Nat} {cs : List (Call (wasmHostSig H))} {s₁ : Store H}
    {f₁ : Frame} {pre : List Val} {code rest : List Admin}
    {nr : Nat} {oc : Outcome} {fl : Binaryen.Flow}
    (he : oc.Ends code) (hm : Interp.FlowMatch fl oc)
    (hnr : ∀ vs, fl.blockVals = some vs → nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr)
    (ht : Sim.ContextTyped ⟨s₁, f₁, vals pre ++ [.label nr [] code] ++ rest⟩)
    (hd : EvDiv (profile o) host n ⟨s₁, f₁, vals pre ++ [.label nr [] code] ++ rest⟩ cs) :
    ∃ vs, fl.blockVals = some vs ∧
      Sim.ContextTyped ⟨s₁, f₁, vals (pre ++ (vs.take nr).reverse) ++ rest⟩ ∧
      EvDiv (profile o) host n ⟨s₁, f₁, vals (pre ++ (vs.take nr).reverse) ++ rest⟩ cs := by
  cases hvs : fl.blockVals with
  | some vs =>
    have hx := Interp.exit_blockVals (P := profile o) (host := Det.noHost) (s₁ := s₁) (f₁ := f₁)
      (pre := pre) (rest := rest) he hm hvs (hnr vs hvs) hnorm
    exact ⟨vs, rfl, ht.steps hx, evDiv_through_steps hx ht hd⟩
  | none =>
    exfalso
    have hfl : (∃ k vs, fl = Binaryen.Flow.brk (k + 1) vs) ∨ fl.Escapes := by
      rcases fl with _ | ⟨_ | k, vs⟩ | _ | _ | _ <;>
        simp_all [Binaryen.Flow.blockVals, Binaryen.Flow.Escapes]
    rcases hfl with ⟨k, vs, rfl⟩ | hesc
    · exact evDiv_label_abrupt he hm (.inl ⟨k, vs, rfl, rfl⟩) id ht hd
    · exact evDiv_label_abrupt he hm (.inr ⟨hesc, rfl⟩) (by
        rcases fl <;> simp_all [Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]) ht hd

/-- Through a unique host-free step: the same measure, smaller when there are events. -/
theorem evDiv_step {n : Nat} {K d : Config H} {cs : List (Call (wasmHostSig H))}
    (huniq : ∀ c₁, Step (profile o) host K c₁ → c₁ = d) (hK : Step (profile o) Det.noHost K d)
    (ht : Sim.ContextTyped K) (h : EvDiv (profile o) host n K cs) :
    ∃ m ≤ n, (cs ≠ [] → m < n) ∧ EvDiv (profile o) host m d cs := by
  by_cases hcs : cs = []
  · exact ⟨n, le_refl _, fun h => (h hcs).elim, evDiv_through_steps (.single hK) ht h⟩
  · obtain ⟨m, hm, h⟩ := evDiv_unique huniq hK hcs h
    exact ⟨m, hm.le, fun _ => hm, h⟩

/-! ## Operator trees -/

/-- **The operator case** other than a call. -/
theorem divL_op_flat (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {Q : CalleeDiv H}
    {n : Nat} {i : Instr} {args es : List Binaryen.BExpr} (hi : ∀ x, i ≠ .call x)
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.op i args :: es) →
      DivGoalL o host Q m es') :
    DivGoalL o host Q n (.op i args :: es) := by
  intro s f stk labels ret out cs hS hc ht hdv
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk i args es
  have hta : Sim.ContextTyped
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  rw [hcode] at hdv
  rcases evDiv_seq_split hdv with hda | ⟨c₁, n₁, m, cs₁, cs₂, ws, rfl, hm, hr₁, hw, hd₁⟩
  · exact logDivOut_lift₀ (fun _ => LogDiv.args) (fun _ _ => ReachL.args)
      (ihle n (le_refl _) args Interp.size_args s f stk labels ret oa cs hS ha hta hda)
  obtain ⟨stk₁, l₁, hev, d₁, hl₁, rfl⟩ := backOutL_vals
    (back_wholeL hT hH n₁ args s f stk labels ret oa c₁ cs₁ hS ha hta hr₁ (stuck_of_vals hw)) hw
  obtain ⟨s₁, f₁, k₁⟩ := c₁
  dsimp only at hev d₁ hd₁
  have htyped : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
      expression (Binaryen.BExpr.lowerList es)⟩ := by
    have hr := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain i :: expression (Binaryen.BExpr.lowerList es)) (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT (hcode ▸ ht) hr
  obtain ⟨hf, inv1⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
  obtain ⟨⟨s₂, f₂, fl⟩, hfl⟩ := Interp.evalFlat_progressH hf hi htyped
  by_cases hn : fl.IsNormal
  · rcases fl with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨ho, inv2⟩ := Interp.flat_normal (ext := Interp.noExt) hfl hf
    have inv12 : Interp.EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have h2' : Interp.chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [← ho]; exact Interp.chk_inv inv12 h2
    have hst := Interp.steps_flat_normal (P := profile o) (host := Det.noHost) hi hf hfl
      (expression (Binaryen.BExpr.lowerList es))
    exact logDivOut_lift (fun _ h => LogDiv.opK hi d₁ hfl h) (fun _ _ h => ReachL.opK hi d₁ hfl h)
      hl₁ (ihle m hm es Interp.size_tail s₂ f₂ stk₂ labels ret out cs₂
        (Interp.storeChk_inv inv12 hS) h2' (htyped.steps hst)
        (evDiv_through_steps hst htyped hd₁))
  · exfalso
    have hw := Interp.wp_flat_abrupt (P := profile o) (host := Det.noHost) hf hfl hn
      (expression (Binaryen.BExpr.lowerList es))
    obtain ⟨c', o', hst, he, hm⟩ := Interp.run_of_wp hw
    exact evDiv_stuck (ends_abrupt_stuck (P := profile o) (host := host) (s := s₂) (f := f₂)
      he hm hn) (evDiv_through_steps hst htyped hd₁)

/-! ## Calls -/

/-- **The call case.** -/
theorem divL_call (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {Q : CalleeDiv H}
    (hnat : NatDiv Q) (hfun : FunDiv Q) {n : Nat} {x : FuncIdx} {args es : List Binaryen.BExpr}
    (ihlt : ∀ m < n, ∀ es', DivGoalL o host Q m es')
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.op (.call x) args :: es) →
      DivGoalL o host Q m es') :
    DivGoalL o host Q n (.op (.call x) args :: es) := by
  intro s f stk labels ret out cs hS hc ht hdv
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk (.call x) args es
  have hta : Sim.ContextTyped
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  rw [hcode] at hdv
  rcases evDiv_seq_split hdv with hda | ⟨c₁, n₁, m, cs₁, cs₂, ws, rfl, hm, hr₁, hw, hd₁⟩
  · exact logDivOut_lift₀ (fun _ => LogDiv.args) (fun _ _ => ReachL.args)
      (ihle n (le_refl _) args Interp.size_args s f stk labels ret oa cs hS ha hta hda)
  obtain ⟨stk₁, l₁, hev, d₁, hl₁, rfl⟩ := backOutL_vals
    (back_wholeL hT hH n₁ args s f stk labels ret oa c₁ cs₁ hS ha hta hr₁ (stuck_of_vals hw)) hw
  obtain ⟨s₁, f₁, k₁⟩ := c₁
  dsimp only at hev d₁ hd₁
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  obtain ⟨a, fi, ps, rs, hfi, hty, inv1, hp, -⟩ := call_info o hH hS hc hev
  have hS₁ := Interp.storeChk_inv inv1 hS
  obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
  -- typing after the arguments, and after `call x`
  have htK₀ : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ := by
    have hr := Silmaril.Wasm.Logic.Core.Steps.append (.plain (.call x) :: rest)
      (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT (hcode ▸ ht) hr
  have hs₁ : Step (profile o) Det.noHost
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := Det.noHost)
      stk₁.reverse rest (Step.call hx hf)
  have htK₁ := htK₀.steps (.single hs₁)
  obtain ⟨m₁, hm₁, hlt₁, hd₂⟩ := evDiv_step (fun c₁ h => call_step_unique hfi h) hs₁ htK₀ hd₁
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := Interp.expand_of_funcType hty
  cases hcd : fi.code with
  | host hh =>
    rw [code_call_split stk₁ ps.length] at hd₂
    have hn : (stk₁.take ps.length).reverse.length = ps'.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨s', r, cs', rfl, hhost, hd₃⟩ := evDiv_host_call hf hcd hex hn hd₂
    have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (s', resFlow r) := by
      rw [hostCall_fixpoint]
      exact .inr ⟨fi, hh, r, hf, hcd, hhost, rfl⟩
    rcases r with ws | t | _
    · have hvs : (resFlow (.values ws)).retVals = some ws.reverse := rfl
      obtain ⟨labels', ret', out', hS₂, hc₂, ht₂⟩ := after_call o hT hH hS hc ht hev hfi hty hcall hvs
      have hd₄ : EvDiv (profile o) host m₁ ⟨s', f₁, vals (ws.reverse.take rs.length ++
          stk₁.drop ps.length).reverse ++ rest⟩ cs' := by
        have hl := hH.arity s₁ a fi hh ps rs _ ws s' (Interp.funcs_of_func? hfi) hcd hty hhost
        have htake : ws.reverse.take rs.length = ws.reverse :=
          List.take_of_length_le (by simp [hl])
        rw [htake]
        simpa [Result.toAdmin, List.reverse_append, List.append_assoc] using hd₃
      have hz := res_single (close_host hf hcd hty (exitFlow_of_retVals hvs) :
        ([⟨(hh, s₁, (stk₁.take ps.length).reverse), (s', Result.values ws)⟩],
          End.ret (Sum.inl ((ws.reverse.take rs.length).reverse)) s') ∈ _)
      have := logDivOut_lift (Q := Q)
        (l₀ := l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁
          (.inl (ws.reverse.take rs.length).reverse) s'])
        (fun l h => by
          have := LogDiv.callK (ws := (ws.reverse.take rs.length).reverse) (s₂ := s')
            d₁ hfi hty (by rw [List.reverse_reverse]; exact h)
          simpa [List.append_assoc] using this)
        (fun l y h => by
          have := ReachL.callK (ws := (ws.reverse.take rs.length).reverse) (s₂ := s')
            d₁ hfi hty (by rw [List.reverse_reverse]; exact h)
          simpa [List.append_assoc] using this)
        (res_append hl₁ hz)
        (ihle m₁ (hm₁.trans hm) es Interp.size_tail s' f₁ _ labels' ret' out' cs' hS₂ hc₂ ht₂ hd₄)
      simpa [List.append_assoc] using this
    · exact (hH.noThrow hh s₁ _ s' t hhost).elim
    · exact (evDiv_trap (by simpa [Result.toAdmin] using hd₃)).elim
  | wasm fn =>
    have hp' : ps'.length ≤ stk₁.length := by omega
    have hs₂ : Step (profile o) Det.noHost
        ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩
        ⟨s₁, f₁, vals (stk₁.drop ps'.length).reverse ++
          [.frame rs'.length (Frame.forCall fi.module (stk₁.take ps'.length).reverse fn.locals)
            [.label rs'.length [] (expression fn.body)]] ++ rest⟩ := by
      rw [code_call_split stk₁ ps'.length]
      have hn : (stk₁.take ps'.length).reverse.length = ps'.length := by
        simp only [List.length_reverse, List.length_take]; omega
      simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := Det.noHost)
        (stk₁.drop ps'.length).reverse rest
        (Step.callRefFunc (c := .callRefType fi.type) trivial hf hex hn hcd)
    have htK₂ := htK₁.steps (.single hs₂)
    obtain ⟨m₂, hm₂, hlt₂, hd₃⟩ :=
      evDiv_step (fun c₁ h => callRef_wasm_step_unique hf hcd hex hp' h) hs₂ htK₁ hd₂
    rw [hpl, hrl] at hd₃ htK₂
    obtain ⟨ob, hob, hcb⟩ := Interp.callee_chk (ext := Interp.noExt) hS₁ hfi hcd hty hp
    have htc : Sim.ContextTyped ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
        vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have h₁ := Sim.ContextTyped.frame htK₂
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    have hfa := Interp.funcs_of_func? hfi
    rcases evDiv_frame_seq_split hd₃ with hdb |
        ⟨⟨rcs, rcf, rcc⟩, N₁, mm, cs₂₁, cs₂₂, rfl, hmm, hb, hsb, hdc, hd₄⟩
    · -- the callee body diverges: a descent
      have hdb' : EvDiv (profile o) host m₂ ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
          vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cs₂ := by
        simpa [Binaryen.lowerList_liftInstrs, vals] using hdb
      have hbody : LogDivOut Q s₁ (Interp.calleeFrame fi fn stk₁ ps.length) []
          (Binaryen.liftInstrs fn.body) cs₂ := by
        by_cases hcs : cs₂ = []
        · subst hcs
          exact div_baseL hnat hS₁ hcb htc hdb'
        · exact ihlt m₂ (by have := hlt₁ hcs; have := hlt₂ hcs; omega) _ s₁ _ [] [rs.length]
            rs.length ob cs₂ hS₁ hcb htc hdb'
      exact .inr ⟨l₁, ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩, cs₁, cs₂, .here d₁ hfi hty, hl₁,
        hfun ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ fi fn ps rs cs₂ hfa hcd hty hbody, rfl⟩
    · -- the callee body ends
      dsimp only at hsb hdc hd₄
      have hb' : EvRunN (profile o) host N₁
          ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length, vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cs₂₁
          ⟨rcs, rcf, rcc⟩ := by
        simpa [Binaryen.lowerList_liftInstrs, vals] using hb
      obtain ⟨fl, oc, hevb, he, hm', hlog⟩ :=
        backOutL_end (back_wholeL hT hH N₁ _ s₁ _ [] [rs.length] rs.length ob _ cs₂₁ hS₁ hcb htc
          hb' hsb) hdc
      dsimp only at hevb he hlog
      have htyF := typed_frame_steps hT htK₂ (evRunN_steps hb)
      dsimp only at htyF
      have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (rcs, fl) := by
        rw [hostCall_fixpoint]
        exact .inl ⟨fi, fn, ps, rs, rcf, hf, hcd, hty, hevb⟩
      obtain ⟨hok, -⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hcb
      cases hvs : fl.retVals with
      | some vs =>
        have hrs := Interp.retVals_length hok hob hvs
        have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
          intro ws hws; rw [hws] at hok; exact Interp.length_of_ends hok hob
        obtain ⟨s', res, hret', hK⟩ := Silmaril.Wasm.Logic.Core.frame_ends
          (P := profile o) (host := Det.noHost) (f := f₁) he
          (Interp.funcPost_of_match (s₂ := rcs) (F := rcf) hm' hvs hrs hnorm)
        obtain ⟨rfl, rfl⟩ := hK
        have hx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o)
          (host := Det.noHost) (stk₁.drop ps.length).reverse rest hret'
        have hd₅ := evDiv_through_steps hx htyF hd₄
        obtain ⟨labels', ret', out', hS₂, hc₂, ht₂⟩ :=
          after_call o hT hH hS hc ht hev hfi hty hcall hvs
        have hd₆ : EvDiv (profile o) host mm ⟨s', f₁, vals (vs.take rs.length ++
            stk₁.drop ps.length).reverse ++ rest⟩ cs₂₂ := by
          simpa [Interp.stack_after] using hd₅
        have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.retVals] at hvs
        obtain ⟨lb, db, hlb⟩ := hlog hnt
        have hz := res_single (close_wasm hfa hcd hty db hlb (exitFlow_of_retVals hvs))
        have := logDivOut_lift (Q := Q)
          (l₀ := l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁
            (.inl (vs.take rs.length).reverse) s'])
          (fun l h => by
            have := LogDiv.callK (ws := (vs.take rs.length).reverse) (s₂ := s')
              d₁ hfi hty (by rw [List.reverse_reverse]; exact h)
            simpa [List.append_assoc] using this)
          (fun l y h => by
            have := ReachL.callK (ws := (vs.take rs.length).reverse) (s₂ := s')
              d₁ hfi hty (by rw [List.reverse_reverse]; exact h)
            simpa [List.append_assoc] using this)
          (res_append hl₁ hz)
          (ihle mm (by omega) es Interp.size_tail s' f₁ _ labels' ret' out' cs₂₂ hS₂ hc₂ ht₂ hd₆)
        simpa [List.append_assoc] using this
      | none =>
        exfalso
        have hfl : fl = .trap := by
          rcases hfl : fl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok hvs <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOkE]
        subst hfl
        have hc' : rcc = [.trap] := by
          rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm'
          exact he
        subst hc'
        have hout : Steps (profile o) Det.noHost
            ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++
              [.frame rs.length rcf [.label rs.length [] [.trap]]] ++ rest⟩
            ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++ [.trap] ++ rest⟩ :=
          Silmaril.Wasm.Logic.Core.Steps.ctx _ rest
            ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
        exact evDiv_trap (by simpa using evDiv_through_steps hout htyF hd₄)

/-! ## Structured trees -/

/-- **The block case.** -/
theorem divL_block (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {Q : CalleeDiv H}
    {n : Nat} {bt : BlockType} {body es : List Binaryen.BExpr}
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.block bt body :: es) →
      DivGoalL o host Q m es') :
    DivGoalL o host Q n (.block bt body :: es) := by
  intro s f stk labels ret out cs hS hc ht hdv
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_block (body := body) stk bt es
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_block har) rest
  have ht₀ : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList body)) :: rest⟩ := hcode ▸ ht
  have htK := ht₀.steps henter
  have hdK := evDiv_through_steps henter ht₀ (hcode ▸ hdv)
  have htb : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ := Sim.ContextTyped.label htK
  rcases evDiv_label_seq_split hdK with hdb |
      ⟨⟨rcs, rcf, rcc⟩, N₁, mm, cs₁, cs₂, rfl, hmm, hbr, hsb, hdc, hd₁⟩
  · exact logDivOut_lift₀ (fun _ => LogDiv.block har) (fun _ _ => ReachL.block har)
      (ihle n (le_refl _) body Interp.size_block s f (stk.take np) (nr :: labels) ret ob cs hS
        hb' htb hdb)
  dsimp only at hsb hdc hd₁
  obtain ⟨fl, oc, hev, he, hm, hlog⟩ :=
    backOutL_end (back_wholeL hT hH N₁ body s f (stk.take np) (nr :: labels) ret ob _ cs₁ hS hb'
      htb hbr hsb) hdc
  dsimp only at hev he hlog
  obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl; exact Interp.length_of_ends hok hob
  have htL := typed_label_steps hT htK (evRunN_steps hbr)
  obtain ⟨vs, hvs, ht₂, hd₂⟩ :=
    evDiv_block_exit he hm (fun vs hvs => Interp.blockVals_length hok hob hvs) hnorm htL hd₁
  have hnr' := Interp.blockVals_length hok hob hvs
  have h2' := Interp.chk_after (ext := Interp.noExt) inv1 hp hnr' h2
  have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.blockVals] at hvs
  obtain ⟨l₁, d₁, hl₁⟩ := hlog hnt
  rw [← Interp.stack_after] at ht₂ hd₂
  exact logDivOut_lift (fun _ h => LogDiv.blockK har d₁ hvs h)
    (fun _ _ h => ReachL.blockK har d₁ hvs h) hl₁
    (ihle mm hmm es Interp.size_tail rcs rcf _ labels ret out cs₂ (Interp.storeChk_inv inv1 hS)
      h2' ht₂ hd₂)

/-- **The loop case.** -/
theorem divL_loop (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {Q : CalleeDiv H}
    (hnat : NatDiv Q) {n : Nat} {bt : BlockType} {body es : List Binaryen.BExpr}
    (ihlt : ∀ m < n, ∀ es', DivGoalL o host Q m es')
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.loop bt body :: es) →
      DivGoalL o host Q m es') :
    DivGoalL o host Q n (.loop bt body :: es) := by
  intro s f stk labels ret out cs hS hc ht hdv
  by_cases hcs : cs = []
  · subst hcs
    exact div_baseL hnat hS hc ht hdv
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_loop (body := body) stk bt es
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  have hstep := Interp.step_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har) rest
  have ht₀ : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: rest⟩ := hcode ▸ ht
  have htK := ht₀.steps (.single hstep)
  obtain ⟨m₀, -, hlt₀, hdK⟩ :=
    evDiv_step (fun c₁ h => loop_step_unique har hp h) hstep ht₀ (hcode ▸ hdv)
  have hm₀ := hlt₀ hcs
  have htb : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ := Sim.ContextTyped.label htK
  rcases evDiv_label_seq_split hdK with hdb |
      ⟨⟨rcs, rcf, rcc⟩, N₁, mm, cs₁, cs₂, rfl, hmm, hbr, hsb, hdc, hd₁⟩
  · exact logDivOut_lift₀ (fun _ => LogDiv.loop har) (fun _ _ => ReachL.loop har)
      (ihle m₀ hm₀.le body Interp.size_loop s f (stk.take np) (np :: labels) ret ob cs hS hb'
        htb hdb)
  dsimp only at hsb hdc hd₁
  obtain ⟨fl, oc, hev, he, hm, hlog⟩ :=
    backOutL_end (back_wholeL hT hH N₁ body s f (stk.take np) (np :: labels) ret ob _ cs₁ hS hb'
      htb hbr hsb) hdc
  dsimp only at hev he hlog
  obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
  have htL := typed_label_steps hT htK (evRunN_steps hbr)
  dsimp only at htL
  rcases fl with ws | ⟨_ | k, vs⟩ | ws | _ | t
  · -- falls through
    have hlen : ws.length = nr := Interp.length_of_ends hok hob
    have h2' := Interp.chk_after (ext := Interp.noExt) (vs := ws) inv1 hp hlen.ge h2
    have hx := Interp.exit_normal (P := profile o) (host := Det.noHost) (s₁ := rcs) (f₁ := rcf)
      (n := np) (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm (stk.drop np).reverse
      rest
    have htake : ws.take nr = ws := List.take_of_length_le hlen.le
    obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
    have ht₂ : Sim.ContextTyped ⟨rcs, rcf, vals (ws.take nr ++ stk.drop np).reverse ++ rest⟩ := by
      rw [htake]
      simpa [List.reverse_append] using htL.steps hx
    have hd₂ : EvDiv (profile o) host mm
        ⟨rcs, rcf, vals (ws.take nr ++ stk.drop np).reverse ++ rest⟩ cs₂ := by
      rw [htake]
      simpa [List.reverse_append] using evDiv_through_steps hx htL hd₁
    exact logDivOut_lift (fun _ h => LogDiv.loopK har d₁ h) (fun _ _ h => ReachL.loopK har d₁ h)
      hl₁ (ihle mm (by omega) es Interp.size_tail rcs rcf _ labels ret out cs₂
        (Interp.storeChk_inv inv1 hS) h2' ht₂ hd₂)
  · -- branches back to the loop
    have hnp : np ≤ vs.length := by
      obtain ⟨k, hk, hkl⟩ := hok
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      omega
    have hx := Interp.exit_br0 (P := profile o) (host := Det.noHost) (s₁ := rcs) (f₁ := rcf)
      (n := np) (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm hnp
      (stk.drop np).reverse rest
    have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have hc' : Interp.chk rcs.funcs rcf.module rcf.locals.length ret labels
        (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
      rw [hlen]; exact Interp.chk_inv inv1 hc
    obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
    have ht₂ : Sim.ContextTyped ⟨rcs, rcf, vals (vs.take np ++ stk.drop np).reverse ++
        expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ := by
      rw [Interp.code_loop]
      simpa [List.reverse_append, List.append_assoc, expression, hrest] using htL.steps hx
    have hd₂ : EvDiv (profile o) host mm ⟨rcs, rcf, vals (vs.take np ++ stk.drop np).reverse ++
        expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ cs₂ := by
      rw [Interp.code_loop]
      simpa [List.reverse_append, List.append_assoc, expression, hrest] using
        evDiv_through_steps hx htL hd₁
    exact logDivOut_lift (fun _ h => LogDiv.loopBack har d₁ h)
      (fun _ _ h => ReachL.loopBack har d₁ h) hl₁
      (ihlt mm (by omega) _ rcs rcf _ labels ret out cs₂ (Interp.storeChk_inv inv1 hS) hc' ht₂ hd₂)
  · exact (evDiv_label_abrupt he hm (.inl ⟨k, vs, rfl, rfl⟩) id htL hd₁).elim
  · exact (evDiv_label_abrupt he hm (.inr ⟨by simp [Binaryen.Flow.Escapes], rfl⟩)
      (by simp [Binaryen.Flow.IsNormal]) htL hd₁).elim
  · exact (evDiv_label_abrupt he hm (.inr ⟨by simp [Binaryen.Flow.Escapes], rfl⟩)
      (by simp [Binaryen.Flow.IsNormal]) htL hd₁).elim
  · exact (evDiv_label_abrupt he hm (.inr ⟨by simp [Binaryen.Flow.Escapes], rfl⟩)
      (by simp [Binaryen.Flow.IsNormal]) htL hd₁).elim

/-- **The `if` case.** -/
theorem divL_if (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {Q : CalleeDiv H}
    {n : Nat} {bt : BlockType} {cnd t el es : List Binaryen.BExpr}
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.if_ bt cnd t el :: es) →
      DivGoalL o host Q m es') :
    DivGoalL o host Q n (.if_ bt cnd t el :: es) := by
  intro s f stk labels ret out cs hS hc ht hdv
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := Interp.chk1_ifE h1
  have hcode := Interp.code_if stk bt cnd t el es
  have htc : Sim.ContextTyped
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList cnd)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  rw [hcode] at hdv
  rcases evDiv_seq_split hdv with hdc | ⟨c₁, n₁, m, cs₁, cs₂, ws, rfl, hm, hr₁, hw, hd₁⟩
  · exact logDivOut_lift₀ (fun _ => LogDiv.cond) (fun _ _ => ReachL.cond)
      (ihle n (le_refl _) cnd Interp.size_cond s f stk labels ret oc cs hS hco htc hdc)
  obtain ⟨stk', l₁, hev, d₁, hl₁, rfl⟩ := backOutL_vals
    (back_wholeL hT hH n₁ cnd s f stk labels ret oc c₁ cs₁ hS hco htc hr₁ (stuck_of_vals hw)) hw
  obtain ⟨s₁, f₁, k₁⟩ := c₁
  dsimp only at hev d₁ hd₁
  have hafter : Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
        (Binaryen.BExpr.lowerList (.if_ bt cnd t el :: es))⟩
      ⟨s₁, f₁, vals stk'.reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩ := by
    rw [hcode]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ (run_of_evalH (o := o) hH hev hS hco)
  have ht₁ := ContextTyped.steps_typed hT ht hafter
  obtain ⟨hoc, inv0⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hco
  obtain ⟨np, nr, ha, -⟩ := hk1 _ hoc
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [Interp.arity_eq, inv0.2.1]; exact ha
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := Interp.truthy_progressH ht₁
  obtain ⟨inv1, hp, hendArm, h2'⟩ :=
    Interp.arity_if_pre (b := b) hS (Interp.evalH_good (P := profile o) hH hev).1 har hc
  obtain ⟨ob, hb', hob⟩ := Interp.endsAt_eq (Interp.chk_inv_endsAt inv1 hendArm)
  have hb'' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
      (some (stk₁.take np).length) (if b then t else el) = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb'
  have hS₁ := Interp.storeChk_inv inv1 hS
  have hif := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
    (el := el) (rest := rest) hb
  have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s₁) (f := f₁)
    (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (Interp.step_block har) rest
  have hpre := (Relation.ReflTransGen.single hif).trans henter
  have htK := ht₁.steps hpre
  have hdK := evDiv_through_steps hpre ht₁ hd₁
  have htarm : Sim.ContextTyped ⟨s₁, f₁, vals (stk₁.take np).reverse ++
      expression (Binaryen.BExpr.lowerList (if b then t else el))⟩ := Sim.ContextTyped.label htK
  rcases evDiv_label_seq_split hdK with hda |
      ⟨⟨rcs, rcf, rcc⟩, N₁, mm, cs₂₁, cs₂₂, rfl, hmm, hbr, hsb, hdc, hd₂⟩
  · exact logDivOut_lift (fun _ h => LogDiv.arm d₁ hb har h)
      (fun _ _ h => ReachL.arm d₁ hb har h) hl₁
      (ihle m hm _ (Interp.size_arm b) s₁ f₁ (stk₁.take np) (nr :: labels) ret ob cs₂ hS₁ hb''
        htarm hda)
  dsimp only at hsb hdc hd₂
  obtain ⟨fl, oc', hevb, he, hm', hlog⟩ :=
    backOutL_end (back_wholeL hT hH N₁ _ s₁ f₁ (stk₁.take np) (nr :: labels) ret ob _ cs₂₁ hS₁
      hb'' htarm hbr hsb) hdc
  dsimp only at hevb he hlog
  obtain ⟨hok, inv2⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hb''
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl; exact Interp.length_of_ends hok hob
  have htL := typed_label_steps hT htK (evRunN_steps hbr)
  obtain ⟨vs, hvs, ht₂, hd₃⟩ :=
    evDiv_block_exit he hm' (fun vs hvs => Interp.blockVals_length hok hob hvs) hnorm htL hd₂
  have hnr' := Interp.blockVals_length hok hob hvs
  have h2₂ := Interp.chk_after (ext := Interp.noExt) inv2 hp hnr' (Interp.chk_inv inv1 h2')
  have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.blockVals] at hvs
  obtain ⟨l₂, d₂, hl₂⟩ := hlog hnt
  rw [← Interp.stack_after] at ht₂ hd₃
  have := logDivOut_lift (fun _ h => LogDiv.ifK d₁ hb har d₂ hvs h)
    (fun _ _ h => ReachL.ifK d₁ hb har d₂ hvs h) (res_append hl₁ hl₂)
    (ihle mm (by omega) es Interp.size_tail rcs rcf _ labels ret out cs₂₂
      (Interp.storeChk_inv (inv1.trans inv2) hS) h2₂ ht₂ hd₃)
  simpa [List.append_assoc] using this

/-! ## The whole run -/

/-- **Divergence after a logged prefix**, deterministic profile `profile o`: well-founded
induction on the measure of `EvDiv`, then the tree size. -/
theorem div_wholeL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {Q : CalleeDiv H}
    (hnat : NatDiv Q) (hfun : FunDiv Q) : ∀ n es, DivGoalL o host Q n es := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro es
  induction hsz : sizeOf es using Nat.strong_induction_on generalizing es with
  | _ k ihk =>
  have ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf es → DivGoalL o host Q m es' := by
    intro m hm es' hes'
    rcases Nat.lt_or_eq_of_le hm with hlt | rfl
    · exact ihn m hlt es'
    · exact ihk _ (hsz ▸ hes') es' rfl
  rcases es with _ | ⟨e, es⟩
  · intro s f stk labels ret out cs _ _ _ hdv
    exact (evDiv_stuck (stuck_of_vals (ws := stk.reverse) (by simp [expression])) hdv).elim
  · rcases e with ⟨i, args⟩ | ⟨bt, body⟩ | ⟨bt, body⟩ | ⟨bt, cnd, t, el⟩ | ⟨bt, cs, body⟩
    · by_cases hcall : ∃ x, i = .call x
      · obtain ⟨x, rfl⟩ := hcall
        exact divL_call hT hH hnat hfun ihn ihle
      · exact divL_op_flat hT hH (fun x hx => hcall ⟨x, hx⟩) ihle
    · exact divL_block hT hH ihle
    · exact divL_loop hT hH hnat ihn ihle
    · exact divL_if hT hH ihle
    · intro s f stk labels ret out cs _ hc
      obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
      simp [Interp.chk1E, Interp.noExt] at h1

/-! ## Invocations -/

/-- **Divergence of an invocation after a logged prefix** (deterministic profile): a Core run
of a typed invocation with the events `cs`, then host-free divergence, is `Q` of the
invocation after exactly `cs`. -/
theorem invoke_divL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {Q : CalleeDiv H}
    (hnat : NatDiv Q) (hfun : FunDiv Q) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (h : EvDiv (profile o) host n (invoke s a vs) cs) :
    Q ⟨a, (vs, s)⟩ cs := by
  obtain ⟨-, -, rts, -, -, hcok⟩ := invoke_ok hs hok
  obtain ⟨fi, ps', rs', hfi, he, hvt⟩ := hok
  have hty := Interp.funcType_of_expand he
  have hlen : vs.length = ps'.toList.length :=
    Interp.args_length ⟨fi, ps', rs', hfi, he, hvt⟩ hfi hty
  have hinv : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  have htI : Sim.ContextTyped ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ :=
    hinv ▸ Sim.ContextTyped.of_configOk hcok
  rw [hinv] at h
  cases hcd : fi.code with
  | host hh =>
    have h' : EvDiv (profile o) host n
        ⟨s, {}, vals [] ++ vals vs ++ .ref (.func a) :: .callRefType fi.type :: []⟩ cs := by
      simpa using h
    have hn : vs.length = ps'.length := by simpa [Validation.Ty.length] using hlen
    obtain ⟨s', r, cs', rfl, hhost, hd⟩ := evDiv_host_call hfi hcd he hn h'
    exfalso
    rcases r with ws | t | _
    · exact evDiv_stuck (stuck_of_vals (c := ⟨s', {}, vals ws⟩) rfl)
        (by simpa [Result.toAdmin] using hd)
    · exact hH.noThrow hh s vs s' t hhost
    · exact evDiv_trap (ws := []) (r := []) (by simpa [Result.toAdmin] using hd)
  | wasm fn =>
    have hn : vs.length = ps'.length := by simpa [Validation.Ty.length] using hlen
    set F := Frame.forCall fi.module vs fn.locals with hF
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq (hS a fi fn _ _ hfi hcd hty)
    have hbc : Interp.chk s.funcs F.module F.locals.length rs'.toList.length [rs'.toList.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
      rw [hF, Interp.forCall_length _ _ hlen]; exact hb
    have enter : Steps (profile o) Det.noHost
        ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s, {}, [.frame rs'.length F [.label rs'.length [] (expression fn.body)]]⟩ :=
      .single (Step.callRefFunc trivial hfi he hn hcd)
    have htF : Sim.ContextTyped
        ⟨s, {}, vals [] ++ [.frame rs'.length F [.label rs'.length [] (expression fn.body)]] ++
          []⟩ := by
      simpa [vals] using htI.steps enter
    have hct : Sim.ContextTyped ⟨s, F, vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have h₁ := Sim.ContextTyped.frame htF
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    have hd₁ : EvDiv (profile o) host n
        ⟨s, {}, vals [] ++ [.frame rs'.length F [.label rs'.length [] (expression fn.body)]] ++
          []⟩ cs := by
      simpa [vals] using evDiv_through_steps enter htI h
    have hty' : Validation.DefType.funcType? fi.type = some (ps'.toList, rs'.toList) := hty
    rcases evDiv_frame_seq_split hd₁ with hdb |
        ⟨⟨rcs, rcf, rcc⟩, N₁, mm, cs₁, cs₂, rfl, hmm, hbr, hsb, hdc, hd₂⟩
    · refine hfun ⟨a, (vs, s)⟩ fi fn _ _ cs hfi hcd hty' ?_
      exact div_wholeL hT hH hnat hfun n _ s F [] [rs'.toList.length] rs'.toList.length ob cs hS
        hbc hct (by simpa [Binaryen.lowerList_liftInstrs, vals] using hdb)
    · exfalso
      dsimp only at hsb hdc hd₂
      have hbr' : EvRunN (profile o) host N₁ ⟨s, F, vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cs₁
          ⟨rcs, rcf, rcc⟩ := by
        simpa [Binaryen.lowerList_liftInstrs, vals] using hbr
      obtain ⟨fl, oc, hevb, hen, hm, -⟩ :=
        backOutL_end (back_wholeL hT hH N₁ _ s F [] [rs'.toList.length] rs'.toList.length ob _ cs₁
          hS hbc hct hbr' hsb) hdc
      dsimp only at hevb hen
      have htyF := typed_frame_steps hT htF (evRunN_steps hbr)
      dsimp only at htyF
      obtain ⟨hok', -⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS hbc
      cases hvs : fl.retVals with
      | some ws =>
        have hrs := Interp.retVals_length hok' hob hvs
        have hnorm : ∀ ws, fl = .normal ws → ws.length = rs'.toList.length := by
          intro ws hws; rw [hws] at hok'; exact Interp.length_of_ends hok' hob
        obtain ⟨s', res, hret', -⟩ := Silmaril.Wasm.Logic.Core.frame_ends
          (P := profile o) (host := Det.noHost) (f := {}) hen
          (Interp.funcPost_of_match (s₂ := rcs) (F := rcf) hm hvs hrs hnorm)
        have hx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o)
          (host := Det.noHost) [] [] hret'
        have hx' : Steps (profile o) Det.noHost
            ⟨rcs, {}, vals [] ++ [.frame rs'.length rcf [.label rs'.length [] rcc]] ++ []⟩
            ⟨s', {}, vals res⟩ := by
          simpa [vals, Validation.Ty.length] using hx
        exact evDiv_stuck (stuck_of_vals (c := ⟨s', {}, vals res⟩) rfl)
          (evDiv_through_steps hx' htyF hd₂)
      | none =>
        have hfl : fl = .trap := by
          rcases hfl : fl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok' hvs <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOkE]
        subst hfl
        have hc' : rcc = [.trap] := by
          rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
          exact hen
        subst hc'
        have hout : Steps (profile o) Det.noHost
            ⟨rcs, {}, vals [] ++ [.frame rs'.length rcf [.label rs'.length [] [.trap]]] ++ []⟩
            ⟨rcs, {}, vals [] ++ [.trap] ++ []⟩ :=
          Silmaril.Wasm.Logic.Core.Steps.ctx _ []
            ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
        exact evDiv_trap (ws := []) (r := []) (by simpa using evDiv_through_steps hout htyF hd₂)

/-- **Divergence of an invocation after a logged prefix** (deterministic profile): a finite
Core run of a typed invocation with its exact host-event log `cs`, quiescent from there by
host-free divergence, is `Q` of the invocation after exactly `cs`. -/
theorem evRun_divL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {Q : CalleeDiv H}
    (hnat : NatDiv Q) (hfun : FunDiv Q) {s : Store H} {a : Nat} {vs : List Val} {c' : Config H}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hrun : EvRun (profile o) host (invoke s a vs) cs c')
    (hd : Diverges (profile o) (fun _ _ _ _ => False) c') : Q ⟨a, (vs, s)⟩ cs := by
  obtain ⟨n, hn⟩ := evDiv_of_evRun hrun hd
  exact invoke_divL hT hH hnat hfun hs hS hok hn

end Silmaril.Proofs.Wasm.Abstract.HostEval
