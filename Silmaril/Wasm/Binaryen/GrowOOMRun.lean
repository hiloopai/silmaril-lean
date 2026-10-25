module

public import Silmaril.Wasm.Binaryen.GrowOOM
public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim
public import Silmaril.Wasm.Binaryen.CoalesceLocalsCompletion

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOM

open Execution.Core Execution.Core.Sim Numerics Validation MemoryGrowFailure
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open GrowWrapper (Forced)

variable {H : Type} {P : Profile}

/-- Strip a forced finite prefix from a completed run. Intermediate prefix
states cannot already be terminal because they have an actual next step. -/
theorem forced_terminal_tail {c d e : Config H} (h : Forced (P := P) c d)
    (run : Steps P closedHost c e) (terminal : e.Terminal) :
    Steps P closedHost d e := by
  induction h with
  | done => exact run
  | step hs unique _ ih =>
    rcases run.cases_head with he | ⟨x, hx, hxe⟩
    · subst e
      exact (BehaviourRefinement.not_step_of_terminal terminal hs).elim
    · obtain rfl := unique x hx
      exact ih hxe

/-- Divergence likewise passes through the same forced prefix. -/
theorem forced_diverges_tail {c d : Config H} (h : Forced (P := P) c d)
    (diverges : Diverges P closedHost c) : Diverges P closedHost d := by
  induction h with
  | done => exact diverges
  | step _ unique _ ih =>
    obtain ⟨x, hx, tail⟩ := InfiniteTrace.unfold diverges
    obtain rfl := unique x hx
    exact ih tail

/-- A label around an ordinary, nonterminal body can only step its body. -/
theorem label_context_inv {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {body : List Admin} {c : Config H}
    (hn : body.all Admin.isVal = false) (he : ¬ ExitShape body)
    (h : Step P closedHost ⟨s, f, [.label n cont body]⟩ c) :
    ∃ s' f' body', Step P closedHost ⟨s, f, body⟩ ⟨s', f', body'⟩ ∧
      c = ⟨s', f', [.label n cont body']⟩ := by
  cases c with | mk s' f' code =>
    obtain ⟨is', hr, hc⟩ := Closure.Step.label_inv (us := []) (by simpa using h)
    cases hr with
    | ctxt hs => exact ⟨_, _, _, hs, by simpa using hc⟩
    | values vs => simp at hn
    | @brZero vs' vs l rest hl hv =>
      exact (he ⟨vs' ++ vs, [.plain (.br l)], rest, .br l, by simp⟩).elim
    | @brSucc vs l rest hl => exact (he ⟨vs, _, rest, .br l, rfl⟩).elim
    | @returnCallRef vs a rest hreturn =>
      exact (he ⟨vs, [a], rest, .returnCallRef hreturn, rfl⟩).elim
    | @return_ vs rest => exact (he ⟨vs, _, rest, .return_, rfl⟩).elim
    | throwRef a => exact (he ⟨[], _, [], .throw a, by simp⟩).elim
    | trap => exact (he ⟨[], _, [], .trap, by simp⟩).elim

/-- Preserve unique ordinary reductions under the wrapper's label and frame. -/
theorem nested_step_unique {s : Store H} {f fi : Frame} {body : List Admin}
    {s' : Store H} {fi' : Frame} {body' : List Admin}
    (hn : body.all Admin.isVal = false) (he : ¬ ExitShape body)
    (unique : ∀ c, Step P closedHost ⟨s, fi, body⟩ c → c = ⟨s', fi', body'⟩)
    {c : Config H}
    (h : Step P closedHost ⟨s, f, [.frame 1 fi [.label 1 [] body]]⟩ c) :
    c = ⟨s', f, [.frame 1 fi' [.label 1 [] body']]⟩ := by
  obtain ⟨t, gi, code, hlabel, hc⟩ :=
    GrowWrapper.frame_single_inv h rfl (by simp) (by simp)
  obtain ⟨t', gi', body'', hbody, hl⟩ := label_context_inv hn he hlabel
  have hb := unique _ hbody
  simp only [Config.mk.injEq] at hb hl
  obtain ⟨rfl, rfl, rfl⟩ := hb
  obtain ⟨rfl, rfl, rfl⟩ := hl
  exact hc

/-- A head which is neither a value nor a control exit excludes exit shape. -/
theorem not_exit_shape {vs : List Val} {e : Admin} {rest : List Admin}
    (hv : e.val? = none) (hb : ∀ l, e ≠ .plain (.br l))
    (hr : e ≠ .plain .return_) (hc : ¬ e.IsReturnCallRef)
    (ht : e ≠ .trap) (hx : e ≠ .plain .throwRef) :
    ¬ ExitShape (vals vs ++ e :: rest) := by
  rintro ⟨ws, k, tail, hk, he⟩
  exact GuardSim.not_exit hv hb hr hc ht hx hk he

/-- Integer tests have one successor at any numerical profile. -/
theorem head_intTest {s : Store H} {f : Frame} {args : List Val} {t : IntType}
    {op : IntTestOp} {c : Config H}
    (h : Head P s f args (.plain (.intTestOp t op)) c) :
    ∃ x : BitVec t.width, args = [.num ⟨.int t, x⟩] ∧
      c = ⟨s, f, [constI32 (intTestOp t op x)]⟩ := by
  have hv := h.fam_inv (by simp [famOf])
  simp only [famOf, FamRel] at hv
  obtain ⟨is', hv, rfl⟩ := hv
  generalize he : vals args ++ [Admin.plain (.intTestOp t op)] = code at hv
  cases hv with
  | @intTestOp t' op' x =>
    obtain ⟨ha, hi⟩ := (append_singleton_inj
      (l₂ := [Admin.plain (.intConst t' x)])).mp he
    simp only [Admin.plain.injEq, Instr.intTestOp.injEq] at hi
    obtain ⟨rfl, _⟩ := hi
    cases op
    cases op'
    have hv : args = [Val.num ⟨.int t, x⟩] := vals_inj.mp ha
    exact ⟨x, hv, rfl⟩
  | _ =>
    have hh := congrArg List.getLast? he
    simp at hh

theorem intTest_step_unique {s : Store H} {f : Frame} {t : IntType}
    {op : IntTestOp} {x : BitVec t.width} {rest : List Admin} {c : Config H}
    (h : Step P closedHost ⟨s, f, [.plain (.intConst t x), .plain (.intTestOp t op)] ++ rest⟩ c) :
    c = ⟨s, f, constI32 (intTestOp t op x) :: rest⟩ := by
  have h' : Step P closedHost
      ⟨s, f, vals [Val.num ⟨.int t, x⟩] ++ .plain (.intTestOp t op) :: rest⟩ c := h
  obtain ⟨pre, args, cfg, hw, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h'
  obtain ⟨y, rfl, rfl⟩ := head_intTest hh
  obtain ⟨rfl, hv⟩ := (append_singleton_inj (l₁ := [])).mp hw
  have hy : x = y := by cases t <;> cases hv <;> rfl
  subst y
  exact hc

/-- Every growth head exposes its actual memory and its chosen success/failure
permission, rather than replacing nondeterminism with a fixed oracle. -/
theorem head_grow {s : Store H} {f : Frame} {args : List Val} {x : MemIdx}
    {c : Config H} (h : Head P s f args (.plain (.memoryGrow x)) c) :
    ∃ (a : AddrType) (n : BitVec a.intType.width) (ma : Nat) (mi : MemInst),
      args = [addrVal a n] ∧ s.mem? f x = some (ma, mi) ∧
      ((∃ mi', mi.grow? n.toNat = some mi' ∧
          P.growMaySucceed .memory ma mi.pages n.toNat ∧
          c = ⟨s.setMem ma mi', f, [aconst a (BitVec.ofNat _ mi.pages)]⟩) ∨
       ((P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none) ∧
          c = ⟨s, f, [aconst a (BitVec.allOnes _)]⟩)) := by
  have hv := h.fam_inv (by simp [famOf])
  simp only [famOf, FamRel] at hv
  generalize he : (⟨s, f, vals args ++ [.plain (.memoryGrow x)]⟩ : Config H) = cfg at hv
  cases hv with
  | @growSucceed s' f' x' a n ma mi mi' hm hg hp =>
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, he⟩ := he
    obtain ⟨ha, hx⟩ := (append_singleton_inj (l₂ := [aconst a n])).mp he
    simp only [Admin.plain.injEq, Instr.memoryGrow.injEq] at hx
    subst x'
    exact ⟨a, n, ma, mi, vals_inj.mp ha, hm, .inl ⟨mi', hg, hp, rfl⟩⟩
  | @growFail s' f' x' a n ma mi hm hp =>
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, he⟩ := he
    obtain ⟨ha, hx⟩ := (append_singleton_inj (l₂ := [aconst a n])).mp he
    simp only [Admin.plain.injEq, Instr.memoryGrow.injEq] at hx
    subst x'
    exact ⟨a, n, ma, mi, vals_inj.mp ha, hm, .inr ⟨hp, rfl⟩⟩
  | _ =>
    simp only [Config.mk.injEq] at he
    have hh := congrArg List.getLast? he.2.2
    simp at hh

theorem addrVal_zero_inj {a b : AddrType} {n : BitVec b.intType.width}
    (h : addrVal a 0 = addrVal b n) :
    ∃ _e : a = b, HEq (0 : BitVec a.intType.width) n := by
  cases a <;> cases b <;> cases h <;> exact ⟨rfl, HEq.rfl⟩

theorem empty_grow_zero (a : AddrType) :
    (emptyMemory a).grow? 0 = some (emptyMemory a) := by
  simp [emptyMemory, MemInst.grow?]
  rfl

/-- Invert the actual chosen zero-growth transition. No profile is replaced
and neither permitted choice is discarded. -/
theorem grow_zero_step_inv {s : Store H} {f : Frame} {a : AddrType} {ma : Nat}
    {rest : List Admin} {c : Config H}
    (hm : s.mem? f ⟨0⟩ = some (ma, emptyMemory a))
    (hsame : s.setMem ma (emptyMemory a) = s)
    (h : Step P closedHost
      ⟨s, f, [aconst a 0, .plain (.memoryGrow ⟨0⟩)] ++ rest⟩ c) :
    (P.growMaySucceed .memory ma 0 0 ∧ c = ⟨s, f, aconst a 0 :: rest⟩) ∨
    (P.growMayFail .memory ma 0 0 ∧ c = ⟨s, f, aconst a (BitVec.allOnes _) :: rest⟩) := by
  have h' : Step P closedHost
      ⟨s, f, vals [addrVal a 0] ++ .plain (.memoryGrow ⟨0⟩) :: rest⟩ c := h
  obtain ⟨pre, args, cfg, hw, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h'
  obtain ⟨b, n, addr, mi, rfl, hm', choices⟩ := head_grow hh
  obtain ⟨rfl, hv⟩ := (append_singleton_inj (l₁ := [])).mp hw
  obtain ⟨rfl, hn⟩ := addrVal_zero_inj hv
  obtain rfl := eq_of_heq hn
  have hmEq := Option.some.inj (hm.symm.trans hm')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmEq
  rcases choices with ⟨mi', hg, hp, rfl⟩ | ⟨hp, rfl⟩
  · have hg' : some mi' = (emptyMemory a).grow? 0 := by simpa using hg.symm
    have heq : mi' = emptyMemory a := Option.some.inj (hg'.trans (empty_grow_zero a))
    subst mi'
    rw [hsame] at hc
    exact .inl ⟨by simpa [emptyMemory, MemInst.pages] using hp,
      by simpa [emptyMemory, MemInst.pages] using hc⟩
  · have hf : P.growMayFail .memory ma 0 0 := by
      rcases hp with hp | impossible
      · simpa [emptyMemory, MemInst.pages] using hp
      · simp [empty_grow_zero] at impossible
    exact .inr ⟨hf, by simpa using hc⟩

/-- Forced reductions compose with a label. Actual body steps exclude every
administrative exit, using the same generic inversion as dead-store completion. -/
theorem forced_label {c d : Config H} (h : Forced (P := P) c d)
    (n : Nat) (cont : List Instr) :
    Forced (P := P) ⟨c.store, c.frame, [.label n cont c.code]⟩
      ⟨d.store, d.frame, [.label n cont d.code]⟩ := by
  induction h with
  | done c => exact .done _
  | @step c d e hs unique tail ih =>
    rcases c with ⟨s, f, code⟩
    rcases d with ⟨s', f', code'⟩
    refine .step (.ctxtLabel hs) ?_ ih
    rintro ⟨t, g, es⟩ hstep
    obtain ⟨out, hr, he⟩ := Closure.Step.label_inv (us := []) (by simpa using hstep)
    obtain ⟨body, hbody, hout⟩ := CoalesceLocalsLite.labelRed_ctxt_of_step hs hr
    have hu := unique _ hbody
    simp only [Config.mk.injEq] at hu
    simp only [vals, List.map_nil, List.nil_append] at he
    simp only [Config.mk.injEq]
    exact ⟨hu.1, hu.2.1, by simpa [hout, hu.2.2] using he⟩

/-- Forced reductions likewise compose with a frame. -/
theorem forced_frame {c d : Config H} (h : Forced (P := P) c d)
    (n : Nat) (outer : Frame) :
    Forced (P := P) ⟨c.store, outer, [.frame n c.frame c.code]⟩
      ⟨d.store, outer, [.frame n d.frame d.code]⟩ := by
  induction h with
  | done c => exact .done _
  | @step c d e hs unique tail ih =>
    rcases c with ⟨s, f, code⟩
    rcases d with ⟨s', f', code'⟩
    refine .step (.ctxtFrame hs) ?_ ih
    rintro ⟨t, g, es⟩ hstep
    obtain ⟨out, he, hr⟩ := Closure.Step.frame_redex_aux hstep [] n f code rfl
    obtain ⟨fi, body, hbody, hg, hout⟩ := CoalesceLocalsLite.frameRedex_ctxt_of_step hs hr
    have hu := unique _ hbody
    simp only [Config.mk.injEq] at hu
    simp only [vals, List.map_nil, List.nil_append] at he
    change g = outer at hg
    simp only [Config.mk.injEq]
    exact ⟨hu.1, hg, by simpa [hout, hu.2.1, hu.2.2] using he⟩

theorem if_step_unique {s : Store H} {f : Frame} {c : BitVec 32}
    {bt : BlockType} {yes no : List Instr} {target : Config H}
    (h : Step P closedHost ⟨s, f, [constI32 c, .plain (.if_ bt yes no)]⟩ target) :
    target = ⟨s, f, [.plain (.block bt (if c = 0 then no else yes))]⟩ := by
  have h' : Step P closedHost
      ⟨s, f, vals [Val.i32 c] ++ [.plain (.if_ bt yes no)]⟩ target := h
  obtain ⟨pre, args, cfg, hw, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h'
  obtain ⟨d, rfl, rfl⟩ := GuardSim.head_if hh
  obtain ⟨rfl, hv⟩ := (append_singleton_inj (l₁ := [])).mp hw
  have hd : c = d := by cases hv; rfl
  subst d
  exact hc

theorem block_value_step_unique {s : Store H} {f : Frame} {a : AddrType}
    {body : List Instr} {target : Config H}
    (h : Step P closedHost ⟨s, f, [.plain (.block (.value (.num (.int a.intType))) body)]⟩ target) :
    target = ⟨s, f, [.label 1 [] (expression body)]⟩ := by
  obtain ⟨cfg, hh, hc⟩ := LoopCex.head_single h rfl (by simp) (by simp)
  cases hh with
  | block hbt hm =>
    simp only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] at hbt
    obtain ⟨rfl, rfl⟩ := hbt
    simpa [vals, Ty.length] using hc
  | _ => fam_absurd

theorem unreachable_step_unique {s : Store H} {f : Frame} {target : Config H}
    (h : Step P closedHost ⟨s, f, [.plain .unreachable]⟩ target) :
    target = ⟨s, f, [.trap]⟩ := by
  obtain ⟨cfg, hh, hc⟩ := LoopCex.head_single h rfl (by simp) (by simp)
  have hp := hh.fam_inv (by simp [famOf])
  simp only [famOf, FamRel] at hp
  obtain ⟨out, hp, rfl⟩ := hp
  generalize he : vals ([] : List Val) ++ [Admin.plain .unreachable] = code at hp
  cases hp with
  | unreachable => exact hc
  | _ =>
    have hl := congrArg List.getLast? he
    simp at hl

theorem label_trap_step_unique {s : Store H} {f : Frame} {n : Nat}
    {cont : List Instr} {target : Config H}
    (h : Step P closedHost ⟨s, f, [.label n cont [.trap]]⟩ target) :
    target = ⟨s, f, [.trap]⟩ := by
  obtain ⟨cfg, hh, hc⟩ := LoopCex.head_single h rfl (by simp) (by simp)
  cases hh with
  | ctxtLabel hs => exact (not_step_trap hs).elim
  | labelVals hb => exact (LoopCex.single_ne_vals rfl hb).elim
  | brLabelZero hb _ _ =>
    rw [LoopCex.vals_vals_br] at hb
    have he := (LoopCex.single_vals_inv rfl hb).2.1
    cases he
  | brLabelSucc hb _ | returnLabel hb =>
    rw [LoopCex.vals_one] at hb
    have he := (LoopCex.single_vals_inv rfl hb).2.1
    cases he
  | returnCallRefLabel hb hrc =>
    rw [LoopCex.vals_one] at hb
    have he := (LoopCex.single_vals_inv rfl hb).2.1
    subst he
    exact (hrc : False).elim
  | trapLabel => exact hc
  | _ => fam_absurd

theorem frame_trap_step_unique {s : Store H} {f fi : Frame} {n : Nat}
    {target : Config H}
    (h : Step P closedHost ⟨s, f, [.frame n fi [.trap]]⟩ target) :
    target = ⟨s, f, [.trap]⟩ := by
  obtain ⟨cfg, hh, hc⟩ := LoopCex.head_single h rfl (by simp) (by simp)
  cases hh with
  | ctxtFrame hs => exact (not_step_trap hs).elim
  | frameVals hb _ => exact (LoopCex.single_ne_vals rfl hb).elim
  | returnFrame hb _ =>
    rename_i pre args rest _hlen
    have hb' : [.trap] = vals (pre ++ args) ++ .plain .return_ :: rest := by
      simpa [List.append_assoc] using hb
    have he := (LoopCex.single_vals_inv rfl hb').2.1
    cases he
  | returnCallRefFrameNull hb _ | returnCallRefFrameAddr hb _ _ _ _ =>
    have he := congrArg List.length hb
    simp at he
    omega
  | trapFrame => exact hc
  | _ => fam_absurd

theorem forced_trans {c d e : Config H} (first : Forced (P := P) c d)
    (second : Forced (P := P) d e) : Forced (P := P) c e := by
  induction first with
  | done => exact second
  | step hs unique _ ih => exact .step hs unique (ih second)

theorem finish_values_forced (s : Store H) (f fi : Frame) (v : Val) :
    Forced (P := P) ⟨s, f, [.frame 1 fi [.label 1 [] (vals [v])]]⟩
      ⟨s, f, vals [v]⟩ := by
  have label : Forced (P := P) ⟨s, fi, [.label 1 [] (vals [v])]⟩ ⟨s, fi, vals [v]⟩ :=
    .step .labelVals (fun _ h => GrowWrapper.label_values_unique h) (.done _)
  exact forced_trans (forced_frame label 1 f)
    (.step (.frameVals rfl) (fun _ h => GrowWrapper.frame_values_unique h) (.done _))

theorem finish_trap_forced (s : Store H) (f fi : Frame) :
    Forced (P := P) ⟨s, f, [.frame 1 fi [.label 1 [] [.trap]]]⟩ ⟨s, f, [.trap]⟩ := by
  have label : Forced (P := P) ⟨s, fi, [.label 1 [] [.trap]]⟩ ⟨s, fi, [.trap]⟩ :=
    .step .trapLabel (fun _ h => label_trap_step_unique h) (.done _)
  exact forced_trans (forced_frame label 1 f)
    (.step .trapFrame (fun _ h => frame_trap_step_unique h) (.done _))

def guardRest (a : AddrType) : List Admin :=
  [.plain (.intTestOp a.intType .eqz),
    .plain (.if_ (.value (.num (.int a.intType))) [.intConst a.intType 0] [.unreachable])]

def guardResult (a : AddrType) (failure : Bool) : Result :=
  if failure then .trap else .values [addrVal a 0]

theorem block_zero_forced (s : Store H) (f : Frame) (a : AddrType) :
    Forced (P := P)
      ⟨s, f, [.plain (.block (.value (.num (.int a.intType))) [.intConst a.intType 0])]⟩
      ⟨s, f, [aconst a 0]⟩ := by
  refine .step (by simpa [vals] using
    (Step.block (P := P) (host := closedHost) (s := s) (f := f) (vs := [])
      (t₁ := []) (t₂ := [.num (.int a.intType)]) rfl rfl))
    (fun _ h => block_value_step_unique h) ?_
  simpa [expression, vals, addrVal, Val.toAdmin] using
    (Forced.step (Step.labelVals (P := P) (host := closedHost) (s := s) (f := f)
      (n := 1) (cont := []) (vs := [addrVal a 0]))
      (fun _ h => GrowWrapper.label_values_unique h) (.done _))

theorem block_trap_forced (s : Store H) (f : Frame) (a : AddrType) :
    Forced (P := P)
      ⟨s, f, [.plain (.block (.value (.num (.int a.intType))) [.unreachable])]⟩
      ⟨s, f, [.trap]⟩ := by
  refine .step (by simpa [vals] using
    (Step.block (P := P) (host := closedHost) (s := s) (f := f) (vs := [])
      (t₁ := []) (t₂ := [.num (.int a.intType)]) rfl rfl))
    (fun _ h => block_value_step_unique h) ?_
  have unreach : Forced (P := P) ⟨s, f, [.plain .unreachable]⟩ ⟨s, f, [.trap]⟩ :=
    .step (.parametric .unreachable) (fun _ h => unreachable_step_unique h) (.done _)
  exact forced_trans (forced_label unreach 1 [])
    (.step .trapLabel (fun _ h => label_trap_step_unique h) (.done _))

/-- The post-growth guard is forced and preserves the complete store. -/
theorem guard_forced (s : Store H) (f : Frame) (a : AddrType) (failure : Bool) :
    Forced (P := P)
      ⟨s, f, aconst a (if failure then BitVec.allOnes _ else 0) :: guardRest a⟩
      ⟨s, f, (guardResult a failure).toAdmin⟩ := by
  have test_zero : intTestOp a.intType .eqz (0 : BitVec a.intType.width) = (1 : BitVec 32) := by cases a <;> decide +kernel
  have test_fail : intTestOp a.intType .eqz (BitVec.allOnes _) = 0 := by
    cases a <;> decide +kernel
  cases failure with
  | false =>
    refine .step (d := ⟨s, f, [constI32 1,
      .plain (.if_ (.value (.num (.int a.intType))) [.intConst a.intType 0] [.unreachable])]⟩)
      (by simpa only [guardRest, aconst, Bool.false_eq_true, ↓reduceIte, test_zero, List.cons_append, List.nil_append] using
      (Step.append_right (Step.numeric (P := P) (host := closedHost) (s := s) (f := f)
        (NumericStep.intTestOp (t := a.intType) (op := .eqz) (x := 0)))
        [(.plain (.if_ (.value (.num (.int a.intType))) [.intConst a.intType 0] [.unreachable]))]))
      (fun _ h => by rw [← test_zero]; exact intTest_step_unique h) ?_
    refine .step (.ifTrue (by decide)) (fun _ h => by simpa using if_step_unique h) ?_
    simpa [guardResult, Result.toAdmin, addrVal, vals, Val.toAdmin] using block_zero_forced (P := P) s f a
  | true =>
    refine .step (d := ⟨s, f, [constI32 0,
      .plain (.if_ (.value (.num (.int a.intType))) [.intConst a.intType 0] [.unreachable])]⟩)
      (by simpa [guardRest, test_fail] using
      (Step.append_right (Step.numeric (P := P) (host := closedHost) (s := s) (f := f)
        (NumericStep.intTestOp (t := a.intType) (op := .eqz) (x := BitVec.allOnes _)))
        [(.plain (.if_ (.value (.num (.int a.intType))) [.intConst a.intType 0] [.unreachable]))]))
      (fun _ h => by simpa [test_fail] using intTest_step_unique h) ?_
    refine .step .ifFalse (fun _ h => by simpa using if_step_unique h) ?_
    simpa [guardResult, Result.toAdmin] using block_trap_forced (P := P) s f a

end Silmaril.Wasm.Binaryen.GrowOOM
