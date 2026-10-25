module

public import Silmaril.Wasm.Binaryen.GrowWrapper
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowWrapper

open Execution.Core Execution.Core.Sim Numerics Validation MemoryGrowFailure
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Wasm.SingleThreaded.Exec

variable {H : Type} {P : Profile}

/-- A finite path whose next reduction is forced at every intermediate state. -/
inductive Forced : Config H → Config H → Prop where
  | done (c : Config H) : Forced c c
  | step {c d e : Config H} (hs : Step P closedHost c d)
      (unique : ∀ d', Step P closedHost c d' → d' = d)
      (tail : Forced d e) : Forced c e

namespace Forced

theorem steps {c d : Config H} (h : Forced (P := P) c d) : Steps P closedHost c d := by
  induction h with
  | done => exact .refl
  | step hs _ _ ih => exact .head hs ih

theorem reachable {c d : Config H} (h : Forced (P := P) c d)
    (hn : ∀ x, ¬ Step P closedHost d x) {e : Config H} (run : Steps P closedHost c e) : Steps P closedHost e d := by
  induction h with
  | done =>
    rcases run.cases_head with rfl | ⟨x, hx, _⟩
    · exact .refl
    · exact (hn x hx).elim
  | step hs unique tail ih =>
    rcases run.cases_head with rfl | ⟨x, hx, hxe⟩
    · exact .head hs tail.steps
    · obtain rfl := unique _ hx
      exact ih hn hxe

theorem not_diverges {c d : Config H} (h : Forced (P := P) c d)
    (hn : ∀ x, ¬ Step P closedHost d x) : ¬ Diverges P closedHost c := by
  intro hd
  induction h with
  | done =>
    obtain ⟨x, hx, _⟩ := InfiniteTrace.unfold hd
    exact hn x hx
  | step _ unique _ ih =>
    obtain ⟨x, hx, hd'⟩ := InfiniteTrace.unfold hd
    obtain rfl := unique _ hx
    exact ih hn hd'

theorem terminal_eq {c d e : Config H} (h : Forced (P := P) c d)
    (hn : ∀ x, ¬ Step P closedHost d x) (run : Steps P closedHost c e)
    (he : e.Terminal) : e = d := by
  have hb := h.reachable hn run
  rcases hb.cases_head with heq | ⟨x, hx, _⟩
  · exact heq
  · exact (BehaviourRefinement.not_step_of_terminal he hx).elim

end Forced

theorem invoke_first_unique {s : Store H} {a : Nat} {fi : FuncInst H}
    {fn : Func} {rt : CValType} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func .nil (.cons rt .nil))) (hfn : fi.code = .wasm fn)
    {c : Config H} (hs : Step P closedHost (invoke s a []) c) :
    c = ⟨s, {}, [.frame 1 (Frame.forCall fi.module [] fn.locals)
      [.label 1 [] (expression fn.body)]]⟩ := by
  unfold closedHost at hs
  have hs' : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, {}, vals [Val.ref (.func a)] ++ [.callRefType fi.type]⟩ c := by
    simpa [invoke, hf, vals, Val.toAdmin] using hs
  obtain ⟨pre, args, c₀, hw, hh, hc⟩ := Step.head_inv hs' rfl (by simp) (by simp)
  cases hh with
  | parametric h => exact (by have h' := (famOf_of_shape (ParametricStep.shape h)).2; cases h')
  | numeric h => exact (by have h' := (famOf_of_shape (NumericStep.shape h)).2; cases h')
  | vector h => exact (by have h' := (famOf_of_shape (VectorStep.shape h)).2; cases h')
  | «variable» h => exact (by have h' := (famOf_of_shape (VariableStep.shape h)).2; cases h')
  | table h => exact (by have h' := (famOf_of_shape (TableStep.shape h)).2; cases h')
  | memory h => exact (by have h' := (famOf_of_shape (MemoryStep.shape h)).2; cases h')
  | reference h => exact (by have h' := (famOf_of_shape (RefStep.shape h)).2; cases h')
  | aggregate h => exact (by have h' := (famOf_of_shape (AggregateStep.shape h)).2; cases h')
  | callRefNull _ =>
    have h := ((append_singleton_inj (l₁ := [])).mp hw).2
    cases h
  | callRefFunc ha _ hf' he' hn hfn' =>
    rw [ha, ← List.append_assoc] at hw
    obtain ⟨hpre, haddr⟩ := (append_singleton_inj (l₁ := [])).mp hw
    simp only [List.nil_eq_append_iff] at hpre
    obtain ⟨rfl, rfl⟩ := hpre
    cases haddr
    have hfi := hf.symm.trans hf'
    cases hfi
    have htypes := (Expand.iff.mp he).symm.trans (Expand.iff.mp he')
    simp only [Option.some.injEq, Ty.func.injEq] at htypes
    obtain ⟨rfl, rfl⟩ := htypes
    cases hfn.symm.trans hfn'
    simpa [vals, Ty.length] using hc


theorem label_values_unique {s : Store H} {f : Frame} {n : Nat}
    {cont : List Instr} {vs : List Val} {c : Config H}
    (hs : Step P closedHost ⟨s, f, [.label n cont (vals vs)]⟩ c) :
    c = ⟨s, f, vals vs⟩ := by
  obtain ⟨c₀, hh, hc⟩ := LoopCex.head_single hs rfl (by simp) (by simp)
  generalize hb : vals vs = body at hh
  cases hh with
  | ctxtLabel h => exact (not_step_vals (hb ▸ h)).elim
  | labelVals hv =>
    obtain rfl := vals_inj.mp (hb.trans hv)
    simpa only [← hb] using hc
  | brLabelZero hx _ _ | brLabelSucc hx _ | returnLabel hx =>
    have hx := congrArg (fun code : List Admin => code.all Admin.isVal) (hb.trans hx)
    simp [List.all_append, Admin.isVal, Admin.val?] at hx
  | returnCallRefLabel hx hcall =>
    have hx := congrArg (fun code : List Admin => code.all Admin.isVal) (hb.trans hx)
    simp [List.all_append, Admin.isVal, Admin.val?_of_isReturnCallRef hcall] at hx
  | trapLabel =>
    have hx := congrArg (fun code : List Admin => code.all Admin.isVal) hb
    simp [Admin.isVal, Admin.val?] at hx
  | throwRefLabel =>
    have hm : Admin.plain .throwRef ∈ vals vs := by rw [hb]; simp
    exact (mem_vals hm rfl).elim
  | _ => fam_absurd

theorem frame_values_unique {s : Store H} {f fi : Frame} {n : Nat}
    {vs : List Val} {c : Config H}
    (hs : Step P closedHost ⟨s, f, [.frame n fi (vals vs)]⟩ c) :
    c = ⟨s, f, vals vs⟩ := by
  obtain ⟨c₀, hh, hc⟩ := LoopCex.head_single hs rfl (by simp) (by simp)
  generalize hb : vals vs = body at hh
  cases hh with
  | ctxtFrame h => exact (not_step_vals (hb ▸ h)).elim
  | frameVals hv _ =>
    obtain rfl := vals_inj.mp (hb.trans hv)
    simpa only [← hb] using hc
  | returnFrame hx _ =>
    have hx := congrArg (fun code : List Admin => code.all Admin.isVal) (hb.trans hx)
    simp [List.all_append, Admin.isVal, Admin.val?] at hx
  | returnCallRefFrameNull hx hcall | returnCallRefFrameAddr hx hcall _ _ _ =>
    have hx := congrArg (fun code : List Admin => code.all Admin.isVal) (hb.trans hx)
    simp [List.all_append, Admin.isVal, Admin.val?_of_isReturnCallRef hcall] at hx
  | trapFrame =>
    have hx := congrArg (fun code : List Admin => code.all Admin.isVal) hb
    simp [Admin.isVal, Admin.val?] at hx
  | throwRefFrame =>
    have hm : Admin.plain .throwRef ∈ vals vs := by rw [hb]; simp
    exact (mem_vals hm rfl).elim
  | _ => fam_absurd

theorem frame_single_inv {s : Store H} {f fi : Frame} {n : Nat}
    {a : Admin} {c : Config H}
    (hs : Step P closedHost ⟨s, f, [.frame n fi [a]]⟩ c)
    (ha : a.val? = none) (htrap : a ≠ .trap) (hret : a ≠ .plain .return_) :
    ∃ s' fi' body, Step P closedHost ⟨s, fi, [a]⟩ ⟨s', fi', body⟩ ∧
      c = ⟨s', f, [.frame n fi' body]⟩ := by
  obtain ⟨c₀, hh, hc⟩ := LoopCex.head_single hs rfl (by simp) (by simp)
  cases hh with
  | ctxtFrame h => exact ⟨_, _, _, h, hc⟩
  | frameVals hb _ => exact (LoopCex.single_ne_vals ha hb).elim
  | @returnFrame _ _ _ _ pre args rest hb _ =>
    have hb' : [a] = vals (pre ++ args) ++ .plain .return_ :: rest := by
      simpa [List.append_assoc] using hb
    have h := (LoopCex.single_vals_inv ha hb').2.1
    exact (hret h.symm).elim
  | returnCallRefFrameNull hb _ | returnCallRefFrameAddr hb _ _ _ _ =>
    have hlen := congrArg List.length hb
    simp at hlen
    omega
  | trapFrame => exact (htrap rfl).elim
  | _ => fam_absurd


/-- Enter the allocated wrapper, preserving the complete store. -/
theorem invoke_first (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (failure : Bool) :
    Step P closedHost (invoke (store s a n failure) s.funcs.length [])
      ⟨store s a n failure, {}, [.frame 1 {module := moduleInst s a}
        [.label 1 [] (expression (func a n failure).body)]]⟩ := by
  have h := Step.callRefFunc (P := P) (host := closedHost)
    (s := store s a n failure) (f := {})
    (c := .callRefType (dt a)) (vs := []) trivial (func_lookup s a n failure)
    (Expand.iff.mpr (expand_dt a)) rfl rfl
  simpa [invoke, func_lookup, Frame.forCall, func, vals, Ty.length] using h

theorem finish (s : Store H) (f fi : Frame) (v : Val) :
    Steps P closedHost ⟨s, f, [.frame 1 fi [.label 1 [] (vals [v])]]⟩
      ⟨s, f, vals [v]⟩ :=
  (Step.ctxtFrame (Step.labelVals (P := P) (host := closedHost)
    (s := s) (f := fi) (n := 1) (cont := []) (vs := [v]))).steps.trans
    (Step.frameVals (P := P) (host := closedHost) (s := s) (f := f)
      (fi := fi) (vs := [v]) rfl).steps

/-- Every target invocation follows a forced finite path and leaves exactly the
original store, including the exported memory, unchanged. -/
theorem target_forced (s : Store H) (a : AddrType) (n : BitVec a.intType.width) :
    Forced (P := P) (invoke (store s a n true) s.funcs.length [])
      ⟨store s a n true, {}, vals [failed a]⟩ := by
  refine .step (invoke_first s a n true) ?_ ?_
  · intro c hc
    simpa [func, expression, Frame.forCall, vals, failed, addrVal, Val.toAdmin] using
      invoke_first_unique (func_lookup s a n true)
        (Expand.iff.mpr (expand_dt a)) rfl hc
  · change Forced (P := P)
      ⟨store s a n true, {}, [.frame 1 {module := moduleInst s a}
        [.label 1 [] (vals [failed a])]]⟩ _
    refine .step (Step.ctxtFrame (Step.labelVals (vs := [failed a]))) ?_ ?_
    · intro c hc
      obtain ⟨s', fi', body, hi, hcode⟩ :=
        frame_single_inv hc rfl (by simp) (by simp)
      have he := label_values_unique hi
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact hcode
    · exact .step (Step.frameVals (vs := [failed a]) rfl)
        (fun _ hc => frame_values_unique hc) (.done _)

/-- The source matches the target return by choosing failure, preserving its
complete store exactly. This applies to every literal delta. -/
theorem source_failure_run (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Steps (Profile.spec nd r) closedHost
      (invoke (store s a n false) s.funcs.length [])
      ⟨store s a n false, {}, vals [failed a]⟩ := by
  have hm : (store s a n false).mem? {module := moduleInst s a} ⟨0⟩ =
      some (s.mems.length, emptyMemory a) := by
    simp [Store.mem?, store, moduleInst, Idx.toNat]
  have hg := (source_fail (P := Profile.spec nd r) (host := closedHost)
    (n := n) hm (.inl trivial) [] []).steps
  have hbody : Steps (Profile.spec nd r) closedHost
      ⟨store s a n false, {module := moduleInst s a}, expression (func a n false).body⟩
      ⟨store s a n false, {module := moduleInst s a}, vals [failed a]⟩ := by
    simpa [func, expression, failed, addrVal, vals, Val.toAdmin] using hg
  exact (invoke_first s a n false).steps.trans
    ((Steps.frame (Steps.label hbody)).trans (finish _ _ _ _))

/-- A completed target call determines the full final store and result. -/
theorem target_run_inv (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    {c : Config H} {r : Result}
    (run : Steps P closedHost (invoke (store s a n true) s.funcs.length []) c)
    (hr : c.code = r.toAdmin) :
    c = ⟨store s a n true, {}, vals [failed a]⟩ ∧ r = .values [failed a] := by
  have hc := (target_forced (P := P) s a n).terminal_eq
    (fun _ => not_step_vals) run ⟨r, hr⟩
  subst c
  refine ⟨rfl, ?_⟩
  have he := (BehaviourRefinement.outcome?_eq_some_of_code hr).symm.trans
    (BehaviourRefinement.outcome?_eq_some_of_code (r := .values [failed a]) rfl)
  exact Option.some.inj he

/-- Every target session is matched by the source with exactly the same
observations. The unchanged stores allow arbitrarily many calls. -/
theorem session_source_of_target (s : Store H) (a : AddrType)
    (n : BitVec a.intType.width) (nd : Bool) (r : RelaxedChoice)
    (script : List Call) {bs : List (Behaviour Val)}
    (ht : Session (Profile.spec nd r) closedHost (moduleInst s a)
      (store s a n true) script bs) :
    Session (Profile.spec nd r) closedHost (moduleInst s a)
      (store s a n false) script bs := by
  induction script generalizing bs with
  | nil => cases ht; exact .nil
  | cons call rest ih =>
    obtain ⟨x, vs⟩ := call
    cases ht with
    | stop h =>
      exact .stop fun addr ha hok => h addr ha (by
        obtain ⟨_, rfl⟩ := (exportFunc_iff s a x addr).mp ha
        exact (invokeOk_iff s a n true vs).mpr ((invokeOk_iff s a n false vs).mp hok))
    | @done _ _ _ _ addr c result _ ha hok run hr tail =>
      obtain ⟨rfl, rfl⟩ := (exportFunc_iff s a x addr).mp ha
      obtain rfl := (invokeOk_iff s a n true vs).mp hok
      obtain ⟨rfl, rfl⟩ := target_run_inv s a n run hr
      exact .done ((exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
        ((invokeOk_iff s a n false []).mpr rfl)
        (source_failure_run s a n nd r) rfl (ih tail)
    | @diverge _ _ _ _ addr ha hok hd =>
      obtain ⟨_, rfl⟩ := (exportFunc_iff s a x addr).mp ha
      obtain rfl := (invokeOk_iff s a n true vs).mp hok
      exact ((target_forced s a n).not_diverges (fun _ => not_step_vals) hd).elim

/-- The closed target admits a session observation for every script, even if
an invalid request ends the session early. No host totality is assumed. -/
theorem target_session_exists (s : Store H) (a : AddrType)
    (n : BitVec a.intType.width) (script : List Call) :
    ∃ bs, Session P closedHost (moduleInst s a) (store s a n true) script bs := by
  induction script with
  | nil => exact ⟨[], .nil⟩
  | cons call rest ih =>
    obtain ⟨x, vs⟩ := call
    by_cases hv : x = "grow" ∧ vs = []
    · obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨bs, hb⟩ := ih
      exact ⟨.returns [failed a] :: bs,
        .done (r := .values [failed a]) ((exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
          ((invokeOk_iff s a n true []).mpr rfl) (target_forced s a n).steps rfl hb⟩
    · exact ⟨[], .stop fun addr ha hok => hv
        ⟨((exportFunc_iff s a x addr).mp ha).1,
          (invokeOk_iff s a n true vs).mp (by
            obtain ⟨_, rfl⟩ := (exportFunc_iff s a x addr).mp ha
            exact hok)⟩⟩

/-- The zero-delta source may also succeed, returning its old size `0`. This
fixture is used only to separate refinement from equivalence. -/
theorem source_zero_success (a : AddrType) (nd : Bool) (r : RelaxedChoice) :
    Steps (Profile.spec nd r) closedHost
      (invoke (store ({} : Store H) a 0 false) 0 [])
      ⟨store {} a 0 false, {}, vals [addrVal a 0]⟩ := by
  have hm : (store ({} : Store H) a 0 false).mem? {module := moduleInst ({} : Store H) a} ⟨0⟩ =
      some (0, emptyMemory a) := by
    simp [Store.mem?, store, moduleInst, Idx.toNat]
  have hg : (emptyMemory a).grow? (0 : BitVec a.intType.width).toNat =
      some (emptyMemory a) := by
    simp [emptyMemory, MemInst.grow?]
    rfl
  have hmem := (Step.memory (host := (closedHost : HostSemantics H))
    (MemoryStep.growSucceed (P := Profile.spec nd r) hm hg (by trivial))).steps
  have hbody : Steps (Profile.spec nd r) closedHost
      ⟨store ({} : Store H) a 0 false, {module := moduleInst ({} : Store H) a},
        expression (func a 0 false).body⟩
      ⟨store {} a 0 false, {module := moduleInst ({} : Store H) a}, vals [addrVal a 0]⟩ := by
    simpa [func, expression, addrVal, emptyMemory, MemInst.pages, vals, Val.toAdmin,
      Store.setMem, store, List.set] using hmem
  exact (invoke_first ({} : Store H) a 0 false).steps.trans
    ((Steps.frame (Steps.label hbody)).trans (finish _ _ _ _))

/-- A single valid target call can observe only the selected failure return. -/
theorem target_session_single (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    {bs : List (Behaviour Val)}
    (hs : Session P closedHost (moduleInst s a) (store s a n true) [("grow", [])] bs) :
    bs = [.returns [failed a]] := by
  cases hs with
  | stop h => exact (h s.funcs.length
      ((exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
      ((invokeOk_iff s a n true []).mpr rfl)).elim
  | @done _ _ _ _ addr c result _ ha _ run hr tail =>
    obtain ⟨_, rfl⟩ := (exportFunc_iff s a "grow" addr).mp ha
    obtain ⟨rfl, rfl⟩ := target_run_inv s a n run hr
    cases tail
    rfl
  | @diverge _ _ _ _ addr ha _ hd =>
    obtain ⟨_, rfl⟩ := (exportFunc_iff s a "grow" addr).mp ha
    exact ((target_forced s a n).not_diverges (fun _ => not_step_vals) hd).elim

end Silmaril.Wasm.Binaryen.GrowWrapper
