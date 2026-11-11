module

public import Silmaril.Wasm.SSA.CoreCert.Defs
public import Silmaril.Wasm.SSA.Native.Thms
public import Silmaril.Wasm.Interp.Thms

@[expose] public section

/-!
# Invocations of a native fragment function (proofs)

The native behaviours (`Binaryen.nbeh`) of an invocation are determined by its observations,
the results `invokeRun` reaches at some fuel (`nbeh_congr`). For a function whose code is the
lowering of a recognised, arity-checked (`FragFunc.native`), folded body, invoked on integer
arguments of its parameter types, the observations are exactly the images (`foutFlow`) of the
outcomes of the fragment function (`obs_iff_run`), by `native_adequate`, `native_outcome` and
silmaril's folding invariance (`eval_of_eval_lift`, `eval_lift_of_eval`). New proofs.
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

variable {H : Type}

/-! ## Observations of an invocation -/

/-- The results an invocation reaches at some fuel. -/
def Obs (s : Store H) (a : Nat) (vs : List Val) (fl : Flow) : Prop :=
  ∃ fuel s', invokeRun fuel s a vs = some (s', fl)

/-- No fuel suffices exactly when nothing is observed. -/
theorem invokeRun_none_iff (s : Store H) (a : Nat) (vs : List Val) :
    (∀ fuel, invokeRun fuel s a vs = none) ↔ ¬ ∃ fl, Obs s a vs fl := by
  constructor
  · rintro hn ⟨fl, fuel, s', hs⟩
    have hc : (none : Option (Store H × Flow)) = some (s', fl) := (hn fuel).symm.trans hs
    cases hc
  · intro hn fuel
    rcases hr : invokeRun fuel s a vs with _ | ⟨s', fl⟩
    · rfl
    · exact absurd ⟨fl, fuel, s', hr⟩ hn

/-- **Native behaviours are determined by observations.** -/
theorem nbeh_congr {H' : Type} {s : Store H} {s' : Store H'} {a a' : Nat} {vs vs' : List Val}
    (h : ∀ fl, Obs s a vs fl ↔ Obs s' a' vs' fl) : nbeh s a vs = nbeh s' a' vs' := by
  have hnone : (∀ fuel, invokeRun fuel s a vs = none) ↔
      (∀ fuel, invokeRun fuel s' a' vs' = none) :=
    (invokeRun_none_iff s a vs).trans
      ((not_congr (exists_congr h)).trans (invokeRun_none_iff s' a' vs').symm)
  ext b
  constructor
  · rintro (⟨fuel, s₁, fl, hr, hb⟩ | ⟨rfl, hd⟩)
    · obtain ⟨fuel', s₁', hr'⟩ := (h fl).mp ⟨fuel, s₁, hr⟩
      exact .inl ⟨fuel', s₁', fl, hr', hb⟩
    · exact .inr ⟨rfl, hnone.mp hd⟩
  · rintro (⟨fuel, s₁, fl, hr, hb⟩ | ⟨rfl, hd⟩)
    · obtain ⟨fuel', s₁', hr'⟩ := (h fl).mpr ⟨fuel, s₁, hr⟩
      exact .inl ⟨fuel', s₁', fl, hr', hb⟩
    · exact .inr ⟨rfl, hnone.mpr hd⟩

/-- The flow an invocation hands back for a final flow of its body (`invokeRun`). -/
def retFlow (n : Nat) : Flow → Option Flow
  | .normal ws | .ret ws | .brk 0 ws => some (.normal (ws.take n).reverse)
  | .trap => some .trap
  | .throw x => some (.throw x)
  | _ => none

/-- `invokeRun` through its body. -/
theorem invokeRun_eq {fuel : Nat} {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    invokeRun fuel s a vs =
      (run fuel s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)).bind
        fun r => (retFlow rs.length r.2.2).map fun fl => (r.1, fl) := by
  unfold invokeRun
  rw [hfi]
  simp only [hcode, hty]
  rcases run fuel s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) with
    _ | ⟨s', f', fl⟩
  · rfl
  · rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | x <;> rfl

/-- Observations through the body, as evaluations. -/
theorem obs_iff_eval {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (fl : Flow) :
    Obs s a vs fl ↔ ∃ s' f' bfl, Eval s (Frame.forCall fi.module vs fn.locals) []
      (liftInstrs fn.body) (s', f', bfl) ∧ retFlow rs.length bfl = some fl := by
  constructor
  · rintro ⟨fuel, s', hr⟩
    rw [invokeRun_eq hfi hcode hty, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨s₁, f₁, bfl⟩, hrun, hk⟩ := hr
    obtain ⟨fl', hfl', he⟩ := Option.map_eq_some_iff.mp hk
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact ⟨s₁, f₁, bfl, eval_of_run hrun, hfl'⟩
  · rintro ⟨s', f', bfl, he, hfl⟩
    obtain ⟨fuel, hrun⟩ := run_of_eval he
    refine ⟨fuel, s', ?_⟩
    rw [invokeRun_eq hfi hcode hty, hrun]
    simp [hfl]

/-! ## Fragment functions -/

theorem ofVal?_eq_some {v : Val} {w : WVal} (h : WVal.ofVal? v = some w) : v = w.toVal := by
  rcases v with ⟨⟨ty, x⟩⟩ | _ | _ <;> (try rcases ty with ty | ty) <;> (try cases ty) <;>
    simp only [WVal.ofVal?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

/-- The flow an invocation hands back for a call outcome. -/
def foutFlow : FOut → Flow
  | .ret none => .normal []
  | .ret (some w) => .normal [w.toVal]
  | .trap => .trap

/-- A normal, `return` or own-label result with a call outcome hands back that outcome's flow. -/
theorem retFlow_normal {res : Option IntType} {ws : List Val} {o : FOut}
    (hw : flowOut res (.normal ws) = some o) :
    some (Flow.normal ((ws.take (resultTypes res).length).reverse)) = some (foutFlow o) := by
  cases res with
  | none =>
    have ho : o = .ret none := (Option.some.inj hw).symm
    rw [ho]
    rfl
  | some t =>
    have hw' : ∃ w, (∃ v, ws.head? = some v ∧ WVal.ofVal? v = some w) ∧ FOut.ret (some w) = o := by
      simpa only [flowOut, Option.map_eq_some_iff, Option.bind_eq_some_iff] using hw
    obtain ⟨w, ⟨v, hv, hvw⟩, rfl⟩ := hw'
    obtain ⟨r, rfl⟩ : ∃ r, ws = v :: r := by
      rcases ws with _ | ⟨v', r⟩
      · cases hv
      · exact ⟨r, by rw [Option.some.inj hv]⟩
    show some (Flow.normal [v]) = some (Flow.normal [w.toVal])
    rw [ofVal?_eq_some hvw]

/-- The flow handed back for a body flow with a call outcome is that outcome's. -/
theorem retFlow_of_flowOut {res : Option IntType} {fl : Flow} {o : FOut}
    (h : flowOut res fl = some o) : retFlow (resultTypes res).length fl = some (foutFlow o) := by
  rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | x
  · exact retFlow_normal h
  · exact retFlow_normal (by simpa [flowOut] using h)
  · simp [flowOut] at h
  · exact retFlow_normal (by simpa [flowOut] using h)
  · have ho : o = .trap := (Option.some.inj h).symm
    rw [ho]
    rfl
  · simp [flowOut] at h

/-- The integer value types of a recognised list. -/
theorem mapM_ofValType? : ∀ {ts : List ValType} {us : List IntType},
    ts.mapM ofValType? = some us → ts = us.map fun t => .num (.int t)
  | [], us, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | t :: ts, us, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨u, hu, us', hus, rfl⟩ := h
    have ht : t = .num (.int u) := by
      rcases t with ⟨_ | _⟩ | _ | _ <;> simp only [ofValType?, reduceCtorEq,
        Option.some.injEq] at hu
      subst hu
      rfl
    rw [ht, mapM_ofValType? hus]
    rfl

/-- A recognised function's locals are its fragment locals. -/
theorem locals_of_ofBFunc? {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (h : ofBFunc? ft bf = some f) : bf.locals = f.locals.map fun t => .num (.int t) := by
  obtain ⟨params, results⟩ := ft
  rcases results with _ | ⟨t, _ | ⟨t₂, rest⟩⟩ <;>
    simp only [ofBFunc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
  · obtain ⟨_, _, _, _, ls, hls, _, _, rfl⟩ := h
    exact mapM_ofValType? hls
  · obtain ⟨_, _, _, _, ls, hls, _, _, rfl⟩ := h
    exact mapM_ofValType? hls
  · simp at h

/-- The callee frame of integer arguments and integer locals is the fragment's frame. -/
theorem forCall_eq (mi : ModuleInst) (args : List WVal) (ls : List IntType) (f : FragFunc)
    (hls : f.locals = ls) :
    Frame.forCall mi (args.map WVal.toVal) (ls.map fun t => .num (.int t)) =
      frameOf mi (f.initLocals args) := by
  subst hls
  have hz : ∀ t : IntType, defaultVal? ((Validation.liftVal (.num (.int t))).substAll
      (mi.types.map .dt)) = some (WVal.toVal (WVal.zero t)) := by
    intro t
    cases t <;> rfl
  simp only [Frame.forCall, frameOf, FragFunc.initLocals, List.map_append, List.map_map]
  congr 2
  apply List.map_congr_left
  intro t _
  exact hz t

/-- **Observations of a fragment function** are the images of its outcomes. -/
theorem obs_iff_run {s : Store H} {a : Nat} {fi : FuncInst H} {ft : FuncType} {bf : BFunc}
    {f : FragFunc} {ps rs : List Validation.CValType} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm (coreFunc bf)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hrs : rs.length = (resultTypes f.result).length) (hf : ofBFunc? ft bf = some f)
    (hn : f.native = true) (hst : BExpr.structuredList bf.body = true) {args : List WVal}
    (hargs : args.map WVal.type = f.params) (fl : Flow) :
    Obs s a (args.map WVal.toVal) fl ↔ ∃ o, f.Run args o ∧ fl = foutFlow o := by
  have hframe : Frame.forCall fi.module (args.map WVal.toVal) (coreFunc bf).locals =
      frameOf fi.module (f.initLocals args) := by
    rw [show (coreFunc bf).locals = bf.locals from rfl, locals_of_ofBFunc? hf]
    exact forCall_eq fi.module args f.locals f rfl
  have hb : ofBExprs? bf.body = some f.body := ofBFunc?_body hf
  rw [obs_iff_eval hfi hcode hty, hframe]
  constructor
  · rintro ⟨s', f', bfl, he, hr⟩
    have he' : Eval s (frameOf fi.module (f.initLocals args)) [] bf.body (s', f', bfl) :=
      eval_of_eval_lift bf.body hst he
    obtain ⟨o, ho, hrun⟩ := native_outcome hb hn hargs he'
    have hr' : retFlow rs.length bfl = some (foutFlow o) := hrs ▸ retFlow_of_flowOut ho
    exact ⟨o, hrun, Option.some.inj (hr.symm.trans hr')⟩
  · rintro ⟨o, hrun, rfl⟩
    obtain ⟨s', fr, bfl, he, ho⟩ := (native_adequate s fi.module hb hn hargs o).mp hrun
    exact ⟨s', fr, bfl, eval_lift_of_eval he hst, hrs ▸ retFlow_of_flowOut ho⟩

theorem flowBeh_foutFlow (o : FOut) : flowBeh (foutFlow o) = some (outBeh (some o)) := by
  rcases o with ⟨_ | _⟩ | _ <;> rfl

/-- No fuel suffices exactly when there is no outcome. -/
theorem none_iff_no_outcome {s : Store H} {a : Nat} {vs : List Val} {R : FOut → Prop}
    (hobs : ∀ fl, Obs s a vs fl ↔ ∃ o, R o ∧ fl = foutFlow o) :
    (∀ fuel, invokeRun fuel s a vs = none) ↔ ∀ o, ¬ R o := by
  refine (invokeRun_none_iff s a vs).trans
    ⟨fun h o ho => h ⟨foutFlow o, (hobs _).mpr ⟨o, ho, rfl⟩⟩, ?_⟩
  rintro h ⟨fl, hfl⟩
  obtain ⟨o, ho, -⟩ := (hobs fl).mp hfl
  exact h o ho

/-- **Native behaviours from outcomes**: when the observations are the images of the outcomes
`R`, the native behaviours are the outcomes, and divergence exactly when there is none. -/
theorem nbeh_of_outcomes {s : Store H} {a : Nat} {vs : List Val} {R : FOut → Prop}
    (hobs : ∀ fl, Obs s a vs fl ↔ ∃ o, R o ∧ fl = foutFlow o) :
    nbeh s a vs = {b | (∃ o, R o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ R o)} := by
  have hnone : (∀ fuel, invokeRun fuel s a vs = none) ↔ ∀ o, ¬ R o := none_iff_no_outcome hobs
  ext b
  constructor
  · rintro (⟨fuel, s₁, fl, hr, hb⟩ | ⟨rfl, hd⟩)
    · obtain ⟨o, ho, rfl⟩ := (hobs fl).mp ⟨fuel, s₁, hr⟩
      have hb' : outBeh (some o) = b := Option.some.inj ((flowBeh_foutFlow o).symm.trans hb)
      exact .inl ⟨o, ho, hb'.symm⟩
    · exact .inr ⟨rfl, hnone.mp hd⟩
  · rintro (⟨o, ho, rfl⟩ | ⟨rfl, hd⟩)
    · obtain ⟨fuel, s₁, hr⟩ := (hobs (foutFlow o)).mpr ⟨o, ho, rfl⟩
      exact .inl ⟨fuel, s₁, foutFlow o, hr, flowBeh_foutFlow o⟩
    · exact .inr ⟨rfl, hnone.mpr hd⟩

/-- **The native behaviours of a fragment function** are its outcomes, and divergence when it
has none. -/
theorem nbeh_eq_run {s : Store H} {a : Nat} {fi : FuncInst H} {ft : FuncType} {bf : BFunc}
    {f : FragFunc} {ps rs : List Validation.CValType} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm (coreFunc bf)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hrs : rs.length = (resultTypes f.result).length) (hf : ofBFunc? ft bf = some f)
    (hn : f.native = true) (hst : BExpr.structuredList bf.body = true) {args : List WVal}
    (hargs : args.map WVal.type = f.params) :
    nbeh s a (args.map WVal.toVal) =
      {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} :=
  nbeh_of_outcomes (obs_iff_run hfi hcode hty hrs hf hn hst hargs)

end Silmaril.Proofs.Wasm.SSA.CoreCert
