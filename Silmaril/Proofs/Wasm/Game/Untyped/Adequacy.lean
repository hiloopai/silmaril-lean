module

public import Silmaril.Proofs.Wasm.Game.Untyped.Typing

/-!
# Untyped adequacy: well-typed calls, every Core host, the closed program after a call

* `uDiverges_of_no_answer`, `uAdequacy`: for a well-typed export call and a well-formed
  environment, no answer means an infinite product run (progress), so the plain
  strategy reads may-divergence off the absence of answers.
* `responds_ok`: **the instance guarantees the host contract on its exports when its
  environment satisfies it on its imports**: every answer to a well-typed export call is
  a typed store extending the caller's, with a result typed (relative to that store) at
  the declared results.
* `uEnvOk_uOfHost`, `behaviours_eq_uBehavioursOf`: every `HostOk` host is a well-formed
  untyped environment, and the Core behaviours of a well-typed invocation under it are
  its product behaviours. No condition on the host functions a host may add.
* `closed_after_iff`: after an answered call the closed program continues against the
  environment in the host state left by the call.

New proofs; the host part follows `Silmaril.Proofs.Wasm.Game.Shared.Host` without
`HostKeeps`, the last part `Silmaril.Proofs.Wasm.Game.Shared.After`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Untyped

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

variable {U : UInstance} {P : Profile} {L : SEnv UImp}

open Silmaril.Wasm.Game.UInstance

/-! ### Well-typed export calls -/

/-- **No answer is divergence**, for a well-typed export call and a well-formed environment. -/
theorem uDiverges_of_no_answer {f : U.F.Op} {ps rs : Ty (.list .val)} (hq : U.CallOk f ps rs)
    (hL : UEnvOk f.store L) {q : L.S} (hno : ∀ a, ¬ Responds (U.closed P L q) f a) :
    InfiniteTrace (UStep P L) (invoke f.store (U.addr f.target) f.args, q) := by
  refine InfiniteTrace.coinduct
    (fun y => USteps P L (invoke f.store (U.addr f.target) f.args, q) y) ?_
    Relation.ReflTransGen.refl
  intro y run
  have hg : UGood f.store rs.toList y.1 := uGood_uSteps (x := (_, q)) hL (uGood_invoke hq) run
  rcases uGood_progress (P := P) (L := L) y.2 hg.ok with ⟨r, hr⟩ | ⟨y', hy'⟩
  · exact absurd (responds_of_run f run hr) (hno _)
  · exact ⟨y', hy', run.tail hy'⟩

/-- **M2 for the untyped game, plain strategies**: observations of the closed program
together with may-divergence, for a well-typed call and a well-formed environment. -/
theorem uAdequacy {f : U.F.Op} {ps rs : Ty (.list .val)} (hq : U.CallOk f ps rs)
    (hL : UEnvOk f.store L) (q : L.S) :
    uBehavioursOf P L q (invoke f.store (U.addr f.target) f.args) =
      uCompositeObs (U.closed P L q) f ∪
        {b | b = .diverges ∧ InfiniteTrace (UStep P L) (invoke f.store (U.addr f.target) f.args, q)} := by
  ext b
  show (_ ∨ _) ↔ ((_ ∨ _) ∨ _)
  have hfin := mem_finite_iff (P := P) (L := L) f q b
  constructor
  · rintro (h | h)
    · exact .inl (.inl (hfin.1 h))
    · exact .inr h
  · rintro ((h | ⟨hb, hno⟩) | h)
    · exact .inl (hfin.2 h)
    · exact .inr ⟨hb, uDiverges_of_no_answer hq hL hno⟩
    · exact .inr h

/-- The declared results of a function of a typed store are closed types. -/
theorem resultOk_of_callOk {f : U.F.Op} {ps rs : Ty (.list .val)} (hq : U.CallOk f ps rs) :
    ResultOk {} rs.toList := by
  obtain ⟨hs, fi, hfi, hexp, -⟩ := hq
  have hd : TyOk {} fi.type := by
    cases hs.funcs fi (List.mem_of_getElem? hfi) <;> assumption
  exact (Expand.resultOk hd hexp).2

/-- **The instance guarantees the host contract on its exports** (rely: the environment
satisfies it on the imports): an answer to a well-typed export call is a typed store
extending the caller's store and a result typed at the declared results in that store. -/
theorem responds_ok {f : U.F.Op} {ps rs : Ty (.list .val)} (hq : U.CallOk f ps rs)
    (hL : UEnvOk f.store L) {q : L.S} {a : UReply} (h : Responds (U.closed P L q) f a) :
    a.OkFor f.store rs := by
  obtain ⟨c', q', run, final, hstore⟩ := run_of_responds h
  have hg : UGood f.store rs.toList c' := uGood_uSteps (x := (_, q)) hL (uGood_invoke hq) run
  have htyped : ResultTyped c'.store a.result rs.toList :=
    resultTyped_of_final hg.ok (resultOk_of_callOk hq) final
  have hs' : StoreOk c'.store := ConfigOk.storeOk hg.ok
  exact ⟨hstore ▸ hs', hstore ▸ hg.ext, hstore ▸ htyped⟩

/-! ### Every Core host -/

/-- The three kinds of product steps, for any untyped environment. -/
theorem uStep_elim {L : SEnv UImp} {x y : Config Nat × L.S} (h : UStep P L x y) :
    (Step P (fun _ _ _ _ => False) x.1 y.1 ∧ y.2 = x.2) ∨
      (∃ (E : Ctx) (fa hh : Nat) (args : List Val) (a : UReply),
        decompose? x.1.store x.1.code = some (E, fa, hh, args) ∧
        L.Ans x.2 ⟨hh, x.1.store, args⟩ a y.2 ∧ y.1 = ⟨a.store, x.1.frame, E.fill a.result.toAdmin⟩) ∨
      (∃ (E : Ctx) (fa hh : Nat) (args : List Val),
        decompose? x.1.store x.1.code = some (E, fa, hh, args) ∧
        L.Silent x.2 ⟨hh, x.1.store, args⟩ ∧ y = x) := by
  cases h with
  | internal h0 => exact .inl ⟨h0, rfl⟩
  | answer hd ans => exact .inr (.inl ⟨_, _, _, _, _, hd, ans, rfl⟩)
  | silent hd hs => exact .inr (.inr ⟨_, _, _, _, hd, hs, rfl⟩)

/-- **Every `HostOk` host is a well-formed untyped environment**, from every store. -/
theorem uEnvOk_uOfHost {host : HostSemantics Nat} (hok : HostOk host) (s₀ : Store Nat) :
    UEnvOk s₀ (SEnv.uOfHost host) := by
  intro q e a q' ps rs _ ⟨hs, fi, hfi, hcode, hexp, hvs⟩ hans
  exact (hok e.store fi e.target e.args ps rs hs hfi hcode hexp hvs).2 _ hans

/-- **A Core step under any host is a product step** against the host as an environment. -/
theorem core_uStep_ofHost {host : HostSemantics Nat} {c c' : Config Nat}
    (h : Step P host c c') : UStep P (SEnv.uOfHost host) (c, ()) (c', ()) := by
  rcases Step.split_host h with h0 | ⟨E, fa, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · exact .internal h0
  · exact .answer (a := ⟨s', r⟩) hd hr
  · exact .silent hd (.inl hdiv)

/-- A host call with no returned answer diverges under a `HostOk` host, at a typed
configuration. -/
theorem diverged_of_silent (P : Profile) {host : HostSemantics Nat} (hok : HostOk host)
    {c : Config Nat}
    {ts : List CValType} (hc : ConfigOk c ts) {E : Ctx} {fa hh : Nat} {args : List Val}
    (hd : decompose? c.store c.code = some (E, fa, hh, args))
    (hs : (SEnv.uOfHost host).Silent () ⟨hh, c.store, args⟩) :
    host hh c.store args .diverged := by
  rcases hs with hdiv | hno
  · exact hdiv
  · obtain ⟨ps, rs, hcs, fi, hfi, hcode, hexp, hvs⟩ := callsHost_of_decompose P hc hd
    obtain ⟨⟨out, hout⟩, -⟩ := hok c.store fi hh args ps rs hcs hfi hcode hexp hvs
    cases out with
    | diverged => exact hout
    | returned s' r => exact absurd hout (hno ⟨s', r⟩ ())

/-- A product step against a `HostOk` host, from a typed configuration, is a Core step. -/
theorem core_of_uStep_ofHost {host : HostSemantics Nat} (hok : HostOk host)
    {ts : List CValType} {x y : Config Nat × Unit} (hc : ConfigOk x.1 ts)
    (h : UStep P (SEnv.uOfHost host) x y) : Step P host x.1 y.1 := by
  rcases uStep_elim h with ⟨h0, -⟩ | ⟨E, fa, hh, args, a, hd, ans, hy⟩ | ⟨E, fa, hh, args, hd, hs, rfl⟩
  · exact Step.of_noHost host h0
  · rw [hy]
    exact ScalarInstance.step_of_callout_returned hd ans
  · exact ScalarInstance.step_of_callout_diverged hd (diverged_of_silent P hok hc hd hs)

section Runs

variable {host : HostSemantics Nat} (hok : HostOk host) {s₀ : Store Nat} {ts : List CValType}
include hok

/-- Product runs against a `HostOk` host are Core runs, from a typed configuration. -/
theorem steps_of_uSteps {c : Config Nat} {y : Config Nat × Unit} (hg : UGood s₀ ts c)
    (h : USteps P (SEnv.uOfHost host) (c, ()) y) : Steps P host c y.1 := by
  induction h with
  | refl => exact .refl
  | @tail b y hb hst ih =>
    have hgb : UGood s₀ ts b.1 := uGood_uSteps (x := (c, ())) (uEnvOk_uOfHost hok s₀) hg hb
    exact ih.tail (core_of_uStep_ofHost hok hgb.ok hst)

/-- Infinite product runs against a `HostOk` host are infinite Core runs. -/
theorem diverges_of_inf {c : Config Nat} (hg : UGood s₀ ts c)
    (h : InfiniteTrace (UStep P (SEnv.uOfHost host)) (c, ())) :
    InfiniteTrace (Step P host) c := by
  refine InfiniteTrace.coinduct
    (fun c => UGood s₀ ts c ∧ InfiniteTrace (UStep P (SEnv.uOfHost host)) (c, ())) ?_ ⟨hg, h⟩
  rintro c ⟨hgc, hinf⟩
  obtain ⟨⟨c', ⟨⟩⟩, hst, hinf'⟩ := hinf.unfold
  exact ⟨c', core_of_uStep_ofHost hok hgc.ok hst,
    uGood_uStep (x := (c, ())) (uEnvOk_uOfHost hok s₀) hgc hst, hinf'⟩

end Runs

/-- Core runs under any host are product runs. -/
theorem uSteps_of_steps {host : HostSemantics Nat} {c c' : Config Nat} (h : Steps P host c c') :
    USteps P (SEnv.uOfHost host) (c, ()) (c', ()) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (core_uStep_ofHost hst)

/-- Infinite Core runs under any host are infinite product runs. -/
theorem inf_of_diverges {host : HostSemantics Nat} {c : Config Nat}
    (h : InfiniteTrace (Step P host) c) : InfiniteTrace (UStep P (SEnv.uOfHost host)) (c, ()) := by
  refine InfiniteTrace.coinduct (fun x => x.2 = () ∧ InfiniteTrace (Step P host) x.1) ?_ ⟨rfl, h⟩
  rintro ⟨c, ⟨⟩⟩ ⟨-, hinf⟩
  obtain ⟨c', hst, hinf'⟩ := hinf.unfold
  exact ⟨(c', ()), core_uStep_ofHost hst, rfl, hinf'⟩

/-- **The Core behaviours of a well-typed invocation under a `HostOk` host are its product
behaviours** against the host as an untyped environment. -/
theorem behaviours_eq_uBehavioursOf {host : HostSemantics Nat} (hok : HostOk host) {f : U.F.Op}
    {ps rs : Ty (.list .val)} (hq : U.CallOk f ps rs) :
    behaviours P host f.store (U.addr f.target) f.args =
      uBehavioursOf P (SEnv.uOfHost host) () (invoke f.store (U.addr f.target) f.args) := by
  have hg := uGood_invoke hq
  rw [behaviours_eq]
  ext b
  constructor
  · rintro (⟨c', r, run, final, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact .inl ⟨c', (), r, uSteps_of_steps run, final, rfl⟩
    · exact .inr ⟨rfl, inf_of_diverges hdiv⟩
  · rintro (⟨c', q', r, run, final, rfl⟩ | ⟨rfl, hinf⟩)
    · exact .inl ⟨c', r, steps_of_uSteps hok hg run, final, rfl⟩
    · exact .inr ⟨rfl, diverges_of_inf hok hg hinf⟩

/-! ### After an answered call -/

/-- Steps of the composite system do not depend on the initial host state. -/
theorem step_reinit {q : L.S} (q' : L.S) {x y : (Cmp U P L q).State}
    {l : Option (Move Sig.empty U.F)} (h : (Cmp U P L q).step x l y) :
    (Cmp U P L q').step x l y := by
  cases h with
  | tau₁ hk => exact .tau₁ hk
  | tau₂ hi => exact .tau₂ hi
  | left g hk => exact .left g hk
  | right g hi => exact .right g hi
  | sync g hk hi => exact .sync g hk hi

/-- Runs of the composite system do not depend on the initial host state. -/
theorem run_reinit {q : L.S} (q' : L.S) {x y : (Cmp U P L q).State}
    {p : List (Move Sig.empty U.F)} (h : (Cmp U P L q).Run x p y) : (Cmp U P L q').Run x p y := by
  induction h with
  | nil x => exact .nil (L := Cmp U P L q') x
  | tau hs _ ih => exact .tau (step_reinit q' hs) ih
  | vis hs _ ih => exact .vis (step_reinit q' hs) ih

/-- An idle composite state takes no silent step. -/
theorem idle_no_silent {q₀ q : L.S} {x : (Cmp U P L q₀).State}
    (hs : (Cmp U P L q₀).step ((q, none), .idle) none x) : False := by
  cases hs with
  | tau₁ hk => cases hk
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ask q e => cases hi

/-- Silent runs from an idle state stay there. -/
theorem idle_run_nil {q₀ q : L.S} {x y : (Cmp U P L q₀).State} {p : List (Move Sig.empty U.F)}
    (h : (Cmp U P L q₀).Run x p y) (hp : p = []) (hx : x = ((q, none), .idle)) :
    y = ((q, none), .idle) := by
  cases h with
  | nil => exact hx
  | tau hs _ => exact (idle_no_silent (hx ▸ hs)).elim
  | vis _ _ => cases hp

/-- The answer move from a running state goes to the idle state. -/
theorem ans_target_running {q₀ : L.S} (f : U.F.Op) {s : Store Nat} {t : Thread} {q : L.S}
    {a : UReply} {x' : (Cmp U P L q₀).State}
    (hs : (Cmp U P L q₀).step ((q, none), .running f s t) (some (.inr (.ans f a))) x') :
    x' = ((q, none), .idle) := by
  cases hs with
  | right g hi =>
    cases hi with
    | oret => rfl

/-- The answer move from a related state goes to the idle state with the same host state. -/
theorem ans_target {q₀ : L.S} (f : U.F.Op) {cq : Config Nat × L.S} {a : UReply}
    {x x' : (Cmp U P L q₀).State} (hc : URel f cq x)
    (hs : (Cmp U P L q₀).step x (some (.inr (.ans f a))) x') : x' = ((cq.2, none), .idle) := by
  rcases hc with ⟨s, t, hx, -⟩ | ⟨s, t, h, args, hx, -, -⟩
  · rw [hx] at hs
    exact ans_target_running f hs
  · rw [hx] at hs
    exact (not_ans_waiting (q := (some ⟨h, s, args⟩, cq.2)) f hs).elim

/-- A run of the composite reading an answered export call: a product run to the result, the
composite back at the idle state in the final host state. -/
theorem run_answer_inv {f : U.F.Op} {q : L.S} {a : UReply} {y : (Cmp U P L q).State}
    (h : (Cmp U P L q).Run (Cmp U P L q).init [.inr (.ask f), .inr (.ans f a)] y) :
    ∃ (c' : Config Nat) (q' : L.S),
      USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q') ∧
        c'.code = a.result.toAdmin ∧ c'.store = a.store ∧ y = ((q', none), .idle) := by
  obtain ⟨x₁, x₂, hr₁, hs₁, hr₂⟩ := LTS.Run.cons_inv h
  have hx₁ : x₁ = (Cmp U P L q).init := init_run_nil hr₁ rfl rfl
  have hx₂ : x₂ = ((q, none), .running f f.store (U.init f)) := step_ask_inv (hx₁ ▸ hs₁)
  have hc₂ : URel (q₀ := q) f (invoke f.store (U.addr f.target) f.args, q) x₂ :=
    .inl ⟨f.store, U.init f, hx₂, rfl⟩
  obtain ⟨x₃, x₄, hr₃, hs₃, hr₄⟩ := LTS.Run.cons_inv hr₂
  obtain ⟨⟨c', q'⟩, hrun, hc₃⟩ := uSteps_of_run_nil f hr₃ rfl _ hc₂
  obtain ⟨hfinal, hstore⟩ := final_of_step_ans f hc₃ hs₃
  have hy : y = ((q', none), .idle) := idle_run_nil hr₄ rfl (ans_target f hc₃ hs₃)
  exact ⟨c', q', hrun, hfinal, hstore, hy⟩

/-- **The closed program after an answered call** continues as the closed program against the
environment in the host state left by some product run of the call. -/
theorem closed_after_iff {f : U.F.Op} {q : L.S} {a : UReply} (p : List (Move Sig.empty U.F)) :
    [.inr (.ask f), .inr (.ans f a)] ++ p ∈ U.closed P L q ↔
      ∃ (c' : Config Nat) (q' : L.S),
        USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q') ∧
          c'.code = a.result.toAdmin ∧ c'.store = a.store ∧ p ∈ U.closed P L q' := by
  rw [← cmp_denotes P L q]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨xm, hm, hp⟩ := LTS.Run.of_append hy
    obtain ⟨c', q', hrun, hfinal, hstore, rfl⟩ := run_answer_inv hm
    have hp' : (Cmp U P L q').Run (Cmp U P L q').init p y := run_reinit (q := q) q' hp
    exact ⟨c', q', hrun, hfinal, hstore, (cmp_denotes P L q' p).1 ⟨_, hp'⟩⟩
  · rintro ⟨c', q', hrun, hfinal, hstore, hp⟩
    obtain ⟨y, hy⟩ := (cmp_denotes P L q' p).2 hp
    have hy' : (Cmp U P L q).Run ((q', none), .idle) p y := run_reinit (q := q') q hy
    have hrun' := cmp_run_of_run f hrun hfinal
    have ha : (⟨c'.store, a.result⟩ : UReply) = a := by rw [hstore]
    rw [ha] at hrun'
    exact ⟨y, hrun'.append hy'⟩

end Silmaril.Proofs.Wasm.Game.Untyped
