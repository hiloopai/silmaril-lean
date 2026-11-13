module

public import Silmaril.Wasm.Resource.Replay.Defs
public import Silmaril.Wasm.Resource.Check.Thms
public import Silmaril.Wasm.Resource.Link.Thms
public import Silmaril.Wasm.Verify.Refute.Thms
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.Game.Strategy.Thms

/-!
# Replaying environment answers: soundness

Every replay recorded by `replayFrom` from a typed configuration is read off a path of the
instance's transition system (`replayFrom_path`): the interpreter's host-free run is a machine run
(`reach_of_steps'`), its callout an import question (`importOp?_of_typedB`), the scripted answer
an import answer, and the resumed configuration is typed again (silmaril-lean's
`Ctx.fill_callout_typed`, with the answer typed by the host function's result types). Hence a
replay of an export call is a play of `I.strategy P I.store` (`replayExport_play`), and a replay
rejected by a protocol refutes the protocol sentence (`not_models_of_replay`), at every profile
admitting the deterministic steps of the refuter. The client and ownership refuters
(`client_refuted_replay`, `ob_refuted_replay`) follow, at every specification profile.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify
open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## Machine runs -/

/-- A host-free Core run from a thread's configuration is a machine run to a thread denoting the
final configuration. -/
theorem reach_of_steps' {P : Profile} {s : Store Nat} {t : Thread} {d : Config Nat}
    (h : Steps P Det.noHost (t.config s) d) :
    ∃ s' t', Reach P (s, t) (s', t') ∧ t'.config s' = d := by
  induction h with
  | refl => exact ⟨s, t, .refl, rfl⟩
  | @tail c d _ hst ih =>
    obtain ⟨s', t', hr, hc⟩ := ih
    refine ⟨d.store, .active d.frame d.code, .tail hr ⟨d.frame, d.code, rfl, ?_⟩, rfl⟩
    rw [hc]
    exact hst

/-- Scalar typing of values is Core typing. -/
theorem forall₂_valOk {s : Store Nat} : ∀ {ts : List ScalarType} {vs : List Val},
    List.Forall₂ ScalarType.HasVal ts vs → List.Forall₂ (ValOk s) vs (ts.map ScalarType.toC)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons ((ScalarType.hasVal_iff_valOk s _ _).1 h) (forall₂_valOk t)

theorem resultsOk_sound {ft? : Option FnType} {vs : List Val} (h : resultsOk ft? vs = true) :
    ∃ ft, ft? = some ft ∧ List.Forall₂ ScalarType.HasVal ft.results vs := by
  cases ft? with
  | none => cases h
  | some ft => exact ⟨ft, rfl, typedB_sound h⟩

theorem argsOk_sound {I : ScalarInstance} {h : Nat} {args : List Val}
    (hok : argsOk I h args = true) :
    ∃ hi : h < I.imports.length, typedB (I.imports.get ⟨h, hi⟩).params args = true := by
  unfold argsOk at hok
  split at hok
  · rename_i ft hft
    obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.1 hft
    exact ⟨hi, by simpa [hget] using hok⟩
  · cases hok

/-- Resuming at a callout redex plugs the result into its context. -/
theorem resumeResult_of_decompose {s : Store Nat} {t : Thread} {E : Ctx} {a h : Nat}
    {args : List Val} (hd : decompose? s (t.config s).code = some (E, a, h, args)) (r : Result) :
    resumeResult s t r = .active (t.config s).frame (E.fill r.toAdmin) := by
  simp only [resumeResult, hd]

/-- Plugging values typed by the callee's result types into a typed callout context gives a
typed configuration. -/
theorem fill_typed {s : Store Nat} {f : Frame} {code : List Admin} {ts : List CValType}
    (hok : ConfigOk ⟨s, f, code⟩ ts) {E : Ctx} {a h : Nat} {args vs : List Val}
    (hd : decompose? s code = some (E, a, h, args)) {ft : FnType}
    (hft : funcType? s a = some ft) (hvs : List.Forall₂ ScalarType.HasVal ft.results vs) :
    ConfigOk ⟨s, f, E.fill (vals vs)⟩ ts := by
  obtain ⟨fi, yy, ps, rs, hfi, -, hyy, hexp, hn, hcode⟩ := decompose?_sound hd
  have hft' : FnType.ofDefType? fi.type = some ft := by
    simpa [funcType?, hfi] using hft
  have heq := Expand.func_eq hexp (FnType.expand_of_ofDefType? hft')
  simp only [FnType.toComp, Ty.func.injEq] at heq
  obtain ⟨-, rfl⟩ := heq
  have hs := ConfigOk.storeOk hok
  refine Ctx.fill_callout_typed (hcode ▸ hok) hfi hexp hyy hn hs (Extend.refl hs) ?_
  rw [Ty.toList_ofList]
  exact forall₂_valOk hvs

/-! ## Replays are paths -/

variable {I : ScalarInstance}

/-- A move of the instance read with plain indices. -/
abbrev rmv (m : Move I.E I.F) : RMove := RMove.ofEvent (moveEvent (X := ifaceOf I) m)

theorem rmv_ask (e : I.E.Op) : rmv (I := I) (.inl (.ask e)) = .ask e.1.val e.2.1 := rfl

theorem rmv_ans (e : I.E.Op) (v : I.E.Ar e) :
    rmv (I := I) (.inl (.ans e v)) = .ans e.1.val (Answer.toBehaviour (ft := I.imports.get e.1) v) :=
  rfl

/-- **A replay is a path**: from a typed running state, the moves recorded by `replayFrom` are
read off a path of the transition system, every profile admitting the refuter's steps. -/
theorem replayFrom_path {sc : Script} {fuel : Nat} {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (f : I.F.Op) : ∀ (n k : Nat) (s : Store Nat) (t : Thread) (ts : List CValType),
      ConfigOk (t.config s) ts → ∃ (ms : List (Move I.E I.F)) (q : I.HState),
        I.Path P (.running f s t) ms q ∧ ms.map rmv = replayFrom I sc fuel n k (t.config s)
  | 0, _, _, _, _, _ => ⟨[], _, .nil _, by simp [replayFrom]⟩
  | n + 1, k, s, t, ts, hok => by
    cases hr : runTo? fuel (t.config s) with
    | none => exact ⟨[], _, .nil _, by simp [replayFrom, hr]⟩
    | some x =>
      obtain ⟨⟨ds, df, dc⟩, E, a, h, args⟩ := x
      obtain ⟨y, hdec, hy⟩ := Option.map_eq_some_iff.1 hr
      simp only [Prod.mk.injEq] at hy
      obtain ⟨hrun, rfl⟩ := hy
      have hdec' : decompose? ds dc = some (E, a, h, args) := by rw [hrun] at hdec; exact hdec
      have hsteps := Exec.runI_steps_typed (o := refOracle) fuel hok
      have hokd := Exec.runI_typed (o := refOracle) fuel hok
      rw [hrun] at hsteps hokd
      obtain ⟨s', t', hreach, hcfg⟩ := reach_of_steps' (Relation.ReflTransGen.mono hP _ _ hsteps)
      have hs' : s' = ds := by rw [← Thread.config_store s' t', hcfg]
      subst hs'
      have hco : CalloutAt s' t' h args := ⟨E, a, by rw [hcfg]; exact hdec'⟩
      by_cases hargs : argsOk I h args = true
      · obtain ⟨hi, hty⟩ := argsOk_sound hargs
        obtain ⟨e, he, he1, he2⟩ := importOp?_of_typedB hi hty
        have hev : e.1.val = h := by rw [he1]
        have step₁ : I.Trans P (.running f s t) (.inl (.ask e)) (.waiting f s' t' e) :=
          .ucall hreach hco he
        by_cases hans : ansOk I s' a h (sc k h args) = true
        · simp only [ansOk, Bool.and_eq_true] at hans
          obtain ⟨⟨ft, hft, hvs⟩, ⟨ft', hft', hvs'⟩⟩ :=
            And.intro (resultsOk_sound hans.1) (resultsOk_sound hans.2)
          have hget : I.imports.get e.1 = ft := by
            rw [he1]
            exact (List.getElem?_eq_some_iff.1 hft).2
          let v : I.E.Ar e := .values ⟨sc k h args, hget ▸ hvs⟩
          have hres : resumeResult s' t' (Answer.toResult (ft := I.imports.get e.1) v) =
              .active df (E.fill (vals (sc k h args))) := by
            rw [resumeResult_of_decompose (by rw [hcfg]; exact hdec'), hcfg]
            rfl
          have hokr : ConfigOk ⟨s', df, E.fill (vals (sc k h args))⟩ ts :=
            fill_typed hokd hdec' hft' hvs'
          obtain ⟨ms, q, hp, hms⟩ := replayFrom_path hP f n (k + 1) s'
            (.active df (E.fill (vals (sc k h args)))) ts hokr
          have step₂ : I.Trans P (.waiting f s' t' e) (.inl (.ans e v))
              (.running f s' (.active df (E.fill (vals (sc k h args))))) := by
            have := ScalarInstance.Trans.uret (P := P) (f := f) (s := s') (t := t') v
            rwa [hres] at this
          refine ⟨.inl (.ask e) :: .inl (.ans e v) :: ms, q, .cons step₁ (.cons step₂ hp), ?_⟩
          simp only [replayFrom, hr, hargs, ↓reduceIte, List.map_cons, hms, ansOk, hans.1, hans.2,
            Bool.and_self, rmv_ask, rmv_ans, hev, he2]
          rfl
        · refine ⟨[.inl (.ask e)], _, .cons step₁ (.nil _), ?_⟩
          simp only [replayFrom, hr, hargs, ↓reduceIte, hans, Bool.false_eq_true,
            List.map_cons, List.map_nil, rmv_ask, hev, he2]
      · exact ⟨[], _, .nil _, by simp [replayFrom, hr, hargs]⟩

/-- **A replay of an export call is a play** of the instance's strategy. -/
theorem replayExport_play (hw : I.Ok) {sc : Script} {fuel n : Nat} {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (j : Fin I.exports.length) (k : Nat) :
    ∃ ms ∈ I.strategy P I.store, ms.map rmv = replayExport I sc fuel n j k := by
  let w : Typed (I.exports.get j).params :=
    ⟨candArgs k (I.exports.get j).params, candArgs_typed k _⟩
  have hinv : InvokeOk I.store (I.addr j) w.1 := invokeOk_of_wellFormed hw j w
  obtain ⟨-, -, rs, -, -, hok⟩ := invoke_ok hw.storeOk hinv
  obtain ⟨ms, q, hp, hms⟩ := replayFrom_path (sc := sc) (fuel := fuel) hP ⟨j, w⟩ n 0 I.store
    (I.initThread ⟨j, w⟩) _ hok
  refine ⟨.inr (.ask ⟨j, w⟩) :: ms, ScalarInstance.mem_strategy_iff.2 ⟨q, .cons (.call _ _) hp⟩, ?_⟩
  rw [List.map_cons, hms]
  rfl

/-- **A flagged replay is a play** of the instance's strategy. -/
theorem replayRefute_play (hw : I.Ok) {sc : Script} {fuel n : Nat} {bad : List RMove → Bool}
    {rs : List RMove} (h : replayRefute I sc fuel n bad = some rs) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    bad rs = true ∧ ∃ ms ∈ I.strategy P I.store, ms.map rmv = rs := by
  refine ⟨List.find?_some h, ?_⟩
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 (List.mem_of_find?_eq_some h)
  rcases List.mem_pair.1 hj with rfl | rfl
  · exact replayExport_play hw hP j 0
  · exact replayExport_play hw hP j 1

/-! ## Refutations -/

/-- **Refutation by a replay** (every profile admitting the refuter's steps): a replay rejected
by the protocol `pr`, read through a classifier `c` that factors through `RMove.ofEvent`. -/
theorem not_models_of_replay {S α : Type} (pr : Protocol S α) (c : WEvent (ifaceOf I) → α)
    (cN : RMove → α) (hc : ∀ e, c e = cN (RMove.ofEvent e)) (hw : I.Ok) {sc : Script}
    {fuel n : Nat} {bad : List RMove → Bool}
    (hbad : ∀ rs, bad rs = true → pr.acceptsB (rs.map cN) = false)
    (h : (replayRefute I sc fuel n bad).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) S) (wasmSem P)
      (WasmProg.ofInstance I) (pr.comap c) := by
  obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨hb, ms, hms, hmap⟩ := replayRefute_play hw hrs hP
  refine not_models_of_play (WasmProg.ofInstance I) _ hms ?_
  have hev : ∀ l : List (Move I.E I.F), (l.map moveEvent).map c = (l.map rmv).map cN := by
    intro l
    induction l with
    | nil => rfl
    | cons m l ih => exact congrArg₂ List.cons (hc _) ih
  simp only [Protocol.acceptsB, Protocol.run_comap, hev, hmap]
  exact hbad rs hb

theorem clientEv_eq {X : WIface} (ia iu if_ : X.Imp) (e : WEvent X) :
    clientEv ia iu if_ e = clientEvN ia.val iu.val if_.val (RMove.ofEvent e) := by
  rcases e with (⟨i, a⟩ | ⟨i, b⟩) | (⟨j, a⟩ | ⟨j, b⟩) <;>
    simp [clientEv, clientEvN, RMove.ofEvent, Fin.ext_iff]

theorem obEv_eq {X : WIface} (r : NRoles) (e : WEvent X) :
    obEv (r.toOB (X := X)) e = obEvN r (RMove.ofEvent e) := by
  rcases e with (⟨i, a⟩ | ⟨i, b⟩) | (⟨j, a⟩ | ⟨j, b⟩) <;>
    simp [obEv, obEvN, RMove.ofEvent, NRoles.toOB] <;> rfl

/-- **Client refutation by a replay on an instance**, every profile admitting the refuter's
steps. -/
theorem client_refuted_replay_inst (hw : I.Ok) {ia iu if_ : (ifaceOf I).Imp} {sc : Script}
    {fuel n : Nat} (h : (replayRefute I sc fuel n (clientBad ia.val iu.val if_.val)).isSome = true)
    {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (WasmProg.ofInstance I) (clientSpec ia iu if_) :=
  not_models_of_replay (handleProto Val .client) _ _ (clientEv_eq ia iu if_) hw
    (fun rs hb => by simpa [clientBad] using hb) h hP

/-- **Ownership refutation by a replay on an instance**, every profile admitting the refuter's
steps. -/
theorem ob_refuted_replay_inst (hw : I.Ok) (r : NRoles) {sc : Script} {fuel n : Nat}
    (h : (replayRefute I sc fuel n (obBad r)).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode))))
      (wasmSem P) (WasmProg.ofInstance I) (obSpec (X := ifaceOf I) r.toOB) :=
  not_models_of_replay (obProto Val) _ _ (obEv_eq r) hw
    (fun rs hb => by simpa [obBad] using hb) h hP

/-- **Client refutation by a replay on a module** (every specification profile): the replay
refuter finds an export call whose play, with the client script answering, is rejected by the
client sentence (use after free, double free, use or free of a never-allocated handle). -/
theorem client_refuted_replay {m : Module} (hm : (instance? m).isSome = true)
    {ia iu if_ : (ifaceOf (instOf m)).Imp} {n : Nat}
    (h : (clientReplay? m ia.val iu.val if_.val n).isSome = true) (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val)))
      (wasmSem (Profile.spec nd {})) (progOf m) (clientSpec ia iu if_) := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  exact client_refuted_replay_inst hI.ok h fun _ _ hs => Step.deterministic_refines_spec nd hs

/-- **Ownership refutation by a replay on a module** (every specification profile). -/
theorem ob_refuted_replay {m : Module} (hm : (instance? m).isSome = true) (r : NRoles) {n : Nat}
    (h : (obReplay? m r n).isSome = true) (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode))))
      (wasmSem (Profile.spec nd {})) (progOf m) (obSpec (X := ifaceOf (instOf m)) r.toOB) := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  exact ob_refuted_replay_inst hI.ok r h fun _ _ hs => Step.deterministic_refines_spec nd hs

end Silmaril.Wasm.Resource
