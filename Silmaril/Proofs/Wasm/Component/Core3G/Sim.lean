module

public import Silmaril.Proofs.Wasm.Component.Core3G.Bridge
public import Silmaril.Proofs.Wasm.Component.Reference.CallTyping
public import Silmaril.Proofs.Wasm.Component.Reference.CoreRun
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Games.LTS.Thms

/-!
# The engine semantics of `core3P P` is `modSem P`: the runtime simulation

Proofs for `Silmaril.Wasm.Component.Core3G.Thms` (`engineSem_eq_modSem`).

A numeric module with an instance `I` (`NumModule.IsInst`) has no imports, and its `modSem P`
strategy is the composite `ofHandler importH ∘ I.strategy P I.store ∘ ofHandler exportH`. The
composite is denoted by the parallel composition `LC` of the three transition systems
(`LTS.Denotes.comp`). When the engine instance of the module is `I` (`SameInst`), the engine
transition system `engineLTS` and `LC` simulate each other:

* `simEC` (engine to composite): an engine call is the export handler's question followed by the
  hidden instance call; an engine answer is the hidden instance answer followed by the handler's
  answer. The instance answer exists because returned values are typed (type soundness of the
  instance, `ScalarInstance.answer_of_run`, kept along the run by `wellFormed_after_run`).
* `simCE` (composite to engine): the composite's hidden steps are matched by no engine step; the
  answer the composite commits to at its hidden instance answer is recorded in the relation
  (`R2.answering`) and played by the engine at the visible answer.

The import handler never moves (the module has no imports), and neither does any import event of
the instance (its import signature is empty).
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Core3G

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Game (ScalarInstance InternalP Reach ResultAt statusP)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Result vals throwing)
open Silmaril.Wasm.SingleThreaded (Thread ofFlat toFlat?)

/-! ## The status of finished threads -/

section Status

variable {H : Type} {P : Profile} {s : Silmaril.Wasm.Execution.Core.Store H} {t : Thread}

theorem not_vals_trap : ¬ ∃ vs, ([.trap] : List Silmaril.Wasm.Execution.Core.Admin) = vals vs := by
  rintro ⟨vs, h⟩
  have h' := congrArg Silmaril.Wasm.SingleThreaded.splitVals h
  rw [Silmaril.Wasm.SingleThreaded.splitVals_vals] at h'
  simp [Silmaril.Wasm.SingleThreaded.splitVals, Silmaril.Wasm.Execution.Core.Admin.val?] at h'

theorem not_vals_throwing (a : Nat) : ¬ ∃ vs, throwing a = vals vs := by
  rintro ⟨vs, h⟩
  have h' := congrArg Silmaril.Wasm.SingleThreaded.splitVals h
  rw [Silmaril.Wasm.SingleThreaded.splitVals_vals] at h'
  simp [Silmaril.Wasm.SingleThreaded.splitVals, Silmaril.Wasm.Execution.Core.Admin.val?] at h'

theorem statusP_of_values {vs : List Silmaril.Wasm.Execution.Core.Val}
    (h : (t.config s).code = vals vs) : statusP P s t = .returned (.values vs) := by
  have hex : ∃ vs, (t.config s).code = vals vs := ⟨vs, h⟩
  unfold statusP
  rw [dite_eq_left hex, Silmaril.Wasm.SingleThreaded.vals_injective (hex.choose_spec.symm.trans h)]

theorem statusP_of_trap (h : (t.config s).code = [.trap]) : statusP P s t = .returned .trap := by
  have h1 : ¬ ∃ vs, (t.config s).code = vals vs := h ▸ not_vals_trap
  unfold statusP
  rw [dite_eq_right h1, ite_eq_left h]

theorem statusP_of_throwing {a : Nat} (h : (t.config s).code = throwing a) :
    statusP P s t = .returned .trap := by
  have h1 : ¬ ∃ vs, (t.config s).code = vals vs := h ▸ not_vals_throwing a
  have h2 : (t.config s).code ≠ [.trap] := by rw [h]; simp [throwing]
  unfold statusP
  rw [dite_eq_right h1, ite_eq_right h2, ite_eq_left ⟨a, h⟩]

end Status

/-! ## Flat views of typed values -/

theorem toFlat?_isSome : ∀ {ts : List Silmaril.Wasm.NumType} {vs : List Silmaril.Wasm.Execution.Core.Val},
    List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (ts.map .num) vs →
      ∃ ys, vs.mapM toFlat? = some ys
  | [], [], _ => ⟨[], rfl⟩
  | t :: ts, v :: vs, .cons ⟨bits, hv⟩ hr => by
    subst hv
    obtain ⟨ys, hys⟩ := toFlat?_isSome hr
    exact ⟨⟨t, bits⟩ :: ys, by simp only [List.mapM_cons, toFlat?, hys]; rfl⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem hasVal_of_flatTyped {ps : List Silmaril.Wasm.NumType} {xs : List Flat}
    (h : FlatTyped ps xs) :
    List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (ps.map .num) (xs.map ofFlat) := by
  have hps : ps.map Silmaril.Wasm.Game.ScalarType.num = xs.map fun x => .num x.type := by
    rw [← show xs.map (·.type) = ps from h, List.map_map]
    rfl
  rw [hps]
  exact Silmaril.Proofs.Wasm.Component.Reference.forall₂_hasVal_ofFlat xs

/-- `typed?` on typed values. -/
theorem typed?_of {ts : List Silmaril.Wasm.Game.ScalarType} {vs : List Silmaril.Wasm.Execution.Core.Val}
    (h : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal ts vs) : typed? ts vs = some ⟨vs, h⟩ :=
  dite_eq_left h

/-! ## The instance -/

section Inst

variable {P : Profile} {m : NumModule} {I : ScalarInstance}

/-- The instance has no import operations. -/
theorem imp_empty (hI : m.IsInst I) (e : (Silmaril.Wasm.Game.ifaceSig I.imports).Op) : False :=
  absurd e.1.isLt (by simp [hI.2.1])

/-- The instance has no import events. -/
theorem ev_empty (hI : m.IsInst I) (e : Ev (Silmaril.Wasm.Game.ifaceSig I.imports)) : False := by
  cases e with
  | ask e => exact imp_empty hI e
  | ans e _ => exact imp_empty hI e

/-- The continuation of the export handler after the instance call. -/
@[expose] def kAns (f : I.F.Op) : I.F.Ar f → Prog I.F (Option Payload) :=
  fun a => .pure (answerPayload a)

/-- The parameter types of the instance's export `j`. -/
theorem params_eq (hI : m.IsInst I) (j : Fin m.exports.length) :
    (I.exports.get (Fin.cast (numInst hI).exports_length j)).params =
      (m.exports[j].2.params).map .num := by
  simp only [numInst, List.get_eq_getElem, hI.2.2, List.getElem_map, fnOf]
  rfl

/-- The result types of the instance's exports are numeric. -/
theorem results_eq (hI : m.IsInst I) (j : Fin I.exports.length) :
    ∃ ts : List Silmaril.Wasm.NumType, (I.exports.get j).results = ts.map .num := by
  have hmem : I.exports.get j ∈ m.exports.map fun p => fnOf p.2 :=
    Eq.mp (congrArg (I.exports.get j ∈ ·) hI.2.2) (List.get_mem I.exports j)
  obtain ⟨p, -, hp⟩ := List.mem_map.1 hmem
  exact ⟨p.2.results, by rw [← hp]; rfl⟩

/-- A question with a callee is an instance call of the export handler, starting the engine's
thread. -/
theorem exportH_of_callee (hI : m.IsInst I) {q : (sigN m.exports.length).Op} {a : Nat} {xs : List Flat}
    (hc : callee? (E := core3P P) I.addrs m.exports q = some (a, xs)) :
    ∃ f : I.F.Op, exportH (numInst hI) q = .call f (kAns f) ∧
      I.initThread f = Thread.invokeFlat a xs := by
  obtain ⟨j, pl⟩ := q
  cases pl with
  | vals _ => cases hc
  | flat xs' =>
    have hty : FlatTyped m.exports[j].2.params xs' := by
      by_contra hn
      simp only [callee?, hn, ite_false] at hc
      cases hc
    have hc' : (I.addrs[j.1]?).map (fun a => (a, xs')) = some (a, xs) := by
      simp only [callee?, hty, ite_true] at hc
      exact hc
    obtain ⟨a', ha, he⟩ := Option.map_eq_some_iff.1 hc'
    obtain ⟨h1, h2⟩ := Prod.mk.inj he
    subst a' xs
    have hv := hasVal_of_flatTyped hty
    rw [← params_eq hI j] at hv
    refine ⟨⟨Fin.cast (numInst hI).exports_length j, ⟨xs'.map ofFlat, hv⟩⟩, ?_, ?_⟩
    · have ht : typed? ((numInst hI).inst.exports.get (Fin.cast (numInst hI).exports_length j)).params
          (xs'.map ofFlat) = some ⟨_, hv⟩ := typed?_of hv
      simp only [exportH, ht]
      rfl
    · show Thread.pending (I.addrs.getD j.1 0) (xs'.map ofFlat) = Thread.pending a (xs'.map ofFlat)
      rw [List.getD_eq_getElem?_getD, ha]
      rfl

/-- A question without a callee is answered at once by a trap by the export handler. -/
theorem exportH_of_no_callee (hI : m.IsInst I) (hw : I.addrs.length = I.exports.length)
    {q : (sigN m.exports.length).Op}
    (hc : callee? (E := core3P P) I.addrs m.exports q = none) :
    exportH (numInst hI) q = .pure none := by
  apply exportH_ill hI
  intro xs hq hty
  obtain ⟨j, pl⟩ := q
  subst hq
  have hj : j.1 < I.addrs.length := by
    rw [hw, hI.2.2, List.length_map]
    exact j.2
  have hc' : (I.addrs[j.1]?).map (fun a => (a, xs)) = none := by
    simp only [callee?, hty, ite_true] at hc
    exact hc
  exact absurd (List.getElem?_eq_none_iff.1 (Option.map_eq_none_iff.1 hc')) (Nat.not_le.2 hj)

end Inst


/-! ## Answers -/

section Answers

variable {P : Profile} {m : NumModule} {I : ScalarInstance}

/-- The engine status of a finished thread for the answer payload `r`: a trap for `none`, the
flat values `ys` for `some (.flat ys)`. -/
@[expose] def Answers (P : Profile) (s : Silmaril.Wasm.Execution.Core.Store Nat) (t : Thread)
    (r : Option Payload) : Prop :=
  (r = none ∧ (core3P P).status s t = .returned .trap) ∨
    ∃ ys, r = some (.flat ys) ∧ (core3P P).status s t = .returned (.values ys)

/-- The answer payload of typed values. -/
theorem answerPayload_values {ft : Silmaril.Wasm.Game.FnType}
    {vs : List Silmaril.Wasm.Execution.Core.Val} {v : Silmaril.Wasm.Game.Answer ft}
    (hv : Silmaril.Wasm.Game.Answer.ofResult? ft (.values vs) = some v) :
    answerPayload v = (vs.mapM toFlat?).map .flat := by
  unfold Silmaril.Wasm.Game.Answer.ofResult? at hv
  dsimp only at hv
  split_ifs at hv with ht
  cases hv
  rfl

/-- A returned value thread answers its flat values. -/
theorem answers_values {s : Silmaril.Wasm.Execution.Core.Store Nat} {t : Thread}
    {vs : List Silmaril.Wasm.Execution.Core.Val} {ys : List Flat}
    (final : (t.config s).code = vals vs) (hys : vs.mapM toFlat? = some ys) :
    Answers P s t ((vs.mapM toFlat?).map .flat) := by
  refine .inr ⟨ys, by rw [hys]; rfl, ?_⟩
  show flatStatus (statusP P s t) = _
  rw [statusP_of_values final]
  simp only [flatStatus, hys]

/-- The instance answer read off a finished thread is the engine status of the thread. -/
theorem answers_of_result (hI : m.IsInst I) {f : I.F.Op}
    {s : Silmaril.Wasm.Execution.Core.Store Nat} {t : Thread} {r : Result} {v : I.F.Ar f}
    (final : ResultAt s t r) (hv : Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) r = some v) :
    Answers P s t (answerPayload v) := by
  cases r with
  | values vs =>
    have ht : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (I.exports.get f.1).results vs := by
      unfold Silmaril.Wasm.Game.Answer.ofResult? at hv
      dsimp only at hv
      split_ifs at hv with ht
      exact ht
    obtain ⟨ts, hts⟩ := results_eq hI f.1
    obtain ⟨ys, hys⟩ := toFlat?_isSome (hts ▸ ht)
    rw [answerPayload_values hv]
    exact answers_values final hys
  | trap =>
    cases hv
    exact .inl ⟨rfl, show flatStatus _ = _ by rw [statusP_of_trap final]; rfl⟩
  | throw a =>
    cases hv
    exact .inl ⟨rfl, show flatStatus _ = _ by rw [statusP_of_throwing final]; rfl⟩

/-- The answer payload of an engine call result. -/
@[expose] def payloadOf : Silmaril.Wasm.Component.Engine.CallResult → Option Payload
  | .values ys => some (.flat ys)
  | .trap => none

/-- The engine status of a finished run is the answer of a Core result. -/
theorem result_of_status {s : Silmaril.Wasm.Execution.Core.Store Nat} {t : Thread}
    {res : Silmaril.Wasm.Component.Engine.CallResult}
    (h : (core3P P).status s t = .returned res) :
    ∃ r : Result, ResultAt s t r ∧ ∀ {ft : Silmaril.Wasm.Game.FnType} {v : Silmaril.Wasm.Game.Answer ft},
      Silmaril.Wasm.Game.Answer.ofResult? ft r = some v →
        answerPayload v = payloadOf res := by
  cases res with
  | values ys =>
    obtain ⟨vs, hcode, hm⟩ := Silmaril.Proofs.Wasm.Component.Reference.status_values h
    refine ⟨.values vs, hcode, fun hv => ?_⟩
    rw [answerPayload_values hv, hm]
    rfl
  | trap =>
    rcases Silmaril.Proofs.Wasm.Component.Reference.status_trap h with hc | ⟨a, hc⟩
    · exact ⟨.trap, hc, fun hv => by cases hv; rfl⟩
    · exact ⟨.throw a, hc, fun hv => by cases hv; rfl⟩

end Answers

/-! ## The two transition systems -/

section Systems

variable (P : Profile) {m : NumModule} {I : ScalarInstance} (hI : m.IsInst I)

/-- The transition system of the export handler. -/
noncomputable abbrev LX : LTS I.F (sigN m.exports.length) := (exportH (numInst hI)).toReduction.toLTS

/-- The transition system of the instance below its export handler. -/
noncomputable abbrev LM : LTS (Silmaril.Wasm.Game.ifaceSig I.imports) (sigN m.exports.length) :=
  (I.lts P I.store).comp (LX hI)

/-- **The transition system of the `modSem` composite**: import handler, instance, export
handler. -/
noncomputable abbrev LC : LTS (sigN 0) (sigN m.exports.length) :=
  (importH (numInst hI)).toReduction.toLTS.comp (LM P hI)

/-- The engine transition system of the instance. -/
noncomputable abbrev LE (P : Profile) (m : NumModule) (I : ScalarInstance) :
    LTS (sigN 0) (sigN m.exports.length) :=
  engineLTS (core3P P) ⟨I.store, I.addrs⟩ [] m.exports

/-- The composite denotes `modSem P`. -/
theorem lc_denotes : (LC P hI).Denotes ((modSem P).sem m) := by
  rw [modSem_eq_of_isInst P hI]
  exact LTS.Denotes.comp (Handler.denotes_toLTS _)
    (LTS.Denotes.comp (ScalarInstance.denotes P _) (Handler.denotes_toLTS _))

end Systems

/-! ## Steps of the composite -/

section Steps

variable {P : Profile} {m : NumModule} {I : ScalarInstance} {hI : m.IsInst I}

/-- The export question. -/
theorem lc_ask (s : Silmaril.Wasm.Execution.Core.Store Nat) (q : (sigN m.exports.length).Op) :
    (LC P hI).step (.idle, (.idle s, .idle)) (some (.inr (.ask q)))
      (.idle, (.idle s, .run q (exportH (numInst hI) q))) :=
  .right _ (.right _ (Reduction.Step.ask q))

/-- The hidden instance call. -/
theorem lc_call {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
    {f : I.F.Op} {k : I.F.Ar f → Prog I.F (Option Payload)}
    (hk : exportH (numInst hI) q = .call f k) :
    (LC P hI).step (.idle, (.idle s, .run q (exportH (numInst hI) q))) none
      (.idle, (.running f s (I.initThread f), .wait q f k)) :=
  .tau₂ (.sync (.ask f) ⟨_, rfl, .call s f⟩ (Reduction.Step.call hk))

/-- The hidden instance answer. -/
theorem lc_oret {s s' : Silmaril.Wasm.Execution.Core.Store Nat} {t t' : Thread}
    {q : (sigN m.exports.length).Op} {f : I.F.Op} {k : I.F.Ar f → Prog I.F (Option Payload)}
    {r : Result} {v : I.F.Ar f} (run : Reach P (s, t) (s', t')) (final : ResultAt s' t' r)
    (hv : Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) r = some v) :
    (LC P hI).step (.idle, (.running f s t, .wait q f k)) none (.idle, (.idle s', .run q (k v))) :=
  .tau₂ (.sync (.ans f v) ⟨_, rfl, .oret run final hv⟩ (Reduction.Step.resume (R := (exportH (numInst hI)).toReduction) q f k v))

/-- The export answer. -/
theorem lc_ret (s : Silmaril.Wasm.Execution.Core.Store Nat) (q : (sigN m.exports.length).Op)
    (r : Option Payload) :
    (LC P hI).step (.idle, (.idle s, .run q (.pure r))) (some (.inr (.ans q r)))
      (.idle, (.idle s, .idle)) :=
  .right _ (.right _ (Reduction.Step.ret rfl))

/-- The import handler never moves. -/
theorem lc_inv {y : (LM P hI).State} {l : Option (Move (sigN 0) (sigN m.exports.length))}
    {z : (LC P hI).State} (h : (LC P hI).step (.idle, y) l z) :
    ∃ y', z = (.idle, y') ∧ ((l = none ∧ (LM P hI).step y none y') ∨
      ∃ g, l = some (.inr g) ∧ (LM P hI).step y (some (.inr g)) y') := by
  cases h with
  | tau₁ h => cases h
  | tau₂ h => exact ⟨_, rfl, .inl ⟨rfl, h⟩⟩
  | left e h => cases h
  | right g h => exact ⟨_, rfl, .inr ⟨g, rfl, h⟩⟩
  | sync f h₁ h₂ =>
    cases h₁ with
    | ask e => exact (imp_empty hI e).elim

/-- From an idle instance and handler: the export question. -/
theorem lm_idle_inv {s : Silmaril.Wasm.Execution.Core.Store Nat}
    {l : Option (Move (Silmaril.Wasm.Game.ifaceSig I.imports) (sigN m.exports.length))}
    {y : (LM P hI).State} (h : (LM P hI).step (.idle s, .idle) l y) :
    ∃ q, l = some (.inr (.ask q)) ∧ y = (.idle s, .run q (exportH (numInst hI) q)) := by
  cases h with
  | tau₁ h => obtain ⟨_, h, -⟩ := h; cases h
  | tau₂ h => cases h
  | left e h => exact (ev_empty hI e).elim
  | right g h =>
    cases h with
    | ask q => exact ⟨q, rfl, rfl⟩
  | sync f h₁ h₂ => cases h₂

/-- From an idle instance and a running handler: the hidden instance call, or the export
answer. -/
theorem lm_run_inv {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
    {c : Prog I.F (Option Payload)}
    {l : Option (Move (Silmaril.Wasm.Game.ifaceSig I.imports) (sigN m.exports.length))}
    {y : (LM P hI).State} (h : (LM P hI).step (.idle s, .run q c) l y) :
    (∃ f k, c = .call f k ∧ l = none ∧ y = (.running f s (I.initThread f), .wait q f k)) ∨
      ∃ r, c = .pure r ∧ l = some (.inr (.ans q r)) ∧ y = (.idle s, .idle) := by
  cases h with
  | tau₁ h => obtain ⟨_, h, -⟩ := h; cases h
  | tau₂ h => cases h with | tau h => exact h.elim
  | left e h => exact (ev_empty hI e).elim
  | right g h =>
    cases h with
    | ret hr => exact .inr ⟨_, hr, rfl, rfl⟩
  | sync f h₁ h₂ =>
    obtain ⟨_, h, ht⟩ := h₁
    cases h
    cases ht
    cases h₂ with
    | call hk => exact .inl ⟨_, _, hk, rfl, rfl⟩

/-- From a running instance and a waiting handler: the hidden instance answer. -/
theorem lm_wait_inv {s : Silmaril.Wasm.Execution.Core.Store Nat} {t : Thread}
    {q : (sigN m.exports.length).Op} {f : I.F.Op} {k : I.F.Ar f → Prog I.F (Option Payload)}
    {l : Option (Move (Silmaril.Wasm.Game.ifaceSig I.imports) (sigN m.exports.length))}
    {y : (LM P hI).State} (h : (LM P hI).step (.running f s t, .wait q f k) l y) :
    ∃ s' t' r v, Reach P (s, t) (s', t') ∧ ResultAt s' t' r ∧
      Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) r = some v ∧ l = none ∧
      y = (.idle s', .run q (k v)) := by
  cases h with
  | tau₁ h => obtain ⟨_, h, -⟩ := h; cases h
  | tau₂ h => cases h
  | left e h => exact (ev_empty hI e).elim
  | right g h => cases h
  | sync f' h₁ h₂ =>
    obtain ⟨_, h, ht⟩ := h₁
    cases h
    cases h₂ with
    | resume => cases ht with
      | oret run final hv => exact ⟨_, _, _, _, run, final, hv, rfl, rfl⟩

end Steps

/-! ## Engine to composite -/

section EC

variable {P : Profile} {m : NumModule} {I : ScalarInstance} {hI : m.IsInst I}

/-- The thread of an export call runs from a typed invocation at a well-formed store. -/
@[expose] def RunInv (P : Profile) (I : ScalarInstance) (f : I.F.Op)
    (s : Silmaril.Wasm.Execution.Core.Store Nat) (t : Thread) : Prop :=
  ∃ s₀, I.WellFormed s₀ ∧ Reach P (s₀, I.initThread f) (s, t)

/-- The relation of the engine-to-composite simulation. -/
@[expose] def R1 (P : Profile) (hI : m.IsInst I) :
    (LE P m I).State → (LC P hI).State → Prop
  | .idle s, z => z = (.idle, (.idle s, .idle)) ∧ I.WellFormed s
  | .refusing q s, z => z = (.idle, (.idle s, .run q (.pure none))) ∧ I.WellFormed s
  | .running q s t, z => ∃ f, z = (.idle, (.running f s t, .wait q f (kAns f))) ∧ RunInv P I f s t
  | .waiting .., _ => False

/-- An engine call: the export question, then the hidden instance call. -/
theorem ec_call {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
    {a : Nat} {xs : List Flat} (hw : I.WellFormed s)
    (hc : callee? (E := core3P P) I.addrs m.exports q = some (a, xs)) :
    ∃ z, (LC P hI).Run (.idle, (.idle s, .idle)) [.inr (.ask q)] z ∧
      R1 P hI (.running q s (Thread.invokeFlat a xs)) z := by
  obtain ⟨f, hf, hth⟩ := exportH_of_callee hI hc
  refine ⟨_, .vis (lc_ask s q) (.tau (lc_call hf) (.nil _)), f, ?_, s, hw, ?_⟩
  · rw [hth]
    rfl
  · rw [← hth]

/-- A refused engine call: the export question, answered by the handler at once. -/
theorem ec_refuse {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
    (hw : I.WellFormed s) (hc : callee? (E := core3P P) I.addrs m.exports q = none) :
    ∃ z, (LC P hI).Run (.idle, (.idle s, .idle)) [.inr (.ask q)] z ∧
      R1 P hI (.refusing q s) z := by
  have hx := exportH_of_no_callee hI hI.1.choose_spec.ok.addrs_length hc
  refine ⟨_, .vis (lc_ask s q) (.nil _), ?_, hw⟩
  rw [hx]
  rfl

/-- An engine answer: the hidden instance answer, then the export answer. -/
theorem ec_ret {s s' : Silmaril.Wasm.Execution.Core.Store Nat} {t t' : Thread}
    {q : (sigN m.exports.length).Op} {f : I.F.Op} {res : Silmaril.Wasm.Component.Engine.CallResult}
    (hinv : RunInv P I f s t) (run : Reach P (s, t) (s', t'))
    (final : (core3P P).status s' t' = .returned res) :
    ∃ z, (LC P hI).Run (.idle, (.running f s t, .wait q f (kAns f)))
      [.inr (.ans q (payloadOf res))] z ∧
      R1 P hI (.idle s') z := by
  obtain ⟨s₀, hw₀, reach₀⟩ := hinv
  obtain ⟨r, hr, hans⟩ := result_of_status final
  have reach : Reach P (s₀, I.initThread f) (s', t') := reach₀.trans run
  have steps : Silmaril.Wasm.Execution.Core.Steps P
      (Silmaril.Wasm.Game.hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
      (Silmaril.Wasm.Execution.Core.invoke s₀ (I.addr f.1) f.2.1) (t'.config s') :=
    Silmaril.Wasm.Game.Reach.steps reach
  have hK := Silmaril.Proofs.Wasm.Component.Reference.throwsBelow_silent I s₀.exns.length
  obtain ⟨v, hv, -⟩ := ScalarInstance.answer_of_run hw₀ hK steps hr
  have hw' : I.WellFormed (t'.config s').store :=
    (ScalarInstance.wellFormed_after_run hw₀ hK steps hr).1
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hw'
  refine ⟨_, .tau (lc_oret run hr hv) ?_, rfl, hw'⟩
  rw [← hans hv]
  exact .vis (lc_ret s' q _) (.nil _)

/-- **The engine simulates into the composite.** -/
theorem ec_step {x x' : (LE P m I).State} {z : (LC P hI).State}
    {l : Option (Move (sigN 0) (sigN m.exports.length))} (hr : R1 P hI x z)
    (h : (LE P m I).step x l x') : ∃ z', (LC P hI).Run z l.toList z' ∧ R1 P hI x' z' := by
  obtain ⟨mv, rfl, h⟩ := h
  cases h with
  | call hc =>
    obtain ⟨rfl, hw⟩ := hr
    exact ec_call hw hc
  | refuse hc =>
    obtain ⟨rfl, hw⟩ := hr
    exact ec_refuse hw hc
  | refused =>
    obtain ⟨rfl, hw⟩ := hr
    exact ⟨_, .vis (lc_ret _ _ none) (.nil _), rfl, hw⟩
  | ucall _ _ hh => exact absurd hh (Nat.not_lt_zero _)
  | uret => exact hr.elim
  | oret run final =>
    obtain ⟨f, rfl, hinv⟩ := hr
    exact ec_ret hinv run final
  | otrap run final =>
    obtain ⟨f, rfl, hinv⟩ := hr
    exact ec_ret hinv run final

/-- The engine-to-composite simulation. -/
def simEC (P : Profile) (hI : m.IsInst I) : (LE P m I).Simulation (LC P hI) where
  R := R1 P hI
  init := ⟨rfl, hI.1.choose_spec.ok⟩
  step := ec_step

end EC

/-! ## Composite to engine -/

section CE

variable {P : Profile} {m : NumModule} {I : ScalarInstance} {hI : m.IsInst I}

/-- The relation of the composite-to-engine simulation. `answering`: the hidden instance answer
has committed to the run to `(s', t')`, which the engine plays at the export answer. -/
inductive R2 (P : Profile) (hI : m.IsInst I) : (LC P hI).State → (LE P m I).State → Prop
  /-- Between calls. -/
  | idle {s : Silmaril.Wasm.Execution.Core.Store Nat} : R2 P hI (.idle, (.idle s, .idle)) (.idle s)
  /-- An ill-typed question. -/
  | refusing {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
      (hc : callee? (E := core3P P) I.addrs m.exports q = none) :
      R2 P hI (.idle, (.idle s, .run q (exportH (numInst hI) q))) (.refusing q s)
  /-- A typed question before the hidden instance call. -/
  | pending {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
      {a : Nat} {xs : List Flat}
      (hc : callee? (E := core3P P) I.addrs m.exports q = some (a, xs)) :
      R2 P hI (.idle, (.idle s, .run q (exportH (numInst hI) q)))
        (.running q s (Thread.invokeFlat a xs))
  /-- The instance runs the thread. -/
  | running {s : Silmaril.Wasm.Execution.Core.Store Nat} {t : Thread}
      {q : (sigN m.exports.length).Op} {f : I.F.Op} :
      R2 P hI (.idle, (.running f s t, .wait q f (kAns f))) (.running q s t)
  /-- The instance has answered; the export handler has not yet. -/
  | answering {s s' : Silmaril.Wasm.Execution.Core.Store Nat} {t t' : Thread}
      {q : (sigN m.exports.length).Op} {r : Option Payload} (run : Reach P (s, t) (s', t'))
      (hst : Answers P s' t' r) :
      R2 P hI (.idle, (.idle s', .run q (.pure r))) (.running q s t)

/-- From between calls: an export question. -/
theorem ce_idle {s : Silmaril.Wasm.Execution.Core.Store Nat}
    {l : Option (Move (sigN 0) (sigN m.exports.length))} {z' : (LC P hI).State}
    (h : (LC P hI).step (.idle, (.idle s, .idle)) l z') :
    ∃ x', (LE P m I).Run (.idle s) l.toList x' ∧ R2 P hI z' x' := by
  obtain ⟨y', rfl, ⟨rfl, hy⟩ | ⟨g, rfl, hy⟩⟩ := lc_inv h
  · obtain ⟨q, hl, -⟩ := lm_idle_inv hy
    cases hl
  · obtain ⟨q, hl, rfl⟩ := lm_idle_inv hy
    cases hl
    cases hc : callee? (E := core3P P) I.addrs m.exports q with
    | none => exact ⟨_, .vis ⟨_, rfl, .refuse hc⟩ (.nil _), .refusing hc⟩
    | some p => exact ⟨_, .vis ⟨_, rfl, .call hc⟩ (.nil _), .pending hc⟩

/-- From a handler that has just answered `r`. -/
theorem ce_pure {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
    {c : Prog I.F (Option Payload)} {l : Option (Move (sigN 0) (sigN m.exports.length))}
    {z' : (LC P hI).State} (h : (LC P hI).step (.idle, (.idle s, .run q c)) l z') :
    (∃ f k, c = .call f k ∧ l = none ∧ z' = (.idle, (.running f s (I.initThread f), .wait q f k))) ∨
      ∃ r, c = .pure r ∧ l = some (.inr (.ans q r)) ∧ z' = (.idle, (.idle s, .idle)) := by
  obtain ⟨y', rfl, ⟨rfl, hy⟩ | ⟨g, rfl, hy⟩⟩ := lc_inv h
  · rcases lm_run_inv hy with ⟨f, k, hc, -, rfl⟩ | ⟨r, -, hl, -⟩
    · exact .inl ⟨f, k, hc, rfl, rfl⟩
    · cases hl
  · rcases lm_run_inv hy with ⟨f, k, -, hl, -⟩ | ⟨r, hc, hl, rfl⟩
    · cases hl
    · exact .inr ⟨r, hc, by cases hl; rfl, rfl⟩

/-- From a running thread: the hidden instance answer. -/
theorem ce_running {s : Silmaril.Wasm.Execution.Core.Store Nat} {t : Thread}
    {q : (sigN m.exports.length).Op} {f : I.F.Op}
    {l : Option (Move (sigN 0) (sigN m.exports.length))} {z' : (LC P hI).State}
    (h : (LC P hI).step (.idle, (.running f s t, .wait q f (kAns f))) l z') :
    ∃ x', (LE P m I).Run (.running q s t) l.toList x' ∧ R2 P hI z' x' := by
  obtain ⟨y', rfl, ⟨rfl, hy⟩ | ⟨g, rfl, hy⟩⟩ := lc_inv h
  · obtain ⟨s', t', r, v, run, final, hv, -, rfl⟩ := lm_wait_inv hy
    exact ⟨_, .nil _, .answering run (answers_of_result hI final hv)⟩
  · obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := lm_wait_inv hy
    cases hl

/-- From an ill-typed question: the trap answer. -/
theorem ce_refusing {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
    {l : Option (Move (sigN 0) (sigN m.exports.length))} {z' : (LC P hI).State}
    (hc : callee? (E := core3P P) I.addrs m.exports q = none)
    (h : (LC P hI).step (.idle, (.idle s, .run q (exportH (numInst hI) q))) l z') :
    ∃ x', (LE P m I).Run (.refusing q s) l.toList x' ∧ R2 P hI z' x' := by
  have hx := exportH_of_no_callee hI hI.1.choose_spec.ok.addrs_length hc
  rcases ce_pure h with ⟨f, k, hk, -, -⟩ | ⟨r, hk, rfl, rfl⟩
  · exact absurd (hx.symm.trans hk) nofun
  · obtain rfl : none = r := Prog.pure.inj (hx.symm.trans hk)
    exact ⟨_, .vis ⟨_, rfl, .refused⟩ (.nil _), .idle⟩

/-- From a typed question: the hidden instance call, matched by no engine step. -/
theorem ce_pending {s : Silmaril.Wasm.Execution.Core.Store Nat} {q : (sigN m.exports.length).Op}
    {a : Nat} {xs : List Flat} {l : Option (Move (sigN 0) (sigN m.exports.length))}
    {z' : (LC P hI).State} (hc : callee? (E := core3P P) I.addrs m.exports q = some (a, xs))
    (h : (LC P hI).step (.idle, (.idle s, .run q (exportH (numInst hI) q))) l z') :
    ∃ x', (LE P m I).Run (.running q s (Thread.invokeFlat a xs)) l.toList x' ∧ R2 P hI z' x' := by
  obtain ⟨f, hf, hth⟩ := exportH_of_callee hI hc
  rcases ce_pure h with ⟨f', k, hk, rfl, rfl⟩ | ⟨r, hk, -, -⟩
  · cases hf.symm.trans hk
    rw [hth]
    exact ⟨_, .nil _, .running⟩
  · exact absurd (hf.symm.trans hk) nofun

/-- From an answered instance: the export answer, played by the engine's committed run. -/
theorem ce_answering {s s' : Silmaril.Wasm.Execution.Core.Store Nat} {t t' : Thread}
    {q : (sigN m.exports.length).Op} {r : Option Payload}
    {l : Option (Move (sigN 0) (sigN m.exports.length))} {z' : (LC P hI).State}
    (run : Reach P (s, t) (s', t')) (hst : Answers P s' t' r)
    (h : (LC P hI).step (.idle, (.idle s', .run q (.pure r))) l z') :
    ∃ x', (LE P m I).Run (.running q s t) l.toList x' ∧ R2 P hI z' x' := by
  rcases ce_pure h with ⟨f, k, hk, -, -⟩ | ⟨r', hk, rfl, rfl⟩
  · cases hk
  · cases hk
    rcases hst with ⟨rfl, final⟩ | ⟨ys, rfl, final⟩
    · exact ⟨_, .vis ⟨_, rfl, .otrap run final⟩ (.nil _), .idle⟩
    · exact ⟨_, .vis ⟨_, rfl, .oret run final⟩ (.nil _), .idle⟩

/-- **The composite simulates into the engine.** -/
theorem ce_step {z z' : (LC P hI).State} {x : (LE P m I).State}
    {l : Option (Move (sigN 0) (sigN m.exports.length))} (hr : R2 P hI z x)
    (h : (LC P hI).step z l z') : ∃ x', (LE P m I).Run x l.toList x' ∧ R2 P hI z' x' := by
  cases hr with
  | idle => exact ce_idle h
  | refusing hc => exact ce_refusing hc h
  | pending hc => exact ce_pending hc h
  | running => exact ce_running h
  | answering run hst => exact ce_answering run hst h

/-- The composite-to-engine simulation. -/
def simCE (P : Profile) (hI : m.IsInst I) : (LC P hI).Simulation (LE P m I) where
  R := R2 P hI
  init := .idle
  step := ce_step

end CE

/-! ## The bridge -/

/-- The engine semantics of a module whose engine instance is `I`. -/
theorem engineSem_of_sameInst {P : Profile} {m : NumModule} {I : ScalarInstance}
    (hS : instOf (core3P P) m.mod [] m.exports = some ⟨I.store, I.addrs⟩) :
    (engineSem (core3P P) NumModule NumModule.mod).sem m =
      engineStrategy (core3P P) ⟨I.store, I.addrs⟩ [] m.exports := by
  have hS' : instOf (core3P P) (NumModule.mod m) (CoreModule.imports m) (CoreModule.exports m) =
      some ⟨I.store, I.addrs⟩ := hS
  simp only [engineSem, hS']
  rfl

/-- **The bridge**: with the same instance on both sides, the game semantics of the Core 3.0
engine is `modSem P`. -/
theorem engineSem_eq_modSem (P : Profile) {m : NumModule} {I : ScalarInstance}
    (hI : m.IsInst I) (hS : instOf (core3P P) m.mod [] m.exports = some ⟨I.store, I.addrs⟩) :
    (engineSem (core3P P) NumModule NumModule.mod).sem m = (modSem P).sem m := by
  rw [engineSem_of_sameInst hS]
  apply le_antisymm
  · exact Strategy.ofLTS_le_iff.2 fun p hp _ =>
      (lc_denotes P hI p).1 ((simEC P hI).traces_subset hp)
  · intro p hp
    exact Strategy.mem_ofLTS_of_mem_traces
      ((simCE P hI).traces_subset ((lc_denotes P hI p).2 hp)) (Strategy.legal _ hp)

end Silmaril.Proofs.Wasm.Component.Core3G
