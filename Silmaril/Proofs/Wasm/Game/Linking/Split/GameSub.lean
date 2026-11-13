module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Typed
public import Silmaril.Proofs.Wasm.Game.Linking.Split.Back
public import Silmaril.Proofs.Wasm.Game.Adequacy.Termination
public import Silmaril.Wasm.SingleThreaded.Interface

/-!
# Static linking, separation: the shared world is simulated by the composition

Original module documentation:

# The shared object is the provider interacting with the consumer: `⊆` (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

Every play of the shared object is an overlay play of the consumer's stateful plays run against
the provider object. When the shared world answers an export call, its host-free run reaches a
normal form; the joint machine of the split world (consumer steps, calls into the provider,
provider steps, returns) simulates it step by step (`Joint`), so it cannot run forever
(`reach_normal_not_infinite`: an infinite joint run would be an infinite shared run), it is
never stuck (typed threads, `statusP_ne_stuck`; typed callouts are import calls,
`callout_args_typed`; typed provider results are answers, `vals_typed`), and its result is the
shared one (`reach_normal_unique`). The induction is on accessibility of the shared
configuration (`run_to_result`).

Silmaril: the statement and the proof are now for **every profile** `P`. The deterministic proof
followed a joint step to its forward image and used uniqueness of normal forms
(`reach_normal_unique`, `Internal.deterministic`) to stay on the shared run. Here the
induction is on the given shared run instead (`run_to_result`, `Next`): the next shared
configuration is the forward image of the joint step, or the shared step is `Soft` (a profile
choice or a bubble, `Choice.eq_or_soft`), and then it is the image of a consumer or provider
step (`CRel.soft_back`, `PRel.soft_back`, `Silmaril.Proofs.Wasm.Game.Linking.Split.Back`). A
trapping provider is handled by `reach_doomed'` (every run from a trapped configuration ends in
a trap in the same store) instead of uniqueness (`p_doomed`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Proofs.Wasm.Game.Linking

variable {S : Setup}

theorem threadOk_storeOk {s : Store Nat} {t : Thread} {ts : List CValType} (h : ThreadOk s t ts) :
    StoreOk s := by
  have := ConfigOk.storeOk h
  rwa [Thread.config_store] at this

/-- A normal configuration reaches only itself. -/
theorem reach_eq_of_normal {P : Profile} {x y : Store Nat × Thread} (h : Reach P x y)
    (hx : ∀ z, ¬ InternalP P x z) : x = y := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨z, hz, -⟩
  · rfl
  · exact absurd hz (hx z)

/-- A renamed result typed by a scalar answer was not renamed. -/
theorem result_eq_of_ren {ft : FnType} {ρ : Ren} {r rs : Result} {v : Answer ft}
    (h : ρ.result r = rs) (hans : Answer.ofResult? ft rs = some v) : r = rs := by
  cases r with
  | values vs =>
    subst h
    have := forall₂_hasVal_of_ren (ofResult?_values hans)
    simp [Ren.result, this]
  | trap => exact h
  | throw a => exact h

theorem resume_values_eq (s : Store Nat) (t : Thread) (vs : List Val) :
    resume s t (.values vs) = resumeResult s t (.values vs) := by
  simp only [resume, resumeResult, CallResult.toAdmin, Result.toAdmin]

/-- The result types of an export call. -/
abbrev resT (f : S.consumerI.F.Op) : List CValType :=
  (S.exportTypes.get f.1).results.map ScalarType.toC

/-- The result types of a stub call. -/
abbrev stubT (e : S.consumerI.E.Op) : List CValType :=
  (S.stubTypes.get e.1).results.map ScalarType.toC

/-- The Core result types of a function type. -/
abbrev resC (ft : FnType) : List CValType := ft.results.map ScalarType.toC

/-- `LRun I P x evs y`: from `x`, the thread of `I` runs host-free, stopping at the import calls
`evs` (questions with the answers it received), and is at `y` after the last answer. -/
inductive LRun (I : ScalarInstance) (P : Profile) :
    Store Nat × Thread → List (Ev I.E) → Store Nat × Thread → Prop where
  /-- A host-free run. -/
  | done {x y : Store Nat × Thread} : Reach P x y → LRun I P x [] y
  /-- A host-free run to a callout, the import call `e` answered `w`, then the rest. -/
  | call {x y : Store Nat × Thread} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
      {e : I.E.Op} {w : I.E.Ar e} {l : List (Ev I.E)} :
      Reach P x (s, t) → CalloutAt s t h args → I.importOp? h args = some e →
      LRun I P (s, resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)) l y →
      LRun I P x (.ask e :: .ans e w :: l) y

/-- `LRunTo I P x evs ft v s'`: from `x`, through the import calls `evs`, the thread reaches a
result whose answer of type `ft` is `v`, at the store `s'`. -/
def LRunTo (I : ScalarInstance) (P : Profile) (x : Store Nat × Thread) (evs : List (Ev I.E))
    (ft : FnType) (v : Answer ft) (s' : Store Nat) : Prop :=
  ∃ (t' : Thread) (r : Result), LRun I P x evs (s', t') ∧ ResultAt s' t' r ∧
    Answer.ofResult? ft r = some v

theorem LRunTo.done {I : ScalarInstance} {P : Profile} {x : Store Nat × Thread} {s' : Store Nat}
    {t' : Thread} {ft : FnType} {r : Result} {v : Answer ft} (run : Reach P x (s', t'))
    (final : ResultAt s' t' r) (answer : Answer.ofResult? ft r = some v) :
    LRunTo I P x [] ft v s' :=
  ⟨t', r, .done run, final, answer⟩

theorem LRunTo.call {I : ScalarInstance} {P : Profile} {x : Store Nat × Thread} {s s' : Store Nat}
    {t : Thread} {h : Nat} {args : List Val} {e : I.E.Op} {w : I.E.Ar e} {l : List (Ev I.E)}
    {ft : FnType} {v : Answer ft} (run : Reach P x (s, t)) (callout : CalloutAt s t h args)
    (op : I.importOp? h args = some e)
    (rest : LRunTo I P (s, resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)) l ft v s') :
    LRunTo I P x (.ask e :: .ans e w :: l) ft v s' := by
  obtain ⟨t', r, hr, final, answer⟩ := rest
  exact ⟨t', r, .call run callout op hr, final, answer⟩

/-- The path of `LRunTo.path`, from an arbitrary start. -/
theorem LRun.path {I : ScalarInstance} {P : Profile} {f : I.F.Op} {v : I.F.Ar f} {r : Result}
    {x y : Store Nat × Thread} {evs : List (Ev I.E)} (hr : LRun I P x evs y)
    (final : ResultAt y.1 y.2 r) (answer : Answer.ofResult? (I.exports.get f.1) r = some v) :
    I.Path P (.running f x.1 x.2) (evs.map .inl ++ [.inr (.ans f v)]) (.idle y.1) := by
  induction hr with
  | done run => exact .cons (ScalarInstance.Trans.oret run final answer) (.nil _)
  | @call x y s₁ t₁ h args e w l run callout op _ ih =>
    exact .cons (ScalarInstance.Trans.ucall run callout op)
      (.cons (ScalarInstance.Trans.uret w) (ih final))

/-- A run through import calls to an answer of the export `f` is a path of the instance. -/
theorem LRunTo.path {I : ScalarInstance} {P : Profile} {f : I.F.Op} {v : I.F.Ar f} :
    ∀ {s : Store Nat} {t : Thread} {evs : List (Ev I.E)} {s' : Store Nat},
      LRunTo I P (s, t) evs (I.exports.get f.1) v s' →
      I.Path P (.running f s t) (evs.map .inl ++ [.inr (.ans f v)]) (.idle s') := by
  intro s t evs s' h
  obtain ⟨t', r, hr, final, answer⟩ := h
  exact LRun.path hr final answer

/-- States of the joint machine, with the game states they continue. -/
inductive JS (S : Setup) where
  /-- The consumer runs: its last game state is `running f κ₀ tc₀`, its thread is now `tc`. -/
  | c (κ₀ : Store Nat) (tc₀ : Thread) (κ : Store Nat) (tc : Thread) (π : Store Nat)
  /-- The provider runs the stub call `e` from its game state `running e π₀ _`. -/
  | p (κ : Store Nat) (tc : Thread) (e : S.consumerI.E.Op) (π₀ π : Store Nat) (tp : Thread)

/-- Typed stores with no call active. -/
def IdleT (St : Static S) (σ π κ : Store Nat) : Prop := Idle St σ π κ ∧ StoreOk π ∧ StoreOk κ

/-- The invariant of the joint machine at the shared configuration `x`. -/
def JInv (St : Static S) (P : Profile) (ft : FnType) (x : Store Nat × Thread) :
    JS S → Prop
  | .c κ₀ tc₀ κ tc π => Reach P (κ₀, tc₀) (κ, tc) ∧ CRel St x.1 x.2 π κ tc ∧ StoreOk π ∧
      ThreadOk κ tc (resC ft)
  | .p κ tc e π₀ π tp => CalloutAt κ tc e.1 e.2.1 ∧
      Reach P (π₀, S.providerI.initThread e) (π, tp) ∧ PRel St x.1 x.2 π tp κ tc e.1 e.2.1 ∧
      ThreadOk κ tc (resC ft) ∧ ThreadOk π tp (stubT e) ∧ ∀ r, ¬ ResultAt π tp r

/-- What the joint machine produces when the shared world answers `v` (of type `ft`): the
consumer's run through its import calls `evs` to the answer `v`, and the provider's play
answering them. -/
def JGoal (St : Static S) (P : Profile) (ft : FnType) (v : Answer ft)
    (σf : Store Nat) : JS S → Prop
  | .c κ₀ tc₀ _ _ π => ∃ (evs : List (Ev S.consumerI.E))
      (pp : List (Move S.providerI.E S.providerI.F)) (κ' π' : Store Nat),
      LRunTo S.consumerI P (κ₀, tc₀) evs ft v κ' ∧
      S.providerI.Path P (.idle π) pp (.idle π') ∧ evs = upper pp ∧ IdleT St σf π' κ'
  | .p κ tc e π₀ _ _ => ∃ (w : S.consumerI.E.Ar e) (evs : List (Ev S.consumerI.E))
      (pp : List (Move S.providerI.E S.providerI.F)) (κ' π' : Store Nat),
      LRunTo S.consumerI P
        (κ, resumeResult κ tc (Answer.toResult (ft := S.consumerI.imports.get e.1) w)) evs ft v κ' ∧
      S.providerI.Path P (.running e π₀ (S.providerI.initThread e)) (.inr (.ans e w) :: pp)
        (.idle π') ∧
      evs = upper pp ∧ IdleT St σf π' κ'

theorem CRel.world {St : Static S} {σ π κ : Store Nat} {ts tc : Thread}
    (h : CRel St σ ts π κ tc) : ∃ ρp Op ρc Oc, World St σ π κ ρp Op ρc Oc := by
  obtain ⟨ρp, Op, ρc, Oc, hW, -⟩ := h
  exact ⟨ρp, Op, ρc, Oc, hW⟩

theorem PRel.world {St : Static S} {σ π κ : Store Nat} {ts tp tc : Thread} {h : Nat}
    {args : List Val} (hP : PRel St σ ts π tp κ tc h args) :
    ∃ ρp Op ρc Oc, World St σ π κ ρp Op ρc Oc := by
  obtain ⟨ρp, Op, ρc, Oc, -, -, hW, -⟩ := hP
  exact ⟨ρp, Op, ρc, Oc, hW⟩

/-! ### Steps of the joint machine -/

/-- The consumer finishes with the shared result. -/
private theorem c_finish {St : Static S} {P : Profile} {ft : FnType}
    {σf : Store Nat} {tsf : Thread} {rs : Result} {v : Answer ft}
    (hfin : ResultAt σf tsf rs)
    (hans : Answer.ofResult? ft rs = some v)
    {σ κ₀ κ π : Store Nat} {ts tc₀ tc : Thread}
    (hx : Reach P (σ, ts) (σf, tsf)) (hrκ : Reach P (κ₀, tc₀) (κ, tc))
    (hR : CRel St σ ts π κ tc) (hπ : StoreOk π) (hκ : StoreOk κ)
    {r : Result} (hr : ResultAt κ tc r) : JGoal St P ft v σf (.c κ₀ tc₀ κ tc π) := by
  obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := hR.result hr
  have hxe : (σ, ts) = (σf, tsf) := reach_eq_of_normal hx (resultAt_no_internal hres)
  have hσ : σ = σf ∧ ts = tsf := Prod.mk.inj hxe
  have hres' : ResultAt σf tsf (ρ.result r) := hσ.1 ▸ hσ.2 ▸ hres
  have hrr : r = rs := result_eq_of_ren (resultAt_unique hres' hfin) hans
  have hans' : Answer.ofResult? ft r = some v := hrr ▸ hans
  have hI' : IdleT St σf π κ := ⟨hσ.1 ▸ hI, hπ, hκ⟩
  exact ⟨[], [], κ, π, LRunTo.done hrκ hr hans', .nil _, rfl, hI'⟩

/-- The arguments of a consumer callout are typed by its stub. -/
theorem stub_args_typed {P : Profile} {κ : Store Nat} {tc : Thread}
    {ts : List CValType} (htc : ThreadOk κ tc ts) (hwc : S.consumerI.WellFormed κ)
    {h : Nat} {args : List Val} (hco : CalloutAt κ tc h args) :
    ∃ hlt : h < S.stubTypes.length,
      List.Forall₂ ScalarType.HasVal (S.stubTypes.get ⟨h, hlt⟩).params args := by
  obtain ⟨a', fi, ps, rs', hfi, hcode, hexp, hvs⟩ := callout_args_typed (P := P) htc hco
  obtain ⟨hlt, hexp'⟩ := hwc.host_type a' fi h hfi hcode
  have hps : ps = Ty.ofList ((S.consumerI.imports.get ⟨h, hlt⟩).params.map ScalarType.toC) ∧
      rs' = Ty.ofList ((S.consumerI.imports.get ⟨h, hlt⟩).results.map ScalarType.toC) := by
    simpa only [FnType.toComp, Ty.func.injEq] using Expand.func_eq hexp hexp'
  have hvs' : List.Forall₂ (ValOk κ) args
      ((S.consumerI.imports.get ⟨h, hlt⟩).params.map ScalarType.toC) := by
    simpa only [hps.1, toList_toC] using hvs
  exact ⟨hlt, forall₂_hasVal_of_valOk hvs'⟩

/-- A typed stub call is an import operation of the consumer. -/
theorem importOp?_stub {h : Nat} {args : List Val} (hlt : h < S.stubTypes.length)
    (hargs : List.Forall₂ ScalarType.HasVal (S.stubTypes.get ⟨h, hlt⟩).params args) :
    S.consumerI.importOp? h args = some (⟨⟨h, hlt⟩, ⟨args, hargs⟩⟩ : S.consumerI.E.Op) := by
  show ifaceOp? S.stubTypes h args = some _
  unfold ifaceOp?
  split
  · rfl
  · exact absurd hlt ‹_›

/-! ### Following the shared run -/

/-- Two internal steps to equal configurations have equal targets. -/
theorem internalP_eq {P : Profile} {x y z : Store Nat × Thread} (hy : InternalP P x y)
    (hz : InternalP P x z) (h : y.2.config y.1 = z.2.config z.1) : y = z := by
  rcases y with ⟨s₁, t₁⟩
  rcases z with ⟨s₂, t₂⟩
  obtain ⟨f₁, c₁, rfl, -⟩ := hy
  obtain ⟨f₂, c₂, rfl, -⟩ := hz
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj h
  rfl

/-- The next configuration of the shared run is the forward image of a joint step, or the
shared step is `Soft` (`Choice.eq_or_soft`). -/
theorem next_eq_or_soft {P : Profile} {x y y₁ : Store Nat × Thread} (hy : InternalP P x y)
    (hy₁ : InternalP P x y₁) : y = y₁ ∨ Choice.Soft P (x.2.config x.1) (y.2.config y.1) := by
  rcases Choice.eq_or_soft (InternalP.toStep P noHost hy₁) (InternalP.toStep P noHost hy) with
    h | h
  · exact .inl (internalP_eq hy hy₁ h)
  · exact .inr h

/-- The target of an internal step is the active thread of its configuration. -/
theorem internalP_active {P : Profile} {x y : Store Nat × Thread} (hy : InternalP P x y) :
    y = (y.1, .active (y.2.config y.1).frame (y.2.config y.1).code) := by
  rcases y with ⟨s, t⟩
  obtain ⟨f, c, rfl, -⟩ := hy
  rfl

/-- What the shared run offers at `x`: `x` is its result, or its next step together with the
induction hypothesis there. -/
def Next (St : Static S) (P : Profile) (ft : FnType) (v : Answer ft)
    (σf : Store Nat) (tsf : Thread) (x : Store Nat × Thread) : Prop :=
  x = (σf, tsf) ∨ ∃ y, InternalP P x y ∧ Reach P y (σf, tsf) ∧
    ∀ js, JInv St P ft y js → JGoal St P ft v σf js

/-- A joint step at `x` has a shared image; at the result there is none. -/
theorem Next.step {St : Static S} {P : Profile} {ft : FnType} {v : Answer ft}
    {σf : Store Nat} {tsf : Thread} {rs : Result} (hfin : ResultAt σf tsf rs)
    {x y₁ : Store Nat × Thread} (hn : Next St P ft v σf tsf x) (hy₁ : InternalP P x y₁) :
    ∃ y, InternalP P x y ∧ Reach P y (σf, tsf) ∧
      (∀ js, JInv St P ft y js → JGoal St P ft v σf js) ∧
      (y = y₁ ∨ Choice.Soft P (x.2.config x.1) (y.2.config y.1)) := by
  rcases hn with rfl | ⟨y, hy, hyf, IH⟩
  · exact absurd hy₁ (resultAt_no_internal hfin y₁)
  · exact ⟨y, hy, hyf, IH, next_eq_or_soft hy hy₁⟩

/-- The consumer calls a stub: the provider takes over. -/
private theorem c_callout {St : Static S} {P : Profile} {ft : FnType}
    {σf : Store Nat} {tsf : Thread} {rs : Result} (hfin : ResultAt σf tsf rs)
    {v : Answer ft} {σ κ₀ κ π : Store Nat} {ts tc₀ tc : Thread}
    (hn : Next St P ft v σf tsf (σ, ts))
    (hrκ : Reach P (κ₀, tc₀) (κ, tc)) (hR : CRel St σ ts π κ tc) (hπ : StoreOk π)
    (htc : ThreadOk κ tc (resC ft)) (hwc : S.consumerI.WellFormed κ)
    (hwp : S.providerI.WellFormed π) {h : Nat} {args : List Val}
    (hco : CalloutAt κ tc h args) : JGoal St P ft v σf (.c κ₀ tc₀ κ tc π) := by
  obtain ⟨hlt, hargs⟩ := stub_args_typed (P := P) htc hwc hco
  let e : S.consumerI.E.Op := ⟨⟨h, hlt⟩, ⟨args, hargs⟩⟩
  have hop : S.consumerI.importOp? h args = some e := importOp?_stub hlt hargs
  obtain ⟨hlt', tp₀, ts₁, hp₀, hs₁, hP, hnr⟩ := hR.call (P := P) hco hargs
  obtain ⟨y, -, -, IH, hy⟩ := hn.step hfin hs₁
  have hy' : y = (σ, ts₁) := by
    rcases hy with h' | hsoft
    · exact h'
    · obtain ⟨X', hstep, -, -⟩ := hR.soft_back hsoft
      exact absurd hstep (calloutAt_no_internal hco _)
  subst hy'
  have hp₀' : InternalP P (π, S.providerI.initThread e) (π, tp₀) := hp₀
  have htp₀ : ThreadOk π tp₀ (stubT e) :=
    (InternalP.preserves hπ (hwp.init_typed e) hp₀').2.1
  obtain ⟨w, evs, pp, κ', π', hrun, hpp, hproj, hI⟩ :=
    IH (.p κ tc e π π tp₀) ⟨hco, .single hp₀', hP, htc, htp₀, hnr⟩
  have hproj' : (Ev.ask e :: Ev.ans e w :: evs : List (Ev S.consumerI.E)) =
      upper (.inr (.ask e) :: .inr (.ans e w) :: pp : List (Move S.providerI.E S.providerI.F)) := by
    rw [hproj]
    rfl
  exact ⟨.ask e :: .ans e w :: evs, .inr (.ask e) :: .inr (.ans e w) :: pp, κ', π',
    LRunTo.call hrκ hco hop hrun,
    .cons (ScalarInstance.Trans.call (I := S.providerI) (P := P) π e) hpp, hproj', hI⟩

/-- The consumer takes a step: the forward image or, for a `Soft` shared step, its
backward image. -/
private theorem c_step {St : Static S} {P : Profile} {ft : FnType}
    {σf : Store Nat} {tsf : Thread} {rs : Result} (hfin : ResultAt σf tsf rs)
    {v : Answer ft} {σ κ₀ κ κ' π : Store Nat} {ts tc₀ tc tc' : Thread}
    (hn : Next St P ft v σf tsf (σ, ts)) (hrκ : Reach P (κ₀, tc₀) (κ, tc))
    (hR : CRel St σ ts π κ tc) (hπ : StoreOk π) (hκ : StoreOk κ) (htc : ThreadOk κ tc (resC ft))
    (hy : InternalP P (κ, tc) (κ', tc')) : JGoal St P ft v σf (.c κ₀ tc₀ κ tc π) := by
  obtain ⟨σ', ts', hx', hR'⟩ := hR.step hy
  obtain ⟨y, hxy, -, IH, hyy⟩ := hn.step hfin hx'
  rcases hyy with rfl | hsoft
  · obtain ⟨-, htc', -⟩ := InternalP.preserves hκ htc hy
    exact IH (.c κ₀ tc₀ κ' tc' π) ⟨hrκ.tail hy, hR', hπ, htc'⟩
  · rcases y with ⟨σy, ty⟩
    obtain ⟨fy, cy, rfl, -⟩ := hxy
    obtain ⟨X', hstep, hst, hRs⟩ := hR.soft_back hsoft
    have hy1 : σy = σ := hst
    subst hy1
    obtain ⟨-, htcs, -⟩ := InternalP.preserves hκ htc hstep
    exact IH (.c κ₀ tc₀ κ (.active (tc.config κ).frame X') π) ⟨hrκ.tail hstep, hRs, hπ, htcs⟩

/-- **The consumer runs.** -/
private theorem run_c (St : Static S) (hS : S.Scalar) (P : Profile) (ft : FnType)
    {σf : Store Nat} {tsf : Thread} {rs : Result} {v : Answer ft}
    (hfin : ResultAt σf tsf rs)
    (hans : Answer.ofResult? ft rs = some v)
    {σ κ₀ κ π : Store Nat} {ts tc₀ tc : Thread} (hx : Reach P (σ, ts) (σf, tsf))
    (hn : Next St P ft v σf tsf (σ, ts))
    (hj : JInv St P ft (σ, ts) (.c κ₀ tc₀ κ tc π)) : JGoal St P ft v σf (.c κ₀ tc₀ κ tc π) := by
  obtain ⟨hrκ, hR, hπ, htc⟩ := hj
  have hκ : StoreOk κ := threadOk_storeOk htc
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hR.world
  have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
  have hwp : S.providerI.WellFormed π := hS.provider.of_funcs hπ hW.fπ
  have hst : statusP P κ tc ≠ .stuck := statusP_ne_stuck hκ htc
  have finish : ∀ r, ResultAt κ tc r → JGoal St P ft v σf (.c κ₀ tc₀ κ tc π) :=
    fun _ hr => c_finish hfin hans hx hrκ hR hπ hκ hr
  cases hstat : statusP P κ tc with
  | returned cr =>
    cases cr with
    | values vs => exact finish (.values vs) (statusP_returned_values hstat)
    | trap =>
      rcases statusP_returned_trap_inv hstat with h | ⟨a, h⟩
      · exact finish .trap h
      · exact absurd rfl ((hR.result (r := .throw a) h).1 a)
  | stuck => exact absurd hstat hst
  | running =>
    obtain ⟨⟨κ', tc'⟩, hy⟩ := statusP_running_inv hstat
    exact c_step hfin hn hrκ hR hπ hκ htc hy
  | callout h args =>
    obtain ⟨E, a, hd⟩ := statusP_callout_inv hstat
    exact c_callout hfin hn hrκ hR hπ htc hwc hwp ⟨E, a, hd⟩

/-- The provider world has no callout. -/
theorem p_no_callout {St : Static S} {P : Profile} {σ π κ : Store Nat}
    {ts tp tc : Thread} {h : Nat} {args : List Val} (hP : PRel St σ ts π tp κ tc h args)
    {h' : Nat} {args' : List Val} : statusP P π tp ≠ .callout h' args' := by
  intro hstat
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hP.world
  obtain ⟨E, a, hd⟩ := statusP_callout_inv hstat
  obtain ⟨fi, -, -, -, hfi, hcode, -⟩ := decompose?_sound hd
  obtain ⟨c, hc⟩ := St.pwasm a fi (by rw [← hW.fπ]; exact hfi)
  exact absurd (hcode.symm.trans hc) (by simp)

/-- The values returned by a stub are typed by its result types. -/
theorem stub_results_typed {π : Store Nat} {tp : Thread} {e : S.consumerI.E.Op}
    {vs : List Val} (htp : ThreadOk π tp (stubT e)) (hr : ResultAt π tp (.values vs)) :
    List.Forall₂ ScalarType.HasVal (S.stubTypes.get e.1).results vs := by
  have hcfg : tp.config π = ⟨π, (tp.config π).frame, vals vs⟩ := by
    have hcode : (tp.config π).code = vals vs := hr
    rw [← hcode]
    exact Thread.config_eta π tp
  have hok : ConfigOk ⟨π, (tp.config π).frame, vals vs⟩ (stubT e) := by
    have h1 : ConfigOk (tp.config π) (stubT e) := htp
    exact hcfg ▸ h1
  exact forall₂_hasVal_of_valOk (vals_typed hok (fun t ht => by
    obtain ⟨st, -, rfl⟩ := List.mem_map.mp ht
    exact scalar_tyOk st))

/-- The consumer resumes from a stub call with typed values. -/
theorem resume_values_typed (P : Profile) {κ : Store Nat} {tc : Thread}
    {ft : FnType} {e : S.consumerI.E.Op} {vs : List Val} (hκ : StoreOk κ)
    (htc : ThreadOk κ tc (resC ft)) (hwc : S.consumerI.WellFormed κ)
    (hco : CalloutAt κ tc e.1 e.2.1)
    (hv : List.Forall₂ ScalarType.HasVal (S.stubTypes.get e.1).results vs) :
    ThreadOk κ (resumeResult κ tc (.values vs)) (resC ft) := by
  have hco' : statusP P κ tc = .callout e.1 e.2.1 := (calloutAt_iff_status (P := P)).mp hco
  rw [← resume_values_eq]
  refine resumeP_typed hκ htc hco' hκ (Extend.refl hκ) ?_
  intro E' a' args' hd'
  obtain ⟨fi, -, -, -, hfi, hcode, -⟩ := decompose?_sound hd'
  obtain ⟨hlt, hexp⟩ := hwc.host_type a' fi _ hfi hcode
  refine ⟨fi, Ty.ofList ((S.stubTypes.get ⟨_, hlt⟩).params.map ScalarType.toC),
    Ty.ofList ((S.stubTypes.get ⟨_, hlt⟩).results.map ScalarType.toC), hfi, hexp, ?_⟩
  rw [toList_toC]
  exact forall₂_valOk_of_hasVal hv

/-- The stub returns values: the consumer resumes. -/
private theorem p_values {St : Static S} (hS : S.Scalar) {P : Profile} {ft : FnType}
    {σf : Store Nat} {v : Answer ft} {σ' κ π₀ π π' : Store Nat} {ts' tc tp tp' : Thread}
    {e : S.consumerI.E.Op} {vs : List Val}
    (IH' : ∀ js, JInv St P ft (σ', ts') js → JGoal St P ft v σf js)
    (hco : CalloutAt κ tc e.1 e.2.1) (hrπ' : Reach P (π₀, S.providerI.initThread e) (π', tp'))
    (hP' : PRel St σ' ts' π' tp' κ tc e.1 e.2.1) (htc : ThreadOk κ tc (resC ft))
    (htp' : ThreadOk π' tp' (stubT e)) (hr : ResultAt π' tp' (.values vs)) :
    JGoal St P ft v σf (.p κ tc e π₀ π tp) := by
  have hπ' : StoreOk π' := threadOk_storeOk htp'
  have hκ : StoreOk κ := threadOk_storeOk htc
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hP'.world
  have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
  have hv : List.Forall₂ ScalarType.HasVal (S.stubTypes.get e.1).results vs :=
    stub_results_typed htp' hr
  let w : S.consumerI.E.Ar e := .values ⟨vs, hv⟩
  have hw : Answer.ofResult? (S.stubTypes.get e.1) (.values vs) = some w := by
    simp only [Answer.ofResult?]
    rw [dite_eq_left hv]
    rfl
  obtain ⟨-, hC⟩ := hP'.ret hr (fun vs' h => by cases h; exact ⟨_, hv⟩)
  have htc' : ThreadOk κ (resumeResult κ tc (.values vs)) (resC ft) :=
    resume_values_typed P hκ htc hwc hco hv
  obtain ⟨evs, pp, κ', π'', hrun, hpp, hproj, hI⟩ :=
    IH' (.c κ (resumeResult κ tc (.values vs)) κ (resumeResult κ tc (.values vs)) π')
      ⟨.refl, hC, hπ', htc'⟩
  exact ⟨w, evs, pp, κ', π'', hrun, .cons (ScalarInstance.Trans.oret hrπ' hr hw) hpp, hproj, hI⟩

/-- A trapped provider: the trap bubbles through the consumer, and the shared run ends in the
same trap in the same store (`reach_doomed'`, every profile). -/
private theorem p_doomed {St : Static S} {P : Profile} {ft : FnType}
    {σf : Store Nat} {tsf : Thread} {rs : Result} {v : Answer ft}
    (hfin : ResultAt σf tsf rs)
    (hans : Answer.ofResult? ft rs = some v)
    {σ κ π₀ π : Store Nat} {ts tc tp : Thread} {e : S.consumerI.E.Op}
    (hx : Reach P (σ, ts) (σf, tsf)) (hco : CalloutAt κ tc e.1 e.2.1)
    (hrπ : Reach P (π₀, S.providerI.initThread e) (π, tp))
    (hP : PRel St σ ts π tp κ tc e.1 e.2.1) (hκ : StoreOk κ) (hπ : StoreOk π)
    {W : List Val} {R : List Admin} (hdoom : (tp.config π).code = vals W ++ [.trap] ++ R) :
    JGoal St P ft v σf (.p κ tc e π₀ π tp) := by
  have hI : Idle St σ π κ := hP.world
  obtain ⟨ρp, Op, ρc, Oc, E', a', -, -, -, -, hF, -, -, hts⟩ := hP
  have hts' : ts.config σ = ⟨σ, ρc.frame (tc.config κ).frame,
      (Ctx.ext (ρc.ctx E') (W.map ρp.val) (ρp.code R)).fill [.trap]⟩ := by
    rw [hts, hdoom, ← Ctx.fill_ext]
    simp
  obtain ⟨hrs, hσf⟩ := reach_doomed' hx hts' hfin
  have hprov : ∃ tpf, Reach P (π₀, S.providerI.initThread e) (π, tpf) ∧
      ResultAt π tpf .trap := by
    by_cases hne : W ≠ [] ∨ R ≠ []
    · refine ⟨.active {} [.trap], hrπ.tail ⟨{}, [.trap], rfl, ?_⟩, rfl⟩
      have hc : tp.config π = ⟨π, {}, vals W ++ [.trap] ++ R⟩ := by
        rw [Thread.config_eta π tp, hF, hdoom]
      rw [hc]
      exact .trapInstrs hne
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      exact ⟨tp, hrπ, by simpa [ResultAt, Result.toAdmin] using hdoom⟩
  obtain ⟨tpf, hrπ', hr⟩ := hprov
  obtain ⟨E, a, hd⟩ := hco
  let w : S.consumerI.E.Ar e := .trap
  have hrt : resumeResult κ tc .trap = .active (tc.config κ).frame (E.fill [.trap]) := by
    unfold resumeResult
    simp only [hd, Result.toAdmin]
  have hrun : Reach P (κ, resumeResult κ tc .trap) (κ, .active (tc.config κ).frame [.trap]) :=
    hrt ▸ fill_trap_reach P κ E (tc.config κ).frame
  have hres' : ResultAt κ (.active (tc.config κ).frame [.trap]) .trap := rfl
  have hv : Answer.ofResult? ft .trap = some v := hrs ▸ hans
  have hσf' : σf = σ := hσf
  have hI' : IdleT St σf π κ := ⟨by rw [hσf']; exact hI, hπ, hκ⟩
  exact ⟨w, [], [], κ, π, LRunTo.done hrun hres' hv,
    .cons (ScalarInstance.Trans.oret hrπ' hr rfl) (.nil _), rfl, hI'⟩

theorem fnv_nil_vals {l : List Admin} {W : List Val} (h : Det.fnv l = (W, [])) : l = vals W := by
  induction l generalizing W with
  | nil =>
    have hW : W = [] := by simpa using h.symm
    rw [hW]
    rfl
  | cons a l ih =>
    rcases ha : a.val? with _ | u
    · rw [Det.fnv_cons_of_none ha] at h; simp at h
    · have hau : a = u.toAdmin := Admin.eq_of_val? ha
      subst hau
      rw [Det.fnv_toAdmin_cons] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact congrArg (u.toAdmin :: ·) (ih (W := (Det.fnv l).1) (by rw [← h2]))

/-- Provider code that is not a result is trapped or running. -/
theorem doomed_or_live {π : Store Nat} {tp : Thread} (hnr : ∀ r, ¬ ResultAt π tp r) :
    (∃ W R, (tp.config π).code = vals W ++ [.trap] ++ R) ∨ Live (tp.config π).code := by
  rcases hf : Det.fnv (tp.config π).code with ⟨W, _ | ⟨e, R⟩⟩
  · exact absurd (fnv_nil_vals hf) (hnr (.values W))
  · by_cases he : e = .trap
    · subst he
      obtain ⟨hl, -⟩ := fnv_eq hf
      exact .inl ⟨W, R, by rw [hl]; simp⟩
    · exact .inr ⟨W, e, R, hf, he⟩

/-- After a provider step: the provider answers, traps, or keeps running. -/
private theorem p_cont {St : Static S} (hS : S.Scalar) {P : Profile} {ft : FnType}
    {σf : Store Nat} {tsf : Thread} {rs : Result} {v : Answer ft}
    (hfin : ResultAt σf tsf rs)
    (hans : Answer.ofResult? ft rs = some v)
    {σ' κ π₀ π π' : Store Nat} {ts' tc tp tp' : Thread} {e : S.consumerI.E.Op}
    (hyf : Reach P (σ', ts') (σf, tsf))
    (IH : ∀ js, JInv St P ft (σ', ts') js → JGoal St P ft v σf js)
    (hco : CalloutAt κ tc e.1 e.2.1) (hrπ' : Reach P (π₀, S.providerI.initThread e) (π', tp'))
    (hP' : PRel St σ' ts' π' tp' κ tc e.1 e.2.1) (htc : ThreadOk κ tc (resC ft))
    (htp' : ThreadOk π' tp' (stubT e)) : JGoal St P ft v σf (.p κ tc e π₀ π tp) := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  have hπ' : StoreOk π' := threadOk_storeOk htp'
  by_cases hres : ∃ r, ResultAt π' tp' r
  · obtain ⟨r, hr⟩ := hres
    cases r with
    | throw a' => exact absurd rfl ((hP'.ret hr (fun _ h => by cases h)).1 a')
    | values vs => exact p_values hS IH hco hrπ' hP' htc htp' hr
    | trap =>
      show ∃ w evs pp κ' π'', _
      have hd : (tp'.config π').code = vals [] ++ [.trap] ++ [] := by
        simpa [ResultAt, Result.toAdmin] using hr
      obtain ⟨w, evs, pp, κ', π'', hrun, hpp, hproj, hI⟩ :=
        p_doomed (tp := tp') (π := π') (σ := σ') hfin hans hyf hco hrπ' hP' hκ hπ' hd
      exact ⟨w, evs, pp, κ', π'', hrun, hpp, hproj, hI⟩
  · have hres' : ∀ r, ¬ ResultAt π' tp' r := fun r hr => hres ⟨r, hr⟩
    exact IH (.p κ tc e π₀ π' tp') ⟨hco, hrπ', hP', htc, htp', hres'⟩

/-- **The provider runs.** -/
private theorem run_p (St : Static S) (hS : S.Scalar) (P : Profile) (ft : FnType)
    {σf : Store Nat} {tsf : Thread} {rs : Result} {v : Answer ft}
    (hfin : ResultAt σf tsf rs)
    (hans : Answer.ofResult? ft rs = some v)
    {σ κ π₀ π : Store Nat} {ts tc tp : Thread} {e : S.consumerI.E.Op}
    (hx : Reach P (σ, ts) (σf, tsf)) (hn : Next St P ft v σf tsf (σ, ts))
    (hj : JInv St P ft (σ, ts) (.p κ tc e π₀ π tp)) : JGoal St P ft v σf (.p κ tc e π₀ π tp) := by
  obtain ⟨hco, hrπ, hP, htc, htp, hnr⟩ := hj
  have hκ : StoreOk κ := threadOk_storeOk htc
  have hπ : StoreOk π := threadOk_storeOk htp
  rcases doomed_or_live hnr with ⟨W, R, hdoom⟩ | hlive
  · exact p_doomed hfin hans hx hco hrπ hP hκ hπ hdoom
  have hst : statusP P π tp ≠ .stuck := statusP_ne_stuck hπ htp
  cases hstat : statusP P π tp with
  | returned cr =>
    cases cr with
    | values vs => exact absurd (statusP_returned_values hstat) (hnr (.values vs))
    | trap =>
      rcases statusP_returned_trap_inv hstat with h | ⟨a, h⟩
      · exact absurd h (hnr .trap)
      · exact absurd h (hnr (.throw a))
  | stuck => exact absurd hstat hst
  | callout h' args' => exact absurd hstat (p_no_callout hP)
  | running =>
    show JGoal St P ft v σf (.p κ tc e π₀ π tp)
    obtain ⟨⟨π', tp'⟩, hy⟩ := statusP_running_inv hstat
    obtain ⟨σ', ts', hx', hP'⟩ := hP.step hy
    obtain ⟨y, hxy, hyf, IH, hyy⟩ := hn.step hfin hx'
    rcases hyy with rfl | hsoft
    · obtain ⟨-, htp', -⟩ := InternalP.preserves hπ htp hy
      exact p_cont hS hfin hans hyf IH hco (hrπ.tail hy) hP' htc htp'
    · rcases y with ⟨σy, ty⟩
      obtain ⟨fy, cy, rfl, -⟩ := hxy
      obtain ⟨X', hstep, hst', hPs⟩ := hP.soft_back hlive hsoft
      have hy1 : σy = σ := hst'
      subst hy1
      obtain ⟨-, htps, -⟩ := InternalP.preserves hπ htp hstep
      exact p_cont hS hfin hans hyf IH hco (hrπ.tail hstep) hPs htc htps

/-- **The joint machine runs to the shared result**, for every profile. By induction on the
shared run: each step of the shared run is the image of joint steps (the forward image, or the
backward image of a `Soft` step). -/
theorem run_to_result (St : Static S) (hS : S.Scalar) (P : Profile) (ft : FnType)
    {σf : Store Nat} {tsf : Thread} {rs : Result} {v : Answer ft}
    (hfin : ResultAt σf tsf rs)
    (hans : Answer.ofResult? ft rs = some v) :
    ∀ x, Reach P x (σf, tsf) → ∀ js, JInv St P ft x js → JGoal St P ft v σf js := by
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro js hj
    cases js with
    | c κ₀ tc₀ κ tc π => exact run_c St hS P ft hfin hans .refl (.inl rfl) hj
    | p κ tc e π₀ π tp => exact run_p St hS P ft hfin hans .refl (.inl rfl) hj
  | @head x y hxy hyf ih =>
    intro js hj
    rcases x with ⟨σ, ts⟩
    have hn : Next St P ft v σf tsf (σ, ts) := .inr ⟨y, hxy, hyf, ih⟩
    cases js with
    | c κ₀ tc₀ κ tc π => exact run_c St hS P ft hfin hans (.head hxy hyf) hn hj
    | p κ tc e π₀ π tp => exact run_p St hS P ft hfin hans (.head hxy hyf) hn hj

/-! ### `⊆` -/

/-- The invariant between game states for `⊆`: typed, and the shared world never in the middle
of a run (it moves only at export calls and answers). -/
inductive GInvT (St : Static S) (P : Profile) :
    S.sharedI.HState → S.providerI.HState → S.consumerI.HState → Prop where
  | idle {σ π κ : Store Nat} (h : IdleT St σ π κ) : GInvT St P (.idle σ) (.idle π) (.idle κ)
  | run {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tc : Thread} (h : CRel St σ ts π κ tc)
      (hπ : StoreOk π) (htc : ThreadOk κ tc (resT f)) :
      GInvT St P (.running f σ ts) (.idle π) (.running f κ tc)

theorem path_append {I : ScalarInstance} {P : Profile} {q₁ q₂ q₃ : I.HState}
    {p₁ p₂ : List (Move I.E I.F)} (h₁ : I.Path P q₁ p₁ q₂) (h₂ : I.Path P q₂ p₂ q₃) :
    I.Path P q₁ (p₁ ++ p₂) q₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons ht _ ih => exact .cons ht (ih h₂)

/-- `⊆` at an export call: the consumer starts, the provider stays idle. -/
private theorem sub_call (St : Static S) (hS : S.Scalar) (P : Profile) {σ π κ : Store Nat}
    {f : S.sharedI.F.Op} {ps : List (Move S.sharedI.E S.sharedI.F)} (hI : IdleT St σ π κ)
    (ih : ∀ {qp : S.providerI.HState} {qc : S.consumerI.HState},
      GInvT St P (.running f σ (S.sharedI.initThread f)) qp qc →
      ∃ (pc : List (Move S.consumerI.E S.consumerI.F))
        (pp : List (Move S.providerI.E S.providerI.F)) (qc' : S.consumerI.HState)
        (qp' : S.providerI.HState),
        S.consumerI.Path P qc pc qc' ∧ S.providerI.Path P qp pp qp' ∧ lower pc = upper pp ∧
          upper pc = upper ps) :
    ∃ (pc : List (Move S.consumerI.E S.consumerI.F))
      (pp : List (Move S.providerI.E S.providerI.F)) (qc' : S.consumerI.HState)
      (qp' : S.providerI.HState),
      S.consumerI.Path P (.idle κ) pc qc' ∧ S.providerI.Path P (.idle π) pp qp' ∧
        lower pc = upper pp ∧ upper pc = upper (.inr (.ask f) :: ps) := by
  obtain ⟨⟨ρp, Op, ρc, Oc, hW⟩, hπ, hκ⟩ := hI
  have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
  obtain ⟨pc, pp, qc', qp', hpc, hpp, hproj, hpf⟩ :=
    ih (GInvT.run (Idle.start ⟨ρp, Op, ρc, Oc, hW⟩ f) hπ (hwc.init_typed f))
  refine ⟨.inr (.ask f) :: pc, pp, qc', qp',
    .cons (ScalarInstance.Trans.call (I := S.consumerI) (P := P) κ f) hpc, hpp, ?_, ?_⟩
  · simpa using hproj
  · simp only [upper_cons_inr, hpf]
    rfl

/-- `⊆` at an export answer: the joint machine runs to the shared result. -/
private theorem sub_oret (St : Static S) (hS : S.Scalar) (P : Profile)
    {f : S.sharedI.F.Op} {σ σ' π κ : Store Nat} {ts ts' tc : Thread} {r : Result}
    {v : S.sharedI.F.Ar f} {ps : List (Move S.sharedI.E S.sharedI.F)}
    (run : Reach P (σ, ts) (σ', ts')) (final : ResultAt σ' ts' r)
    (answer : Answer.ofResult? (S.sharedI.exports.get f.1) r = some v)
    (hR : CRel St σ ts π κ tc) (hπ : StoreOk π) (htc : ThreadOk κ tc (resT f))
    (ih : ∀ {qp : S.providerI.HState} {qc : S.consumerI.HState},
      GInvT St P (.idle σ') qp qc →
      ∃ (pc : List (Move S.consumerI.E S.consumerI.F))
        (pp : List (Move S.providerI.E S.providerI.F)) (qc' : S.consumerI.HState)
        (qp' : S.providerI.HState),
        S.consumerI.Path P qc pc qc' ∧ S.providerI.Path P qp pp qp' ∧ lower pc = upper pp ∧
          upper pc = upper ps) :
    ∃ (pc : List (Move S.consumerI.E S.consumerI.F))
      (pp : List (Move S.providerI.E S.providerI.F)) (qc' : S.consumerI.HState)
      (qp' : S.providerI.HState),
      S.consumerI.Path P (.running f κ tc) pc qc' ∧ S.providerI.Path P (.idle π) pp qp' ∧
        lower pc = upper pp ∧ upper pc = upper (.inr (.ans f v) :: ps) := by
  obtain ⟨evs, pp₁, κ', π', hrun, hpp₁, hproj₁, hI⟩ :=
    run_to_result St hS P (S.sharedI.exports.get f.1) final answer (σ, ts) run (.c κ tc κ tc π)
      ⟨.refl, hR, hπ, htc⟩
  have hpc₁ : S.consumerI.Path P (.running f κ tc)
      (evs.map .inl ++ [(.inr (.ans f v) : Move S.consumerI.E S.consumerI.F)]) (.idle κ') :=
    LRunTo.path hrun
  obtain ⟨pc₂, pp₂, qc', qp', hpc₂, hpp₂, hproj₂, hpf₂⟩ := ih (GInvT.idle hI)
  refine ⟨(evs.map .inl ++ [(.inr (.ans f v) : Move S.consumerI.E S.consumerI.F)]) ++ pc₂,
    pp₁ ++ pp₂, qc', qp', path_append hpc₁ hpc₂, path_append hpp₁ hpp₂, ?_, ?_⟩
  · simp only [lower_append, lower_map_inl, lower_cons_inr, lower_nil, List.append_nil]
    rw [hproj₁, hproj₂, upper_append]
    rfl
  · rw [upper_append, upper_append, hpf₂]
    simp only [upper_map_inl, upper_cons_inr, upper_nil, List.nil_append, List.singleton_append]
    rfl

/-- **`⊆`, core.** A play of the shared world is played by the consumer against the provider. -/
theorem sub_core (St : Static S) (hS : S.Scalar) (P : Profile) {qs qs' : S.sharedI.HState}
    {ps : List (Move S.sharedI.E S.sharedI.F)} (hs : S.sharedI.Path P qs ps qs') :
    ∀ {qp : S.providerI.HState} {qc : S.consumerI.HState}, GInvT St P qs qp qc →
      ∃ (pc : List (Move S.consumerI.E S.consumerI.F))
        (pp : List (Move S.providerI.E S.providerI.F)) (qc' : S.consumerI.HState)
        (qp' : S.providerI.HState),
        S.consumerI.Path P qc pc qc' ∧ S.providerI.Path P qp pp qp' ∧ lower pc = upper pp ∧
          upper pc = upper ps := by
  induction hs with
  | nil q =>
    intro qp qc _
    exact ⟨[], [], qc, qp, .nil _, .nil _, rfl, rfl⟩
  | cons ht hrest ih =>
    intro qp qc hg
    cases ht with
    | call σ f => cases hg with | idle hI => exact sub_call St hS P hI ih
    | oret run final answer =>
      cases hg with | run hR hπ htc => exact sub_oret St hS P run final answer hR hπ htc ih
    | @ucall _ _ _ _ _ _ _ e _ _ _ => exact emptySig_op_elim e
    | @uret _ _ _ e _ => exact emptySig_op_elim e

/-- **(B), given the static facts.** -/
theorem shared_eq_interact (St : Static S) (hS : S.Scalar) (P : Profile) :
    S.sharedI.objPlays P S.sc =
      interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs) := by
  apply Set.Subset.antisymm
  · rintro t ⟨ps, ⟨qs, hps⟩, rfl⟩
    obtain ⟨pc, pp, qc', qp', hpc, hpp, hproj, hpf⟩ := sub_core St hS P hps
      (GInvT.idle ⟨St.idle, hS.provider.storeOk, hS.consumer.storeOk⟩)
    exact ⟨pc, ⟨qc', hpc⟩, ⟨pp, ⟨qp', hpp⟩, hproj.symm⟩, hpf⟩
  · exact interact_subset St P

end Silmaril.Proofs.Wasm.Game.Linking.Split
