module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.GameSub
public import Silmaril.Proofs.Wasm.Game.Linking.Split.GameSup
public import Silmaril.Proofs.Wasm.Game.Linking.Shared
public import Silmaril.Wasm.Game.Start.Defs

/-!
# Static linking, separation: start functions

The start functions of a link run in the shared world (provider and consumer in one store)
before any export call. This module shows that they split as the separation of
`Silmaril.Proofs.Wasm.Game.Linking.Split` predicts, for **every profile**:

* the provider's start function runs alone in the provider part (`SRel`, the provider
  analogue of `CRel`): its runs in the provider world are runs of the shared world
  (`prov_start_fwd`) and conversely (`prov_start_back`, by induction on the shared run:
  the forward image of a provider step, or a `Soft` shared step, which is a provider step,
  `SRel.soft_back`); a returning start function leaves the three stores related with no call
  active (`IdleT`);
* the consumer's start function runs like an export call of the consumer: the shared run to a
  result is a run of the consumer through its stub calls, answered by provider activations
  (`cons_start_back`, from the generalised joint machine `run_to_result` at the type
  `startType`), and conversely (`LRun.sup`, the forward simulation of `GameSup` along a
  consumer run).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game
  Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Proofs.Wasm.Game.Linking

variable {S : Setup}

/-! ### Typing of a start invocation -/

/-- The instance with the single export `a` of type `startType`. -/
def startI (I : ScalarInstance) (a : Nat) : ScalarInstance := ⟨I.imports, [startType], [a], I.store⟩

theorem startI_wellFormed {I : ScalarInstance} {s : Store Nat} {a : Nat} (hw : I.WellFormed s)
    (ha : StartTyped s a) : (startI I a).WellFormed s where
  storeOk := hw.storeOk
  addrs_length := rfl
  export_type j := by
    obtain ⟨fi, hfi, hty⟩ := ha
    match j with
    | ⟨0, _⟩ => exact ⟨fi, hfi, hty⟩
  host_type := hw.host_type

/-- **A start invocation is typed** by the empty result type. -/
theorem start_typed {I : ScalarInstance} {s : Store Nat} {a : Nat} (hw : I.WellFormed s)
    (ha : StartTyped s a) : ThreadOk s (.pending a []) (resC startType) :=
  (startI_wellFormed hw ha).init_typed (I := startI I a) ⟨⟨0, Nat.zero_lt_one⟩, ⟨[], .nil⟩⟩

/-- A result typed by the empty result type is `values []`, a trap or an exception. -/
theorem result_of_start_typed {s : Store Nat} {t : Thread} {r : Result}
    (ht : ThreadOk s t (resC startType)) (hr : ResultAt s t r) :
    r = .values [] ∨ r = .trap ∨ ∃ a, r = .throw a := by
  cases r with
  | values vs =>
    have hcfg : t.config s = ⟨s, (t.config s).frame, vals vs⟩ := by
      have hcode : (t.config s).code = vals vs := hr
      rw [← hcode]
      exact Thread.config_eta s t
    have hok : ConfigOk ⟨s, (t.config s).frame, vals vs⟩ (resC startType) := by
      have h1 : ConfigOk (t.config s) (resC startType) := ht
      exact hcfg ▸ h1
    have hvs : List.Forall₂ (ValOk s) vs [] := vals_typed hok (fun _ h => by cases h)
    exact .inl (congrArg Result.values (List.forall₂_nil_right_iff.1 hvs))
  | trap => exact .inr (.inl rfl)
  | throw a => exact .inr (.inr ⟨a, rfl⟩)

/-! ### A provider thread running alone -/

/-- The provider runs a thread of its own (its start function), not called by the consumer;
the shared thread is the renamed provider thread. -/
def SRel (St : Static S) (σ : Store Nat) (ts : Thread) (π κ : Store Nat) (tp : Thread) : Prop :=
  ∃ ρp Op ρc Oc, World St σ π κ ρp Op ρc Oc ∧ Op.FrameGood (tp.config π).frame ∧
    Op.CodeGood (tp.config π).code ∧
    ts.config σ = ⟨σ, ρp.frame (tp.config π).frame, ρp.code (tp.config π).code⟩

/-- One provider step is one shared step. -/
theorem SRel.step {St : Static S} {P : Profile} {σ π π' κ : Store Nat} {ts tp tp' : Thread}
    (hR : SRel St σ ts π κ tp) (h : InternalP P (π, tp) (π', tp')) :
    ∃ σ' ts', InternalP P (σ, ts) (σ', ts') ∧ SRel St σ' ts' π' κ tp' := by
  obtain ⟨ρp, Op, ρc, Oc, hW, hf, hc, hts⟩ := hR
  have hfun : π'.funcs = π.funcs := InternalP.funcs_prefix h
  obtain ⟨f', c', rfl, hst⟩ := internal_config h
  obtain ⟨ρp', Op', σ', hst', hR', hf', hc', -, -, -⟩ := hW.rel.provider_step hf hc hst
  have hi : InternalP P (σ, ts) (σ', .active (ρp'.frame f') (ρp'.code c')) :=
    internal_of_step hts hst'
  refine ⟨σ', _, hi, ρp', Op', ρc, Oc, ⟨hR', ?_, ?_, hW.fκ⟩, hf', hc', rfl⟩
  · rw [InternalP.funcs_prefix hi, hW.fσ]
  · rw [hfun, hW.fπ]

/-- Provider runs are shared runs. -/
theorem SRel.reach {St : Static S} {P : Profile} {σ π π' κ : Store Nat} {ts tp tp' : Thread}
    (hR : SRel St σ ts π κ tp) (h : Reach P (π, tp) (π', tp')) :
    ∃ σ' ts', Reach P (σ, ts) (σ', ts') ∧ SRel St σ' ts' π' κ tp' := by
  generalize hx : (π, tp) = x at h
  generalize hy : (π', tp') = y at h
  induction h generalizing π' tp' with
  | refl => subst hx; cases hy; exact ⟨σ, ts, .refl, hR⟩
  | @tail y₁ y₂ _ hst ih =>
    subst hy
    obtain ⟨σ₁, ts₁, h₁, hR₁⟩ := ih (π' := y₁.1) (tp' := y₁.2) rfl
    obtain ⟨σ₂, ts₂, h₂, hR₂⟩ := hR₁.step hst
    exact ⟨σ₂, ts₂, h₁.tail h₂, hR₂⟩

/-- A `Soft` step of the shared world while the provider runs alone is a provider step. -/
theorem SRel.soft_back {St : Static S} {P : Profile} {σ π κ : Store Nat} {ts tp : Thread}
    (hR : SRel St σ ts π κ tp) {d : Config Nat} (hs : Choice.Soft P (ts.config σ) d) :
    ∃ X', InternalP P (π, tp) (π, .active (tp.config π).frame X') ∧ d.store = σ ∧
      SRel St σ (.active d.frame d.code) π κ (.active (tp.config π).frame X') := by
  obtain ⟨ρp, Op, ρc, Oc, hW, hf, hc, hts⟩ := hR
  obtain ⟨X', hstep, hd, hgood⟩ := ren_soft_back (p := π) hs hts hf hc
  have hstep' : Step P noHost (tp.config π) ⟨π, (tp.config π).frame, X'⟩ := by
    rw [Thread.config_eta π tp]
    exact hstep
  refine ⟨X', ⟨_, _, rfl, hstep'⟩, by rw [hd], ρp, Op, ρc, Oc, hW, hf, hgood, ?_⟩
  rw [active_config, hd]
  rfl

/-- **Result.** A result of the provider is (renamed) a result of the shared world, and the
stores are related with no call active. The provider never throws. -/
theorem SRel.result {St : Static S} {σ π κ : Store Nat} {ts tp : Thread} {r : Result}
    (hR : SRel St σ ts π κ tp) (hres : ResultAt π tp r) :
    (∀ a, r ≠ .throw a) ∧ (∃ ρ : Ren, ResultAt σ ts (ρ.result r)) ∧ Idle St σ π κ := by
  obtain ⟨ρp, Op, ρc, Oc, hW, hf, hc, hts⟩ := hR
  unfold ResultAt at hres ⊢
  have hnt : ∀ a, r ≠ .throw a := by
    rintro b rfl
    rw [hres] at hc
    exact Own.not_codeGood_throwing (a := b) hc (by simp [Result.toAdmin])
  refine ⟨hnt, ⟨ρp, ?_⟩, ρp, Op, ρc, Oc, hW⟩
  rw [hts]
  simp only
  rw [hres, Ren.result_toAdmin ρp r hnt]

/-- The provider world has no callout. -/
theorem SRel.no_callout {St : Static S} {P : Profile} {σ π κ : Store Nat} {ts tp : Thread}
    (hR : SRel St σ ts π κ tp) {h : Nat} {args : List Val} : statusP P π tp ≠ .callout h args := by
  intro hstat
  obtain ⟨ρp, Op, ρc, Oc, hW, -⟩ := hR
  obtain ⟨E, a, hd⟩ := statusP_callout_inv hstat
  obtain ⟨fi, -, -, -, hfi, hcode, -⟩ := decompose?_sound hd
  obtain ⟨c, hc⟩ := St.pwasm a fi (by rw [← hW.fπ]; exact hfi)
  exact absurd (hcode.symm.trans hc) (by simp)

/-- **Start.** An invocation of a provider function starts related threads. -/
theorem Idle.startProv {St : Static S} {σ π κ : Store Nat} (hI : Idle St σ π κ) {a : Nat}
    (hOp : St.Op.fn a) : SRel St σ (.pending a []) π κ (.pending a []) := by
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI
  have hOp' : Op.fn a := by rw [hW.rel.fnp]; exact hOp
  obtain ⟨fi, hfi, fi', hfi', hty, -⟩ := hW.rel.rp.fn _ hOp'
  refine ⟨ρp, Op, ρc, Oc, hW, Op.frameGood_empty, ?_, ?_⟩
  · simp only [Thread.config, invoke]
    exact Op.codeGood_append.mpr ⟨Op.codeGood_vals.mpr (fun _ h => by cases h),
      .cons_ref hOp' (Op.codeGood_single_callRefType _)⟩
  · simp only [Thread.config, invoke]
    rw [hfi, hfi']
    simp [hty]

/-- **Start.** An invocation of a consumer function (or stub) starts related threads. -/
theorem Idle.startCons {St : Static S} {σ π κ : Store Nat} (hI : Idle St σ π κ) {a : Nat}
    (hOc : St.Oc.fn a) : CRel St σ (.pending a []) π κ (.pending a []) := by
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI
  have hOc' : Oc.fn a := by rw [hW.rel.fnc]; exact hOc
  obtain ⟨fi, hfi, fi', hfi', hty, -⟩ := hW.rel.rc.fn _ hOc'
  refine ⟨ρp, Op, ρc, Oc, hW, Oc.frameGood_empty, ?_, ?_⟩
  · simp only [Thread.config, invoke]
    exact Oc.codeGood_append.mpr ⟨Oc.codeGood_vals.mpr (fun _ h => by cases h),
      .cons_ref hOc' (Oc.codeGood_single_callRefType _)⟩
  · simp only [Thread.config, invoke]
    rw [hfi, hfi']
    simp [hty]

/-! ### The provider's start function -/

/-- A start result is not renamed. -/
theorem ren_start_result {ρ : Ren} {r : Result}
    (hr : r = .values [] ∨ r = .trap ∨ ∃ a, r = .throw a) : ρ.result r = r := by
  rcases hr with rfl | rfl | ⟨a, rfl⟩ <;> rfl

/-- **The provider's start function, forward** (every profile): a run of the provider world
to a result is a run of the shared world to the same result, after which the stores are
related with no call active. -/
theorem prov_start_fwd {St : Static S} {P : Profile} {σ π π' κ : Store Nat} {ts tp tp' : Thread}
    {r : Result} (hR : SRel St σ ts π κ tp) (hr : r = .values [] ∨ r = .trap ∨ ∃ a, r = .throw a)
    (run : Reach P (π, tp) (π', tp')) (final : ResultAt π' tp' r) :
    ∃ σ' ts', Reach P (σ, ts) (σ', ts') ∧ ResultAt σ' ts' r ∧ Idle St σ' π' κ := by
  obtain ⟨σ', ts', hrun, hR'⟩ := hR.reach run
  obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := hR'.result final
  have hρ : ρ.result r = r := ren_start_result hr
  exact ⟨σ', ts', hrun, hρ ▸ hres, hI⟩

/-- The provider at a result: the shared world is at a renamed result. -/
private theorem prov_back_returned {St : Static S} {P : Profile} {σ π κ σf : Store Nat}
    {ts tp tsf : Thread} {rs r : Result} (hfin : ResultAt σf tsf rs)
    (hx : Reach P (σ, ts) (σf, tsf)) (hR : SRel St σ ts π κ tp)
    (htp : ThreadOk π tp (resC startType)) (hr : ResultAt π tp r) :
    ∃ π' tp', Reach P (π, tp) (π', tp') ∧ ResultAt π' tp' rs ∧ Idle St σf π' κ := by
  obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := hR.result hr
  have hxe : (σ, ts) = (σf, tsf) := reach_eq_of_normal hx (resultAt_no_internal hres)
  have hσ : σ = σf ∧ ts = tsf := Prod.mk.inj hxe
  have hres' : ResultAt σf tsf (ρ.result r) := hσ.1 ▸ hσ.2 ▸ hres
  have hρ : ρ.result r = r := ren_start_result (result_of_start_typed htp hr)
  have hrr : r = rs := hρ ▸ resultAt_unique hres' hfin
  exact ⟨π, tp, .refl, hrr ▸ hr, hσ.1 ▸ hI⟩

/-- A returned thread is at a result. -/
theorem status_result {P : Profile} {π : Store Nat} {tp : Thread} {cr : CallResult}
    (h : statusP P π tp = .returned cr) : ∃ r, ResultAt π tp r := by
  cases cr with
  | values vs => exact ⟨.values vs, statusP_returned_values h⟩
  | trap =>
    rcases statusP_returned_trap_inv h with h' | ⟨a, h'⟩
    · exact ⟨.trap, h'⟩
    · exact ⟨.throw a, h'⟩

/-- What `prov_start_back` produces from the provider thread `(π, tp)`. -/
def ProvBack (St : Static S) (P : Profile) (σf : Store Nat) (rs : Result) (π κ : Store Nat)
    (tp : Thread) : Prop :=
  ∃ π' tp', Reach P (π, tp) (π', tp') ∧ ResultAt π' tp' rs ∧ Idle St σf π' κ

/-- `prov_start_back` at the end of the shared run. -/
theorem prov_back_end {St : Static S} {P : Profile} {σf π κ : Store Nat} {tsf tp : Thread}
    {rs : Result} (hfin : ResultAt σf tsf rs) (hR : SRel St σf tsf π κ tp)
    (htp : ThreadOk π tp (resC startType)) : ProvBack St P σf rs π κ tp := by
  have hπ : StoreOk π := threadOk_storeOk htp
  cases hstat : statusP P π tp with
  | returned cr =>
    obtain ⟨r, hr⟩ := status_result hstat
    exact prov_back_returned hfin .refl hR htp hr
  | stuck => exact absurd hstat (statusP_ne_stuck hπ htp)
  | callout h args => exact absurd hstat hR.no_callout
  | running =>
    obtain ⟨⟨π₁, tp₁⟩, hy⟩ := statusP_running_inv hstat
    obtain ⟨σ₁, ts₁, hx₁, -⟩ := hR.step hy
    exact absurd hx₁ (resultAt_no_internal hfin _)

/-- A `Soft` shared step, while the provider runs alone, is a provider step. -/
theorem prov_back_soft {St : Static S} {P : Profile} {σ π κ : Store Nat} {ts tp : Thread}
    {y : Store Nat × Thread} (hxy : InternalP P (σ, ts) y) (hR : SRel St σ ts π κ tp)
    (hsoft : Choice.Soft P (ts.config σ) (y.2.config y.1)) :
    ∃ X', InternalP P (π, tp) (π, .active (tp.config π).frame X') ∧
      SRel St y.1 y.2 π κ (.active (tp.config π).frame X') := by
  rcases y with ⟨σy, ty⟩
  obtain ⟨fy, cy, rfl, -⟩ := hxy
  obtain ⟨X', hstep, hst, hRs⟩ := hR.soft_back hsoft
  have hy1 : σy = σ := hst
  subst hy1
  exact ⟨X', hstep, hRs⟩

/-- `prov_start_back` for a running provider: the shared step is the forward image of its step,
or a `Soft` step, which is a provider step. -/
theorem prov_back_running {St : Static S} {P : Profile} {σ σf π κ : Store Nat} {ts tp : Thread}
    {rs : Result} {y : Store Nat × Thread} (hxy : InternalP P (σ, ts) y)
    (hR : SRel St σ ts π κ tp) (htp : ThreadOk π tp (resC startType))
    (ih : ∀ {π κ : Store Nat} {tp : Thread}, SRel St y.1 y.2 π κ tp →
      ThreadOk π tp (resC startType) → ProvBack St P σf rs π κ tp)
    {π₁ : Store Nat} {tp₁ : Thread} (hy : InternalP P (π, tp) (π₁, tp₁)) :
    ProvBack St P σf rs π κ tp := by
  have hπ : StoreOk π := threadOk_storeOk htp
  obtain ⟨σ₁, ts₁, hx₁, hR₁⟩ := hR.step hy
  rcases next_eq_or_soft hxy hx₁ with rfl | hsoft
  · have htp₁ : ThreadOk π₁ tp₁ (resC startType) := (InternalP.preserves hπ htp hy).2.1
    obtain ⟨π', tp', hr', hres', hI'⟩ := ih hR₁ htp₁
    exact ⟨π', tp', .head hy hr', hres', hI'⟩
  · obtain ⟨X', hstep, hRs⟩ := prov_back_soft hxy hR hsoft
    have htps : ThreadOk π (.active (tp.config π).frame X') (resC startType) :=
      (InternalP.preserves hπ htp hstep).2.1
    obtain ⟨π', tp', hr', hres', hI'⟩ := ih hRs htps
    exact ⟨π', tp', .head hstep hr', hres', hI'⟩

/-- **The provider's start function, backward** (every profile): a run of the shared world to
a result, from a configuration related to a provider thread, is a run of the provider world
to the same result, after which the stores are related with no call active. By induction on
the shared run: each shared step is the forward image of a provider step, or a `Soft` step,
which is a provider step (`SRel.soft_back`). -/
theorem prov_start_back (St : Static S) (P : Profile) {σf : Store Nat} {tsf : Thread}
    {rs : Result} (hfin : ResultAt σf tsf rs) :
    ∀ x, Reach P x (σf, tsf) → ∀ {π κ : Store Nat} {tp : Thread}, SRel St x.1 x.2 π κ tp →
      ThreadOk π tp (resC startType) →
      ∃ π' tp', Reach P (π, tp) (π', tp') ∧ ResultAt π' tp' rs ∧ Idle St σf π' κ := by
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hR htp => prov_back_end hfin hR htp
  | @head x y hxy hyf ih =>
    intro π κ tp hR htp
    show ProvBack St P σf rs π κ tp
    have hπ : StoreOk π := threadOk_storeOk htp
    cases hstat : statusP P π tp with
    | returned cr =>
      obtain ⟨r, hr⟩ := status_result hstat
      obtain ⟨-, ⟨ρ, hres⟩, -⟩ := hR.result hr
      exact absurd hxy (resultAt_no_internal hres y)
    | stuck => exact absurd hstat (statusP_ne_stuck hπ htp)
    | callout h args => exact absurd hstat hR.no_callout
    | running =>
      obtain ⟨⟨π₁, tp₁⟩, hy⟩ := statusP_running_inv hstat
      exact prov_back_running hxy hR htp ih hy

/-! ### The consumer's start function -/

/-- **The consumer's start function, backward** (every profile): a run of the shared world
from the consumer's start invocation to a result is a run of the consumer through stub calls,
answered by a play of the provider, to the same result (`run_to_result` at `startType`). -/
theorem cons_start_back (St : Static S) (hS : S.Scalar) (P : Profile) {σ π κ σf : Store Nat}
    {tsf : Thread} {rs : Result} {a : Nat} (hI : IdleT St σ π κ) (hOc : St.Oc.fn a)
    (hty : ThreadOk κ (.pending a []) (resC startType))
    (run : Reach P (σ, .pending a []) (σf, tsf)) (hfin : ResultAt σf tsf rs)
    {v : Answer startType} (hans : Answer.ofResult? startType rs = some v) :
    ∃ (evs : List (Ev S.consumerI.E)) (pp : List (Move S.providerI.E S.providerI.F))
      (κ' π' : Store Nat),
      LRunTo S.consumerI P (κ, .pending a []) evs startType v κ' ∧
      S.providerI.Path P (.idle π) pp (.idle π') ∧ evs = upper pp ∧ IdleT St σf π' κ' :=
  run_to_result St hS P startType hfin hans (σ, .pending a []) run
    (.c κ (.pending a []) κ (.pending a []) π) ⟨.refl, hI.1.startCons hOc, hI.2.1, hty⟩

/-- A play of the closed provider with no events is empty. -/
theorem provider_path_nil {P : Profile} {π : Store Nat} {qp : S.providerI.HState}
    {pp : List (Move S.providerI.E S.providerI.F)} (hp : S.providerI.Path P (.idle π) pp qp)
    (hu : upper pp = []) : pp = [] ∧ qp = .idle π := by
  cases pp with
  | nil => cases hp; exact ⟨rfl, rfl⟩
  | cons m pp' =>
    obtain ⟨f, rfl, -⟩ := path_idle_cons hp
    simp at hu

/-- A play of the closed provider starting with the events of one call is that activation,
then the rest. -/
theorem split_activation {P : Profile} {π : Store Nat}
    {pp : List (Move S.providerI.E S.providerI.F)} {q : S.providerI.HState}
    {e : S.consumerI.E.Op} {w : S.consumerI.E.Ar e} {l : List (Ev S.consumerI.E)}
    (hp : S.providerI.Path P (.idle π) pp q)
    (hu : upper pp = (.ask e :: .ans e w :: l : List (Ev S.consumerI.E))) :
    ∃ π₁ rest, pp = .inr (.ask e) :: .inr (.ans e w) :: rest ∧
      S.providerI.Path P (.idle π) [.inr (.ask e), .inr (.ans e w)] (.idle π₁) ∧
      S.providerI.Path P (.idle π₁) rest q ∧ upper rest = l := by
  match pp, hp, hu with
  | [], _, hu => cases hu
  | [m], hp, hu =>
    obtain ⟨f, rfl, -⟩ := path_idle_cons hp
    exact absurd (List.cons.inj (hu : [Ev.ask f] = _)).2 (List.cons_ne_nil _ _).symm
  | m :: n :: rest, hp, hu =>
    obtain ⟨f, v, π₁, rfl, rfl, hc, hrest⟩ :=
      ScalarInstance.path_cons_cons_closed (I := S.providerI) rfl hp
    have hu' : (Ev.ask f :: Ev.ans f v :: upper rest : List (Ev S.providerI.F)) =
        Ev.ask e :: Ev.ans e w :: l := hu
    obtain ⟨h₁, hu₂⟩ := List.cons.inj hu'
    obtain ⟨h₂, hu₃⟩ := List.cons.inj hu₂
    have hef : f = e := Ev.ask.inj h₁
    subst hef
    have hvw : v = w := eq_of_heq (Ev.ans.inj h₂).2
    subst hvw
    exact ⟨π₁, rest, rfl, hc, hrest, hu₃⟩

/-- A stub call answered by a complete provider activation is a shared run back to the
consumer. -/
theorem stub_call_sup (St : Static S) {P : Profile} {σ π π₁ s : Store Nat} {ts t : Thread}
    {e : S.consumerI.E.Op} {w : S.consumerI.E.Ar e} (hR : CRel St σ ts π s t)
    (hco : CalloutAt s t e.1 e.2.1)
    (hc : S.providerI.Path P (.idle π) [.inr (.ask e), .inr (.ans e w)] (.idle π₁)) :
    ∃ σ' ts', Reach P (σ, ts) (σ', ts') ∧
      CRel St σ' ts' π₁ s (resumeResult s t (Answer.toResult (ft := S.consumerI.imports.get e.1) w)) := by
  obtain ⟨tp', r, prun, final, answer⟩ := ScalarInstance.path_pair_iff.mp hc
  obtain ⟨hlt, tp₀, ts₂, hp₀, hs₂, hP, -⟩ := hR.call (P := P) hco e.2.2
  have hrun : Reach P (π, tp₀) (π₁, tp') :=
    reach_of_unique_step (fun _ hy => InternalP.pending_unique hy hp₀) prun
      (resultAt_no_internal final) hp₀
  obtain ⟨σ₃, ts₃, hr₃, hP₃⟩ := hP.reach hrun
  obtain ⟨-, hC⟩ := hP₃.ret final (fun vs hvs => ⟨_, ofResult?_values (hvs ▸ answer)⟩)
  have hC' : CRel St σ₃ ts₃ π₁ s
      (resumeResult s t (Answer.toResult (ft := S.consumerI.imports.get e.1) w)) :=
    (ofResult?_toResult' answer).symm ▸ hC
  exact ⟨σ₃, ts₃, .head hs₂ hr₃, hC'⟩

/-- **The consumer's start function, forward** (every profile): a run of the consumer through
stub calls, answered by a play of the provider, is a run of the shared world, after which the
consumer's thread is still related to the shared one. -/
theorem LRun.sup (St : Static S) {P : Profile} {x y : Store Nat × Thread}
    {evs : List (Ev S.consumerI.E)} (hl : LRun S.consumerI P x evs y) :
    ∀ {σ π π' : Store Nat} {ts : Thread} {pp : List (Move S.providerI.E S.providerI.F)},
      CRel St σ ts π x.1 x.2 → S.providerI.Path P (.idle π) pp (.idle π') → evs = upper pp →
      ∃ σ' ts', Reach P (σ, ts) (σ', ts') ∧ CRel St σ' ts' π' y.1 y.2 := by
  induction hl with
  | done run =>
    intro σ π π' ts pp hR hp hproj
    obtain ⟨-, hq⟩ := provider_path_nil hp hproj.symm
    cases hq
    exact hR.reach run
  | @call x y s t h args e w l run callout op _ ih =>
    intro σ π π' ts pp hR hp hproj
    show ∃ σ' ts', Reach P (σ, ts) (σ', ts') ∧ CRel St σ' ts' π' y.1 y.2
    obtain ⟨σ₁, ts₁, hr₁, hR₁⟩ := hR.reach run
    obtain ⟨h1, h2⟩ := ifaceOp?_eq op
    have hco : CalloutAt s t e.1 e.2.1 := by rw [h1, h2]; exact callout
    have hu : upper pp = (.ask e :: .ans e w :: l : List (Ev S.consumerI.E)) := hproj.symm
    obtain ⟨π₁, rest, -, hc, hrest, hur⟩ := split_activation hp hu
    obtain ⟨σ₂, ts₂, hr₂, hR₂⟩ := stub_call_sup St hR₁ hco hc
    obtain ⟨σ', ts', hr', hR'⟩ := ih hR₂ hrest hur.symm
    exact ⟨σ', ts', (hr₁.trans hr₂).trans hr', hR'⟩

end Silmaril.Proofs.Wasm.Game.Linking.Split
