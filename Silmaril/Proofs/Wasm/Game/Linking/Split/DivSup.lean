module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.GameSup
public import Silmaril.Proofs.Wasm.Game.Linking.Split.Init
public import Silmaril.Proofs.Wasm.Game.Linking.DivShared

/-!
# Static linking, separation: the composite system is simulated by the shared world,
divergence observed

The composite transition system of the provider and the consumer
(`(S.providerI.dlts P S.sp).comp (S.consumerI.dlts P S.scs)`, the import interface of the
consumer synchronised with the export interface of the provider and hidden) is simulated by the
shared world `S.sharedI.dlts P S.sc` **divergence-sensitively** (`LTS.DivSimulation`), for every
profile (`compSim`):

* a provider or consumer host-free step is one shared step (`CRel.step`, `PRel.step`); the
  provider's first step from its `$invoke` is the shared `call_ref` step of the consumer's
  callout (`CRel.call`, unique by `InternalP.pending_unique`);
* the two synchronisations (the consumer's import call accepted by the idle provider, and the
  provider's answer resuming the consumer) take **no** shared step; they decrease the measure
  `rank` (consumer at a callout `1` to provider pending `0`; provider running `2` to consumer
  resumed `1`), so a run cannot synchronise forever without shared steps;
* export calls and answers of the consumer are those of the shared world (`Idle.start`,
  `CRel.result`).

The related states are those of `GInv` of `GameSup`, made step-wise (`CS`).

New proofs (the step lemmas are those of `Split/Joint.lean`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Proofs.Wasm.Game.Linking

variable {S : Setup}

/-- The thread is not a pending invocation. -/
def NotPending (t : Thread) : Prop := ∀ a args, t ≠ .pending a args

/-- The target thread of a host-free step is not pending. -/
theorem notPending_of_internal {P : Profile} {x : Store Nat × Thread} {s' : Store Nat}
    {t' : Thread} (h : InternalP P x (s', t')) : NotPending t' := by
  obtain ⟨f', c', he, -⟩ := h
  intro a args hp
  rw [hp] at he
  cases he

/-- The states of the composite system related to states of the shared world. -/
inductive CS (St : Static S) :
    S.providerI.HState × S.consumerI.HState → S.sharedI.HState → Prop where
  | idle {σ π κ : Store Nat} (h : Idle St σ π κ) : CS St (.idle π, .idle κ) (.idle σ)
  | run {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tc : Thread}
      (h : CRel St σ ts π κ tc) : CS St (.idle π, .running f κ tc) (.running f σ ts)
  | call {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tc : Thread} {e : S.consumerI.E.Op}
      (h : CRel St σ ts π κ tc) (hco : CalloutAt κ tc e.1 e.2.1) :
      CS St (.running e π (S.providerI.initThread e), .waiting f κ tc e) (.running f σ ts)
  | prov {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
      (h : PRel St σ ts π tp κ tc e.1 e.2.1) (hnp : NotPending tp) :
      CS St (.running e π tp, .waiting f κ tc e) (.running f σ ts)

/-- The measure of the synchronisations. -/
def rank : S.providerI.HState × S.consumerI.HState → Nat
  | (.running _ _ (.pending _ _), _) => 0
  | (.running _ _ (.active _ _), _) => 2
  | (.idle _, .running _ _ _) => 1
  | _ => 0

/-- The measure order. -/
def RankLt (x y : S.providerI.HState × S.consumerI.HState) : Prop := rank x < rank y

theorem rankLt_wf : WellFounded (RankLt (S := S)) := InvImage.wf rank Nat.lt_wfRel.wf

theorem rank_prov {e : S.providerI.F.Op} {π : Store Nat} {tp : Thread}
    {qc : S.consumerI.HState} (hnp : NotPending tp) : rank (S := S) (.running e π tp, qc) = 2 := by
  cases tp with
  | pending a args => exact absurd rfl (hnp a args)
  | active f c => rfl

/-- The composite system. -/
noncomputable abbrev Comp (P : Profile) :
    LTS S.providerI.E S.consumerI.F :=
  (S.providerI.dlts P S.sp).comp (S.consumerI.dlts P S.scs)

/-- The outcome of a composite step: matched by shared steps, or by none while the measure
decreases. -/
def Matched (St : Static S) (P : Profile) (x' : S.providerI.HState × S.consumerI.HState)
    (x : S.providerI.HState × S.consumerI.HState) (y : S.sharedI.HState) : Prop :=
  (∃ y', Relation.TransGen (S.sharedI.dlts P S.sc).Silent y y' ∧ CS St x' y') ∨
    (CS St x' y ∧ RankLt x' x)

/-! ### Silent steps -/

/-- A consumer step. -/
theorem tau_consumer {St : Static S} {P : Profile} {xp : S.providerI.HState}
    {xc xc' : S.consumerI.HState} {y : S.sharedI.HState} (hR : CS St (xp, xc) y)
    (h : S.consumerI.DTrans P xc none xc') : Matched St P (xp, xc') (xp, xc) y := by
  cases h with
  | tau hi =>
    cases hR with
    | run hC =>
      obtain ⟨σ', ts', hi', hC'⟩ := hC.step hi
      exact .inl ⟨_, .single (ScalarInstance.DTrans.tau (I := S.sharedI) hi'), .run hC'⟩

/-- A provider step. -/
theorem tau_provider {St : Static S} {P : Profile} {xp xp' : S.providerI.HState}
    {xc : S.consumerI.HState} {y : S.sharedI.HState} (hR : CS St (xp, xc) y)
    (h : S.providerI.DTrans P xp none xp') : Matched St P (xp', xc) (xp, xc) y := by
  cases h with
  | @tau e π π' tp tp' hi =>
    cases hR with
    | @call f σ _ κ ts tc _ hC hco =>
      obtain ⟨hlt, tp₀, ts', hp₀, hs', hP, -⟩ := hC.call (P := P) hco e.2.2
      have hp₀' : InternalP P (π, S.providerI.initThread e) (π, tp₀) := hp₀
      have he : (π', tp') = (π, tp₀) := InternalP.pending_unique hi hp₀'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact .inl ⟨_, .single (ScalarInstance.DTrans.tau (I := S.sharedI) hs'),
        .prov hP (notPending_of_internal hp₀')⟩
    | prov hP hnp =>
      obtain ⟨σ', ts', hi', hP'⟩ := hP.step hi
      exact .inl ⟨_, .single (ScalarInstance.DTrans.tau (I := S.sharedI) hi'),
        .prov hP' (notPending_of_internal hi)⟩

/-- The consumer's import call accepted by the provider: no shared step. -/
theorem sync_ask {St : Static S} {P : Profile} {xp xp' : S.providerI.HState}
    {xc xc' : S.consumerI.HState} {y : S.sharedI.HState} {e : S.consumerI.E.Op}
    (hR : CS St (xp, xc) y) (hp : S.providerI.DTrans P xp (some (.inr (.ask e))) xp')
    (hc : S.consumerI.DTrans P xc (some (.inl (.ask e))) xc') :
    Matched St P (xp', xc') (xp, xc) y := by
  cases hp with
  | call π _ =>
    cases hc with
    | @ucall f κ tc h args _ callout op =>
      cases hR with
      | run hC =>
        obtain ⟨h1, h2⟩ := ifaceOp?_eq op
        have hco : CalloutAt κ tc e.1 e.2.1 := by rw [h1, h2]; exact callout
        exact .inr ⟨.call hC hco, Nat.zero_lt_one⟩

/-- The provider's answer resuming the consumer: no shared step. -/
theorem sync_ans {St : Static S} {P : Profile} {xp xp' : S.providerI.HState}
    {xc xc' : S.consumerI.HState} {y : S.sharedI.HState} {e : S.consumerI.E.Op}
    {v : S.consumerI.E.Ar e}
    (hR : CS St (xp, xc) y) (hp : S.providerI.DTrans P xp (some (.inr (.ans e v))) xp')
    (hc : S.consumerI.DTrans P xc (some (.inl (.ans e v))) xc') :
    Matched St P (xp', xc') (xp, xc) y := by
  cases hp with
  | @oret _ π tp r _ final answer =>
    cases hc with
    | uret _ =>
      cases hR with
      | call hC hco =>
        obtain ⟨hlt, tp₀, ts', hp₀, hs', hP', hnr⟩ := hC.call (P := P) hco e.2.2
        have hp₀' : InternalP P (π, S.providerI.initThread e) (π, tp₀) := hp₀
        exact absurd hp₀' (resultAt_no_internal final _)
      | prov hP hnp =>
        obtain ⟨-, hC⟩ := hP.ret final (fun vs hvs => ⟨_, ofResult?_values (hvs ▸ answer)⟩)
        have hC' := (ofResult?_toResult' answer).symm ▸ hC
        refine .inr ⟨.run hC', ?_⟩
        show rank _ < rank _
        cases tp with
        | pending a args => exact absurd rfl (hnp a args)
        | active _ _ => exact Nat.one_lt_two

/-- **Silent steps of the composite system** are matched divergence-sensitively. -/
theorem comp_tau {St : Static S} {P : Profile} {x x' : S.providerI.HState × S.consumerI.HState}
    {y : S.sharedI.HState} (hR : CS St x y) (h : (Comp (S := S) P).step x none x') :
    Matched St P x' x y := by
  rcases x with ⟨xp, xc⟩
  have h' : LTS.CompStep (S.providerI.dlts P S.sp) (S.consumerI.dlts P S.scs) (xp, xc) none x' := h
  cases h' with
  | tau₁ hp => exact tau_provider hR hp
  | tau₂ hc => exact tau_consumer hR hc
  | sync g hp hc =>
    cases g with
    | ask e => exact sync_ask hR hp hc
    | ans e v => exact sync_ans hR hp hc

/-! ### Visible steps -/

/-- **Visible steps of the composite system** are visible steps of the shared world. -/
theorem comp_vis {St : Static S} {P : Profile} {x x' : S.providerI.HState × S.consumerI.HState}
    {y : S.sharedI.HState} {o : Move S.providerI.E S.consumerI.F} (hR : CS St x y)
    (h : (Comp (S := S) P).step x (some o) x') :
    ∃ y', S.sharedI.DTrans P y (some o) y' ∧ CS St x' y' := by
  rcases x with ⟨xp, xc⟩
  have h' : LTS.CompStep (S.providerI.dlts P S.sp) (S.consumerI.dlts P S.scs) (xp, xc) (some o)
      x' := h
  cases h' with
  | left e hp => exact DivShared.closed_op_elim (by cases e <;> assumption)
  | right g hc =>
    cases hc with
    | call κ f =>
      cases hR with
      | idle hI => exact ⟨_, ScalarInstance.DTrans.call (I := S.sharedI) _ f, .run (hI.start f)⟩
    | @oret f κ tc r v final answer =>
      cases hR with
      | @run _ σ _ _ ts _ hC =>
        obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := hC.result final
        have hres' : ResultAt σ ts r := by
          simpa only [ren_result_of_ofResult? answer ρ] using hres
        exact ⟨_, ScalarInstance.DTrans.oret (I := S.sharedI) hres' answer, .idle hI⟩

/-! ### The simulation -/

/-- A silent run as a run without visible moves. -/
theorem run_of_transGen {E F : Sig.{0}} {L : LTS E F} {y y' : L.State}
    (h : Relation.TransGen L.Silent y y') : L.Run y [] y' := by
  induction h with
  | single hs => exact .tau hs (.nil _)
  | tail _ hs ih => exact ih.append (.tau hs (.nil _))

/-- **The composite system is simulated by the shared world, divergence-sensitively.** -/
noncomputable def compSim (St : Static S) (P : Profile) :
    LTS.DivSimulation (Comp (S := S) P) (S.sharedI.dlts P S.sc) where
  R := CS St
  init := .idle St.idle
  step {x x' y l} hR h := by
    cases l with
    | none =>
      rcases comp_tau hR h with ⟨y', hy', hR'⟩ | ⟨hR', -⟩
      · exact ⟨y', run_of_transGen hy', hR'⟩
      · exact ⟨y, .nil _, hR'⟩
    | some o =>
      obtain ⟨y', hy', hR'⟩ := comp_vis hR h
      exact ⟨y', .vis hy' (.nil _), hR'⟩
  lt := RankLt
  wf := rankLt_wf
  tau hR h := comp_tau hR h

/-- **Divergence-aware `⊇` of step (B)**: the divergence-observing strategy of the composite
system refines that of the shared world (plays, divergences, infinite plays). -/
theorem comp_le_shared (hS : S.Scalar) (P : Profile) :
    DStrategy.ofLTS (Comp (S := S) P) ≤ S.sharedI.dstrategy P S.sc :=
  (static_nonempty S hS).elim fun St => (compSim St P).ofLTS_le

end Silmaril.Proofs.Wasm.Game.Linking.Split
