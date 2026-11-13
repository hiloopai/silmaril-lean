module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Machine
public import Silmaril.Wasm.Game.Start.Defs

/-!
# Strategies with an instantiation phase under global-address embeddings

`instStrategyT_emb`: the divergence-observing strategy of an instance whose instantiation phase
runs the thread `t₀` from the store `s` (`ScalarInstance.instStrategyT`, used for the
specification's `$instantiate` configuration by `ScalarInstance.specStrategy`) equals the one
running the renamed thread `thread ι t₀` from an embedding `t` of `s` (`Emb ι Univ s t`,
`ι` injective), for every profile. The proof is the lock-step simulation of
`Silmaril.Proofs.Wasm.Game.SpecGlobals.Machine` lifted to the states of an instantiable system
(`InstSystem.St`): instantiation configurations, import continuations, persisted stores and
export calls are related by renaming threads.

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace InstPhase

variable (I : ScalarInstance) (P : Profile) (ι : Nat → Nat)

/-- Related machine states: embedded stores, renamed threads. -/
def PR (x y : Store Nat × Thread) : Prop := Emb ι Univ x.1 y.1 ∧ y.2 = thread ι x.2

/-- Related states of the instantiable systems at `s` and at an embedding. -/
inductive Rel {s t : Store Nat} {t₀ t₁ : Thread} :
    (I.instSysT P s t₀).St → (I.instSysT P t t₁).St → Prop where
  | fresh : Rel .fresh .fresh
  | inst {c d : Store Nat × Thread} (h : PR ι c d) : Rel (.inst c) (.inst d)
  | iwait {m : I.E.Op} {k k' : I.E.Ar m → Store Nat × Thread} (h : ∀ n, PR ι (k n) (k' n)) :
      Rel (.iwait m k) (.iwait m k')
  | ready {st st' : Store Nat} (h : Emb ι Univ st st') : Rel (.ready st) (.ready st')
  | run {q : I.F.Op} {c d : Store Nat × Thread} (h : PR ι c d) : Rel (.run q c) (.run q d)
  | wait {q : I.F.Op} {m : I.E.Op} {k k' : I.E.Ar m → Store Nat × Thread}
      (h : ∀ n, PR ι (k n) (k' n)) : Rel (.wait q m k) (.wait q m k')
  | dead : Rel .dead .dead

variable {I P ι} {κ : Nat → Nat}

theorem calls_fwd (hκ : ∀ a, κ (ι a) = a) {c d : Store Nat × Thread} (h : PR ι c d)
    {e : I.E.Op} (hc : I.CallsOut c e) :
    I.CallsOut d e ∧ ∀ n, PR ι (I.resumeK c.1 c.2 e n) (I.resumeK d.1 d.2 e n) := by
  obtain ⟨hco, args, hat, hop⟩ := hc
  have hd : d.2 = thread ι c.2 := h.2
  refine ⟨⟨hco, args, hd ▸ calloutAt_emb h.1 hat, hop⟩, fun n => ⟨h.1, ?_⟩⟩
  show resumeResult d.1 d.2 _ = thread ι (resumeResult c.1 c.2 _)
  rw [hd, resumeResult_emb _ hκ h.1]

theorem calls_bwd (hκ : ∀ a, κ (ι a) = a) {c d : Store Nat × Thread} (h : PR ι c d)
    {e : I.E.Op} (hc : I.CallsOut d e) :
    I.CallsOut c e ∧ ∀ n, PR ι (I.resumeK c.1 c.2 e n) (I.resumeK d.1 d.2 e n) := by
  obtain ⟨hco, args, hat, hop⟩ := hc
  have hd : d.2 = thread ι c.2 := h.2
  have hat' : CalloutAt c.1 c.2 hco args := calloutAt_back hκ h.1 (hd ▸ hat)
  have hs : I.CallsOut c e := ⟨hco, args, hat', hop⟩
  exact ⟨hs, (calls_fwd hκ h hs).2⟩

theorem result_fwd {c d : Store Nat × Thread} (h : PR ι c d) {r : Result}
    (hr : ResultAt c.1 c.2 r) : ResultAt d.1 d.2 r := by
  rw [h.2]
  exact resultAt_emb h.1 hr

theorem result_bwd (hκ : ∀ a, κ (ι a) = a) {c d : Store Nat × Thread} (h : PR ι c d) {r : Result}
    (hr : ResultAt d.1 d.2 r) : ResultAt c.1 c.2 r := by
  rw [h.2] at hr
  exact resultAt_back hκ h.1 hr

theorem failed_fwd {c d : Store Nat × Thread} (h : PR ι c d) {b : Behaviour Val}
    (hf : StartFailed c b) : StartFailed d b := by
  rcases hf with ⟨hr, hb⟩ | ⟨a, hr, hb⟩
  · exact .inl ⟨result_fwd h hr, hb⟩
  · exact .inr ⟨a, result_fwd h hr, hb⟩

theorem failed_bwd (hκ : ∀ a, κ (ι a) = a) {c d : Store Nat × Thread} (h : PR ι c d)
    {b : Behaviour Val} (hf : StartFailed d b) : StartFailed c b := by
  rcases hf with ⟨hr, hb⟩ | ⟨a, hr, hb⟩
  · exact .inl ⟨result_bwd hκ h hr, hb⟩
  · exact .inr ⟨a, result_bwd hκ h hr, hb⟩

theorem internal_fwd {c d c' : Store Nat × Thread} (h : PR ι c d) (hi : InternalP P c c') :
    ∃ d', InternalP P d d' ∧ PR ι c' d' := by
  obtain ⟨s, th⟩ := c
  obtain ⟨t, th₁⟩ := d
  obtain ⟨s', th'⟩ := c'
  obtain ⟨he, rfl⟩ := h
  obtain ⟨t', hi', he'⟩ := internal_emb he hi
  exact ⟨(t', thread ι th'), hi', he', rfl⟩

theorem internal_bwd (hκ : ∀ a, κ (ι a) = a) {c d d' : Store Nat × Thread} (h : PR ι c d)
    (hi : InternalP P d d') : ∃ c', InternalP P c c' ∧ PR ι c' d' := by
  obtain ⟨s, th⟩ := c
  obtain ⟨t, th₁⟩ := d
  obtain ⟨t', th₂⟩ := d'
  obtain ⟨he, rfl⟩ := h
  obtain ⟨s', th', hth, hi', he'⟩ := internal_back hκ he hi
  exact ⟨(s', th'), hi', he', hth⟩

theorem pr_start (q : I.F.Op) {st st' : Store Nat} (h : Emb ι Univ st st') :
    PR ι (st, I.initThread q) (st', I.initThread q) := ⟨h, rfl⟩

variable {s t : Store Nat} {t₀ : Thread}

/-- Transitions at `s` are matched at the embedding. -/
theorem fwd_step (he₀ : Emb ι Univ s t) (hκ : ∀ a, κ (ι a) = a) {x x' : (I.instSysT P s t₀).St}
    {y : (I.instSysT P t (thread ι t₀)).St} {l : Option (Move I.E (I.F.withInst (Behaviour Val)))}
    (hR : Rel I P ι x y) (h : (I.instSysT P s t₀).Step x l x') :
    ∃ y', (I.instSysT P t (thread ι t₀)).Step y l y' ∧ Rel I P ι x' y' := by
  cases h with
  | askInst => cases hR; exact ⟨_, .askInst, .inst ⟨he₀, rfl⟩⟩
  | itau hi =>
    cases hR with
    | inst hp =>
      obtain ⟨d', hd', hp'⟩ := internal_fwd hp hi
      exact ⟨_, .itau hd', .inst hp'⟩
  | icall hc =>
    cases hR with
    | inst hp =>
      obtain ⟨hco, hkk⟩ := hc
      obtain ⟨hco', hk⟩ := calls_fwd hκ hp hco
      exact ⟨_, .icall ⟨hco', rfl⟩, .iwait (by rw [hkk]; exact hk)⟩
  | iresume m k n => cases hR with | iwait hk => exact ⟨_, .iresume _ _ n, .inst (hk n)⟩
  | iready hr =>
    cases hR with
    | inst hp =>
      obtain ⟨hres, hst⟩ := hr
      exact ⟨_, .iready ⟨result_fwd hp hres, rfl⟩, .ready (by rw [hst]; exact hp.1)⟩
  | ifail hf => cases hR with | inst hp => exact ⟨_, .ifail (failed_fwd hp hf), .dead⟩
  | askEx st q => cases hR with | ready he => exact ⟨_, .askEx _ q, .run (pr_start q he)⟩
  | tau hi =>
    cases hR with
    | run hp =>
      obtain ⟨d', hd', hp'⟩ := internal_fwd hp hi
      exact ⟨_, .tau hd', .run hp'⟩
  | call hc =>
    cases hR with
    | run hp =>
      obtain ⟨hco, hkk⟩ := hc
      obtain ⟨hco', hk⟩ := calls_fwd hκ hp hco
      exact ⟨_, .call ⟨hco', rfl⟩, .wait (by rw [hkk]; exact hk)⟩
  | resume q m k n => cases hR with | wait hk => exact ⟨_, .resume _ _ _ n, .run (hk n)⟩
  | ret hd =>
    cases hR with
    | run hp =>
      obtain ⟨r, hres, hans, hst⟩ := hd
      exact ⟨_, .ret ⟨r, result_fwd hp hres, hans, rfl⟩, .ready (by rw [hst]; exact hp.1)⟩

/-- Transitions at the embedding are matched at `s`. -/
theorem bwd_step (he₀ : Emb ι Univ s t) (hκ : ∀ a, κ (ι a) = a) {x : (I.instSysT P s t₀).St}
    {y y' : (I.instSysT P t (thread ι t₀)).St}
    {l : Option (Move I.E (I.F.withInst (Behaviour Val)))}
    (hR : Rel I P ι x y) (h : (I.instSysT P t (thread ι t₀)).Step y l y') :
    ∃ x', (I.instSysT P s t₀).Step x l x' ∧ Rel I P ι x' y' := by
  cases h with
  | askInst => cases hR; exact ⟨_, .askInst, .inst ⟨he₀, rfl⟩⟩
  | itau hi =>
    cases hR with
    | inst hp =>
      obtain ⟨c', hc', hp'⟩ := internal_bwd hκ hp hi
      exact ⟨_, .itau hc', .inst hp'⟩
  | icall hc =>
    cases hR with
    | inst hp =>
      obtain ⟨hco, hkk⟩ := hc
      obtain ⟨hco', hk⟩ := calls_bwd hκ hp hco
      exact ⟨_, .icall ⟨hco', rfl⟩, .iwait (by rw [hkk]; exact hk)⟩
  | iresume m k n => cases hR with | iwait hk => exact ⟨_, .iresume _ _ n, .inst (hk n)⟩
  | iready hr =>
    cases hR with
    | inst hp =>
      obtain ⟨hres, hst⟩ := hr
      exact ⟨_, .iready ⟨result_bwd hκ hp hres, rfl⟩, .ready (by rw [hst]; exact hp.1)⟩
  | ifail hf => cases hR with | inst hp => exact ⟨_, .ifail (failed_bwd hκ hp hf), .dead⟩
  | askEx st q => cases hR with | ready he => exact ⟨_, .askEx _ q, .run (pr_start q he)⟩
  | tau hi =>
    cases hR with
    | run hp =>
      obtain ⟨c', hc', hp'⟩ := internal_bwd hκ hp hi
      exact ⟨_, .tau hc', .run hp'⟩
  | call hc =>
    cases hR with
    | run hp =>
      obtain ⟨hco, hkk⟩ := hc
      obtain ⟨hco', hk⟩ := calls_bwd hκ hp hco
      exact ⟨_, .call ⟨hco', rfl⟩, .wait (by rw [hkk]; exact hk)⟩
  | resume q m k n => cases hR with | wait hk => exact ⟨_, .resume _ _ _ n, .run (hk n)⟩
  | ret hd =>
    cases hR with
    | run hp =>
      obtain ⟨r, hres, hans, hst⟩ := hd
      exact ⟨_, .ret ⟨r, result_bwd hκ hp hres, hans, rfl⟩, .ready (by rw [hst]; exact hp.1)⟩

/-- `s` to its embedding, divergence-sensitive. -/
def fwdSim (he₀ : Emb ι Univ s t) (hκ : ∀ a, κ (ι a) = a) :
    LTS.DivSimulation (I.instSysT P s t₀).toLTS (I.instSysT P t (thread ι t₀)).toLTS where
  R := Rel I P ι
  init := .fresh
  step hR hs := by
    obtain ⟨y', hy', hR'⟩ := fwd_step he₀ hκ hR hs
    exact ⟨y', LTS.Run.of_step (L := (I.instSysT P t (thread ι t₀)).toLTS) hy', hR'⟩
  lt := Strat.noLt
  wf := Strat.noLt_wf
  tau hR hs := by
    obtain ⟨y', hy', hR'⟩ := fwd_step he₀ hκ hR hs
    exact .inl ⟨y', .single hy', hR'⟩

/-- The embedding back to `s`, divergence-sensitive. -/
def bwdSim (he₀ : Emb ι Univ s t) (hκ : ∀ a, κ (ι a) = a) :
    LTS.DivSimulation (I.instSysT P t (thread ι t₀)).toLTS (I.instSysT P s t₀).toLTS where
  R y x := Rel I P ι x y
  init := .fresh
  step hR hs := by
    obtain ⟨x', hx', hR'⟩ := bwd_step he₀ hκ hR hs
    exact ⟨x', LTS.Run.of_step (L := (I.instSysT P s t₀).toLTS) hx', hR'⟩
  lt := Strat.noLt
  wf := Strat.noLt_wf
  tau hR hs := by
    obtain ⟨x', hx', hR'⟩ := bwd_step he₀ hκ hR hs
    exact .inl ⟨x', .single hx', hR'⟩

end InstPhase

/-- **Strategies with an instantiation phase are invariant under global embeddings**, every
profile: running the renamed thread from an embedding gives the same divergence-observing
strategy. -/
theorem instStrategyT_emb (I : ScalarInstance) (P : Profile) {ι : Nat → Nat}
    (hinj : Function.Injective ι) {s t : Store Nat} (h : Emb ι Univ s t) (t₀ : Thread) :
    I.instStrategyT P s t₀ = I.instStrategyT P t (thread ι t₀) := by
  have hκ : ∀ a, Function.invFun ι (ι a) = a := Function.leftInverse_invFun hinj
  exact le_antisymm (InstPhase.fwdSim (I := I) (P := P) (t₀ := t₀) h hκ).ofLTS_le
    (InstPhase.bwdSim (I := I) (P := P) (t₀ := t₀) h hκ).ofLTS_le

end Silmaril.Proofs.Wasm.Game.SpecGlobals
