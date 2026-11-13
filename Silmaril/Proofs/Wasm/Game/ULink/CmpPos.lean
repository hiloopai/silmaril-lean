module

public import Silmaril.Proofs.Wasm.Game.ULink.Resolver

/-!
# Positions of the composite of provider and consumer

The composite system `Cmp L P` (resolver × consumer) takes silent steps only in running
positions (`cmp_silentRunning`). Its position `cpos` is the consumer's, refined by the
resolver's callout while the consumer waits on the resolver; along reachable states (`CInv`:
the resolver is idle unless the consumer waits) visible steps are game steps and silent
steps keep a running position.

Hence the divergence-observing composite of an environment and `L.compDStrategy P` is the
strategy of the composite system (`compClosedD_eq_ofLTS`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {L : ULink} {P : Profile}

/-- The game position of a composite state. -/
def cpos (L : ULink) : RState × L.U.State → Pos UImp L.U.F
  | (_, .idle) => .idle
  | (_, .running f _ _) => .run f
  | (r, .waiting f _ _ _) =>
    match r.pos L with
    | .wait _ e' => .wait f e'
    | _ => .run f

/-- Reachable composite states: the resolver is idle unless the consumer waits on it. -/
def CInv (L : ULink) : RState × L.U.State → Prop
  | (r, .idle) => r = .idle
  | (r, .running _ _ _) => r = .idle
  | (_, .waiting _ _ _ _) => True

/-- An idle resolver takes no silent step. -/
theorem rtrans_idle_tau {r' : RState} (h : L.RTrans P .idle none r') : False := by
  cases h

/-- An idle resolver makes no lower move. -/
theorem rtrans_idle_inl {r' : RState} {g : Ev UImp} (h : L.RTrans P .idle (some (.inl g)) r') :
    False := by
  cases h

/-- The resolver answers only into the idle state. -/
theorem rtrans_ans_idle {r r' : RState} {e : UCall Nat} {a : UReply}
    (h : L.RTrans P r (some (.inr (.ans e a))) r') : r' = .idle := by
  cases h <;> rfl

/-- **Composite steps keep the reachability invariant.** -/
theorem cinv_step {x x' : (Cmp L P).State} {o : Option (Move UImp L.U.F)} (hx : CInv L x)
    (hs : (Cmp L P).step x o x') : CInv L x' := by
  rcases x with ⟨r, y⟩
  cases hs with
  | tau₁ hr =>
    cases y with
    | idle => exact (rtrans_idle_tau (hx ▸ hr)).elim
    | running => exact (rtrans_idle_tau (hx ▸ hr)).elim
    | waiting => trivial
  | tau₂ hc =>
    cases hc
    exact hx
  | left g hr =>
    cases y with
    | idle => exact (rtrans_idle_inl (hx ▸ hr)).elim
    | running => exact (rtrans_idle_inl (hx ▸ hr)).elim
    | waiting => trivial
  | right g hc =>
    cases hc with
    | call f => exact hx
    | oret => exact hx
  | sync g hr hc =>
    cases hc with
    | ucall => trivial
    | uret a => exact rtrans_ans_idle hr

/-- The position of a waiting consumer while the resolver runs. -/
theorem cpos_waiting_run {r : RState} {f : L.U.F.Op} {σ : Store Nat} {t : Thread} {e e₀ : UCall Nat}
    (hr : r.pos L = .run e₀) : cpos L (r, .waiting f σ t e) = .run f := by
  simp only [cpos, hr]

/-- The position of a waiting consumer while the resolver waits. -/
theorem cpos_waiting_wait {r : RState} {f : L.U.F.Op} {σ : Store Nat} {t : Thread}
    {e e₀ e' : UCall Nat} (hr : r.pos L = .wait e₀ e') :
    cpos L (r, .waiting f σ t e) = .wait f e' := by
  simp only [cpos, hr]

/-- A non-idle resolver position after an Opponent question. -/
theorem rtrans_ask_run {r' : RState} {e : UCall Nat} (h : L.RTrans P .idle (some (.inr (.ask e))) r') :
    r'.pos L = .run e := by
  cases h <;> rfl

/-- A synchronisation where the consumer asks the resolver keeps a running position. -/
theorem cpos_sync_ask {r' : RState} {f : L.U.F.Op} {σ σ' : Store Nat} {t t' : Thread}
    {e e' : UCall Nat} (hr : L.RTrans P .idle (some (.inr (.ask e))) r') :
    cpos L (r', .waiting f σ' t' e') = cpos L (.idle, .running f σ t) ∧
      ∃ q, cpos L ((.idle, .running f σ t) : RState × L.U.State) = .run q :=
  ⟨cpos_waiting_run (rtrans_ask_run hr), f, rfl⟩

/-- A synchronisation where the resolver answers the consumer keeps a running position. -/
theorem cpos_sync_ans {r : RState} {f : L.U.F.Op} {σ σ' : Store Nat} {t t' : Thread}
    {e : UCall Nat} {a : UReply} (hr : L.RTrans P r (some (.inr (.ans e a))) .idle) :
    cpos L (.idle, .running f σ' t') = cpos L (r, .waiting f σ t e) ∧
      ∃ q, cpos L ((r, .waiting f σ t e) : RState × L.U.State) = .run q := by
  cases hr <;> exact ⟨rfl, _, rfl⟩

/-- **Silent composite steps keep a running position.** -/
theorem cpos_tau {x x' : (Cmp L P).State} (hx : CInv L x) (hs : (Cmp L P).step x none x') :
    cpos L x' = cpos L x ∧ ∃ q, cpos L x = .run q := by
  rcases x with ⟨r, y⟩
  cases hs with
  | tau₁ hr =>
    cases y with
    | idle => exact (rtrans_idle_tau (hx ▸ hr)).elim
    | running => exact (rtrans_idle_tau (hx ▸ hr)).elim
    | waiting f σ t e =>
      cases hr
      exact ⟨rfl, f, rfl⟩
  | tau₂ hc =>
    cases hc
    exact ⟨rfl, _, rfl⟩
  | sync g hr hc =>
    show cpos L _ = cpos L (r, y) ∧ ∃ q, cpos L (r, y) = .run q
    cases hc with
    | ucall =>
      have hr0 : r = .idle := hx
      exact hr0 ▸ cpos_sync_ask (hr0 ▸ hr)
    | uret a =>
      have hr' : _ = RState.idle := rtrans_ans_idle hr
      subst hr'
      exact cpos_sync_ans hr

/-- **Visible composite steps are game steps of the position.** -/
theorem cpos_vis {x x' : (Cmp L P).State} {m : Move UImp L.U.F} (hx : CInv L x)
    (hs : (Cmp L P).step x (some m) x') : Silmaril.Games.Step (cpos L x) m (cpos L x') := by
  rcases x with ⟨r, y⟩
  cases hs with
  | left g hr =>
    cases y with
    | idle => exact (rtrans_idle_inl (hx ▸ hr)).elim
    | running => exact (rtrans_idle_inl (hx ▸ hr)).elim
    | waiting f σ t e =>
      cases hr with
      | fwdAsk e => exact .call _ _
      | fwdAns e a => exact .reply _ _ _
      | ucall => exact .call _ _
      | uret a => exact .reply _ _ _
  | right g hc =>
    cases hc with
    | call f => exact .ask _
    | oret => exact .ret _ _

/-- Composite runs from reachable states follow the positions. -/
theorem cpos_run {x x' : (Cmp L P).State} {p : List (Move UImp L.U.F)} (hx : CInv L x)
    (h : (Cmp L P).Run x p x') : CInv L x' ∧ Silmaril.Games.Path (cpos L x) p (cpos L x') := by
  induction h with
  | nil => exact ⟨hx, .nil _⟩
  | tau hs _ ih =>
    obtain ⟨hi, hp⟩ := ih (cinv_step hx hs)
    exact ⟨hi, (cpos_tau hx hs).1 ▸ hp⟩
  | vis hs _ ih =>
    obtain ⟨hi, hp⟩ := ih (cinv_step hx hs)
    exact ⟨hi, .cons (cpos_vis hx hs) hp⟩

/-- **The composite takes silent steps only in running positions.** -/
theorem cmp_silentRunning (P : Profile) : (Cmp L P).SilentRunning := by
  intro s x y hr hs
  have hinit : CInv L (Cmp L P).init := rfl
  obtain ⟨hx, hp⟩ := cpos_run hinit hr
  obtain ⟨q, hq⟩ := (cpos_tau hx hs).2
  have hp' : Silmaril.Games.Path .idle s (cpos L x) := hp
  exact ⟨q, hq ▸ hp'⟩

/-- **The closed composite is the strategy of the closed composite system.** -/
theorem compClosedD_eq_ofLTS (P : Profile) (Lenv : SEnv UImp) (q : Lenv.S) :
    (Lenv.dstrategy q).comp (L.compDStrategy P) = DStrategy.ofLTS ((Lenv.dlts q).comp (Cmp L P)) := by
  rw [compD_eq_ofLTS]
  exact (DStrategy.ofLTS_comp (SEnv.denotes_dlts Lenv q) (comp_denotes P)
    (LTS.SilentRunning.divRunning (SEnv.silentRunning_dlts Lenv q))
    (LTS.SilentRunning.divRunning (cmp_silentRunning P))).symm

end Silmaril.Proofs.Wasm.Game.ULink
