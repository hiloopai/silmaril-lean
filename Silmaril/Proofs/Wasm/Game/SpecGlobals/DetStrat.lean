module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Det
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Games.DivLTS.Thms

/-!
# A forced instantiation prefix does not change the strategy

`instStrategyT_detTo`: if the instantiation configuration `c` reaches `d` by a forced run
(`DetTo P c d`), the strategy whose instantiation phase runs `c` is the one whose
instantiation phase runs `d` (divergence observed, every profile). Forward, the forced steps
stutter (measured by the remaining forced run); backward, the forced run is replayed silently
before the first step from `d`.

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace DetStrat

variable {I : ScalarInstance} {P : Profile}

/-- The state of a configuration. -/
def cst (e : Config Nat) : Store Nat × Thread := (e.store, configThread e)

theorem cst_config (e : Config Nat) : (cst e).2.config (cst e).1 = e := rfl

theorem cst_inj {e e' : Config Nat} (h : cst e = cst e') : e = e' := by
  obtain ⟨s, f, code⟩ := e
  obtain ⟨s', f', code'⟩ := e'
  simp only [cst, configThread, Prod.mk.injEq, Thread.active.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, h2, h3]

/-- Transport a state between two systems that differ only in their initial configuration. -/
def conv {s₀ s₁ : Store Nat} {t₀ t₁ : Thread} :
    (I.instSysT P s₀ t₀).St → (I.instSysT P s₁ t₁).St
  | .fresh => .fresh
  | .inst c => .inst c
  | .iwait m k => .iwait m k
  | .ready st => .ready st
  | .run q c => .run q c
  | .wait q m k => .wait q m k
  | .dead => .dead
  | .pstart => .pstart
  | .pwait => .pwait
  | .pfail r => .pfail r

theorem conv_conv {s₀ s₁ : Store Nat} {t₀ t₁ : Thread} (x : (I.instSysT P s₀ t₀).St) :
    conv (s₀ := s₁) (t₀ := t₁) (conv (s₁ := s₁) (t₁ := t₁) x) = x := by
  cases x <;> rfl

/-- Steps other than the instantiation question transport between the systems. -/
theorem conv_step {s₀ s₁ : Store Nat} {t₀ t₁ : Thread} {x x' : (I.instSysT P s₀ t₀).St}
    {l : Option (Move I.E (I.F.withInst (Behaviour Val)))} (h : (I.instSysT P s₀ t₀).Step x l x')
    (hx : x ≠ .fresh) : (I.instSysT P s₁ t₁).Step (conv x) l (conv x') := by
  cases h with
  | askInst => exact absurd rfl hx
  | itau hi => exact .itau hi
  | icall hc => exact .icall hc
  | iresume m k n => exact InstSystem.Step.iresume (S := I.instSysT P s₁ t₁) m k n
  | iready hr => exact .iready hr
  | ifail hf => exact .ifail hf
  | askEx st q => exact InstSystem.Step.askEx (S := I.instSysT P s₁ t₁) st q
  | tau hi => exact .tau hi
  | call hc => exact .call hc
  | resume q m k n => exact InstSystem.Step.resume (S := I.instSysT P s₁ t₁) q m k n
  | ret hd => exact .ret hd

theorem conv_ne_fresh {s₀ s₁ : Store Nat} {t₀ t₁ : Thread} {x : (I.instSysT P s₀ t₀).St}
    (hx : x ≠ .fresh) : conv (s₁ := s₁) (t₁ := t₁) x ≠ .fresh := by
  cases x <;> first | exact absurd rfl hx | exact fun h => by cases h

/-- The only transition of a forced configuration is its forced step. -/
theorem forced_step {s₀ : Store Nat} {t₀ : Thread} {e e' : Config Nat}
    (uniq : ∀ g, Step P noHost e g → g = e') (nocall : decompose? e.store e.code = none)
    (nores : ∀ r : Result, e.code ≠ r.toAdmin) {l : Option (Move I.E (I.F.withInst (Behaviour Val)))}
    {x' : (I.instSysT P s₀ t₀).St} (h : (I.instSysT P s₀ t₀).Step (.inst (cst e)) l x') :
    l = none ∧ x' = .inst (cst e') := by
  cases h with
  | @itau _ c₁ hi =>
    obtain ⟨s', t'⟩ := c₁
    obtain ⟨f', code', hth, hs⟩ := hi
    have hth' : t' = .active f' code' := hth
    have he : (⟨s', f', code'⟩ : Config Nat) = e' := uniq _ hs
    rw [hth', ← he]
    exact ⟨rfl, rfl⟩
  | icall hc =>
    obtain ⟨⟨h, args, ⟨E, a, hd⟩, -⟩, -⟩ := hc
    have hd' : decompose? e.store e.code = some (E, a, h, args) := hd
    rw [nocall] at hd'
    cases hd'
  | iready hr => exact absurd hr.1 (nores _)
  | ifail hf =>
    rcases hf with ⟨hr, -⟩ | ⟨a, hr, -⟩
    · exact absurd hr (nores _)
    · exact absurd hr (nores _)

/-- One forced step towards `d`. -/
def Lt (P : Profile) (d : Config Nat) {s₀ : Store Nat} {t₀ : Thread}
    (a b : (I.instSysT P s₀ t₀).St) : Prop :=
  ∃ e e', b = .inst (cst e) ∧ a = .inst (cst e') ∧ e ≠ d ∧ DetTo P e d ∧
    ∀ g, Step P noHost e g → g = e'

theorem lt_acc {d : Config Nat} {s₀ : Store Nat} {t₀ : Thread} {e : Config Nat}
    (h : DetTo P e d) : Acc (Lt (I := I) P d (s₀ := s₀) (t₀ := t₀)) (.inst (cst e)) := by
  induction h with
  | refl c =>
    refine ⟨_, fun a hab => ?_⟩
    obtain ⟨e₀, e', hb, -, hne, -⟩ := hab
    have he : c = e₀ := cst_inj (InstSystem.St.inst.inj hb)
    exact absurd he.symm hne
  | step hs uniq _ _ _ ih =>
    refine ⟨_, fun a hab => ?_⟩
    obtain ⟨e₀, e', hb, ha, -, -, uniq₀⟩ := hab
    have he : _ = e₀ := cst_inj (InstSystem.St.inst.inj hb)
    subst he
    have he' : e' = _ := (uniq₀ _ hs).symm
    rw [ha, he']
    exact ih

theorem lt_wf (d : Config Nat) {s₀ : Store Nat} {t₀ : Thread} :
    WellFounded (Lt (I := I) P d (s₀ := s₀) (t₀ := t₀)) := by
  refine ⟨fun b => ⟨_, fun a hab => ?_⟩⟩
  obtain ⟨e, e', hb, ha, hne, hd, uniq⟩ := hab
  have hacc := lt_acc (I := I) (s₀ := s₀) (t₀ := t₀) hd
  rw [← hb] at hacc
  exact hacc.inv ⟨e, e', hb, ha, hne, hd, uniq⟩

/-! ## The two simulations -/

variable {c d : Config Nat}

/-- Related states: equal, or a configuration on the forced run against `d`. -/
def FR (P : Profile) (c d : Config Nat) (x : (I.instSysT P c.store (configThread c)).St)
    (y : (I.instSysT P d.store (configThread d)).St) : Prop :=
  (x ≠ .fresh ∧ y = conv x) ∨ (x = .fresh ∧ y = .fresh) ∨
    ∃ e, x = .inst (cst e) ∧ DetTo P e d ∧ y = .inst (cst d)

theorem fwd_tau (hcd : DetTo P c d) {x x' : (I.instSysT P c.store (configThread c)).St}
    {y : (I.instSysT P d.store (configThread d)).St} (hR : FR P c d x y)
    {l : Option (Move I.E (I.F.withInst (Behaviour Val)))}
    (h : (I.instSysT P c.store (configThread c)).Step x l x') :
    (∃ y', (I.instSysT P d.store (configThread d)).Step y l y' ∧ FR P c d x' y') ∨
      (l = none ∧ FR P c d x' y ∧ Lt P d x' x) := by
  rcases hR with ⟨hx, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e, rfl, hd, rfl⟩
  · have hx' : x' ≠ .fresh := by cases h <;> exact fun h' => by cases h'
    exact .inl ⟨_, conv_step h hx, .inl ⟨hx', rfl⟩⟩
  · cases h with
    | askInst => exact .inl ⟨_, .askInst, .inr (.inr ⟨c, rfl, hcd, rfl⟩)⟩
  · by_cases hed : e = d
    · subst hed
      have hy : (InstSystem.St.inst (cst e) : (I.instSysT P e.store (configThread e)).St) =
          conv (InstSystem.St.inst (cst e) : (I.instSysT P c.store (configThread c)).St) := rfl
      have hx' : x' ≠ .fresh := by cases h <;> exact fun h' => by cases h'
      exact .inl ⟨_, hy ▸ conv_step h (fun h' => by cases h'), .inl ⟨hx', rfl⟩⟩
    · cases hd with
      | refl => exact absurd rfl hed
      | step hs uniq nocall nores rest =>
        obtain ⟨hl, hx'⟩ := forced_step uniq nocall nores h
        refine .inr ⟨hl, .inr (.inr ⟨_, hx', rest, rfl⟩), ?_⟩
        exact ⟨e, _, rfl, hx', hed, .step hs uniq nocall nores rest, uniq⟩

theorem silent_run {s₀ : Store Nat} {t₀ : Thread} {e : Config Nat} (h : DetTo P e d) :
    Relation.ReflTransGen (I.instSysT P s₀ t₀).toLTS.Silent (.inst (cst e)) (.inst (cst d)) := by
  induction h with
  | refl => exact .refl
  | @step e₀ e₁ _ hs _ _ _ _ ih =>
    have hi : InternalP P (cst e₀) (cst e₁) := ⟨e₁.frame, e₁.code, rfl, hs⟩
    exact .head (InstSystem.Step.itau hi) ih

theorem run_of_silent {L : LTS I.E (I.F.withInst (Behaviour Val))} {a b z : L.State}
    {t : List (Move I.E (I.F.withInst (Behaviour Val)))}
    (h : Relation.ReflTransGen L.Silent a b) (r : L.Run b t z) : L.Run a t z := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact r
  | head hs _ ih => exact .tau hs ih

theorem bwd {x : (I.instSysT P c.store (configThread c)).St}
    {y y' : (I.instSysT P d.store (configThread d)).St} (hcd : DetTo P c d) (hR : FR P c d x y)
    {l : Option (Move I.E (I.F.withInst (Behaviour Val)))}
    (h : (I.instSysT P d.store (configThread d)).Step y l y') :
    Relation.ReflTransGen (I.instSysT P c.store (configThread c)).toLTS.Silent x (conv y) ∧
      (I.instSysT P c.store (configThread c)).Step (conv y) l (conv y') ∧ FR P c d (conv y') y' ∨
    ((I.instSysT P c.store (configThread c)).Step x l (.inst (cst c)) ∧
      FR P c d (.inst (cst c)) y') := by
  have hy' : y' ≠ .fresh := by cases h <;> exact fun h' => by cases h'
  have hfr : FR P c d (conv y') y' := .inl ⟨conv_ne_fresh hy', (conv_conv y').symm⟩
  rcases hR with ⟨hx, rfl⟩ | ⟨rfl, rfl⟩ | ⟨e, rfl, hd, rfl⟩
  · refine .inl ⟨?_, conv_step h (conv_ne_fresh hx), hfr⟩
    rw [conv_conv]
  · cases h with
    | askInst => exact .inr ⟨.askInst, .inr (.inr ⟨c, rfl, hcd, rfl⟩)⟩
  · exact .inl ⟨silent_run hd, conv_step h (fun h' => by cases h'), hfr⟩

/-- From the forced run's start to its end, divergence-sensitive. -/
def fwdSim (hcd : DetTo P c d) :
    LTS.DivSimulation (I.instSysT P c.store (configThread c)).toLTS
      (I.instSysT P d.store (configThread d)).toLTS where
  R := FR P c d
  init := .inr (.inl ⟨rfl, rfl⟩)
  step hR hs := by
    rcases fwd_tau hcd hR hs with ⟨y', hy', hR'⟩ | ⟨rfl, hR', -⟩
    · exact ⟨y', LTS.Run.of_step hy', hR'⟩
    · exact ⟨_, .nil _, hR'⟩
  lt := Lt P d
  wf := lt_wf d
  tau hR hs := by
    rcases fwd_tau hcd hR hs with ⟨y', hy', hR'⟩ | ⟨-, hR', hlt⟩
    · exact .inl ⟨y', .single hy', hR'⟩
    · exact .inr ⟨hR', hlt⟩

/-- From the forced run's end back to its start, divergence-sensitive. -/
def bwdSim (hcd : DetTo P c d) :
    LTS.DivSimulation (I.instSysT P d.store (configThread d)).toLTS
      (I.instSysT P c.store (configThread c)).toLTS where
  R y x := FR P c d x y
  init := .inr (.inl ⟨rfl, rfl⟩)
  step hR hs := by
    rcases bwd hcd hR hs with ⟨hpre, hst, hR'⟩ | ⟨hst, hR'⟩
    · exact ⟨_, run_of_silent hpre (LTS.Run.of_step hst), hR'⟩
    · exact ⟨_, LTS.Run.of_step hst, hR'⟩
  lt := fun _ _ => False
  wf := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  tau hR hs := by
    rcases bwd hcd hR hs with ⟨hpre, hst, hR'⟩ | ⟨hst, hR'⟩
    · exact .inl ⟨_, Relation.TransGen.tail' hpre hst, hR'⟩
    · exact .inl ⟨_, .single hst, hR'⟩

end DetStrat

/-- **A forced instantiation prefix does not change the strategy**, every profile. -/
theorem instStrategyT_detTo (I : ScalarInstance) {P : Profile} {c d : Config Nat}
    (hcd : DetTo P c d) :
    I.instStrategyT P c.store (configThread c) = I.instStrategyT P d.store (configThread d) :=
  le_antisymm (DetStrat.fwdSim (I := I) hcd).ofLTS_le (DetStrat.bwdSim (I := I) hcd).ofLTS_le

end Silmaril.Proofs.Wasm.Game.SpecGlobals
