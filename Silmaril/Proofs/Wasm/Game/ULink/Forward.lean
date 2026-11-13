module

public import Silmaril.Proofs.Wasm.Game.ULink.Threads

/-!
# The composite is simulated by the linked module (`≤`)

`FRel x y` relates a state `x` of the composite system `Cmp L P` (resolver × consumer) to a
state `y` of the linked module:

* `cons`: the consumer runs thread `t` in the stubbed store `L.stubS s`, the linked module runs
  the same thread in the real store `s`;
* `prov`, `provWait`: the consumer waits at a stub call with context `E`, the provider runs (or
  waits at a callout with) top-level code `Y` in the real store, and the linked thread is the
  consumer's context filled with `Y`;
* `fwd`, `fwdWait`, `fwdRet`: a call of a host code that is not a stub is being forwarded;
* `stuck`: the provider will never answer.

Each silent composite step is one silent linked step, or none while the measure `rank`
decreases (`sim_tau`); each visible composite step, read through `stubUp`, is the same linked
move (`sim_vis`). Hence (`run_sim`, `diverges_sim`) composite runs and divergence along
`p.map L.stubUp` are linked runs and divergence along `p`, for plays whose stores have the
layout.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Proofs.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.Linking.Split

variable {L : ULink} {P : Profile}

/-- The simulation relation (see the module docstring). -/
inductive FRel (L : ULink) : RState × L.U.State → L.U.State → Prop where
  | idle : FRel L (.idle, .idle) .idle
  | cons {f : L.U.F.Op} {s : Store Nat} {t : Thread} (hq : L.Layout f.store) (hl : L.Layout s) :
      FRel L (.idle, .running (L.stubQ f) (L.stubS s) t) (.running f s t)
  | prov {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat} {args : List Val}
      {Y : List Admin} (hq : L.Layout f.store) (hl : L.Layout s)
      (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (htop : TopOK Y) :
      FRel L (.running ⟨k, σ₀, args⟩ s (.active {} Y), .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩)
        (.running f s (.active (t.config σ₀).frame (E.fill Y)))
  | provWait {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat}
      {args : List Val} {Y : List Admin} {h' : Nat} {args' : List Val} (hq : L.Layout f.store)
      (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (htop : TopOK Y)
      (hco : CalloutAt s (.active {} Y) h' args') :
      FRel L (.waiting ⟨k, σ₀, args⟩ s (.active {} Y) ⟨h', s, args'⟩,
          .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩)
        (.waiting f s (.active (t.config σ₀).frame (E.fill Y)) ⟨h', s, args'⟩)
  | stuck {f : L.U.F.Op} {σ : Store Nat} {t : Thread} {e : UCall Nat} {y : L.U.State} :
      FRel L (.stuck e, .waiting (L.stubQ f) σ t e) y
  | fwd {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
      (hq : L.Layout f.store) (hl : L.Layout s) (ht : L.target h = none)
      (hco : CalloutAt (L.stubS s) t h args) :
      FRel L (.fwd ⟨h, L.stubS s, args⟩, .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩)
        (.running f s t)
  | fwdWait {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
      (hq : L.Layout f.store) (hl : L.Layout s) (ht : L.target h = none)
      (hco : CalloutAt (L.stubS s) t h args) :
      FRel L (.fwdWait ⟨h, L.stubS s, args⟩,
          .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩)
        (.waiting f s t ⟨h, s, args⟩)
  | fwdRet {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
      {a : UReply} (hq : L.Layout f.store) (ht : L.target h = none)
      (hco : CalloutAt (L.stubS s) t h args) (ha : L.Layout a.store) :
      FRel L (.fwdRet ⟨h, L.stubS s, args⟩ a,
          .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩)
        (.running f a.store (resumeResult s t a.result))

/-- The measure bounding the composite steps that the linked module does not take. -/
def rank : RState × L.U.State → Nat
  | (.idle, .running _ _ _) => 1
  | (.running _ _ _, _) => 2
  | (.fwdRet _ _, _) => 2
  | _ => 0

/-! ### Silent steps -/

theorem tau_cons {f : L.U.F.Op} {s : Store Nat} {t : Thread} (hq : L.Layout f.store)
    (hl : L.Layout s) {x' : (Cmp L P).State}
    (hs : (Cmp L P).step (.idle, .running (L.stubQ f) (L.stubS s) t) none x') :
    (∃ y', (L.U.lts P).step (.running f s t) none y' ∧ FRel L x' y') ∨
      (FRel L x' (.running f s t) ∧ rank x' < rank (L := L) (.idle, .running (L.stubQ f) (L.stubS s) t)) := by
  cases hs with
  | tau₁ hr => cases hr
  | tau₂ hc =>
    cases hc with
    | tau hi =>
      obtain ⟨s', rfl, hf, hi'⟩ := internal_cons hi
      exact .inl ⟨_, .tau hi', .cons hq (Layout.of_funcs hl hf)⟩
  | sync g hr hc =>
    cases hc with
    | @ucall _ _ _ k args callout =>
      cases hr with
      | call e ht hf he hn hc =>
        obtain ⟨E, a, hd⟩ := callout
        refine .inl ⟨_, .tau (call_internal hl hd ht hf he hn hc), ?_⟩
        have hus : L.unstubS (L.stubS s) = s := unstub_stub hl
        show FRel L (.running _ (L.unstubS (L.stubS s)) _, _) _
        rw [hus]
        exact .prov hq hl hd (by simp [TopOK, TopAdmin, callCode])
      | callStuck e _ => exact .inr ⟨.stuck, by simp [rank]⟩
      | fwdCall e ht => exact .inr ⟨.fwd hq hl ht callout, by simp [rank]⟩

theorem tau_prov {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat}
    {args : List Val} {Y : List Admin} (hq : L.Layout f.store) (hl : L.Layout s)
    (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (htop : TopOK Y)
    {x' : (Cmp L P).State}
    (hs : (Cmp L P).step (.running ⟨k, σ₀, args⟩ s (.active {} Y),
      .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩) none x') :
    (∃ y', (L.U.lts P).step (.running f s (.active (t.config σ₀).frame (E.fill Y))) none y' ∧
        FRel L x' y') ∨
      (FRel L x' (.running f s (.active (t.config σ₀).frame (E.fill Y))) ∧
        rank x' < rank (L := L) (.running ⟨k, σ₀, args⟩ s (.active {} Y),
          .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩)) := by
  cases hs with
  | tau₁ hr =>
    cases hr with
    | tau hi =>
      obtain ⟨Y', rfl, htop', hf, hall⟩ := internal_prov htop hi
      exact .inl ⟨_, .tau (hall _ E), .prov hq (Layout.of_funcs hl hf) hd htop'⟩
  | tau₂ hc => cases hc
  | sync g hr hc =>
    cases hr with
    | @oret _ _ _ r final =>
      cases hc with
      | uret a' =>
        have hY : Y = r.toAdmin := final
        subst hY
        refine .inr ⟨?_, by simp [rank]⟩
        show FRel L (.idle, .running (L.stubQ f) (L.stubS s) (resumeResult σ₀ t r)) _
        rw [resume_active hd]
        exact .cons hq hl

theorem tau_fwdRet {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    {a : UReply} (hq : L.Layout f.store) (ht : L.target h = none)
    (hco : CalloutAt (L.stubS s) t h args) (ha : L.Layout a.store) {x' : (Cmp L P).State}
    (hs : (Cmp L P).step (.fwdRet ⟨h, L.stubS s, args⟩ a,
      .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) none x') :
    FRel L x' (.running f a.store (resumeResult s t a.result)) := by
  cases hs with
  | tau₁ hr => cases hr
  | tau₂ hc => cases hc
  | sync g hr hc =>
    cases hr with
    | fwdRet e a =>
      cases hc with
      | uret a' =>
        obtain ⟨E, a₀, hd⟩ := hco
        rw [resume_stub hd ht]
        exact .cons hq ha

theorem tau_idle {x' : (Cmp L P).State} (hs : (Cmp L P).step (.idle, .idle) none x') : False := by
  cases hs with
  | tau₁ hr => cases hr
  | tau₂ hc => cases hc
  | sync g hr hc => cases hc

theorem tau_waiting {r : RState} {f : L.U.F.Op} {σ : Store Nat} {t : Thread} {e : UCall Nat}
    (hr₀ : ∀ r', ¬ L.RTrans P r none r') (hr₁ : ∀ g r', ¬ L.RTrans P r (some (.inr g)) r')
    {x' : (Cmp L P).State} (hs : (Cmp L P).step (r, .waiting f σ t e) none x') : False := by
  cases hs with
  | tau₁ hr => exact hr₀ _ hr
  | tau₂ hc => cases hc
  | sync g hr hc => exact hr₁ _ _ hr

theorem fwdRet_rank {s : Store Nat} {f : L.U.F.Op} {t : Thread} {h : Nat} {args : List Val}
    {a : UReply} {x' : (Cmp L P).State}
    (hs : (Cmp L P).step (.fwdRet ⟨h, L.stubS s, args⟩ a,
      .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) none x') :
    rank x' < rank (L := L) (.fwdRet ⟨h, L.stubS s, args⟩ a,
      .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) := by
  cases hs with
  | tau₁ hr => cases hr
  | tau₂ hc => cases hc
  | sync g hr hc =>
    cases hr
    cases hc
    simp [rank]

/-- **Silent composite steps.** -/
theorem sim_tau {x x' : (Cmp L P).State} {y : L.U.State} (hR : FRel L x y)
    (hs : (Cmp L P).step x none x') :
    (∃ y', (L.U.lts P).step y none y' ∧ FRel L x' y') ∨ (FRel L x' y ∧ rank x' < rank x) := by
  cases hR with
  | idle => exact (tau_idle hs).elim
  | cons hq hl => exact tau_cons hq hl hs
  | prov hq hl hd htop => exact tau_prov hq hl hd htop hs
  | provWait hq hd htop hco =>
    exact (tau_waiting (fun _ h => by cases h) (fun _ _ h => by cases h) hs).elim
  | stuck => exact (tau_waiting (fun _ h => by cases h) (fun _ _ h => by cases h) hs).elim
  | fwd hq hl ht hco =>
    exact (tau_waiting (fun _ h => by cases h) (fun _ _ h => by cases h) hs).elim
  | fwdWait hq hl ht hco =>
    exact (tau_waiting (fun _ h => by cases h) (fun _ _ h => by cases h) hs).elim
  | fwdRet hq ht hco ha => exact .inr ⟨tau_fwdRet hq ht hco ha hs, fwdRet_rank hs⟩

/-! ### Moves -/

theorem stubUp_inl {m : Move UImp L.U.F} {e : Ev UImp} (h : .inl e = L.stubUp m) : m = .inl e := by
  rcases m with e' | (⟨f⟩ | ⟨f, a⟩)
  · exact h.symm
  · cases h
  · cases h

theorem stubUp_ask {m : Move UImp L.U.F} {f' : L.U.F.Op} (h : .inr (.ask f') = L.stubUp m) :
    ∃ f, m = .inr (.ask f) ∧ f' = L.stubQ f := by
  rcases m with e' | (⟨f⟩ | ⟨f, a⟩)
  · cases h
  · cases h
    exact ⟨f, rfl, rfl⟩
  · cases h

theorem stubUp_ans {m : Move UImp L.U.F} {f' : L.U.F.Op} {a' : UReply}
    (h : .inr (.ans f' a') = L.stubUp m) :
    ∃ f a, m = .inr (.ans f a) ∧ f' = L.stubQ f ∧ a' = L.stubR a := by
  rcases m with e' | (⟨f⟩ | ⟨f, a⟩)
  · cases h
  · cases h
  · cases h
    exact ⟨f, a, rfl, rfl, rfl⟩

/-- Stubbing is injective on stores with the layout. -/
theorem stubS_inj {s s' : Store Nat} (hs : L.Layout s) (hs' : L.Layout s')
    (h : L.stubS s = L.stubS s') : s = s' := by
  rw [← unstub_stub hs, ← unstub_stub hs', h]

theorem stubQ_inj {f f' : L.U.F.Op} (hf : L.Layout f.store) (hf' : L.Layout f'.store)
    (h : L.stubQ f = L.stubQ f') : f = f' := by
  obtain ⟨x, s, args⟩ := f
  obtain ⟨x', s', args'⟩ := f'
  obtain ⟨rfl, hs, rfl⟩ : x = x' ∧ L.stubS s = L.stubS s' ∧ args = args' := by
    simpa [ULink.stubQ] using h
  have hss : s = s' := stubS_inj hf hf' hs
  rw [hss]

/-! ### Visible steps -/

theorem vis_idle {m' : Move UImp L.U.F} {x' : (Cmp L P).State} {m : Move UImp L.U.F}
    (hs : (Cmp L P).step (.idle, .idle) (some m') x') (hm : m' = L.stubUp m)
    (hml : L.MoveLayout m) : ∃ y', (L.U.lts P).step .idle (some m) y' ∧ FRel L x' y' := by
  cases hs with
  | left g hr => cases hr
  | right g hc =>
    cases hc with
    | call f' =>
      obtain ⟨f, rfl, rfl⟩ := stubUp_ask hm
      exact ⟨_, .call f, .cons hml hml⟩

/-- The consumer's answer is the linked answer. -/
theorem cons_oret {f : L.U.F.Op} {s : Store Nat} {t : Thread} (hq : L.Layout f.store)
    (hl : L.Layout s) {r : Result} (final : ResultAt (L.stubS s) t r) {m : Move UImp L.U.F}
    (hm : (.inr (.ans (L.stubQ f) ⟨L.stubS s, r⟩) : Move UImp L.U.F) = L.stubUp m)
    (hml : L.MoveLayout m) : (L.U.lts P).step (.running f s t) (some m) .idle := by
  obtain ⟨f'', a, rfl, hf, ha⟩ := stubUp_ans hm
  obtain ⟨hlf, hla⟩ := hml
  have hff : f = f'' := stubQ_inj hq hlf hf
  have has : s = a.store := stubS_inj hl hla (congrArg UReply.store ha)
  have har : r = a.result := congrArg UReply.result ha
  have hc : (t.config (L.stubS s)).code = (t.config s).code := by rw [config_stub]
  have final' : ResultAt s t r := by
    show (t.config s).code = r.toAdmin
    rw [← hc]
    exact final
  have hae : a = ⟨s, r⟩ := by rw [has, har]
  rw [← hff, hae]
  exact UInstance.Trans.oret final'

theorem vis_cons {f : L.U.F.Op} {s : Store Nat} {t : Thread} (hq : L.Layout f.store)
    (hl : L.Layout s) {m' : Move UImp L.U.F} {x' : (Cmp L P).State} {m : Move UImp L.U.F}
    (hs : (Cmp L P).step (.idle, .running (L.stubQ f) (L.stubS s) t) (some m') x')
    (hm : m' = L.stubUp m) (hml : L.MoveLayout m) :
    ∃ y', (L.U.lts P).step (.running f s t) (some m) y' ∧ FRel L x' y' := by
  cases hs with
  | left g hr => cases hr
  | right g hc =>
    cases hc with
    | oret final => exact ⟨.idle, cons_oret hq hl final hm hml, .idle⟩

theorem vis_prov {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat}
    {args : List Val} {Y : List Admin} (hq : L.Layout f.store)
    (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (htop : TopOK Y)
    {m' : Move UImp L.U.F} {x' : (Cmp L P).State} {m : Move UImp L.U.F}
    (hs : (Cmp L P).step (.running ⟨k, σ₀, args⟩ s (.active {} Y),
      .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩) (some m') x') (hm : m' = L.stubUp m) :
    ∃ y', (L.U.lts P).step (.running f s (.active (t.config σ₀).frame (E.fill Y))) (some m) y' ∧
      FRel L x' y' := by
  cases hs with
  | left g hr =>
    cases hr with
    | @ucall _ _ _ h' args' callout =>
      have hm' := stubUp_inl hm
      subst hm'
      obtain ⟨E', -, -, hall⟩ := callout_comp callout
      exact ⟨_, .ucall (hall _ E).1, .provWait hq hd htop callout⟩
  | right g hc => cases hc

theorem vis_provWait {f : L.U.F.Op} {σ₀ s : Store Nat} {t : Thread} {E : Ctx} {a k : Nat}
    {args : List Val} {Y : List Admin} {h' : Nat} {args' : List Val} (hq : L.Layout f.store)
    (hd : decompose? σ₀ (t.config σ₀).code = some (E, a, k, args)) (htop : TopOK Y)
    (hco : CalloutAt s (.active {} Y) h' args')
    {m' : Move UImp L.U.F} {x' : (Cmp L P).State} {m : Move UImp L.U.F}
    (hs : (Cmp L P).step (.waiting ⟨k, σ₀, args⟩ s (.active {} Y) ⟨h', s, args'⟩,
      .waiting (L.stubQ f) σ₀ t ⟨k, σ₀, args⟩) (some m') x') (hm : m' = L.stubUp m)
    (hml : L.MoveLayout m) :
    ∃ y', (L.U.lts P).step (.waiting f s (.active (t.config σ₀).frame (E.fill Y)) ⟨h', s, args'⟩)
      (some m) y' ∧ FRel L x' y' := by
  cases hs with
  | left g hr =>
    cases hr with
    | uret ans =>
      have hm' := stubUp_inl hm
      subst hm'
      obtain ⟨E', hres, htop', hall⟩ := callout_comp hco
      refine ⟨_, .uret ans, ?_⟩
      rw [hres, (hall _ E).2]
      exact .prov hq hml hd (htop' htop ans.result)
  | right g hc => cases hc

theorem vis_fwd {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hq : L.Layout f.store) (hl : L.Layout s) (ht : L.target h = none)
    (hco : CalloutAt (L.stubS s) t h args)
    {m' : Move UImp L.U.F} {x' : (Cmp L P).State} {m : Move UImp L.U.F}
    (hs : (Cmp L P).step (.fwd ⟨h, L.stubS s, args⟩,
      .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) (some m') x')
    (hm : m' = L.stubUp m) :
    ∃ y', (L.U.lts P).step (.running f s t) (some m) y' ∧ FRel L x' y' := by
  cases hs with
  | left g hr =>
    cases hr with
    | fwdAsk e =>
      have hm' := stubUp_inl hm
      subst hm'
      obtain ⟨E, a, hd⟩ := hco
      have hcode : (t.config (L.stubS s)).code = (t.config s).code := by rw [config_stub]
      have hd' : decompose? s (t.config s).code = some (E, a, h, args) :=
        decompose_real_of_stub (hcode ▸ hd) ht
      have hq' : L.fwdQ ⟨h, L.stubS s, args⟩ = ⟨h, s, args⟩ := by
        simp [ULink.fwdQ, unstub_stub hl]
      rw [hq']
      exact ⟨_, .ucall ⟨E, a, hd'⟩, .fwdWait hq hl ht ⟨E, a, hd⟩⟩
  | right g hc => cases hc

theorem vis_fwdWait {f : L.U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hq : L.Layout f.store) (hl : L.Layout s) (ht : L.target h = none)
    (hco : CalloutAt (L.stubS s) t h args)
    {m' : Move UImp L.U.F} {x' : (Cmp L P).State} {m : Move UImp L.U.F}
    (hs : (Cmp L P).step (.fwdWait ⟨h, L.stubS s, args⟩,
      .waiting (L.stubQ f) (L.stubS s) t ⟨h, L.stubS s, args⟩) (some m') x')
    (hm : m' = L.stubUp m) (hml : L.MoveLayout m) :
    ∃ y', (L.U.lts P).step (.waiting f s t ⟨h, s, args⟩) (some m) y' ∧ FRel L x' y' := by
  cases hs with
  | left g hr =>
    cases hr with
    | fwdAns e ans =>
      have hm' := stubUp_inl hm
      subst hm'
      have hq' : L.fwdQ ⟨h, L.stubS s, args⟩ = ⟨h, s, args⟩ := by
        simp [ULink.fwdQ, unstub_stub hl]
      have hstep : (L.U.lts P).step (.waiting f s t ⟨h, s, args⟩)
          (some (.inl (.ans (L.fwdQ ⟨h, L.stubS s, args⟩) ans)))
          (.running f ans.store (resumeResult s t ans.result)) := by
        rw [hq']
        exact UInstance.Trans.uret ans
      exact ⟨_, hstep, .fwdRet hq ht hco hml⟩
  | right g hc => cases hc

theorem vis_none {r : RState} {f : L.U.F.Op} {σ : Store Nat} {t : Thread} {e : UCall Nat}
    (hr : ∀ g r', ¬ L.RTrans P r (some (.inl g)) r') {m' : Move UImp L.U.F}
    {x' : (Cmp L P).State} (hs : (Cmp L P).step (r, .waiting f σ t e) (some m') x') : False := by
  cases hs with
  | left g hr' => exact hr _ _ hr'
  | right g hc => cases hc

/-- **Visible composite steps, read through `stubUp`.** -/
theorem sim_vis {x x' : (Cmp L P).State} {y : L.U.State} {m' m : Move UImp L.U.F}
    (hR : FRel L x y) (hs : (Cmp L P).step x (some m') x') (hm : m' = L.stubUp m)
    (hml : L.MoveLayout m) : ∃ y', (L.U.lts P).step y (some m) y' ∧ FRel L x' y' := by
  cases hR with
  | idle => exact vis_idle hs hm hml
  | cons hq hl => exact vis_cons hq hl hs hm hml
  | prov hq hl hd htop => exact vis_prov hq hd htop hs hm
  | provWait hq hd htop hco => exact vis_provWait hq hd htop hco hs hm hml
  | stuck => exact (vis_none (fun _ _ h => by cases h) hs).elim
  | fwd hq hl ht hco => exact vis_fwd hq hl ht hco hs hm
  | fwdWait hq hl ht hco => exact vis_fwdWait hq hl ht hco hs hm hml
  | fwdRet hq ht hco ha => exact (vis_none (fun _ _ h => by cases h) hs).elim

/-! ### Runs and divergence -/

theorem map_cons_inv {m' : Move UImp L.U.F} {q p : List (Move UImp L.U.F)}
    (hp : m' :: q = p.map L.stubUp) : ∃ m p₀, p = m :: p₀ ∧ m' = L.stubUp m ∧ q = p₀.map L.stubUp := by
  cases p with
  | nil => cases hp
  | cons m p₀ => exact ⟨m, p₀, rfl, (List.cons.inj hp).1, (List.cons.inj hp).2⟩

/-- **Composite runs along an erased play are linked runs along the play.** -/
theorem run_sim {x x' : (Cmp L P).State} {q : List (Move UImp L.U.F)} (h : (Cmp L P).Run x q x') :
    ∀ (y : L.U.State) (p : List (Move UImp L.U.F)), FRel L x y → q = p.map L.stubUp →
      L.LayoutPlay p → ∃ y', (L.U.lts P).Run y p y' ∧ FRel L x' y' := by
  induction h with
  | nil x =>
    intro y p hR hp _
    have hp' : p = [] := List.map_eq_nil_iff.mp hp.symm
    exact ⟨y, hp' ▸ .nil _, hR⟩
  | tau hs _ ih =>
    intro y p hR hp hl
    rcases sim_tau hR hs with ⟨y₁, hy, hR₁⟩ | ⟨hR₁, -⟩
    · obtain ⟨y', hr, hR'⟩ := ih y₁ p hR₁ hp hl
      exact ⟨y', .tau hy hr, hR'⟩
    · exact ih y p hR₁ hp hl
  | vis hs _ ih =>
    intro y p hR hp hl
    obtain ⟨m, p₀, rfl, hm, hp₀⟩ := map_cons_inv hp
    obtain ⟨y₁, hy, hR₁⟩ := sim_vis hR hs hm (hl m (List.mem_cons_self ..))
    obtain ⟨y', hr, hR'⟩ := ih y₁ p₀ hR₁ hp₀ (fun m' hm' => hl m' (List.mem_cons_of_mem _ hm'))
    exact ⟨y', .vis hy hr, hR'⟩

/-- **Composite divergence is linked divergence.** -/
theorem diverges_sim {x : (Cmp L P).State} {y : L.U.State} (hR : FRel L x y)
    (hd : (Cmp L P).Diverges x) : (L.U.lts P).Diverges y := by
  refine InfiniteTrace.coinduct (fun y => ∃ x, FRel L x y ∧ (Cmp L P).Diverges x) ?_ ⟨x, hR, hd⟩
  rintro y ⟨x, hR, hd⟩
  induction hn : rank x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
    rcases sim_tau hR hs with ⟨y₁, hy, hR₁⟩ | ⟨hR₁, hlt⟩
    · exact ⟨y₁, hy, x₁, hR₁, hd₁⟩
    · exact ih (rank x₁) (hn ▸ hlt) x₁ hR₁ hd₁ rfl

end Silmaril.Proofs.Wasm.Game.ULink

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril

variable {L : ULink} {P : Profile}

/-- **Finite plays: the composite is contained in the linked module.** -/
theorem comp_le_link {p : List (Move UImp L.U.F)} (hl : L.LayoutPlay p)
    (h : p.map L.stubUp ∈ L.compStrategy P) : p ∈ L.U.strategy P := by
  obtain ⟨x, hx⟩ := (comp_denotes P _).2 h
  obtain ⟨y, hy, -⟩ := run_sim hx .idle p .idle rfl hl
  exact Untyped.mem_strategy_iff.2 ⟨y, hy⟩

/-- **Divergence: the composite's is contained in the linked module's.** -/
theorem comp_div_le_link {p : List (Move UImp L.U.F)} (hl : L.LayoutPlay p)
    (h : p.map L.stubUp ∈ (L.compDStrategy P).div) : p ∈ (L.U.dstrategy P).div := by
  rw [compD_eq_ofLTS] at h
  obtain ⟨⟨x, hx, hd⟩, -⟩ := h
  obtain ⟨y, hy, hR⟩ := run_sim hx .idle p .idle rfl hl
  have hdy : (L.U.lts P).Diverges y := diverges_sim hR hd
  obtain ⟨y₁, hs, -⟩ := hdy.unfold
  obtain ⟨q, hq⟩ := Untyped.trans_tau_run hs
  have hpath : Silmaril.Games.Path .idle p y.pos := Untyped.run_pos hy
  rw [hq] at hpath
  exact DStrategy.mem_div_ofLTS_of_run hy hdy hpath

end Silmaril.Proofs.Wasm.Game.ULink
