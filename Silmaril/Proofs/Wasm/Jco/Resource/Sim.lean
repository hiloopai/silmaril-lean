module

public import Silmaril.Wasm.Jco.Resource.Basic.Defs
public import Silmaril.Wasm.Jco.Basic.Thms

/-!
# Resources in the jco toolchain: laws of `onFst`, `ofTab` and `Sim`

* `onFst_pure`, `onFst_bind`, `onFst_fail`, `onFst_check`, `onFst_ofOption`: running a core
  computation next to a handle table commutes with the monad operations.
* `Sim` is compositional: `sim_bind`, `sim_pure`, `sim_fail`, `sim_onFst`, `sim_returns`,
  `sim_mono`, `sim_det`, `sim_fail_left`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM

variable {σ τ α β γ δ : Type}

/-! ## `onFst` -/

theorem onFst_ok (m : RM σ α) (s : σ) (t : τ) (a : α) (s' : σ) (t' : τ) :
    m.onFst (s, t) (.ok a (s', t')) ↔ m s (.ok a s') ∧ t' = t := Iff.rfl

theorem onFst_trap (m : RM σ α) (s : σ) (t : τ) : m.onFst (s, t) .trap ↔ m s .trap := Iff.rfl

theorem onFst_pure (a : α) : ((pure a : RM σ α).onFst : RM (σ × τ) α) = pure a := by
  funext st o
  rcases st with ⟨s, t⟩
  cases o with
  | ok b st' =>
    rcases st' with ⟨s', t'⟩
    simp only [onFst_ok, pure_apply, Out.ok.injEq, Prod.mk.injEq, eq_iff_iff]
    constructor
    · rintro ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨⟨rfl, rfl⟩, rfl⟩
  | trap => simp [onFst_trap, pure_apply]

theorem onFst_fail : ((fail : RM σ α).onFst : RM (σ × τ) α) = fail := by
  funext st o
  rcases st with ⟨s, t⟩
  cases o with
  | ok b st' =>
    rcases st' with ⟨s', t'⟩
    simp [onFst_ok, fail]
  | trap => simp [onFst_trap, fail]

theorem onFst_check (b : Bool) : ((check b : RM σ Unit).onFst : RM (σ × τ) Unit) = check b := by
  cases b
  · exact onFst_fail
  · exact onFst_pure ()

theorem onFst_ofOption (x : Option α) :
    ((ofOption x : RM σ α).onFst : RM (σ × τ) α) = ofOption x := by
  cases x
  · exact onFst_fail
  · exact onFst_pure _

theorem onFst_bind_ok (m : RM σ α) (k : α → RM σ β) (s : σ) (t : τ) (b : β) (s' : σ)
    (t' : τ) : (m >>= k).onFst (s, t) (.ok b (s', t')) ↔
      (m.onFst >>= fun a => (k a).onFst) (s, t) (.ok b (s', t')) := by
  rw [onFst_ok, bind_apply, bind_apply]
  constructor
  · rintro ⟨(⟨a, s1, h1, h2⟩ | ⟨_, h⟩), ht⟩
    · exact .inl ⟨a, (s1, t), ⟨h1, rfl⟩, h2, ht⟩
    · cases h
  · rintro (⟨a, ⟨s1, t1⟩, ⟨h1, ht1⟩, h2, ht⟩ | ⟨_, h⟩)
    · exact ⟨.inl ⟨a, s1, h1, h2⟩, ht.trans ht1⟩
    · cases h

theorem onFst_bind_trap (m : RM σ α) (k : α → RM σ β) (s : σ) (t : τ) :
    (m >>= k).onFst (s, t) .trap ↔ (m.onFst >>= fun a => (k a).onFst) (s, t) .trap := by
  rw [onFst_trap, bind_apply, bind_apply]
  constructor
  · rintro (⟨a, s1, h1, h2⟩ | ⟨h, -⟩)
    · exact .inl ⟨a, (s1, t), ⟨h1, rfl⟩, h2⟩
    · exact .inr ⟨h, rfl⟩
  · rintro (⟨a, ⟨s1, t1⟩, ⟨h1, -⟩, h2⟩ | ⟨h, -⟩)
    · exact .inl ⟨a, s1, h1, h2⟩
    · exact .inr ⟨h, rfl⟩

theorem onFst_bind (m : RM σ α) (k : α → RM σ β) :
    ((m >>= k).onFst : RM (σ × τ) β) = (m.onFst >>= fun a => (k a).onFst) := by
  funext st o
  rcases st with ⟨s, t⟩
  cases o with
  | ok b st' =>
    rcases st' with ⟨s', t'⟩
    exact propext (onFst_bind_ok m k s t b s' t')
  | trap => exact propext (onFst_bind_trap m k s t)

/-! ## `Sim` -/

theorem sim_bind_fwd {m : RM (σ × τ) α} {n : RM σ β} {t : τ} {R : α → β → τ → Prop}
    {k : α → RM (σ × τ) γ} {k' : β → RM σ δ} {R' : γ → δ → τ → Prop}
    (h : Sim m n t R) (hk : ∀ a b t', R a b t' → Sim (k a) (k' b) t' R')
    (s : σ) (c : γ) (s' : σ) (t' : τ) (hc : (m >>= k) (s, t) (.ok c (s', t'))) :
    ∃ d, (n >>= k') s (.ok d s') ∧ R' c d t' := by
  rcases hc with ⟨a, ⟨s1, t1⟩, h1, h2⟩ | ⟨_, h⟩
  · obtain ⟨b, hb, hR⟩ := h.fwd s a s1 t1 h1
    obtain ⟨d, hd, hR'⟩ := (hk a b t1 hR).fwd s1 c s' t' h2
    exact ⟨d, .inl ⟨b, s1, hb, hd⟩, hR'⟩
  · cases h

theorem sim_bind_bwd {m : RM (σ × τ) α} {n : RM σ β} {t : τ} {R : α → β → τ → Prop}
    {k : α → RM (σ × τ) γ} {k' : β → RM σ δ} {R' : γ → δ → τ → Prop}
    (h : Sim m n t R) (hk : ∀ a b t', R a b t' → Sim (k a) (k' b) t' R')
    (s : σ) (d : δ) (s' : σ) (hd : (n >>= k') s (.ok d s')) :
    ∃ c t', (m >>= k) (s, t) (.ok c (s', t')) ∧ R' c d t' := by
  rcases hd with ⟨b, s1, h1, h2⟩ | ⟨_, h⟩
  · obtain ⟨a, t1, ha, hR⟩ := h.bwd s b s1 h1
    obtain ⟨c, t', hc, hR'⟩ := (hk a b t1 hR).bwd s1 d s' h2
    exact ⟨c, t', .inl ⟨a, (s1, t1), ha, hc⟩, hR'⟩
  · cases h

theorem sim_bind_trap {m : RM (σ × τ) α} {n : RM σ β} {t : τ} {R : α → β → τ → Prop}
    {k : α → RM (σ × τ) γ} {k' : β → RM σ δ} {R' : γ → δ → τ → Prop}
    (h : Sim m n t R) (hk : ∀ a b t', R a b t' → Sim (k a) (k' b) t' R') (s : σ) :
    (m >>= k) (s, t) .trap ↔ (n >>= k') s .trap := by
  rw [bind_apply, bind_apply]
  constructor
  · rintro (⟨a, ⟨s1, t1⟩, h1, h2⟩ | ⟨h1, -⟩)
    · obtain ⟨b, hb, hR⟩ := h.fwd s a s1 t1 h1
      exact .inl ⟨b, s1, hb, ((hk a b t1 hR).trap s1).1 h2⟩
    · exact .inr ⟨(h.trap s).1 h1, rfl⟩
  · rintro (⟨b, s1, h1, h2⟩ | ⟨h1, -⟩)
    · obtain ⟨a, t1, ha, hR⟩ := h.bwd s b s1 h1
      exact .inl ⟨a, (s1, t1), ha, ((hk a b t1 hR).trap s1).2 h2⟩
    · exact .inr ⟨(h.trap s).2 h1, rfl⟩

/-- `Sim` composes along `bind`. -/
theorem sim_bind {m : RM (σ × τ) α} {n : RM σ β} {t : τ} {R : α → β → τ → Prop}
    {k : α → RM (σ × τ) γ} {k' : β → RM σ δ} {R' : γ → δ → τ → Prop}
    (h : Sim m n t R) (hk : ∀ a b t', R a b t' → Sim (k a) (k' b) t' R') :
    Sim (m >>= k) (n >>= k') t R' :=
  ⟨sim_bind_fwd h hk, sim_bind_bwd h hk, sim_bind_trap h hk⟩

theorem sim_pure {a : α} {b : β} {t : τ} {R : α → β → τ → Prop} (h : R a b t) :
    Sim (pure a : RM (σ × τ) α) (pure b : RM σ β) t R where
  fwd s a' s' t' hc := by
    have he : a' = a ∧ s' = s ∧ t' = t := by simpa [pure_apply] using hc
    exact ⟨b, by rw [he.2.1]; rfl, he.1 ▸ he.2.2 ▸ h⟩
  bwd s b' s' hc := by
    have he : b' = b ∧ s' = s := by simpa [pure_apply] using hc
    exact ⟨a, t, by rw [he.2]; rfl, he.1 ▸ h⟩
  trap s := by simp [pure_apply]

theorem sim_fail {t : τ} {R : α → β → τ → Prop} :
    Sim (fail : RM (σ × τ) α) (fail : RM σ β) t R where
  fwd _ _ _ _ hc := by cases hc
  bwd _ _ _ hc := by cases hc
  trap _ := ⟨fun _ => rfl, fun _ => rfl⟩

theorem sim_onFst (n : RM σ α) (t : τ) :
    Sim (n.onFst : RM (σ × τ) α) n t fun a b t' => a = b ∧ t' = t where
  fwd _ a _ _ h := ⟨a, h.1, rfl, h.2⟩
  bwd _ b _ h := ⟨b, t, ⟨h, rfl⟩, rfl, rfl⟩
  trap _ := Iff.rfl

theorem sim_mono {m : RM (σ × τ) α} {n : RM σ β} {t : τ} {R R' : α → β → τ → Prop}
    (h : Sim m n t R) (hR : ∀ a b t', R a b t' → R' a b t') : Sim m n t R' where
  fwd s a s' t' hm := (h.fwd s a s' t' hm).imp fun _ hb => ⟨hb.1, hR _ _ _ hb.2⟩
  bwd s b s' hn := (h.bwd s b s' hn).imp fun _ ha => ha.imp fun _ hc => ⟨hc.1, hR _ _ _ hc.2⟩
  trap := h.trap

/-- Add what the right-hand side returns to the relation. -/
theorem sim_returns {m : RM (σ × τ) α} {n : RM σ β} {t : τ} {R : α → β → τ → Prop}
    (h : Sim m n t R) {P : β → Prop} (hn : Returns n P) :
    Sim m n t fun a b t' => R a b t' ∧ P b where
  fwd s a s' t' hm := (h.fwd s a s' t' hm).imp fun b hb => ⟨hb.1, hb.2, hn s b s' hb.1⟩
  bwd s b s' hb := (h.bwd s b s' hb).imp fun _ ha =>
    ha.imp fun _ hc => ⟨hc.1, hc.2, hn s b s' hb⟩
  trap := h.trap

/-- A deterministic table-side run against a pure right-hand side. -/
theorem sim_det {m : RM (σ × τ) α} {t t' : τ} {a : α} {b : β} {R : α → β → τ → Prop}
    (hm : ∀ s, Det m (s, t) (.ok a (s, t'))) (hR : R a b t') :
    Sim m (pure b : RM σ β) t R where
  fwd s a' s' t'' hc := by
    have he : a' = a ∧ s' = s ∧ t'' = t' := by simpa using (hm s _).1 hc
    exact ⟨b, by rw [he.2.1]; rfl, he.1 ▸ he.2.2 ▸ hR⟩
  bwd s b' s' hc := by
    have he : b' = b ∧ s' = s := by simpa [pure_apply] using hc
    exact ⟨a, t', by rw [he.2]; exact (hm s _).2 rfl, he.1 ▸ hR⟩
  trap s := by simpa [pure_apply] using hm s .trap

/-- A table-side run that traps against a computation that traps. -/
theorem sim_trap {m : RM (σ × τ) α} {n : RM σ β} {t : τ} {R : α → β → τ → Prop}
    (hm : ∀ s, Det m (s, t) .trap) (hn : ∀ s, Det n s .trap) : Sim m n t R where
  fwd s a s' t' hc := by cases (hm s _).1 hc
  bwd s b s' hc := by cases (hn s _).1 hc
  trap s := by simp [(hm s _), (hn s _)]

/-- A deterministic table-side first step. -/
theorem sim_det_bind {m : RM (σ × τ) α} {k : α → RM (σ × τ) γ} {n : RM σ β} {t t' : τ} {a : α}
    {R : γ → β → τ → Prop} (hm : ∀ s, Det m (s, t) (.ok a (s, t'))) (h : Sim (k a) n t' R) :
    Sim (m >>= k) n t R := by
  have he : ∀ s o, (m >>= k) (s, t) o ↔ k a (s, t') o := by
    intro s o
    rw [bind_apply]
    constructor
    · rintro (⟨a', st', h1, h2⟩ | ⟨h1, -⟩)
      · have heq : Out.ok a' st' = Out.ok a (s, t') := ((hm s _).1 h1)
        cases heq
        exact h2
      · cases ((hm s _).1 h1)
    · exact fun h2 => .inl ⟨a, (s, t'), (hm s _).2 rfl, h2⟩
  exact ⟨fun s a s' t'' hc => h.fwd s a s' t'' ((he s _).1 hc),
    fun s b s' hb => (h.bwd s b s' hb).imp fun _ hc => hc.imp fun _ hd => ⟨(he s _).2 hd.1, hd.2⟩,
    fun s => (he s _).trans (h.trap s)⟩

end Silmaril.Proofs.Wasm.Jco.Res
