module

public import Silmaril.Wasm.Jco.Resource.Merge.Defs
public import Silmaril.Proofs.Wasm.Jco.Resource.Lift

/-!
# Merging a resource manager: algebra of table operations

* `ofTab_pure`, `ofTab_fail`, `ofTab_bind`, `ofTab_bind_fail`: deterministic table operations
  compose; `hostLift_ofTab`: the caller's argument lifting is one of them.
* `Total`; `total_bind`, … : computations that always have an outcome (no divergence).
* **`comm_ofTab`**: a deterministic table operation commutes with a total computation of the core
  state.
* `onSnd_ofFn`: the manager's operations, seen from the merged instance.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM

variable {σ τ α β γ : Type}

theorem ofTab_apply_some {f : τ → Option (α × τ)} {s : σ} {t t' : τ} {a : α}
    (h : f t = some (a, t')) (o : Out (σ × τ) α) : RM.ofTab f (s, t) o ↔ o = .ok a (s, t') := by
  simp only [RM.ofTab, h]

theorem ofTab_apply_none {f : τ → Option (α × τ)} {s : σ} {t : τ} (h : f t = none)
    (o : Out (σ × τ) α) : RM.ofTab f (s, t) o ↔ o = .trap := by
  simp only [RM.ofTab, h]

theorem ofTab_bind_some {f : τ → Option (α × τ)} {k : α → RM (σ × τ) β} {s : σ} {t t' : τ}
    {a : α} (h : f t = some (a, t')) (o : Out (σ × τ) β) :
    (RM.ofTab f >>= k) (s, t) o ↔ k a (s, t') o := by
  rw [bind_apply]
  constructor
  · rintro (⟨a', st', h1, h2⟩ | ⟨h1, -⟩)
    · have he : Out.ok a' st' = Out.ok a (s, t') := (ofTab_apply_some h _).1 h1
      cases he
      exact h2
    · cases (ofTab_apply_some h _).1 h1
  · exact fun h2 => .inl ⟨a, (s, t'), (ofTab_apply_some h _).2 rfl, h2⟩

theorem ofTab_bind_none {f : τ → Option (α × τ)} {k : α → RM (σ × τ) β} {s : σ} {t : τ}
    (h : f t = none) (o : Out (σ × τ) β) : (RM.ofTab f >>= k) (s, t) o ↔ o = .trap := by
  rw [bind_apply]
  constructor
  · rintro (⟨a', st', h1, -⟩ | ⟨-, h2⟩)
    · cases (ofTab_apply_none h _).1 h1
    · exact h2
  · exact fun h2 => .inr ⟨(ofTab_apply_none h _).2 rfl, h2⟩

theorem ofTab_pure (a : α) :
    (pure a : RM (σ × τ) α) = RM.ofTab fun t => some (a, t) := rfl

theorem ofTab_fail : (fail : RM (σ × τ) α) = RM.ofTab fun _ => none := rfl

theorem ofTab_bind (f : τ → Option (α × τ)) (g : α → τ → Option (β × τ)) :
    (RM.ofTab f >>= fun a => (RM.ofTab (g a) : RM (σ × τ) β)) =
      RM.ofTab fun t => (f t).bind fun p => g p.1 p.2 := by
  funext st o
  rcases st with ⟨s, t⟩
  cases hf : f t with
  | none =>
    rw [ofTab_bind_none hf, ofTab_apply_none (by simp [hf])]
  | some p =>
    rcases p with ⟨a, t'⟩
    rw [ofTab_bind_some hf]
    cases hg : g a t' with
    | none => rw [ofTab_apply_none hg, ofTab_apply_none (by simp [hf, hg])]
    | some q =>
      rcases q with ⟨b, t''⟩
      rw [ofTab_apply_some hg, ofTab_apply_some (a := b) (t' := t'') (by simp [hf, hg])]

theorem ofTab_bind_fail (f : τ → Option (α × τ)) :
    (RM.ofTab f >>= fun _ => (fail : RM (σ × τ) β)) = fail := by
  rw [ofTab_fail, ofTab_bind]
  congr 1
  funext t
  cases f t <;> rfl

/-! ## Total computations -/

/-- Every start state has an outcome (no divergence). -/
def Total (m : RM σ α) : Prop := ∀ s, ∃ o, m s o

theorem total_pure (a : α) : Total (pure a : RM σ α) := fun _ => ⟨_, rfl⟩

theorem total_fail : Total (fail : RM σ α) := fun _ => ⟨_, rfl⟩

theorem total_bind {m : RM σ α} {k : α → RM σ β} (hm : Total m) (hk : ∀ a, Total (k a)) :
    Total (m >>= k) := by
  intro s
  obtain ⟨o, ho⟩ := hm s
  cases o with
  | ok a s' =>
    obtain ⟨o', ho'⟩ := hk a s'
    exact ⟨o', .inl ⟨a, s', ho, ho'⟩⟩
  | trap => exact ⟨.trap, .inr ⟨ho, rfl⟩⟩

theorem total_check (b : Bool) : Total (check b : RM σ Unit) := by
  cases b
  · exact total_fail
  · exact total_pure ()

theorem total_ofOption (x : Option α) : Total (ofOption x : RM σ α) := by
  cases x
  · exact total_fail
  · exact total_pure _

theorem total_get : Total (RM.get : RM σ σ) := fun _ => ⟨_, rfl⟩

theorem total_set (s' : σ) : Total (RM.set s' : RM σ Unit) := fun _ => ⟨_, rfl⟩

/-! ## Commutation -/

theorem comm_none {m : RM σ α} (hm : Total m) {F : τ → Option (β × τ)}
    {k : β → α → RM (σ × τ) γ} {s : σ} {t : τ} (hF : F t = none) (o : Out (σ × τ) γ) :
    (m.onFst >>= fun b => RM.ofTab F >>= fun a => k a b) (s, t) o ↔ o = .trap := by
  rw [bind_apply]
  constructor
  · rintro (⟨b, ⟨s1, t1⟩, ⟨_, ht⟩, h2⟩ | ⟨_, h2⟩)
    · have hF1 : F t1 = none := by rw [show t1 = t from ht]; exact hF
      exact (ofTab_bind_none hF1 _).1 h2
    · exact h2
  · intro ho
    obtain ⟨o1, h1⟩ := hm s
    cases o1 with
    | ok b s1 => exact .inl ⟨b, (s1, t), ⟨h1, rfl⟩, (ofTab_bind_none hF _).2 ho⟩
    | trap => exact .inr ⟨h1, ho⟩

theorem comm_some {m : RM σ α} {F : τ → Option (β × τ)} {k : β → α → RM (σ × τ) γ} {s : σ}
    {t t' : τ} {a : β} (hF : F t = some (a, t')) (o : Out (σ × τ) γ) :
    (m.onFst >>= fun b => RM.ofTab F >>= fun a => k a b) (s, t) o ↔
      (m.onFst >>= fun b => k a b) (s, t') o := by
  rw [bind_apply, bind_apply]
  constructor
  · rintro (⟨b, ⟨s1, t1⟩, ⟨h1, ht⟩, h2⟩ | ⟨h1, h2⟩)
    · have hF1 : F t1 = some (a, t') := by rw [show t1 = t from ht]; exact hF
      exact .inl ⟨b, (s1, t'), ⟨h1, rfl⟩, (ofTab_bind_some hF1 _).1 h2⟩
    · exact .inr ⟨h1, h2⟩
  · rintro (⟨b, ⟨s1, t1⟩, ⟨h1, ht⟩, h2⟩ | ⟨h1, h2⟩)
    · have h2' : k a b (s1, t') o := by rw [show t' = t1 from ht.symm]; exact h2
      exact .inl ⟨b, (s1, t), ⟨h1, rfl⟩, (ofTab_bind_some hF _).2 h2'⟩
    · exact .inr ⟨h1, h2⟩

/-- **A deterministic table operation commutes with a total core computation.** -/
theorem comm_ofTab {m : RM σ α} (hm : Total m) (F : τ → Option (β × τ))
    (k : β → α → RM (σ × τ) γ) :
    (m.onFst >>= fun b => RM.ofTab F >>= fun a => k a b) =
      (RM.ofTab F >>= fun a => m.onFst >>= fun b => k a b) := by
  funext st o
  rcases st with ⟨s, t⟩
  cases hF : F t with
  | none => exact propext ((comm_none hm hF o).trans (ofTab_bind_none hF o).symm)
  | some p =>
    have hF' : F t = some (p.1, p.2) := hF
    exact propext ((comm_some hF' o).trans
      (ofTab_bind_some (k := fun a => m.onFst >>= fun b => k a b) hF' o).symm)

/-- A deterministic operation of the manager, seen from the merged instance. -/
theorem onSnd_ofFn (f : τ → Option (α × τ)) :
    ((RM.ofFn f).onSnd : RM (σ × τ) α) = RM.ofTab f := by
  funext st o
  rcases st with ⟨s, t⟩
  cases o with
  | ok a st' =>
    rcases st' with ⟨s', t'⟩
    simp only [RM.onSnd, RM.ofFn, RM.ofTab]
    cases f t with
    | none => simp
    | some p =>
      rcases p with ⟨a', t''⟩
      simp only [Out.ok.injEq, Prod.mk.injEq, eq_iff_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩
        exact ⟨⟨h1, h2⟩, h3⟩
  | trap =>
    simp only [RM.onSnd, RM.ofFn, RM.ofTab]
    cases f t <;> simp

end Silmaril.Proofs.Wasm.Jco.Res
