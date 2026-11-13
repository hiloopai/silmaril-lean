module

public import Silmaril.Wasm.Component.Reference.Canon.Prog.Defs

/-!
# `Canon.Prog`: laws of the component reference

Theorems of the component reference copy `Canon.Prog`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Prog`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

universe u v w

namespace Prog

variable {S : Sig} {α β γ : Type}

section eval

variable {σ : Type u} {H : (o : S.Op) → σ → S.Resp o → σ → Prop}

theorem Eval.op_inv {o : S.Op} {k : S.Resp o → Prog S α} {s s' : σ} {a : α}
    (h : Eval H (.op o k) s a s') : ∃ r s₁, H o s r s₁ ∧ Eval H (k r) s₁ a s' := by
  cases h with
  | op r hH hk => exact ⟨r, _, hH, hk⟩

theorem eval_op_iff {o : S.Op} {k : S.Resp o → Prog S α} {s s' : σ} {a : α} :
    Eval H (.op o k) s a s' ↔ ∃ r s₁, H o s r s₁ ∧ Eval H (k r) s₁ a s' :=
  ⟨Eval.op_inv, fun ⟨r, _, hH, hk⟩ => Eval.op r hH hk⟩

theorem eval_lift_iff {o : S.Op} {s s' : σ} {r : S.Resp o} :
    Eval H (lift o) s r s' ↔ H o s r s' := by
  simp only [lift, eval_op_iff, eval_pure_iff]
  constructor
  · rintro ⟨r', s₁, hH, rfl, rfl⟩; exact hH
  · intro hH; exact ⟨r, s', hH, rfl, rfl⟩

/-- Evaluation of a sequential composition. -/
theorem Eval.bind {p : Prog S α} {f : α → Prog S β} {s s₁ s₂ : σ} {a : α} {b : β}
    (hp : Eval H p s a s₁) (hf : Eval H (f a) s₁ b s₂) : Eval H (p >>= f) s b s₂ := by
  induction hp with
  | pure => exact hf
  | op r hH _ ih => exact Eval.op r hH (ih hf)

/-- Inversion of evaluation of a sequential composition. -/
theorem Eval.bind_inv {p : Prog S α} {f : α → Prog S β} {s s₂ : σ} {b : β}
    (h : Eval H (p >>= f) s b s₂) :
    ∃ a s₁, Eval H p s a s₁ ∧ Eval H (f a) s₁ b s₂ := by
  induction p generalizing s with
  | pure a => exact ⟨a, s, Eval.pure a s, h⟩
  | op o k ih =>
    obtain ⟨r, s₁, hH, hk⟩ := Eval.op_inv (k := fun r => (k r).bind f) h
    obtain ⟨a, s₃, hka, hfa⟩ := ih r hk
    exact ⟨a, s₃, Eval.op r hH hka, hfa⟩

theorem eval_bind_iff {p : Prog S α} {f : α → Prog S β} {s s₂ : σ} {b : β} :
    Eval H (p >>= f) s b s₂ ↔ ∃ a s₁, Eval H p s a s₁ ∧ Eval H (f a) s₁ b s₂ :=
  ⟨Eval.bind_inv, fun ⟨_, _, hp, hf⟩ => hp.bind hf⟩

end eval

section every

variable {P Q : S.Op → Prop}

theorem every_op_iff {o : S.Op} {k : S.Resp o → Prog S α} :
    Every P (.op o k) ↔ P o ∧ ∀ r, Every P (k r) := by
  constructor
  · intro h; cases h with
    | op ho hk => exact ⟨ho, hk⟩
  · rintro ⟨ho, hk⟩; exact Every.op ho hk

theorem Every.lift {o : S.Op} (h : P o) : Every P (lift o) :=
  Every.op h (fun r => Every.pure r)

theorem Every.bind {p : Prog S α} {f : α → Prog S β} (hp : Every P p)
    (hf : ∀ a, Every P (f a)) : Every P (p >>= f) := by
  induction hp with
  | pure a => exact hf a
  | op ho _ ih => exact Every.op ho ih

end every

theorem foldlM_eq_list_foldlM (f : β → α → Prog S β) (b : β) (xs : List α) :
    foldlM f b xs = List.foldlM f b xs := by
  induction xs generalizing b with
  | nil => rfl
  | cons a as ih => simp only [foldlM_cons, List.foldlM_cons, ih, bind_eq]

section everyList

variable {P : S.Op → Prop}

theorem Every.mapM {f : α → Prog S β} {xs : List α} (h : ∀ a ∈ xs, Every P (f a)) :
    Every P (mapM f xs) := by
  induction xs with
  | nil => exact Every.pure _
  | cons a as ih =>
    exact Every.bind (h a (List.mem_cons_self ..)) fun _ =>
      Every.bind (ih fun x hx => h x (List.mem_cons_of_mem _ hx)) fun _ => Every.pure _

theorem Every.forM {f : α → Prog S PUnit} {xs : List α} (h : ∀ a ∈ xs, Every P (f a)) :
    Every P (forM xs f) := by
  induction xs with
  | nil => exact Every.pure _
  | cons a as ih =>
    exact Every.bind (h a (List.mem_cons_self ..)) fun _ =>
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem Every.foldlM {f : β → α → Prog S β} {b : β} {xs : List α}
    (h : ∀ b, ∀ a ∈ xs, Every P (f b a)) : Every P (foldlM f b xs) := by
  induction xs generalizing b with
  | nil => exact Every.pure _
  | cons a as ih =>
    exact Every.bind (h b a (List.mem_cons_self ..)) fun b' =>
      ih (b := b') fun b x hx => h b x (List.mem_cons_of_mem _ hx)

end everyList

end Prog

end Silmaril.Wasm.Component.Canon
