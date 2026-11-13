module

public import Silmaril.Wasm.Models.FunCloDiv.Defs
public import Silmaril.Wasm.Models.FunClo.Thms

/-!
# FunClo with divergence: inversion of divergence

`conv_or_div`: a term evaluates with some fuel or diverges. For a well-typed term in a typed
environment, divergence of a compound term comes from one of its parts, in evaluation order
(`div_arith`, `div_cmp`, `div_ite`, `div_let`, `div_pair`, `div_fst`, `div_snd`, `div_inl`,
`div_inr`, `div_case`, `div_app`): either a subterm diverges, or the subterms before it return
values and the next one diverges. For an application whose function and argument return, the
closure's body diverges in its typed environment. Variables, constants and `fix` never diverge
(`not_div_var`, `not_div_eval`).

Typing is what excludes stuck terms: `Diverges` alone (no fuel gives a value) would also hold of
a term that is stuck, such as `fst 1`.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloDiv

open Silmaril.Wasm.Models.FunClo (Tm Val Ty eval HasTy ValTy EnvTy eval_le eval_sound)
open Silmaril.Wasm.Models.FunCloDiv (Diverges)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)

/-- A term that returns with some fuel does not diverge. -/
theorem not_div_eval {ρ : List Val} {e : Tm} {k : Nat} {v : Val} (h : eval k ρ e = some v) :
    ¬ Diverges ρ e :=
  fun hd => absurd ((hd k).symm.trans h) (by simp)

/-- **A term returns with some fuel, or diverges.** -/
theorem conv_or_div (ρ : List Val) (e : Tm) : (∃ k v, eval k ρ e = some v) ∨ Diverges ρ e := by
  by_cases h : ∃ k v, eval k ρ e = some v
  · exact .inl h
  · refine .inr fun k => ?_
    cases hk : eval k ρ e with
    | none => rfl
    | some v => exact absurd ⟨k, v, hk⟩ h

/-- Two evaluations at a common fuel. -/
theorem eval_max {k k' : Nat} {ρ ρ' : List Val} {a b : Tm} {va vb : Val}
    (ha : eval k ρ a = some va) (hb : eval k' ρ' b = some vb) :
    eval (max k k') ρ a = some va ∧ eval (max k k') ρ' b = some vb :=
  ⟨eval_le ha (le_max_left _ _), eval_le hb (le_max_right _ _)⟩

theorem EnvTy.length : ∀ {ρ : List Val} {Γ : List Ty}, EnvTy ρ Γ → ρ.length = Γ.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg (· + 1) (EnvTy.length h)

/-- A variable of a typed environment does not diverge. -/
theorem not_div_var {Γ : List Ty} {ρ : List Val} {i : Nat} {τ : Ty} (hρ : EnvTy ρ Γ)
    (hi : Γ[i]? = some τ) : ¬ Diverges ρ (.var i) := by
  have hlt : i < ρ.length := by
    rw [EnvTy.length hρ]; exact (List.getElem?_eq_some_iff.1 hi).1
  have he : eval 1 ρ (.var i) = some ρ[i] := by
    simp only [eval]; exact List.getElem?_eq_getElem hlt
  exact not_div_eval he

/-! ## Compound terms -/

theorem div_arith {Γ : List Ty} {ρ : List Val} {op : Arith} {a b : Tm} (hρ : EnvTy ρ Γ)
    (ha : HasTy Γ a .int) (hb : HasTy Γ b .int) (hd : Diverges ρ (.arith op a b)) :
    Diverges ρ a ∨ ∃ k x, eval k ρ a = some (.int x) ∧ Diverges ρ b := by
  rcases conv_or_div ρ a with ⟨ka, va, hva⟩ | hda
  · obtain ⟨x, hx⟩ := (eval_sound ka ha hρ hva).int_inv
    refine .inr ⟨ka, x, hx ▸ hva, ?_⟩
    rcases conv_or_div ρ b with ⟨kb, vb, hvb⟩ | hdb
    · obtain ⟨y, hy⟩ := (eval_sound kb hb hρ hvb).int_inv
      obtain ⟨h₁, h₂⟩ := eval_max (hx ▸ hva) (hy ▸ hvb)
      have he : eval (max ka kb + 1) ρ (.arith op a b) = some (.int (op.eval x y)) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

theorem div_cmp {Γ : List Ty} {ρ : List Val} {op : Cmp} {a b : Tm} (hρ : EnvTy ρ Γ)
    (ha : HasTy Γ a .int) (hb : HasTy Γ b .int) (hd : Diverges ρ (.cmp op a b)) :
    Diverges ρ a ∨ ∃ k x, eval k ρ a = some (.int x) ∧ Diverges ρ b := by
  rcases conv_or_div ρ a with ⟨ka, va, hva⟩ | hda
  · obtain ⟨x, hx⟩ := (eval_sound ka ha hρ hva).int_inv
    refine .inr ⟨ka, x, hx ▸ hva, ?_⟩
    rcases conv_or_div ρ b with ⟨kb, vb, hvb⟩ | hdb
    · obtain ⟨y, hy⟩ := (eval_sound kb hb hρ hvb).int_inv
      obtain ⟨h₁, h₂⟩ := eval_max (hx ▸ hva) (hy ▸ hvb)
      have he : eval (max ka kb + 1) ρ (.cmp op a b) = some (.bool (op.eval x y)) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

theorem eval_ite_of {k : Nat} {ρ : List Val} {c t e : Tm} {b : Bool}
    (h : eval k ρ c = some (.bool b)) :
    eval (k + 1) ρ (.ite c t e) = eval k ρ (if b then t else e) := by
  cases b <;> simp only [eval, h, Bool.false_eq_true, ↓reduceIte]

theorem div_ite {Γ : List Ty} {ρ : List Val} {c t e : Tm} (hρ : EnvTy ρ Γ)
    (hc : HasTy Γ c .bool) (hd : Diverges ρ (.ite c t e)) :
    Diverges ρ c ∨ ∃ k b, eval k ρ c = some (.bool b) ∧ Diverges ρ (if b then t else e) := by
  rcases conv_or_div ρ c with ⟨kc, vc, hvc⟩ | hdc
  · obtain ⟨b, hb⟩ := (eval_sound kc hc hρ hvc).bool_inv
    refine .inr ⟨kc, b, hb ▸ hvc, ?_⟩
    rcases conv_or_div ρ (if b then t else e) with ⟨kt, vt, hvt⟩ | hdt
    · obtain ⟨h₁, h₂⟩ := eval_max (hb ▸ hvc) hvt
      have he : eval (max kc kt + 1) ρ (.ite c t e) = some vt := (eval_ite_of h₁).trans h₂
      exact absurd hd (not_div_eval he)
    · exact hdt
  · exact .inl hdc

theorem div_let {ρ : List Val} {a b : Tm} (hd : Diverges ρ (.let_ a b)) :
    Diverges ρ a ∨ ∃ k u, eval k ρ a = some u ∧ Diverges (u :: ρ) b := by
  rcases conv_or_div ρ a with ⟨ka, u, hu⟩ | hda
  · refine .inr ⟨ka, u, hu, ?_⟩
    rcases conv_or_div (u :: ρ) b with ⟨kb, v, hv⟩ | hdb
    · obtain ⟨h₁, h₂⟩ := eval_max hu hv
      have he : eval (max ka kb + 1) ρ (.let_ a b) = some v := by simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

theorem div_pair {ρ : List Val} {a b : Tm} (hd : Diverges ρ (.pair a b)) :
    Diverges ρ a ∨ ∃ k x, eval k ρ a = some x ∧ Diverges ρ b := by
  rcases conv_or_div ρ a with ⟨ka, x, hx⟩ | hda
  · refine .inr ⟨ka, x, hx, ?_⟩
    rcases conv_or_div ρ b with ⟨kb, y, hy⟩ | hdb
    · obtain ⟨h₁, h₂⟩ := eval_max hx hy
      have he : eval (max ka kb + 1) ρ (.pair a b) = some (.pair x y) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

theorem div_fst {Γ : List Ty} {ρ : List Val} {e : Tm} {σ τ : Ty} (hρ : EnvTy ρ Γ)
    (he : HasTy Γ e (.prod σ τ)) (hd : Diverges ρ (.fst e)) : Diverges ρ e := by
  rcases conv_or_div ρ e with ⟨k, v, hv⟩ | hde
  · obtain ⟨x, y, hxy, -, -⟩ := (eval_sound k he hρ hv).prod_inv
    have he' : eval (k + 1) ρ (.fst e) = some x := by simp only [eval, hxy ▸ hv]
    exact absurd hd (not_div_eval he')
  · exact hde

theorem div_snd {Γ : List Ty} {ρ : List Val} {e : Tm} {σ τ : Ty} (hρ : EnvTy ρ Γ)
    (he : HasTy Γ e (.prod σ τ)) (hd : Diverges ρ (.snd e)) : Diverges ρ e := by
  rcases conv_or_div ρ e with ⟨k, v, hv⟩ | hde
  · obtain ⟨x, y, hxy, -, -⟩ := (eval_sound k he hρ hv).prod_inv
    have he' : eval (k + 1) ρ (.snd e) = some y := by simp only [eval, hxy ▸ hv]
    exact absurd hd (not_div_eval he')
  · exact hde

theorem div_inl {ρ : List Val} {e : Tm} (hd : Diverges ρ (.inl e)) : Diverges ρ e := by
  rcases conv_or_div ρ e with ⟨k, v, hv⟩ | hde
  · have he' : eval (k + 1) ρ (.inl e) = some (.inl v) := by simp only [eval, hv, Option.map]
    exact absurd hd (not_div_eval he')
  · exact hde

theorem div_inr {ρ : List Val} {e : Tm} (hd : Diverges ρ (.inr e)) : Diverges ρ e := by
  rcases conv_or_div ρ e with ⟨k, v, hv⟩ | hde
  · have he' : eval (k + 1) ρ (.inr e) = some (.inr v) := by simp only [eval, hv, Option.map]
    exact absurd hd (not_div_eval he')
  · exact hde

/-- A `case` whose scrutinee returns `inl u` diverges in its branch. -/
theorem div_case_branch {ρ : List Val} {e l r : Tm} {k : Nat} {u : Val}
    (hu : eval k ρ e = some u) (hd : Diverges ρ (.case e l r)) :
    ∀ v, (u = .inl v → Diverges (v :: ρ) l) ∧ (u = .inr v → Diverges (v :: ρ) r) := by
  intro v
  constructor
  · intro huv
    rcases conv_or_div (v :: ρ) l with ⟨kl, w, hw⟩ | hdl
    · obtain ⟨h₁, h₂⟩ := eval_max (huv ▸ hu) hw
      have he : eval (max k kl + 1) ρ (.case e l r) = some w := by simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdl
  · intro huv
    rcases conv_or_div (v :: ρ) r with ⟨kr, w, hw⟩ | hdr
    · obtain ⟨h₁, h₂⟩ := eval_max (huv ▸ hu) hw
      have he : eval (max k kr + 1) ρ (.case e l r) = some w := by simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdr

theorem div_case {Γ : List Ty} {ρ : List Val} {e l r : Tm} {σ τ : Ty} (hρ : EnvTy ρ Γ)
    (he : HasTy Γ e (.sum σ τ)) (hd : Diverges ρ (.case e l r)) :
    Diverges ρ e ∨
      (∃ k u, eval k ρ e = some (.inl u) ∧ ValTy u σ ∧ Diverges (u :: ρ) l) ∨
      (∃ k u, eval k ρ e = some (.inr u) ∧ ValTy u τ ∧ Diverges (u :: ρ) r) := by
  rcases conv_or_div ρ e with ⟨k, v, hv⟩ | hde
  · rcases (eval_sound k he hρ hv).sum_inv with ⟨u, rfl, hu⟩ | ⟨u, rfl, hu⟩
    · exact .inr (.inl ⟨k, u, hv, hu, (div_case_branch hv hd u).1 rfl⟩)
    · exact .inr (.inr ⟨k, u, hv, hu, (div_case_branch hv hd u).2 rfl⟩)
  · exact .inl hde

/-- An application whose function and argument return diverges in the closure's body. -/
theorem div_app_body {ρ : List Val} {f a : Tm} {k : Nat} {b : Tm} {ρ' : List Val} {u : Val}
    (hf : eval k ρ f = some (.clo b ρ')) (ha : eval k ρ a = some u)
    (hd : Diverges ρ (.app f a)) : Diverges (u :: .clo b ρ' :: ρ') b := by
  rcases conv_or_div (u :: .clo b ρ' :: ρ') b with ⟨kb, w, hw⟩ | hdb
  · obtain ⟨h₁, h₂⟩ := eval_max hf hw
    have h₃ : eval (max k kb) ρ a = some u := eval_le ha (le_max_left _ _)
    have he : eval (max k kb + 1) ρ (.app f a) = some w := by simp only [eval, h₁, h₂, h₃]
    exact absurd hd (not_div_eval he)
  · exact hdb

theorem div_app {Γ : List Ty} {ρ : List Val} {f a : Tm} {σ τ : Ty} (hρ : EnvTy ρ Γ)
    (hf : HasTy Γ f (.arr σ τ)) (ha : HasTy Γ a σ) (hd : Diverges ρ (.app f a)) :
    Diverges ρ f ∨ (∃ k b ρ', eval k ρ f = some (.clo b ρ') ∧ Diverges ρ a) ∨
      ∃ k b ρ' u Γb, eval k ρ f = some (.clo b ρ') ∧ eval k ρ a = some u ∧
        EnvTy (u :: .clo b ρ' :: ρ') Γb ∧ HasTy Γb b τ ∧ Diverges (u :: .clo b ρ' :: ρ') b := by
  rcases conv_or_div ρ f with ⟨kf, vf, hvf⟩ | hdf
  · have hvt : ValTy vf (.arr σ τ) := eval_sound kf hf hρ hvf
    obtain ⟨b, ρ', Γ', rfl, hρ', hb⟩ := hvt.arr_inv
    rcases conv_or_div ρ a with ⟨ka, u, hu⟩ | hda
    · obtain ⟨h₁, h₂⟩ := eval_max hvf hu
      have henv : EnvTy (u :: .clo b ρ' :: ρ') (σ :: .arr σ τ :: Γ') :=
        .cons (eval_sound _ ha hρ h₂) (.cons hvt hρ')
      exact .inr (.inr ⟨_, b, ρ', u, _, h₁, h₂, henv, hb, div_app_body h₁ h₂ hd⟩)
    · exact .inr (.inl ⟨kf, b, ρ', hvf, hda⟩)
  · exact .inl hdf

end Silmaril.Proofs.Wasm.Models.FunCloDiv
