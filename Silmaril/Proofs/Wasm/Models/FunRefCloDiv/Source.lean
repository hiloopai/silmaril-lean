module

public import Silmaril.Wasm.Models.FunRefCloDiv.Defs
public import Silmaril.Wasm.Models.FunRefClo.Thms

/-!
# FunRefClo with divergence: inversion of divergence

As `Silmaril.Proofs.Wasm.Models.FunCloDiv.Source`, with the heap threaded from left to right.
`conv_or_div`: a term evaluates with some fuel or diverges. `Typed Γ σ ρ`: some heap typing types
the heap `σ` and the environment `ρ` at `Γ`. For a well-typed term in a typed heap and
environment, divergence of a compound term comes from one of its parts, in evaluation order
(`div_arith`, `div_cmp`, `div_ite`, `div_let`, `div_pair`, `div_fst`, `div_snd`, `div_inl`,
`div_inr`, `div_case`, `div_app`, `div_ref`, `div_get`, `div_set`): either a subterm diverges,
or the subterms before it return values, ending in a heap that is again typed (type
preservation, `FunRefClo.eval_sound`), and the next one diverges from that heap. For an
application whose function and argument return, the closure's body diverges in its typed
environment. Variables, constants and `fix` never diverge (`not_div_var`, `not_div_eval`).

Typing is what excludes stuck terms: it gives the shape of returned values and, for `get` and
`set`, that the location is allocated.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloDiv

open Silmaril.Wasm.Models.FunRefClo (Tm Val Ty Heap eval HasTy ValTy EnvTy HeapTy eval_le
  eval_sound)
open Silmaril.Wasm.Models.FunRefCloDiv (Diverges)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)

/-- A term that returns with some fuel does not diverge. -/
theorem not_div_eval {σ : Heap} {ρ : List Val} {e : Tm} {k : Nat} {r : Val × Heap}
    (h : eval k σ ρ e = some r) : ¬ Diverges σ ρ e :=
  fun hd => absurd ((hd k).symm.trans h) (by simp)

/-- **A term returns with some fuel, or diverges.** -/
theorem conv_or_div (σ : Heap) (ρ : List Val) (e : Tm) :
    (∃ k v σ', eval k σ ρ e = some (v, σ')) ∨ Diverges σ ρ e := by
  by_cases h : ∃ k v σ', eval k σ ρ e = some (v, σ')
  · exact .inl h
  · refine .inr fun k => ?_
    cases hk : eval k σ ρ e with
    | none => rfl
    | some r => exact absurd ⟨k, r.1, r.2, hk⟩ h

/-- Two evaluations at a common fuel. -/
theorem eval_max {k k' : Nat} {σ σ' : Heap} {ρ ρ' : List Val} {a b : Tm} {ra rb : Val × Heap}
    (ha : eval k σ ρ a = some ra) (hb : eval k' σ' ρ' b = some rb) :
    eval (max k k') σ ρ a = some ra ∧ eval (max k k') σ' ρ' b = some rb :=
  ⟨eval_le ha (le_max_left _ _), eval_le hb (le_max_right _ _)⟩

/-- **A typed heap and environment**, for some heap typing. -/
def Typed (Γ : List Ty) (σ : Heap) (ρ : List Val) : Prop :=
  ∃ Ψ, HeapTy Ψ σ ∧ EnvTy Ψ ρ Γ

/-- A returned value is typed, in a typed heap where the environment is still typed. -/
theorem ret_typed {Γ : List Ty} {σ σ₁ : Heap} {ρ : List Val} {e : Tm} {τ : Ty} {k : Nat}
    {v : Val} (ht : HasTy Γ e τ) (hT : Typed Γ σ ρ) (h : eval k σ ρ e = some (v, σ₁)) :
    ∃ Ψ₁, HeapTy Ψ₁ σ₁ ∧ EnvTy Ψ₁ ρ Γ ∧ ValTy Ψ₁ v τ := by
  obtain ⟨Ψ, hσ, hρ⟩ := hT
  obtain ⟨Ψ₁, hΨ, hσ₁, hv⟩ := eval_sound k ht hσ hρ h
  exact ⟨Ψ₁, hσ₁, hρ.mono hΨ, hv⟩

/-- The environment stays typed after a subterm returns. -/
theorem typed_after {Γ : List Ty} {σ σ₁ : Heap} {ρ : List Val} {e : Tm} {τ : Ty} {k : Nat}
    {v : Val} (ht : HasTy Γ e τ) (hT : Typed Γ σ ρ) (h : eval k σ ρ e = some (v, σ₁)) :
    Typed Γ σ₁ ρ :=
  let ⟨Ψ₁, hσ₁, hρ, _⟩ := ret_typed ht hT h
  ⟨Ψ₁, hσ₁, hρ⟩

/-- The environment extended by a returned value is typed. -/
theorem typed_cons {Γ : List Ty} {σ σ₁ : Heap} {ρ : List Val} {e : Tm} {τ : Ty} {k : Nat}
    {v : Val} (ht : HasTy Γ e τ) (hT : Typed Γ σ ρ) (h : eval k σ ρ e = some (v, σ₁)) :
    Typed (τ :: Γ) σ₁ (v :: ρ) :=
  let ⟨Ψ₁, hσ₁, hρ, hv⟩ := ret_typed ht hT h
  ⟨Ψ₁, hσ₁, .cons hv hρ⟩

/-- A variable of a typed environment does not diverge. -/
theorem not_div_var {Γ : List Ty} {σ : Heap} {ρ : List Val} {i : Nat} {τ : Ty}
    (hT : Typed Γ σ ρ) (hi : Γ[i]? = some τ) : ¬ Diverges σ ρ (.var i) := by
  obtain ⟨Ψ, -, hρ⟩ := hT
  obtain ⟨v, hv, -⟩ := hρ.getElem? hi
  have he : eval 1 σ ρ (.var i) = some (v, σ) := by simp only [eval, hv, Option.map_some]
  exact not_div_eval he

/-! ## Compound terms -/

theorem div_arith {Γ : List Ty} {σ : Heap} {ρ : List Val} {op : Arith} {a b : Tm}
    (hT : Typed Γ σ ρ) (ha : HasTy Γ a .int) (hb : HasTy Γ b .int)
    (hd : Diverges σ ρ (.arith op a b)) :
    Diverges σ ρ a ∨ ∃ k x σ₁, eval k σ ρ a = some (.int x, σ₁) ∧ Typed Γ σ₁ ρ ∧
      Diverges σ₁ ρ b := by
  rcases conv_or_div σ ρ a with ⟨ka, va, σ₁, hva⟩ | hda
  · obtain ⟨Ψ₁, hσ₁, hρ₁, hvt⟩ := ret_typed ha hT hva
    obtain ⟨x, rfl⟩ := hvt.int_inv
    refine .inr ⟨ka, x, σ₁, hva, ⟨Ψ₁, hσ₁, hρ₁⟩, ?_⟩
    rcases conv_or_div σ₁ ρ b with ⟨kb, vb, σ₂, hvb⟩ | hdb
    · obtain ⟨Ψ₂, -, -, hvb'⟩ := ret_typed hb ⟨Ψ₁, hσ₁, hρ₁⟩ hvb
      obtain ⟨y, rfl⟩ := hvb'.int_inv
      obtain ⟨h₁, h₂⟩ := eval_max hva hvb
      have he : eval (max ka kb + 1) σ ρ (.arith op a b) = some (.int (op.eval x y), σ₂) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

theorem div_cmp {Γ : List Ty} {σ : Heap} {ρ : List Val} {op : Cmp} {a b : Tm}
    (hT : Typed Γ σ ρ) (ha : HasTy Γ a .int) (hb : HasTy Γ b .int)
    (hd : Diverges σ ρ (.cmp op a b)) :
    Diverges σ ρ a ∨ ∃ k x σ₁, eval k σ ρ a = some (.int x, σ₁) ∧ Typed Γ σ₁ ρ ∧
      Diverges σ₁ ρ b := by
  rcases conv_or_div σ ρ a with ⟨ka, va, σ₁, hva⟩ | hda
  · obtain ⟨Ψ₁, hσ₁, hρ₁, hvt⟩ := ret_typed ha hT hva
    obtain ⟨x, rfl⟩ := hvt.int_inv
    refine .inr ⟨ka, x, σ₁, hva, ⟨Ψ₁, hσ₁, hρ₁⟩, ?_⟩
    rcases conv_or_div σ₁ ρ b with ⟨kb, vb, σ₂, hvb⟩ | hdb
    · obtain ⟨Ψ₂, -, -, hvb'⟩ := ret_typed hb ⟨Ψ₁, hσ₁, hρ₁⟩ hvb
      obtain ⟨y, rfl⟩ := hvb'.int_inv
      obtain ⟨h₁, h₂⟩ := eval_max hva hvb
      have he : eval (max ka kb + 1) σ ρ (.cmp op a b) = some (.bool (op.eval x y), σ₂) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

theorem eval_ite_of {k : Nat} {σ σ₁ : Heap} {ρ : List Val} {c t e : Tm} {b : Bool}
    (h : eval k σ ρ c = some (.bool b, σ₁)) :
    eval (k + 1) σ ρ (.ite c t e) = eval k σ₁ ρ (if b then t else e) := by
  cases b <;> simp only [eval, h, Bool.false_eq_true, ↓reduceIte]

theorem div_ite {Γ : List Ty} {σ : Heap} {ρ : List Val} {c t e : Tm} (hT : Typed Γ σ ρ)
    (hc : HasTy Γ c .bool) (hd : Diverges σ ρ (.ite c t e)) :
    Diverges σ ρ c ∨ ∃ k b σ₁, eval k σ ρ c = some (.bool b, σ₁) ∧ Typed Γ σ₁ ρ ∧
      Diverges σ₁ ρ (if b then t else e) := by
  rcases conv_or_div σ ρ c with ⟨kc, vc, σ₁, hvc⟩ | hdc
  · obtain ⟨Ψ₁, hσ₁, hρ₁, hvt⟩ := ret_typed hc hT hvc
    obtain ⟨b, rfl⟩ := hvt.bool_inv
    refine .inr ⟨kc, b, σ₁, hvc, ⟨Ψ₁, hσ₁, hρ₁⟩, ?_⟩
    rcases conv_or_div σ₁ ρ (if b then t else e) with ⟨kt, vt, σ₂, hvt⟩ | hdt
    · obtain ⟨h₁, h₂⟩ := eval_max hvc hvt
      have he : eval (max kc kt + 1) σ ρ (.ite c t e) = some (vt, σ₂) :=
        (eval_ite_of h₁).trans h₂
      exact absurd hd (not_div_eval he)
    · exact hdt
  · exact .inl hdc

theorem div_let {Γ : List Ty} {σ : Heap} {ρ : List Val} {a b : Tm} {σa : Ty}
    (hT : Typed Γ σ ρ) (ha : HasTy Γ a σa) (hd : Diverges σ ρ (.let_ a b)) :
    Diverges σ ρ a ∨ ∃ k u σ₁, eval k σ ρ a = some (u, σ₁) ∧ Typed (σa :: Γ) σ₁ (u :: ρ) ∧
      Diverges σ₁ (u :: ρ) b := by
  rcases conv_or_div σ ρ a with ⟨ka, u, σ₁, hu⟩ | hda
  · refine .inr ⟨ka, u, σ₁, hu, typed_cons ha hT hu, ?_⟩
    rcases conv_or_div σ₁ (u :: ρ) b with ⟨kb, v, σ₂, hv⟩ | hdb
    · obtain ⟨h₁, h₂⟩ := eval_max hu hv
      have he : eval (max ka kb + 1) σ ρ (.let_ a b) = some (v, σ₂) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

theorem div_pair {Γ : List Ty} {σ : Heap} {ρ : List Val} {a b : Tm} {σa : Ty}
    (hT : Typed Γ σ ρ) (ha : HasTy Γ a σa) (hd : Diverges σ ρ (.pair a b)) :
    Diverges σ ρ a ∨ ∃ k x σ₁, eval k σ ρ a = some (x, σ₁) ∧ Typed Γ σ₁ ρ ∧
      Diverges σ₁ ρ b := by
  rcases conv_or_div σ ρ a with ⟨ka, x, σ₁, hx⟩ | hda
  · refine .inr ⟨ka, x, σ₁, hx, typed_after ha hT hx, ?_⟩
    rcases conv_or_div σ₁ ρ b with ⟨kb, y, σ₂, hy⟩ | hdb
    · obtain ⟨h₁, h₂⟩ := eval_max hx hy
      have he : eval (max ka kb + 1) σ ρ (.pair a b) = some (.pair x y, σ₂) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

theorem div_fst {Γ : List Ty} {σ : Heap} {ρ : List Val} {e : Tm} {σa τ : Ty}
    (hT : Typed Γ σ ρ) (he : HasTy Γ e (.prod σa τ)) (hd : Diverges σ ρ (.fst e)) :
    Diverges σ ρ e := by
  rcases conv_or_div σ ρ e with ⟨k, v, σ₁, hv⟩ | hde
  · obtain ⟨Ψ₁, -, -, hvt⟩ := ret_typed he hT hv
    obtain ⟨x, y, rfl, -, -⟩ := hvt.prod_inv
    have he' : eval (k + 1) σ ρ (.fst e) = some (x, σ₁) := by simp only [eval, hv]
    exact absurd hd (not_div_eval he')
  · exact hde

theorem div_snd {Γ : List Ty} {σ : Heap} {ρ : List Val} {e : Tm} {σa τ : Ty}
    (hT : Typed Γ σ ρ) (he : HasTy Γ e (.prod σa τ)) (hd : Diverges σ ρ (.snd e)) :
    Diverges σ ρ e := by
  rcases conv_or_div σ ρ e with ⟨k, v, σ₁, hv⟩ | hde
  · obtain ⟨Ψ₁, -, -, hvt⟩ := ret_typed he hT hv
    obtain ⟨x, y, rfl, -, -⟩ := hvt.prod_inv
    have he' : eval (k + 1) σ ρ (.snd e) = some (y, σ₁) := by simp only [eval, hv]
    exact absurd hd (not_div_eval he')
  · exact hde

theorem div_inl {σ : Heap} {ρ : List Val} {e : Tm} (hd : Diverges σ ρ (.inl e)) :
    Diverges σ ρ e := by
  rcases conv_or_div σ ρ e with ⟨k, v, σ₁, hv⟩ | hde
  · have he' : eval (k + 1) σ ρ (.inl e) = some (.inl v, σ₁) := by
      simp only [eval, hv, Option.map]
    exact absurd hd (not_div_eval he')
  · exact hde

theorem div_inr {σ : Heap} {ρ : List Val} {e : Tm} (hd : Diverges σ ρ (.inr e)) :
    Diverges σ ρ e := by
  rcases conv_or_div σ ρ e with ⟨k, v, σ₁, hv⟩ | hde
  · have he' : eval (k + 1) σ ρ (.inr e) = some (.inr v, σ₁) := by
      simp only [eval, hv, Option.map]
    exact absurd hd (not_div_eval he')
  · exact hde

/-- A `case` whose scrutinee returns `inl u` or `inr u` diverges in the selected branch. -/
theorem div_case_branch {σ σ₁ : Heap} {ρ : List Val} {e l r : Tm} {k : Nat} {w : Val}
    (hu : eval k σ ρ e = some (w, σ₁)) (hd : Diverges σ ρ (.case e l r)) :
    ∀ v, (w = .inl v → Diverges σ₁ (v :: ρ) l) ∧ (w = .inr v → Diverges σ₁ (v :: ρ) r) := by
  intro v
  constructor
  · rintro rfl
    rcases conv_or_div σ₁ (v :: ρ) l with ⟨kl, x, σ₂, hx⟩ | hdl
    · obtain ⟨h₁, h₂⟩ := eval_max hu hx
      have he : eval (max k kl + 1) σ ρ (.case e l r) = some (x, σ₂) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdl
  · rintro rfl
    rcases conv_or_div σ₁ (v :: ρ) r with ⟨kr, x, σ₂, hx⟩ | hdr
    · obtain ⟨h₁, h₂⟩ := eval_max hu hx
      have he : eval (max k kr + 1) σ ρ (.case e l r) = some (x, σ₂) := by
        simp only [eval, h₁, h₂]
      exact absurd hd (not_div_eval he)
    · exact hdr

theorem div_case {Γ : List Ty} {σ : Heap} {ρ : List Val} {e l r : Tm} {σa τ : Ty}
    (hT : Typed Γ σ ρ) (he : HasTy Γ e (.sum σa τ)) (hd : Diverges σ ρ (.case e l r)) :
    Diverges σ ρ e ∨
      (∃ k u σ₁, eval k σ ρ e = some (.inl u, σ₁) ∧ Typed (σa :: Γ) σ₁ (u :: ρ) ∧
        Diverges σ₁ (u :: ρ) l) ∨
      (∃ k u σ₁, eval k σ ρ e = some (.inr u, σ₁) ∧ Typed (τ :: Γ) σ₁ (u :: ρ) ∧
        Diverges σ₁ (u :: ρ) r) := by
  rcases conv_or_div σ ρ e with ⟨k, w, σ₁, hw⟩ | hde
  · obtain ⟨Ψ₁, hσ₁, hρ₁, hwt⟩ := ret_typed he hT hw
    rcases hwt.sum_inv with ⟨u, rfl, hu⟩ | ⟨u, rfl, hu⟩
    · exact .inr (.inl ⟨k, u, σ₁, hw, ⟨Ψ₁, hσ₁, .cons hu hρ₁⟩, (div_case_branch hw hd u).1 rfl⟩)
    · exact .inr (.inr ⟨k, u, σ₁, hw, ⟨Ψ₁, hσ₁, .cons hu hρ₁⟩, (div_case_branch hw hd u).2 rfl⟩)
  · exact .inl hde

/-- An application whose function and argument return diverges in the closure's body. -/
theorem div_app_body {σ σ₁ σ₂ : Heap} {ρ : List Val} {f a : Tm} {k : Nat} {b : Tm}
    {ρ' : List Val} {u : Val} (hf : eval k σ ρ f = some (.clo b ρ', σ₁))
    (ha : eval k σ₁ ρ a = some (u, σ₂)) (hd : Diverges σ ρ (.app f a)) :
    Diverges σ₂ (u :: .clo b ρ' :: ρ') b := by
  rcases conv_or_div σ₂ (u :: .clo b ρ' :: ρ') b with ⟨kb, w, σ₃, hw⟩ | hdb
  · obtain ⟨h₁, h₂⟩ := eval_max hf hw
    have h₃ : eval (max k kb) σ₁ ρ a = some (u, σ₂) := eval_le ha (le_max_left _ _)
    have he : eval (max k kb + 1) σ ρ (.app f a) = some (w, σ₃) := by
      simp only [eval, h₁, h₂, h₃]
    exact absurd hd (not_div_eval he)
  · exact hdb

theorem div_app {Γ : List Ty} {σ : Heap} {ρ : List Val} {f a : Tm} {σa τ : Ty}
    (hT : Typed Γ σ ρ) (hf : HasTy Γ f (.arr σa τ)) (ha : HasTy Γ a σa)
    (hd : Diverges σ ρ (.app f a)) :
    Diverges σ ρ f ∨
      (∃ k b ρ' σ₁, eval k σ ρ f = some (.clo b ρ', σ₁) ∧ Typed Γ σ₁ ρ ∧ Diverges σ₁ ρ a) ∨
      ∃ k b ρ' σ₁ u σ₂ Γb, eval k σ ρ f = some (.clo b ρ', σ₁) ∧
        eval k σ₁ ρ a = some (u, σ₂) ∧ Typed Γb σ₂ (u :: .clo b ρ' :: ρ') ∧ HasTy Γb b τ ∧
        Diverges σ₂ (u :: .clo b ρ' :: ρ') b := by
  rcases conv_or_div σ ρ f with ⟨kf, vf, σ₁, hvf⟩ | hdf
  · obtain ⟨Ψ₁, hσ₁, hρ₁, hvt⟩ := ret_typed hf hT hvf
    obtain ⟨b, ρ', Γ', rfl, hρ', hb⟩ := hvt.arr_inv
    rcases conv_or_div σ₁ ρ a with ⟨ka, u, σ₂, hu⟩ | hda
    · obtain ⟨Ψ₂, hΨ, hσ₂, hut⟩ := eval_sound ka ha hσ₁ hρ₁ hu
      obtain ⟨h₁, h₂⟩ := eval_max hvf hu
      have henv : Typed (σa :: .arr σa τ :: Γ') σ₂ (u :: .clo b ρ' :: ρ') :=
        ⟨Ψ₂, hσ₂, .cons hut (.cons (hvt.mono hΨ) (hρ'.mono hΨ))⟩
      exact .inr (.inr ⟨_, b, ρ', σ₁, u, σ₂, _, h₁, h₂, henv, hb, div_app_body h₁ h₂ hd⟩)
    · exact .inr (.inl ⟨kf, b, ρ', σ₁, hvf, ⟨Ψ₁, hσ₁, hρ₁⟩, hda⟩)
  · exact .inl hdf

theorem div_ref {σ : Heap} {ρ : List Val} {e : Tm} (hd : Diverges σ ρ (.ref e)) :
    Diverges σ ρ e := by
  rcases conv_or_div σ ρ e with ⟨k, v, σ₁, hv⟩ | hde
  · have he' : eval (k + 1) σ ρ (.ref e) = some (.loc σ₁.length, σ₁ ++ [v]) := by
      simp only [eval, hv]
    exact absurd hd (not_div_eval he')
  · exact hde

/-- A location of a typed heap is allocated. -/
theorem lt_of_loc {Ψ : List Ty} {σ : Heap} {l : Nat} {τ : Ty} (hσ : HeapTy Ψ σ)
    (hl : Ψ[l]? = some τ) : l < σ.length := by
  rw [List.Forall₂.length_eq hσ]
  exact (List.getElem?_eq_some_iff.1 hl).1

theorem div_get {Γ : List Ty} {σ : Heap} {ρ : List Val} {e : Tm} {τ : Ty}
    (hT : Typed Γ σ ρ) (he : HasTy Γ e (.ref τ)) (hd : Diverges σ ρ (.get e)) :
    Diverges σ ρ e := by
  rcases conv_or_div σ ρ e with ⟨k, v, σ₁, hv⟩ | hde
  · obtain ⟨Ψ₁, hσ₁, -, hvt⟩ := ret_typed he hT hv
    obtain ⟨l, rfl, hl⟩ := hvt.ref_inv
    have hlt := lt_of_loc hσ₁ hl
    have he' : eval (k + 1) σ ρ (.get e) = some (σ₁[l], σ₁) := by
      simp only [eval, hv, List.getElem?_eq_getElem hlt, Option.map_some]
    exact absurd hd (not_div_eval he')
  · exact hde

theorem div_set {Γ : List Ty} {σ : Heap} {ρ : List Val} {a b : Tm} {τ : Ty}
    (hT : Typed Γ σ ρ) (ha : HasTy Γ a (.ref τ)) (hb : HasTy Γ b τ)
    (hd : Diverges σ ρ (.set a b)) :
    Diverges σ ρ a ∨ ∃ k l σ₁, eval k σ ρ a = some (.loc l, σ₁) ∧ Typed Γ σ₁ ρ ∧
      Diverges σ₁ ρ b := by
  rcases conv_or_div σ ρ a with ⟨ka, va, σ₁, hva⟩ | hda
  · obtain ⟨Ψ₁, hσ₁, hρ₁, hvt⟩ := ret_typed ha hT hva
    obtain ⟨l, rfl, hl⟩ := hvt.ref_inv
    refine .inr ⟨ka, l, σ₁, hva, ⟨Ψ₁, hσ₁, hρ₁⟩, ?_⟩
    rcases conv_or_div σ₁ ρ b with ⟨kb, vb, σ₂, hvb⟩ | hdb
    · obtain ⟨Ψ₂, hΨ, hσ₂, -⟩ := eval_sound kb hb hσ₁ hρ₁ hvb
      have hlt : l < σ₂.length :=
        lt_of_loc hσ₂ (Silmaril.Wasm.Models.FunRef.getElem?_of_prefix hΨ hl)
      obtain ⟨h₁, h₂⟩ := eval_max hva hvb
      have he : eval (max ka kb + 1) σ ρ (.set a b) = some (.bool true, σ₂.set l vb) := by
        simp only [eval, h₁, h₂, hlt, ↓reduceIte]
      exact absurd hd (not_div_eval he)
    · exact hdb
  · exact .inl hda

end Silmaril.Proofs.Wasm.Models.FunRefCloDiv
