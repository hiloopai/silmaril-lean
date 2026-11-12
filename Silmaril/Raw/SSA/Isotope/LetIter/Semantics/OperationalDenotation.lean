module

public import Silmaril.Raw.SSA.Isotope.Semantics.Environment
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Monadic
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Operational

/-! # Agreement of operational and stateful powerset interpretations -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetIter.Semantics

open LocallyNameless
open Isotope.Semantics

variable {κ : Type u} (F : κ → Type u) {ν : Type v} [DecidableEq ν]
  {Φ : Type w} [HasTy Φ (Ty κ)] {σ : Type u}

/-- Visible names in the runtime environment represent the typed environment. -/
abbrev FreeEncodes {Γ : Ctx ν (Ty κ)} (γ : Isotope.Semantics.FreeEnv (Ty.denote F) Γ)
    (free : FreeEnv ν (Sigma F)) : Prop :=
  Isotope.Semantics.FreeEnv.Encodes F γ free

/-- Every runtime bound slot represents its corresponding typed value. -/
abbrev BoundEncodes {n : Nat} {β : BoundCtx (Ty κ) n}
    (ρ : Isotope.Semantics.BoundEnv (Ty.denote F) β) (bound : BoundEnv (Sigma F) n) : Prop :=
  Isotope.Semantics.BoundEnv.Encodes F ρ bound

theorem BoundEncodes.snoc {n : Nat} {β : BoundCtx (Ty κ) n} {A : Ty κ}
    {ρ : Isotope.Semantics.BoundEnv (Ty.denote F) β} {bound : BoundEnv (Sigma F) n}
    (h : BoundEncodes F ρ bound) (a : Ty.denote F A) :
    BoundEncodes F (ρ.snoc a) (extend bound (encodeValue F A a)) :=
  Fin.cases rfl h

omit [DecidableEq ν] [HasTy Φ (Ty κ)] in
/-- A body-level agreement lifts to the two independently defined finite iteration relations. -/
theorem loop_iff_iterates {n : Nat} {A B : Ty κ} (bound : BoundEnv (Sigma F) n)
    (body : Tm ν Φ (n + 1)) (free : FreeEnv ν (Sigma F))
    (instr : Φ → Value (Sigma F) → σ → Value (Sigma F) → σ → Prop)
    (f : Ty.denote F A → StateT σ SetM (Ty.denote F B ⊕ Ty.denote F A))
    (agree : ∀ a s value s',
      Eval instr free (extend bound (encodeValue F A a)) body s value s' ↔
        ∃ result, value = encodeValue F (.coprod B A) result ∧ (result, s') ∈ (f a s).run)
    (a : Ty.denote F A) (s : σ) (value : Value (Sigma F)) (s' : σ) :
    Loop instr free bound body (encodeValue F A a) s value s' ↔
      ∃ b, value = encodeValue F B b ∧ Stateful.Iterates f a s b s' := by
  constructor
  · intro h
    generalize currentEq : encodeValue F A a = current at h
    induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) generalizing a with
    | done step _ =>
        cases currentEq
        obtain ⟨result, hv, hs⟩ := (agree a ..).mp step
        cases result with
        | inl b => exact ⟨b, Value.inl.inj hv, .done hs⟩
        | inr _ => cases hv
    | step head tail _ ih =>
        cases currentEq
        obtain ⟨result, hv, hs⟩ := (agree a ..).mp head
        cases result with
        | inl _ => cases hv
        | inr next =>
            obtain ⟨b, hb, ht⟩ := ih agree next (Value.inr.inj hv).symm
            exact ⟨b, hb, .more hs ht⟩
    | _ => trivial
  · rintro ⟨b, rfl, run⟩
    induction run with
    | done step => exact .done ((agree ..).mpr ⟨.inl _, rfl, step⟩)
    | more head tail ih => exact .step ((agree ..).mpr ⟨.inr _, rfl, head⟩) ih

variable (M : InstructionModel (Ty.denote F) Φ (StateT σ SetM))
    (instr : Φ → Value (Sigma F) → σ → Value (Sigma F) → σ → Prop)
    (compatible : M.Compatible F instr)

include compatible
/-- All finite runtime outcomes, including their final states, are exactly the
encoded outcomes of the existing typed monadic interpretation. -/
theorem eval_iff_denote {Γ : Ctx ν (Ty κ)} {n : Nat} {β : BoundCtx (Ty κ) n}
    {t : Tm ν Φ n} {A : Ty κ} (d : Derivation Φ Γ β t A) :
    ∀ (γ : Isotope.Semantics.FreeEnv (Ty.denote F) Γ)
      (ρ : Isotope.Semantics.BoundEnv (Ty.denote F) β)
      (free : FreeEnv ν (Sigma F)) (bound : BoundEnv (Sigma F) n),
      FreeEncodes F γ free → BoundEncodes F ρ bound → ∀ s value s',
      Eval instr free bound t s value s' ↔
        ∃ a, value = encodeValue F A a ∧ (a, s') ∈ (d.denote (Ty.denote F) M γ ρ s).run := by
  induction d with
  | fv h =>
      intro γ ρ free bound hf hb s value s'
      constructor
      · intro run
        cases run
        exact ⟨_, hf _ _ h, rfl⟩
      · rintro ⟨a, rfl, hm⟩
        have hm' : a = γ _ _ h ∧ s' = s := (Stateful.mem_pure ..).mp hm
        obtain ⟨rfl, rfl⟩ := hm'
        rw [← hf _ _ h]
        exact .fv
  | bv =>
      intro γ ρ free bound hf hb s value s'
      constructor
      · intro run
        cases run
        exact ⟨_, hb _, rfl⟩
      · rintro ⟨a, rfl, hm⟩
        have hm' : a = ρ _ ∧ s' = s := (Stateful.mem_pure ..).mp hm
        obtain ⟨rfl, rfl⟩ := hm'
        rw [← hb _]
        exact .bv
  | unit =>
      intro γ ρ free bound hf hb s value s'
      constructor
      · intro run
        cases run
        exact ⟨PUnit.unit, rfl, rfl⟩
      · rintro ⟨a, rfl, hm⟩
        have hm' : a = PUnit.unit ∧ s' = s := (Stateful.mem_pure ..).mp hm
        obtain ⟨rfl, rfl⟩ := hm'
        exact .unit
  | op arg ih =>
      intro γ ρ free bound hf hb s value s'
      simp only [Derivation.denote, Stateful.mem_bind]
      constructor
      · intro run
        cases run with
        | op ha step =>
            obtain ⟨a, rfl, ha'⟩ := (ih γ ρ free bound hf hb ..).mp ha
            obtain ⟨b, hv, hs⟩ := (compatible _ a ..).mp step
            exact ⟨b, hv, a, _, ha', hs⟩
      · rintro ⟨b, hv, a, s₁, ha, hs⟩
        exact .op ((ih γ ρ free bound hf hb ..).mpr ⟨a, rfl, ha⟩)
          ((compatible _ a ..).mpr ⟨b, hv, hs⟩)
  | let₁ arg body ihArg ihBody =>
      intro γ ρ free bound hf hb s value s'
      simp only [Derivation.denote, Stateful.mem_bind]
      constructor
      · intro run
        cases run with
        | let₁ ha hbody =>
            obtain ⟨a, rfl, ha'⟩ := (ihArg γ ρ free bound hf hb ..).mp ha
            obtain ⟨b, hv, hs⟩ := (ihBody γ (ρ.snoc a) free _ hf (hb.snoc F a) ..).mp hbody
            exact ⟨b, hv, a, _, ha', hs⟩
      · rintro ⟨b, hv, a, s₁, ha, hs⟩
        exact .let₁ ((ihArg γ ρ free bound hf hb ..).mpr ⟨a, rfl, ha⟩)
          ((ihBody γ (ρ.snoc a) free _ hf (hb.snoc F a) ..).mpr ⟨b, hv, hs⟩)
  | pair left right ihLeft ihRight =>
      intro γ ρ free bound hf hb s value s'
      simp only [Derivation.denote, Stateful.mem_bind, Stateful.mem_pure]
      constructor
      · intro run
        cases run with
        | pair hl hr =>
            obtain ⟨a, rfl, hl'⟩ := (ihLeft γ ρ free bound hf hb ..).mp hl
            obtain ⟨b, rfl, hr'⟩ := (ihRight γ ρ free bound hf hb ..).mp hr
            exact ⟨(a, b), rfl, a, _, hl', b, _, hr', rfl, rfl⟩
      · rintro ⟨ab, hv, a, s₁, ha, b, s₂, hb', hab, hs⟩
        subst ab
        subst s'
        subst value
        exact .pair ((ihLeft γ ρ free bound hf hb ..).mpr ⟨a, rfl, ha⟩)
          ((ihRight γ ρ free bound hf hb ..).mpr ⟨b, rfl, hb'⟩)
  | let₂ arg body ihArg ihBody =>
      intro γ ρ free bound hf hb s value s'
      simp only [Derivation.denote, Stateful.mem_bind]
      constructor
      · intro run
        cases run with
        | let₂ ha hbody =>
            obtain ⟨⟨a, b⟩, hab, ha'⟩ := (ihArg γ ρ free bound hf hb ..).mp ha
            obtain ⟨rfl, rfl⟩ := Value.pair.inj hab
            obtain ⟨c, hv, hs⟩ := (ihBody γ ((ρ.snoc a).snoc b) free _ hf
              ((hb.snoc F a).snoc F b) ..).mp hbody
            exact ⟨c, hv, (a, b), _, ha', hs⟩
      · rintro ⟨c, hv, ⟨a, b⟩, s₁, ha, hs⟩
        exact .let₂ ((ihArg γ ρ free bound hf hb ..).mpr ⟨(a, b), rfl, ha⟩)
          ((ihBody γ ((ρ.snoc a).snoc b) free _ hf
            ((hb.snoc F a).snoc F b) ..).mpr ⟨c, hv, hs⟩)
  | inl arg ih =>
      intro γ ρ free bound hf hb s value s'
      simp only [Derivation.denote, Stateful.mem_bind, Stateful.mem_pure]
      constructor
      · intro run
        cases run with
        | inl ha =>
            obtain ⟨a, rfl, ha'⟩ := (ih γ ρ free bound hf hb ..).mp ha
            exact ⟨.inl a, rfl, a, _, ha', rfl, rfl⟩
      · rintro ⟨x, hv, a, s₁, ha, hx, hs⟩
        subst x
        subst s'
        subst value
        exact .inl ((ih γ ρ free bound hf hb ..).mpr ⟨a, rfl, ha⟩)
  | inr arg ih =>
      intro γ ρ free bound hf hb s value s'
      simp only [Derivation.denote, Stateful.mem_bind, Stateful.mem_pure]
      constructor
      · intro run
        cases run with
        | inr ha =>
            obtain ⟨a, rfl, ha'⟩ := (ih γ ρ free bound hf hb ..).mp ha
            exact ⟨.inr a, rfl, a, _, ha', rfl, rfl⟩
      · rintro ⟨x, hv, a, s₁, ha, hx, hs⟩
        subst x
        subst s'
        subst value
        exact .inr ((ih γ ρ free bound hf hb ..).mpr ⟨a, rfl, ha⟩)
  | case scrutinee left right ihScrutinee ihLeft ihRight =>
      intro γ ρ free bound hf hb s value s'
      simp only [Derivation.denote, Stateful.mem_bind]
      constructor
      · intro run
        cases run with
        | case_inl he hl =>
            obtain ⟨x, hx, he'⟩ := (ihScrutinee γ ρ free bound hf hb ..).mp he
            cases x with
            | inl a =>
                cases Value.inl.inj hx
                obtain ⟨b, hv, hs⟩ := (ihLeft γ (ρ.snoc a) free _ hf (hb.snoc F a) ..).mp hl
                exact ⟨b, hv, .inl a, _, he', hs⟩
            | inr _ => cases hx
        | case_inr he hr =>
            obtain ⟨x, hx, he'⟩ := (ihScrutinee γ ρ free bound hf hb ..).mp he
            cases x with
            | inl _ => cases hx
            | inr a =>
                cases Value.inr.inj hx
                obtain ⟨b, hv, hs⟩ := (ihRight γ (ρ.snoc a) free _ hf (hb.snoc F a) ..).mp hr
                exact ⟨b, hv, .inr a, _, he', hs⟩
      · rintro ⟨b, hv, x, s₁, he, hbranch⟩
        cases x with
        | inl a =>
            exact .case_inl ((ihScrutinee γ ρ free bound hf hb ..).mpr ⟨.inl a, rfl, he⟩)
              ((ihLeft γ (ρ.snoc a) free _ hf (hb.snoc F a) ..).mpr ⟨b, hv, hbranch⟩)
        | inr a =>
            exact .case_inr ((ihScrutinee γ ρ free bound hf hb ..).mpr ⟨.inr a, rfl, he⟩)
              ((ihRight γ (ρ.snoc a) free _ hf (hb.snoc F a) ..).mpr ⟨b, hv, hbranch⟩)
  | abort arg ih =>
      intro γ ρ free bound hf hb s value s'
      simp only [Derivation.denote, Stateful.mem_bind]
      constructor
      · intro run; cases run
      · rintro ⟨_, _, z, _, _, _⟩
        exact z.elim
  | iter init body ihInit ihBody =>
      intro γ ρ free bound hf hb s value s'
      change Eval instr free bound _ s value s' ↔
        ∃ b, value = encodeValue F _ b ∧
          (b, s') ∈ ((init.denote (Ty.denote F) M γ ρ >>= Elgot.iter
            (fun a => body.denote (Ty.denote F) M γ (ρ.snoc a) >>= pure)) s).run
      have bodyPure : (fun a => body.denote (Ty.denote F) M γ (ρ.snoc a) >>= pure) =
          (fun a => body.denote (Ty.denote F) M γ (ρ.snoc a)) := by
        funext a
        exact bind_pure _
      set_option backward.isDefEq.respectTransparency false in
        rw [bodyPure]
      simp only [Stateful.mem_bind]
      have loopAgree := loop_iff_iterates F bound _ free instr
        (fun a => body.denote (Ty.denote F) M γ (ρ.snoc a))
        (fun a => ihBody γ (ρ.snoc a) free _ hf (hb.snoc F a))
      constructor
      · intro run
        cases run with
        | iter hi hl =>
            obtain ⟨a, rfl, hi'⟩ := (ihInit γ ρ free bound hf hb ..).mp hi
            obtain ⟨b, hv, hl'⟩ := (loopAgree a ..).mp hl
            exact ⟨b, hv, a, _, hi', (Stateful.mem_iter ..).mpr hl'⟩
      · rintro ⟨b, hv, a, s₁, hi, hl⟩
        exact .iter ((ihInit γ ρ free bound hf hb ..).mpr ⟨a, rfl, hi⟩)
          ((loopAgree a ..).mpr ⟨b, hv, (Stateful.mem_iter ..).mp hl⟩)

/-- Membership of a particular typed result is equivalent to its encoded evaluation. -/
theorem eval_encode_iff_denote {Γ : Ctx ν (Ty κ)} {n : Nat} {β : BoundCtx (Ty κ) n}
    {t : Tm ν Φ n} {A : Ty κ} (d : Derivation Φ Γ β t A)
    (γ : Isotope.Semantics.FreeEnv (Ty.denote F) Γ)
    (ρ : Isotope.Semantics.BoundEnv (Ty.denote F) β)
    (free : FreeEnv ν (Sigma F)) (bound : BoundEnv (Sigma F) n)
    (hf : FreeEncodes F γ free) (hb : BoundEncodes F ρ bound)
    (s s' : σ) (a : Ty.denote F A) :
    Eval instr free bound t s (encodeValue F A a) s' ↔
      (a, s') ∈ (d.denote (Ty.denote F) M γ ρ s).run := by
  rw [eval_iff_denote F M instr compatible d γ ρ free bound hf hb]
  constructor
  · rintro ⟨b, hab, run⟩
    cases encodeValue_injective F A hab
    exact run
  · intro run
    exact ⟨a, rfl, run⟩

omit compatible in
/-- Every typed primitive model has a canonical compatible operational interpretation. -/
theorem eval_operational_iff_denote {Γ : Ctx ν (Ty κ)} {n : Nat} {β : BoundCtx (Ty κ) n}
    {t : Tm ν Φ n} {A : Ty κ} (d : Derivation Φ Γ β t A)
    (γ : Isotope.Semantics.FreeEnv (Ty.denote F) Γ)
    (ρ : Isotope.Semantics.BoundEnv (Ty.denote F) β)
    (free : FreeEnv ν (Sigma F)) (bound : BoundEnv (Sigma F) n)
    (hf : FreeEncodes F γ free) (hb : BoundEncodes F ρ bound)
    (s s' : σ) (a : Ty.denote F A) :
    Eval (M.operational F) free bound t s (encodeValue F A a) s' ↔
      (a, s') ∈ (d.denote (Ty.denote F) M γ ρ s).run :=
  eval_encode_iff_denote F M (M.operational F) (M.operational_compatible F)
    d γ ρ free bound hf hb s s' a

end Silmaril.Isotope.LetIter.Semantics
