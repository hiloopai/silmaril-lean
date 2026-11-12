module

public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.Embedding

@[expose] public section
noncomputable section
set_option autoImplicit true

namespace Silmaril.Isotope.LetSeq.ProofRelevant.LocallyNameless

open Silmaril.Isotope.LetSeq.LocallyNameless (Tm)

universe u v w r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] {pureEff : ε} {Γ : Ctx ν τ}

namespace Embedding

def embedded {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, A⟩ :=
  ⟨Morphism.SeqCase.embed t, h.embed⟩

def equation {i : Isotope.Theory.TypingIndex τ}
    (a b : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ i) : Type (max u v w r) :=
  LetCase.ProofRelevant.LocallyNameless.TypedEquiv.Deriv pureEff Γ a.2 b.2

def tlet {n : Nat} {β : BoundCtx τ n} {A B : τ}
    (a : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, A⟩)
    (b : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n+1, β.snoc A, B⟩) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, B⟩ := ⟨.let₁ a.1 b.1, .let₁ a.2 b.2⟩

def tpair {n : Nat} {β : BoundCtx τ n} {A B : τ}
    (a : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, A⟩)
    (b : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, B⟩) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, product A B⟩ := ⟨.pair a.1 b.1, .pair a.2 b.2⟩

def tlet₂ {n : Nat} {β : BoundCtx τ n} {A B C : τ}
    (a : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, product A B⟩)
    (b : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n+2, (β.snoc A).snoc B, C⟩) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, C⟩ := ⟨.let₂ a.1 b.1, .let₂ a.2 b.2⟩

def top {n : Nat} {β : BoundCtx τ n} {f : Φ}
    (a : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, instrSrc f⟩) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, instrTrg f⟩ := ⟨.op f a.1, .op a.2⟩

def tlift {n : Nat} {β : BoundCtx τ n} {A B : τ}
    (a : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, A⟩) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n+1, β.snoc B, A⟩ := ⟨a.1.lift, a.2.lift⟩

def tunder {n : Nat} {β : BoundCtx τ n} {A X Y : τ}
    (a : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n+1, β.snoc Y, A⟩) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n+2, (β.snoc X).snoc Y, A⟩ := ⟨a.1.underBinder, a.2.underBinder⟩

def tunder₂ {n : Nat} {β : BoundCtx τ n} {A X Y Z : τ}
    (a : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n+2, (β.snoc Y).snoc Z, A⟩) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n+3, ((β.snoc X).snoc Y).snoc Z, A⟩ :=
  ⟨a.1.underTwoBinders, a.2.underTwoBinders⟩

def tinst {n : Nat} {β : BoundCtx τ n} {A B : τ}
    (b : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n+1, β.snoc A, B⟩)
    (a : LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, A⟩) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ ⟨n, β, B⟩ := ⟨b.1.instantiate a.1, b.2.instantiate a.2⟩

variable {n : Nat} {β : BoundCtx τ n}

theorem embedded_let (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (β.snoc A) b B) :
    embedded (.let₁ ha hb) = tlet (embedded ha) (embedded hb) := rfl
theorem embedded_pair (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
    embedded (.pair ha hb) = tpair (embedded ha) (embedded hb) := rfl
theorem embedded_let₂ (ha : HasType Φ Γ β a (product A B))
    (hb : HasType Φ Γ ((β.snoc A).snoc B) b C) :
    embedded (.let₂ ha hb) = tlet₂ (embedded ha) (embedded hb) := rfl
theorem embedded_op (ha : HasType Φ Γ β a (instrSrc f)) :
    embedded (.op ha) = top (f := f) (embedded ha) := rfl
theorem embedded_lift (ha : HasType Φ Γ β a A) :
    embedded (ha.lift (B := B)) = tlift (embedded ha) :=
  Sigma.ext (Morphism.SeqCase.embed_lift _) ha.embed_lift
theorem embedded_under (ha : HasType Φ Γ (β.snoc Y) a A) :
    embedded (ha.underBinder (X := X)) = tunder (embedded ha) :=
  Sigma.ext (Morphism.SeqCase.embed_underBinder _) (ha.embed_rename _)
theorem embedded_under₂ (ha : HasType Φ Γ ((β.snoc Y).snoc Z) a A) :
    embedded (ha.underTwoBinders (X := X)) = tunder₂ (embedded ha) :=
  Sigma.ext (Morphism.SeqCase.embed_underTwoBinders _) (ha.embed_rename _)
theorem embedded_instantiate (hb : HasType Φ Γ (β.snoc A) b B)
    (ha : HasType Φ Γ β a A) : embedded (hb.instantiate ha) = tinst (embedded hb) (embedded ha) :=
  Sigma.ext (Morphism.SeqCase.embed_instantiate _ _) (hb.embed_instantiate ha)

end Embedding

open Embedding

/-- Native equational derivations include into the next fragment with both
endpoint typing witnesses retained. -/
def TypedEquiv.Deriv.embed {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : TypedEquiv.Deriv pureEff Γ ha hb) :
    LetCase.ProofRelevant.LocallyNameless.TypedEquiv.Deriv pureEff Γ ha.embed hb.embed := by
  change equation (embedded ha) (embedded hb)
  induction d with
  | refl h => exact .refl h.embed
  | symm _ ih => exact .symm ih
  | trans _ _ ih ik => exact .trans ih ik
  | sub _ d ih => exact .sub ih d
  | op _ ih => exact .op ih
  | let₁ _ _ ih ik => exact .let₁ ih ik
  | pair _ _ ih ik => exact .pair ih ik
  | let₂ _ _ ih ik => exact .let₂ ih ik
  | letBeta hp ha hb =>
    rw [embedded_let, embedded_instantiate]
    exact .letBeta (Morphism.SeqCase.embed_pure hp) ha.embed hb.embed
  | letEta ha => exact .letEta ha.embed
  | unitEta ha => exact .unitEta ha.embed
  | pairBeta ha hb hc =>
    simp only [embedded_let₂, embedded_pair, embedded_let, embedded_lift]
    exact .pairBeta ha.embed hb.embed hc.embed
  | pairEta ha => exact .pairEta ha.embed
  | bindOp ha hc =>
    simp only [embedded_let, embedded_op, embedded_under]
    exact .bindOp ha.embed hc.embed
  | bindLet ha hb hc =>
    simp only [embedded_let, embedded_under]
    exact .bindLet ha.embed hb.embed hc.embed
  | bindLetPair he hc hd =>
    simp only [embedded_let, embedded_let₂, embedded_under]
    exact .bindLetPair he.embed hc.embed hd.embed
  | bindPair ha hc =>
    simp only [embedded_let₂, embedded_let, embedded_under₂]
    exact .bindPair ha.embed hc.embed

end Silmaril.Isotope.LetSeq.ProofRelevant.LocallyNameless
