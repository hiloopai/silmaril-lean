module

public import Silmaril.Wasm.FnInst.Comor.Defs

/-!
# Partial-body models and the information order

Model (a) of the design: what is known about the *other* functions' bodies. A partial model
`M : PModel L W C` over a context `C` lives in some module context `M.C'` that `C` embeds into
(`M.emb`), and says for each function of `M.C'` whether its body is

* `free`: unknown, so calls to it may behave arbitrarily;
* `base`: given by the base handler `M.base` (an import with known behaviour, say);
* `code b`: the body `b` (over `M.C'`), so calls to it run `b`.

Non-call events (globals, memories) are answered by `M.base`. Its **denotation** `M.den` is the
set of handlers over `C` it allows (model (c)): reducts along `M.emb` of handlers that agree
with `M.base` off free and specified functions and satisfy the body equations
(`Completes`). Recursion makes the body equations a fixpoint condition; `den` may be empty,
and then every sentence holds vacuously (stated, not hidden: see `docs/projects/logic-inst.md`).

The reduct of a partial model only changes the embedding, so `den` commutes with reducts
(`PModel.den_reduct`), and every handler presentation `P : HPres` lifts to an institution of
partial models (`HPres.partialInst`) whose satisfaction is *truth in every completion*.

**Information order**: `M.InfoLe N` when every completion of `N` is a completion of `M`.
Specifying more bodies goes up (`PModel.infoLe_withBody`). `free h₀` (all bodies unknown) is
least informative among models with base `h₀` and context `C`; `exact h₀` (every call answered
by `h₀`) has `den = {h₀}`.

Distinction sentences, at the level of partial models: `DistSome M φ` (some completion
refutes `φ`) and `DistAll M φ` (every completion refutes `φ`).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst

open CategoryTheory Silmaril.Inst

/-- What a partial model knows about one function body. -/
inductive BodySpec (L : Lang) (C : Ctx) where
  | free
  | base
  | code (b : L.Code C)

/-- Information order on body specifications: `free` below everything. -/
def BodySpec.Le {L : Lang} {C : Ctx} (s t : BodySpec L C) : Prop := s = .free ∨ s = t

/-- A partial-body model over `C`. -/
structure PModel (L : Lang) (W : Type) (C : Ctx) where
  /-- The module the context lives in. -/
  C' : Ctx
  /-- The embedding of the context. -/
  emb : C ⟶ C'
  /-- Answers to non-call events and to calls of `base` functions. -/
  base : Handler L W C'
  /-- What is known of each body. -/
  body : C'.Idx .func → BodySpec L C'

namespace PModel

variable {L : Lang} {W : Type} {C : Ctx}

/-- `h` completes `M`: it agrees with the base where `M` says so, and calls to a specified
function run its body. -/
def Completes (M : PModel L W C) (h : Handler L W M.C') : Prop :=
  (∀ e, (∀ f a, e = L.callEv f a → M.body f = .base) → h e = M.base e) ∧
  ∀ f b, M.body f = .code b → ∀ a w, h (L.callEv f a) w = L.ret (L.exec h b (L.entry a) w)

/-- The completions of `M`, as handlers over `C`. -/
def den (M : PModel L W C) : Set (Handler L W C) :=
  {h | ∃ h', M.Completes h' ∧ Handler.reduct M.emb h' = h}

/-- The reduct along an embedding: only the embedding changes. -/
def reduct {C₀ : Ctx} (σ : C₀ ⟶ C) (M : PModel L W C) : PModel L W C₀ :=
  ⟨M.C', σ ≫ M.emb, M.base, M.body⟩

theorem reduct_id (M : PModel L W C) : M.reduct (𝟙 C) = M := by
  cases M
  simp only [reduct, Category.id_comp]

theorem reduct_comp {C₀ C₁ : Ctx} (σ : C₀ ⟶ C₁) (τ : C₁ ⟶ C) (M : PModel L W C) :
    M.reduct (σ ≫ τ) = (M.reduct τ).reduct σ := by
  cases M
  simp only [reduct, Category.assoc]

theorem den_reduct {C₀ : Ctx} (σ : C₀ ⟶ C) (M : PModel L W C) :
    (M.reduct σ).den = Handler.reduct σ '' M.den := by
  ext h
  constructor
  · rintro ⟨h', hc, rfl⟩
    exact ⟨_, ⟨h', hc, rfl⟩, (Handler.reduct_comp σ M.emb h').symm⟩
  · rintro ⟨_, ⟨h', hc, rfl⟩, rfl⟩
    exact ⟨h', hc, Handler.reduct_comp σ M.emb h'⟩

/-- `N` is at least as informative as `M`. -/
def InfoLe (M N : PModel L W C) : Prop := N.den ⊆ M.den

/-- The same model with other body specifications. -/
def withBody (M : PModel L W C) (body : M.C'.Idx .func → BodySpec L M.C') : PModel L W C :=
  ⟨M.C', M.emb, M.base, body⟩

/-- Nothing known about any body: the least informative model with base `h₀`. -/
def free (h₀ : Handler L W C) : PModel L W C := ⟨C, 𝟙 C, h₀, fun _ => .free⟩

/-- Every call answered by `h₀`: the model whose only completion is `h₀`. -/
def exact (h₀ : Handler L W C) : PModel L W C := ⟨C, 𝟙 C, h₀, fun _ => .base⟩

end PModel

namespace HPres

variable {L : Lang} {W : Type} {Sign : Type} [Category.{0} Sign] (P : HPres L W Sign)

/-- The institution of partial models of a handler presentation: same signatures and
sentences, partial models, truth in every completion. -/
def partialPlain : Plain.{0, 0, 0, 0} Sign where
  Sen := P.Sen
  map := P.map
  map_id := P.map_id
  map_comp := P.map_comp
  Mod S := PModel L W (P.ctx.obj S)
  reduct σ M := M.reduct (P.ctx.map σ)
  reduct_id S M := by rw [Functor.map_id, PModel.reduct_id]
  reduct_comp σ τ M := by rw [Functor.map_comp, PModel.reduct_comp]
  Sat M φ := ∀ h ∈ M.den, P.Sat h φ
  sat_map σ M φ := by
    rw [PModel.den_reduct, Set.forall_mem_image]
    exact forall₂_congr fun h _ => P.sat_map σ h φ

/-- The partial-model institution. -/
abbrev partialInst : Institution₀ := P.partialPlain.toInst

/-- Some completion refutes `φ`: `φ` is distinguished *in some completion*. -/
def DistSome {S : Sign} (M : PModel L W (P.ctx.obj S)) (φ : P.Sen S) : Prop :=
  ∃ h ∈ M.den, ¬ P.Sat h φ

/-- Every completion refutes `φ`: `φ` is distinguished *in every completion*. -/
def DistAll {S : Sign} (M : PModel L W (P.ctx.obj S)) (φ : P.Sen S) : Prop :=
  ∀ h ∈ M.den, ¬ P.Sat h φ

end HPres

/-! ### Partial versions of the four institutions and their comorphisms -/

variable (L : Lang) (W : Type)

/-- Partial-model hole institution. -/
abbrev holePInst : Institution₀ := (holePres L W).partialInst
/-- Partial-model one-function institution. -/
abbrev onePInst : Institution₀ := (onePres L W).partialInst
/-- Partial-model several-function institution. -/
abbrev setPInst : Institution₀ := (setPres L W).partialInst
/-- Partial-model all-function institution. -/
abbrev allPInst : Institution₀ := (allPres L W).partialInst

/-- one → several, on partial models. -/
def oneToSetP : Comorphism (onePInst L W) (setPInst L W) :=
  Comorphism.ofPlain (P := (onePres L W).partialPlain) (Q := (setPres L W).partialPlain)
    OneSig.toSet
    (fun S φ => Formula.map (FnAtom.reindex fun _ => ⟨S.f, rfl⟩) φ)
    (fun _ M => M)
    (fun S _ φ => forall₂_congr fun h _ => (Formula.holds_map _ _ φ).trans
      (Formula.holds_congr (fun a =>
        FnAtom.holds_reindex _ (fun _ => S.f) Subtype.val (fun _ => rfl) h a) φ))
    (fun σ φ => Formula.map_map_eq (fun a =>
      FnAtom.reindex_rename _ _ _ _ _ (fun _ => Subtype.ext (OneSig.Hom.f σ).symm) a) φ)
    (fun _ _ => rfl)

/-- several → all, on partial models. -/
def setToAllP : Comorphism (setPInst L W) (allPInst L W) :=
  Comorphism.ofPlain (P := (setPres L W).partialPlain) (Q := (allPres L W).partialPlain)
    SetSig.toAll
    (fun _ φ => Formula.map (FnAtom.reindex Subtype.val) φ)
    (fun _ M => M)
    (fun _ _ φ => forall₂_congr fun h _ => (Formula.holds_map _ _ φ).trans
      (Formula.holds_congr (fun a =>
        FnAtom.holds_reindex Subtype.val Subtype.val id (fun _ => rfl) h a) φ))
    (fun σ φ => Formula.map_map_eq (fun a =>
      FnAtom.reindex_rename (SetSig.Hom.emb σ) (SetSig.Hom.focus σ)
        (Ctx.Hom.map (SetSig.Hom.emb σ) .func) Subtype.val Subtype.val (fun _ => rfl) a) φ)
    (fun _ _ => rfl)

/-- hole → all, on partial models. -/
def holeToAllP : Comorphism (holePInst L W) (allPInst L W) :=
  Comorphism.ofPlain (P := (holePres L W).partialPlain) (Q := (allPres L W).partialPlain)
    HoleSig.toAll
    (fun S φ => Formula.map (fun p : L.Code S.C × L.Code S.C => FnAtom.seg S.ty p.1 p.2) φ)
    (fun _ M => M)
    (fun S _ φ => forall₂_congr fun h _ =>
      Formula.holds_map (fun p : L.Code S.C × L.Code S.C => FnAtom.seg S.ty p.1 p.2)
        (FnAtom.Holds id h) φ)
    (fun σ φ => Formula.map_map_eq (fun p => by
      show FnAtom.seg _ _ _ = FnAtom.seg _ _ _
      rw [HoleSig.Hom.ty σ]
      rfl) φ)
    (fun _ _ => rfl)

end Silmaril.Wasm.FnInst
