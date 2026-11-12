module

public import Silmaril.Logic.Inst.Builders.Defs
public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.SSA.Fragment.Defs

/-!
# Function-body equivalence institutions over a body language (track `ir`)

A *body language* `L : Lang` gives, for each hole type `h` (parameters and result of a
function), the candidate bodies `L.Body h`, a runtime environment type `L.Env`, and the
denotation `L.den e h b : Beh` of a body: its terminating outcomes per argument list. All
languages of this track (the structured fragment, its native-checked part, lambda-SSA and
Binaryen's folded IR) share the behaviour type `Beh` and its refinement `Beh.Le`, so
translations between them can be compared on the nose.

A *signature frame* `F : Frame Sig` supplies the signatures: a category `Sig`, the hole type
`F.hole S` of the focus (preserved by morphisms: embedding a function into a bigger module does
not change its type) and the contexts `F.Ctx S` (information about the rest of the module),
which reduce contravariantly. The frame is the plug for the `core` track's signature category:
any category with a focus type and a context functor gives one.

`Lang.inst F L` is the institution with

* signatures `S : Sig`;
* models `F.Ctx S × L.Env`: a context and a runtime environment;
* sentences `Formula (L.Body (F.hole S))`: `b ⊑ b'`, `b ≐ b'` and conjunctions over candidate
  bodies of the focus;
* satisfaction: `⊑` is `Beh.Le` of the denotations (`≐` is `⊑` both ways).

The bodies of the languages of this track do not call other functions, so their denotation does
not read the context; the satisfaction condition then only needs the transport of bodies along
the hole equality of a morphism. A language whose bodies call functions needs denotations that
read the context; that is the `core`/`models` tracks' institution.

A *translation* `T : Lang.Tr L₁ L₂` maps bodies forwards, environments backwards, and is exact:
`L₂.den e h (T.body h b) = L₁.den (T.env e) h b`. It gives a comorphism
`T.comorphism F : Comorphism (L₁.inst F) (L₂.inst F)` with the identity signature functor;
it is model-expansive when `T.env` is surjective (`Lang.Tr.modelExpansive`, in `Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.IR

open CategoryTheory
open Silmaril.Inst
open Silmaril.Wasm.Institution (Formula)
open Silmaril.Wasm.SSA (WVal FOut)
open Silmaril.Wasm (IntType)

/-- The type of a hole: the parameter and result types of a fragment function. -/
structure Hole where
  params : List IntType
  result : Option IntType
  deriving DecidableEq

/-- Observable behaviour of a body: its terminating outcomes on each argument list. -/
abbrev Beh : Type := List WVal → FOut → Prop

/-- Refinement of behaviours: every outcome of the first is an outcome of the second. -/
def Beh.Le (B B' : Beh) : Prop := ∀ args o, B args o → B' args o

/-- Equivalence of behaviours: the same outcomes. -/
def Beh.Equiv (B B' : Beh) : Prop := ∀ args o, B args o ↔ B' args o

/-- A signature frame: signatures with a focus hole type preserved by morphisms, and
contexts that reduce along morphisms. -/
structure Frame (Sig : Type) [Category.{0} Sig] where
  /-- The hole type of the focus. -/
  hole : Sig → Hole
  /-- Morphisms keep the focus type. -/
  hole_hom : ∀ {S S' : Sig}, (S ⟶ S') → hole S = hole S'
  /-- Contexts: what a model knows about the rest of the module. -/
  Ctx : Sig → Type
  /-- The reduct of a context. -/
  red : ∀ {S S' : Sig}, (S ⟶ S') → Ctx S' → Ctx S
  red_id : ∀ (S : Sig) (c : Ctx S), red (𝟙 S) c = c
  red_comp : ∀ {S S' S'' : Sig} (σ : S ⟶ S') (τ : S' ⟶ S'') (c : Ctx S''),
    red (σ ≫ τ) c = red σ (red τ c)

/-- A body language: candidate bodies per hole type, a runtime environment, a denotation. -/
structure Lang where
  /-- Candidate bodies of a hole. -/
  Body : Hole → Type
  /-- The runtime environment a body runs in (store and module instance for Binaryen). -/
  Env : Type
  /-- The denotation of a body. -/
  den : Env → (h : Hole) → Body h → Beh

namespace Lang

variable (L : Lang)

/-- Transport of a body along an equality of hole types. -/
def cast {h h' : Hole} (e : h = h') (b : L.Body h) : L.Body h' := _root_.cast (congrArg L.Body e) b

@[simp] theorem cast_rfl {h : Hole} (b : L.Body h) : L.cast rfl b = b := rfl

theorem cast_cast {h h' h'' : Hole} (e : h = h') (e' : h' = h'') (b : L.Body h) :
    L.cast e' (L.cast e b) = L.cast (e.trans e') b := by
  subst e; subst e'; rfl

theorem den_cast (env : L.Env) {h h' : Hole} (e : h = h') (b : L.Body h) :
    L.den env h' (L.cast e b) = L.den env h b := by
  subst e; rfl

/-- Refinement of two bodies under an environment. -/
def Le (env : L.Env) (h : Hole) (b b' : L.Body h) : Prop := Beh.Le (L.den env h b) (L.den env h b')

/-- The plain presentation of the institution of `L` over the frame `F`. -/
def plain {Sig : Type} [Category.{0} Sig] (F : Frame Sig) : Plain.{0, 0, 0, 0} Sig where
  Sen S := Formula (L.Body (F.hole S))
  map σ φ := φ.map (L.cast (F.hole_hom σ))
  map_id S φ := by
    rw [Formula.map_congr (g := id) (fun b => L.cast_rfl b), Formula.map_id]
  map_comp σ τ φ := by
    rw [Formula.map_map]
    exact Formula.map_congr (fun b => (L.cast_cast _ _ b).symm) φ
  Mod S := F.Ctx S × L.Env
  reduct σ M := (F.red σ M.1, M.2)
  reduct_id S M := by rw [F.red_id]
  reduct_comp σ τ M := by rw [F.red_comp]
  Sat M φ := φ.Holds (L.Le M.2 _)
  sat_map σ M φ := by
    rw [Formula.holds_map]
    exact Formula.holds_congr (fun b b' => by simp only [Le, den_cast]) φ

/-- **The function-body institution** of the language `L` over the frame `F`. -/
abbrev inst {Sig : Type} [Category.{0} Sig] (F : Frame Sig) : Institution₀ := (L.plain F).toInst

/-- A translation between body languages: bodies forwards, environments backwards, exact on
denotations. -/
structure Tr (L₁ L₂ : Lang) where
  /-- The body translation (same hole type). -/
  body : ∀ h, L₁.Body h → L₂.Body h
  /-- The environment map. -/
  env : L₂.Env → L₁.Env
  /-- Exactness: a translated body means what the source body means. -/
  den_body : ∀ e h b, L₂.den e h (body h b) = L₁.den (env e) h b

namespace Tr

variable {L₁ L₂ L₃ : Lang}

/-- The identity translation. -/
def id (L : Lang) : Tr L L := ⟨fun _ b => b, fun e => e, fun _ _ _ => rfl⟩

/-- Composition of translations. -/
def comp (T : Tr L₁ L₂) (U : Tr L₂ L₃) : Tr L₁ L₃ where
  body h b := U.body h (T.body h b)
  env e := T.env (U.env e)
  den_body e h b := by rw [U.den_body, T.den_body]

theorem body_cast (T : Tr L₁ L₂) {h h' : Hole} (e : h = h') (b : L₁.Body h) :
    T.body h' (L₁.cast e b) = L₂.cast e (T.body h b) := by
  subst e; rfl

/-- **The comorphism of a translation**, with the identity signature functor. -/
def comorphism (T : Tr L₁ L₂) {Sig : Type} [Category.{0} Sig] (F : Frame Sig) :
    Comorphism (L₁.inst F) (L₂.inst F) :=
  Comorphism.ofPlain (P := L₁.plain F) (Q := L₂.plain F) (𝟭 Sig)
    (fun _ φ => φ.map (T.body _)) (fun _ M => (M.1, T.env M.2))
    (fun S (M : F.Ctx S × L₂.Env) (φ : Formula (L₁.Body (F.hole S))) =>
      (Formula.holds_map _ _ φ).trans
        (Formula.holds_congr (fun b b' => by simp only [Le, T.den_body]; exact Iff.rfl) φ))
    (fun σ (φ : Formula (L₁.Body (F.hole _))) =>
      (Formula.map_map _ _ φ).trans ((Formula.map_congr (fun b => T.body_cast _ b) φ).trans
        (Formula.map_map _ _ φ).symm))
    (fun _ _ => rfl)

end Tr

end Lang

end Silmaril.Wasm.FnInst.IR
