module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Set.Image

/-!
# Function-level contexts, partial modules and their semantic models

The base of the *models* track of the function-level institutions (`docs/projects/logic-inst.md`).
Everything is generic in a body language:

* `FnSyntax`: function types and bodies `Body n` over `n` callable functions, with renaming of
  call indices (`rename`, strictly functorial);
* `FnSem L`: a semantics of the bodies: a semantic domain `Den` (behaviours of one function:
  e.g. inputs and state to sets of outcomes) and `eval env b`, the denotation of `b` when the
  callable functions denote `env`; `eval_rename` says calls are the only way a body sees its
  context.

Contexts and signatures:

* `Ctx L`: a module context (the types of all functions, public and private);
  `Ctx.Hom`: an embedding (an injective, type-preserving renumbering of functions);
* `Sig L`: a context with a **focus** (one function index), `Sig.Hom`: an embedding that maps
  the focus to the focus.

Sentences (`Sen L n`): equations `b ≐ b'` between candidate bodies for the focus, and
conjunction. `Sen.Holds S env φ` reads them in an environment.

Models:

* **(c) semantic models**: sets of environments `Fin n → S.Den` (each function, including
  imports and functions without a known body, denotes some behaviour); fewer environments is
  more information;
* **(a) partial bodies**: `PMod T` is a module *containing* the context of `T`: a bigger context
  `ctx`, an embedding `emb` of `T` into it and partial bodies for its functions (`none`:
  unknown body, e.g. an import). Its denotation `den` is the set of restrictions of the
  environments that solve the body equations of every function except the focus (`Sol`);
* `PMod.Le`: the information order (embed into a bigger module that keeps every known body);
  `PMod.bot T`: the least informative model (the context itself, no body known).

The institutions are in `Silmaril.Wasm.FnInst.Models.Inst`; theorems in `Base.Thms`.

New definitions; local interfaces (the core models define their own signatures).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models

/-- A body language: function types, and bodies over `n` callable functions with renaming of
call indices. -/
structure FnSyntax where
  /-- Function types (params → results). -/
  Ty : Type
  /-- Bodies that may call functions `Fin n`. -/
  Body : ℕ → Type
  /-- Renumbering of call indices. -/
  rename : ∀ {n m : ℕ}, (Fin n → Fin m) → Body n → Body m
  rename_id : ∀ {n : ℕ} (b : Body n), rename id b = b
  rename_comp : ∀ {n m k : ℕ} (f : Fin n → Fin m) (g : Fin m → Fin k) (b : Body n),
    rename (g ∘ f) b = rename g (rename f b)

/-- A semantics of a body language: a domain of function behaviours, and the behaviour of a
body given the behaviours of the functions it may call. -/
structure FnSem (L : FnSyntax) where
  /-- Behaviours of one function. -/
  Den : Type
  /-- The behaviour of a body when the callable functions behave as `env`. -/
  eval : ∀ {n : ℕ}, (Fin n → Den) → L.Body n → Den
  /-- A body sees its context only through calls. -/
  eval_rename : ∀ {n m : ℕ} (f : Fin n → Fin m) (env : Fin m → Den) (b : L.Body n),
    eval env (L.rename f b) = eval (env ∘ f) b

variable {L : FnSyntax}

/-- A module context: the types of all functions (imports, public and private). -/
structure Ctx (L : FnSyntax) where
  /-- Number of functions. -/
  n : ℕ
  /-- Their types. -/
  ty : Fin n → L.Ty

/-- An embedding of contexts: an injective renumbering that keeps types. -/
structure Ctx.Hom (Γ Δ : Ctx L) where
  /-- The renumbering. -/
  f : Fin Γ.n → Fin Δ.n
  inj : Function.Injective f
  ty : ∀ i, Δ.ty (f i) = Γ.ty i

/-- The identity embedding. -/
def Ctx.Hom.id (Γ : Ctx L) : Ctx.Hom Γ Γ := ⟨fun i => i, fun _ _ h => h, fun _ => rfl⟩

/-- Composition of embeddings (diagrammatic order). -/
def Ctx.Hom.comp {Γ Δ Θ : Ctx L} (σ : Ctx.Hom Γ Δ) (τ : Ctx.Hom Δ Θ) : Ctx.Hom Γ Θ :=
  ⟨fun i => τ.f (σ.f i), fun _ _ h => σ.inj (τ.inj h), fun i => (τ.ty _).trans (σ.ty i)⟩

open CategoryTheory in
instance : Category (Ctx L) where
  Hom := Ctx.Hom
  id := Ctx.Hom.id
  comp := Ctx.Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A signature: a module context and a focus function. -/
structure Sig (L : FnSyntax) extends Ctx L where
  /-- The function whose body the sentences are about. -/
  focus : Fin n

/-- A signature morphism: an embedding of contexts that maps the focus to the focus. -/
structure Sig.Hom (A B : Sig L) where
  /-- The embedding of contexts. -/
  c : Ctx.Hom A.toCtx B.toCtx
  focus : c.f A.focus = B.focus

/-- The identity signature morphism. -/
def Sig.Hom.id (A : Sig L) : Sig.Hom A A := ⟨Ctx.Hom.id A.toCtx, rfl⟩

/-- Composition of signature morphisms (diagrammatic order). -/
def Sig.Hom.comp {A B C : Sig L} (σ : Sig.Hom A B) (τ : Sig.Hom B C) : Sig.Hom A C :=
  ⟨σ.c.comp τ.c, by
    show τ.c.f (σ.c.f _) = _
    rw [σ.focus, τ.focus]⟩

open CategoryTheory in
instance : Category (Sig L) where
  Hom := Sig.Hom
  id := Sig.Hom.id
  comp := Sig.Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ### Sentences -/

/-- Sentences over `n` functions: equations between candidate bodies, and conjunction. -/
inductive Sen (L : FnSyntax) (n : ℕ) : Type where
  /-- `b ≐ b'`: the two candidate bodies behave the same. -/
  | eq (b b' : L.Body n)
  /-- Conjunction. -/
  | and (φ ψ : Sen L n)

namespace Sen

/-- Renumbering the calls of a sentence. -/
def map {n m : ℕ} (f : Fin n → Fin m) : Sen L n → Sen L m
  | eq b b' => eq (L.rename f b) (L.rename f b')
  | and φ ψ => and (map f φ) (map f ψ)

/-- A sentence holds in an environment. -/
def Holds (S : FnSem L) {n : ℕ} (env : Fin n → S.Den) : Sen L n → Prop
  | eq b b' => S.eval env b = S.eval env b'
  | and φ ψ => Holds S env φ ∧ Holds S env ψ

end Sen

/-! ### Semantic models (c) -/

/-- Environments over `n` functions. -/
abbrev Env (S : FnSem L) (n : ℕ) : Type := Fin n → S.Den

/-- A semantic model `E` satisfies `φ` when `φ` holds in every environment of `E`. -/
def SemSat (S : FnSem L) {n : ℕ} (E : Set (Env S n)) (φ : Sen L n) : Prop :=
  ∀ env ∈ E, Sen.Holds S env φ

/-- The reduct of a semantic model along a renumbering: restrict every environment. -/
def semReduct (S : FnSem L) {n m : ℕ} (f : Fin n → Fin m) (E : Set (Env S m)) :
    Set (Env S n) :=
  (fun env => env ∘ f) '' E

/-! ### Partial bodies (a) -/

/-- Partial bodies over a context: `none` is an unknown body (an import, or a function nothing
is assumed about). -/
abbrev PBodies (Γ : Ctx L) : Type := Fin Γ.n → Option (L.Body Γ.n)

/-- The **solutions** of partial bodies outside `X`: environments in which every function
outside `X` with a known body behaves as its body. Functions without a body are
unconstrained. -/
def Sol (S : FnSem L) {n : ℕ} (B : Fin n → Option (L.Body n)) (X : Set (Fin n)) :
    Set (Env S n) :=
  {env | ∀ j, j ∉ X → ∀ b, B j = some b → env j = S.eval env b}

/-- A model with partial bodies over `T`: a module context containing `T`'s, and partial bodies
of its functions. The body of the focus, if any, is ignored by satisfaction (sentences are
about candidates for it). -/
structure PMod (T : Sig L) where
  /-- The whole module's context. -/
  ctx : Ctx L
  /-- Where `T`'s functions sit in it. -/
  emb : Ctx.Hom T.toCtx ctx
  /-- The known bodies. -/
  bodies : PBodies ctx

namespace PMod

variable {T U : Sig L}

/-- The denotation into semantic models: restrictions of the solutions. -/
def den (S : FnSem L) (M : PMod T) : Set (Env S T.n) :=
  semReduct S M.emb.f (Sol S M.bodies {M.emb.f T.focus})

/-- The reduct along a signature morphism: the same module, seen from the smaller
signature. -/
def reduct (σ : Sig.Hom T U) (M : PMod U) : PMod T := ⟨M.ctx, σ.c.comp M.emb, M.bodies⟩

/-- The **information order**: `M'` embeds `M`'s module (over `T`) and keeps every known
body. -/
def Le (M M' : PMod T) : Prop :=
  ∃ κ : Ctx.Hom M.ctx M'.ctx, (∀ i, κ.f (M.emb.f i) = M'.emb.f i) ∧
    ∀ j b, M.bodies j = some b → M'.bodies (κ.f j) = some (L.rename κ.f b)

/-- The least informative model: the context of `T` itself, with no body known. -/
def bot (T : Sig L) : PMod T := ⟨T.toCtx, Ctx.Hom.id _, fun _ => none⟩

/-- The model of a module context `T` with partial bodies `B` (the focus body is ignored). -/
def ofBodies (B : PBodies T.toCtx) : PMod T := ⟨T.toCtx, Ctx.Hom.id _, B⟩

end PMod

/-! ### Bodies plus a choice of semantics (b) -/

/-- A model with partial bodies and a choice `k` among a family of semantics `sems`. -/
structure KMod {K : Type} (_sems : K → FnSem L) (T : Sig L) where
  /-- The chosen semantics. -/
  k : K
  /-- The partial bodies. -/
  m : PMod T

end Silmaril.Wasm.FnInst.Models
