module

public import Silmaril.Wasm.FnInst.Ctx.Defs
public import Silmaril.Logic.Inst.Builders.Core.Defs

/-!
# Function-level equivalence institutions for Wasm (core)

Institutions for reasoning about the code of Wasm functions *within* a module, built with the
facade `Silmaril.Inst` (`Plain`, `Comorphism.ofPlain`).

**Languages.** A `Lang` is a body language over module contexts (`Ctx`): code `Code C` that
renames along context embeddings, the *events* `Ev C` by which code acts on its module (calls,
global, memory and table accesses), and an execution `exec h c cfg w` of code `c` from a
segment configuration `cfg` (operand stack, locals, ...) in a world `w`, where every event is
answered by a **handler** `h : Ev C → W → Resp × W`. The one law is naturality: running renamed
code under `h` is running the original code under `h` precomposed with the event renaming
(`exec_rename`). `Silmaril.Wasm.FnInst.Frag` is a Wasm instruction fragment that is a `Lang`.

**Models** are handlers (model (c) of the design: an abstract semantic function per function
index and per memory, global and table operation, from inputs and world to responses). The
handler answers calls to *every* function of the context, including the focus, so a sentence is
about the code of one body with the behaviour of everything else left to the model; a function
with an unspecified body denotes an arbitrary handler entry. Partial bodies (model (a)) and the
information order are in `Silmaril.Wasm.FnInst.Partial`.

**Sentences** are conjunctions of atoms:

* `seg τ b b'`: the segments `b` and `b'` have the same outcome from every configuration that
  fits the segment type `τ` (`SegEq`);
* `fn i b b'`: as bodies of function `i`, `b` and `b'` give the same call results from every
  argument list that fits `i`'s type (`FnEq`).

**Four signature categories**, one per kind of focus, each an `HPres` (a presentation by
handlers) and so an `Institution₀` whose satisfaction condition is `exec_rename`:

| institution | signature | morphisms | atoms |
| --- | --- | --- | --- |
| `holeInst` | a context and a segment type `τ` (an abstract hole) | embeddings, `τ` kept | `seg τ` |
| `oneInst` | a context and one function index | embeddings mapping the index | `seg`, `fn` at the index |
| `setInst` | a context and a set of function indices | embeddings mapping the set into the set | `seg`, `fn` at members |
| `allInst` | a context | embeddings | `seg`, `fn` at every index |

and comorphisms `oneToSet`, `setToAll`, `holeToAll` (and `oneToAll`), identity on models,
hence model-expansive.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst

open CategoryTheory Silmaril.Inst

/-- The type of a code segment, the *abstract hole*: what it consumes and produces on the
operand stack, the locals it may use and its label context (result types of enclosing
labels, innermost first). -/
structure SegTy where
  params : List ValTy
  results : List ValTy
  locals : List ValTy
  labels : List (List ValTy)
  deriving DecidableEq, Repr

/-- A body language over module contexts, with a handler semantics natural in embeddings. -/
structure Lang where
  /-- Code over a context. -/
  Code : Ctx → Type
  /-- Renaming code along an embedding. -/
  rename : ∀ {C C' : Ctx}, (C ⟶ C') → Code C → Code C'
  rename_id : ∀ {C : Ctx} (c : Code C), rename (𝟙 C) c = c
  rename_comp : ∀ {C C' C'' : Ctx} (σ : C ⟶ C') (τ : C' ⟶ C'') (c : Code C),
    rename (σ ≫ τ) c = rename τ (rename σ c)
  /-- Events by which code acts on its module (calls, globals, memories, tables). -/
  Ev : Ctx → Type
  /-- Renaming events along an embedding. -/
  evMap : ∀ {C C' : Ctx}, (C ⟶ C') → Ev C → Ev C'
  evMap_id : ∀ {C : Ctx} (e : Ev C), evMap (𝟙 C) e = e
  evMap_comp : ∀ {C C' C'' : Ctx} (σ : C ⟶ C') (τ : C' ⟶ C'') (e : Ev C),
    evMap (σ ≫ τ) e = evMap τ (evMap σ e)
  /-- Answers to events. -/
  Resp : Type
  /-- Segment configurations (operand stack, locals). -/
  Cfg : Type
  /-- Argument lists of calls. -/
  Args : Type
  /-- Outcomes of a segment in a world `W`. -/
  Out : Type → Type
  /-- Execution of code under a handler. -/
  exec : ∀ {C : Ctx} {W : Type}, (Ev C → W → Resp × W) → Code C → Cfg → W → Out W
  /-- Naturality: renamed code under `h` runs as the code under `h ∘ evMap σ`. -/
  exec_rename : ∀ {C C' : Ctx} {W : Type} (σ : C ⟶ C') (h : Ev C' → W → Resp × W)
    (c : Code C), exec h (rename σ c) = exec (fun e => h (evMap σ e)) c
  /-- Configurations that fit a segment type. -/
  fits : SegTy → Cfg → Prop
  /-- Argument lists that fit a function type. -/
  argsFit : FnTy → Args → Prop
  /-- The configuration at function entry. -/
  entry : Args → Cfg
  /-- The call result of an outcome. -/
  ret : ∀ {W : Type}, Out W → Resp × W
  /-- The call event. -/
  callEv : ∀ {C : Ctx}, C.Idx .func → Args → Ev C
  evMap_callEv : ∀ {C C' : Ctx} (σ : C ⟶ C') (f : C.Idx .func) (a : Args),
    evMap σ (callEv f a) = callEv (Ctx.Hom.map σ .func f) a

variable (L : Lang) (W : Type)

/-- Handlers: models of the function-level institutions (model (c)). -/
abbrev Handler (C : Ctx) : Type := L.Ev C → W → L.Resp × W

variable {L W}

/-- The reduct of a handler along an embedding: precompose with the event renaming. -/
def Handler.reduct {C C' : Ctx} (σ : C ⟶ C') (h : Handler L W C') : Handler L W C :=
  fun e => h (L.evMap σ e)

theorem Handler.reduct_id {C : Ctx} (h : Handler L W C) : Handler.reduct (𝟙 C) h = h :=
  funext fun e => by simp only [Handler.reduct, L.evMap_id]

theorem Handler.reduct_comp {C C' C'' : Ctx} (σ : C ⟶ C') (τ : C' ⟶ C'')
    (h : Handler L W C'') : Handler.reduct (σ ≫ τ) h = Handler.reduct σ (Handler.reduct τ h) :=
  funext fun e => by simp only [Handler.reduct, L.evMap_comp]

/-- Segment equivalence at `τ`: the same outcome from every configuration fitting `τ`. -/
def SegEq {C : Ctx} (h : Handler L W C) (τ : SegTy) (b b' : L.Code C) : Prop :=
  ∀ c w, L.fits τ c → L.exec h b c w = L.exec h b' c w

/-- Body equivalence at a function type: the same call result for every fitting argument
list. -/
def FnEq {C : Ctx} (h : Handler L W C) (t : FnTy) (b b' : L.Code C) : Prop :=
  ∀ a w, L.argsFit t a → L.ret (L.exec h b (L.entry a) w) = L.ret (L.exec h b' (L.entry a) w)

theorem segEq_rename {C C' : Ctx} (σ : C ⟶ C') (h : Handler L W C') (τ : SegTy)
    (b b' : L.Code C) :
    SegEq h τ (L.rename σ b) (L.rename σ b') ↔ SegEq (Handler.reduct σ h) τ b b' := by
  simp only [SegEq, L.exec_rename]
  exact Iff.rfl

theorem fnEq_rename {C C' : Ctx} (σ : C ⟶ C') (h : Handler L W C') (t : FnTy)
    (b b' : L.Code C) :
    FnEq h t (L.rename σ b) (L.rename σ b') ↔ FnEq (Handler.reduct σ h) t b b' := by
  simp only [FnEq, L.exec_rename]
  exact Iff.rfl

/-! ### Formulas -/

/-- Conjunctions of atoms. -/
inductive Formula (α : Type) where
  | top
  | atom (a : α)
  | and (φ ψ : Formula α)

namespace Formula

variable {α β γ : Type}

/-- Mapping atoms. -/
def map (f : α → β) : Formula α → Formula β
  | top => top
  | atom a => atom (f a)
  | and φ ψ => and (φ.map f) (ψ.map f)

/-- Truth, given the truth of atoms. -/
def Holds (P : α → Prop) : Formula α → Prop
  | top => True
  | atom a => P a
  | and φ ψ => φ.Holds P ∧ ψ.Holds P

theorem map_id (φ : Formula α) : φ.map id = φ := by
  induction φ with
  | top => rfl
  | atom a => rfl
  | and φ ψ ihφ ihψ => simp only [map, ihφ, ihψ]

theorem map_map (f : α → β) (g : β → γ) (φ : Formula α) : (φ.map f).map g = φ.map (g ∘ f) := by
  induction φ with
  | top => rfl
  | atom a => rfl
  | and φ ψ ihφ ihψ => simp only [map, ihφ, ihψ]

theorem holds_map (f : α → β) (P : β → Prop) (φ : Formula α) :
    (φ.map f).Holds P ↔ φ.Holds (fun a => P (f a)) := by
  induction φ with
  | top => exact Iff.rfl
  | atom a => exact Iff.rfl
  | and φ ψ ihφ ihψ => exact and_congr ihφ ihψ

theorem holds_congr {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) (φ : Formula α) :
    φ.Holds P ↔ φ.Holds Q := by
  induction φ with
  | top => exact Iff.rfl
  | atom a => exact h a
  | and φ ψ ihφ ihψ => exact and_congr ihφ ihψ

theorem holds_mono {P Q : α → Prop} (h : ∀ a, P a → Q a) (φ : Formula α) :
    φ.Holds P → φ.Holds Q := by
  induction φ with
  | top => exact id
  | atom a => exact h a
  | and φ ψ ihφ ihψ => exact fun hφψ => ⟨ihφ hφψ.1, ihψ hφψ.2⟩

end Formula

/-! ### Presentations by handlers -/

/-- An institution whose models are handlers over an underlying context of each signature:
sentences, their translation, and a satisfaction relation invariant under handler reducts. -/
structure HPres (L : Lang) (W : Type) (Sign : Type) [Category.{0} Sign] where
  /-- The module context of a signature. -/
  ctx : Sign ⥤ Ctx
  /-- Sentences. -/
  Sen : Sign → Type
  /-- Sentence translation. -/
  map : ∀ {S S' : Sign}, (S ⟶ S') → Sen S → Sen S'
  map_id : ∀ (S : Sign) (φ : Sen S), map (𝟙 S) φ = φ
  map_comp : ∀ {S S' S'' : Sign} (σ : S ⟶ S') (τ : S' ⟶ S'') (φ : Sen S),
    map (σ ≫ τ) φ = map τ (map σ φ)
  /-- Satisfaction by a handler. -/
  Sat : ∀ {S : Sign}, Handler L W (ctx.obj S) → Sen S → Prop
  /-- The satisfaction condition. -/
  sat_map : ∀ {S S' : Sign} (σ : S ⟶ S') (h : Handler L W (ctx.obj S')) (φ : Sen S),
    Sat h (map σ φ) ↔ Sat (Handler.reduct (ctx.map σ) h) φ

namespace HPres

variable {Sign : Type} [Category.{0} Sign] (P : HPres L W Sign)

/-- The plain presentation: models are handlers, the reduct precomposes with event renaming. -/
def toPlain : Plain.{0, 0, 0, 0} Sign where
  Sen := P.Sen
  map := P.map
  map_id := P.map_id
  map_comp := P.map_comp
  Mod S := Handler L W (P.ctx.obj S)
  reduct σ h := Handler.reduct (P.ctx.map σ) h
  reduct_id S h := by simp only [Functor.map_id, Handler.reduct_id]
  reduct_comp σ τ h := by simp only [Functor.map_comp, Handler.reduct_comp]
  Sat h φ := P.Sat h φ
  sat_map := P.sat_map

/-- The institution of a presentation by handlers. -/
abbrev inst : Institution₀ := P.toPlain.toInst

end HPres

/-! ### Atoms and their semantics -/

/-- Atoms of the function-focused institutions: segment equivalences at any segment type, and
body equivalences at the function indices `I` of the focus. -/
inductive FnAtom (L : Lang) (C : Ctx) (I : Type) where
  | seg (τ : SegTy) (b b' : L.Code C)
  | fn (i : I) (b b' : L.Code C)

namespace FnAtom

variable {C C' : Ctx} {I I' : Type}

/-- Renaming an atom along an embedding and a map of focus indices. -/
def rename (σ : C ⟶ C') (f : I → I') : FnAtom L C I → FnAtom L C' I'
  | seg τ b b' => seg τ (L.rename σ b) (L.rename σ b')
  | fn i b b' => fn (f i) (L.rename σ b) (L.rename σ b')

/-- Truth of an atom in a handler; `ix` reads a focus index as a function index. -/
def Holds (ix : I → C.Idx .func) (h : Handler L W C) : FnAtom L C I → Prop
  | seg τ b b' => SegEq h τ b b'
  | fn i b b' => FnEq h (C.fty (ix i)) b b'

theorem rename_id (a : FnAtom L C I) : a.rename (𝟙 C) id = a := by
  cases a <;> simp only [rename, L.rename_id, id]

theorem rename_comp {C'' : Ctx} {I'' : Type} (σ : C ⟶ C') (τ : C' ⟶ C'') (f : I → I')
    (g : I' → I'') (a : FnAtom L C I) :
    a.rename (σ ≫ τ) (g ∘ f) = (a.rename σ f).rename τ g := by
  cases a <;> simp only [rename, L.rename_comp, Function.comp]

/-- The satisfaction condition of atoms. -/
theorem holds_rename (σ : C ⟶ C') (f : I → I') (ix : I → C.Idx .func) (ix' : I' → C'.Idx .func)
    (hix : ∀ i, ix' (f i) = Ctx.Hom.map σ .func (ix i)) (h : Handler L W C')
    (a : FnAtom L C I) :
    (a.rename σ f).Holds ix' h ↔ a.Holds ix (Handler.reduct σ h) := by
  cases a with
  | seg τ b b' => exact segEq_rename σ h τ b b'
  | fn i b b' =>
    show FnEq h (C'.fty (ix' (f i))) _ _ ↔ FnEq _ (C.fty (ix i)) b b'
    rw [hix i, Ctx.Hom.fty σ (ix i)]
    exact fnEq_rename σ h _ b b'

end FnAtom

/-! ### The four signature categories -/

/-- Signatures with an abstract hole: a context and the type of the segment. -/
structure HoleSig where
  C : Ctx
  ty : SegTy

/-- Morphisms of hole signatures: embeddings that keep the segment type. -/
structure HoleSig.Hom (S S' : HoleSig) where
  emb : S.C ⟶ S'.C
  ty : S.ty = S'.ty

@[ext] theorem HoleSig.Hom.ext {S S' : HoleSig} {σ τ : HoleSig.Hom S S'} (h : σ.emb = τ.emb) :
    σ = τ := by
  cases σ; cases τ; cases h; rfl

instance : Category HoleSig where
  Hom := HoleSig.Hom
  id S := ⟨𝟙 S.C, rfl⟩
  comp σ τ := ⟨σ.emb ≫ τ.emb, σ.ty.trans τ.ty⟩

/-- Signatures focused on one function. -/
structure OneSig where
  C : Ctx
  f : C.Idx .func

/-- Morphisms of one-function signatures: embeddings that map the focus to the focus. -/
structure OneSig.Hom (S S' : OneSig) where
  emb : S.C ⟶ S'.C
  f : Ctx.Hom.map emb .func S.f = S'.f

@[ext] theorem OneSig.Hom.ext {S S' : OneSig} {σ τ : OneSig.Hom S S'} (h : σ.emb = τ.emb) :
    σ = τ := by
  cases σ; cases τ; cases h; rfl

instance : Category OneSig where
  Hom := OneSig.Hom
  id S := ⟨𝟙 S.C, rfl⟩
  comp σ τ := ⟨σ.emb ≫ τ.emb, by
    show Ctx.Hom.map τ.emb .func (Ctx.Hom.map σ.emb .func _) = _
    rw [σ.f, τ.f]⟩

/-- Signatures focused on a set of functions. -/
structure SetSig where
  C : Ctx
  F : Set (C.Idx .func)

/-- Morphisms of several-function signatures: embeddings that map the focus into the focus. -/
structure SetSig.Hom (S S' : SetSig) where
  emb : S.C ⟶ S'.C
  F : ∀ i ∈ S.F, Ctx.Hom.map emb .func i ∈ S'.F

@[ext] theorem SetSig.Hom.ext {S S' : SetSig} {σ τ : SetSig.Hom S S'} (h : σ.emb = τ.emb) :
    σ = τ := by
  cases σ; cases τ; cases h; rfl

instance : Category SetSig where
  Hom := SetSig.Hom
  id S := ⟨𝟙 S.C, fun _ hi => hi⟩
  comp σ τ := ⟨σ.emb ≫ τ.emb, fun i hi => τ.F _ (σ.F i hi)⟩

/-- The underlying context of hole signatures. -/
def HoleSig.ctx : HoleSig ⥤ Ctx where
  obj S := S.C
  map σ := HoleSig.Hom.emb σ

/-- The underlying context of one-function signatures. -/
def OneSig.ctx : OneSig ⥤ Ctx where
  obj S := S.C
  map σ := OneSig.Hom.emb σ

/-- The underlying context of several-function signatures. -/
def SetSig.ctx : SetSig ⥤ Ctx where
  obj S := S.C
  map σ := SetSig.Hom.emb σ

/-- The focus of a several-function signature, as a type. -/
abbrev SetSig.Focus (S : SetSig) : Type := {i : S.C.Idx .func // i ∈ S.F}

/-- The focus map of a several-function morphism. -/
def SetSig.Hom.focus {S S' : SetSig} (σ : S ⟶ S') : S.Focus → S'.Focus :=
  fun i => ⟨Ctx.Hom.map (SetSig.Hom.emb σ) .func i.1, SetSig.Hom.F σ i.1 i.2⟩

/-! ### The four presentations -/

variable (L W)

/-- **The abstract-hole institution**: sentences are conjunctions of equivalences of segments
of the hole's type. -/
def holePres : HPres L W HoleSig where
  ctx := HoleSig.ctx
  Sen S := Formula (L.Code S.C × L.Code S.C)
  map σ φ := φ.map fun p => (L.rename (HoleSig.Hom.emb σ) p.1, L.rename (HoleSig.Hom.emb σ) p.2)
  map_id S φ := by
    show φ.map _ = φ
    conv_rhs => rw [← Formula.map_id φ]
    exact congrArg (fun f => φ.map f) (funext fun p => by
      show (L.rename (𝟙 S.C) p.1, L.rename (𝟙 S.C) p.2) = p
      rw [L.rename_id, L.rename_id])
  map_comp σ τ φ := by
    show φ.map _ = (φ.map _).map _
    rw [Formula.map_map]
    exact congrArg (fun f => φ.map f) (funext fun p => by
      simp only [Function.comp]
      exact Prod.ext (L.rename_comp _ _ _) (L.rename_comp _ _ _))
  Sat {S} h φ := φ.Holds fun p => SegEq h S.ty p.1 p.2
  sat_map {S S'} σ h φ := by
    rw [Formula.holds_map]
    refine Formula.holds_congr (fun p => ?_) φ
    show SegEq h S'.ty _ _ ↔ SegEq _ S.ty p.1 p.2
    rw [← HoleSig.Hom.ty σ]
    exact segEq_rename _ h S.ty p.1 p.2

/-- **The one-function institution**. -/
def onePres : HPres L W OneSig where
  ctx := OneSig.ctx
  Sen S := Formula (FnAtom L S.C Unit)
  map σ φ := φ.map (FnAtom.rename (OneSig.Hom.emb σ) id)
  map_id S φ := by
    show φ.map _ = φ
    conv_rhs => rw [← Formula.map_id φ]
    exact congrArg (fun f => φ.map f) (funext fun a => FnAtom.rename_id a)
  map_comp σ τ φ := by
    show φ.map _ = (φ.map _).map _
    rw [Formula.map_map]
    exact congrArg (fun f => φ.map f) (funext fun a => FnAtom.rename_comp _ _ id id a)
  Sat {S} h φ := φ.Holds (FnAtom.Holds (fun _ => S.f) h)
  sat_map {S S'} σ h φ := by
    rw [Formula.holds_map]
    exact Formula.holds_congr (fun a => FnAtom.holds_rename _ id _ _
      (fun _ => (OneSig.Hom.f σ).symm) h a) φ

/-- **The several-function institution**. -/
def setPres : HPres L W SetSig where
  ctx := SetSig.ctx
  Sen S := Formula (FnAtom L S.C S.Focus)
  map σ φ := φ.map (FnAtom.rename (SetSig.Hom.emb σ) (SetSig.Hom.focus σ))
  map_id S φ := by
    show φ.map _ = φ
    conv_rhs => rw [← Formula.map_id φ]
    exact congrArg (fun f => φ.map f) (funext fun a => FnAtom.rename_id a)
  map_comp σ τ φ := by
    show φ.map _ = (φ.map _).map _
    rw [Formula.map_map]
    exact congrArg (fun f => φ.map f) (funext fun a =>
      FnAtom.rename_comp (SetSig.Hom.emb σ) (SetSig.Hom.emb τ) (SetSig.Hom.focus σ)
        (SetSig.Hom.focus τ) a)
  Sat {S} h φ := φ.Holds (FnAtom.Holds Subtype.val h)
  sat_map {S S'} σ h φ :=
    (Formula.holds_map _ _ φ).trans (Formula.holds_congr (fun a =>
      FnAtom.holds_rename (SetSig.Hom.emb σ) (SetSig.Hom.focus σ) Subtype.val Subtype.val
        (fun _ => rfl) h a) φ)

/-- **The all-function institution**: signatures are contexts. -/
def allPres : HPres L W Ctx where
  ctx := 𝟭 Ctx
  Sen C := Formula (FnAtom L C (C.Idx .func))
  map σ φ := φ.map (FnAtom.rename σ (Ctx.Hom.map σ .func))
  map_id C φ := by
    show φ.map _ = φ
    conv_rhs => rw [← Formula.map_id φ]
    exact congrArg (fun f => φ.map f) (funext fun a => FnAtom.rename_id a)
  map_comp σ τ φ := by
    show φ.map _ = (φ.map _).map _
    rw [Formula.map_map]
    exact congrArg (fun f => φ.map f) (funext fun a =>
      FnAtom.rename_comp σ τ (Ctx.Hom.map σ .func) (Ctx.Hom.map τ .func) a)
  Sat {C} h φ := φ.Holds (FnAtom.Holds id h)
  sat_map σ h φ :=
    (Formula.holds_map _ _ φ).trans (Formula.holds_congr (fun a =>
      FnAtom.holds_rename σ (Ctx.Hom.map σ .func) id id (fun _ => rfl) h a) φ)

/-- The abstract-hole institution. -/
abbrev holeInst : Institution₀ := (holePres L W).inst
/-- The one-function institution. -/
abbrev oneInst : Institution₀ := (onePres L W).inst
/-- The several-function institution. -/
abbrev setInst : Institution₀ := (setPres L W).inst
/-- The all-function institution. -/
abbrev allInst : Institution₀ := (allPres L W).inst

end Silmaril.Wasm.FnInst
