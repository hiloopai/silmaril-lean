module

public import Silmaril.Compile.Category.Factor
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-!
# Passes and pipelines: composing compiler stages across the zoo

The API in which every stage of every pipeline is stated, so that a new stage needs only its
own local correctness lemma and the end-to-end theorem of any pipeline containing it follows
by composition (the lax law, `valid_comp_le`).

* `Pass c` — a stage between any two languages of the zoo, **indexed by its convention**
  `c : L ⟶ L'`: a partial translation (`none` is a compile-time failure) every success of which
  is valid at `c`. Passes are the morphisms of `CompCat` with their convention made a type
  index (`Pass.toCompiler`, `Pass.ofCompiler`), so a pipeline's convention is computed by type
  checking.
* `Pass.comp : Pass c → Pass d → Pass (c ≫ d)` (notation `≫ₚ`): composition, sound by the lax
  law; `Pass.weaken` moves a pass up the convention order (`valid_mono`), `Pass.congr` along
  an equation of conventions.
* `EndoPass L` — an optimization on one IR: total, and a refinement (`Language.Refines`). It is
  a `Pass (𝟙 L)` (`EndoPass.toPass`), endo-passes form a monoid under sequencing, and composing
  with them leaves a convention unchanged (`Pass.thenEndo : Pass c → EndoPass L' → Pass c`,
  `EndoPass.thenPass`). This is the binaryen `Pass`/`pipeline` monoid
  (`Silmaril/Wasm/Binaryen/PassAPI/Pass.lean`) for an arbitrary zoo language.
* Validators (LCF style): `Pass.checked` and `EndoPass.checked` wrap an *untrusted*
  transformation and a checker whose `true` answers are proved sound; on `false` the pass fails
  (`Pass`) or falls back to its input (`EndoPass`, like binaryen's `Pass.ofOption`/`guardedP`).
* `Pipeline c` — a path through the zoo graph: a list of passes whose conventions compose to
  `c`; `Pipeline.sound` is the end-to-end theorem, by induction, for free.
* `RoundTrip L S` — a lift into another IR and a lowering back, whose composite convention is
  below the identity (`lift.conv ≫ lower.conv ≤ 𝟙 L`): then every endo-pass on `S`
  conjugates to a refinement on `L` (`RoundTrip.conj`). An SSA optimization of Mir is an
  endo-pass on the SSA language, conjugated by the Mir → SSA → Mir round trip.

The same round-trip interface can express SSA optimizations of imperative IRs.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

variable {L L' L'' L''' : Language.{u}}

/-! ## Passes -/

/-- A pass at the convention `c`: a partial translation whose successes are valid at `c`. -/
@[ext]
structure Pass (c : L ⟶ L') where
  /-- The translation; `none` is a compile-time failure. -/
  run : L.Prog → Option L'.Prog
  /-- Soundness: every successful translation is valid at `c`. -/
  sound : ∀ p p', run p = some p' → Valid c p p'

namespace Pass

/-- The identity pass. -/
def id (L : Language.{u}) : Pass (𝟙 L) := ⟨some, fun p _ h => Option.some.inj h ▸ valid_id_refl p⟩

/-- **Composition of passes**: Kleisli composition, valid at the composite convention by the
lax law. -/
def comp {c : L ⟶ L'} {d : L' ⟶ L''} (P : Pass c) (Q : Pass d) : Pass (c ≫ d) where
  run p := (P.run p).bind Q.run
  sound p r h := by
    cases hq : P.run p with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      exact valid_comp_le c d p r ⟨q, P.sound p q hq, Q.sound q r h⟩

@[inherit_doc] infixr:80 " ≫ₚ " => Pass.comp

/-- A pass at a convention is a pass at every larger convention. -/
def weaken {c d : L ⟶ L'} (h : c ≤ d) (P : Pass c) : Pass d :=
  ⟨P.run, fun p p' hp => valid_mono h p p' (P.sound p p' hp)⟩

/-- Transport along an equation of conventions. -/
def congr {c d : L ⟶ L'} (h : c = d) (P : Pass c) : Pass d := ⟨P.run, h ▸ P.sound⟩

@[simp] theorem comp_run {c : L ⟶ L'} {d : L' ⟶ L''} (P : Pass c) (Q : Pass d) (p : L.Prog) :
    (P ≫ₚ Q).run p = (P.run p).bind Q.run := rfl
@[simp] theorem weaken_run {c d : L ⟶ L'} (h : c ≤ d) (P : Pass c) : (P.weaken h).run = P.run :=
  rfl
@[simp] theorem congr_run {c d : L ⟶ L'} (h : c = d) (P : Pass c) : (P.congr h).run = P.run :=
  rfl

theorem id_comp {c : L ⟶ L'} (P : Pass c) : (Pass.id L ≫ₚ P).run = P.run := rfl

theorem comp_id {c : L ⟶ L'} (P : Pass c) : (P ≫ₚ Pass.id L').run = P.run := by
  funext p
  show (P.run p).bind some = P.run p
  cases P.run p <;> rfl

theorem assoc {c : L ⟶ L'} {d : L' ⟶ L''} {e : L'' ⟶ L'''} (P : Pass c) (Q : Pass d)
    (R : Pass e) : ((P ≫ₚ Q) ≫ₚ R).run = (P ≫ₚ Q ≫ₚ R).run := by
  funext p
  show ((P.run p).bind Q.run).bind R.run = (P.run p).bind fun q => (Q.run q).bind R.run
  cases P.run p <;> rfl

/-- What a pass guarantees: target behaviours realise source behaviours. -/
theorem sound_beh {c : L ⟶ L'} (P : Pass c) {p : L.Prog} {p' : L'.Prog}
    (h : P.run p = some p') : L'.beh p' ⊆ c.lift (L.beh p) :=
  ((valid_iff_beh c p p').1 (P.sound p p' h)).2

/-- The compiler of a pass. -/
def toCompiler {c : L ⟶ L'} (P : Pass c) : Compiler L L' := ⟨c, P.run, P.sound⟩

/-- The pass of a compiler, at its convention. -/
def ofCompiler (C : Compiler L L') : Pass C.conv := ⟨C.run, C.sound⟩

theorem toCompiler_comp {c : L ⟶ L'} {d : L' ⟶ L''} (P : Pass c) (Q : Pass d) :
    (P ≫ₚ Q).toCompiler = P.toCompiler.comp Q.toCompiler := rfl

/-- **A validator as a pass** (LCF style): an untrusted translation `f`, kept only when the
checker accepts it; the checker's acceptances are what is proved. -/
def checked {c : L ⟶ L'} (f : L.Prog → Option L'.Prog) (check : L.Prog → L'.Prog → Bool)
    (hcheck : ∀ p p', check p p' = true → Valid c p p') : Pass c where
  run p := (f p).bind fun p' => if check p p' then some p' else none
  sound p p' h := by
    cases hf : f p with
    | none => rw [hf] at h; cases h
    | some q =>
      rw [hf] at h
      simp only [Option.bind_some] at h
      split at h
      · cases h; exact hcheck p _ (by assumption)
      · cases h

end Pass

/-! ## Endo-passes: optimizations on one IR -/

/-- An optimization on one language: total, and a refinement of its input. -/
@[ext]
structure EndoPass (L : Language.{u}) where
  run : L.Prog → L.Prog
  refines : ∀ p, L.Refines p (run p)

namespace EndoPass

/-- The pass of an endo-pass, at the identity convention. -/
def toPass (E : EndoPass L) : Pass (𝟙 L) :=
  ⟨fun p => some (E.run p), fun p _ h => Option.some.inj h ▸ (valid_id_iff _ _).2 (E.refines p)⟩

/-- Doing nothing. -/
protected def id (L : Language.{u}) : EndoPass L := ⟨fun p => p, L.refines_refl⟩

/-- Sequencing: `E` then `F`. -/
def seq (E F : EndoPass L) : EndoPass L :=
  ⟨fun p => F.run (E.run p), fun p => L.refines_trans (E.refines p) (F.refines _)⟩

/-- Endo-passes form a monoid under sequencing (diagrammatic order, as binaryen's). -/
instance : Monoid (EndoPass L) where
  mul := seq
  one := EndoPass.id L
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

theorem mul_run (E F : EndoPass L) (p : L.Prog) : (E * F).run p = F.run (E.run p) := rfl

/-- A list of endo-passes, run left to right. -/
def pipeline (Es : List (EndoPass L)) : EndoPass L := Es.prod

/-- A partial optimization falls back to its input on failure (binaryen's `Pass.ofOption`). -/
def ofPass (P : Pass (𝟙 L)) : EndoPass L where
  run p := (P.run p).getD p
  refines p := by
    cases h : P.run p with
    | none => exact L.refines_refl p
    | some q => exact (valid_id_iff p q).1 (P.sound p q h)

/-- **A validated optimization** (LCF style): the untrusted `f` is kept when the checker
accepts it, and the input is kept otherwise. -/
def checked (f : L.Prog → L.Prog) (check : L.Prog → L.Prog → Bool)
    (hcheck : ∀ p q, check p q = true → L.Refines p q) : EndoPass L where
  run p := if check p (f p) then f p else p
  refines p := by
    split
    · exact hcheck p _ (by assumption)
    · exact L.refines_refl p

theorem checked_run (f : L.Prog → L.Prog) (check : L.Prog → L.Prog → Bool)
    (hcheck : ∀ p q, check p q = true → L.Refines p q) (p : L.Prog) :
    (checked f check hcheck).run p = if check p (f p) then f p else p := rfl

/-- Run an optimization before a pass: the convention is unchanged. -/
def thenPass {c : L ⟶ L'} (E : EndoPass L) (P : Pass c) : Pass c :=
  (E.toPass ≫ₚ P).congr (Category.id_comp c)

end EndoPass

/-- Run an optimization after a pass: the convention is unchanged. -/
def Pass.thenEndo {c : L ⟶ L'} (P : Pass c) (E : EndoPass L') : Pass c :=
  (P ≫ₚ E.toPass).congr (Category.comp_id c)

@[simp] theorem Pass.thenEndo_run {c : L ⟶ L'} (P : Pass c) (E : EndoPass L') (p : L.Prog) :
    (P.thenEndo E).run p = (P.run p).map E.run := by
  show (P.run p).bind (fun q => some (E.run q)) = _
  cases P.run p <;> rfl

@[simp] theorem EndoPass.thenPass_run {c : L ⟶ L'} (E : EndoPass L) (P : Pass c) (p : L.Prog) :
    (E.thenPass P).run p = P.run (E.run p) := rfl

/-! ## Pipelines: paths through the zoo -/

/-- A pipeline: a path of passes through the zoo, indexed by its composite convention. -/
inductive Pipeline : {L L' : Language.{u}} → (L ⟶ L') → Type (u + 1)
  | nil (L : Language.{u}) : Pipeline (𝟙 L)
  | cons {L L' L'' : Language.{u}} {c : L ⟶ L'} {d : L' ⟶ L''} (P : Pass c) (rest : Pipeline d) :
      Pipeline (c ≫ d)

namespace Pipeline

/-- Run a pipeline. -/
def run : {L L' : Language.{u}} → {c : L ⟶ L'} → Pipeline c → L.Prog → Option L'.Prog
  | _, _, _, .nil _, p => some p
  | _, _, _, .cons P rest, p => (P.run p).bind rest.run

/-- The pass of a pipeline. -/
def toPass : {L L' : Language.{u}} → {c : L ⟶ L'} → Pipeline c → Pass c
  | _, _, _, .nil L => Pass.id L
  | _, _, _, .cons P rest => P ≫ₚ rest.toPass

theorem toPass_run {c : L ⟶ L'} (P : Pipeline c) : P.toPass.run = P.run := by
  induction P with
  | nil => rfl
  | cons P rest ih => funext p; simp only [toPass, Pass.comp_run, run, ih]

/-- **The end-to-end theorem of a pipeline**, from the soundness of its passes. -/
theorem sound {c : L ⟶ L'} (P : Pipeline c) {p : L.Prog} {p' : L'.Prog} (h : P.run p = some p') :
    Valid c p p' :=
  P.toPass.sound p p' (by rw [toPass_run]; exact h)

/-- Appending pipelines. -/
def append : {L L' L'' : Language.{u}} → {c : L ⟶ L'} → {d : L' ⟶ L''} → Pipeline c →
    Pipeline d → Pipeline (c ≫ d)
  | _, _, _, _, d, .nil _, Q => (Category.id_comp d).symm ▸ Q
  | _, _, _, _, e, .cons (c := c) (d := d) P rest, Q =>
    (Category.assoc c d e).symm ▸ cons P (rest.append Q)

/-- A one-pass pipeline. -/
def single {c : L ⟶ L'} (P : Pass c) : Pipeline (c ≫ 𝟙 L') := cons P (nil L')

end Pipeline

/-! ## Round trips between IRs -/

/-- A lift into another IR and a lowering back whose composite convention is below the
identity: lifting, then lowering, refines. -/
structure RoundTrip (L S : Language.{u}) where
  {up : L ⟶ S}
  {down : S ⟶ L}
  lift : Pass up
  lower : Pass down
  le_id : up ≫ down ≤ 𝟙 L

namespace RoundTrip

/-- **Conjugation**: an optimization on `S` is a pass at the identity of `L`, through the
round trip. -/
def conj {S : Language.{u}} (T : RoundTrip L S) (E : EndoPass S) : Pass (𝟙 L) :=
  ((T.lift.thenEndo E) ≫ₚ T.lower).weaken T.le_id

theorem conj_run {S : Language.{u}} (T : RoundTrip L S) (E : EndoPass S) (p : L.Prog) :
    (T.conj E).run p = ((T.lift.run p).map E.run).bind T.lower.run := by
  simp [conj, Pass.weaken_run, Pass.comp_run]

/-- The conjugated optimization, with fallback: an endo-pass on `L`. -/
def endo {S : Language.{u}} (T : RoundTrip L S) (E : EndoPass S) : EndoPass L :=
  EndoPass.ofPass (T.conj E)

/-- Conjugation is a monoid map up to the round trip: conjugating `E * F` is a refinement of
the input, like conjugating each (both are endo-passes on `L`). -/
theorem endo_refines {S : Language.{u}} (T : RoundTrip L S) (E : EndoPass S) (p : L.Prog) :
    L.Refines p ((T.endo E).run p) :=
  (T.endo E).refines p

end RoundTrip

end Silmaril.Compile.Category
