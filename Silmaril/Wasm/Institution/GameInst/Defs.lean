module

public import Silmaril.Games.Institution.Thms
public import Silmaril.Games.InstFacade.Defs
public import Silmaril.Wasm.Institution.Games.Defs
public import Silmaril.Wasm.Spec.Format.Thms

/-!
# Wasm logics in the institution of game semantics

Maps from the game-based Wasm logics into `Silmaril.Games.GInst` (`docs/projects/spectec/README.md` §2.3).

## From the game-semantics logic `gameSem G E`

`coHom G E : Inst.CoHom (gameSem G E).inst GInst`, the comorphism of the game reading
`reading G E : GInst.Reading (gameSem G E).inst` (`Silmaril.Games.InstFacade.Defs`).

* Signatures: `gameΦ` sends a gameSem signature `(V, X)` (program variables `V` at interface
  `X`) to the game `(E, copies V (G.sig X))`. It offers `V` copies of the operations of `X`,
  one for each unknown component. A signature morphism `(ren, sub)` goes to the game morphism
  with identity lower renaming and upper renaming `copiesHom ren (G.hom sub)`.
* Models: a strategy `σ` of the game goes to the assignment `v ↦ σ.restrict (inj v)`
  (`modOf`), which serves copy `v` only.
* Sentences: a gameSem sentence goes to the property "its model assignment satisfies it"
  (`senOf`, the sentence translation `Reading.sen` of the reading).
  The reading is natural by `reduct_modOf`: restricting the copies and then along `sub` is the
  same as reducting the game first. The builder `GInst.Reading.coHom` supplies the corridors
  and both naturality squares (`(reading G E).corridor A`, `(reading G E).sen_map f s`).
* `senOf_le_prog`: an atom `x ⊑ p` (an unknown refines a program) goes to a **play
  sentence** `□ (pull (injHom x) ⟦p⟧)`. This is safety with respect to the plays of `p`, read
  through copy `x`. Atoms between two unknowns are not play sentences, which is why `GInst`
  sentences are properties of strategies.

`redCoHom` and `ltsCoHom` compose the existing translations `redToGame`/`ltsToGame` with
`coHom`.

## From the trace institutions `Spec.Format.inst`

`Event A R X` and `Move` have the same shape. `specGame X` is the game
`(sigOf imports, sigOf exports)`, and `toEvent` forgets the question carried by an answer.
`stratSemantics A R` is the trace semantics whose programs are strategies; `Good` comes from
prefix closure. At each interface there is a corridor `specCorridor L X` from the Spec room
of `L`-specifications of strategies to the `GInst` room of `specGame X`. For the safety logic
and the test logic, `models_safety_iff` and `models_test_iff` identify Spec satisfaction with
`□` and `◇` sentences.

**Open (not a comorphism yet).** These corridors do not form an institution comorphism
`Spec.Format.inst L stratSemantics → GInst`, for two reasons.

1. A Spec model is a program together with an observation `⟨iface, obs, prog⟩`. Its reduct
   changes `obs` and keeps `prog`, while a `GInst` reduct changes the strategy, so the square
   for models does not commute strictly.
2. A Spec interface morphism embeds imports covariantly and erases unobserved import events.
   A `GInst` lower renaming is contravariant, because each lower call of the larger game must
   be forwarded to the smaller one.

A comorphism would need a Spec semantics quotiented by observation, and an import-erasing
lower reduct in `GInst`.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.GameInst

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Games (Game Strategy GSen GInst Move Ev)
open Silmaril.Wasm.Institution.Games (GameIfaces gameSem redSem ltsSem redToGame ltsToGame)

/-! ## Copies of a signature -/

/-- `V` copies of a signature: one operation `(v, q)` for each copy `v` and operation `q`. -/
abbrev copies (V : Type) (S : Silmaril.Games.Sig.{0}) : Silmaril.Games.Sig.{0} :=
  ⟨V × S.Op, fun vq => S.Ar vq.2⟩

/-- Renaming copies and operations. -/
def copiesHom {V W : Type} {S T : Silmaril.Games.Sig.{0}} (ren : V → W) (h : Silmaril.Games.Sig.Hom S T) :
    Silmaril.Games.Sig.Hom (copies V S) (copies W T) :=
  ⟨fun vq => (ren vq.1, h.op vq.2), fun vq n => h.ar vq.2 n⟩

/-- The copy `v` of a signature. -/
def inj {V : Type} {S : Silmaril.Games.Sig.{0}} (v : V) : Silmaril.Games.Sig.Hom S (copies V S) :=
  ⟨fun q => (v, q), fun _ n => n⟩

/-! ## The game-semantics logic -/

variable (G : GameIfaces) (E : Silmaril.Games.Sig.{0})

/-- The game of a gameSem signature `(V, X)`: `V` copies of the operations of `X`. -/
abbrev gameOf (A : Silmaril.Wasm.Institution.Sig G.I) : Game.{0} :=
  ⟨E, copies A.V (G.sig A.iface)⟩

/-- The game morphism of a gameSem signature morphism. -/
abbrev homOf {A B : Silmaril.Wasm.Institution.Sig G.I} (f : A ⟶ B) :
    gameOf G E A ⟶ gameOf G E B :=
  (⟨Silmaril.Games.Sig.Hom.id E, copiesHom f.ren (G.hom f.sub)⟩ : Game.Hom (gameOf G E A) (gameOf G E B))

/-- Signatures of `gameSem G E` as games. -/
def gameΦ : Silmaril.Wasm.Institution.Sig G.I ⥤ Game.{0} where
  obj A := gameOf G E A
  map f := homOf G E f
  map_id A := by
    change (⟨Silmaril.Games.Sig.Hom.id E, copiesHom id (G.hom (𝟙 A.iface))⟩ :
        Game.Hom (gameOf G E A) (gameOf G E A)) =
      ⟨Silmaril.Games.Sig.Hom.id E, Silmaril.Games.Sig.Hom.id _⟩
    rw [G.hom_id]
    rfl
  map_comp {A B C} f g := by
    change (⟨Silmaril.Games.Sig.Hom.id E, copiesHom (g.ren ∘ f.ren) (G.hom (f.sub ≫ g.sub))⟩ :
        Game.Hom (gameOf G E A) (gameOf G E C)) =
      ⟨(Silmaril.Games.Sig.Hom.id E).comp (Silmaril.Games.Sig.Hom.id E),
        (copiesHom f.ren (G.hom f.sub)).comp (copiesHom g.ren (G.hom g.sub))⟩
    rw [G.hom_comp]
    rfl

/-- The model assignment of a strategy: copy `v` serves variable `v`. -/
def modOf (A : Silmaril.Wasm.Institution.Sig G.I) (σ : (gameOf G E A).Model) :
    (gameSem G E).Model A :=
  fun v => σ.restrict (inj v)

/-- Model assignments commute with reducts. -/
theorem reduct_modOf {A B : Silmaril.Wasm.Institution.Sig G.I} (f : A ⟶ B)
    (σ : (gameOf G E B).Model) :
    ((gameSem G E).reduct f).obj (modOf G E B σ) =
      modOf G E A (Game.reduct (homOf G E f) σ) := by
  funext v
  have h := Game.reduct_id_lo (E := E) (copiesHom f.ren (G.hom f.sub)) σ
  calc (σ.restrict (inj (f.ren v))).restrict (G.hom f.sub)
      = σ.restrict ((G.hom f.sub).comp (inj (f.ren v))) := (Strategy.restrict_comp σ _ _).symm
    _ = (σ.restrict (copiesHom f.ren (G.hom f.sub))).restrict (inj v) :=
        Strategy.restrict_comp σ (inj v) (copiesHom f.ren (G.hom f.sub))
    _ = _ := congrArg (fun τ : Strategy E (copies A.V (G.sig A.iface)) => τ.restrict (inj v)) h.symm

/-- **The game reading of the game-semantics logic**: copy `v` of the strategy serves variable
`v`. -/
def reading : GInst.Reading (gameSem G E).inst where
  game := gameΦ G E
  mod := modOf G E
  mod_reduct f σ := reduct_modOf G E f σ

/-- The sentence translation: a gameSem sentence holds of a strategy when it holds of its
model assignment. It is the sentence translation of `reading`. -/
def senOf (A : Silmaril.Wasm.Institution.Sig G.I) (s : (gameSem G E).Sen A) :
    GSen (gameOf G E A).E (gameOf G E A).F :=
  (reading G E).sen A s

/-- **The comorphism from the game-semantics logic into `GInst`**: the comorphism of the game
reading `reading G E`. -/
def coHom : Inst.CoHom (gameSem G E).inst GInst :=
  (reading G E).coHom

/-- The game morphism reading copy `x`. -/
def injHom (A : Silmaril.Wasm.Institution.Sig G.I) (x : A.V) :
    (⟨E, G.sig A.iface⟩ : Game.{0}) ⟶ gameOf G E A :=
  (⟨Silmaril.Games.Sig.Hom.id E, inj x⟩ : Game.Hom ⟨E, G.sig A.iface⟩ (gameOf G E A))

/-- **An atom `x ⊑ p` becomes a play sentence**: safety with respect to the plays of `p`, read
through copy `x`. -/
theorem senOf_le_prog (A : Silmaril.Wasm.Institution.Sig G.I) (x : A.V)
    (p : (gameSem G E).Prog) :
    senOf G E A ⟨A.iface, 𝟙 _, .le (.var x) (.prog p)⟩ =
      GSen.box (Game.pull (injHom G E A x) ((gameSem G E).den A.iface p).plays) := by
  rw [← Game.map_box]
  refine GSen.ext (funext fun σ => propext ?_)
  have h₁ := Game.reduct_id_lo (E := E) (inj (S := G.sig A.iface) x) σ
  have h₂ : (σ.restrict (inj x)).restrict (G.hom (𝟙 A.iface)) = σ.restrict (inj x) := by
    rw [G.hom_id, Strategy.restrict_id]
  change (σ.restrict (inj x)).restrict (G.hom (𝟙 A.iface)) ≤ (gameSem G E).den A.iface p ↔
    ∀ s ∈ Game.reduct (G := ⟨E, _⟩) (G' := ⟨E, _⟩) ⟨Silmaril.Games.Sig.Hom.id E, inj x⟩ σ,
      s ∈ ((gameSem G E).den A.iface p).plays
  rw [h₁, h₂]
  exact Iff.rfl

/-- The sentence part of `coHom` is `senOf`. -/
theorem coHom_sen (A : Silmaril.Wasm.Institution.Sig G.I) (s : (gameSem G E).Sen A) :
    ((coHom G E).ρ.app A).sen s = senOf G E A s := rfl

variable {RProg : Type}

/-- Reduction semantics into `GInst`, through `redToGame`. -/
noncomputable def redCoHom (red : RProg → Silmaril.Games.Reduction E (G.sig G.top)) :
    Inst.CoHom (redSem G E red).inst GInst :=
  (redToGame G E red).coHom.comp (coHom G E)

/-- Transition systems into `GInst`, through `ltsToGame`. -/
noncomputable def ltsCoHom (lts : RProg → Silmaril.Games.LTS E (G.sig G.top)) :
    Inst.CoHom (ltsSem G E lts).inst GInst :=
  (ltsToGame G E lts).coHom.comp (coHom G E)

/-! ## The trace institutions of `Silmaril.Wasm.Spec.Format` -/

section Spec

open Silmaril.Wasm.Spec

variable {Ty A R : Type}

/-- The signature of `n` functions taking `A` and returning `R`. -/
def sigOf (A R : Type) (n : ℕ) : Silmaril.Games.Sig.{0} := ⟨Fin n × A, fun _ => R⟩

/-- The game of a typed interface: imports below, exports above. -/
def specGame (A R : Type) (X : Iface Ty) : Game.{0} :=
  ⟨sigOf A R X.imports.length, sigOf A R X.exports.length⟩

/-- An event of a game interface as a Spec event: answers forget their question. -/
def evOf {n : ℕ} : Ev (sigOf A R n) → SideEv A R n
  | .ask ia => .ask ia.1 ia.2
  | .ans ia r => .ans ia.1 r

/-- A move of `specGame X` as an event of `X` (`Event = Move`). -/
def toEvent {X : Iface Ty} : Move (specGame A R X).E (specGame A R X).F → Event A R X :=
  Sum.map evOf evOf

/-- The traces of a strategy: its plays as events. -/
def stratTraces {X : Iface Ty} (σ : (specGame A R X).Model) : Set (List (Event A R X)) :=
  {t | ∃ s ∈ σ, s.map toEvent = t}

/-- The traces of a strategy are good. -/
theorem stratTraces_good {X : Iface Ty} (σ : (specGame A R X).Model) : Good (stratTraces σ) where
  nil_mem := ⟨[], σ.nil_mem, rfl⟩
  of_prefix := by
    rintro t _ ⟨s, hs, rfl⟩ ht
    refine ⟨s.take t.length, σ.of_prefix hs (List.take_prefix _ _), ?_⟩
    rw [List.map_take, ← List.prefix_iff_eq_take.1 ht]

/-- **Strategies as a Spec trace semantics.** -/
def stratSemantics (Ty A R : Type) : Semantics Ty A R where
  Prog X := (specGame A R X).Model
  traces σ := stratTraces σ
  good σ := stratTraces_good σ

/-- The Spec safety logic: formulas are sets of traces, satisfied by subsets. -/
def safety (Ty A R : Type) : Logic Ty A R where
  Fm X := Set (List (Event A R X))
  Sat T S := T ⊆ S

/-- The Spec test logic: formulas are traces, satisfied by trace sets containing them. -/
def test (Ty A R : Type) : Logic Ty A R where
  Fm X := List (Event A R X)
  Sat T t := t ∈ T

/-- **Spec safety of a strategy is a `□` sentence.** -/
theorem models_safety_iff {X : Iface Ty} (σ : (stratSemantics Ty A R).Prog X)
    (S : Set (List (Event A R X))) :
    Models (safety Ty A R) (stratSemantics Ty A R) σ S ↔
      (GSen.box {s | s.map toEvent ∈ S}).holds (σ : (specGame A R X).Model) := by
  refine (models_iff _ _ _ _).trans ?_
  constructor
  · intro h s hs
    exact h ⟨s, hs, rfl⟩
  · rintro h _ ⟨s, hs, rfl⟩
    exact h s hs

/-- **A Spec test of a strategy is a `◇` sentence.** -/
theorem models_test_iff {X : Iface Ty} (σ : (stratSemantics Ty A R).Prog X) (t : List (Event A R X)) :
    Models (test Ty A R) (stratSemantics Ty A R) σ t ↔
      (GSen.dia {s | s.map toEvent = t}).holds (σ : (specGame A R X).Model) := by
  refine (models_iff _ _ _ _).trans ?_
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, rfl, hs⟩
  · rintro ⟨s, hst, hs⟩
    exact ⟨s, hs, hst⟩

/-- The corridor at an interface: from `L`-specifications of strategies to `GInst`. A Spec
sentence holds of a strategy when the strategy, as a program, satisfies it. -/
def specCorridor (L : Logic Ty A R) (X : Iface Ty) :
    room L (stratSemantics Ty A R) X ⟶ GInst.I.obj (specGame A R X) :=
  ⟨fun s => ⟨fun σ => Silmaril.Wasm.Spec.Sat L (stratSemantics Ty A R) (Model.ofProg σ) s⟩,
    { obj := fun σ => Model.ofProg σ
      map := fun h => ⟨congrArg (fun σ : (specGame A R X).Model =>
        (Model.ofProg σ : Model (stratSemantics Ty A R) X)) h.down⟩ },
    fun _ _ => Iff.rfl⟩

end Spec

end Silmaril.Wasm.Institution.GameInst
