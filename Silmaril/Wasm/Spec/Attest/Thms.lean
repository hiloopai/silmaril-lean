module

public import Silmaril.Wasm.Spec.Attest.Defs
public import Silmaril.Proofs.Wasm.Spec.Attest.Encode

/-!
# Positive propositional logic by "may call `attest`": theorems

For every kit `K` with `K.Ok stopE` (`Silmaril.Wasm.Spec.Attest.Defs`) and all modules:

* `mayCall_or`: `orM M N` may attest iff `M` or `N` may (no hypothesis);
* `mayCall_and`: `andM K M N` may attest iff `M` and `N` may, when `M` propagates traps;
* `orM_trapProp`, `andM_trapProp`, `enc_trapProp`: the combinators keep trap propagation;
* **`mayCall_enc`**: for module valuations `μ` that propagate traps, the encoding of a
  positive formula `φ` may attest iff `φ` holds under `valOf μ` ("`x` holds iff `μ x` may
  attest"). Soundness is the right-to-left direction, completeness the left-to-right one.

## The institution-theoretic reading

Positive propositional logic is the institution whose signatures are sets of variables `V`
(morphisms: functions), sentences `PForm V` (translated by `PForm.rename`) and models valuations
`V → Prop` (reduced by precomposition), with `plRoom V` its room at `V`. The attesting modules
form a second institution over the same signatures and sentences, whose models at `V` are
trap-propagating module valuations and whose satisfaction is "the encoding may attest"
(`attRoom K stopE V`). For a Core 3.0 kit, a leaf satisfies `may attest` iff it violates the
`neverCall attest` sentence of `inst neverCall (wasmSem P)` (`Silmaril.Wasm.Spec.Attest.Core`).

* `corridor K hK V : Corridor (plRoom V) (attRoom K stopE V)`: sentences are kept, a module
  valuation is sent to the valuation it induces, and the satisfaction condition is
  `mayCall_enc`. Its components form a comorphism from positive logic to the attesting modules:
  `plSat_rename` and `attSat_rename` are the two satisfaction conditions along signature
  morphisms, and `valOf_comp` the naturality of the model map. (The functor `Sign ⥤ Room` of
  `Silmaril.Logic.Institution.Inst` is not packaged; its object and arrow parts are these.)
* `corridor_modelExpansive`: every valuation is induced by a module valuation (`tt`/`ff` at each
  variable). Hence **borrowing** (`entails_iff`): semantic consequence between positive formulas
  is the same in both rooms.

New (no source).
-/

public section

namespace Silmaril.Wasm.Spec.Attest

open Silmaril.Games CategoryTheory Silmaril.Logic.Institution

universe u

variable {E : Sig.{u}} {stopE : ∀ m : E.Op, E.Ar m}

/-- **Disjunction**: two modules side by side may attest iff one of them may. -/
theorem mayCall_or (M N : AMod E) : MayCall (orM M N).σ ↔ MayCall M.σ ∨ MayCall N.σ :=
  Silmaril.Proofs.Wasm.Spec.Attest.mayCall_pair M.σ N.σ

/-- **Conjunction**: the two modules linked to the gate may attest iff both may, when the left
one propagates traps. -/
theorem mayCall_and (K : Kit E) (hK : K.Ok stopE) (M N : AMod E) (hM : TrapProp M.σ stopE M.stop) :
    MayCall (andM K M N).σ ↔ MayCall M.σ ∧ MayCall N.σ :=
  ⟨Silmaril.Proofs.Wasm.Spec.Attest.mayCall_and_mp K hK M N,
    fun ⟨h₁, h₂⟩ => Silmaril.Proofs.Wasm.Spec.Attest.mayCall_and_mpr K hK M N hM h₁ h₂⟩

/-- Side by side keeps trap propagation. -/
theorem orM_trapProp {M N : AMod E} (hM : TrapProp M.σ stopE M.stop)
    (hN : TrapProp N.σ stopE N.stop) : TrapProp (orM M N).σ stopE (orM M N).stop :=
  Silmaril.Proofs.Wasm.Spec.Attest.orM_trapProp hM hN

/-- Linking to the gate keeps trap propagation. -/
theorem andM_trapProp (K : Kit E) (hK : K.Ok stopE) {M N : AMod E} (hM : TrapProp M.σ stopE M.stop)
    (hN : TrapProp N.σ stopE N.stop) : TrapProp (andM K M N).σ stopE (andM K M N).stop :=
  Silmaril.Proofs.Wasm.Spec.Attest.andM_trapProp K hK hM hN

/-- Every encoding propagates traps. -/
theorem enc_trapProp {V : Type u} {K : Kit E} (hK : K.Ok stopE) {μ : V → AMod E}
    (hμ : ∀ x, TrapProp (μ x).σ stopE (μ x).stop) (φ : PForm V) :
    TrapProp (enc K μ φ).σ stopE (enc K μ φ).stop :=
  Silmaril.Proofs.Wasm.Spec.Attest.enc_trapProp hK hμ φ

/-- **Soundness and completeness of the encoding**: the module of `φ` may attest iff `φ` holds
when each variable `x` is read as "`μ x` may attest". -/
theorem mayCall_enc {V : Type u} {K : Kit E} (hK : K.Ok stopE) {μ : V → AMod E}
    (hμ : ∀ x, TrapProp (μ x).σ stopE (μ x).stop) (φ : PForm V) :
    MayCall (enc K μ φ).σ ↔ φ.Holds (valOf μ) :=
  Silmaril.Proofs.Wasm.Spec.Attest.mayCall_enc hK hμ φ

/-! ### Signature morphisms -/

/-- Truth of a renamed formula is truth under the reduced valuation. -/
theorem PForm.holds_rename {V W : Type u} (f : V → W) (v : W → Prop) :
    ∀ φ : PForm V, (φ.rename f).Holds v ↔ φ.Holds (v ∘ f)
  | .var _ => Iff.rfl
  | .tt => Iff.rfl
  | .ff => Iff.rfl
  | .or φ ψ => or_congr (holds_rename f v φ) (holds_rename f v ψ)
  | .and φ ψ => and_congr (holds_rename f v φ) (holds_rename f v ψ)

/-- The encoding of a renamed formula is the encoding under the reduced module valuation. -/
theorem enc_rename {V W : Type u} (K : Kit E) (f : V → W) (μ : W → AMod E) :
    ∀ φ : PForm V, enc K μ (φ.rename f) = enc K (μ ∘ f) φ
  | .var _ => rfl
  | .tt => rfl
  | .ff => rfl
  | .or φ ψ => by
    show orM (enc K μ (φ.rename f)) (enc K μ (ψ.rename f)) = orM (enc K (μ ∘ f) φ) (enc K (μ ∘ f) ψ)
    rw [enc_rename K f μ φ, enc_rename K f μ ψ]
  | .and φ ψ => by
    show andM K (enc K μ (φ.rename f)) (enc K μ (ψ.rename f)) =
      andM K (enc K (μ ∘ f) φ) (enc K (μ ∘ f) ψ)
    rw [enc_rename K f μ φ, enc_rename K f μ ψ]

/-- **The satisfaction condition of positive logic** along `f : V → W`. -/
theorem plSat_rename {V W : Type} (f : V → W) (v : W → Prop) (φ : PForm V) :
    (plRoom W).Sat (ULift.up v) (φ.rename f) ↔ (plRoom V).Sat (ULift.up (v ∘ f)) φ :=
  PForm.holds_rename f v φ

/-- **The satisfaction condition of the attesting modules** along `f : V → W`. -/
theorem attSat_rename {E : Sig.{0}} {stopE : ∀ m : E.Op, E.Ar m} (K : Kit E) {V W : Type}
    (f : V → W) (μ : TPVal stopE W) (φ : PForm V) :
    (attRoom K stopE W).Sat μ (φ.rename f) ↔
      (attRoom K stopE V).Sat (⟨μ.val ∘ f, fun x => μ.property (f x)⟩ : TPVal stopE V) φ := by
  show MayCall (enc K μ.val (φ.rename f)).σ ↔ MayCall (enc K (μ.val ∘ f) φ).σ
  rw [enc_rename]

/-- The model map commutes with reducts (naturality). -/
theorem valOf_comp {V W : Type u} (f : V → W) (μ : W → AMod E) : valOf (μ ∘ f) = valOf μ ∘ f :=
  rfl

/-! ### The corridor -/

/-- **The corridor from positive logic to attesting modules** at `V`. -/
def corridor {E : Sig.{0}} {stopE : ∀ m : E.Op, E.Ar m} (K : Kit E) (hK : K.Ok stopE) (V : Type) :
    Corridor (plRoom V) (attRoom K stopE V) where
  sen φ := φ
  mod :=
    { obj := fun μ => (ULift.up (valOf (Subtype.val (p := fun μ : V → AMod E =>
        ∀ x, TrapProp (μ x).σ stopE (μ x).stop) μ)) : Disc (ULift.{1} (V → Prop)))
      map := fun h => ⟨congrArg (fun μ : TPVal stopE V => (ULift.up (valOf μ.val) :
        Disc (ULift.{1} (V → Prop)))) h.down⟩ }
  sat μ φ := mayCall_enc hK μ.property φ

/-- **Every valuation comes from Core-style modules**: put `tt` where it holds, `ff` elsewhere. -/
theorem corridor_modelExpansive {E : Sig.{0}} {stopE : ∀ m : E.Op, E.Ar m} (K : Kit E)
    (hK : K.Ok stopE) (V : Type) : (corridor K hK V).ModelExpansive := by
  classical
  intro v
  let μ : V → AMod E := fun x => if v.down x then K.tt else K.ff
  have hμ : ∀ x, TrapProp (μ x).σ stopE (μ x).stop := fun x => by
    by_cases hx : v.down x
    · rw [show μ x = K.tt from ite_eq_left hx]; exact hK.tt_tp
    · rw [show μ x = K.ff from ite_eq_right hx]; exact hK.ff_tp
  refine ⟨⟨μ, hμ⟩, ?_⟩
  have hval : valOf μ = v.down := funext fun x => by
    by_cases hx : v.down x
    · rw [valOf, show μ x = K.tt from ite_eq_left hx]
      exact propext ⟨fun _ => hx, fun _ => hK.tt_may⟩
    · rw [valOf, show μ x = K.ff from ite_eq_right hx]
      exact propext ⟨fun h => absurd h hK.ff_not, fun h => absurd h hx⟩
  show (ULift.up (valOf μ) : ULift.{1} (V → Prop)) = v
  rw [hval]
  rfl

/-- **Borrowing**: semantic consequence between positive formulas is the same for valuations
and for attesting modules. -/
theorem entails_iff {E : Sig.{0}} {stopE : ∀ m : E.Op, E.Ar m} (K : Kit E) (hK : K.Ok stopE)
    {V : Type} (Γ : Set (PForm V)) (φ : PForm V) :
    (plRoom V).Entails Γ φ ↔ (attRoom K stopE V).Entails Γ φ := by
  have h := (corridor K hK V).entails_map_iff (corridor_modelExpansive K hK V) Γ φ
  have hs : (corridor K hK V).sen '' Γ = Γ := Set.image_id' Γ
  rw [hs] at h
  exact h

end Silmaril.Wasm.Spec.Attest
