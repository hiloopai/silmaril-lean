module

public import Silmaril.Logic.Institution.Hets.LogicGraph
public import Silmaril.Logic.Institution.Hets.Free

@[expose] public section

/-!
# Heterogeneous structured specifications over a logic graph

The heterogeneous kernel language of HetCASL/DOL over a logic graph `L`, with its model-class
semantics. Specifications are indexed by Grothendieck signatures `(a, Σ)`:

* `basic X E`: a presentation in the logic of `X`;
* `union SP₁ SP₂`: union of two specifications over the same signature;
* `translate σ SP`: translation along a Grothendieck signature morphism `σ = (d, σ₀)`, which
  covers homogeneous translation (`d = id`) and heterogeneous translation along a path `d` of
  comorphisms;
* `hide σ SP'`: hiding along a Grothendieck signature morphism;
* `hideMor μ SP`: heterogeneous hiding along a morphism edge `μ : a → b` of the logic graph,
  `derive from SP by μ`, with signature `Φ^μ(Σ)` and models `{β^μ_Σ(M) | M ∈ Mod(SP)}`;
* `free σ SP'` and `cofree σ SP'`: the models of `SP'` free (cofree) over their `σ`-reducts
  (`Hets/Free.lean`).

Derived forms: `extension σ SP E` (`SP then E`, translation followed by union with a basic
specification). The kernel language `StrSpec` of `Hets/StructuredSpec.lean` over the
Grothendieck institution embeds by `ofStrSpec`, preserving model classes
(`models_ofStrSpec`). Entailment is borrowed along heterogeneous hiding by the satisfaction
condition of institution morphisms (`entails_hideMor_iff`).

## References

* `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125, PDF
  page 127: the kernel language) and §6.11 (printed pages 179–180, PDF pages 181–182:
  heterogeneous translation and heterogeneous hiding, "`Sig[derive from SP by μ] := Φ(Σ)`,
  `Mod[derive from SP by μ] := {β_Σ(M') | M' ∈ Mod[SP]}`").
* `mossakowski-codescu-neuhaus-kutz-2015-dol` in `references.bib` and
  `omg-dol-1.0-2018` in `references.bib`: the Distributed Ontology, Model and Specification Language (DOL) structuring constructs.
* `cofi-2004-casl-reference-manual` in `references.bib`: CASL structured specifications
  (`then`, `free`, `cofree`).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u₀ v₀ u v w m₁ m₂

namespace LogicGraph

variable (L : LogicGraph.{u₀, v₀, u, v, w, m₁, m₂})

/-- The room of a Grothendieck signature of the logic graph. -/
abbrev room (X : L.Sig) : Room.{w, m₁, m₂} := (IndexedCoInst.flat L.indexed).obj X

/-- Heterogeneous structured specifications over a logic graph.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125,
PDF page 127) and §6.11 (printed pages 179–180, PDF pages 181–182). -/
inductive LGSpec : L.Sig → Type (max u₀ v₀ u v w)
  /-- A presentation. -/
  | basic (X : L.Sig) (E : Set (L.room X).Sen) : LGSpec X
  /-- Union of two specifications over the same signature. -/
  | union {X : L.Sig} (SP₁ SP₂ : LGSpec X) : LGSpec X
  /-- Translation along a Grothendieck signature morphism. -/
  | translate {X Y : L.Sig} (σ : X ⟶ Y) (SP : LGSpec X) : LGSpec Y
  /-- Hiding along a Grothendieck signature morphism. -/
  | hide {X Y : L.Sig} (σ : X ⟶ Y) (SP' : LGSpec Y) : LGSpec X
  /-- Heterogeneous hiding along a morphism edge of the logic graph. -/
  | hideMor {a b : L.Idx} (μ : L.Mor a b) {S : (L.inst a).Sign} (SP : LGSpec (L.sigOf a S)) :
      LGSpec (L.sigOf b ((L.mor μ).Φ.obj S))
  /-- `free SP' along σ`. -/
  | free {X Y : L.Sig} (σ : X ⟶ Y) (SP' : LGSpec Y) : LGSpec Y
  /-- `cofree SP' along σ`. -/
  | cofree {X Y : L.Sig} (σ : X ⟶ Y) (SP' : LGSpec Y) : LGSpec Y

namespace LGSpec

variable {L}

/-- The model class of a heterogeneous structured specification.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125,
PDF page 127) and §6.11 (printed pages 179–180, PDF pages 181–182). -/
def models : {X : L.Sig} → LGSpec L X → Set (L.room X).Mod
  | _, basic X E => (L.room X).modelsOf E
  | _, union SP₁ SP₂ => SP₁.models ∩ SP₂.models
  | _, translate σ SP => ((IndexedCoInst.flat L.indexed).map σ).mod.obj ⁻¹' SP.models
  | _, hide σ SP' => ((IndexedCoInst.flat L.indexed).map σ).mod.obj '' SP'.models
  | _, @hideMor _ _ _ μ S SP => ((L.mor μ).η.app S).mod.obj '' SP.models
  | _, free σ SP' => freeModels (IndexedCoInst.flat L.indexed) σ SP'.models
  | _, cofree σ SP' => cofreeModels (IndexedCoInst.flat L.indexed) σ SP'.models

/-- Semantic consequence `SP ⊨ φ`. -/
def Entails {X : L.Sig} (SP : LGSpec L X) (φ : (L.room X).Sen) : Prop :=
  ∀ M ∈ SP.models, (L.room X).Sat M φ

/-- Refinement `SP₁ ⇝ SP₂`: every model of `SP₂` is a model of `SP₁`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 126,
PDF page 128). -/
def Refines {X : L.Sig} (SP₁ SP₂ : LGSpec L X) : Prop :=
  SP₂.models ⊆ SP₁.models

/-- The extension `SP then E` along `σ : X ⟶ Y`: translate `SP` and add the axioms `E`. -/
def extension {X Y : L.Sig} (σ : X ⟶ Y) (SP : LGSpec L X) (E : Set (L.room Y).Sen) :
    LGSpec L Y :=
  union (translate σ SP) (basic Y E)

theorem models_extension {X Y : L.Sig} (σ : X ⟶ Y) (SP : LGSpec L X)
    (E : Set (L.room Y).Sen) :
    (extension σ SP E).models =
      ((IndexedCoInst.flat L.indexed).map σ).mod.obj ⁻¹' SP.models ∩ (L.room Y).modelsOf E :=
  rfl

/-- The kernel language over the Grothendieck institution embeds into the heterogeneous
language. -/
def ofStrSpec : {X : L.Sig} → StrSpec (IndexedCoInst.flat L.indexed) X → LGSpec L X
  | _, .basic X E => basic X E
  | _, .union SP₁ SP₂ => union (ofStrSpec SP₁) (ofStrSpec SP₂)
  | _, .translate σ SP => translate σ (ofStrSpec SP)
  | _, .hide σ SP' => hide σ (ofStrSpec SP')

/-- The embedding of the kernel language preserves model classes. -/
theorem models_ofStrSpec {X : L.Sig} (SP : StrSpec (IndexedCoInst.flat L.indexed) X) :
    (ofStrSpec SP).models = SP.models := by
  induction SP with
  | basic X E => rfl
  | union SP₁ SP₂ ih₁ ih₂ =>
    show (ofStrSpec SP₁).models ∩ (ofStrSpec SP₂).models = SP₁.models ∩ SP₂.models
    rw [ih₁, ih₂]
  | translate σ SP ih =>
    show _ ⁻¹' (ofStrSpec SP).models = _ ⁻¹' SP.models
    rw [ih]
  | hide σ SP' ih =>
    show _ '' (ofStrSpec SP').models = _ '' SP'.models
    rw [ih]

/-- **Entailment across heterogeneous hiding**: `derive from SP by μ ⊨ φ` iff `SP ⊨ α^μ(φ)`,
by the satisfaction condition of the institution morphism `μ`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.11 (printed page 179,
PDF page 181), with the satisfaction condition of institution morphisms
(`goguen-burstall-1992` in `references.bib`, §2.5, Definition 13). -/
theorem entails_hideMor_iff {a b : L.Idx} (μ : L.Mor a b) {S : (L.inst a).Sign}
    (SP : LGSpec L (L.sigOf a S)) (φ : ((L.inst b).I.obj ((L.mor μ).Φ.obj S)).Sen) :
    (hideMor μ SP).Entails φ ↔ SP.Entails (((L.mor μ).η.app S).sen φ) := by
  constructor
  · intro h M hM
    exact ((L.mor μ).satisfaction S M φ).2 (h _ ⟨M, hM, rfl⟩)
  · rintro h _ ⟨M, hM, rfl⟩
    exact ((L.mor μ).satisfaction S M φ).1 (h M hM)

end LGSpec

end LogicGraph

end Silmaril.Logic.Institution
