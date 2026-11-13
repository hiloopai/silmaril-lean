module

public import Silmaril.Wasm.Institution.Api.Graphs.Defs

@[expose] public section

/-!
# The Wasm institution API: examples

Small checks that the API reads as intended; `docs/projects/logic-inst.md` ("wasm")
quotes them next to the statements they replace.

* `⊨` and the `simp` transfer lemma `Translation.sat_sen_iff'`;
* `ExpTranslation.ofProg` gives back `Session.progT` definitionally;
* `valid_bir_trapsUB_iff_core_eq'`: the composite validity transfer of `Graph` from the
  edges of `Graph.obsGraph`, without passing surjectivity proofs;
* the identity translation transfers satisfaction trivially.
-/

namespace Silmaril.Wasm.Institution

open CategoryTheory ObsSemantics
open scoped Silmaril.Inst

section
variable {I J : Type} [Category.{0} I] [Category.{0} J] {F : I ⥤ J}
  {A : ObsSemantics I} {B : ObsSemantics J}

/-- `⊨` is the satisfaction of the observational semantics. -/
example (S : ObsSemantics I) (K : Sig I) (β : S.Model K) (s : S.Sen K) :
    β ⊨ s ↔ S.Sat K β s := Iff.rfl

/-- The satisfaction condition of a translation, by `simp`. -/
example (T : Translation F A B) (K : Sig I) (β : B.Model ((Sig.map F).obj K)) (s : A.Sen K) :
    β ⊨ T.sen s ↔ (T.modFun K).obj β ⊨ s := by
  simp

/-- The same in `⊨` form, by the API lemma. -/
example (T : ExpTranslation F A B) (K : Sig I) (β : B.Model ((Sig.map F).obj K))
    (s : A.Sen K) : β ⊨ T.sen s ↔ (T.modFun K).obj β ⊨ s :=
  T.sat_iff β s

/-- The comorphism of a model-expansive translation is model-expansive, with no side
condition. -/
example (T : ExpTranslation F A B) : T.comorphism.ModelExpansive := T.modelExpansive

end

/-- `ExpTranslation.ofProg` is the generic form of `Session.progT`. -/
example {H : Type} {Prog Prog' : Type} {d : ∀ X : Session.Iface, Prog → Session.Obj H X}
    {d' : ∀ X : Session.Iface, Prog' → Session.Obj H X} (g : Prog → Prog')
    (hg : ∀ X p, d' X (g p) = d X p)
    (Le : ∀ X : Session.Iface, Session.Obj H X → Session.Obj H X → Prop) :
    (ExpTranslation.ofProg (Session.mk Prog d Le) (d' := d') g hg).toTranslation =
      Session.progT g hg Le :=
  rfl

namespace Graph

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (Env : Module → Store H → List ExternAddr → Prop)

/-- `valid_bir_trapsUB_iff_core_eq` through the API: each edge of `obsGraph` carries its own
surjectivity, so the proof is two `valid_iff`s. -/
theorem valid_bir_trapsUB_iff_core_eq' {K : Sig (Set String)}
    (s : Sen (sem P host Env ⟨.session, .bir, .refTrapsUB⟩) K) :
    (sem P host Env ⟨.session, .bir, .refTrapsUB⟩).Valid s ↔
      (sem P host Env ⟨.session, .core, .refEq⟩).Valid
        (((obsGraph P host Env).edge (.close .session .core)).sen
          (((obsGraph P host Env).edge (.lower .session .refTrapsUB)).sen s)) :=
  (((obsGraph P host Env).edge (Edge.lower .session .refTrapsUB)).valid_iff s).trans
    (((obsGraph P host Env).edge (Edge.close .session .core)).valid_iff _)

/-- The API statement is the existing one. -/
example {K : Sig (Set String)} (s : Sen (sem P host Env ⟨.session, .bir, .refTrapsUB⟩) K) :
    valid_bir_trapsUB_iff_core_eq' P host Env s = valid_bir_trapsUB_iff_core_eq P host Env s :=
  rfl

/-- Borrowing along any path of the phase-1 graph, from `AllExpansive`. -/
example {a b : (graph P host Env).Idx} (p : Quiver.Path a b)
    (S : LogicGraph.Sign (graph P host Env) a)
    (Γ : Set (LogicGraph.FlatRoom (graph P host Env) a S).Sen)
    (φ : (LogicGraph.FlatRoom (graph P host Env) a S).Sen) :
    (LogicGraph.FlatRoom (graph P host Env) a S).Entails Γ φ ↔
      (LogicGraph.FlatRoom (graph P host Env) b
          (LogicGraph.pathSig (graph P host Env) p S)).Entails
        (LogicGraph.pathSen (graph P host Env) p S '' Γ)
        (LogicGraph.pathSen (graph P host Env) p S φ) :=
  (allExpansive P host Env).entails_path_iff p S Γ φ

/-! ### Through the facade -/

/-- Two edges of the phase-1 graph as a facade `GraphSpec`: every edge model-expansive for
free, so every path borrows. -/
noncomputable abbrev spec₂ : Silmaril.Inst.GraphSpec (obsGraph P host Env).inst :=
  (obsGraph P host Env).toSpec
    [⟨_, _, Edge.lower .session .refTrapsUB⟩, ⟨_, _, Edge.close .session .core⟩]

example : (spec₂ P host Env).AllModelExpansive :=
  (obsGraph P host Env).toSpec_allModelExpansive _ _

/-- The nodes of `obsGraph` are facade `Institution₁`s. -/
example (a : Node) : Silmaril.Inst.Institution₁ := (obsGraph P host Env).inst a

/-- `valid_bir_trapsUB_iff_core_eq` in the facade's terms: two `ExpTranslation.valid_iff'`s,
composed. -/
example {K : Sig (Set String)} (s : Sen (sem P host Env ⟨.session, .bir, .refTrapsUB⟩) K) :
    (Silmaril.Inst.Institution.ofObs (sem P host Env ⟨.session, .bir, .refTrapsUB⟩)).Valid s ↔
      (Silmaril.Inst.Institution.ofObs (sem P host Env ⟨.session, .core, .refEq⟩)).Valid
        ((((obsGraph P host Env).edge (.lower .session .refTrapsUB)).comorphism ≫ᶜ
          ((obsGraph P host Env).edge (.close .session .core)).comorphism).sen K s) :=
  (((obsGraph P host Env).edge (Edge.lower .session .refTrapsUB)).valid_iff' s).trans
    (((obsGraph P host Env).edge (Edge.close .session .core)).valid_iff' _)

end Graph

section Facade

variable {I J : Type} [Category.{0} I] [Category.{0} J] {F : I ⥤ J}
  {A : ObsSemantics I} {B : ObsSemantics J}

/-- `⊨` and the facade's `⊨[A]` are the same relation. -/
example (S : ObsSemantics I) (K : Sig I) (β : S.Model K) (s : S.Sen K) :
    β ⊨ s ↔ β ⊨[Silmaril.Inst.Institution.ofObs S] s := Iff.rfl

/-- The satisfaction condition of the comorphism of a translation, by the facade lemma
`Comorphism.sat_sen_iff`. (`simp` does not fire here: `Institution.ofObs B` unfolds to
`B.inst`, a semireducible `def`, so `(Sig.map F).obj K` is a signature of `ofObs B` only up to
default transparency; see the guide's gap list.) -/
example (T : Translation F A B) (K : Sig I) (β : B.Model ((Sig.map F).obj K)) (s : A.Sen K) :
    β ⊨[Silmaril.Inst.Institution.ofObs B] (Silmaril.Inst.Comorphism.ofObs T).sen K s ↔
      (Silmaril.Inst.Comorphism.ofObs T).mod K β ⊨[Silmaril.Inst.Institution.ofObs A] s :=
  (Silmaril.Inst.Comorphism.ofObs T).sat_sen_iff K β s

/-- Composition of translations' comorphisms with the facade notation, and its
model-expansiveness from the parts. -/
example {C : ObsSemantics I} (T : ExpTranslation (𝟭 I) A A) (U : ExpTranslation (𝟭 I) A C) :
    (T.comorphism ≫ᶜ U.comorphism).ModelExpansive :=
  T.modelExpansive.comp U.modelExpansive

/-- The identity comorphism through the facade is the comorphism of the identity
equivalence. -/
example (S : ObsSemantics I) :
    𝟙ᶜ (Silmaril.Inst.Institution.ofObs S) = Silmaril.Inst.Comorphism.ofIso (Iso.refl S.institution) :=
  ObsSemantics.ofObs_id_eq_ofIso S

end Facade

end Silmaril.Wasm.Institution
