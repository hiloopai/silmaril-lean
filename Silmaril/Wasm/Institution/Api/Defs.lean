module

public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.InstObs.Defs
public import Silmaril.Logic.Inst.Builders.Defs
public import Silmaril.Logic.Inst.Graph.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

/-!
# The Wasm institution API

One front door for the institutions that `Silmaril.Wasm.Institution` builds from observational
semantics, expressed through the institution facade `Silmaril.Inst` (`Silmaril.Logic.Inst`): the
institution of an observational semantics is a facade `Institution₁`
(`Silmaril.Inst.Institution.ofObs`), a translation gives a facade `Comorphism` built by
`Comorphism.ofTranslation`, and the typed graph builder `ObsGraph` presents finite edge lists
as a facade `GraphSpec`. Nothing here is a new construction: every definition is an
abbreviation of, or a thin bundle around, the existing one, and every theorem is a restatement.
See `docs/projects/logic-inst.md` (sections "wasm") for worked examples and
before/after comparisons.

* **Universe-free names.** The institutions of `ObsSemantics.inst` are the facade's
  `Silmaril.Inst.Institution₁` (`Inst.{1, 0, 0, 0, 0}`), and their logic graphs are the facade's
  `Silmaril.Inst.LogicGraph₁` (`LogicGraph.{0, 0, 1, 0, 0, 0, 0}`, the type of
  `GraphSpec.toLogicGraph` for a graph of `Institution₁`s indexed by a `Type`).
* **Satisfaction notation.** The canonical `β ⊨ s` of the facade (class
  `Silmaril.Inst.Satisfies`, scoped in `Silmaril.Inst`): the observational semantics at a signature
  are an instance (`ObsSemantics.instSatisfies`), rooms already are (`Satisfies.room`). The
  instance *is* the facade's satisfaction (`ObsSemantics.sat_iff_ofObs`, `Iff.rfl`), and the
  `@[simp]` lemma `ObsSemantics.sat_def` unfolds it.
* **One name per builder.** The comorphism of a translation is `Comorphism.ofObs T` (=
  `T.coHom`); the facade builder `Comorphism.ofTranslation` gives it back
  (`Translation.ofTranslation_eq_ofObs`, `rfl`). The morphism over `𝟭` is `Morphism.ofObs T`
  (= `T.toHom`). For a model-expansive translation they are `ExpTranslation.comorphism` and
  `ExpTranslation.morphism`.
* **Model-expansive translations** `ExpTranslation F A B`: a translation bundled with the
  surjectivity of its semantic maps. Its comorphism is model-expansive, its morphism is sound,
  and borrowing (`entails_iff`, `valid_iff`) needs no extra hypothesis. Builders:
  `ExpTranslation.id`, `ExpTranslation.ofProg` (an exact change of programs) and
  `ExpTranslation.ofSemEquiv` (an equivalence of semantic objects).
* **Transfer lemmas.** `simp` normal form is `S.Sat A β s` (`sat_def` unfolds `⊨`); the
  satisfaction conditions `ObsSemantics.sat_map_iff` and `Translation.sat_sen_iff` become
  `@[simp]`, with `⊨` forms `sat_map_iff'`, `Translation.sat_sen_iff'` for rewriting; the
  structure lemmas `coHom_Φ`, `coHom_ρ_app`, `corridor_sen`, `corridor_mod`, `inst_I_obj`,
  `room_Sat` are `@[simp]`.
* **Equivalences.** The identity comorphism of `Institution.ofObs S` is the comorphism of the
  identity equivalence (`ofObs_id_eq_ofIso`). `ExpTranslation.id` is *not* the identity
  comorphism: it rewrites an equation `a ≐ b` into `a ⊑ b ∧ b ⊑ a`
  (`ExpTranslation.id_sen_eq`); it agrees with the identity on satisfaction
  (`ExpTranslation.id_sat_iff`).
* **Logic graphs.** `LogicGraph.FlatRoom`, `pathSig`, `pathSen` name the parts of the
  Grothendieck institution of a logic graph that silmaril's `entails_lift_path_iff` spells
  out; `LogicGraph.AllExpansive` says every comorphism edge is model-expansive, and
  `AllExpansive.entails_path_iff` is borrowing along every path in one line.
* **Typed graph builder** `ObsGraph Iface`: nodes with observational semantics over one
  interface category, comorphism edges given by model-expansive translations and morphism
  edges given by model-expansive translations read backwards. `ObsGraph.graph` is the
  silmaril logic graph; `pathModelExpansive`, `entails_path_iff` and `proj_sound` come for
  free. `ObsGraph.inst` is the facade institution of a node, `ObsGraph.coEdge` the facade
  `CoEdge` of an edge, and `ObsGraph.toSpec` presents a list of edges as a facade
  `GraphSpec` whose edges are all model-expansive (`ObsGraph.toSpec_allModelExpansive`).
-/

namespace Silmaril.Wasm.Institution

open CategoryTheory Silmaril.Logic.Institution

/-! ## Satisfaction notation

`β ⊨ s` is the canonical notation of the facade (class `Silmaril.Inst.Satisfies`, scoped in
`Silmaril.Inst`). Rooms are instances in the facade (`Satisfies.room`); here the observational
semantics at a signature become one. -/

open scoped Silmaril.Inst

universe u v w m₁ m₂ u₁ v₁

namespace ObsSemantics

variable {Iface : Type} [Category.{0} Iface] (S : ObsSemantics Iface)

/-- Observational semantics: `β ⊨ s` is the facade satisfaction of `Institution.ofObs S`,
that is `S.Sat A β s`. -/
instance instSatisfies (A : Sig Iface) : Silmaril.Inst.Satisfies (S.Model A) (S.Sen A) :=
  ⟨fun β s => Silmaril.Inst.Institution.Sat (Silmaril.Inst.Institution.ofObs S) (S := A) β s⟩

@[simp] theorem sat_def {A : Sig Iface} (β : S.Model A) (s : S.Sen A) :
    β ⊨ s ↔ S.Sat A β s := Iff.rfl

/-- **`⊨` is the facade's satisfaction** of `Institution.ofObs S`. -/
theorem sat_iff_ofObs {A : Sig Iface} (β : S.Model A) (s : S.Sen A) :
    β ⊨ s ↔ β ⊨[Silmaril.Inst.Institution.ofObs S] s := Iff.rfl

open scoped Silmaril.Inst in
/-- The identity comorphism of `Institution.ofObs S` is the comorphism of the identity
equivalence of its room functor. -/
theorem ofObs_id_eq_ofIso :
    𝟙ᶜ (Silmaril.Inst.Institution.ofObs S) = Silmaril.Inst.Comorphism.ofIso (Iso.refl S.institution) :=
  Inst.CoHom.ext rfl (by
    simp [Silmaril.Inst.Comorphism.ofIso, Silmaril.Inst.Comorphism.id, Inst.CoHom.id]
    rfl)

/-- The institution of `S` at a signature is its room. -/
@[simp] theorem inst_I_obj (A : Sig Iface) : S.inst.I.obj A = S.room A := rfl

/-- The satisfaction of the room of `S` is `S.Sat`. -/
@[simp] theorem room_Sat (A : Sig Iface) : (S.room A).Sat = S.Sat A := rfl

/-- The sentences of the room of `S` are `S.Sen`. -/
@[simp] theorem room_Sen (A : Sig Iface) : (S.room A).Sen = S.Sen A := rfl

/-- The signature morphisms of `S.inst` act on sentences by `Sen.map`. -/
@[simp] theorem inst_I_map_sen {A B : Sig Iface} (f : A ⟶ B) (s : S.Sen A) :
    (S.inst.I.map f).sen s = s.map f := rfl

attribute [simp] sat_map_iff Translation.sat_sen_iff

/-- The satisfaction condition of `S.inst`, in `⊨` form. -/
theorem sat_map_iff' {A B : Sig Iface} (f : A ⟶ B) (β : S.Model B) (s : S.Sen A) :
    β ⊨ s.map f ↔ (S.reduct f).obj β ⊨ s :=
  S.sat_map_iff f β s

/-! ## Translations: consistent names and transfer lemmas -/

variable {I J : Type} [Category.{0} I] [Category.{0} J] {F : I ⥤ J}
  {A : ObsSemantics I} {B : ObsSemantics J}

/-- Naturality of the model translation of a translation, as an equation of functors. -/
theorem Translation.modFun_nat (T : Translation F A B) {K₁ K₂ : Sig I} (f : K₁ ⟶ K₂) :
    T.modFun K₂ ⋙ A.reduct f = B.reduct ((Sig.map F).map f) ⋙ T.modFun K₁ :=
  Functor.ext (fun β => funext fun x => (T.sem_restrict f.sub (β (f.ren x))).symm)
    (fun _ _ _ => rfl)

/-- The facade builder `Comorphism.ofTranslation`, fed with the sentence translation, the model
translation, the satisfaction condition and the two naturality equations of a translation, gives
back its comorphism `Comorphism.ofObs T` (that is, `T.coHom`). -/
theorem Translation.ofTranslation_eq_ofObs (T : Translation F A B) :
    Silmaril.Inst.Comorphism.ofTranslation (Sig.map F) (fun _ s => T.sen s) T.modFun
      (fun K β s => T.sat_sen_iff K β s) (fun f s => T.sen_map f s) (fun f => T.modFun_nat f) =
      Silmaril.Inst.Comorphism.ofObs T :=
  rfl

@[simp] theorem Translation.coHom_Φ (T : Translation F A B) : T.coHom.Φ = Sig.map F := rfl

@[simp] theorem Translation.coHom_ρ_app (T : Translation F A B) (K : Sig I) :
    T.coHom.ρ.app K = T.corridor K := rfl

@[simp] theorem Translation.corridor_sen (T : Translation F A B) (K : Sig I) :
    (T.corridor K).sen = T.sen := rfl

@[simp] theorem Translation.corridor_mod (T : Translation F A B) (K : Sig I) :
    (T.corridor K).mod = T.modFun K := rfl

@[simp] theorem Translation.modFun_obj (T : Translation F A B) (K : Sig I)
    (β : B.Model ((Sig.map F).obj K)) (x : K.V) : (T.modFun K).obj β x = T.sem K.iface (β x) :=
  rfl

/-- **The satisfaction condition of a translation**, in `⊨` form. (`simp` unfolds `⊨` by
`sat_def` and then uses `Translation.sat_sen_iff`, which is a `simp` lemma.) -/
theorem Translation.sat_sen_iff' (T : Translation F A B) {K : Sig I}
    (β : B.Model ((Sig.map F).obj K)) (s : A.Sen K) :
    β ⊨ T.sen s ↔ (T.modFun K).obj β ⊨ s :=
  T.sat_sen_iff K β s

/-! ## Model-expansive translations -/

/-- A **model-expansive translation**: a translation whose semantic maps are surjective. Its
comorphism is model-expansive and its morphism (over `𝟭`) is sound. -/
structure ExpTranslation (F : I ⥤ J) (A : ObsSemantics I) (B : ObsSemantics J)
    extends Translation F A B where
  /-- Every semantic map is surjective. -/
  sem_surjective : ∀ X, Function.Surjective (sem X)

namespace ExpTranslation

variable (T : ExpTranslation F A B)

/-- The comorphism, `Comorphism.ofObs` of the translation. -/
noncomputable abbrev comorphism :
    Silmaril.Inst.Comorphism (Silmaril.Inst.Institution.ofObs A) (Silmaril.Inst.Institution.ofObs B) :=
  Silmaril.Inst.Comorphism.ofObs T.toTranslation

/-- The source sentence translation. -/
abbrev sen {K : Sig I} (s : A.Sen K) : B.Sen ((Sig.map F).obj K) := T.toTranslation.sen s

theorem modelExpansive : T.comorphism.ModelExpansive :=
  T.toTranslation.coHom_modelExpansive T.sem_surjective

/-- Borrowing: consequence in `A` is consequence of the translated sentences in `B`. -/
theorem entails_iff (K : Sig I) (Γ : Set (A.Sen K)) (s : A.Sen K) :
    (A.room K).Entails Γ s ↔ (B.room ((Sig.map F).obj K)).Entails (T.sen '' Γ) (T.sen s) :=
  T.toTranslation.entails_iff T.sem_surjective K Γ s

/-- Validity is preserved and reflected. -/
theorem valid_iff {K : Sig I} (s : A.Sen K) : A.Valid s ↔ B.Valid (T.sen s) :=
  T.toTranslation.valid_iff T.sem_surjective s

/-- The satisfaction condition, in `⊨` form. -/
theorem sat_iff {K : Sig I} (β : B.Model ((Sig.map F).obj K)) (s : A.Sen K) :
    β ⊨ T.sen s ↔ (T.modFun K).obj β ⊨ s :=
  T.toTranslation.sat_sen_iff K β s

/-- Borrowing validity, in the facade's terms: the facade lemma `Comorphism.valid_iff` with
the model-expansiveness of `T` supplied. -/
theorem valid_iff' {K : Sig I} (s : A.Sen K) :
    (Silmaril.Inst.Institution.ofObs A).Valid s ↔
      (Silmaril.Inst.Institution.ofObs B).Valid (T.comorphism.sen K s) :=
  T.comorphism.valid_iff T.modelExpansive s

/-- Borrowing consequence, in the facade's terms (`Comorphism.entails_iff`). -/
theorem entails_iff' (K : Sig I) (Γ : Set (A.Sen K)) (s : A.Sen K) :
    (Silmaril.Inst.Institution.ofObs A).Entails Γ s ↔
      (Silmaril.Inst.Institution.ofObs B).Entails (T.comorphism.sen K '' Γ) (T.comorphism.sen K s) :=
  T.comorphism.entails_iff T.modelExpansive K Γ s

end ExpTranslation

namespace ExpTranslation

variable {A B : ObsSemantics I}

/-- The institution morphism `B → A` of a model-expansive translation over `𝟭`. -/
noncomputable abbrev morphism (T : ExpTranslation (𝟭 I) A B) :
    Silmaril.Inst.Morphism (Silmaril.Inst.Institution.ofObs B) (Silmaril.Inst.Institution.ofObs A) :=
  Silmaril.Inst.Morphism.ofObs T.toTranslation

theorem sound (T : ExpTranslation (𝟭 I) A B) : T.morphism.Sound :=
  T.toTranslation.toHom_sound T.sem_surjective

/-- **The identity translation** of an observational semantics. -/
def id (S : ObsSemantics I) : ExpTranslation (𝟭 I) S S where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog p := p
  sem_den _ _ := rfl
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .le t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := Iff.rfl
  sem_surjective _ a := ⟨a, rfl⟩

/-- The identity translation is the identity on terms. -/
theorem id_term (S : ObsSemantics I) {V : Type} (t : S.Tm V) :
    (ExpTranslation.id S).toTranslation.term t = t := by
  induction t with
  | var x => rfl
  | prog p => rfl
  | app o t ih => exact congrArg (Term.app o) ih

/-- **`ExpTranslation.id` is not syntactically the identity comorphism**: its formula
translation replaces every equation `a ≐ b` by `a ⊑ b ∧ b ⊑ a` (`Formula.bindLe` with plain
refinement atoms). So its comorphism is not `𝟙ᶜ` (nor `Comorphism.ofIso`); it agrees with the
identity on satisfaction (`ExpTranslation.sat_iff`). -/
theorem id_sen_φ (S : ObsSemantics I) {K : Sig I} (s : S.Sen K) :
    ((ExpTranslation.id S).sen s).φ = s.φ.bindLe (fun t u => .le t u) := by
  show s.φ.bindLe (fun t u => .le ((ExpTranslation.id S).toTranslation.term t)
    ((ExpTranslation.id S).toTranslation.term u)) = _
  simp only [id_term]

end ExpTranslation

/-! ### Exact change of programs -/

/-- `S` with its programs and denotations replaced (the rest unchanged). -/
def withProg (S : ObsSemantics I) (Prog : Type) (den : ∀ X : I, Prog → S.Sem X) :
    ObsSemantics I :=
  { S with Prog := Prog, den := den }

/-- **An exact behaviour translation**: a map of programs that preserves denotations is a
model-expansive translation, the identity on interfaces, semantic objects, operators and
refinement atoms. -/
def ExpTranslation.ofProg (S : ObsSemantics I) {P P' : Type} {d : ∀ X : I, P → S.Sem X}
    {d' : ∀ X : I, P' → S.Sem X} (g : P → P') (hg : ∀ X p, d' X (g p) = d X p) :
    ExpTranslation (𝟭 I) (S.withProg P d) (S.withProg P' d') where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog := g
  sem_den X p := hg X p
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .le t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := Iff.rfl
  sem_surjective _ a := ⟨a, rfl⟩

/-! ### From an equivalence of semantic objects -/

/-- **A translation from an equivalence of semantic objects**: a natural equivalence
`B.Sem (F X) ≃ A.Sem X` that matches denotations, operators and refinement. -/
def ExpTranslation.ofSemEquiv (e : ∀ X : I, B.Sem (F.obj X) ≃ A.Sem X)
    (he : ∀ {X Y : I} (f : X ⟶ Y) (b : B.Sem (F.obj Y)),
      e X (B.restrict (F.map f) b) = A.restrict f (e Y b))
    (prog : A.Prog → B.Prog) (hden : ∀ X p, e X (B.den (F.obj X) (prog p)) = A.den X p)
    (op : A.Op → B.Op) (hop : ∀ X o b, e X (B.op (F.obj X) (op o) b) = A.op X o (e X b))
    (hle : ∀ X a b, B.Le (F.obj X) a b ↔ A.Le X (e X a) (e X b)) : ExpTranslation F A B where
  sem X := e X
  sem_restrict := he
  prog := prog
  sem_den := hden
  op := op
  sem_op := hop
  atom t u := .le t u
  atom_mapVars _ _ _ := rfl
  atom_holds X _ _ _ _ := hle X _ _
  sem_surjective X := (e X).surjective

end ObsSemantics

/-! ## Logic graphs: named parts and borrowing along every path -/

namespace LogicGraph

universe u₀ v₀

variable (L : Silmaril.Logic.Institution.LogicGraph.{u₀, v₀, u₁, v₁, w, m₁, m₂})

/-- The signatures of a node, as seen by the Grothendieck institution. -/
abbrev Sign (a : L.Idx) := (IndexedCoInst.inst L.indexed (L.pt a)).Sign

/-- The room of the Grothendieck institution at the signature `(a, S)`. -/
abbrev FlatRoom (a : L.Idx) (S : Sign L a) :=
  (IndexedCoInst.flat L.indexed).obj (IndexedCoInst.mkSig L.indexed (L.pt a) S)

/-- The signature reached from `S` along a path. -/
abbrev pathSig {a b : L.Idx} (p : Quiver.Path a b) (S : Sign L a) : Sign L b :=
  (IndexedCoInst.coHom L.indexed (L.pathHom p)).Φ.obj S

/-- Sentence translation along a path, in the Grothendieck institution. -/
abbrev pathSen {a b : L.Idx} (p : Quiver.Path a b) (S : Sign L a) :
    (FlatRoom L a S).Sen → (FlatRoom L b (pathSig L p S)).Sen :=
  ((IndexedCoInst.flat L.indexed).map (IndexedCoInst.lift L.indexed (L.pathHom p) S)).sen

/-- Every comorphism edge of the graph is model-expansive. (A structure, so that dot notation
`h.path`, `h.entails_path_iff` works.) -/
structure AllExpansive : Prop where
  /-- Each edge is model-expansive. -/
  edge : ∀ {a b : L.Logics} (e : L.Comor a b), (L.comor e).ModelExpansive

variable {L}

/-- If every edge is model-expansive, so is every path. -/
theorem AllExpansive.path (h : AllExpansive L) :
    ∀ {a b : L.Idx} (p : Quiver.Path a b), L.PathModelExpansive p
  | _, _, .nil => trivial
  | _, _, .cons p e => ⟨h.path p, h.edge e⟩

/-- **Borrowing along every path** of a graph whose edges are model-expansive. -/
theorem AllExpansive.entails_path_iff (h : AllExpansive L) {a b : L.Idx}
    (p : Quiver.Path a b) (S : Sign L a) (Γ : Set (FlatRoom L a S).Sen)
    (φ : (FlatRoom L a S).Sen) :
    (FlatRoom L a S).Entails Γ φ ↔
      (FlatRoom L b (pathSig L p S)).Entails (pathSen L p S '' Γ) (pathSen L p S φ) :=
  L.entails_lift_path_iff p (h.path p) S Γ φ

end LogicGraph

/-! ## A typed logic-graph builder -/

/-- **A logic graph of observational semantics** over one interface category: nodes with
their semantics, comorphism edges given by model-expansive translations along interface
endofunctors (by default the identity), and morphism edges `a → b` given by model-expansive
translations `b → a` over the identity, read as institution morphisms. -/
structure ObsGraph (Iface : Type) [Category.{0} Iface] where
  /-- The logics. -/
  Node : Type
  /-- The observational semantics of a logic. -/
  sem : Node → ObsSemantics Iface
  /-- Comorphism edges. -/
  Edge : Node → Node → Type
  /-- The interface functor of an edge. -/
  F : ∀ {a b : Node}, Edge a b → Iface ⥤ Iface := fun _ => 𝟭 Iface
  /-- The translation of an edge. -/
  edge : ∀ {a b : Node} (e : Edge a b), ObsSemantics.ExpTranslation (F e) (sem a) (sem b)
  /-- Morphism (projection) edges. -/
  Proj : Node → Node → Type := fun _ _ => PEmpty
  /-- The translation read backwards by a projection edge. -/
  proj : ∀ {a b : Node}, Proj a b → ObsSemantics.ExpTranslation (𝟭 Iface) (sem b) (sem a)

namespace ObsGraph

variable {Iface : Type} [Category.{0} Iface] (G : ObsGraph Iface)

/-- The facade institution of a node. -/
abbrev inst (a : G.Node) : Silmaril.Inst.Institution₁ := Silmaril.Inst.Institution.ofObs (G.sem a)

/-- **The silmaril logic graph** of an `ObsGraph`. -/
noncomputable def graph : Silmaril.Inst.LogicGraph₁ where
  Logics := G.Node
  inst := G.inst
  Comor := G.Edge
  comor e := (G.edge e).comorphism
  Mor := G.Proj
  mor e := (G.proj e).morphism

theorem allExpansive : LogicGraph.AllExpansive G.graph := ⟨fun e => (G.edge e).modelExpansive⟩

/-- Every path of the graph is model-expansive. -/
theorem pathModelExpansive {a b : G.graph.Idx} (p : Quiver.Path a b) :
    G.graph.PathModelExpansive p :=
  G.allExpansive.path p

/-- Every projection edge is a sound institution morphism. -/
theorem proj_sound {a b : G.Node} (e : G.Proj a b) : (G.graph.mor e).Sound :=
  (G.proj e).sound

/-- **Heterogeneous borrowing** along every path of the graph. -/
theorem entails_path_iff {a b : G.graph.Idx} (p : Quiver.Path a b)
    (S : LogicGraph.Sign G.graph a) (Γ : Set (LogicGraph.FlatRoom G.graph a S).Sen)
    (φ : (LogicGraph.FlatRoom G.graph a S).Sen) :
    (LogicGraph.FlatRoom G.graph a S).Entails Γ φ ↔
      (LogicGraph.FlatRoom G.graph b (LogicGraph.pathSig G.graph p S)).Entails
        (LogicGraph.pathSen G.graph p S '' Γ) (LogicGraph.pathSen G.graph p S φ) :=
  G.allExpansive.entails_path_iff p S Γ φ

/-! ### Finite presentations as facade `GraphSpec`s -/

/-- The facade comorphism edge of an edge of `G`. -/
noncomputable def coEdge {a b : G.Node} (e : G.Edge a b) : Silmaril.Inst.CoEdge G.inst :=
  ⟨a, b, (G.edge e).comorphism⟩

/-- The facade morphism edge of a projection edge of `G`. -/
noncomputable def morEdge {a b : G.Node} (e : G.Proj a b) : Silmaril.Inst.MorEdge G.inst :=
  ⟨a, b, (G.proj e).morphism⟩

/-- **A list of edges of `G` as a facade `GraphSpec`**: the comorphism edges `es` and the
projection edges `ps`, each typed against its endpoints. -/
noncomputable def toSpec (es : List ((a : G.Node) × (b : G.Node) × G.Edge a b))
    (ps : List ((a : G.Node) × (b : G.Node) × G.Proj a b) := []) :
    Silmaril.Inst.GraphSpec G.inst where
  comors := es.map fun e => G.coEdge e.2.2
  mors := ps.map fun e => G.morEdge e.2.2

/-- Every listed edge of `toSpec` is model-expansive: `ExpTranslation` carries the proof. -/
theorem toSpec_allModelExpansive (es : List ((a : G.Node) × (b : G.Node) × G.Edge a b))
    (ps : List ((a : G.Node) × (b : G.Node) × G.Proj a b)) :
    (G.toSpec es ps).AllModelExpansive := by
  intro e he
  obtain ⟨⟨a, b, e'⟩, -, rfl⟩ := List.mem_map.1 he
  exact (G.edge e').modelExpansive

/-- Every path of the graph of `toSpec` is model-expansive, so heterogeneous borrowing
applies along it (`LogicGraph.entails_lift_path_iff`). -/
theorem toSpec_pathModelExpansive (es : List ((a : G.Node) × (b : G.Node) × G.Edge a b))
    (ps : List ((a : G.Node) × (b : G.Node) × G.Proj a b)) {a b : G.Node}
    (p : Quiver.Path (V := (G.toSpec es ps).toLogicGraph.Idx) a b) :
    (G.toSpec es ps).toLogicGraph.PathModelExpansive p :=
  (G.toSpec es ps).pathModelExpansive (G.toSpec_allModelExpansive es ps) p

/-- The listed edges of `toSpec` act by the comorphisms of their translations. -/
theorem toSpec_comor (es : List ((a : G.Node) × (b : G.Node) × G.Edge a b))
    (ps : List ((a : G.Node) × (b : G.Node) × G.Proj a b))
    (i : Fin (G.toSpec es ps).comors.length) :
    (G.toSpec es ps).toLogicGraph.comor ((G.toSpec es ps).coEdge i) =
      (G.toSpec es ps).comors[i].comor :=
  rfl

end ObsGraph

end Silmaril.Wasm.Institution
