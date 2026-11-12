module

public import Silmaril.Wasm.SpecTec.Institution.Amalg.Defs
public import Silmaril.Wasm.SpecTec.Institution.Thms
public import Silmaril.Wasm.SpecTec.GrammarInst.Thms

/-!
# Whole SpecTec scripts with a shared evaluator: construction and least model

* `asatisfaction`, `afunctor`, `ainst`: the amalgamated institution, a functor `ASig ⥤ Room`, at
  each conclusion reading.
* `asat_prods_iff`: a model satisfies the productions of `wholeTheory env` at the evaluator `env`
  exactly when its nonterminal interpretation satisfies the grammar theory
  `GrammarInst.scriptAxioms env`. The grammar half of the amalgamation is the grammar institution,
  read at the model's evaluator.
* `canonW`, `canonW_sat`: `DDerivesB env O` with the least model of `gramOf env` satisfies the
  whole theory; `canonW_least_rel`, `canonW_least_gram`: at `O = noElse` it lies below every
  model with evaluator `env`.
* `entailsAt_fact_iff`, `entailsAt_derives_iff`: relation facts are `DDerivesB env noElse`, and
  derivability assertions are `gramRelSup env`, as consequences of the whole theory at `env`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril (EncRel)
open Silmaril.SpecTec.Grammar (Bytes)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB)

/-! ## The institution -/

theorem ASen.InSig.mono {S T : ASig} (h : S ≤ T) : ∀ {ψ : ASen}, ψ.InSig S → ψ.InSig T
  | .rel _, hψ => SSen.InSig.mono h.1 hψ
  | .prod _ _ _, hψ => h.2 hψ
  | .derives _ _ _ _, _ => trivial

/-- **The satisfaction condition** of the amalgamated institution along an inclusion. -/
theorem asatisfaction (alts : Reading) {S T : ASig} (h : S ≤ T) (M : AModel T) (ψ : ASenOf S) :
    ψ.1.Sat alts M.base.env M.base.D M.I ↔
      ψ.1.Sat alts (M.reduct h).base.env (M.reduct h).base.D (M.reduct h).I := by
  obtain ⟨ψ, hψ⟩ := ψ
  cases ψ with
  | rel φ => exact satisfaction alts h.1 M.base ⟨φ, hψ⟩
  | prod => exact Iff.rfl
  | derives => exact Iff.rfl

theorem AModel.reduct_self {S : ASig} (h : S ≤ S) (M : AModel S) : M.reduct h = M := by
  have hb : M.base.reduct h.1 = M.base := Model.reduct_self h.1 M.base
  exact AModel.ext hb rfl

theorem AModel.reduct_reduct {S T U : ASig} (h : S ≤ T) (k : T ≤ U) (M : AModel U) :
    M.reduct (h.trans k) = (M.reduct k).reduct h := by
  have hb : M.base.reduct (h.trans k).1 = (M.base.reduct k.1).reduct h.1 :=
    Model.reduct_reduct h.1 k.1 M.base
  exact AModel.ext hb rfl

/-- The room of a whole-script signature. -/
def aroom (alts : Reading) (S : ASig) : Room.{0, 0, 0} :=
  ⟨ASenOf S, Cat.of (Discrete (AModel S)), fun M ψ => ψ.1.Sat alts M.as.base.env M.as.base.D M.as.I⟩

/-- The corridor of an inclusion. -/
def acorridor (alts : Reading) {S T : ASig} (h : S ≤ T) : aroom alts S ⟶ aroom alts T :=
  ⟨fun ψ => ⟨ψ.1, ψ.2.mono h⟩, Discrete.functor (fun M => Discrete.mk (M.reduct h)),
    fun M ψ => asatisfaction alts h M.as ψ⟩

/-- **The amalgamated institution of whole SpecTec scripts**, as a functor into rooms. -/
def afunctor (alts : Reading) : ASig ⥤ Room.{0, 0, 0} where
  obj := aroom alts
  map f := acorridor alts (leOfHom f)
  map_id S := by
    apply Corridor.ext
    · rfl
    · change Discrete.functor (fun M : AModel S => Discrete.mk (M.reduct le_rfl)) = 𝟭 _
      exact CategoryTheory.Functor.ext
        (fun M => by rw [Discrete.functor_obj, AModel.reduct_self]; rfl)
        (fun _ _ _ => Subsingleton.elim _ _)
  map_comp {S T U} f g := by
    apply Corridor.ext
    · rfl
    · change Discrete.functor (fun M : AModel U => Discrete.mk (M.reduct (leOfHom (f ≫ g)))) =
        Discrete.functor (fun M : AModel U => Discrete.mk (M.reduct (leOfHom g))) ⋙
          Discrete.functor (fun M : AModel T => Discrete.mk (M.reduct (leOfHom f)))
      exact CategoryTheory.Functor.ext
        (fun M => congrArg Discrete.mk (AModel.reduct_reduct (leOfHom f) (leOfHom g) M.as))
        (fun _ _ _ => Subsingleton.elim _ _)

/-- **The amalgamated institution of whole SpecTec scripts** at a conclusion reading. -/
def ainst (alts : Reading) : Silmaril.Logic.Institution.Inst.{0, 0, 0, 0, 0} :=
  ⟨ASig, afunctor alts⟩

/-! ## The grammar half is the grammar institution at the model's evaluator -/

/-- **The productions of the whole theory, at evaluator `env`, are the grammar theory of `env`.** -/
theorem asat_prods_iff (alts : Reading) (env : Env) (D : Interp) (I : NT → EncRel Bytes Act) :
    (∀ x ps t prods p, env.findGram? x = some (ps, t, prods) → p ∈ prods →
        (ASen.prod x ps p).Sat alts env D I) ↔
      ∀ φ ∈ GrammarInst.scriptAxioms env, φ.Holds actAlg I := by
  constructor
  · rintro h φ ⟨n, g, hg, rfl⟩
    obtain ⟨x, args⟩ := n
    have hg' : g ∈ prodsOf env env (x, args) := hg
    unfold prodsOf at hg'
    split at hg'
    · exact absurd hg' List.not_mem_nil
    · rename_i ps t prods hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg'
      exact h x ps t prods p hx hp args
  · intro h x ps t prods p hx hp args
    have hmem : transProd env ps args p ∈ prodsOf env env (x, args) := by
      show transProd env ps args p ∈ (match env.findGram? x with
        | none => [] | some (ps, _, prods) => prods.map (transProd env ps args))
      rw [hx]
      exact List.mem_map_of_mem hp
    exact h _ ⟨(x, args), _, hmem, rfl⟩

/-- A model satisfies the whole theory exactly when its relational part satisfies the theory of
relations and its nonterminal part satisfies the grammar theory, both at the evaluator `env`. -/
theorem asatTh_wholeTheory_iff (alts : Reading) (env : Env) (D : Interp)
    (I : NT → EncRel Bytes Act) :
    ASatTh alts env D I (wholeTheory env) ↔
      SatTh alts env D (theoryOf env) ∧ ∀ φ ∈ GrammarInst.scriptAxioms env, φ.Holds actAlg I := by
  rw [← asat_prods_iff alts env D I]
  constructor
  · intro h
    exact ⟨fun φ hφ => h (.rel φ) (Or.inl ⟨φ, hφ, rfl⟩),
      fun x ps t prods p hx hp => h _ (Or.inr ⟨x, ps, t, prods, p, hx, hp, rfl⟩)⟩
  · rintro ⟨hr, hg⟩ ψ (⟨φ, hφ, rfl⟩ | ⟨x, ps, t, prods, p, hx, hp, rfl⟩)
    · exact hr φ hφ
    · exact hg x ps t prods p hx hp

/-! ## The canonical model -/

/-- The productions of a script's grammars are declared grammar names. -/
theorem wholeTheory_inSig {env : Env} {x : IL.Id} {ps : List Param} {p : IL.Prod}
    (h : ASen.prod x ps p ∈ wholeTheory env) : (ASen.prod x ps p).InSig (asigOf env) := by
  rcases h with ⟨_, _, h⟩ | ⟨x', ps', t, prods, p', hx, _, h⟩
  · exact ASen.noConfusion h
  · have hx' : x = x' := (ASen.prod.inj h).1
    show (env.findGram? x).isSome
    rw [hx', hx]
    rfl

/-- **The canonical model of a whole script**: `DDerivesB env O` for relations and the least model
of `gramOf env` for nonterminals, with the one evaluator `env`. -/
def canonW (env : Env) (O : ElseI) : AModel (asigOf env) :=
  ⟨canonB env O, (GrammarInst.leastModel (gramOf env)).rel⟩

/-- **The canonical model satisfies the whole theory**, at every `otherwise` reading. -/
theorem canonW_sat (env : Env) (O : ElseI) :
    ASatTh backend env (canonW env O).base.D (canonW env O).I (wholeTheory env) :=
  (asatTh_wholeTheory_iff backend env _ _).2
    ⟨canonB_sat env O, fun φ hφ => GrammarInst.scriptLeastModel_sat env φ hφ⟩

/-- **Leastness, relations**: every model of the whole theory with evaluator `env` contains
`DDerivesB env noElse`. -/
theorem canonW_least_rel {env : Env} {D : Interp} {I : NT → EncRel Bytes Act}
    (h : ASatTh backend env D I (wholeTheory env)) {x op args v}
    (hd : DDerivesB env noElse x op args v) : D x op args v :=
  canonB_least ((asatTh_wholeTheory_iff backend env D I).1 h).1 hd

/-- **Leastness, grammars**: every model of the whole theory with evaluator `env` contains the
least model of `gramOf env`. -/
theorem canonW_least_gram {env : Env} {D : Interp} {I : NT → EncRel Bytes Act}
    (h : ASatTh backend env D I (wholeTheory env)) (n : NT) :
    (GrammarInst.leastModel (gramOf env)).rel n ≤ I n :=
  GrammarInst.scriptLeastModel_le env ⟨I⟩ ((asatTh_wholeTheory_iff backend env D I).1 h).2 n

/-- **Relation facts are consequences**: `DDerivesB env noElse` is what the whole theory entails
at the evaluator `env`. -/
theorem entailsAt_fact_iff (env : Env) (x : IL.Id) (op : MixopS) (args : List ArgV) (v : Value) :
    EntailsAt backend env (wholeTheory env) (.rel (.fact x op args v)) ↔
      DDerivesB env noElse x op args v :=
  ⟨fun h => h _ _ (canonW_sat env noElse), fun hd _ _ hM => canonW_least_rel hM hd⟩

/-- **Derivability is consequence**: `gramRelSup env` is what the whole theory entails at the
evaluator `env`, with relations present. -/
theorem entailsAt_derives_iff (env : Env) (ρ : VarEnv) (g : IL.Sym) (bs : Bytes) (v : Value) :
    EntailsAt backend env (wholeTheory env) (.derives g ρ bs v) ↔ gramRelSup env ρ g bs v := by
  rw [GrammarInst.gramRelSup_iff_entails]
  constructor
  · intro h M hM
    have hc := h (DDerivesB env noElse) M.rel
      ((asatTh_wholeTheory_iff backend env _ _).2 ⟨canonB_sat env noElse, hM⟩)
    exact hc
  · intro h D I hM
    exact h ⟨I⟩ ((asatTh_wholeTheory_iff backend env D I).1 hM).2

end Silmaril.Wasm.SpecTec.Institution
