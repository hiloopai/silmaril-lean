module

public import Silmaril.Wasm.SpecTec.Institution.Defs

/-!
# The institution of SpecTec specifications: construction and canonical models

* `premW_mono`, `ruleBodyA_mono`: premises and rule bodies only read the relations they mention.
* `sat_restrict_iff`: satisfaction is invariant under restricting the interpretation to a set of
  symbols containing the sentence's; hence `satisfaction` (the satisfaction condition).
* `functor`, `inst`: the institution, a functor `Sig ⥤ Room`, at each conclusion reading.
* `canon`, `canonB`: `DDerives env O` and `DDerivesB env O` as models of `sigOf env`;
  `canon_sat`, `canonB_sat`: they satisfy `theoryOf env`; `canon_least`, `canonB_least`: at
  `O = noElse` they are below every interpretation satisfying `theoryOf env` with evaluator
  `env`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

/-! ## Locality -/

/-- A premise reads only the relations it mentions, and `otherwise` monotonically. -/
theorem premW_mono {env : Env} {D D' : Interp} {els els' : Prop} {ρ : VarEnv} {pr : Prem}
    (h : PremW env D els ρ pr)
    (hD : ∀ x op avs w, (x, op) ∈ premSyms pr → D x op avs w → D' x op avs w)
    (he : els → els') : PremW env D' els' ρ pr := by
  revert hD he
  induction h with
  | ifPr h => exact fun _ _ => .ifPr h
  | elsePr h => exact fun _ he => .elsePr (he h)
  | letPr h₁ h₂ => exact fun _ _ => .letPr h₁ h₂
  | rulePr ha hv hd => exact fun hD _ => .rulePr ha hv (hD _ _ _ _ (List.mem_singleton_self _) hd)
  | iterOptNone hd hne hall => exact fun _ _ => .iterOptNone hd hne hall
  | iterOptSome hd hne hs _ ih => exact fun hD he => .iterOptSome hd hne hs (ih hD he)
  | iterList hit hd hne hl hlen _ ih =>
      exact fun hD he => .iterList hit hd hne hl hlen (fun r hr => ih r hr hD he)
  | iterListN hd hn hk hl hlen _ ih =>
      exact fun hD he => .iterListN hd hn hk hl hlen (fun r hr => ih r hr hD he)

/-- A rule body reads only the relations its premises mention. -/
theorem ruleBodyA_mono {alts : Reading} {env : Env} {D D' : Interp} {els els' : Prop}
    {ps : List Param} {args : List ArgV} {op : MixopS} {r : Rule} {v : Value}
    (h : RuleBodyA alts env D els ps args op r v)
    (hD : ∀ x op avs w, (x, op) ∈ ruleSyms r → D x op avs w → D' x op avs w)
    (he : els → els') : RuleBodyA alts env D' els' ps args op r v := by
  cases r with
  | ruleD nm qs op' e prems =>
    obtain ⟨e', halt, hop, ρ₀, σ, hps, hq, hev, hp⟩ := h
    have hsyms : ∀ pr ∈ prems, ∀ s ∈ premSyms pr, s ∈ ruleSyms (.ruleD nm qs op' e prems) :=
      fun pr hpr s hs => List.mem_flatMap.2 ⟨pr, hpr, hs⟩
    exact ⟨e', halt, hop, ρ₀, σ, hps, hq, hev, fun pr hpr =>
      premW_mono (hp pr hpr) (fun x o avs w hs => hD x o avs w (hsyms pr hpr _ hs)) he⟩

/-- The symbols of a sentence lie in `R`. -/
def SSen.SymsIn (R : Set RelSym) : SSen → Prop
  | .rule d r => d.sym ∈ R ∧ ∀ s ∈ ruleSyms r, s ∈ R
  | .fact x op _ _ => (x, op) ∈ R

theorem SSen.InSig.symsIn {S : Sig} : ∀ {φ : SSen}, φ.InSig S → φ.SymsIn S.relSyms
  | .rule _ _, h => ⟨Set.mem_image_of_mem _ h.1, h.2.1⟩
  | .fact _ _ _ _, h => h

/-- **Locality of satisfaction**: restricting the interpretation to symbols containing the
sentence's does not change satisfaction. -/
theorem sat_restrict_iff {alts : Reading} {env : Env} {D : Interp} {R : Set RelSym} :
    ∀ {φ : SSen}, φ.SymsIn R → (φ.Sat alts env (restrictI R D) ↔ φ.Sat alts env D)
  | .rule d r, ⟨hd, hr⟩ => by
    constructor
    · intro h args v hb
      have hb' : RuleBodyA alts env (restrictI R D) False d.params args d.op r v :=
        ruleBodyA_mono hb (fun x o _ _ hs hx => ⟨hr (x, o) hs, hx⟩) id
      exact (h args v hb').2
    · intro h args v hb
      have hb' : RuleBodyA alts env D False d.params args d.op r v :=
        ruleBodyA_mono hb (fun _ _ _ _ _ hx => hx.2) id
      exact ⟨hd, h args v hb'⟩
  | .fact _ _ _ _, hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- **The satisfaction condition** along an inclusion `Σ ≤ Σ'`. -/
theorem satisfaction (alts : Reading) {S T : Sig} (h : S ≤ T) (M : Model T) (φ : Sen S) :
    φ.1.Sat alts M.env M.D ↔ φ.1.Sat alts (M.reduct h).env (M.reduct h).D :=
  (sat_restrict_iff φ.2.symsIn).symm

/-! ## Functoriality of the reduct -/

theorem Model.ext' {S : Sig} {M N : Model S} (h₁ : M.env = N.env) (h₂ : M.D = N.D) :
    M = N := by
  cases M
  cases N
  cases h₁
  cases h₂
  rfl

theorem Model.reduct_self {S : Sig} (h : S ≤ S) (M : Model S) : M.reduct h = M := by
  refine Model.ext' (show (M.reduct h).env = M.env from rfl) ?_
  funext x op avs w
  exact propext ⟨fun hd => hd.2, fun hd => ⟨M.vanish x op avs w hd, hd⟩⟩

theorem Model.reduct_reduct {S T U : Sig} (h : S ≤ T) (k : T ≤ U) (M : Model U) :
    M.reduct (h.trans k) = (M.reduct k).reduct h := by
  refine Model.ext' (show (M.reduct (h.trans k)).env = ((M.reduct k).reduct h).env from rfl) ?_
  funext x op avs w
  exact propext ⟨fun hd => ⟨hd.1, Sig.relSyms_mono h hd.1, hd.2⟩, fun hd => ⟨hd.1, hd.2.2⟩⟩

/-! ## The institution -/

/-- The room of a signature: its sentences, its (discrete) models and satisfaction. -/
def room (alts : Reading) (S : Sig) : Room.{0, 0, 0} :=
  ⟨Sen S, Cat.of (Discrete (Model S)), fun M φ => φ.1.Sat alts M.as.env M.as.D⟩

/-- The corridor of an inclusion: sentences unchanged, models reduced. -/
def corridor (alts : Reading) {S T : Sig} (h : S ≤ T) : room alts S ⟶ room alts T :=
  ⟨fun φ => ⟨φ.1, φ.2.mono h⟩, Discrete.functor (fun M => Discrete.mk (M.reduct h)),
    fun M φ => satisfaction alts h M.as φ⟩

/-- **The institution of SpecTec specifications** at a conclusion reading, as a functor into
rooms. -/
def functor (alts : Reading) : Sig ⥤ Room.{0, 0, 0} where
  obj := room alts
  map f := corridor alts (leOfHom f)
  map_id S := by
    apply Corridor.ext
    · rfl
    · change Discrete.functor (fun M : Model S => Discrete.mk (M.reduct le_rfl)) = 𝟭 _
      exact CategoryTheory.Functor.ext (fun M => by rw [Discrete.functor_obj, Model.reduct_self]; rfl)
        (fun _ _ _ => Subsingleton.elim _ _)
  map_comp {S T U} f g := by
    apply Corridor.ext
    · rfl
    · change Discrete.functor (fun M : Model U => Discrete.mk (M.reduct (leOfHom (f ≫ g)))) =
        Discrete.functor (fun M : Model U => Discrete.mk (M.reduct (leOfHom g))) ⋙
          Discrete.functor (fun M : Model T => Discrete.mk (M.reduct (leOfHom f)))
      exact CategoryTheory.Functor.ext (fun M => congrArg Discrete.mk (Model.reduct_reduct (leOfHom f) (leOfHom g) M.as))
        (fun _ _ _ => Subsingleton.elim _ _)

/-- **The institution of SpecTec specifications** at a conclusion reading. -/
def inst (alts : Reading) : Silmaril.Logic.Institution.Inst.{0, 0, 0, 0, 0} := ⟨Sig, functor alts⟩

/-! ## Canonical models -/

/-- Premises read by `DDerives env O` are `DPrem` premises. -/
theorem premW_toDPrem {env : Env} {O : ElseI} {els els' : Prop} {ρ : VarEnv} {pr : Prem}
    (h : PremW env (DDerives env O) els ρ pr) (he : els → els') : DPrem env O els' ρ pr := by
  revert he
  induction h with
  | ifPr h => exact fun _ => .ifPr h
  | elsePr h => exact fun he => .elsePr (he h)
  | letPr h₁ h₂ => exact fun _ => .letPr h₁ h₂
  | rulePr ha hv hd => exact fun _ => .rulePr ha hv hd
  | iterOptNone hd hne hall => exact fun _ => .iterOptNone hd hne hall
  | iterOptSome hd hne hs _ ih => exact fun he => .iterOptSome hd hne hs (ih he)
  | iterList hit hd hne hl hlen _ ih =>
      exact fun he => .iterList hit hd hne hl hlen (fun r hr => ih r hr he)
  | iterListN hd hn hk hl hlen _ ih =>
      exact fun he => .iterListN hd hn hk hl hlen (fun r hr => ih r hr he)

/-- Premises read by `DDerivesB env O` are `DPremB` premises. -/
theorem premW_toDPremB {env : Env} {O : ElseI} {els els' : Prop} {ρ : VarEnv} {pr : Prem}
    (h : PremW env (DDerivesB env O) els ρ pr) (he : els → els') : DPremB env O els' ρ pr := by
  revert he
  induction h with
  | ifPr h => exact fun _ => .ifPr h
  | elsePr h => exact fun he => .elsePr (he h)
  | letPr h₁ h₂ => exact fun _ => .letPr h₁ h₂
  | rulePr ha hv hd => exact fun _ => .rulePr ha hv hd
  | iterOptNone hd hne hall => exact fun _ => .iterOptNone hd hne hall
  | iterOptSome hd hne hs _ ih => exact fun he => .iterOptSome hd hne hs (ih he)
  | iterList hit hd hne hl hlen _ ih =>
      exact fun he => .iterList hit hd hne hl hlen (fun r hr => ih r hr he)
  | iterListN hd hn hk hl hlen _ ih =>
      exact fun he => .iterListN hd hn hk hl hlen (fun r hr => ih r hr he)

/-- A relation that derives something is declared. -/
theorem dderives_declared {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {avs : List ArgV}
    {w : Value} (h : DDerives env O x op avs w) : (x, op) ∈ (sigOf env).relSyms := by
  cases h with
  | rule hrel _ _ _ _ _ => exact ⟨(x, _, op, _), ⟨_, hrel⟩, rfl⟩

/-- A relation that derives something under the backend reading is declared. -/
theorem dderivesB_declared {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {avs : List ArgV}
    {w : Value} (h : DDerivesB env O x op avs w) : (x, op) ∈ (sigOf env).relSyms := by
  cases h with
  | rule hrel _ _ _ _ _ _ => exact ⟨(x, _, op, _), ⟨_, hrel⟩, rfl⟩

/-- **The declarative canonical model** of a script: `DDerives env O`. -/
def canon (env : Env) (O : ElseI) : Model (sigOf env) where
  env := env
  D := DDerives env O
  typs_def _ h := h
  funs_def _ h := h
  vanish _ _ _ _ h := dderives_declared h

/-- **The backend canonical model** of a script: `DDerivesB env O`. -/
def canonB (env : Env) (O : ElseI) : Model (sigOf env) where
  env := env
  D := DDerivesB env O
  typs_def _ h := h
  funs_def _ h := h
  vanish _ _ _ _ h := dderivesB_declared h

/-- A theory rule is the `i`-th rule of its declaration. -/
theorem theoryOf_rule {env : Env} {φ : SSen} (h : φ ∈ theoryOf env) :
    ∃ (d : RelDecl) (rules : List Rule) (r : Rule) (i : Nat),
      env.findRel? d.1 = some (d.params, d.op, d.2.2.2, rules) ∧ rules[i]? = some r ∧
        φ = .rule d r := by
  obtain ⟨d, rules, r, hrel, hr, hφ⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
  exact ⟨d, rules, r, i, hrel, hi, hφ⟩

/-- **`DDerives env O` satisfies the theory of `env`**, at every `otherwise` reading `O`. -/
theorem canon_sat (env : Env) (O : ElseI) : SatTh decl env (DDerives env O) (theoryOf env) := by
  intro φ hφ
  obtain ⟨d, rules, r, i, hrel, hi, rfl⟩ := theoryOf_rule hφ
  cases r with
  | ruleD nm qs op' e prems =>
    rintro args v ⟨e', halt, hop, ρ₀, σ, hps, hq, hev, hp⟩
    have he' : e' = e := List.mem_singleton.1 halt
    have hi' : rules[i]? = some (.ruleD nm qs d.op e prems) := hop ▸ hi
    exact .rule hrel hi' hps hq (he' ▸ hev) (fun pr hpr => premW_toDPrem (hp pr hpr) False.elim)

/-- **`DDerivesB env O` satisfies the theory of `env`** at the backend reading, at every `O`. -/
theorem canonB_sat (env : Env) (O : ElseI) :
    SatTh backend env (DDerivesB env O) (theoryOf env) := by
  intro φ hφ
  obtain ⟨d, rules, r, i, hrel, hi, rfl⟩ := theoryOf_rule hφ
  cases r with
  | ruleD nm qs op' e prems =>
    rintro args v ⟨e', halt, hop, ρ₀, σ, hps, hq, hev, hp⟩
    have hi' : rules[i]? = some (.ruleD nm qs d.op e prems) := hop ▸ hi
    exact .rule hrel hi' halt hps hq hev (fun pr hpr => premW_toDPremB (hp pr hpr) False.elim)

/-- **Leastness, declarative**: every interpretation satisfying the theory of `env` (with
evaluator `env`) contains `DDerives env noElse`. -/
theorem canon_least {env : Env} {D : Interp} (hD : SatTh decl env D (theoryOf env)) :
    ∀ {x op args v}, DDerives env noElse x op args v → D x op args v := by
  intro x op args v h
  refine DDerives.rec (motive_1 := fun x op args v _ => D x op args v)
    (motive_2 := fun els ρ pr _ => (els → False) → PremW env D False ρ pr)
    ?_ (fun h _ => .ifPr h) (fun h hn => (hn h).elim) (fun h₁ h₂ _ => .letPr h₁ h₂)
    (fun ha hv _ ih _ => .rulePr ha hv ih) (fun hd hne hall _ => .iterOptNone hd hne hall)
    (fun hd hne hs _ ih hn => .iterOptSome hd hne hs (ih hn))
    (fun hit hd hne hl hlen _ ih hn => .iterList hit hd hne hl hlen (fun r hr => ih r hr hn))
    (fun hd hk hkv hl hlen _ ih hn => .iterListN hd hk hkv hl hlen (fun r hr => ih r hr hn)) h
  intro x op args v ps t rules i nm qs e prems ρ₀ σ hrel hrule hps hq he _ ih
  have hmem : SSen.rule (x, ps, op, t) (.ruleD nm qs op e prems) ∈ theoryOf env :=
    ⟨(x, ps, op, t), rules, _, hrel, List.mem_of_getElem? hrule, rfl⟩
  exact hD _ hmem args v ⟨e, List.mem_singleton_self _, rfl, ρ₀, σ, hps, hq, he,
    fun pr hpr => ih pr hpr id⟩

/-- **Leastness, backend**: every interpretation satisfying the theory of `env` at the backend
reading contains `DDerivesB env noElse`. -/
theorem canonB_least {env : Env} {D : Interp} (hD : SatTh backend env D (theoryOf env)) :
    ∀ {x op args v}, DDerivesB env noElse x op args v → D x op args v := by
  intro x op args v h
  refine DDerivesB.rec (motive_1 := fun x op args v _ => D x op args v)
    (motive_2 := fun els ρ pr _ => (els → False) → PremW env D False ρ pr)
    ?_ (fun h _ => .ifPr h) (fun h hn => (hn h).elim) (fun h₁ h₂ _ => .letPr h₁ h₂)
    (fun ha hv _ ih _ => .rulePr ha hv ih) (fun hd hne hall _ => .iterOptNone hd hne hall)
    (fun hd hne hs _ ih hn => .iterOptSome hd hne hs (ih hn))
    (fun hit hd hne hl hlen _ ih hn => .iterList hit hd hne hl hlen (fun r hr => ih r hr hn))
    (fun hd hk hkv hl hlen _ ih hn => .iterListN hd hk hkv hl hlen (fun r hr => ih r hr hn)) h
  intro x op args v ps t rules i nm qs e e' prems ρ₀ σ hrel hrule halt hps hq he _ ih
  have hmem : SSen.rule (x, ps, op, t) (.ruleD nm qs op e prems) ∈ theoryOf env :=
    ⟨(x, ps, op, t), rules, _, hrel, List.mem_of_getElem? hrule, rfl⟩
  exact hD _ hmem args v ⟨e', halt, rfl, ρ₀, σ, hps, hq, he, fun pr hpr => ih pr hpr id⟩

/-- `DDerives env noElse` is below `DDerives env O` for every `otherwise` reading `O`. -/
theorem dderives_noElse_le {env : Env} (O : ElseI) {x : IL.Id} {op : MixopS} {args : List ArgV}
    {v : Value} (h : DDerives env noElse x op args v) : DDerives env O x op args v :=
  canon_least (canon_sat env O) h

/-- `DDerivesB env noElse` is below `DDerivesB env O` for every `otherwise` reading `O`. -/
theorem dderivesB_noElse_le {env : Env} (O : ElseI) {x : IL.Id} {op : MixopS}
    {args : List ArgV} {v : Value} (h : DDerivesB env noElse x op args v) :
    DDerivesB env O x op args v :=
  canonB_least (canonB_sat env O) h

/-- The backend canonical model's step facts are `Round6.Reading.SStepB`. -/
theorem sat_stepFact_canonB (alts : Reading) (env : Env) (c c' : Value) :
    (stepFact c c').Sat alts (canonB env (otherwiseB env)).env (canonB env (otherwiseB env)).D ↔
      Round6.Reading.SStepB env c c' :=
  Iff.rfl

/-! ## Versions -/

/-- **Partial theory morphisms between versions**: a model of the later theory, reduced to any
smaller signature, satisfies every retained rule of the earlier theory that is a sentence there. -/
theorem retained_sat_reduct (alts : Reading) {env₁ env₂ : Env} {S T : Sig} (h : S ≤ T)
    (M : Model T) (hM : SatTh alts M.env M.D (theoryOf env₂)) (φ : Sen S)
    (hφ : φ.1 ∈ retained env₁ env₂) :
    φ.1.Sat alts (M.reduct h).env (M.reduct h).D :=
  (satisfaction alts h M φ).1 (hM _ hφ.2)

/-- A theory is preserved along `env₁ → env₂` exactly when nothing is dropped. -/
theorem theoryOf_subset_iff (env₁ env₂ : Env) :
    theoryOf env₁ ⊆ theoryOf env₂ ↔ dropped env₁ env₂ = ∅ :=
  Set.sdiff_eq_empty.symm

end Silmaril.Wasm.SpecTec.Institution
