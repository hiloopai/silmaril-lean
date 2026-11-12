module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.PermFree
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Basic

/-!
# The SpecTec specification institution with renamings of type, function and relation names

A signature morphism `σ : SigHomP Σ Σ'` is a permutation `π` of identifiers fixing `"_"` that
sends the declared types, functions and relation declarations of `Σ` to declared ones of `Σ'`
(`rnDecl`). It renames the whole syntax (`rnS`), so it renames type and function names as well
as relation names, together with variables.

* `rnSen σ`: translation of `Σ`-sentences (`inSig_rn`, using `ruleFuns_rnRule`).
* `reductP σ M`: the reduct, with the evaluator environment renamed back (`rnEnv π.symm`)
  and the interpretation read back (`rnI π.symm`), restricted to `Σ`.
* `satisfactionP`: the satisfaction condition, from the equivariance of satisfaction
  (`sat_rnS_iff`) and its locality (`sat_restrict_iff`). It holds at every equivariant conclusion
  reading (`Equivariant`), in particular at `decl`.
* `functorP`, `instP`: the institution.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim

/-! ## Signature morphisms -/

/-- **A renaming of identifiers** between signatures: a permutation fixing `"_"` that sends
declared types, functions and relations to declared ones. -/
@[ext] structure SigHomP (S T : Sig) where
  /-- The permutation of identifiers. -/
  π : Equiv.Perm IL.Id
  /-- The wildcard is fixed. -/
  fix : π "_" = "_"
  /-- Declared types go to declared types. -/
  typs : ∀ x ∈ S.typs, π x ∈ T.typs
  /-- Declared functions go to declared functions. -/
  funs : ∀ f ∈ S.funs, π f ∈ T.funs
  /-- Declared relations go to declared relations. -/
  rels : ∀ d ∈ S.rels, rnDecl π d ∈ T.rels

/-- The identity renaming. -/
def SigHomP.id (S : Sig) : SigHomP S S :=
  ⟨Equiv.refl _, rfl, fun _ h => h, fun _ h => h, fun d h => by
    have hd : rnDecl (Equiv.refl IL.Id) d = d := by
      obtain ⟨x, ps, op, t⟩ := d
      simp only [rnDecl, Equiv.coe_refl, rnParams_id, rnTyp_id, id_eq]
    rw [hd]
    exact h⟩

theorem rnDecl_comp (f g : IL.Id → IL.Id) (d : RelDecl) : rnDecl g (rnDecl f d) = rnDecl (g ∘ f) d := by
  simp only [rnDecl, rnParams_comp, rnTyp_comp, Function.comp_apply]

/-- Composition of renamings. -/
def SigHomP.comp {S T U : Sig} (σ : SigHomP S T) (τ : SigHomP T U) : SigHomP S U where
  π := σ.π.trans τ.π
  fix := by simp only [Equiv.trans_apply, σ.fix, τ.fix]
  typs x hx := τ.typs _ (σ.typs x hx)
  funs f hf := τ.funs _ (σ.funs f hf)
  rels d hd := by
    have h := τ.rels _ (σ.rels d hd)
    rwa [rnDecl_comp] at h

/-- IL signatures, with renamings of identifiers as morphisms. -/
structure SigP where
  /-- The signature. -/
  sig : Sig

instance : Category SigP where
  Hom S T := SigHomP S.sig T.sig
  id S := SigHomP.id S.sig
  comp σ τ := σ.comp τ
  id_comp _ := SigHomP.ext (Equiv.ext fun _ => rfl)
  comp_id _ := SigHomP.ext (Equiv.ext fun _ => rfl)
  assoc _ _ _ := SigHomP.ext (Equiv.ext fun _ => rfl)

/-! ## Sentences -/

theorem premSyms_rnPrem (π : Equiv.Perm IL.Id) :
    ∀ pr : Prem, premSyms (rnPrem π pr) = (premSyms pr).map fun s => (π s.1, s.2)
  | .rulePr _ _ _ _ => rfl
  | .ifPr _ => rfl
  | .letPr _ _ => rfl
  | .elsePr => rfl
  | .iterPr pr _ => premSyms_rnPrem π pr

theorem ruleSyms_rnRule (π : Equiv.Perm IL.Id) (r : Rule) :
    ruleSyms (rnRule π r) = (ruleSyms r).map fun s => (π s.1, s.2) := by
  obtain ⟨nm, qs, op, e, prems⟩ := r
  simp only [rnRule, ruleSyms, rnPrems_eq, List.flatMap_map, premSyms_rnPrem, List.map_flatMap]

/-- A renaming sends declared relation symbols to declared relation symbols. -/
theorem SigHomP.relSyms {S T : Sig} (σ : SigHomP S T) {x : IL.Id} {op : MixopS}
    (hs : (x, op) ∈ S.relSyms) : (σ.π x, op) ∈ T.relSyms := by
  obtain ⟨d, hd, he⟩ := hs
  obtain ⟨y, ps, op', t⟩ := d
  have h : y = x ∧ op' = op := by simpa only [RelDecl.sym, Prod.mk.injEq] using he
  refine ⟨rnDecl σ.π (y, ps, op', t), σ.rels _ hd, ?_⟩
  rw [← h.1, ← h.2]
  rfl

/-- A renamed `Σ`-sentence is a `Σ'`-sentence. -/
theorem inSig_rn {S T : Sig} (σ : SigHomP S T) :
    ∀ {φ : SSen}, φ.InSig S → (rnS σ.π φ).InSig T
  | .rule d r, ⟨hd, hr, hf⟩ => by
    refine ⟨σ.rels d hd, ?_, ?_⟩
    · intro s hs
      rw [ruleSyms_rnRule] at hs
      obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.1 hs
      exact σ.relSyms (hr s₀ hs₀)
    · intro g hg
      rw [ruleFuns_rnRule σ.fix] at hg
      obtain ⟨g₀, hg₀, rfl⟩ := Finset.mem_map.1 hg
      exact σ.funs g₀ (hf g₀ hg₀)
  | .fact _ _ _ _, h => σ.relSyms h

/-- **Translation of sentences along a renaming of identifiers.** -/
def rnSen {S T : Sig} (σ : SigHomP S T) (φ : Sen S) : Sen T := ⟨rnS σ.π φ.1, inSig_rn σ φ.2⟩

/-! ## Models -/

/-- **The reduct along a renaming of identifiers**: the evaluator environment and the
interpretation renamed back, the interpretation restricted to `Σ`. -/
def reductP {S T : Sig} (σ : SigHomP S T) (M : Model T) : Model S where
  env := rnEnv σ.π.symm M.env
  D := restrictI S.relSyms (rnI σ.π.symm M.D)
  typs_def x hx := by
    have h := Env.findTyp?_rn (π := σ.π.symm) M.env (σ.π x)
    rw [Equiv.symm_apply_apply] at h
    rw [h, Option.isSome_map]
    exact M.typs_def _ (σ.typs x hx)
  funs_def f hf := by
    have h := Env.findDef?_rn (π := σ.π.symm) M.env (σ.π f)
    rw [Equiv.symm_apply_apply] at h
    rw [h, Option.isSome_map]
    exact M.funs_def _ (σ.funs f hf)
  vanish _ _ _ _ hd := hd.1

/-- **The satisfaction condition along a renaming of identifiers**, at every equivariant
conclusion reading. -/
theorem satisfactionP {alts : Reading} (ha : Equivariant alts) {S T : Sig} (σ : SigHomP S T)
    (M : Model T) (φ : Sen S) :
    (rnSen σ φ).1.Sat alts M.env M.D ↔ φ.1.Sat alts (reductP σ M).env (reductP σ M).D := by
  have he : rnEnv σ.π (rnEnv σ.π.symm M.env) = M.env := by
    simpa only [Equiv.symm_symm] using rnEnv_symm σ.π.symm M.env
  have hD : rnI σ.π (rnI σ.π.symm M.D) = M.D := by
    simpa only [Equiv.symm_symm] using rnI_symm σ.π.symm M.D
  have h := sat_rnS_iff σ.fix ha (rnEnv σ.π.symm M.env) (rnI σ.π.symm M.D) φ.1
  rw [he, hD] at h
  exact h.trans (sat_restrict_iff φ.2.symsIn).symm

/-! ## Functoriality -/

theorem rnS_comp (f g : IL.Id → IL.Id) (φ : SSen) : rnS g (rnS f φ) = rnS (g ∘ f) φ := by
  cases φ with
  | rule d r => simp only [rnS, rnDecl_comp, rnRule_comp]
  | fact x op args v =>
    have h : (args.map (rnArgV f)).map (rnArgV g) = args.map (rnArgV (g ∘ f)) := by
      rw [List.map_map]
      congr 1
      funext a
      exact rnArgV_comp f g a
    simp only [rnS, h, Function.comp_apply]

theorem rnS_id (φ : SSen) : rnS id φ = φ := by
  cases φ with
  | rule d r =>
    obtain ⟨x, ps, op, t⟩ := d
    simp only [rnS, rnDecl, rnParams_id, rnTyp_id, rnRule_id, id_eq]
  | fact x op args v =>
    have h : args.map (rnArgV id) = args := by
      conv_rhs => rw [← List.map_id args]
      congr 1
      funext a
      exact rnArgV_id a
    simp only [rnS, h, id_eq]

theorem rnTypDef_comp (f g : IL.Id → IL.Id) (d : TypDef) :
    rnTypDef g (rnTypDef f d) = rnTypDef (g ∘ f) d := by
  simp only [rnTypDef, rnParams_comp, rnInsts_comp]

theorem rnDefDef_comp (f g : IL.Id → IL.Id) (d : DefDef) :
    rnDefDef g (rnDefDef f d) = rnDefDef (g ∘ f) d := by
  simp only [rnDefDef, rnParams_comp, rnTyp_comp, rnClauses_comp]

theorem rnRelDef_comp (f g : IL.Id → IL.Id) (d : RelDef) :
    rnRelDef g (rnRelDef f d) = rnRelDef (g ∘ f) d := by
  simp only [rnRelDef, rnParams_comp, rnTyp_comp, rnRules_comp]

theorem rnGramDef_comp (f g : IL.Id → IL.Id) (d : GramDef) :
    rnGramDef g (rnGramDef f d) = rnGramDef (g ∘ f) d := by
  simp only [rnGramDef, rnParams_comp, rnTyp_comp, rnProds_comp]

/-- Renaming a map twice. -/
theorem rnMap_comp' {α : Type} (f g : IL.Id → IL.Id) (h : (IL.Id → IL.Id) → α → α)
    (hh : ∀ a, h g (h f a) = h (g ∘ f) a) (m : Map α) :
    rnMap g (h g) (rnMap f (h f) m) = rnMap (g ∘ f) (h (g ∘ f)) m := by
  rw [rnMap_comp]
  congr 1
  funext a
  exact hh a

/-- Renaming an environment twice is renaming it along the composite. -/
theorem rnEnv_comp (π₁ π₂ : Equiv.Perm IL.Id) (env : Env) :
    rnEnv π₁ (rnEnv π₂ env) = rnEnv (π₂.trans π₁) env := by
  obtain ⟨vars, typs, defs, rels, grams, ⟨b⟩⟩ := env
  have hb : (fun (x : IL.Id) (ws : List ArgV) =>
        b (π₂.symm (π₁.symm x)) ((ws.map (rnArgV π₁.symm)).map (rnArgV π₂.symm))) =
      fun x ws => b ((π₂.trans π₁).symm x) (ws.map (rnArgV (π₂.trans π₁).symm)) := by
    funext x ws
    simp only [List.map_map, Function.comp_def, rnArgV_comp]
    rfl
  simp only [rnEnv, Equiv.coe_trans, rnMap_comp' π₂ π₁ (fun f => rnTyp f) (rnTyp_comp π₂ π₁),
    rnMap_comp' π₂ π₁ (fun f => rnTypDef f) (rnTypDef_comp π₂ π₁),
    rnMap_comp' π₂ π₁ (fun f => rnDefDef f) (rnDefDef_comp π₂ π₁),
    rnMap_comp' π₂ π₁ (fun f => rnRelDef f) (rnRelDef_comp π₂ π₁),
    rnMap_comp' π₂ π₁ (fun f => rnGramDef f) (rnGramDef_comp π₂ π₁), hb]

theorem rnEnv_refl (env : Env) : rnEnv (Equiv.refl _) env = env := by
  have h := rnEnv_symm (Equiv.refl IL.Id) env
  have h' : rnEnv (Equiv.refl IL.Id) (rnEnv (Equiv.refl IL.Id) env) =
      rnEnv (Equiv.refl IL.Id) env := by
    rw [rnEnv_comp]
    rfl
  rwa [Equiv.refl_symm, h'] at h

/-- The reduct along the identity renaming. -/
theorem reductP_id {S : Sig} (M : Model S) : reductP (SigHomP.id S) M = M := by
  refine Model.ext' (rnEnv_refl M.env) ?_
  funext x op avs w
  have ha : avs.map (rnArgV (Equiv.refl IL.Id)) = avs := by
    conv_rhs => rw [← List.map_id avs]
    congr 1
    funext a
    exact rnArgV_id a
  simp only [reductP, restrictI, rnI, SigHomP.id, Equiv.symm_symm, Equiv.refl_apply, ha]
  exact propext ⟨fun hd => hd.2, fun hd => ⟨M.vanish x op avs w hd, hd⟩⟩

/-- The reduct along a composite renaming. -/
theorem reductP_comp {S T U : Sig} (σ : SigHomP S T) (τ : SigHomP T U) (M : Model U) :
    reductP (σ.comp τ) M = reductP σ (reductP τ M) := by
  refine Model.ext' ?_ ?_
  · show rnEnv (σ.π.trans τ.π).symm M.env = rnEnv σ.π.symm (rnEnv τ.π.symm M.env)
    rw [rnEnv_comp]
    rfl
  · funext x op avs w
    have ha : (avs.map (rnArgV σ.π)).map (rnArgV τ.π) = avs.map (rnArgV (σ.π.trans τ.π)) := by
      simp only [List.map_map, Function.comp_def, rnArgV_comp]
      rfl
    show ((x, op) ∈ S.relSyms ∧ M.D (τ.π (σ.π x)) op (avs.map (rnArgV (σ.π.trans τ.π))) w) =
      ((x, op) ∈ S.relSyms ∧ (σ.π x, op) ∈ T.relSyms ∧
        M.D (τ.π (σ.π x)) op ((avs.map (rnArgV σ.π)).map (rnArgV τ.π)) w)
    rw [ha]
    exact propext ⟨fun hd => ⟨hd.1, σ.relSyms hd.1, hd.2⟩, fun hd => ⟨hd.1, hd.2.2⟩⟩

/-! ## The institution -/

/-- The corridor of a renaming: sentences renamed, models reduced. -/
def corridorP {alts : Reading} (ha : Equivariant alts) {S T : Sig} (σ : SigHomP S T) :
    room alts S ⟶ room alts T :=
  ⟨rnSen σ, Discrete.functor (fun M => Discrete.mk (reductP σ M)),
    fun M φ => satisfactionP ha σ M.as φ⟩

/-- **The SpecTec specification institution with renamings of identifiers** (types, functions,
relations), as a functor into rooms, at an equivariant conclusion reading. -/
def functorP {alts : Reading} (ha : Equivariant alts) : SigP ⥤ Room.{0, 0, 0} where
  obj S := room alts S.sig
  map σ := corridorP ha σ
  map_id S := by
    apply Corridor.ext
    · funext φ
      exact Subtype.ext (rnS_id φ.1)
    · change Discrete.functor (fun M : Model S.sig => Discrete.mk (reductP (SigHomP.id S.sig) M)) =
        𝟭 _
      exact CategoryTheory.Functor.ext (fun M => by rw [Discrete.functor_obj, reductP_id]; rfl)
        (fun _ _ _ => Subsingleton.elim _ _)
  map_comp {S T U} σ τ := by
    apply Corridor.ext
    · funext φ
      exact Subtype.ext (rnS_comp σ.π τ.π φ.1).symm
    · change Discrete.functor (fun M : Model U.sig => Discrete.mk (reductP (σ.comp τ) M)) =
        Discrete.functor (fun M : Model U.sig => Discrete.mk (reductP τ M)) ⋙
          Discrete.functor (fun M : Model T.sig => Discrete.mk (reductP σ M))
      exact CategoryTheory.Functor.ext (fun M => congrArg Discrete.mk (reductP_comp σ τ M.as))
        (fun _ _ _ => Subsingleton.elim _ _)

/-- **The SpecTec specification institution with renamings of type, function and relation
names**, at an equivariant conclusion reading. -/
def instP {alts : Reading} (ha : Equivariant alts) : Silmaril.Logic.Institution.Inst.{0, 0, 0, 0, 0} := ⟨SigP, functorP ha⟩

/-- The institution at the declarative reading. -/
def instPDecl : Silmaril.Logic.Institution.Inst.{0, 0, 0, 0, 0} := instP decl_equivariant

/-! ## Inclusions -/

/-- An inclusion of signatures is the identity renaming. -/
def SigHomP.ofLe {S T : Sig} (h : S ≤ T) : SigHomP S T :=
  ⟨Equiv.refl _, rfl, fun _ hx => h.1 hx, fun _ hf => h.2.1 hf, fun d hd => by
    have hd' : rnDecl (Equiv.refl IL.Id) d = d := by
      obtain ⟨x, ps, op, t⟩ := d
      simp only [rnDecl, Equiv.coe_refl, rnParams_id, rnTyp_id, id_eq]
    rw [hd']
    exact h.2.2 hd⟩

/-- Along an inclusion, the reduct is the reduct of `Institution.inst`. -/
theorem reductP_ofLe {S T : Sig} (h : S ≤ T) (M : Model T) :
    reductP (SigHomP.ofLe h) M = M.reduct h := by
  refine Model.ext' (rnEnv_refl M.env) ?_
  funext x op avs w
  have ha : avs.map (rnArgV (Equiv.refl IL.Id)) = avs := by
    conv_rhs => rw [← List.map_id avs]
    congr 1
    funext a
    exact rnArgV_id a
  simp only [reductP, Model.reduct, restrictI, rnI, SigHomP.ofLe, Equiv.symm_symm, Equiv.refl_apply,
    ha]

/-- Along an inclusion, sentence translation is the identity. -/
theorem rnSen_ofLe {S T : Sig} (h : S ≤ T) (φ : Sen S) : (rnSen (SigHomP.ofLe h) φ).1 = φ.1 :=
  rnS_id φ.1

end Silmaril.Wasm.SpecTec.Institution.Perm
