module

public import Silmaril.Wasm.SpecTec.Institution.Rename.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Basic

/-!
# The SpecTec specification institution with renamings: the satisfaction condition

* `premW_renameP_iff`, `ruleBodyA_rename_iff`, `sat_renameS_iff`: renaming the relation names of
  a premise, rule body or sentence is the same as reading the interpretation through the
  renaming. No injectivity is needed.
* `ruleFuns_renameRule`: renaming relation names does not change the functions a rule calls.
* `renameSen`: translation of `Σ`-sentences along a renaming; `satisfactionR`: the satisfaction
  condition.
* `functorR`, `instR`: the institution with renamings; `reductR_ofLe`: along an inclusion the
  reduct is the reduct of `Institution.inst`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim

variable {f : IL.Id → IL.Id}

/-! ## Renaming premises and rule bodies -/

/-- A premise read through `f` is the renamed premise. -/
theorem premW_renameP_of {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {pr : Prem}
    (h : PremW env (renameI f D) els ρ pr) : PremW env D els ρ (renameP f pr) := by
  induction h with
  | ifPr h => exact .ifPr h
  | elsePr h => exact .elsePr h
  | letPr h₁ h₂ => exact .letPr h₁ h₂
  | rulePr ha hv hd => exact .rulePr ha hv hd
  | iterOptNone hd hne hall => exact .iterOptNone hd hne hall
  | iterOptSome hd hne hs _ ih => exact .iterOptSome hd hne hs ih
  | iterList hit hd hne hl hlen _ ih => exact .iterList hit hd hne hl hlen ih
  | iterListN hd hn hk hl hlen _ ih => exact .iterListN hd hn hk hl hlen ih

/-- Inverting `renameP` at a test. -/
theorem renameP_eq_ifPr {pr : Prem} {e : Exp} (h : renameP f pr = .ifPr e) : pr = .ifPr e := by
  cases pr <;> simp_all [renameP]

/-- Inverting `renameP` at `otherwise`. -/
theorem renameP_eq_elsePr {pr : Prem} (h : renameP f pr = .elsePr) : pr = .elsePr := by
  cases pr <;> simp_all [renameP]

/-- Inverting `renameP` at a binding. -/
theorem renameP_eq_letPr {pr : Prem} {e₁ e₂ : Exp} (h : renameP f pr = .letPr e₁ e₂) :
    pr = .letPr e₁ e₂ := by
  cases pr <;> simp_all [renameP]

/-- Inverting `renameP` at a relation premise. -/
theorem renameP_eq_rulePr {pr : Prem} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
    (h : renameP f pr = .rulePr x args op e) : ∃ y, pr = .rulePr y args op e ∧ f y = x := by
  cases pr <;> simp_all [renameP]

/-- Inverting `renameP` at an iteration. -/
theorem renameP_eq_iterPr {pr q : Prem} {it : IterExp} (h : renameP f pr = .iterPr q it) :
    ∃ p, pr = .iterPr p it ∧ renameP f p = q := by
  cases pr <;> simp_all [renameP]

/-- A renamed premise is the premise read through `f`. -/
theorem premW_of_renameP {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {q : Prem}
    (h : PremW env D els ρ q) : ∀ pr, renameP f pr = q → PremW env (renameI f D) els ρ pr := by
  induction h with
  | ifPr h => exact fun pr hpr => (renameP_eq_ifPr hpr) ▸ .ifPr h
  | elsePr h => exact fun pr hpr => (renameP_eq_elsePr hpr) ▸ .elsePr h
  | letPr h₁ h₂ => exact fun pr hpr => (renameP_eq_letPr hpr) ▸ .letPr h₁ h₂
  | rulePr ha hv hd =>
    intro pr hpr
    obtain ⟨y, hy, hfy⟩ := renameP_eq_rulePr hpr
    exact hy ▸ .rulePr ha hv (show D (f y) _ _ _ from hfy ▸ hd)
  | iterOptNone hd hne hall =>
    intro pr hpr
    obtain ⟨p, hp, -⟩ := renameP_eq_iterPr hpr
    exact hp ▸ .iterOptNone hd hne hall
  | iterOptSome hd hne hs _ ih =>
    intro pr hpr
    obtain ⟨p, hp, hq⟩ := renameP_eq_iterPr hpr
    exact hp ▸ .iterOptSome hd hne hs (ih p hq)
  | iterList hit hd hne hl hlen _ ih =>
    intro pr hpr
    obtain ⟨p, hp, hq⟩ := renameP_eq_iterPr hpr
    exact hp ▸ .iterList hit hd hne hl hlen (fun r hr => ih r hr p hq)
  | iterListN hd hn hk hl hlen _ ih =>
    intro pr hpr
    obtain ⟨p, hp, hq⟩ := renameP_eq_iterPr hpr
    exact hp ▸ .iterListN hd hn hk hl hlen (fun r hr => ih r hr p hq)

/-- **Renaming a premise is reading it through the renaming.** -/
theorem premW_renameP_iff {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {pr : Prem} :
    PremW env D els ρ (renameP f pr) ↔ PremW env (renameI f D) els ρ pr :=
  ⟨fun h => premW_of_renameP h pr rfl, premW_renameP_of⟩

/-- **Renaming a rule body is reading it through the renaming.** -/
theorem ruleBodyA_rename_iff {alts : Reading} {env : Env} {D : Interp} {els : Prop}
    {ps : List Param} {args : List ArgV} {op : MixopS} {r : Rule} {v : Value} :
    RuleBodyA alts env D els ps args op (renameRule f r) v ↔
      RuleBodyA alts env (renameI f D) els ps args op r v := by
  cases r with
  | ruleD nm qs op' e prems =>
    simp only [renameRule, RuleBodyA, RuleBody, List.forall_mem_map, premW_renameP_iff]

/-- **Renaming a sentence is reading the interpretation through the renaming.** -/
theorem sat_renameS_iff {alts : Reading} {env : Env} {D : Interp} :
    ∀ {φ : SSen}, (renameS f φ).Sat alts env D ↔ φ.Sat alts env (renameI f D)
  | .rule d r => by
    simp only [renameS, SSen.Sat]
    exact forall_congr' fun args => forall_congr' fun v => imp_congr_left ruleBodyA_rename_iff
  | .fact _ _ _ _ => Iff.rfl

/-! ## Renaming and signatures -/

/-- The relation symbols of a renamed premise are the renamed symbols. -/
theorem premSyms_renameP : ∀ pr : Prem, premSyms (renameP f pr) = (premSyms pr).map (renameSym f)
  | .rulePr _ _ _ _ => rfl
  | .ifPr _ => rfl
  | .letPr _ _ => rfl
  | .elsePr => rfl
  | .iterPr pr _ => premSyms_renameP pr

/-- The relation symbols of a renamed rule are the renamed symbols. -/
theorem ruleSyms_renameRule (r : Rule) : ruleSyms (renameRule f r) = (ruleSyms r).map (renameSym f) := by
  cases r with
  | ruleD nm qs op e prems =>
    simp only [renameRule, ruleSyms, List.flatMap_map, premSyms_renameP, List.map_flatMap]

/-- `boundPrem` is empty. -/
theorem boundPrem_eq_empty (pr : Prem) : boundPrem pr = Sets.empty := by
  cases pr <;> rfl

/-- Renaming relation names does not change the functions a premise calls. -/
theorem freePrem_renameP_defid :
    ∀ pr : Prem, (freePrem (renameP f pr)).defid = (freePrem pr).defid
  | .rulePr _ _ _ _ => by simp [renameP, freePrem, Sets.union, freeRelid, Sets.empty]
  | .ifPr _ => rfl
  | .letPr _ _ => rfl
  | .elsePr => rfl
  | .iterPr pr _ => by simp [renameP, freePrem, Sets.union, Sets.diff, freePrem_renameP_defid pr]

/-- Renaming relation names does not change the functions premises call. -/
theorem freePrems_renameP_defid :
    ∀ prs : List Prem, (freePrems (prs.map (renameP f))).defid = (freePrems prs).defid
  | [] => rfl
  | pr :: prs => by
    simp only [List.map_cons, freePrems, Sets.union, Sets.diff, boundPrem_eq_empty,
      freePrem_renameP_defid pr, freePrems_renameP_defid prs]

/-- **Renaming relation names does not change the functions a rule calls.** -/
theorem ruleFuns_renameRule (r : Rule) : ruleFuns (renameRule f r) = ruleFuns r := by
  cases r with
  | ruleD nm qs op e prems =>
    simp only [ruleFuns, renameRule, freeRule, Sets.union, Sets.diff, freePrems_renameP_defid prems]

/-- A renaming sends declared relation symbols to declared relation symbols. -/
theorem SigHom.relSyms {S T : Sig} (σ : SigHom S T) {s : RelSym} (hs : s ∈ S.relSyms) :
    renameSym σ.f s ∈ T.relSyms := by
  obtain ⟨d, hd, rfl⟩ := hs
  exact ⟨d.rename σ.f, σ.rels d hd, rfl⟩

/-- A renamed `Σ`-sentence is a `Σ'`-sentence. -/
theorem SSen.InSig.rename {S T : Sig} (σ : SigHom S T) :
    ∀ {φ : SSen}, φ.InSig S → (renameS σ.f φ).InSig T
  | .rule d r, ⟨hd, hr, hf⟩ => by
    refine ⟨σ.rels d hd, ?_, ?_⟩
    · intro s hs
      rw [ruleSyms_renameRule] at hs
      obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.1 hs
      exact σ.relSyms (hr s₀ hs₀)
    · intro g hg
      rw [ruleFuns_renameRule] at hg
      exact σ.funs (hf g hg)
  | .fact x op _ _, h => σ.relSyms (s := (x, op)) h

/-- **Translation of sentences along a renaming.** -/
def renameSen {S T : Sig} (σ : SigHom S T) (φ : Sen S) : Sen T := ⟨renameS σ.f φ.1, φ.2.rename σ⟩

/-- **The satisfaction condition along a renaming.** -/
theorem satisfactionR (alts : Reading) {S T : Sig} (σ : SigHom S T) (M : Model T) (φ : Sen S) :
    (renameSen σ φ).1.Sat alts M.env M.D ↔ φ.1.Sat alts (M.reductR σ).env (M.reductR σ).D :=
  sat_renameS_iff.trans (sat_restrict_iff φ.2.symsIn).symm

/-! ## Functoriality -/

theorem renameP_id : ∀ pr : Prem, renameP (fun x => x) pr = pr
  | .rulePr _ _ _ _ => rfl
  | .ifPr _ => rfl
  | .letPr _ _ => rfl
  | .elsePr => rfl
  | .iterPr pr _ => by rw [renameP, renameP_id pr]

theorem renameP_comp (g : IL.Id → IL.Id) :
    ∀ pr : Prem, renameP (fun x => g (f x)) pr = renameP g (renameP f pr)
  | .rulePr _ _ _ _ => rfl
  | .ifPr _ => rfl
  | .letPr _ _ => rfl
  | .elsePr => rfl
  | .iterPr pr _ => by rw [renameP, renameP_comp g pr]; rfl

theorem renameS_id (φ : SSen) : renameS (fun x => x) φ = φ := by
  cases φ with
  | rule d r =>
    cases r with
    | ruleD nm qs op e prems =>
      have hp : prems.map (renameP fun x => x) = prems :=
        (List.map_congr_left fun pr _ => renameP_id pr).trans (List.map_id prems)
      change SSen.rule d (.ruleD nm qs op e (prems.map (renameP fun x => x))) = _
      rw [hp]
  | fact => rfl

theorem renameS_comp (g : IL.Id → IL.Id) (φ : SSen) :
    renameS (fun x => g (f x)) φ = renameS g (renameS f φ) := by
  cases φ with
  | rule d r =>
    cases r with
    | ruleD nm qs op e prems =>
      have hp : prems.map (renameP fun x => g (f x)) = (prems.map (renameP f)).map (renameP g) := by
        rw [List.map_map]
        exact List.map_congr_left fun pr _ => renameP_comp g pr
      change SSen.rule (d.rename fun x => g (f x)) (.ruleD nm qs op e
        (prems.map (renameP fun x => g (f x)))) = _
      rw [hp]
      rfl
  | fact => rfl

theorem Model.reductR_id {S : Sig} (M : Model S) : M.reductR (SigHom.id S) = M := by
  refine Model.ext' rfl ?_
  funext x op avs w
  exact propext ⟨fun hd => hd.2, fun hd => ⟨M.vanish x op avs w hd, hd⟩⟩

theorem Model.reductR_comp {S T U : Sig} (σ : SigHom S T) (τ : SigHom T U) (M : Model U) :
    M.reductR (σ.comp τ) = (M.reductR τ).reductR σ := by
  refine Model.ext' rfl ?_
  funext x op avs w
  exact propext ⟨fun hd => ⟨hd.1, σ.relSyms (s := (x, op)) hd.1, hd.2⟩, fun hd => ⟨hd.1, hd.2.2⟩⟩

/-- Along an inclusion, the reduct of a renaming is the reduct of `Institution.inst`. -/
theorem Model.reductR_ofLe {S T : Sig} (h : S ≤ T) (M : Model T) :
    M.reductR (SigHom.ofLe h) = M.reduct h :=
  rfl

/-- Along an inclusion, sentence translation is the identity. -/
theorem renameSen_ofLe {S T : Sig} (h : S ≤ T) (φ : Sen S) :
    (renameSen (SigHom.ofLe h) φ).1 = φ.1 :=
  renameS_id φ.1

/-! ## The institution -/

/-- The corridor of a renaming: sentences renamed, models reduced. -/
def corridorR (alts : Reading) {S T : Sig} (σ : SigHom S T) : room alts S ⟶ room alts T :=
  ⟨renameSen σ, Discrete.functor (fun M => Discrete.mk (M.reductR σ)),
    fun M φ => satisfactionR alts σ M.as φ⟩

/-- **The SpecTec specification institution with renamings of relation names**, as a functor
into rooms. -/
def functorR (alts : Reading) : SigR ⥤ Room.{0, 0, 0} where
  obj S := room alts S.sig
  map σ := corridorR alts σ
  map_id S := by
    apply Corridor.ext
    · funext φ
      exact Subtype.ext (renameS_id φ.1)
    · change Discrete.functor (fun M : Model S.sig => Discrete.mk (M.reductR (SigHom.id S.sig))) = 𝟭 _
      exact CategoryTheory.Functor.ext (fun M => by rw [Discrete.functor_obj, Model.reductR_id]; rfl)
        (fun _ _ _ => Subsingleton.elim _ _)
  map_comp {S T U} σ τ := by
    apply Corridor.ext
    · funext φ
      exact Subtype.ext (renameS_comp τ.f φ.1)
    · change Discrete.functor (fun M : Model U.sig => Discrete.mk (M.reductR (σ.comp τ))) =
        Discrete.functor (fun M : Model U.sig => Discrete.mk (M.reductR τ)) ⋙
          Discrete.functor (fun M : Model T.sig => Discrete.mk (M.reductR σ))
      exact CategoryTheory.Functor.ext (fun M => congrArg Discrete.mk (Model.reductR_comp σ τ M.as))
        (fun _ _ _ => Subsingleton.elim _ _)

/-- **The SpecTec specification institution with renamings of relation names.** -/
def instR (alts : Reading) : Silmaril.Logic.Institution.Inst.{0, 0, 0, 0, 0} := ⟨SigR, functorR alts⟩

/-! ## Theories along renamings -/

/-- **Renamings transport models of theories**: if every sentence of `Th` renamed by `σ` holds in
`M`, the reduct of `M` satisfies `Th`. -/
theorem satTh_reductR (alts : Reading) {S T : Sig} (σ : SigHom S T) (M : Model T)
    (Th : Set (Sen S)) (hM : ∀ φ ∈ Th, (renameSen σ φ).1.Sat alts M.env M.D) :
    ∀ φ ∈ Th, φ.1.Sat alts (M.reductR σ).env (M.reductR σ).D :=
  fun φ hφ => (satisfactionR alts σ M φ).1 (hM φ hφ)

end Silmaril.Wasm.SpecTec.Institution
