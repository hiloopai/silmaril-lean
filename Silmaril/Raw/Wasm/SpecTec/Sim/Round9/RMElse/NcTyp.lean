module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.Defs

/-!
# Round 9, rm: `CODE`-free types have `CODE`-free inhabitants (unrefined)

A copy of round 7's `NxSites.nxTyp` (`Silmaril/Proofs/…/Round7/NxSites/Typing`) for the record field
`CODE` instead of `EXPORTS`, with `CodeErase.Swap.ncB` for `Swap.nxB`. The abstraction of types
(`NxSites.toAT`, `nxAT`) and the scope facts (`TypsNx`, `ArgNx`, `matchArgs_typsNx`,
`evalArgs_argNx`) are reused unchanged: they do not mention the field.

* `ncB_of_HasTyp`: a value of a type with `nxAT good (toAT t)`, in a `TypsNx` scope of an
  `EnvNC` environment, holds no `CODE` record.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

/-! ## The induction on fuel -/

/-- The fields of a record type have CODE-free types and are not named `EXPORTS`. -/
def FieldsNC (good : List String) (fs : List TypField) : Prop :=
  (fs.all fun f => match f with | .mk a t _ _ => a != "CODE" && goodTyp good t) = true

/-- The cases of a variant type have CODE-free payload types. -/
def CasesNC (good : List String) (cs : List TypCase) : Prop :=
  (cs.all fun c => match c with | .mk _ t _ _ => goodTyp good t) = true

/-- **CODE-free types have CODE-free inhabitants**, at fuel `n`, member by member. -/
structure NcTyp (good : List String) (env : Env) (n : Nat) : Prop where
  typ : ∀ ρ t v, TypsNx good ρ → nxAT good (toAT t) = true → hasTyp n env ρ t v = .ok true →
    ncB v = true
  tup : ∀ ρ bs vs, TypsNx good ρ → nxATs good (toATBinds bs) = true →
    hasTypTup n env ρ bs vs = .ok true → ncBs vs = true
  list : ∀ ρ t vs, TypsNx good ρ → nxAT good (toAT t) = true →
    hasTypList n env ρ t vs = .ok true → ncBs vs = true
  defTyp : ∀ ρ dt v, TypsNx good ρ → goodDTC good dt = true → hasTypDef n env ρ dt v = .ok true →
    ncB v = true
  fields : ∀ ρ fs gs, TypsNx good ρ → FieldsNC good fs → hasTypFields n env ρ fs gs = .ok true →
    ncBf gs = true
  case : ∀ ρ cs op w, TypsNx good ρ → CasesNC good cs → hasTypCase n env ρ cs op w = .ok true →
    ncB w = true
  insts : ∀ is ws v, (∀ w ∈ ws, ArgNx good w) → (∀ i ∈ is, goodDTC good (instDT i) = true) →
    hasTypInsts n env is ws v = .ok true → ncB v = true

theorem ncTyp_zero (good : List String) (env : Env) : NcTyp good env 0 where
  typ := by intros; simp_all [hasTyp]
  tup := by intros; simp_all [hasTypTup]
  list := by intros; simp_all [hasTypList]
  defTyp := by intros; simp_all [hasTypDef]
  fields := by intros; simp_all [hasTypFields]
  case := by intros; simp_all [hasTypCase]
  insts := by intros; simp_all [hasTypInsts]

theorem ncBs_of_all {vs : List Value} (h : ∀ v ∈ vs, ncB v = true) : ncBs vs = true := by
  rw [ncBs_eq_all, List.all_eq_true]
  exact h

section Succ
variable {good : List String} {env : Env} {m : Nat}

theorem ncTyp_typ_base (ρ : VarEnv) (t : Typ) (v : Value)
    (hb : t = .boolT ∨ (∃ k, t = .numT k) ∨ t = .textT)
    (h : hasTyp (m + 1) env ρ t v = .ok true) : ncB v = true := by
  rcases hb with rfl | ⟨k, rfl⟩ | rfl
  · cases v <;> simp_all [hasTyp, Value.asBool?]
  · cases v <;> simp_all [hasTyp, Value.asNum?]
  · cases v <;> simp_all [hasTyp, Value.asText?]

theorem ncTyp_typ_tup (ih : NcTyp good env m) (ρ : VarEnv) (bs : List TypBind) (v : Value)
    (hρ : TypsNx good ρ) (ht : nxAT good (toAT (.tupT bs)) = true)
    (h : hasTyp (m + 1) env ρ (.tupT bs) v = .ok true) : ncB v = true := by
  cases v <;> simp only [hasTyp, Value.asTuple?, Except.ok.injEq, Bool.false_eq_true] at h
  rename_i vs
  exact ih.tup ρ bs vs hρ ht h

theorem ncTyp_typ_list (ih : NcTyp good env m) (ρ : VarEnv) (t : Typ) (v : Value)
    (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ (.iterT t .list) v = .ok true) : ncB v = true := by
  cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true] at h
  exact ih.list ρ t _ hρ ht h

theorem ncTyp_typ_list1 (ih : NcTyp good env m) (ρ : VarEnv) (t : Typ) (v : Value)
    (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ (.iterT t .list1) v = .ok true) : ncB v = true := by
  cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true] at h
  split at h
  · cases h
  · exact ih.list ρ t _ hρ ht h

theorem ncTyp_typ_listN (ih : NcTyp good env m) (ρ : VarEnv) (t : Typ) (e : Exp)
    (x : Option IL.Id) (v : Value) (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ (.iterT t (.listN e x)) v = .ok true) : ncB v = true := by
  cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true,
    Res.bind_eq_ok] at h
  obtain ⟨_, _, _, _, h⟩ := h
  split at h
  · exact ih.list ρ t _ hρ ht h
  · cases h

theorem ncTyp_typ_opt (ih : NcTyp good env m) (ρ : VarEnv) (t : Typ) (v : Value)
    (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ (.iterT t .opt) v = .ok true) : ncB v = true := by
  cases v <;> simp only [hasTyp, Value.asOpt?, Except.ok.injEq, Bool.false_eq_true] at h
  rename_i o
  cases o with
  | none => rfl
  | some w => exact ih.typ ρ t w hρ ht h

theorem ncTyp_typ_var (hE : EnvNC good env) (ih : NcTyp good env m) (ρ : VarEnv) (x : IL.Id)
    (args : List Arg) (v : Value) (hρ : TypsNx good ρ)
    (ht : nxAT good (toAT (.varT x args)) = true)
    (h : hasTyp (m + 1) env ρ (.varT x args) v = .ok true) : ncB v = true := by
  have ht' : good.contains x = true ∧ nxATs good (toATArgs args) = true := by
    simpa only [toAT, nxAT, Bool.and_eq_true] using ht
  simp only [hasTyp] at h
  split at h
  · rename_i t' hl
    have hf : ρ.findTyp? x = some t' := by
      cases args with
      | nil => simpa only [localTyp?] using hl
      | cons _ _ => simp [localTyp?] at hl
    exact ih.typ ρ t' v hρ (hρ (x, t') (Script.mem_of_find? hf)) h
  · obtain ⟨td, htd, ws, hws, h'⟩ : ∃ td, env.findTyp? x = some td ∧ ∃ ws,
        evalArgs m env ρ args = .ok ws ∧ hasTypInsts m env td.2 ws v = .ok true := by
      simpa only [Res.bind_eq_ok, Res.ofOption_eq_ok] using h
    exact ih.insts td.2 ws v (evalArgs_argNx hρ ht'.2 hws) (hE x td htd ht'.1) h'

theorem ncTyp_typ_succ (hE : EnvNC good env) (ih : NcTyp good env m) (ρ : VarEnv) (t : Typ)
    (v : Value) (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ t v = .ok true) : ncB v = true := by
  cases t with
  | boolT => exact ncTyp_typ_base ρ _ v (.inl rfl) h
  | numT k => exact ncTyp_typ_base ρ _ v (.inr (.inl ⟨k, rfl⟩)) h
  | textT => exact ncTyp_typ_base ρ _ v (.inr (.inr rfl)) h
  | tupT bs => exact ncTyp_typ_tup ih ρ bs v hρ ht h
  | iterT t it =>
    cases it with
    | opt => exact ncTyp_typ_opt ih ρ t v hρ ht h
    | list => exact ncTyp_typ_list ih ρ t v hρ ht h
    | list1 => exact ncTyp_typ_list1 ih ρ t v hρ ht h
    | listN e x => exact ncTyp_typ_listN ih ρ t e x v hρ ht h
  | varT x args => exact ncTyp_typ_var hE ih ρ x args v hρ ht h

theorem ncTyp_tup_succ (ih : NcTyp good env m) : ∀ (ρ : VarEnv) (bs : List TypBind)
    (vs : List Value), TypsNx good ρ → nxATs good (toATBinds bs) = true →
    hasTypTup (m + 1) env ρ bs vs = .ok true → ncBs vs = true
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, _, h => by simp [hasTypTup] at h
  | _, _ :: _, [], _, _, h => by simp [hasTypTup] at h
  | ρ, .mk x t :: bs, v :: vs, hρ, hb, h => by
    simp only [toATBinds, nxATs, Bool.and_eq_true] at hb
    simp only [hasTypTup, Res.bind_eq_ok] at h
    obtain ⟨b, hb₁, h⟩ := h
    cases b
    · simp at h
    · simp only [↓reduceIte] at h
      have hv := ih.typ ρ t v hρ hb.1 hb₁
      have hvs := ih.tup (ρ.bindVal x v) bs vs (typsNx_bindVal hρ x v) hb.2 h
      simp [ncBs, hv, hvs]

theorem ncTyp_list_succ (ih : NcTyp good env m) (ρ : VarEnv) (t : Typ) :
    ∀ (vs : List Value), TypsNx good ρ → nxAT good (toAT t) = true →
    hasTypList (m + 1) env ρ t vs = .ok true → ncBs vs = true
  | [], _, _, _ => rfl
  | v :: vs, hρ, ht, h => by
    simp only [hasTypList, Res.bind_eq_ok] at h
    obtain ⟨b, hb₁, h⟩ := h
    cases b
    · simp at h
    · simp only [↓reduceIte] at h
      have hv := ih.typ ρ t v hρ ht hb₁
      have hvs := ih.list ρ t vs hρ ht h
      simp [ncBs, hv, hvs]

theorem ncTyp_defTyp_succ (ih : NcTyp good env m) (ρ : VarEnv) (dt : DefTyp) (v : Value)
    (hρ : TypsNx good ρ) (hd : goodDTC good dt = true)
    (h : hasTypDef (m + 1) env ρ dt v = .ok true) : ncB v = true := by
  cases dt with
  | aliasT t =>
    simp only [goodDTC, goodTyp_eq] at hd
    simp only [hasTypDef] at h
    exact ih.typ ρ t v hρ hd h
  | structT fs =>
    cases v <;> simp only [hasTypDef, Value.asStruct?, Except.ok.injEq, Bool.false_eq_true] at h
    exact ih.fields ρ fs _ hρ hd h
  | variantT cs =>
    cases v <;> simp only [hasTypDef, Value.asCase?, Except.ok.injEq, Bool.false_eq_true] at h
    rename_i op w
    exact ih.case ρ cs op w hρ hd h

theorem ncTyp_fields_succ (ih : NcTyp good env m) : ∀ (ρ : VarEnv) (fs : List TypField)
    (gs : List (AtomS × Value)), TypsNx good ρ → FieldsNC good fs →
    hasTypFields (m + 1) env ρ fs gs = .ok true → ncBf gs = true
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, _, h => by simp [hasTypFields] at h
  | _, _ :: _, [], _, _, h => by simp [hasTypFields] at h
  | ρ, .mk a t _ prems :: fs, (a', w) :: gs, hρ, hf, h => by
    simp only [FieldsNC, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
    obtain ⟨⟨ha, ht⟩, hfs⟩ := hf
    simp only [hasTypFields] at h
    split at h
    · rename_i haa
      subst haa
      simp only [Res.bind_eq_ok] at h
      obtain ⟨b, hb₁, h⟩ := h
      cases b
      · simp at h
      · simp only [↓reduceIte, Res.bind_eq_ok] at h
        obtain ⟨hp, _, h⟩ := h
        cases hp
        · simp at h
        · simp only [↓reduceIte] at h
          rw [goodTyp_eq] at ht
          have hw := ih.typ ρ t w hρ ht hb₁
          have hgs := ih.fields ρ fs gs hρ hfs h
          simp only [ncBf, hw, hgs, Bool.and_true, Bool.true_and, bne_iff_ne, ne_eq]
          exact ha
    · cases h

theorem ncTyp_case_succ (ih : NcTyp good env m) (ρ : VarEnv) : ∀ (cs : List TypCase)
    (op : MixopS) (w : Value), TypsNx good ρ → CasesNC good cs →
    hasTypCase (m + 1) env ρ cs op w = .ok true → ncB w = true
  | [], _, _, _, _, h => by simp [hasTypCase] at h
  | .mk op t qs prems :: cs, op', w, hρ, hc, h => by
    simp only [CasesNC, List.all_cons, Bool.and_eq_true] at hc
    simp only [hasTypCase] at h
    split at h
    · simp only [Res.bind_eq_ok] at h
      obtain ⟨b, hb₁, h⟩ := h
      cases b
      · simp at h
      · rw [goodTyp_eq] at hc
        exact ih.typ ρ t w hρ hc.1 hb₁
    · exact ih.case ρ cs op' w hρ hc.2 h

theorem ncTyp_insts_succ (ih : NcTyp good env m) : ∀ (is : List Inst) (ws : List ArgV)
    (v : Value), (∀ w ∈ ws, ArgNx good w) → (∀ i ∈ is, goodDTC good (instDT i) = true) →
    hasTypInsts (m + 1) env is ws v = .ok true → ncB v = true
  | [], _, _, _, _, h => by simp [hasTypInsts] at h
  | .instD qs pats dt :: is, ws, v, hw, hi, h => by
    simp only [hasTypInsts] at h
    rcases Script.elimUndef_eq_ok h with ⟨ρ', hm, h⟩ | ⟨_, h⟩
    · exact ih.defTyp ρ' dt v (matchArgs_typsNx m (typsNx_empty good) hw hm)
        (hi _ List.mem_cons_self) h
    · exact ih.insts is ws v hw (fun i hm => hi i (List.mem_cons_of_mem _ hm)) h

theorem ncTyp_succ (hE : EnvNC good env) (ih : NcTyp good env m) : NcTyp good env (m + 1) where
  typ := ncTyp_typ_succ hE ih
  tup := ncTyp_tup_succ ih
  list := ncTyp_list_succ ih
  defTyp := ncTyp_defTyp_succ ih
  fields := ncTyp_fields_succ ih
  case := ncTyp_case_succ ih
  insts := ncTyp_insts_succ ih

end Succ

/-- **CODE-free types have CODE-free inhabitants**, at every fuel. -/
theorem ncTyp {good : List String} {env : Env} (hE : EnvNC good env) : ∀ n, NcTyp good env n
  | 0 => ncTyp_zero good env
  | n + 1 => ncTyp_succ hE (ncTyp hE n)

/-- **A value of an CODE-free type is CODE-free**, in a scope whose type variables are bound
to CODE-free types and an environment whose `good` types are CODE-free. -/
theorem ncB_of_HasTyp {good : List String} {env : Env} (hE : EnvNC good env) {ρ : VarEnv}
    {t : Typ} {v : Value} (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : HasTyp env ρ t v) : ncB v = true := by
  obtain ⟨n, hn⟩ := h
  exact (ncTyp hE n).typ ρ t v hρ ht hn


end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
