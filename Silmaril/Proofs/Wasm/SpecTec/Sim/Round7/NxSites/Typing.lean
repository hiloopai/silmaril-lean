module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Value
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Assemble

/-!
# Round 7, REH route 2: export-free types have export-free inhabitants

The link from the static check to runtime values, for values whose type is checked at runtime.
`Sim.QuantsOk` gives every rule quantifier a value `v` with `Sem.HasTyp env ρ t v` for its
declared type `t`. If `toAT t` is export-free, so is `v`:

* `TypsNx good ρ`: the type variables of the scope are bound to export-free types;
* `EnvNx good env`: every type `env` finds under a `good` name has instances whose bodies pass
  `goodDT good`;
* `nxTyp`: by induction on `hasTyp`'s fuel, a value of an export-free type in a `TypsNx` scope of
  an `EnvNx` environment is `nxB` (`nxB_of_hasTyp`, and `nxB_of_HasTyp` without fuel).

Type parameters bound by an instance's argument patterns are bound to the evaluated type
arguments, which are export-free when the type is (`matchArgs_typsNx`, `evalArgs_argNx`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxSites

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (typsPres)

/-- **The type variables of `ρ` are bound to export-free types.** -/
def TypsNx (good : List String) (ρ : VarEnv) : Prop :=
  ∀ p ∈ ρ.typs, nxAT good (toAT p.2) = true

/-- **Every type `env` finds under a `good` name has export-free instance bodies.** -/
def EnvNx (good : List String) (env : Env) : Prop :=
  ∀ x td, env.findTyp? x = some td → good.contains x = true →
    ∀ i ∈ td.2, goodDT good (instDT i) = true

/-- An evaluated type argument is export-free. -/
def ArgNx (good : List String) : ArgV → Prop
  | .typ t => nxAT good (toAT t) = true
  | _ => True

/-! ## `goodTyp` is `nxAT ∘ toAT` -/

mutual
theorem goodTyp_eq (good : List String) : ∀ t : Typ, goodTyp good t = nxAT good (toAT t)
  | .varT n args => by
    simp only [goodTyp, toAT, nxAT, goodArgs_eq good args]
  | .boolT => rfl
  | .numT _ => rfl
  | .textT => rfl
  | .tupT bs => by simp only [goodTyp, toAT, nxAT, goodBinds_eq good bs]
  | .iterT t _ => by simp only [goodTyp, toAT, nxAT, goodTyp_eq good t]

theorem goodArgs_eq (good : List String) :
    ∀ args : List Arg, goodArgs good args = nxATs good (toATArgs args)
  | [] => rfl
  | .typA t :: xs => by simp only [goodArgs, toATArgs, nxATs, goodTyp_eq good t,
      goodArgs_eq good xs]
  | .expA _ :: xs => by simp only [goodArgs, toATArgs, goodArgs_eq good xs]
  | .defA _ :: xs => by simp only [goodArgs, toATArgs, goodArgs_eq good xs]
  | .gramA _ :: xs => by simp only [goodArgs, toATArgs, goodArgs_eq good xs]

theorem goodBinds_eq (good : List String) :
    ∀ bs : List TypBind, goodBinds good bs = nxATs good (toATBinds bs)
  | [] => rfl
  | .mk _ t :: bs => by simp only [goodBinds, toATBinds, nxATs, goodTyp_eq good t,
      goodBinds_eq good bs]
end

/-! ## Scopes -/

theorem typsNx_of_typs {good : List String} {ρ ρ' : VarEnv} (h : TypsNx good ρ)
    (he : ρ'.typs = ρ.typs) : TypsNx good ρ' := by
  intro p hp
  rw [he] at hp
  exact h p hp

theorem typsNx_empty (good : List String) : TypsNx good VarEnv.empty := by
  simp [TypsNx, VarEnv.empty, Map.empty]

theorem typsNx_bindVal {good : List String} {ρ : VarEnv} (h : TypsNx good ρ) (x : IL.Id)
    (v : Value) : TypsNx good (ρ.bindVal x v) :=
  typsNx_of_typs h rfl

theorem typsNx_bindTyp {good : List String} {ρ : VarEnv} (h : TypsNx good ρ) (x : IL.Id)
    {t : Typ} (ht : nxAT good (toAT t) = true) : TypsNx good (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ht
    · exact h p hp

theorem matchTypV_typsNx {good : List String} {env : Env} {ρ ρ' : VarEnv} {pat t : Typ}
    (h : TypsNx good ρ) (ht : nxAT good (toAT t) = true) (hm : matchTypV env ρ pat t = .ok ρ') :
    TypsNx good ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) | (cases hm; exact typsNx_bindTyp h _ ht) |
    (cases hm))

theorem matchSymV_typs' {env : Env} {ρ ρ' : VarEnv} {pat g : Sym}
    (h : matchSymV env ρ pat g = .ok ρ') : ρ'.typs = ρ.typs := by
  unfold matchSymV at h
  repeat (first | (split at h) | (cases h; rfl) | (cases h))

theorem matchArg_typsNx {good : List String} {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg}
    {w : ArgV} (h : TypsNx good ρ) (hw : ArgNx good w) (hm : matchArg n env ρ a w = .ok ρ') :
    TypsNx good ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact typsNx_of_typs h ((typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_typsNx h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact typsNx_of_typs h (matchSymV_typs' hm)
  all_goals cases hm

theorem matchArgs_typsNx {good : List String} {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, TypsNx good ρ →
      (∀ w ∈ ws, ArgNx good w) → matchArgs n env ρ ags ws = .ok ρ' → TypsNx good ρ'
  | 0, _, _, _, _, _, _, hm => by simp [matchArgs] at hm
  | n + 1, ρ, ρ', ags, ws, h, hw, hm => by
    cases ags with
    | nil => cases ws <;> simp only [matchArgs] at hm <;> cases hm; exact h
    | cons a ags =>
      cases ws with
      | nil => simp only [matchArgs] at hm; cases hm
      | cons w ws =>
        simp only [matchArgs, Res.bind_eq_ok] at hm
        obtain ⟨ρ₁, h₁, h₂⟩ := hm
        exact matchArgs_typsNx n (matchArg_typsNx h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

theorem resolveTyp_nx {good : List String} {ρ : VarEnv} (h : TypsNx good ρ) {t : Typ}
    (ht : nxAT good (toAT t) = true) : nxAT good (toAT (resolveTyp ρ t)) = true := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (Script.mem_of_find? hf)
  · exact ht

theorem nxATs_typA {good : List String} {t : Typ} :
    ∀ {ags : List Arg}, nxATs good (toATArgs ags) = true → Arg.typA t ∈ ags →
      nxAT good (toAT t) = true
  | [], _, ha => by simp at ha
  | b :: ags, hA, ha => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · simp only [toATArgs, nxATs, Bool.and_eq_true] at hA
      exact hA.1
    · cases b <;> simp only [toATArgs, nxATs, Bool.and_eq_true] at hA
      · exact nxATs_typA hA ha'
      · exact nxATs_typA hA.2 ha'
      · exact nxATs_typA hA ha'
      · exact nxATs_typA hA ha'

/-- **Evaluated type arguments of an export-free type name are export-free.** -/
theorem evalArgs_argNx {good : List String} {env : Env} {n : Nat} {ρ : VarEnv}
    {ags : List Arg} {ws : List ArgV} (h : TypsNx good ρ)
    (hA : nxATs good (toATArgs ags) = true) (he : evalArgs n env ρ ags = .ok ws) :
    ∀ w ∈ ws, ArgNx good w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := Script.mapM_ok_mem he w hw
  rcases n with _ | n
  · simp [evalArg] at hfa
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA t => cases hfa; exact resolveTyp_nx h (nxATs_typA hA ha)
  case defA x => cases hfa; trivial
  case gramA => cases hfa; trivial

/-! ## The induction on fuel -/

/-- The fields of a record type have export-free types and are not named `EXPORTS`. -/
def FieldsNx (good : List String) (fs : List TypField) : Prop :=
  (fs.all fun f => match f with | .mk a t _ _ => a != "EXPORTS" && goodTyp good t) = true

/-- The cases of a variant type have export-free payload types. -/
def CasesNx (good : List String) (cs : List TypCase) : Prop :=
  (cs.all fun c => match c with | .mk _ t _ _ => goodTyp good t) = true

/-- **Export-free types have export-free inhabitants**, at fuel `n`, member by member. -/
structure NxTyp (good : List String) (env : Env) (n : Nat) : Prop where
  typ : ∀ ρ t v, TypsNx good ρ → nxAT good (toAT t) = true → hasTyp n env ρ t v = .ok true →
    nxB v = true
  tup : ∀ ρ bs vs, TypsNx good ρ → nxATs good (toATBinds bs) = true →
    hasTypTup n env ρ bs vs = .ok true → nxBs vs = true
  list : ∀ ρ t vs, TypsNx good ρ → nxAT good (toAT t) = true →
    hasTypList n env ρ t vs = .ok true → nxBs vs = true
  defTyp : ∀ ρ dt v, TypsNx good ρ → goodDT good dt = true → hasTypDef n env ρ dt v = .ok true →
    nxB v = true
  fields : ∀ ρ fs gs, TypsNx good ρ → FieldsNx good fs → hasTypFields n env ρ fs gs = .ok true →
    nxBf gs = true
  case : ∀ ρ cs op w, TypsNx good ρ → CasesNx good cs → hasTypCase n env ρ cs op w = .ok true →
    nxB w = true
  insts : ∀ is ws v, (∀ w ∈ ws, ArgNx good w) → (∀ i ∈ is, goodDT good (instDT i) = true) →
    hasTypInsts n env is ws v = .ok true → nxB v = true

theorem nxTyp_zero (good : List String) (env : Env) : NxTyp good env 0 where
  typ := by intros; simp_all [hasTyp]
  tup := by intros; simp_all [hasTypTup]
  list := by intros; simp_all [hasTypList]
  defTyp := by intros; simp_all [hasTypDef]
  fields := by intros; simp_all [hasTypFields]
  case := by intros; simp_all [hasTypCase]
  insts := by intros; simp_all [hasTypInsts]

theorem nxBs_of_all {vs : List Value} (h : ∀ v ∈ vs, nxB v = true) : nxBs vs = true := by
  rw [nxBs_eq_all, List.all_eq_true]
  exact h

section Succ
variable {good : List String} {env : Env} {m : Nat}

theorem nxTyp_typ_base (ρ : VarEnv) (t : Typ) (v : Value)
    (hb : t = .boolT ∨ (∃ k, t = .numT k) ∨ t = .textT)
    (h : hasTyp (m + 1) env ρ t v = .ok true) : nxB v = true := by
  rcases hb with rfl | ⟨k, rfl⟩ | rfl
  · cases v <;> simp_all [hasTyp, Value.asBool?]
  · cases v <;> simp_all [hasTyp, Value.asNum?]
  · cases v <;> simp_all [hasTyp, Value.asText?]

theorem nxTyp_typ_tup (ih : NxTyp good env m) (ρ : VarEnv) (bs : List TypBind) (v : Value)
    (hρ : TypsNx good ρ) (ht : nxAT good (toAT (.tupT bs)) = true)
    (h : hasTyp (m + 1) env ρ (.tupT bs) v = .ok true) : nxB v = true := by
  cases v <;> simp only [hasTyp, Value.asTuple?, Except.ok.injEq, Bool.false_eq_true] at h
  rename_i vs
  exact ih.tup ρ bs vs hρ ht h

theorem nxTyp_typ_list (ih : NxTyp good env m) (ρ : VarEnv) (t : Typ) (v : Value)
    (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ (.iterT t .list) v = .ok true) : nxB v = true := by
  cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true] at h
  exact ih.list ρ t _ hρ ht h

theorem nxTyp_typ_list1 (ih : NxTyp good env m) (ρ : VarEnv) (t : Typ) (v : Value)
    (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ (.iterT t .list1) v = .ok true) : nxB v = true := by
  cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true] at h
  split at h
  · cases h
  · exact ih.list ρ t _ hρ ht h

theorem nxTyp_typ_listN (ih : NxTyp good env m) (ρ : VarEnv) (t : Typ) (e : Exp)
    (x : Option IL.Id) (v : Value) (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ (.iterT t (.listN e x)) v = .ok true) : nxB v = true := by
  cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true,
    Res.bind_eq_ok] at h
  obtain ⟨_, _, _, _, h⟩ := h
  split at h
  · exact ih.list ρ t _ hρ ht h
  · cases h

theorem nxTyp_typ_opt (ih : NxTyp good env m) (ρ : VarEnv) (t : Typ) (v : Value)
    (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ (.iterT t .opt) v = .ok true) : nxB v = true := by
  cases v <;> simp only [hasTyp, Value.asOpt?, Except.ok.injEq, Bool.false_eq_true] at h
  rename_i o
  cases o with
  | none => rfl
  | some w => exact ih.typ ρ t w hρ ht h

theorem nxTyp_typ_var (hE : EnvNx good env) (ih : NxTyp good env m) (ρ : VarEnv) (x : IL.Id)
    (args : List Arg) (v : Value) (hρ : TypsNx good ρ)
    (ht : nxAT good (toAT (.varT x args)) = true)
    (h : hasTyp (m + 1) env ρ (.varT x args) v = .ok true) : nxB v = true := by
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

theorem nxTyp_typ_succ (hE : EnvNx good env) (ih : NxTyp good env m) (ρ : VarEnv) (t : Typ)
    (v : Value) (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : hasTyp (m + 1) env ρ t v = .ok true) : nxB v = true := by
  cases t with
  | boolT => exact nxTyp_typ_base ρ _ v (.inl rfl) h
  | numT k => exact nxTyp_typ_base ρ _ v (.inr (.inl ⟨k, rfl⟩)) h
  | textT => exact nxTyp_typ_base ρ _ v (.inr (.inr rfl)) h
  | tupT bs => exact nxTyp_typ_tup ih ρ bs v hρ ht h
  | iterT t it =>
    cases it with
    | opt => exact nxTyp_typ_opt ih ρ t v hρ ht h
    | list => exact nxTyp_typ_list ih ρ t v hρ ht h
    | list1 => exact nxTyp_typ_list1 ih ρ t v hρ ht h
    | listN e x => exact nxTyp_typ_listN ih ρ t e x v hρ ht h
  | varT x args => exact nxTyp_typ_var hE ih ρ x args v hρ ht h

theorem nxTyp_tup_succ (ih : NxTyp good env m) : ∀ (ρ : VarEnv) (bs : List TypBind)
    (vs : List Value), TypsNx good ρ → nxATs good (toATBinds bs) = true →
    hasTypTup (m + 1) env ρ bs vs = .ok true → nxBs vs = true
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
      simp [nxBs, hv, hvs]

theorem nxTyp_list_succ (ih : NxTyp good env m) (ρ : VarEnv) (t : Typ) :
    ∀ (vs : List Value), TypsNx good ρ → nxAT good (toAT t) = true →
    hasTypList (m + 1) env ρ t vs = .ok true → nxBs vs = true
  | [], _, _, _ => rfl
  | v :: vs, hρ, ht, h => by
    simp only [hasTypList, Res.bind_eq_ok] at h
    obtain ⟨b, hb₁, h⟩ := h
    cases b
    · simp at h
    · simp only [↓reduceIte] at h
      have hv := ih.typ ρ t v hρ ht hb₁
      have hvs := ih.list ρ t vs hρ ht h
      simp [nxBs, hv, hvs]

theorem nxTyp_defTyp_succ (ih : NxTyp good env m) (ρ : VarEnv) (dt : DefTyp) (v : Value)
    (hρ : TypsNx good ρ) (hd : goodDT good dt = true)
    (h : hasTypDef (m + 1) env ρ dt v = .ok true) : nxB v = true := by
  cases dt with
  | aliasT t =>
    simp only [goodDT, goodTyp_eq] at hd
    simp only [hasTypDef] at h
    exact ih.typ ρ t v hρ hd h
  | structT fs =>
    cases v <;> simp only [hasTypDef, Value.asStruct?, Except.ok.injEq, Bool.false_eq_true] at h
    exact ih.fields ρ fs _ hρ hd h
  | variantT cs =>
    cases v <;> simp only [hasTypDef, Value.asCase?, Except.ok.injEq, Bool.false_eq_true] at h
    rename_i op w
    exact ih.case ρ cs op w hρ hd h

theorem nxTyp_fields_succ (ih : NxTyp good env m) : ∀ (ρ : VarEnv) (fs : List TypField)
    (gs : List (AtomS × Value)), TypsNx good ρ → FieldsNx good fs →
    hasTypFields (m + 1) env ρ fs gs = .ok true → nxBf gs = true
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, _, h => by simp [hasTypFields] at h
  | _, _ :: _, [], _, _, h => by simp [hasTypFields] at h
  | ρ, .mk a t _ prems :: fs, (a', w) :: gs, hρ, hf, h => by
    simp only [FieldsNx, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
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
          simp only [nxBf, hw, hgs, Bool.and_true, Bool.true_and, bne_iff_ne, ne_eq]
          exact ha
    · cases h

theorem nxTyp_case_succ (ih : NxTyp good env m) (ρ : VarEnv) : ∀ (cs : List TypCase)
    (op : MixopS) (w : Value), TypsNx good ρ → CasesNx good cs →
    hasTypCase (m + 1) env ρ cs op w = .ok true → nxB w = true
  | [], _, _, _, _, h => by simp [hasTypCase] at h
  | .mk op t qs prems :: cs, op', w, hρ, hc, h => by
    simp only [CasesNx, List.all_cons, Bool.and_eq_true] at hc
    simp only [hasTypCase] at h
    split at h
    · simp only [Res.bind_eq_ok] at h
      obtain ⟨b, hb₁, h⟩ := h
      cases b
      · simp at h
      · rw [goodTyp_eq] at hc
        exact ih.typ ρ t w hρ hc.1 hb₁
    · exact ih.case ρ cs op' w hρ hc.2 h

theorem nxTyp_insts_succ (ih : NxTyp good env m) : ∀ (is : List Inst) (ws : List ArgV)
    (v : Value), (∀ w ∈ ws, ArgNx good w) → (∀ i ∈ is, goodDT good (instDT i) = true) →
    hasTypInsts (m + 1) env is ws v = .ok true → nxB v = true
  | [], _, _, _, _, h => by simp [hasTypInsts] at h
  | .instD qs pats dt :: is, ws, v, hw, hi, h => by
    simp only [hasTypInsts] at h
    rcases Script.elimUndef_eq_ok h with ⟨ρ', hm, h⟩ | ⟨_, h⟩
    · exact ih.defTyp ρ' dt v (matchArgs_typsNx m (typsNx_empty good) hw hm)
        (hi _ List.mem_cons_self) h
    · exact ih.insts is ws v hw (fun i hm => hi i (List.mem_cons_of_mem _ hm)) h

theorem nxTyp_succ (hE : EnvNx good env) (ih : NxTyp good env m) : NxTyp good env (m + 1) where
  typ := nxTyp_typ_succ hE ih
  tup := nxTyp_tup_succ ih
  list := nxTyp_list_succ ih
  defTyp := nxTyp_defTyp_succ ih
  fields := nxTyp_fields_succ ih
  case := nxTyp_case_succ ih
  insts := nxTyp_insts_succ ih

end Succ

/-- **Export-free types have export-free inhabitants**, at every fuel. -/
theorem nxTyp {good : List String} {env : Env} (hE : EnvNx good env) : ∀ n, NxTyp good env n
  | 0 => nxTyp_zero good env
  | n + 1 => nxTyp_succ hE (nxTyp hE n)

/-- **A value of an export-free type is export-free**, in a scope whose type variables are bound
to export-free types and an environment whose `good` types are export-free. -/
theorem nxB_of_HasTyp {good : List String} {env : Env} (hE : EnvNx good env) {ρ : VarEnv}
    {t : Typ} {v : Value} (hρ : TypsNx good ρ) (ht : nxAT good (toAT t) = true)
    (h : HasTyp env ρ t v) : nxB v = true := by
  obtain ⟨n, hn⟩ := h
  exact (nxTyp hE n).typ ρ t v hρ ht hn

/-! ## The script's types -/

theorem sigTypOk_good {S : Sig} {x : String} {ps : List Param} {insts : List Inst}
    (h : sigTypOk S x ps insts = true) (hx : S.good.contains x = true) :
    ∀ i ∈ insts, goodDT S.good (instDT i) = true := by
  simp only [sigTypOk, Bool.and_eq_true, hx, Bool.not_true, Bool.false_or,
    List.all_eq_true] at h
  exact h.2

mutual
theorem good_of_itemOk (S : Sig) {x : String} {td : TypDef} {hx : S.good.contains x = true} :
    ∀ d : Def, itemOk S d = true → (x, td) ∈ typsOfDef d →
      ∀ i ∈ td.2, goodDT S.good (instDT i) = true
  | .typD y ps insts, h, hm => by
    simp only [typsOfDef, Map.empty, Map.bind] at hm
    split at hm
    · simp at hm
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp only [itemOk, Bool.and_eq_true] at h
      exact sigTypOk_good h.1 hx
  | .decD _ _ _ _, _, hm => by simp [typsOfDef, Map.empty] at hm
  | .relD _ _ _ _ _, _, hm => by simp [typsOfDef, Map.empty] at hm
  | .gramD _ _ _ _, _, hm => by simp [typsOfDef, Map.empty] at hm
  | .recD ds, h, hm => by
    simp only [itemOk] at h
    simp only [typsOfDef] at hm
    exact good_of_itemsOk S (hx := hx) ds h hm

theorem good_of_itemsOk (S : Sig) {x : String} {td : TypDef} {hx : S.good.contains x = true} :
    ∀ ds : List Def, itemsOk S ds = true → (x, td) ∈ typsOfDefs ds →
      ∀ i ∈ td.2, goodDT S.good (instDT i) = true
  | [], _, hm => by simp [typsOfDefs, Map.empty] at hm
  | d :: ds, h, hm => by
    simp only [itemsOk, Bool.and_eq_true] at h
    simp only [typsOfDefs, List.mem_append] at hm
    rcases hm with hm | hm
    · exact good_of_itemsOk S (hx := hx) ds h.2 hm
    · exact good_of_itemOk S (hx := hx) d h.1 hm
end

/-- `itemsOk` is `List.all itemOk`. -/
theorem itemsOk_eq_all (S : Sig) : ∀ ds : List Def, itemsOk S ds = ds.all (itemOk S)
  | [] => rfl
  | d :: ds => by simp only [itemsOk, List.all_cons, itemsOk_eq_all S ds]

/-- **The round-7 environment's `good` types are export-free.** -/
theorem envNx_utf8Env (B : Builtins) : EnvNx sigFixed.good (utf8Env B) := by
  intro x td h hx
  have he : (utf8Env B).findTyp? x = (simEnv B).findTyp? x := by
    simp only [utf8Env, utf8BaseEnv, simEnv, Env.findTyp?, Env.withBuiltins, Env.bindDef]
  have hm : (x, td) ∈ typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed :=
    TypAgree.mem_typs_of_findTyp (B := B) (he ▸ h)
  exact good_of_itemsOk sigFixed (hx := hx) _
    ((itemsOk_eq_all sigFixed _).trans itemsOk_fixed) hm

/-- **A value of an export-free type is export-free in the round-7 environment**, in a scope
without type variables bound to types that may hold an `EXPORTS` record. -/
theorem nxB_of_HasTyp_utf8Env {B : Builtins} {ρ : VarEnv} {t : Typ} {v : Value}
    (hρ : TypsNx sigFixed.good ρ) (ht : nxAT sigFixed.good (toAT t) = true)
    (h : HasTyp (utf8Env B) ρ t v) : nxB v = true :=
  nxB_of_HasTyp (envNx_utf8Env B) hρ ht h

/-- `bindVals` keeps the type variables. -/
theorem typsNx_bindVals {good : List String} {ρ : VarEnv} (h : TypsNx good ρ)
    (xs : List (IL.Id × Value)) : TypsNx good (ρ.bindVals xs) :=
  typsNx_of_typs h rfl

/-- **Rule quantifiers of export-free types hold export-free values**: under `Sim.QuantsOk` in
`utf8Env B`, in a scope whose type variables are export-free (for a relation without type
parameters, such as `Step`, `Step_pure` and `Step_read`, the scope has none). -/
theorem nxB_of_quantsOk {B : Builtins} {ρ : VarEnv} {qs : List Param}
    (hρ : TypsNx sigFixed.good ρ) (hq : QuantsOk (utf8Env B) ρ qs) {x : IL.Id} {t : Typ}
    (hx : Param.expP x t ∈ qs) (ht : nxAT sigFixed.good (toAT t) = true) :
    ∃ w, ρ.findVal? x = some w ∧ nxB w = true := by
  obtain ⟨w, hw, hty⟩ := hq x t hx
  exact ⟨w, hw, nxB_of_HasTyp_utf8Env hρ ht hty⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
