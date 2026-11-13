module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Else.Defs

/-!
# Terms and scopes that never reach `x₀`

The invariants threaded through the converse monotonicity (`Raw/…/Sim20/Utf8Else/Agree.lean`),
for a definition name `x₀`. They are round 7's `Round7.Script.GoodEvs`, `DefsOk` and `ArgOk` with
"reachable and not `$utf8`" replaced by "not `x₀`":

* `GoodEvs x₀` splits over the events of every syntax class (`goodEvs_exps`, …);
* `goodEvs_of_not_mem`: a list whose references do not include `(1, x₀)` is `GoodEvs x₀`;
* `DefsOk x₀` survives binding values, matching and premises (`defsOk_of_defs` with round 7's
  `Round7.Script.defsPres`), argument matching (`matchArgs_defsOk`) and relation parameters
  (`bindParams_defsOk`); evaluated arguments are `ArgOk x₀` (`evalArgs_argOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open scoped Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evExp evExps evOExp evEFields evPath evIterExp
  evIter evDoms evArg evArgs evPrem evPrems evClause evRule evRefs mem_evRefs mem_of_find?
  defsPres matchTypV_defs matchSymV_defs mapM_ok_mem)

variable {x₀ : String}

/-! ## Events -/

@[simp] theorem goodEvs_nil : GoodEvs x₀ [] := by simp [GoodEvs]

@[simp] theorem goodEvs_cons {e : Ev} {l : List Ev} :
    GoodEvs x₀ (e :: l) ↔ GoodEv x₀ e ∧ GoodEvs x₀ l := by
  simp [GoodEvs]

@[simp] theorem goodEvs_append {l₁ l₂ : List Ev} :
    GoodEvs x₀ (l₁ ++ l₂) ↔ GoodEvs x₀ l₁ ∧ GoodEvs x₀ l₂ := by
  simp only [GoodEvs, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

@[simp] theorem goodEv_atom (a : String) : GoodEv x₀ (.atom a) ↔ True := Iff.rfl
@[simp] theorem goodEv_comp : GoodEv x₀ .comp ↔ True := Iff.rfl
@[simp] theorem goodEv_upd (r : Exp) (ats : List String) : GoodEv x₀ (.upd r ats) ↔ True :=
  Iff.rfl
@[simp] theorem goodEv_ref1 (x : String) : GoodEv x₀ (.ref 1 x) ↔ x ≠ x₀ := Iff.rfl
@[simp] theorem goodEv_ref0 (x : String) : GoodEv x₀ (.ref 0 x) ↔ True := Iff.rfl
@[simp] theorem goodEv_ref2 (x : String) : GoodEv x₀ (.ref 2 x) ↔ True := Iff.rfl
@[simp] theorem goodEv_ref3 (x : String) : GoodEv x₀ (.ref 3 x) ↔ True := Iff.rfl

@[simp] theorem goodEvs_flatMap {α : Type} {f : α → List Ev} {l : List α} :
    GoodEvs x₀ (l.flatMap f) ↔ ∀ x ∈ l, GoodEvs x₀ (f x) := by
  simp only [GoodEvs, List.mem_flatMap]
  exact ⟨fun h x hx e he => h e ⟨x, hx, he⟩, fun h e ⟨x, hx, he⟩ => h x hx e he⟩

theorem goodEvs_exps : ∀ {es : List Exp}, GoodEvs x₀ (evExps es) → ∀ e ∈ es, GoodEvs x₀ (evExp e)
  | [], _ => by simp
  | e :: es, h => by
    simp only [evExps, goodEvs_append] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact goodEvs_exps h.2 e' he'

theorem goodEvs_doms : ∀ {ds : List Dom}, GoodEvs x₀ (evDoms ds) →
    ∀ e ∈ ds.map domSrc, GoodEvs x₀ (evExp e)
  | [], _ => by simp
  | .mk x e :: ds, h => by
    simp only [evDoms, goodEvs_append] at h
    intro e' he'
    simp only [List.map_cons, List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact h.1
    · exact goodEvs_doms h.2 e' he'

theorem goodEvs_doms' : ∀ {ds : List Dom}, GoodEvs x₀ (evDoms ds) →
    ∀ d ∈ ds, GoodEvs x₀ (evExp (domSrc d))
  | [], _ => by simp
  | .mk x e :: ds, h => by
    simp only [evDoms, goodEvs_append] at h
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact goodEvs_doms' h.2 d hd

theorem goodEvs_args : ∀ {ags : List Arg}, GoodEvs x₀ (evArgs ags) →
    ∀ a ∈ ags, GoodEvs x₀ (evArg a)
  | [], _ => by simp
  | a :: ags, h => by
    simp only [evArgs, goodEvs_append] at h
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact h.1
    · exact goodEvs_args h.2 a' ha'

theorem goodEvs_prems : ∀ {ps : List Prem}, GoodEvs x₀ (evPrems ps) →
    ∀ p ∈ ps, GoodEvs x₀ (evPrem p)
  | [], _ => by simp
  | p :: ps, h => by
    simp only [evPrems, goodEvs_append] at h
    intro p' hp'
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact h.1
    · exact goodEvs_prems h.2 p' hp'

theorem goodEvs_fields : ∀ {fs : List ExpField}, GoodEvs x₀ (evEFields fs) →
    ∀ a e, ExpField.mk a e ∈ fs → GoodEvs x₀ (evExp e)
  | [], _ => by simp
  | .mk a e :: fs, h => by
    simp only [evEFields, goodEvs_cons, goodEvs_append] at h
    intro a' e' he'
    rcases List.mem_cons.1 he' with he' | he'
    · cases he'; exact h.2.1
    · exact goodEvs_fields h.2.2 a' e' he'

/-- **A list whose references avoid `(1, x₀)` is `GoodEvs x₀`.** -/
theorem goodEvs_of_not_mem {l : List Ev} (h : (1, x₀) ∉ evRefs l) : GoodEvs x₀ l := by
  intro e he
  cases e with
  | ref k x =>
    rcases k with _ | _ | k
    · trivial
    · intro hx
      subst hx
      exact h (mem_evRefs he)
    · trivial
  | atom a => trivial
  | comp => trivial
  | upd r ats => trivial

/-! ## Scopes -/

theorem defsOk_empty : DefsOk x₀ VarEnv.empty := by simp [DefsOk, VarEnv.empty, Map.empty]

theorem defsOk_of_defs {ρ ρ' : VarEnv} (h : DefsOk x₀ ρ) (he : ρ'.defs = ρ.defs) :
    DefsOk x₀ ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem defsOk_bindVal {ρ : VarEnv} (h : DefsOk x₀ ρ) (x : IL.Id) (v : Value) :
    DefsOk x₀ (ρ.bindVal x v) := h

theorem defsOk_bindVals {ρ : VarEnv} (h : DefsOk x₀ ρ) (xs : List (IL.Id × Value)) :
    DefsOk x₀ (ρ.bindVals xs) := h

theorem defsOk_bindTyp {ρ : VarEnv} (h : DefsOk x₀ ρ) (x : IL.Id) (t : Typ) :
    DefsOk x₀ (ρ.bindTyp x t) := h

theorem defsOk_bindGram {ρ : VarEnv} (h : DefsOk x₀ ρ) (x : IL.Id) (g : Sym) :
    DefsOk x₀ (ρ.bindGram x g) := h

theorem defsOk_bindDef {ρ : VarEnv} (h : DefsOk x₀ ρ) (x : IL.Id) {y : IL.Id} (hy : y ≠ x₀) :
    DefsOk x₀ (ρ.bindDef x y) := by
  intro p hp
  simp only [VarEnv.bindDef, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact hy
    · exact h p hp

theorem goodName_resolve {ρ : VarEnv} (h : DefsOk x₀ ρ) {x : IL.Id} (hx : x ≠ x₀) :
    (ρ.findDef? x).getD x ≠ x₀ := by
  cases hf : ρ.findDef? x with
  | none => exact hx
  | some y => exact h (x, y) (mem_of_find? hf)

theorem matchArg_defsOk {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg} {w : ArgV}
    (h : DefsOk x₀ ρ) (hw : ArgOk x₀ w) (hm : matchArg n env ρ a w = .ok ρ') : DefsOk x₀ ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact defsOk_of_defs h ((defsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact defsOk_of_defs h (matchTypV_defs hm)
  case defA.defName y x => cases hm; exact defsOk_bindDef h y hw
  case gramA.gram => exact defsOk_of_defs h (matchSymV_defs hm)
  all_goals cases hm

theorem matchArgs_defsOk {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, DefsOk x₀ ρ →
      (∀ w ∈ ws, ArgOk x₀ w) → matchArgs n env ρ ags ws = .ok ρ' → DefsOk x₀ ρ'
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
        exact matchArgs_defsOk n (matchArg_defsOk h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

theorem bindParams_defsOk : ∀ {ρ ρ' : VarEnv} {ps : List Param} {ws : List ArgV},
    DefsOk x₀ ρ → (∀ w ∈ ws, ArgOk x₀ w) → bindParams ρ ps ws = some ρ' → DefsOk x₀ ρ'
  | ρ, ρ', [], [], h, _, hb => by
    simp only [bindParams, Option.some.injEq] at hb; subst hb; exact h
  | ρ, ρ', .expP x _ :: ps, .val v :: ws, h, hw, hb => by
    simp only [bindParams] at hb
    exact bindParams_defsOk (defsOk_bindVal h x v)
      (fun w hw' => hw w (List.mem_cons_of_mem _ hw')) hb
  | ρ, ρ', .typP x :: ps, .typ t :: ws, h, hw, hb => by
    simp only [bindParams] at hb
    exact bindParams_defsOk (defsOk_bindTyp h x t)
      (fun w hw' => hw w (List.mem_cons_of_mem _ hw')) hb
  | ρ, ρ', .defP x _ _ :: ps, .defName y :: ws, h, hw, hb => by
    simp only [bindParams] at hb
    exact bindParams_defsOk (defsOk_bindDef h x (hw _ List.mem_cons_self))
      (fun w hw' => hw w (List.mem_cons_of_mem _ hw')) hb
  | ρ, ρ', .gramP x _ _ :: ps, .gram g :: ws, h, hw, hb => by
    simp only [bindParams] at hb
    exact bindParams_defsOk (defsOk_bindGram h x g)
      (fun w hw' => hw w (List.mem_cons_of_mem _ hw')) hb
  | _, _, [], _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, _ :: _, [], _, _, hb => by simp [bindParams] at hb
  | _, _, .expP _ _ :: _, .typ _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .expP _ _ :: _, .defName _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .expP _ _ :: _, .gram _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .typP _ :: _, .val _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .typP _ :: _, .defName _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .typP _ :: _, .gram _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .defP _ _ _ :: _, .val _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .defP _ _ _ :: _, .typ _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .defP _ _ _ :: _, .gram _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .gramP _ _ _ :: _, .val _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .gramP _ _ _ :: _, .typ _ :: _, _, _, hb => by simp [bindParams] at hb
  | _, _, .gramP _ _ _ :: _, .defName _ :: _, _, _, hb => by simp [bindParams] at hb

/-- **Evaluated arguments are `ArgOk x₀`.** -/
theorem evalArgs_argOk {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg} {ws : List ArgV}
    (h : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evArgs ags)) (he : evalArgs n env ρ ags = .ok ws) :
    ∀ w ∈ ws, ArgOk x₀ w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := mapM_ok_mem he w hw
  have hGa := goodEvs_args hG a ha
  rcases n with _ | n
  · simp [evalArg] at hfa
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA => cases hfa; trivial
  case defA x =>
    cases hfa
    simp only [evArg, goodEvs_cons, goodEv_ref1, goodEvs_nil, and_true] at hGa
    exact goodName_resolve h hGa
  case gramA => cases hfa; trivial

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
