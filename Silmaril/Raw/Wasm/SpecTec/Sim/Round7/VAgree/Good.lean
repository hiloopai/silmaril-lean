module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Reach

/-!
# Round 7, memory SIMD: the invariants of the `$vbytes_` agreement (unrefined)

Round 7's `Script/Good.lean` with `GoodName` excluding `$vbytes_` instead of `$utf8`, and relation
references restricted to `GoodRel` (reachable, not `Step` and not `Step_read`). The lemmas are
copied with that change: the scope invariants `DefsOk`/`ArgOk` survive binding, matching, relation
parameters and argument evaluation (`matchArgs_defsOk`, `bindParams_defsOk`, `evalArgs_argOk`).
The environment-independent helpers (`bind_le_of`, `defsPres`, …) are reused from
`Round7.Script`. Kept unrefined, like the original.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open scoped Silmaril.SpecTec.Sem.Res
open Round7.Script (Ev evExp evExps evOExp evEFields evPath evIterExp evIter evDoms evArg evArgs
  evPrem evPrems evClause evRule mem_of_find? defsPres matchTypV_defs matchSymV_defs mapM_ok_mem)

@[simp] theorem goodEvs_nil : GoodEvs [] := by simp [GoodEvs]

@[simp] theorem goodEvs_cons {e : Ev} {l : List Ev} : GoodEvs (e :: l) ↔ GoodEv e ∧ GoodEvs l := by
  simp [GoodEvs]

@[simp] theorem goodEv_atom (a : String) : GoodEv (.atom a) ↔ True := Iff.rfl
@[simp] theorem goodEv_comp : GoodEv .comp ↔ True := Iff.rfl
@[simp] theorem goodEv_upd (r : Exp) (ats : List String) : GoodEv (.upd r ats) ↔ True := Iff.rfl
@[simp] theorem goodEv_ref1 (x : String) : GoodEv (.ref 1 x) ↔ GoodName x := Iff.rfl
@[simp] theorem goodEv_ref0 (x : String) : GoodEv (.ref 0 x) ↔ GoodRel x := Iff.rfl
@[simp] theorem goodEv_ref2 (x : String) : GoodEv (.ref 2 x) ↔ True := Iff.rfl
@[simp] theorem goodEv_ref3 (x : String) : GoodEv (.ref 3 x) ↔ True := Iff.rfl

theorem goodEvs_exps : ∀ {es : List Exp}, GoodEvs (evExps es) → ∀ e ∈ es, GoodEvs (evExp e)
  | [], _ => by simp
  | e :: es, h => by
    simp only [evExps, goodEvs_append] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact goodEvs_exps h.2 e' he'

theorem goodEvs_doms : ∀ {ds : List Dom}, GoodEvs (evDoms ds) → ∀ e ∈ ds.map domSrc, GoodEvs (evExp e)
  | [], _ => by simp
  | .mk x e :: ds, h => by
    simp only [evDoms, goodEvs_append] at h
    intro e' he'
    simp only [List.map_cons, List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact h.1
    · exact goodEvs_doms h.2 e' he'

theorem goodEvs_doms' : ∀ {ds : List Dom}, GoodEvs (evDoms ds) → ∀ d ∈ ds, GoodEvs (evExp (domSrc d))
  | [], _ => by simp
  | .mk x e :: ds, h => by
    simp only [evDoms, goodEvs_append] at h
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact goodEvs_doms' h.2 d hd

theorem goodEvs_args : ∀ {ags : List Arg}, GoodEvs (evArgs ags) → ∀ a ∈ ags, GoodEvs (evArg a)
  | [], _ => by simp
  | a :: ags, h => by
    simp only [evArgs, goodEvs_append] at h
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact h.1
    · exact goodEvs_args h.2 a' ha'

theorem goodEvs_prems : ∀ {ps : List Prem}, GoodEvs (evPrems ps) → ∀ p ∈ ps, GoodEvs (evPrem p)
  | [], _ => by simp
  | p :: ps, h => by
    simp only [evPrems, goodEvs_append] at h
    intro p' hp'
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact h.1
    · exact goodEvs_prems h.2 p' hp'

theorem goodEvs_fields : ∀ {fs : List ExpField}, GoodEvs (evEFields fs) →
    ∀ a e, ExpField.mk a e ∈ fs → GoodEvs (evExp e)
  | [], _ => by simp
  | .mk a e :: fs, h => by
    simp only [evEFields, goodEvs_cons, goodEvs_append] at h
    intro a' e' he'
    rcases List.mem_cons.1 he' with he' | he'
    · cases he'; exact h.2.1
    · exact goodEvs_fields h.2.2 a' e' he'

/-! ## Scopes -/

theorem defsOk_empty : DefsOk VarEnv.empty := by simp [DefsOk, VarEnv.empty, Map.empty]

theorem defsOk_of_defs {ρ ρ' : VarEnv} (h : DefsOk ρ) (he : ρ'.defs = ρ.defs) : DefsOk ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem defsOk_bindVal {ρ : VarEnv} (h : DefsOk ρ) (x : IL.Id) (v : Value) :
    DefsOk (ρ.bindVal x v) := h

theorem defsOk_bindVals {ρ : VarEnv} (h : DefsOk ρ) (xs : List (IL.Id × Value)) :
    DefsOk (ρ.bindVals xs) := h

theorem defsOk_bindTyp {ρ : VarEnv} (h : DefsOk ρ) (x : IL.Id) (t : Typ) :
    DefsOk (ρ.bindTyp x t) := h

theorem defsOk_bindGram {ρ : VarEnv} (h : DefsOk ρ) (x : IL.Id) (g : Sym) :
    DefsOk (ρ.bindGram x g) := h

theorem defsOk_bindDef {ρ : VarEnv} (h : DefsOk ρ) (x : IL.Id) {y : IL.Id} (hy : GoodName y) :
    DefsOk (ρ.bindDef x y) := by
  intro p hp
  simp only [VarEnv.bindDef, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact hy
    · exact h p hp

theorem goodName_resolve {ρ : VarEnv} (h : DefsOk ρ) {x : IL.Id} (hx : GoodName x) :
    GoodName ((ρ.findDef? x).getD x) := by
  cases hf : ρ.findDef? x with
  | none => exact hx
  | some y => exact h (x, y) (mem_of_find? hf)

theorem matchArg_defsOk {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg} {w : ArgV}
    (h : DefsOk ρ) (hw : ArgOk w) (hm : matchArg n env ρ a w = .ok ρ') : DefsOk ρ' := by
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
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, DefsOk ρ →
      (∀ w ∈ ws, ArgOk w) → matchArgs n env ρ ags ws = .ok ρ' → DefsOk ρ'
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

theorem bindParams_defsOk : ∀ {ρ ρ' : VarEnv} {ps : List Param} {ws : List ArgV}, DefsOk ρ →
    (∀ w ∈ ws, ArgOk w) → bindParams ρ ps ws = some ρ' → DefsOk ρ'
  | ρ, ρ', [], [], h, _, hb => by simp only [bindParams, Option.some.injEq] at hb; subst hb; exact h
  | ρ, ρ', .expP x _ :: ps, .val v :: ws, h, hw, hb => by
    simp only [bindParams] at hb
    exact bindParams_defsOk (defsOk_bindVal h x v) (fun w hw' => hw w (List.mem_cons_of_mem _ hw')) hb
  | ρ, ρ', .typP x :: ps, .typ t :: ws, h, hw, hb => by
    simp only [bindParams] at hb
    exact bindParams_defsOk (defsOk_bindTyp h x t) (fun w hw' => hw w (List.mem_cons_of_mem _ hw')) hb
  | ρ, ρ', .defP x _ _ :: ps, .defName y :: ws, h, hw, hb => by
    simp only [bindParams] at hb
    exact bindParams_defsOk (defsOk_bindDef h x (hw _ List.mem_cons_self))
      (fun w hw' => hw w (List.mem_cons_of_mem _ hw')) hb
  | ρ, ρ', .gramP x _ _ :: ps, .gram g :: ws, h, hw, hb => by
    simp only [bindParams] at hb
    exact bindParams_defsOk (defsOk_bindGram h x g) (fun w hw' => hw w (List.mem_cons_of_mem _ hw')) hb
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

/-- **Evaluated arguments are `ArgOk`.** -/
theorem evalArgs_argOk {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg} {ws : List ArgV}
    (h : DefsOk ρ) (hG : GoodEvs (evArgs ags)) (he : evalArgs n env ρ ags = .ok ws) :
    ∀ w ∈ ws, ArgOk w := by
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

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
