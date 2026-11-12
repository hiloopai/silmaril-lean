module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Env
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Script.Pres

/-!
# Round 7: well-behaved terms and scopes for the `simEnv`/`utf8Env` agreement

The invariants that `Round7/Script/Agree.lean` threads through the evaluator:

* `GoodEvs l`: every definition referred to in `l` is reachable and is not `$utf8`
  (`GoodName`), and every relation referred to is reachable. `goodEvs_of_reach` gives it for
  the body of every reachable definition, relation and type other than `$utf8` and `name`.
* `DefsOk ρ`: every definition variable of `ρ` names a `GoodName` definition. `ArgOk w`: a
  definition argument names a `GoodName` definition.
* These survive what the evaluator does to a scope: binding values (`defsOk_bindVal`,
  `defsOk_bindVals`), matching and premises (`Round7.Script.defsPres`), matching an argument list
  (`matchArgs_defsOk`) and binding a relation's parameters (`bindParams_defsOk`). Evaluated
  arguments are `ArgOk` (`evalArgs_argOk`).

The monotonicity helpers `bind_le_of`, `mapM_le_of`, `foldlM_le_of` and `elimUndef_le_of`
restrict the usual ones to the answers that actually occur.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Script

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open scoped Silmaril.SpecTec.Sem.Res

/-! ## The invariants -/

/-- A reachable definition other than `$utf8`. -/
def GoodName (y : String) : Prop := (1, y) ∈ stepReach ∧ y ≠ "utf8"

/-- A harmless event for the agreement: a definition reference is `GoodName`, a relation
reference is reachable. -/
def GoodEv : Ev → Prop
  | .ref 1 x => GoodName x
  | .ref 0 x => (0, x) ∈ stepReach
  | _ => True

/-- Every event of `l` is `GoodEv`. -/
def GoodEvs (l : List Ev) : Prop := ∀ e ∈ l, GoodEv e

/-- Every definition variable of `ρ` names a `GoodName` definition. -/
def DefsOk (ρ : VarEnv) : Prop := ∀ p ∈ ρ.defs, GoodName p.2

/-- A definition argument names a `GoodName` definition. -/
def ArgOk : ArgV → Prop
  | .defName y => GoodName y
  | _ => True

@[simp] theorem goodEvs_nil : GoodEvs [] := by simp [GoodEvs]

@[simp] theorem goodEvs_cons {e : Ev} {l : List Ev} : GoodEvs (e :: l) ↔ GoodEv e ∧ GoodEvs l := by
  simp [GoodEvs]

@[simp] theorem goodEvs_append {l₁ l₂ : List Ev} : GoodEvs (l₁ ++ l₂) ↔ GoodEvs l₁ ∧ GoodEvs l₂ := by
  simp only [GoodEvs, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

@[simp] theorem goodEv_atom (a : String) : GoodEv (.atom a) ↔ True := Iff.rfl
@[simp] theorem goodEv_comp : GoodEv .comp ↔ True := Iff.rfl
@[simp] theorem goodEv_upd (r : Exp) (ats : List String) : GoodEv (.upd r ats) ↔ True := Iff.rfl
@[simp] theorem goodEv_ref1 (x : String) : GoodEv (.ref 1 x) ↔ GoodName x := Iff.rfl
@[simp] theorem goodEv_ref0 (x : String) : GoodEv (.ref 0 x) ↔ (0, x) ∈ stepReach := Iff.rfl
@[simp] theorem goodEv_ref2 (x : String) : GoodEv (.ref 2 x) ↔ True := Iff.rfl
@[simp] theorem goodEv_ref3 (x : String) : GoodEv (.ref 3 x) ↔ True := Iff.rfl

@[simp] theorem goodEvs_flatMap {α : Type} {f : α → List Ev} {l : List α} :
    GoodEvs (l.flatMap f) ↔ ∀ x ∈ l, GoodEvs (f x) := by
  simp only [GoodEvs, List.mem_flatMap]
  exact ⟨fun h x hx e he => h e ⟨x, hx, he⟩, fun h e ⟨x, hx, he⟩ => h x hx e he⟩

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

theorem mem_evRefs : ∀ {l : List Ev} {k : Nat} {x : String}, Ev.ref k x ∈ l → (k, x) ∈ evRefs l
  | [], _, _, h => by simp at h
  | e :: l, k, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [evRefs]
    · have := mem_evRefs h
      cases e <;> simp [evRefs, this]

/-- **The body of a reachable item other than `$utf8` and `name` is `GoodEvs`.** -/
theorem goodEvs_of_reach {n : Nat × String} (hn : n ∉ utf8Allowed) {l : List Ev}
    (hR : ∀ r ∈ evRefs l, r ∈ stepReach) (hok : ∀ e ∈ l, evOk n e = true) : GoodEvs l := by
  intro e he
  cases e with
  | ref k x =>
    have hr := hR _ (mem_evRefs he)
    have ho := hok _ he
    rcases k with _ | _ | k
    · exact hr
    · refine ⟨hr, fun hx => ?_⟩
      subst hx
      simp [evOk, hn] at ho
    · trivial
  | atom a => trivial
  | comp => trivial
  | upd r ats => trivial

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

theorem matchTypV_defs {env : Env} {ρ ρ' : VarEnv} {pat t : Typ}
    (h : matchTypV env ρ pat t = .ok ρ') : ρ'.defs = ρ.defs := by
  unfold matchTypV at h
  repeat (first | (split at h) | (cases h; rfl) | (cases h))

theorem matchSymV_defs {env : Env} {ρ ρ' : VarEnv} {pat g : Sym}
    (h : matchSymV env ρ pat g = .ok ρ') : ρ'.defs = ρ.defs := by
  unfold matchSymV at h
  repeat (first | (split at h) | (cases h; rfl) | (cases h))

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

theorem mapM_ok_mem {α β : Type} {f : α → Res β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h => by simp only [List.mapM_nil] at h; cases h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Res.bind_eq_ok] at h
    obtain ⟨y₀, h₀, ys', h', hys⟩ := h
    cases hys
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, h₀⟩
    · obtain ⟨x', hx', hfx⟩ := mapM_ok_mem h' y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', hfx⟩

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

/-! ## Monotonicity restricted to the answers that occur -/

theorem bind_le_of {α β : Type} {r₁ r₂ : Res α} {f₁ f₂ : α → Res β} (hr : r₁ ⊑ r₂)
    (hf : ∀ a, r₁ = .ok a → f₁ a ⊑ f₂ a) : (r₁ >>= f₁) ⊑ (r₂ >>= f₂) := by
  rcases hr with hr | hr
  · subst hr; exact Or.inl rfl
  · subst hr
    cases r₂ with
    | error e => exact Or.inr rfl
    | ok a => exact hf a rfl

theorem mapM_le_of {α β : Type} {f₁ f₂ : α → Res β} :
    ∀ (xs : List α), (∀ a ∈ xs, f₁ a ⊑ f₂ a) → xs.mapM f₁ ⊑ xs.mapM f₂
  | [], _ => Res.Le.refl _
  | x :: xs, hf => by
    simp only [List.mapM_cons]
    exact Res.bind_le (hf x List.mem_cons_self) fun _ =>
      Res.bind_le (mapM_le_of xs fun a ha => hf a (List.mem_cons_of_mem _ ha)) fun _ =>
        Res.Le.refl _

theorem foldlM_le_of {α β : Type} {P : β → Prop} {f₁ f₂ : β → α → Res β} :
    ∀ (xs : List α), (∀ b a, P b → a ∈ xs → f₁ b a ⊑ f₂ b a) →
      (∀ b a b', P b → a ∈ xs → f₁ b a = .ok b' → P b') →
      ∀ b, P b → xs.foldlM f₁ b ⊑ xs.foldlM f₂ b
  | [], _, _, _, _ => Res.Le.refl _
  | x :: xs, hf, hP, b, hb => by
    simp only [List.foldlM_cons]
    exact bind_le_of (hf b x hb List.mem_cons_self) fun b' hb' =>
      foldlM_le_of xs (fun b a hb ha => hf b a hb (List.mem_cons_of_mem _ ha))
        (fun b a b'' hb ha => hP b a b'' hb (List.mem_cons_of_mem _ ha)) b'
        (hP b x b' hb List.mem_cons_self hb')

theorem elimUndef_le_of {α β : Type} {r₁ r₂ : Res α} {f₁ f₂ : α → Res β}
    {g₁ g₂ : Unit → Res β} (hr : r₁ ⊑ r₂) (hf : ∀ a, r₁ = .ok a → f₁ a ⊑ f₂ a)
    (hg : ∀ u, g₁ u ⊑ g₂ u) : Res.elimUndef r₁ f₁ g₁ ⊑ Res.elimUndef r₂ f₂ g₂ := by
  rcases hr with hr | hr
  · subst hr; exact Or.inl rfl
  · subst hr
    cases r₂ with
    | ok a => exact hf a rfl
    | error e => cases e with
      | undef => exact hg ()
      | outOfFuel => exact Or.inl rfl

theorem le_antisymm' {α : Type} {r₁ r₂ : Res α} (h₁ : r₁ ⊑ r₂) (h₂ : r₂ ⊑ r₁) : r₁ = r₂ := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · rw [h₁, h₂]
    · exact h₂
  · exact h₁.symm

end Silmaril.Wasm.SpecTec.Sim.Round7.Script
