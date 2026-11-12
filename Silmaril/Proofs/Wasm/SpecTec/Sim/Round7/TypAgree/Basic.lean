module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Good
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.TypAgree.CheckA
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.TypAgree.CheckB
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.TypAgree.CheckR
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.TypAgree.Pres

/-!
# Round 7: the invariants of the typing agreement

What `Raw/…/Round7/TypAgree/Agree.lean` threads through `Sem.hasTyp`:

* the checks imply pass 7's `GoodEvs` (`goodEvs_of_goodEvsB`, `goodEvs_of_tyOk`,
  `goodEvs_of_argsOk`), so the evaluator agreement `Round7.Script.agreeAt` applies to every
  expression inside a checked type;
* `tyOk` is monotone in the set of names (`tyOk_mono`), and `tyA ⊆ tyB` (`tyA_sub_tyB`);
* the defining conjuncts of a checked variant case are harmless and typed over `tyA`
  (`quantDefs_ok`);
* `TypsOk` survives what typing does to a scope (`typsOk_caseScope`, `matchArgs_typsOk`), and
  evaluated type arguments are over `tyA` (`evalArgs_argTyOk`);
* every type `simEnv B` finds under a checked name is checked (`instsOk_of_findTyp`, from the
  kernel facts `typMapOk_A`, `typMapOk_B`);
* `ExpFree` passes to the parts of a value (`ValInv`, `valInv_expFree`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script

/-! ## The checks imply `GoodEvs` -/

theorem goodEvs_of_goodEvsB {l : List Ev} (h : goodEvsB l = true) : GoodEvs l := by
  intro e he
  have := List.all_eq_true.1 h e he
  match e, this with
  | .ref 1 x, h' =>
    simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at h'
    exact ⟨h'.1, h'.2⟩
  | .ref 0 x, h' => simpa [List.contains_iff_mem] using h'
  | .ref (k + 2) x, _ => trivial
  | .atom _, _ => trivial
  | .comp, _ => trivial
  | .upd _ _, _ => trivial

mutual
theorem goodEvs_of_tyOk {A S : List String} : ∀ {t : Typ}, tyOk A S t = true → GoodEvs (evTyp t)
  | .varT x args, h => by
    simp only [tyOk, Bool.and_eq_true] at h
    simp only [evTyp, goodEvs_cons, goodEv_ref2, true_and]
    exact goodEvs_of_argsOk h.2
  | .tupT bs, h => by
    simp only [tyOk] at h
    simp only [evTyp]
    exact goodEvs_of_bindsOk h
  | .iterT t it, h => by
    simp only [tyOk, Bool.and_eq_true] at h
    simp only [evTyp, goodEvs_append]
    exact ⟨goodEvs_of_tyOk h.1, goodEvs_of_goodEvsB h.2⟩
  | .boolT, _ => by simp [evTyp]
  | .numT _, _ => by simp [evTyp]
  | .textT, _ => by simp [evTyp]

theorem goodEvs_of_argsOk {A : List String} : ∀ {args : List Arg}, argsOk A args = true →
    GoodEvs (evArgs args)
  | [], _ => by simp [evArgs]
  | .typA t :: r, h => by
    simp only [argsOk, Bool.and_eq_true] at h
    simp only [evArgs, evArg, goodEvs_append]
    exact ⟨goodEvs_of_tyOk h.1, goodEvs_of_argsOk h.2⟩
  | .expA e :: r, h => by
    simp only [argsOk, Bool.and_eq_true] at h
    simp only [evArgs, evArg, goodEvs_append]
    exact ⟨goodEvs_of_goodEvsB h.1, goodEvs_of_argsOk h.2⟩
  | .defA _ :: _, h => by simp [argsOk] at h
  | .gramA _ :: _, h => by simp [argsOk] at h

theorem goodEvs_of_bindsOk {A S : List String} : ∀ {bs : List TypBind}, bindsOk A S bs = true →
    GoodEvs (evBinds bs)
  | [], _ => by simp [evBinds]
  | .mk _ t :: bs, h => by
    simp only [bindsOk, Bool.and_eq_true] at h
    simp only [evBinds, goodEvs_append]
    exact ⟨goodEvs_of_tyOk h.1, goodEvs_of_bindsOk h.2⟩
end

/-! ## Monotonicity in the set of names -/

mutual
theorem tyOk_mono {A S₁ S₂ : List String} (hS : ∀ x, S₁.contains x = true → S₂.contains x = true) :
    ∀ {t : Typ}, tyOk A S₁ t = true → tyOk A S₂ t = true
  | .varT x args, h => by
    simp only [tyOk, Bool.and_eq_true] at h ⊢
    exact ⟨hS x h.1, h.2⟩
  | .tupT bs, h => by
    simp only [tyOk] at h ⊢
    exact bindsOk_mono hS h
  | .iterT t it, h => by
    simp only [tyOk, Bool.and_eq_true] at h ⊢
    exact ⟨tyOk_mono hS h.1, h.2⟩
  | .boolT, _ => by simp [tyOk]
  | .numT _, _ => by simp [tyOk]
  | .textT, _ => by simp [tyOk]

theorem bindsOk_mono {A S₁ S₂ : List String}
    (hS : ∀ x, S₁.contains x = true → S₂.contains x = true) :
    ∀ {bs : List TypBind}, bindsOk A S₁ bs = true → bindsOk A S₂ bs = true
  | [], _ => by simp [bindsOk]
  | .mk _ t :: bs, h => by
    simp only [bindsOk, Bool.and_eq_true] at h ⊢
    exact ⟨tyOk_mono hS h.1, bindsOk_mono hS h.2⟩
end

theorem tyA_sub_tyB (x : String) (h : tyA.contains x = true) : tyB.contains x = true := by
  simp only [tyB, List.contains_append, h, Bool.true_or]

theorem tyA_sub_tyA (x : String) (h : tyA.contains x = true) : tyA.contains x = true := h

/-! ## Defining conjuncts of variant cases -/

theorem quantOf_mem {qs : List Param} {e : Exp} {x : IL.Id} {t : Typ}
    (h : quantOf qs e = some (x, t)) : Param.expP x t ∈ qs := by
  cases e <;> simp only [quantOf, reduceCtorEq] at h
  rename_i y
  induction qs with
  | nil => simp at h
  | cons q qs ih =>
    rw [List.findSome?_cons] at h
    cases q with
    | expP z t' =>
      by_cases hz : z = y
      · subst hz
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact List.mem_cons_self
      · simp only [hz, ↓reduceIte] at h
        exact List.mem_cons_of_mem _ (ih h)
    | typP _ => exact List.mem_cons_of_mem _ (ih h)
    | defP _ _ _ => exact List.mem_cons_of_mem _ (ih h)
    | gramP _ _ _ => exact List.mem_cons_of_mem _ (ih h)

theorem quantEqs_ok {qs : List Param} {e : Exp} (hG : GoodEvs (evExp e)) :
    ∀ d ∈ quantEqs qs e, GoodEvs (evExp d.2.2) ∧ Param.expP d.1 d.2.1 ∈ qs := by
  fun_induction quantEqs qs e with
  | case1 τ a b iha ihb =>
    have hG' : GoodEvs (evExp a) ∧ GoodEvs (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    rcases List.mem_append.1 hd with hd₁ | hd₂
    · exact iha hG'.1 d hd₁
    · exact ihb hG'.2 d hd₂
  | case2 τ a b x t hq =>
    have hG' : GoodEvs (evExp a) ∧ GoodEvs (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    have hd' : d = (x, t, a) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨hG'.1, quantOf_mem hq⟩
  | case3 τ a b _ x t hq =>
    have hG' : GoodEvs (evExp a) ∧ GoodEvs (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    have hd' : d = (x, t, b) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨hG'.2, quantOf_mem hq⟩
  | case4 => intro d hd; simp at hd
  | case5 => intro d hd; simp at hd

theorem quantDefs_ok {A : List String} {qs : List Param} {prems : List Prem}
    (hG : GoodEvs (evPrems prems)) (hq : quantsOk A A qs = true) :
    ∀ d ∈ quantDefs qs prems, GoodEvs (evExp d.2.2) ∧ tyOk A A d.2.1 = true := by
  intro d hd
  simp only [quantDefs, List.mem_flatMap] at hd
  obtain ⟨pr, hpr, hd⟩ := hd
  have hGpr := goodEvs_prems hG pr hpr
  cases pr with
  | ifPr e =>
    simp only [evPrem] at hGpr
    obtain ⟨h₁, h₂⟩ := quantEqs_ok hGpr d hd
    refine ⟨h₁, ?_⟩
    have := List.all_eq_true.1 hq _ h₂
    simpa using this
  | rulePr _ _ _ _ => simp at hd
  | letPr _ _ => simp at hd
  | elsePr => simp at hd
  | iterPr _ _ => simp at hd

/-! ## Scopes -/

theorem typsOk_empty (A : List String) : TypsOk A VarEnv.empty := by
  simp [TypsOk, VarEnv.empty, Map.empty]

theorem typsOk_of_typs {A : List String} {ρ ρ' : VarEnv} (h : TypsOk A ρ)
    (he : ρ'.typs = ρ.typs) : TypsOk A ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem typBinds_typs : ∀ (ρ : VarEnv) (bs : List TypBind) (vs : List Value),
    (typBinds ρ bs vs).typs = ρ.typs ∧ (typBinds ρ bs vs).defs = ρ.defs
  | ρ, .mk x _ :: bs, v :: vs => by
    simp only [typBinds]
    exact typBinds_typs (ρ.bindVal x v) bs vs
  | _, [], _ => by simp [typBinds]
  | _, _ :: _, [] => by simp [typBinds]

theorem caseScope_typs (ρ : VarEnv) (t : Typ) (w : Value) :
    (caseScope ρ t w).typs = ρ.typs ∧ (caseScope ρ t w).defs = ρ.defs := by
  unfold caseScope
  split
  · exact typBinds_typs _ _ _
  · exact ⟨rfl, rfl⟩

theorem bindQuants_typs {ev : VarEnv → Exp → Res Value} {ty : VarEnv → Typ → Value → Res Bool} :
    ∀ (ρ : VarEnv) (ds : List (IL.Id × Typ × Exp)) (ρ' : VarEnv),
      bindQuants ev ty ρ ds = .ok (some ρ') → ρ'.typs = ρ.typs ∧ ρ'.defs = ρ.defs
  | ρ, [], ρ', h => by
    simp only [bindQuants, Except.ok.injEq, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl⟩
  | ρ, (x, t, e) :: ds, ρ', h => by
    simp only [bindQuants, Res.bind_eq_ok] at h
    obtain ⟨v, _, b, _, h⟩ := h
    cases b
    · simp at h
    · exact bindQuants_typs (ρ.bindVal x v) ds ρ' h

/-- A type argument over `A`. -/
def ArgTyOk (A : List String) : ArgV → Prop
  | .typ t => tyOk A A t = true
  | _ => True

theorem typsOk_bindTyp {A : List String} {ρ : VarEnv} (h : TypsOk A ρ) (x : IL.Id) {t : Typ}
    (ht : tyOk A A t = true) : TypsOk A (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ht
    · exact h p hp

theorem matchTypV_typsOk {A : List String} {env : Env} {ρ ρ' : VarEnv} {pat t : Typ}
    (h : TypsOk A ρ) (ht : tyOk A A t = true) (hm : matchTypV env ρ pat t = .ok ρ') :
    TypsOk A ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) | (cases hm; exact typsOk_bindTyp h _ ht) |
    (cases hm))

theorem matchSymV_typs {env : Env} {ρ ρ' : VarEnv} {pat g : Sym}
    (h : matchSymV env ρ pat g = .ok ρ') : ρ'.typs = ρ.typs := by
  unfold matchSymV at h
  repeat (first | (split at h) | (cases h; rfl) | (cases h))

theorem matchArg_typsOk {A : List String} {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg}
    {w : ArgV} (h : TypsOk A ρ) (hw : ArgTyOk A w) (hm : matchArg n env ρ a w = .ok ρ') :
    TypsOk A ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact typsOk_of_typs h ((typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_typsOk h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact typsOk_of_typs h (matchSymV_typs hm)
  all_goals cases hm

theorem matchArgs_typsOk {A : List String} {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, TypsOk A ρ →
      (∀ w ∈ ws, ArgTyOk A w) → matchArgs n env ρ ags ws = .ok ρ' → TypsOk A ρ'
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
        exact matchArgs_typsOk n (matchArg_typsOk h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

theorem resolveTyp_ok {A : List String} {ρ : VarEnv} (h : TypsOk A ρ) {t : Typ}
    (ht : tyOk A A t = true) : tyOk A A (resolveTyp ρ t) = true := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (mem_of_find? hf)
  · exact ht

theorem argsOk_typA {A : List String} {t : Typ} :
    ∀ {ags : List Arg}, argsOk A ags = true → Arg.typA t ∈ ags → tyOk A A t = true
  | [], _, ha => by simp at ha
  | b :: ags, hA, ha => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · simp only [argsOk, Bool.and_eq_true] at hA; exact hA.1
    · cases b <;> simp only [argsOk, Bool.and_eq_true, Bool.false_eq_true] at hA
      · exact argsOk_typA hA.2 ha'
      · exact argsOk_typA hA.2 ha'

/-- **Evaluated type arguments are over `A`.** -/
theorem evalArgs_argTyOk {A : List String} {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg}
    {ws : List ArgV} (h : TypsOk A ρ) (hA : argsOk A ags = true)
    (he : evalArgs n env ρ ags = .ok ws) : ∀ w ∈ ws, ArgTyOk A w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := mapM_ok_mem he w hw
  rcases n with _ | n
  · simp [evalArg] at hfa
  have hAa : ∀ t, a = .typA t → tyOk A A t = true := fun t hat => argsOk_typA hA (hat ▸ ha)
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA t => cases hfa; exact resolveTyp_ok h (hAa t rfl)
  case defA x => cases hfa; trivial
  case gramA => cases hfa; trivial

/-! ## Types found under a checked name -/

theorem mem_typs_of_findTyp {B : Builtins} {x : IL.Id} {v : TypDef}
    (h : (simEnv B).findTyp? x = some v) :
    (x, v) ∈ typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed := by
  unfold simEnv baseEnv at h
  rw [show ∀ (e : Env), (e.withBuiltins B).findTyp? x = e.findTyp? x from fun _ => rfl] at h
  rw [envOfScript, envOfDefs_eq] at h
  have hm := mem_of_find? h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

theorem instsOk_of_typMapOk {A S : List String} {b : Bool} {m : Map TypDef}
    (hm : typMapOk A S b m = true) {x : IL.Id} {v : TypDef} (hx : (x, v) ∈ m)
    (hS : S.contains x = true) : instsOk A S b v.2 = true := by
  have := List.all_eq_true.1 hm _ hx
  simp only [hS, Bool.not_true, Bool.false_or] at this
  exact this

/-- **A type `simEnv B` finds under a name of `tyA` is over `tyA`.** -/
theorem instsOk_A {B : Builtins} {x : IL.Id} {v : TypDef} (h : (simEnv B).findTyp? x = some v)
    (hS : tyA.contains x = true) : instsOk tyA tyA false v.2 = true :=
  instsOk_of_typMapOk typMapOk_A (mem_typs_of_findTyp h) hS

/-- **A type `simEnv B` finds under a name of `tyB` is over `tyB`**, with the `EXPORTS`
exemption. -/
theorem instsOk_B {B : Builtins} {x : IL.Id} {v : TypDef} (h : (simEnv B).findTyp? x = some v)
    (hS : tyB.contains x = true) : instsOk tyA tyB true v.2 = true :=
  instsOk_of_typMapOk typMapOk_B (mem_typs_of_findTyp h) hS

/-! ## Values -/

/-- **What the agreement needs of the values it is run at**: the predicate `P` passes to the
parts that typing looks at, and with `b`, a record's `EXPORTS` field is `[]`. -/
structure ValInv (b : Bool) (P : Value → Prop) : Prop where
  tup : ∀ v vs, P v → v.asTuple? = some vs → ∀ w ∈ vs, P w
  opt : ∀ v w, P v → v.asOpt? = some (some w) → P w
  list : ∀ v vs, P v → v.asList? = some vs → ∀ w ∈ vs, P w
  struct : ∀ v gs, P v → v.asStruct? = some gs → ∀ p ∈ gs, P p.2
  exps : b = true → ∀ v gs, P v → v.asStruct? = some gs → ∀ p ∈ gs, p.1 = "EXPORTS" →
    p.2 = .list []
  case : ∀ v op w, P v → v.asCase? = some (op, w) → P w

theorem valInv_true : ValInv false (fun _ => True) :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ => trivial, fun h => absurd h (by simp), fun _ _ _ _ _ => trivial⟩

theorem valInv_expFree : ValInv true ExpFree := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v vs hv h
    cases hv <;> simp only [Value.asTuple?, reduceCtorEq, Option.some.injEq] at h
    subst h; assumption
  · intro v w hv h
    cases hv <;> simp only [Value.asOpt?, reduceCtorEq, Option.some.injEq] at h
    subst h; rename_i hw; exact hw w rfl
  · intro v vs hv h
    cases hv <;> simp only [Value.asList?, reduceCtorEq, Option.some.injEq] at h
    subst h; assumption
  · intro v gs hv h
    cases hv <;> simp only [Value.asStruct?, reduceCtorEq, Option.some.injEq] at h
    subst h; assumption
  · intro _ v gs hv h
    cases hv <;> simp only [Value.asStruct?, reduceCtorEq, Option.some.injEq] at h
    subst h; assumption
  · intro v op w hv h
    cases hv <;> simp only [Value.asCase?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; assumption

end Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
