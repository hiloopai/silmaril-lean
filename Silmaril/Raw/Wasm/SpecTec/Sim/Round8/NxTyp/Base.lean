module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Erase.Thms

/-!
# Round 8, typing across erasure without a swap set: the bookkeeping (unrefined)

* `TypsTP S ρ`: every type variable of `ρ` is bound to an export-free type that passes `nTy S []`.
  It holds of the scopes that matching returns from such type arguments (`matchArgs_typsTP`), and
  evaluated type arguments are such (`evalArgs_argTP`).
* `Agr A ρ ρ'`: the two scopes bind the variables `A` alike and have the same type, definition
  and grammar variables. Expressions over `A` evaluate alike (`evalExp_agr`, `evalArgs_agr`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (nxAT toAT sigFixed TypsNx)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)

/-! ## Type variables -/

/-- An export-free type that passes the check over no variables. -/
def TP (S : List String) (t : Typ) : Prop := nTy S [] t = true ∧ nxT t = true

/-- **Every type variable is bound to an export-free checked type.** -/
def TypsTP (S : List String) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.typs, TP S p.2

/-- A type argument that is an export-free checked type. -/
def ArgTP (S : List String) : ArgV → Prop
  | .typ t => TP S t
  | _ => True

variable {S : List String}

theorem typsTP_empty : TypsTP S VarEnv.empty := fun _ hp => by cases hp

theorem typsTP_of_typs {ρ ρ' : VarEnv} (h : TypsTP S ρ) (he : ρ'.typs = ρ.typs) :
    TypsTP S ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem typsTP_bindVal {ρ : VarEnv} (h : TypsTP S ρ) (x : IL.Id) (v : Value) :
    TypsTP S (ρ.bindVal x v) :=
  typsTP_of_typs h rfl

theorem typsNx_of_TP {ρ : VarEnv} (h : TypsTP S ρ) : TypsNx sigFixed.good ρ :=
  fun p hp => (h p hp).2

theorem typsTP_bindTyp {ρ : VarEnv} (h : TypsTP S ρ) (x : IL.Id) {t : Typ} (ht : TP S t) :
    TypsTP S (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ht
    · exact h p hp

theorem matchTypV_typsTP {env : Env} {ρ ρ' : VarEnv} {pat t : Typ} (h : TypsTP S ρ) (ht : TP S t)
    (hm : matchTypV env ρ pat t = .ok ρ') : TypsTP S ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) | (cases hm; exact typsTP_bindTyp h _ ht) |
    (cases hm))

theorem matchArg_typsTP {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg} {w : ArgV}
    (h : TypsTP S ρ) (hw : ArgTP S w) (hm : matchArg n env ρ a w = .ok ρ') : TypsTP S ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact typsTP_of_typs h ((TypAgree.typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_typsTP h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact typsTP_of_typs h (TypAgree.matchSymV_typs hm)
  all_goals cases hm

theorem matchArgs_typsTP {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, TypsTP S ρ →
      (∀ w ∈ ws, ArgTP S w) → matchArgs n env ρ ags ws = .ok ρ' → TypsTP S ρ'
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
        exact matchArgs_typsTP n (matchArg_typsTP h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

theorem resolveTyp_TP {ρ : VarEnv} (h : TypsTP S ρ) {t : Typ} (ht : TP S t) :
    TP S (resolveTyp ρ t) := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (Script.mem_of_find? hf)
  · exact ht

theorem nTyArgs_typA {A : List String} {t : Typ} :
    ∀ {ags : List Arg}, nTyArgs S A ags = true → Arg.typA t ∈ ags → TP S t
  | [], _, ha => by simp at ha
  | b :: ags, hA, ha => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · simp only [nTyArgs, Bool.and_eq_true] at hA; exact ⟨hA.1.1.2, hA.1.2⟩
    · cases b <;> simp only [nTyArgs, Bool.and_eq_true, Bool.false_eq_true] at hA
      · exact nTyArgs_typA hA.2 ha'
      · exact nTyArgs_typA hA.2 ha'

/-- **Evaluated type arguments are export-free checked types.** -/
theorem evalArgs_argTP {env : Env} {n : Nat} {ρ : VarEnv} {A : List String} {ags : List Arg}
    {ws : List ArgV} (h : TypsTP S ρ) (hA : nTyArgs S A ags = true)
    (he : evalArgs n env ρ ags = .ok ws) : ∀ w ∈ ws, ArgTP S w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := Script.mapM_ok_mem he w hw
  rcases n with _ | n
  · simp [evalArg] at hfa
  have hAa : ∀ t, a = .typA t → TP S t := fun t hat => nTyArgs_typA hA (hat ▸ ha)
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA t => cases hfa; exact resolveTyp_TP h (hAa t rfl)
  case defA x => cases hfa; trivial
  case gramA => cases hfa; trivial

/-! ## Scopes that agree on `A` -/

/-- **`ρ` and `ρ'` bind the variables `A` alike**, and have the same type, definition and grammar
variables. -/
structure Agr (A : List String) (ρ ρ' : VarEnv) : Prop where
  vals : ∀ x ∈ A, ρ'.findVal? x = ρ.findVal? x
  typs : ρ'.typs = ρ.typs
  defs : ρ'.defs = ρ.defs
  grams : ρ'.grams = ρ.grams

theorem agr_refl (A : List String) (ρ : VarEnv) : Agr A ρ ρ :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Agr.nil {A : List String} {ρ ρ' : VarEnv} (h : Agr A ρ ρ') : Agr [] ρ ρ' :=
  ⟨fun _ hx => (by cases hx), h.typs, h.defs, h.grams⟩

theorem varsIn_mem {K : List IL.Id} {s : Sets} (h : varsIn K s = true) :
    ∀ x ∈ s.varid, x ∈ K := by
  simpa [varsIn] using h

/-- **Agreement on `A` is agreement on every set whose variables are in `A`.** -/
theorem Agr.agreeOn {A : List String} {ρ ρ' : VarEnv} (h : Agr A ρ ρ') {s : Sets}
    (hs : varsIn A s = true) : VarEnv.AgreeOn s ρ ρ' := by
  refine ⟨fun x hx => (h.vals x (varsIn_mem hs x hx)).symm, fun x _ => ?_, fun x _ => ?_,
    fun x _ => ?_⟩
  · show Map.find? ρ.typs x = Map.find? ρ'.typs x; rw [h.typs]
  · show Map.find? ρ.defs x = Map.find? ρ'.defs x; rw [h.defs]
  · show Map.find? ρ.grams x = Map.find? ρ'.grams x; rw [h.grams]

theorem evalExp_agr {n : Nat} {env : Env} {A : List String} {ρ ρ' : VarEnv} (h : Agr A ρ ρ')
    {e : Exp} (he : varsIn A (freeExp e) = true) :
    evalExp n env ρ' e = evalExp n env ρ e :=
  (evalExp_agreeOn (h.agreeOn he)).symm

theorem varsIn_union {A : List String} {s t : Sets} (hs : varsIn A s = true)
    (ht : varsIn A t = true) : varsIn A (s.union t) = true := by
  simp only [varsIn, decide_eq_true_eq] at hs ht ⊢
  intro x hx
  simp only [Sets.union, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact hs x hx
  · exact ht x hx

theorem varsIn_nil_sub {A : List String} {s : Sets} (h : varsIn [] s = true) :
    varsIn A s = true := by
  simp only [varsIn, decide_eq_true_eq] at h ⊢
  intro x hx
  exact absurd (h x hx) (by simp)

/-- The arguments of a checked type name read only `A`. -/
theorem varsIn_freeArgs {A : List String} :
    ∀ {ags : List Arg}, nTyArgs S A ags = true → varsIn A (freeArgs ags) = true
  | [], _ => by simp [varsIn, freeArgs, Sets.empty]
  | b :: ags, hA => by
    cases b <;> simp only [nTyArgs, Bool.and_eq_true, Bool.false_eq_true] at hA
    · exact varsIn_union hA.1 (varsIn_freeArgs hA.2)
    · exact varsIn_union (varsIn_nil_sub hA.1.1.1) (varsIn_freeArgs hA.2)

theorem evalArgs_agr {n : Nat} {env : Env} {A : List String} {ρ ρ' : VarEnv} (h : Agr A ρ ρ')
    {ags : List Arg} (hA : nTyArgs S A ags = true) :
    evalArgs n env ρ' ags = evalArgs n env ρ ags :=
  (evalArgs_agreeOn (h.agreeOn (varsIn_freeArgs hA))).symm

theorem localTyp?_agr {A : List String} {ρ ρ' : VarEnv} (h : Agr A ρ ρ') (x : IL.Id)
    (args : List Arg) : localTyp? ρ' x args = localTyp? ρ x args := by
  cases args with
  | nil => simp only [localTyp?, VarEnv.findTyp?, h.typs]
  | cons _ _ => rfl

/-- **Binding a value and its erasure.** An export-free value is its own erasure, so its binder
joins `A`; otherwise the binder leaves `A`. -/
theorem Agr.bind {A : List String} {ρ ρ' : VarEnv} (h : Agr A ρ ρ') (x : IL.Id) (t : Typ)
    {v : Value} (hv : nxT t = true → Swap.nxB v = true) :
    Agr (if nxT t && x != "_" then x :: A else A.filter (· != x))
      (ρ.bindVal x v) (ρ'.bindVal x (Swap.eraseV v)) := by
  refine ⟨fun y hy => ?_, h.typs, h.defs, h.grams⟩
  simp only [VarEnv.findVal?, VarEnv.bindVal]
  by_cases hc : (nxT t && x != "_") = true
  · simp only [hc, ↓reduceIte] at hy
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [Map.find?_bind_self _ hc.2, Map.find?_bind_self _ hc.2,
        Swap.eraseV_of_nxB _ (hv hc.1)]
    · by_cases hxy : x = y
      · subst hxy
        rw [Map.find?_bind_self _ hc.2, Map.find?_bind_self _ hc.2,
          Swap.eraseV_of_nxB _ (hv hc.1)]
      · rw [Map.find?_bind_of_ne _ hxy, Map.find?_bind_of_ne _ hxy]
        exact h.vals y hy
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hy
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hy
    have hxy : x ≠ y := fun e => hy.2 e.symm
    rw [Map.find?_bind_of_ne _ hxy, Map.find?_bind_of_ne _ hxy]
    exact h.vals y hy.1

end Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp
