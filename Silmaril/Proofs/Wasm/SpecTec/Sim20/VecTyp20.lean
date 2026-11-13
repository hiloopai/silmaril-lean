module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypEq
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypCheck
public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Thms
public import Silmaril.Wasm.SpecTec.Sim20.VecNum.Thms
public import Silmaril.Wasm.SpecTec.Sim20.StoreBulk.Thms

/-!
# State typing at `vecNB P` from `Good20B` at `storeB P`

* `defsGood_simEnv20T`, `typsGood_simEnv20T`: the kernel check `defsTypsOkB_fixedT20` read as
  `RelFree.DefsGood badV20` and `RelFree.TypsGood badV20` of `simEnv20T B`, at every `B`.
* **`bAgree_vecNB`**: `vecNB P` answers as `storeB P` away from `badV20`. The two differ at most
  at `$lanes_`, `$inv_lanes_` and the three dispatchers (`VecNum.vecNB_call_of_ne`,
  `VecLane.vecB_call_of_ne`).
* **`typedV_vecNB`**: a value typed in `simEnv20T (storeB P)` at a harmless type is typed in
  `simEnv20T (vecNB P)`; `state` and `admininstr*` are harmless (`goodEvs_varT`).
* **`state_vecNB_of_good20B`**, `code_vecNB_of_good20B`: the state and the code of a `Good20B`
  configuration are typed in `simEnv20T (vecNB P)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.RelFree (GoodEvs GoodName DefsGood TypsGood rfEvB)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evTyp evArgs evClause evInst items defDefEv typDefEv
  findDef?_envOfScript_item findTyp?_envOfScript_item)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T fixedT20)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.Whole (storeB)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB)

/-! ## The 2.0 tables -/

theorem findTyp?_withB (env : Env) (B : Builtins) (x : IL.Id) :
    (env.withBuiltins B).findTyp? x = env.findTyp? x :=
  rfl

theorem withBuiltins_withB (env : Env) (B B' : Builtins) :
    (env.withBuiltins B).withBuiltins B' = env.withBuiltins B' :=
  rfl

/-- An item of `fixedT20` that is a definition outside `badV20` or a type has harmless events. -/
theorem item_ok {k : Nat} {x : String} {l : List Ev} (hm : (k, x, l) ∈ items fixedT20)
    (hk : k = 2 ∨ (k = 1 ∧ badV20.contains x = false)) : GoodEvs badV20 l := by
  have h := List.all_eq_true.1 defsTypsOkB_fixedT20 _ hm
  intro e he
  rcases hk with rfl | ⟨rfl, hx⟩
  · exact List.all_eq_true.1 (by simpa using h) e he
  · simp only [hx] at h
    exact List.all_eq_true.1 (by simpa using h) e he

/-- **The definitions of `simEnv20T B` outside `badV20` are harmless.** -/
theorem defsGood_simEnv20T (B : Builtins) : DefsGood badV20 (simEnv20T B) := by
  intro x d hx hd c hc e he
  rw [simEnv20T, Env.findDef?_withBuiltins] at hd
  refine item_ok (findDef?_envOfScript_item hd) (Or.inr ⟨rfl, hx⟩) e ?_
  simp only [defDefEv, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨c, hc, he⟩

/-- **The types of `simEnv20T B` are harmless.** -/
theorem typsGood_simEnv20T (B : Builtins) : TypsGood badV20 (simEnv20T B) := by
  intro x td hd i hi e he
  rw [simEnv20T, findTyp?_withB] at hd
  refine item_ok (findTyp?_envOfScript_item hd) (Or.inl rfl) e ?_
  simp only [typDefEv, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨i, hi, he⟩

/-! ## The builtins -/

/-- **`vecNB P` answers as `storeB P` away from `badV20`.** -/
theorem bAgree_vecNB (P : Profile) : BAgree badV20 (storeB P) (vecNB P) := by
  intro x hx ws
  simp only [GoodName, badV20, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
  rw [VecNum.vecNB_call_of_ne hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1,
    VecLane.vecB_call_of_ne hx.2.2.1 hx.2.1]

/-- A type name without arguments is harmless. -/
theorem goodEvs_varT (x : String) : GoodEvs badV20 (evTyp (.varT x [])) := by
  intro e he
  simp only [evTyp, evArgs, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  rfl

theorem goodEvs_adminsTy : GoodEvs badV20 (evTyp adminsTy) := by
  intro e he
  simp only [evTyp, Silmaril.Wasm.SpecTec.Sim.Round7.Script.evIter, evArgs, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  rfl

/-- **Typing in `simEnv20T (storeB P)` at a harmless type holds in `simEnv20T (vecNB P)`.** -/
theorem typedV_vecNB {P : Profile} {t : Typ} {v : Value} (hG : GoodEvs badV20 (evTyp t))
    (h : TypedV (simEnv20T (storeB P)) t v) : TypedV (simEnv20T (vecNB P)) t v := by
  have hB : BAgree badV20 (simEnv20T (storeB P)).builtins (vecNB P) := by
    rw [simEnv20T, Env.builtins_withBuiltins]
    exact bAgree_vecNB P
  have h' := typedV_withB (defsGood_simEnv20T _) hB (typsGood_simEnv20T _) hG h
  rw [simEnv20T, withBuiltins_withB] at h'
  rwa [simEnv20T]

/-! ## `Good20B` configurations -/

variable {H : Type} {hn : H → String}

/-- **The state of a `Good20B` configuration is typed in `simEnv20T (vecNB P)`.** -/
theorem state_vecNB_of_good20B {P : Profile} {c : Config H} (hg : StoreBulk.Good20B hn P c) :
    TypedV (simEnv20T (vecNB P)) stateT (stateV hn c.store c.frame) :=
  typedV_vecNB (goodEvs_varT "state") (StoreBulk.typF_stateB hg.typ hg.store)

/-- **The code of a `Good20B` configuration is typed in `simEnv20T (vecNB P)`.** -/
theorem code_vecNB_of_good20B {P : Profile} {c : Config H} (hg : StoreBulk.Good20B hn P c) :
    TypedV (simEnv20T (vecNB P)) adminsTy (.list (adminsToV c.code)) :=
  typedV_vecNB goodEvs_adminsTy (StoreBulk.typF_codeB hg.typ hg.ok)

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
