module

public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreAgree10Env

/-!
# `simEnv10` and `simEnv10T` type alike off `tbad10`

The 1.0 `STORE` erratum changes the `STORE` cases of `instr` and `admininstr` only. A type whose
unfolding never reaches those two types is typed alike in both environments, in both directions.
This is the mutual induction over the typing block that an earlier step named as missing for
"one invariant instead of a union"; it is 2.0's generic `Sim20.ElseAgree.hasTyp_off_iff`
(`Raw/…/Sim20/ElseAgree/Typ.lean`), instantiated here.

* `tbad10`: the thirteen types of the corrected wasm-1.0 script that reach `instr` or
  `admininstr` (computed by a closure over the script's type table; the kernel checks that the
  rest is closed).
* `typsOffB_fixed10` (kernel): every type of `Scripts.Wasm10.fixed` outside `tbad10` unfolds to
  types outside `tbad10`.
* `typOff10T`: the type tables of `simEnv10 B` and `simEnv10T B` agree outside `tbad10`.
* **`hasTyp_off10T`**: at a type off `tbad10`, in a scope without type variables, a value is
  typed in `simEnv10T B` exactly when it is in `simEnv10 B`.
* Instances: `val` (`hasTyp_val10T`), `valtype` and `memarg`, and lists of `val`
  (`hasTyp_vals10T`), the types the backward recursion and the store rules read.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (find?_map_repl)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (TypOff GoodT TypsOkT typsOffB goodT_of_all
  hasTyp_off_iff)

/-- The types of the corrected wasm-1.0 script that reach `instr` or `admininstr`. -/
def tbad10 : List String :=
  ["instr", "admininstr", "config", "expr", "code", "elem", "global", "func", "data",
    "funcinst", "module", "store", "state"]

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Every type of the corrected wasm-1.0 script outside `tbad10` unfolds to types outside
`tbad10`** (kernel). -/
theorem typsOffB_fixed10 :
    typsOffB tbad10 (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed) = true := by
  decide +kernel

/-- **The type tables of `simEnv10 B` and `simEnv10T B` agree off `tbad10`.** -/
theorem typOff10T (B : Builtins) : TypOff tbad10 (simEnv10 B) (simEnv10T B) := by
  refine ⟨fun x hx => ?_, fun x td hx hd => ?_⟩
  · have ha : x ≠ "admininstr" := by rintro rfl; simp [tbad10] at hx
    have hi : x ≠ "instr" := by rintro rfl; simp [tbad10] at hx
    have ht := (simEnv10T_tables B).1
    simp only [Env.findTyp?, ht, find?_map_repl]
    simp [ha, hi]
  · have hm : (x, td) ∈ typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed := by
      have h' : (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed).find? x = some td := by
        simpa [simEnv10, baseEnv10, Env.withBuiltins, Env.findTyp?, envOfScript, envOfDefs_eq,
          Env.empty, Map.empty] using hd
      exact mem_of_find? h'
    have h := List.all_eq_true.1 typsOffB_fixed10 _ hm
    simp only [hx, Bool.false_or] at h
    intro i hi
    exact goodT_of_all (List.all_eq_true.1 h i hi)

/-- A scope without type variables. -/
theorem typsOkT_nil10 {ρ : VarEnv} (h : ρ.typs = []) : TypsOkT tbad10 ρ := by
  intro p hp; rw [h] at hp; cases hp

/-- **Off `tbad10`, `simEnv10T B` types as `simEnv10 B`**, in both directions. -/
theorem hasTyp_off10T (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {t : Typ} {v : Value}
    (ht : GoodT tbad10 (evTyp t)) : HasTyp (simEnv10T B) ρ t v ↔ HasTyp (simEnv10 B) ρ t v :=
  hasTyp_off_iff (envSame10T B) (typOff10T B) (typsOkT_nil10 hρ) ht

/-- `val` is typed alike in both. -/
theorem hasTyp_val10T (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {v : Value} :
    HasTyp (simEnv10T B) ρ (.varT "val" []) v ↔ HasTyp (simEnv10 B) ρ (.varT "val" []) v :=
  hasTyp_off10T B hρ (goodT_of_all (by decide))

/-- `val*` is typed alike in both. -/
theorem hasTyp_vals10T (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {v : Value} :
    HasTyp (simEnv10T B) ρ (.iterT (.varT "val" []) .list) v ↔
      HasTyp (simEnv10 B) ρ (.iterT (.varT "val" []) .list) v :=
  hasTyp_off10T B hρ (goodT_of_all (by decide))

/-- `valtype` is typed alike in both. -/
theorem hasTyp_valtype10T (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {v : Value} :
    HasTyp (simEnv10T B) ρ (.varT "valtype" []) v ↔ HasTyp (simEnv10 B) ρ (.varT "valtype" []) v :=
  hasTyp_off10T B hρ (goodT_of_all (by decide))

/-- `memarg` is typed alike in both. -/
theorem hasTyp_memarg10T (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {v : Value} :
    HasTyp (simEnv10T B) ρ (.varT "memarg" []) v ↔ HasTyp (simEnv10 B) ρ (.varT "memarg" []) v :=
  hasTyp_off10T B hρ (goodT_of_all (by decide))

/-- `frame` (locals and the module instance, no code) is typed alike in both. -/
theorem hasTyp_frame10T (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {v : Value} :
    HasTyp (simEnv10T B) ρ (.varT "frame" []) v ↔ HasTyp (simEnv10 B) ρ (.varT "frame" []) v :=
  hasTyp_off10T B hρ (goodT_of_all (by decide))

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
