module

public import Silmaril.Wasm.SpecTec.Sim20.StoreBulk.Thms

/-!
# IL typing of the covered instructions without operators or blocks

The last part of `StoreBulk.InvokeOk` asks every function body, erased (`StoreDeep.eD`), to be a
typed `instr*` of `simEnv20 B`. This file types, as `admininstr`s of `simEnv20 B` (`TypedA`), the
covered instructions whose payloads are indices, value types, reference types, memory arguments
or constants, with no hypothesis:

* no payload: `nop`, `unreachable`, `drop`, `return`, `ref.is_null`, `memory.size`,
  `memory.fill`, `memory.copy` (`typedA_nil`);
* one index (`typedA_idx`): `br`, `br_if`, `call`, `local.get/set/tee`, `global.get/set`,
  `ref.func`, `table.get/set/size/fill`, `memory.init`, `data.drop`, `elem.drop`;

Two-index instructions, `br_table`, `select`, `ref.null` and the constants are in
`BodyTypPair`.

Each case is `Pure.typedV_closedCase20` at the case of `admininstr`, found by `rfl`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.BodyTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

set_option maxRecDepth 100000

variable {B : Builtins}

/-- An instruction typed as an `admininstr` of `simEnv20 B`. -/
abbrev TypedA (B : Builtins) (i : V2.Instr) : Prop :=
  TypedV (simEnv20 B) (.varT "admininstr" []) (instrToV i)

/-- A case of `admininstr` without premises, at a payload typed in the empty scope. -/
theorem typedA_case {op : MixopS} {t : Typ} {w : Value}
    (hf : Sim.IntNumeric.findCase (Sim.IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d295 0 0) op = some (t, []))
    (hw : HasTyp (simEnv20 B) VarEnv.empty t w) :
    TypedV (simEnv20 B) (.varT "admininstr" []) (.case op w) :=
  Pure.typedV_closedCase20 Whole.findTyp_admininstr20 hf hw

theorem valsOnly_empty : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩

/-- A typed value is typed in a scope that binds only term variables. -/
theorem hasTyp_bind {t : Typ} {v : Value} (h : TypedV (simEnv20 B) t v) (ρ : VarEnv)
    (hρ : ValsOnly ρ) (x : IL.Id) (w : Value) : HasTyp (simEnv20 B) (ρ.bindVal x w) t v :=
  h _ (Sim.ConfigOk.valsOnly_bindVal hρ x w)

/-! ## Index types -/

/-- The index types of the 2.0 script, each an alias of `idx`. -/
def idxNames : List IL.Id :=
  ["labelidx", "funcidx", "localidx", "globalidx", "tableidx", "typeidx", "elemidx", "dataidx"]

theorem findTyp_idxAlias {x : IL.Id} (hx : x ∈ idxNames) :
    (simEnv20 B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := by
  simp only [idxNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Every index is typed at every index type.** -/
theorem typedV_idxA {x : IL.Id} (hx : x ∈ idxNames) {k : IndexKind} (i : Idx k) :
    TypedV (simEnv20 B) (.varT x []) (idxV i) :=
  Whole.typedV_aliasG (findTyp_idxAlias hx) (Whole.typedV_idx20 i _ valsOnly_empty)

/-- A list of indices is typed at every index type. -/
theorem typedV_idxsA {x : IL.Id} (hx : x ∈ idxNames) {k : IndexKind} (l : List (Idx k)) :
    TypedV (simEnv20 B) (.iterT (.varT x []) .list) (.list (l.map idxV)) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_idxA hx i

/-! ## Single cases -/

theorem typedA_nop : TypedA B .nop := typedA_case rfl hasTyp_tupT_nil
theorem typedA_unreachable : TypedA B .unreachable := typedA_case rfl hasTyp_tupT_nil
theorem typedA_drop : TypedA B .drop := typedA_case rfl hasTyp_tupT_nil
theorem typedA_return : TypedA B .return_ := typedA_case rfl hasTyp_tupT_nil
theorem typedA_refIsNull : TypedA B .refIsNull := typedA_case rfl hasTyp_tupT_nil
theorem typedA_memorySize : TypedA B .memorySize := typedA_case rfl hasTyp_tupT_nil
theorem typedA_memoryFill : TypedA B .memoryFill := typedA_case rfl hasTyp_tupT_nil
theorem typedA_memoryCopy : TypedA B .memoryCopy := typedA_case rfl hasTyp_tupT_nil

theorem typedA_br (l : LabelIdx) : TypedA B (.br l) :=
  typedA_case rfl (typedV_idxA (by decide) l _ valsOnly_empty)
theorem typedA_brIf (l : LabelIdx) : TypedA B (.brIf l) :=
  typedA_case rfl (typedV_idxA (by decide) l _ valsOnly_empty)
theorem typedA_call (x : FuncIdx) : TypedA B (.call x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_refFunc (x : FuncIdx) : TypedA B (.refFunc x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_localGet (x : LocalIdx) : TypedA B (.localGet x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_localSet (x : LocalIdx) : TypedA B (.localSet x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_localTee (x : LocalIdx) : TypedA B (.localTee x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_globalGet (x : GlobalIdx) : TypedA B (.globalGet x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_globalSet (x : GlobalIdx) : TypedA B (.globalSet x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_tableGet (x : TableIdx) : TypedA B (.tableGet x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_tableSet (x : TableIdx) : TypedA B (.tableSet x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_tableSize (x : TableIdx) : TypedA B (.tableSize x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_tableFill (x : TableIdx) : TypedA B (.tableFill x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_memoryInit (x : DataIdx) : TypedA B (.memoryInit x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_dataDrop (x : DataIdx) : TypedA B (.dataDrop x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)
theorem typedA_elemDrop (x : ElemIdx) : TypedA B (.elemDrop x) :=
  typedA_case rfl (typedV_idxA (by decide) x _ valsOnly_empty)

end Silmaril.Wasm.SpecTec.Sim20.BodyTyp
