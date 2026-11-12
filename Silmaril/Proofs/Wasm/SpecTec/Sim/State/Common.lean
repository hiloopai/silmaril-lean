module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Eval
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Assembly

/-!
# Family M: shared facts

The rule provenance of `Step_read` and `Step_pure` in `simEnv B`, typing of values extracted from
a typed configuration (`typedV_val_of_mem`), and the fields of the encoded store, frame and module
instance.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge

/-! ## Provenance -/

/-- The 103 rules of `Step_read` (`Equiv.ExecRead`), in `simEnv B`. -/
theorem hasReadRules_simEnv (B : Builtins) : Equiv.ExecRead.HasReadRules (simEnv B) := by
  have h := Equiv.ExecRead.hasReadRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-- The `Step_pure` rules of `Equiv.Execution`, in `simEnv B`. -/
theorem hasPureRules_simEnv (B : Builtins) : Equiv.Execution.HasStepRules (simEnv B) := by
  have h := Equiv.Execution.hasStepRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-! ## Typing of list elements -/

/-- A successful list check succeeds on the head and on the tail. -/
theorem hasTypList_cons_true {env : Env} {ρ : VarEnv} {t : Typ} {n : Nat} {b : Value}
    {l : List Value} (h : hasTypList (n + 1) env ρ t (b :: l) = .ok true) :
    hasTyp n env ρ t b = .ok true ∧ hasTypList n env ρ t l = .ok true := by
  rw [hasTypList_succ_cons] at h
  cases hb : hasTyp n env ρ t b with
  | error e => simp [hb, Bind.bind, Except.bind] at h
  | ok c =>
    cases c with
    | false => simp [hb, Bind.bind, Except.bind] at h
    | true => exact ⟨rfl, by simpa [hb, Bind.bind, Except.bind] using h⟩

/-- An element of a list that passes the list check has the element type. -/
theorem hasTypList_mem {env : Env} {ρ : VarEnv} {t : Typ} :
    ∀ (n : Nat) (l : List Value) (a : Value), hasTypList n env ρ t l = .ok true → a ∈ l →
      HasTyp env ρ t a
  | 0, _, _, h, _ => by simp [hasTypList_zero] at h
  | _, [], _, _, ha => by cases ha
  | n + 1, b :: l, a, h, ha => by
    have hb : hasTyp n env ρ t b = .ok true ∧ hasTypList n env ρ t l = .ok true :=
      hasTypList_cons_true h
    rcases List.mem_cons.1 ha with rfl | hm
    · exact ⟨n, hb.1⟩
    · exact hasTypList_mem n l a hb.2 hm

/-- An element of a list typed `t*` has type `t`. -/
theorem hasTyp_list_mem {env : Env} {ρ : VarEnv} {t : Typ} {l : List Value} {a : Value}
    (h : HasTyp env ρ (.iterT t .list) (.list l)) (ha : a ∈ l) : HasTyp env ρ t a := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [hasTyp_zero] at h
  | succ n =>
    have hl : hasTypList n env ρ t l = .ok true := by
      simpa [hasTyp_succ_iterT_list, Value.asList?] using h
    exact hasTypList_mem n l a hl ha

/-- `TypedV` of a list, elementwise. -/
theorem typedV_list_mem {env : Env} {t : Typ} {l : List Value} {a : Value}
    (h : TypedV env (.iterT t .list) (.list l)) (ha : a ∈ l) : TypedV env t a :=
  fun ρ hρ => hasTyp_list_mem (h ρ hρ) ha

/-! ## Values in code -/

variable {H : Type}

/-- A value instruction encodes as the value. -/
theorem adminToV_toAdmin (v : Val) : adminToV v.toAdmin = valV v := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r <;> rfl

/-- `adminsToV` of the empty list. -/
theorem adminsToV_nil : adminsToV [] = [] := rfl

/-- `adminsToV` of a cons. -/
theorem adminsToV_cons (a : Admin) (l : List Admin) : adminsToV (a :: l) = adminToV a :: adminsToV l :=
  rfl

/-- The image of a configuration, unfolded. -/
theorem configV_eq (hn : H → String) (s : Store H) (f : Frame) (is : List Admin) :
    configV hn ⟨s, f, is⟩ = cfgV (stV (storeV hn s) (frameV f)) (adminsToV is) := rfl

/-- A typed configuration has a typed state. -/
theorem typedV_state {env : Env} {hn : H → String} (T : TypingFacts env hn) {s : Store H}
    {f : Frame} {is : List Admin} (hc : Typed env hn ⟨s, f, is⟩) :
    TypedV env stateT (stV (storeV hn s) (frameV f)) :=
  ((T.config _).1 hc).1

/-- A typed configuration has typed code. -/
theorem typedV_code {env : Env} {hn : H → String} (T : TypingFacts env hn) {s : Store H}
    {f : Frame} {is : List Admin} (hc : Typed env hn ⟨s, f, is⟩) :
    TypedV env instrsT (.list (adminsToV is)) :=
  ((T.config _).1 hc).2

/-- A value occurring in the code of a typed configuration is a typed `val`. -/
theorem typedV_val_of_mem {env : Env} {hn : H → String} (T : TypingFacts env hn) {s : Store H}
    {f : Frame} {is : List Admin} (hc : Typed env hn ⟨s, f, is⟩) {v : Val}
    (hv : v.toAdmin ∈ is) : TypedV env valT (valV v) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hv
  have hcode := typedV_code T hc
  rw [adminsToV_append, adminsToV_cons] at hcode
  have h₂ := ((T.append _ _).1 hcode).2
  have h₃ : TypedV env instrsT (.list (adminsToV (vals [v]) ++ adminsToV l₂)) := by
    simpa [vals, adminsToV_cons, adminsToV_nil] using h₂
  have h₄ := T.vals [v] ((T.append _ _).1 h₃).1
  exact typedV_list_mem h₄ (by simp [vals, adminsToV_cons, adminToV_toAdmin, adminsToV])

/-! ## Fields of the encoded state -/

@[simp] theorem frameV_LOCALS (f : Frame) :
    (frameV f).field? "LOCALS" = some (.list (f.locals.map fun o => .opt (o.map valV))) := rfl

@[simp] theorem frameV_MODULE (f : Frame) :
    (frameV f).field? "MODULE" = some (moduleInstToValue CT f.module) := rfl

@[simp] theorem moduleV_GLOBALS (m : ModuleInst) :
    (moduleInstToValue CT m).field? "GLOBALS" = some (.list (m.globals.map fun a => .num (.natN a))) :=
  rfl

@[simp] theorem moduleV_TABLES (m : ModuleInst) :
    (moduleInstToValue CT m).field? "TABLES" = some (.list (m.tables.map fun a => .num (.natN a))) :=
  rfl

@[simp] theorem moduleV_MEMS (m : ModuleInst) :
    (moduleInstToValue CT m).field? "MEMS" = some (.list (m.mems.map fun a => .num (.natN a))) :=
  rfl

@[simp] theorem moduleV_ELEMS (m : ModuleInst) :
    (moduleInstToValue CT m).field? "ELEMS" = some (.list (m.elems.map fun a => .num (.natN a))) :=
  rfl

@[simp] theorem moduleV_DATAS (m : ModuleInst) :
    (moduleInstToValue CT m).field? "DATAS" = some (.list (m.datas.map fun a => .num (.natN a))) :=
  rfl

@[simp] theorem storeV_GLOBALS (hn : H → String) (s : Store H) :
    (storeV hn s).field? "GLOBALS" = some (.list (s.globals.map globalInstV)) := rfl

@[simp] theorem storeV_TABLES (hn : H → String) (s : Store H) :
    (storeV hn s).field? "TABLES" = some (.list (s.tables.map (tableInstToValue CT))) := rfl

@[simp] theorem storeV_MEMS (hn : H → String) (s : Store H) :
    (storeV hn s).field? "MEMS" = some (.list (s.mems.map memInstToValue)) := rfl

@[simp] theorem storeV_ELEMS (hn : H → String) (s : Store H) :
    (storeV hn s).field? "ELEMS" = some (.list (s.elems.map (elemInstToValue CT))) := rfl

@[simp] theorem storeV_DATAS (hn : H → String) (s : Store H) :
    (storeV hn s).field? "DATAS" = some (.list (s.datas.map dataInstToValue)) := rfl

/-- An address list entry, read through the encoding. -/
theorem getElem?_map_natN {l : List Nat} {n a : Nat} (h : l[n]? = some a) :
    (l.map fun a => Value.num (.natN a))[n]? = some (.num (.natN a)) := by
  simp [h]

/-- Updating the `LOCALS` field of an encoded frame encodes `Frame.setLocal`. -/
theorem frameV_setLocal (f : Frame) (x : LocalIdx) (v : Val) :
    (frameV f).setField "LOCALS"
      (.list ((f.locals.map fun o => Value.opt (o.map valV)).set x.toNat (.opt (some (valV v))))) =
      some (frameV (f.setLocal x v)) := by
  simp [frameV, Frame.setLocal, List.map_set]

/-- `List.modify` at an index in range is `List.set` of the modified element. -/
theorem List.modify_eq_set_of_getElem? {α : Type} {l : List α} {a : Nat} {x : α}
    (h : l[a]? = some x) (g : α → α) : l.modify a g = l.set a (g x) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_modify, List.getElem_set]
    split <;> simp_all

/-- Updating the `GLOBALS` field of an encoded store encodes `Store.setGlobal`. -/
theorem storeV_setGlobal (hn : H → String) (s : Store H) {a : Nat} {g : GlobalInst}
    (hg : s.globals[a]? = some g) (v : Val) :
    (storeV hn s).setField "GLOBALS"
      (.list ((s.globals.map globalInstV).set a (globalInstV { g with value := v }))) =
      some (storeV hn (s.setGlobal a v)) := by
  simp [storeV, Store.setGlobal, List.modify_eq_set_of_getElem? hg, List.map_set]

/-- The `VALUE` field of an encoded global. -/
@[simp] theorem globalInstV_VALUE (g : GlobalInst) :
    (globalInstV g).field? "VALUE" = some (valV g.value) := rfl

/-- Writing the `VALUE` field of an encoded global. -/
theorem globalInstV_setValue (g : GlobalInst) (v : Val) :
    (globalInstV g).setField "VALUE" (valV v) = some (globalInstV { g with value := v }) := by
  simp [globalInstV]

end Silmaril.Wasm.SpecTec.Sim.State
