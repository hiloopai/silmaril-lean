module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Insts
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.TypedNE
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.SuccTyped

/-!
# Round 5: `PosTypingNE` from its `instr` field

`typedV_store_ne`: a valid, bounded store whose function instances' modules export nothing is a
typed `store`, given `InstrTyping B` (the `instr` field) for the function bodies. Validity is used
only there: `StoreOk` makes each Wasm function body a valid instruction sequence
(`instrsOk_mem`). Every other instance is typed from its bounds alone (`Insts.lean`).

`posTypingNE_of_instr : InstrTyping B → PosTypingNE B hn`: with `Types.lean` and `Module.lean`,
**the positive typing reduces to the `instr` field**.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Validation (tyV)

variable {H : Type} {B : Builtins}

/-- **Every instruction of a valid sequence is valid**, in some context and at some type. -/
theorem instrsOk_mem : ∀ {C : Context} {is : List Instr} {it : InstrType}, InstrsOk C is it →
    ∀ i ∈ is, ∃ C' it', InstrOk C' i it'
  | _, _, _, .nil, _, hi => absurd hi List.not_mem_nil
  | _, _, _, .instr hok, _, hi => by
    obtain rfl := List.mem_singleton.1 hi
    exact ⟨_, _, hok⟩
  | _, _, _, .seq h₁ _ h₂, i, hi => by
    rcases List.mem_append.1 hi with hi₁ | hi₂
    · exact instrsOk_mem h₁ i hi₁
    · exact instrsOk_mem h₂ i hi₂
  | _, _, _, .cons hok _ hs, i, hi => by
    rcases List.mem_cons.1 hi with rfl | hi'
    · exact ⟨_, _, hok⟩
    · exact instrsOk_mem hs i hi'
  | _, _, _, .sub h _ _, i, hi => instrsOk_mem h i hi
  | _, _, _, .frame h _, i, hi => instrsOk_mem h i hi

/-- Every instruction of a bounded sequence is bounded. -/
theorem instrsBnd_mem : ∀ {l : List Instr}, Round4.instrsBnd l = true →
    ∀ i ∈ l, Round4.instrBnd i = true
  | [], _ => fun _ hi => absurd hi List.not_mem_nil
  | _ :: _, h => by
    simp only [Round4.instrsBnd, Bool.and_eq_true] at h
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact h.1
    · exact instrsBnd_mem h.2 i hi

/-- **A valid, bounded instruction sequence is a typed `instr*`**, given `InstrTyping`. -/
theorem typedV_instrs (hI : InstrTyping B) {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) (hb : Round4.instrsBnd is = true) :
    TypedV (simEnv B) instrsT (.list (instrsToV is)) := by
  rw [Exn.instrsToV_eq_map]
  exact typedV_list_iff.2 fun u hu => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
    obtain ⟨C', it', hok⟩ := instrsOk_mem h i hi
    exact hI C' i it' hok (instrsBnd_mem hb i hi)

set_option maxRecDepth 100000 in
theorem findTyp_local : (simEnv B).findTyp? "local" = some ([], [.instD [] []
    (.variantT [.mk "LOCAL" (.varT "valtype" []) [] []])]) := rfl

/-- `expr`, from `instr*`. -/
theorem typedV_expr {v : Value} (h : TypedV (simEnv B) instrsT v) :
    TypedV (simEnv B) (.varT "expr" []) v := fun _ hρ =>
  hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_expr
    Equiv.evalArgs_nil (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2 (h _ ⟨rfl, rfl, rfl⟩)))

/-- The declared locals of a function, as `local*`. -/
theorem typedV_locals (ts : List ValType) :
    TypedV (simEnv B) (.iterT (.varT "local" []) .list)
      (.list (ts.map fun t => .case "LOCAL" (Encode.toValue t))) :=
  typedV_list_iff.2 fun u hu => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hu
    exact Typing.typedV_closedCase findTyp_local rfl (Typing.typedV_valtype t _ ⟨rfl, rfl, rfl⟩)

/-- **A valid Wasm function's code is a typed `funccode`**, given `InstrTyping`. -/
theorem typedV_funccode_wasm (hI : InstrTyping B) {C : Context} {fn : Func} {d : DefType}
    (hf : FuncOk C fn d) (hb : Round4.instrsBnd fn.body = true) :
    TypedV (simEnv B) (.varT "funccode" []) (.case "FUNC" (.tuple
      [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
       .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
       .list (instrsToV fn.body)])) := by
  obtain ⟨-, -, -, hbody⟩ := hf
  exact Typing.typedV_closedCase findTyp_funccode rfl (hasTyp_tup3
    (typedV_typeidxNat fn.type.value.isLt) (typedV_locals fn.locals)
    (typedV_expr (typedV_instrs hI hbody hb)))

/-- **A valid, bounded, export-free function instance is a typed `funcinst`.** -/
theorem typedV_funcinst (hI : InstrTyping B) (hn : H → String) {s : Store H} {fi : FuncInst H}
    (hok : FuncInstOk s fi) (hb : Round4.FuncBnd fi) (he : fi.module.exports = []) :
    TypedV (simEnv B) funcinstT (funcInstV hn fi) := by
  have hcode : TypedV (simEnv B) (.varT "funccode" []) (match fi.code with
      | .wasm fn => .case "FUNC" (.tuple [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
          .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
          .list (instrsToV fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h))) := by
    cases hok with
    | wasm _ _ hc hf _ =>
      rw [hc]
      exact typedV_funccode_wasm hI hf (hb.2.2 _ hc)
    | host _ _ hc =>
      rw [hc]
      exact Typing.typedV_closedCase findTyp_funccode rfl (hasTyp_textT_iff.2 ⟨_, rfl⟩)
  exact typedV_struct ConfigOk.findTyp_funcinst (hasTypFields_cons_of
    (typedV_deftype fi.type hb.1) (hasTypFields_cons_of (typedV_moduleinst_ne _ hb.2.1 he)
      (hasTypFields_one hcode)))

/-- Elementwise typing of a mapped list. -/
theorem typedV_map {α : Type} {x : IL.Id} {l : List α} {f : α → Value}
    (h : ∀ a ∈ l, TypedV (simEnv B) (.varT x []) (f a)) :
    TypedV (simEnv B) (.iterT (.varT x []) .list) (.list (l.map f)) :=
  typedV_list_iff.2 fun u hu => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
    exact h a ha

/-- **A valid, bounded, export-free store is a typed `store`**, given `InstrTyping`. -/
theorem typedV_store_ne (hI : InstrTyping B) (hn : H → String) (s : Store H) (hs : StoreOk s)
    (hb : Round4.StoreBnd s) (he : StoreNE s) : TypedV (simEnv B) storeT (storeV hn s) :=
  typedV_struct ConfigOk.findTyp_store' <|
    hasTypFields_cons_of (typedV_map fun ti hti => typedV_taginst ti (hb.tags ti hti)) <|
    hasTypFields_cons_of (typedV_map fun gi hgi => typedV_globalinst gi (hb.globals gi hgi)) <|
    hasTypFields_cons_of (typedV_map fun mi _ => typedV_meminst mi) <|
    hasTypFields_cons_of (typedV_map fun ti hti => typedV_tableinst ti (hb.tables ti hti)) <|
    hasTypFields_cons_of (typedV_map fun fi hfi =>
      typedV_funcinst hI hn (hs.funcs fi hfi) (hb.funcs fi hfi) (he fi hfi)) <|
    hasTypFields_cons_of (typedV_map fun di _ => typedV_datainst di) <|
    hasTypFields_cons_of (typedV_map fun ei hei => typedV_eleminst ei (hb.elems ei hei)) <|
    hasTypFields_cons_of (typedV_map fun si hsi => typedV_structinst si (hb.structs si hsi)) <|
    hasTypFields_cons_of (typedV_map fun ai hai => typedV_arrayinst ai (hb.arrays ai hai)) <|
    hasTypFields_one (typedV_map fun e _ => Typing.typedV_exninst e (typedV_list_iff.2 fun u hu => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
      exact Typing.typedV_val v))

/-- **`PosTypingNE` from its `instr` field**: every other field is proved. -/
theorem posTypingNE_of_instr (hI : InstrTyping B) (hn : H → String) : PosTypingNE B hn where
  instr := hI
  callRefType d _ h := typedV_callRefType d h
  returnCallRefType d _ h := typedV_returnCallRefType d h
  moduleinst := moduleinst_ne
  store s hs _ hb he := typedV_store_ne hI hn s hs hb he

/-- **`PartsOk` with `pos` reduced to `InstrTyping`.** -/
theorem partsOk_of_instr {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
    (hI : InstrTyping (Round4Int.BI P hn host))
    (fwd : R4Fwd.Forward (Round4Int.BI P hn host) hn P host ValidNE)
    (fam : Round4Int.FamBwdV (simEnv (Round4Int.BI P hn host)) hn P host)
    (rem : Round4Read.RemainingV (simEnv (Round4Int.BI P hn host)) hn P host) :
    PartsOk hn P host :=
  ⟨posTypingNE_of_instr hI hn, fwd, fam, rem⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
