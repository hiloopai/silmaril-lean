module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumInt

/-!
# `NumAgree` for the wasm-2.0 script, discharged

The float clauses of the 2.0 dispatchers (`$unop_`, `$binop_`, `$relop_` at `Fnn`) call the
`hint(builtin)` primitives `$fabs_` … `$fge_` on `$sizenn(Fnn)` and the operands, which `B`
answers through `Floats.FloatB P B` with every result the profile allows
(`applies_unop_float20`, `applies_binop_float20`, `applies_relop_float20`). With the integer
dispatchers of `Sim20.NumInt`, this gives

  `numAgree_simEnv20 : IntB B → Floats.FloatB P B → NumAgree (simEnv20 B) P`,

and in particular for the concrete interpretation `Floats.floatIntB P` (`numAgree_floatIntB20`).
The hypothesis of rounds 2–4 (`IntB`, `FloatB`) is exactly what the 3.0 numerics took, so the
2.0 numeric rules now hold under the same builtins as the 3.0 simulation.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (IntB)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB floatCall unName binName relName unRes binRes)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} {P : Profile}

/-- The scope of a one-operand `Fnn` clause (`Fnn`, `fN`). -/
abbrev fscope1' (t : FloatType) (a : Value) : VarEnv :=
  (VarEnv.empty.bindVal "Fnn" (numTypeV (.float t))).bindVal "fN" a

/-- The scope of a two-operand `Fnn` clause (`Fnn`, `fN_1`, `fN_2`). -/
abbrev fscope2' (t : FloatType) (a b : Value) : VarEnv :=
  ((VarEnv.empty.bindVal "Fnn" (numTypeV (.float t))).bindVal "fN_1" a).bindVal "fN_2" b

/-- The `Fnn` pattern of the 2.0 clauses. -/
abbrev fnnPat : Exp := .subE (.varE "Fnn") (.varT "Fnn" []) (.varT "numtype" [])

/-- The one-operand `Fnn` clause for the opcode `o` fires and calls its primitive. -/
theorem hitUn20 (hB : FloatB P B) {x : IL.Id} (hx : Sim.IntNumeric.NoClauses (simEnv20 B) x)
    {o : MixopS} {q : List Param} {cs : List Clause} {t : FloatType} {a v : Value}
    (hc : floatCall P x [.val (natV t.width), .val a] = some v) :
    TryClauses (simEnv20 B) (.defD q [.expA fnnPat, .expA (.caseE o (.tupE [])), .expA (.varE "fN")]
      (.callE x [.expA (.callE "sizenn" [.expA fnnPat]), .expA (.varE "fN")]) [] :: cs)
      [.val (numTypeV (.float t)), .val (.case o (.tuple [])), .val a] v := by
  have hm : MatchArgs (simEnv20 B) VarEnv.empty
      [.expA fnnPat, .expA (.caseE o (.tupE [])), .expA (.varE "fN")]
      [.val (numTypeV (.float t)), .val (.case o (.tuple [])), .val a] (fscope1' t a) :=
    matchArgs_cons (matchArg_subVar20 (by simp) (argSubOk_fnn_float20 t))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))
  have ha : EvalArgs (simEnv20 B) (fscope1' t a)
      [.expA (.callE "sizenn" [.expA fnnPat]), .expA (.varE "fN")] [.val (natV t.width), .val a] :=
    Equiv.evalArgs_cons (evalExp_sizenn20 (.float t) rfl (by simp))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)
  exact tryClauses_hit hm premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim20 hB hx rfl ha hc))

/-- The two-operand `Fnn` clause for the opcode `o` fires and calls its primitive. -/
theorem hitBin20 (hB : FloatB P B) {x : IL.Id} (hx : Sim.IntNumeric.NoClauses (simEnv20 B) x)
    {o : MixopS} {q : List Param} {cs : List Clause} {t : FloatType} {a b v : Value}
    (hc : floatCall P x [.val (natV t.width), .val a, .val b] = some v) :
    TryClauses (simEnv20 B) (.defD q
      [.expA fnnPat, .expA (.caseE o (.tupE [])), .expA (.varE "fN_1"), .expA (.varE "fN_2")]
      (.callE x [.expA (.callE "sizenn" [.expA fnnPat]), .expA (.varE "fN_1"),
        .expA (.varE "fN_2")]) [] :: cs)
      [.val (numTypeV (.float t)), .val (.case o (.tuple [])), .val a, .val b] v := by
  have hm : MatchArgs (simEnv20 B) VarEnv.empty
      [.expA fnnPat, .expA (.caseE o (.tupE [])), .expA (.varE "fN_1"), .expA (.varE "fN_2")]
      [.val (numTypeV (.float t)), .val (.case o (.tuple [])), .val a, .val b]
      (fscope2' t a b) :=
    matchArgs_cons (matchArg_subVar20 (by simp) (argSubOk_fnn_float20 t))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
          (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))
  have ha : EvalArgs (simEnv20 B) (fscope2' t a b)
      [.expA (.callE "sizenn" [.expA fnnPat]), .expA (.varE "fN_1"), .expA (.varE "fN_2")]
      [.val (natV t.width), .val a, .val b] :=
    Equiv.evalArgs_cons (evalExp_sizenn20 (.float t) rfl (by simp))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil))
  exact tryClauses_hit hm premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim20 hB hx rfl ha hc))

set_option maxRecDepth 100000 in
/-- **`$unop_(Fnn, op, fN)`** is the list of every result the profile allows. -/
theorem applies_unop_float20 (hB : FloatB P B) (t : FloatType) (op : FloatUnOp)
    (x : BitVec t.width) :
    Applies (simEnv20 B) "unop_" [.val (numTypeV (.float t)), .val (floatUnOpV op),
      .val (Sim.floatV t x)] (unRes P t op x) := by
  refine ⟨_, _, _, findDef_unop20 B, Or.inl ?_⟩
  have hc := Sim.Floats.floatCall_un P t op x
  cases op <;> (skip20; exact hitUn20 hB ⟨_, _, rfl⟩ hc)

set_option maxRecDepth 100000 in
/-- **`$binop_(Fnn, op, fN_1, fN_2)`** is the list of every result the profile allows. -/
theorem applies_binop_float20 (hB : FloatB P B) (t : FloatType) (op : FloatBinOp)
    (x y : BitVec t.width) :
    Applies (simEnv20 B) "binop_" [.val (numTypeV (.float t)), .val (floatBinOpV op),
      .val (Sim.floatV t x), .val (Sim.floatV t y)] (binRes P t op x y) := by
  refine ⟨_, _, _, findDef_binop20 B, Or.inl ?_⟩
  have hc := Sim.Floats.floatCall_bin P t op x y
  cases op <;> (skip20; exact hitBin20 hB ⟨_, _, rfl⟩ hc)

set_option maxRecDepth 100000 in
/-- **`$relop_(Fnn, op, fN_1, fN_2)`** is Core's comparison. -/
theorem applies_relop_float20 (hB : FloatB P B) (t : FloatType) (op : FloatRelOp)
    (x y : BitVec t.width) :
    Applies (simEnv20 B) "relop_" [.val (numTypeV (.float t)), .val (floatRelOpV op),
      .val (Sim.floatV t x), .val (Sim.floatV t y)] (Sim.Vec.i32NV (floatRelOp t op x y)) := by
  refine ⟨_, _, _, findDef_relop20 B, Or.inl ?_⟩
  have hc := Sim.Floats.floatCall_rel P t op x y
  cases op <;> (skip20; exact hitBin20 hB ⟨_, _, rfl⟩ hc)

/-- A one-element result list: its members are the one result. -/
theorem mem_singleton_result {α : Type} {f : α → Value} {r : α} {R : α → Prop}
    (hR : ∀ z, R z ↔ z = r) (c : Value) : c ∈ [f r] ↔ ∃ z, R z ∧ c = f z := by
  simp only [List.mem_singleton]
  exact ⟨fun h => ⟨r, (hR r).2 rfl, h⟩, fun ⟨z, hz, h⟩ => (hR z).1 hz ▸ h⟩

/-- **`NumAgree` holds for the wasm-2.0 script** under the builtins the 3.0 numerics take: the
integer primitives (`IntB`) and the float and conversion primitives of the profile (`FloatB`). -/
theorem numAgree_simEnv20 (hI : IntB B) (hF : FloatB P B) : NumAgree (simEnv20 B) P where
  intUnOp t op x _ := ⟨_, applies_unop_int20 hI hF t op x,
    mem_singleton_result (fun _ => Iff.rfl)⟩
  floatUnOp t op x := ⟨_, applies_unop_float20 hF t op x, fun _ => Sim.Floats.mem_map_bitsWhere⟩
  intBinOp t op x y := ⟨_, applies_binop_int20 hI t op x y, fun c => by
    rw [ibinop_agree]
    unfold V2.Execution.IntBinOpResult
    cases intBinOp t op x y with
    | error e => simp [Except.toOption]
    | ok z =>
        simp only [Except.toOption, Option.toList_some, List.map_cons, List.map_nil,
          List.mem_singleton, Except.ok.injEq]
        exact ⟨fun hc => ⟨z, rfl, hc⟩, fun ⟨_, hz, hc⟩ => hz ▸ hc⟩⟩
  floatBinOp t op x y :=
    ⟨_, applies_binop_float20 hF t op x y, fun _ => Sim.Floats.mem_map_bitsWhere⟩
  intTestOp t op x := applies_testop_int20 t op x
  intRelOp t op x y := applies_relop_int20 t op x y
  floatRelOp t op x y := applies_relop_float20 hF t op x y

/-- In particular for the concrete interpretation of the primitives at the profile `P`. -/
theorem numAgree_floatIntB20 : NumAgree (simEnv20 (Sim.Floats.floatIntB P)) P :=
  numAgree_simEnv20 (Sim.Floats.intB_floatIntB P) (Sim.Floats.floatB_floatIntB P)

end Silmaril.Wasm.SpecTec.Sim20.Pure
