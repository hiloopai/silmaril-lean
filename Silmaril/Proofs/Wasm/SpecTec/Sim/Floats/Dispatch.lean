module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Decode

/-!
# Float track: the scalar dispatchers at float types

`$unop_`, `$binop_`, `$relop_` at `Fnn`, read off the fixed script (`Original.d503`, `d504`,
`d506`): every `Inn` clause fails its subtype test (`Sem.argSubOk`), every `Fnn` clause for
another opcode fails on its opcode, and the clause for the opcode calls the primitive, which
`B` answers through `FloatB`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} {P : Profile}

/-- A primitive answered by `B` through `FloatB`. -/
theorem callDef_floatPrim (hB : FloatB P B) {x : IL.Id} (hx : IntNumeric.NoClauses (simEnv B) x)
    {ρ : VarEnv} {args : List Arg} {ws : List ArgV} {v : Value} (hρ : ρ.findDef? x = none)
    (ha : EvalArgs (simEnv B) ρ args ws) (hc : floatCall P x ws = some v) :
    CallDef (simEnv B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := hx
  exact Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha (hB _ _ _ hc)

/-- A clause for an `Inn` type, or for another opcode, is skipped at a float type. -/
theorem skipF {K : IL.Id} (hK : K = "Inn" ∨ K = "Fnn") {X : IL.Id} {o o' : MixopS} {inner : Exp}
    {pats : List Arg} {t : FloatType} {p : Value} {ws : List ArgV} (h : K = "Inn" ∨ o ≠ o') :
    MatchArgsUndef (simEnv B) VarEnv.empty (.expA (kindPat X K) :: .expA (.caseE o' inner) :: pats)
      (.val (Vec.numTypeV (.float t)) :: .val (.case o p) :: ws) := by
  by_cases hI : K = "Inn"
  · exact matchArgs_cons_undef (matchArg_kindPat_undef hK rfl (by simp [kindOf, hI]))
  · have hne : o ≠ o' := h.resolve_left hI
    have hF : kindOf (.float t) = K := by rcases hK with h' | h' <;> simp_all [kindOf]
    exact matchArgs_cons_undef_tail (matchArg_kindPat hK rfl (by simp) hF)
      (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hne)))

/-- The scope of a one-operand `Fnn` clause. -/
abbrev fscope1 (t : FloatType) (a : Value) : VarEnv :=
  (VarEnv.empty.bindVal "Fnn" (Vec.numTypeV (.float t))).bindVal "f" a

/-- The scope of a two-operand `Fnn` clause. -/
abbrev fscope2 (t : FloatType) (a b : Value) : VarEnv :=
  ((VarEnv.empty.bindVal "Fnn" (Vec.numTypeV (.float t))).bindVal "f_1" a).bindVal "f_2" b

/-- The one-operand `Fnn` clause for the opcode `o` fires and calls its primitive. -/
theorem hitUn (hB : FloatB P B) {x : IL.Id} (hx : IntNumeric.NoClauses (simEnv B) x)
    {o : MixopS} {q : List Param} {cs : List Clause} {t : FloatType} {a v : Value}
    (hc : floatCall P x [.val (natV t.width), .val a] = some v) :
    TryClauses (simEnv B) (.defD q
      [.expA (kindPat "Fnn" "Fnn"), .expA (.caseE o (.tupE [])), .expA (.varE "f")]
      (.callE x [.expA (.callE "sizenn" [.expA (kindPat "Fnn" "Fnn")]), .expA (.varE "f")]) []
      :: cs) [.val (Vec.numTypeV (.float t)), .val (.case o (.tuple [])), .val a] v := by
  have hm : MatchArgs (simEnv B) VarEnv.empty
      [.expA (kindPat "Fnn" "Fnn"), .expA (.caseE o (.tupE [])), .expA (.varE "f")]
      [.val (Vec.numTypeV (.float t)), .val (.case o (.tuple [])), .val a] (fscope1 t a) :=
    matchArgs_cons (matchArg_kindPat (.inr rfl) rfl (by simp) rfl)
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))
  have ha : EvalArgs (simEnv B) (fscope1 t a)
      [.expA (.callE "sizenn" [.expA (kindPat "Fnn" "Fnn")]), .expA (.varE "f")]
      [.val (natV t.width), .val a] :=
    Equiv.evalArgs_cons (evalExp_sizeFun findDef_sizenn (.float t) rfl (by simp))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)
  exact tryClauses_hit hm premsHold_nil (evalExp_callE_iff.2 (callDef_floatPrim hB hx rfl ha hc))

/-- The two-operand `Fnn` clause for the opcode `o` fires and calls its primitive. -/
theorem hitBin (hB : FloatB P B) {x : IL.Id} (hx : IntNumeric.NoClauses (simEnv B) x)
    {o : MixopS} {q : List Param} {cs : List Clause} {t : FloatType} {a b v : Value}
    (hc : floatCall P x [.val (natV t.width), .val a, .val b] = some v) :
    TryClauses (simEnv B) (.defD q
      [.expA (kindPat "Fnn" "Fnn"), .expA (.caseE o (.tupE [])), .expA (.varE "f_1"),
        .expA (.varE "f_2")]
      (.callE x [.expA (.callE "sizenn" [.expA (kindPat "Fnn" "Fnn")]), .expA (.varE "f_1"),
        .expA (.varE "f_2")]) [] :: cs)
      [.val (Vec.numTypeV (.float t)), .val (.case o (.tuple [])), .val a, .val b] v := by
  have hm : MatchArgs (simEnv B) VarEnv.empty
      [.expA (kindPat "Fnn" "Fnn"), .expA (.caseE o (.tupE [])), .expA (.varE "f_1"),
        .expA (.varE "f_2")]
      [.val (Vec.numTypeV (.float t)), .val (.case o (.tuple [])), .val a, .val b]
      (fscope2 t a b) :=
    matchArgs_cons (matchArg_kindPat (.inr rfl) rfl (by simp) rfl)
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
          (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))
  have ha : EvalArgs (simEnv B) (fscope2 t a b)
      [.expA (.callE "sizenn" [.expA (kindPat "Fnn" "Fnn")]), .expA (.varE "f_1"),
        .expA (.varE "f_2")] [.val (natV t.width), .val a, .val b] :=
    Equiv.evalArgs_cons (evalExp_sizeFun findDef_sizenn (.float t) rfl (by simp))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil))
  exact tryClauses_hit hm premsHold_nil (evalExp_callE_iff.2 (callDef_floatPrim hB hx rfl ha hc))

set_option maxRecDepth 100000 in
/-- **`$unop_(Fnn, op, f)`** is the list of every result the profile allows. -/
theorem applies_unop_float (hB : FloatB P B) (t : FloatType) (op : FloatUnOp)
    (x : BitVec t.width) :
    Applies (simEnv B) "unop_" [.val (Vec.numTypeV (.float t)), .val (Vec.fUnOpV op),
      .val (floatV t x)] (unRes P t op x) := by
  refine ⟨_, _, _, IntNumeric.findDef_unop B, Or.inl ?_⟩
  have hc := floatCall_un P t op x
  cases op <;>
  · repeat (refine tryClauses_skip_match (skipF (by first | exact .inl rfl | exact .inr rfl)
      (by first | exact .inl rfl | exact .inr (by decide))) ?_)
    exact hitUn hB ⟨_, _, rfl⟩ hc

set_option maxRecDepth 100000 in
/-- **`$binop_(Fnn, op, f_1, f_2)`** is the list of every result the profile allows. -/
theorem applies_binop_float (hB : FloatB P B) (t : FloatType) (op : FloatBinOp)
    (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (Vec.numTypeV (.float t)), .val (Vec.fBinOpV op),
      .val (floatV t x), .val (floatV t y)] (binRes P t op x y) := by
  refine ⟨_, _, _, IntNumeric.findDef_binop B, Or.inl ?_⟩
  have hc := floatCall_bin P t op x y
  cases op <;>
  · repeat (refine tryClauses_skip_match (skipF (by first | exact .inl rfl | exact .inr rfl)
      (by first | exact .inl rfl | exact .inr (by decide))) ?_)
    exact hitBin hB ⟨_, _, rfl⟩ hc

set_option maxRecDepth 100000 in
/-- **`$relop_(Fnn, op, f_1, f_2)`** is Core's comparison. -/
theorem applies_relop_float (hB : FloatB P B) (t : FloatType) (op : FloatRelOp)
    (x y : BitVec t.width) :
    Applies (simEnv B) "relop_" [.val (Vec.numTypeV (.float t)), .val (Vec.vFloatRelOpV op),
      .val (floatV t x), .val (floatV t y)] (Vec.i32NV (floatRelOp t op x y)) := by
  refine ⟨_, _, _, IntNumeric.findDef_relop B, Or.inl ?_⟩
  have hc := floatCall_rel P t op x y
  cases op <;>
  · repeat (refine tryClauses_skip_match (skipF (by first | exact .inl rfl | exact .inr rfl)
      (by first | exact .inl rfl | exact .inr (by decide))) ?_)
    exact hitBin hB ⟨_, _, rfl⟩ hc

end Silmaril.Wasm.SpecTec.Sim.Floats
