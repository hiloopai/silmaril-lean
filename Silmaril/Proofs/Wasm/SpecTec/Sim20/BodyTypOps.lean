module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.BodyTypPair

/-!
# IL typing of the covered numeric instructions

`UNOP`, `BINOP`, `TESTOP` and `RELOP` carry a number type and an operator whose IL type depends on
it (`unop_(numtype)`, …). Round 3's `Pure.numTyped_simEnv20` types every V2 operator at its
number type, with the type bound to the variable `nt`; `hasTyp_of_typedAt` moves that typing to
the binder `numtype` of the `instr` case. `CVTOP` has the premise `numtype_1 =/= numtype_2`, which
holds whenever V2 defines the conversion (`ne_of_toShared`). A load `t.load` has no load operator;
`iNN.loadK_sx` has `loadop_(iNN)`, whose premise `K < |iNN|` is asked for (`PackOk`).
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

/-- **Typing at a scope variable moves to another variable bound to the same value.** -/
theorem hasTyp_of_typedAt {T y : IL.Id} {w v : Value} (h : Pure.TypedAt (simEnv20 B) T "nt" w v)
    {ρ : VarEnv} (hy : ρ.findVal? y = some w) :
    HasTyp (simEnv20 B) ρ (.varT T [.expA (.varE y)]) v := by
  have hx : (VarEnv.empty.bindVal "nt" w).findVal? "nt" = some w := by
    simp [VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.bind]
  have h₁ := h (VarEnv.empty.bindVal "nt" w) (Sim.ConfigOk.valsOnly_bindVal valsOnly_empty _ w) hx
  obtain ⟨td, ws, htd, ha, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h₁
  obtain rfl := Equiv.ExecNumeric.evalArgs_unique ha
    (Equiv.evalArgs_cons (Sim.evalExp_var hx) Equiv.evalArgs_nil)
  exact (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).2
    ⟨td, _, htd, Equiv.evalArgs_cons (Sim.evalExp_var hy) Equiv.evalArgs_nil, hi⟩

/-- The payload of an operator case: a number type and an operator typed at it. -/
theorem hasTyp_opPair {T : IL.Id} {t : NumType} {v : Value}
    (h : Pure.TypedAt (simEnv20 B) T "nt" (numTypeV t) v) :
    HasTyp (simEnv20 B) VarEnv.empty
      (.tupT [.mk "numtype" (.varT "numtype" []), .mk "_" (.varT T [.expA (.varE "numtype")])])
      (.tuple [numTypeV t, v]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    Pure.typedV_numtype20 B t _ valsOnly_empty, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      hasTyp_of_typedAt h (by simp [VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.bind]),
      hasTypTup_nil_iff.2 rfl⟩⟩⟩

theorem typedA_intUnOp (t : IntType) (op : IntUnOp) (hv : op.valid t) :
    TypedA B (.intUnOp t op) :=
  typedA_case rfl (hasTyp_opPair ((Pure.numTyped_simEnv20 B).intUnOp t op hv))
theorem typedA_floatUnOp (t : FloatType) (op : FloatUnOp) : TypedA B (.floatUnOp t op) :=
  typedA_case rfl (hasTyp_opPair ((Pure.numTyped_simEnv20 B).floatUnOp t op))
theorem typedA_intBinOp (t : IntType) (op : IntBinOp) : TypedA B (.intBinOp t op) :=
  typedA_case rfl (hasTyp_opPair ((Pure.numTyped_simEnv20 B).intBinOp t op))
theorem typedA_floatBinOp (t : FloatType) (op : FloatBinOp) : TypedA B (.floatBinOp t op) :=
  typedA_case rfl (hasTyp_opPair ((Pure.numTyped_simEnv20 B).floatBinOp t op))
theorem typedA_intTestOp (t : IntType) (op : IntTestOp) : TypedA B (.intTestOp t op) :=
  typedA_case rfl (hasTyp_opPair ((Pure.numTyped_simEnv20 B).intTestOp t op))
theorem typedA_intRelOp (t : IntType) (op : IntRelOp) : TypedA B (.intRelOp t op) :=
  typedA_case rfl (hasTyp_opPair ((Pure.numTyped_simEnv20 B).intRelOp t op))
theorem typedA_floatRelOp (t : FloatType) (op : FloatRelOp) : TypedA B (.floatRelOp t op) :=
  typedA_case rfl (hasTyp_opPair ((Pure.numTyped_simEnv20 B).floatRelOp t op))

/-! ## Conversions -/

/-- **V2 defines a conversion only between two different number types.** -/
theorem ne_of_toShared {t₁ t₂ : NumType} {op : V2.CvtOp} (h : (op.toShared t₁ t₂).isSome) :
    t₁ ≠ t₂ := by
  rintro rfl
  rcases t₁ with (_ | _) | (_ | _) <;> cases op <;> simp [V2.CvtOp.toShared] at h


/-- A case of `admininstr` with premises, at a payload typed in the empty scope. -/
theorem typedA_caseP {op : MixopS} {t : Typ} {prems : List Prem} {w : Value}
    (hf : Sim.IntNumeric.findCase (Sim.IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d295 0 0) op = some (t, prems))
    (hw : HasTyp (simEnv20 B) VarEnv.empty t w)
    (hp : PremsOk (simEnv20 B) (caseScope VarEnv.empty t w) prems)
    (hq : Sim.IntNumeric.quantFreeAt (Sim.IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d295 0 0) op = true := by rfl) :
    TypedV (simEnv20 B) (.varT "admininstr" []) (.case op w) :=
  fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1])
    Whole.findTyp_admininstr20 Equiv.evalArgs_nil matchArgs_nil
    (Sim.IntNumeric.hasTypCase_of_findCase hf hw hp hq)

theorem numTypeV_beq {t₁ t₂ : NumType} (h : t₁ ≠ t₂) : (numTypeV t₁ == numTypeV t₂) = false := by
  rcases t₁ with (_ | _) | (_ | _) <;> rcases t₂ with (_ | _) | (_ | _) <;>
    first | exact absurd rfl h | (rw [beq_eq_false_iff_ne]; simp [numTypeV, Equiv.Execution.caseNilV])

/-- **`CVTOP`**, at every conversion V2 defines. -/
theorem typedA_cvtOp (t₁ t₂ : NumType) (op : V2.CvtOp) (h : (op.toShared t₁ t₂).isSome) :
    TypedA B (.cvtOp t₁ t₂ op) := by
  have hb := numTypeV_beq (ne_of_toShared h)
  refine typedA_caseP rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    Pure.typedV_numtype20 B t₁ _ valsOnly_empty, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      hasTyp_bind (Pure.typedV_numtype20 B t₂) _ valsOnly_empty _ _,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_bind (Pure.cvtTyped_simEnv20 B op) _
        (Sim.ConfigOk.valsOnly_bindVal valsOnly_empty _ _) _ _, hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩)
    (Sim.IntNumeric.premsOk_if (evalExp_cmpE_iff.2 ⟨numTypeV t₁, numTypeV t₂, Sim.evalExp_var ?_,
      Sim.evalExp_var ?_, ?_⟩))
  · simp [caseScope, typBinds, VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.bind]
  · simp [caseScope, typBinds, VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.bind]
  · simp [cmpValues, hb]

/-! ## Loads -/

/-- A load payload: a number type, an optional load operator typed at it, and a memory
argument. -/
theorem hasTyp_loadPayload {t : NumType} {o : Option Value} (a : V2.MemArg)
    (ho : ∀ u, o = some u → HasTyp (simEnv20 B) (VarEnv.empty.bindVal "numtype" (numTypeV t))
      (.varT "loadop_" [.expA (.varE "numtype")]) u) :
    HasTyp (simEnv20 B) VarEnv.empty
      (.tupT [.mk "numtype" (.varT "numtype" []),
        .mk "_" (.iterT (.varT "loadop_" [.expA (.varE "numtype")]) .opt),
        .mk "memarg" (.varT "memarg" [])])
      (.tuple [numTypeV t, .opt o, memargV a]) := by
  refine hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    Pure.typedV_numtype20 B t _ valsOnly_empty, hasTypTup_cons_iff.2 ⟨_, _, rfl, ?_,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_bind (Whole.typedV_memarg20 a) _
        (Sim.ConfigOk.valsOnly_bindVal valsOnly_empty _ _) _ _, hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩
  rcases o with _ | u
  · exact hasTyp_iterT_opt_iff.2 (Or.inl rfl)
  · exact hasTyp_iterT_opt_iff.2 (Or.inr ⟨u, rfl, ho u rfl⟩)

theorem typedA_floatLoad (t : FloatType) (a : V2.MemArg) : TypedA B (.floatLoad t a) :=
  typedA_case rfl (hasTyp_loadPayload a (o := none) (by simp))

theorem typedA_intLoad_none (t : IntType) (a : V2.MemArg) : TypedA B (.intLoad t none a) :=
  typedA_case rfl (hasTyp_loadPayload a (o := none) (by simp))

set_option maxHeartbeats 4000000 in
/-- **`loadop_(iNN)`**: a pack size below the width, with a signedness (checked by evaluation at
each of the ten pairs). -/
theorem hasTyp_loadop (t : IntType) (sz : PackSize) (sx : Signedness) (h : sz.width < t.width) :
    HasTyp (simEnv20 B) (VarEnv.empty.bindVal "numtype" (numTypeV (.int t)))
      (.varT "loadop_" [.expA (.varE "numtype")]) (.case "%_%" (.tuple [szV sz, sxV sx])) := by
  rcases t <;> rcases sz <;>
    simp only [IntType.width, PackSize.width, Nat.reduceLT] at h <;> rcases sx <;>
    exact ⟨30, by with_unfolding_all rfl⟩

/-- A pack size below the width of the loaded type, if any. -/
def PackOk (t : IntType) : Option (PackSize × Signedness) → Prop
  | none => True
  | some (sz, _) => sz.width < t.width

/-- **`LOAD`** of an integer type, plain or packed below its width. -/
theorem typedA_intLoad (t : IntType) (p : Option (PackSize × Signedness)) (a : V2.MemArg)
    (hp : PackOk t p) : TypedA B (.intLoad t p a) := by
  refine typedA_case rfl (hasTyp_loadPayload a ?_)
  rcases p with _ | ⟨sz, sx⟩
  · simp
  · rintro u hu
    obtain rfl := Option.some.inj hu.symm
    exact hasTyp_loadop t sz sx hp

end Silmaril.Wasm.SpecTec.Sim20.BodyTyp
