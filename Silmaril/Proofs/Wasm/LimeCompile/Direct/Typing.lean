module

public import Silmaril.Wasm.LimeCompile.Direct.Defs
public import Silmaril.Wasm.Validation.Modules

/-!
# The direct rewrite keeps validity

A typed `select (result t)` at a number type `t` has type `[t t i32] → [t]`
(`Instr_ok/select-expl`); the untyped `select` has the same type at a number operand
(`Instr_ok/select-impl`). So the rewrite keeps every instruction typing (`lowerI_ok`,
`lowerL_ok`, by mutual structural recursion on the typing derivations), every function typing
(`lowerFunc_ok`) and the module typing (`lowerModule_ok`): the lowering of a valid module is
valid, with the same module type.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Direct

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Direct

theorem lowerL_append : ∀ a b : List Instr, lowerL (a ++ b) = lowerL a ++ lowerL b
  | [], b => by rw [List.nil_append, lowerL, List.nil_append]
  | i :: a, b => by rw [List.cons_append, lowerL, lowerL, lowerL_append a b, List.cons_append]

/-- A typing of an instruction the rewrite leaves alone. -/
theorem keep {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    (e : lowerI i = i) : InstrOk C (lowerI i) it := by
  rw [e]
  exact h

/-- `lowerI` is the identity on a concrete non-structural instruction. -/
macro "lower_id" : tactic => `(tactic| (rw [lowerI] <;> simp))

/-- The typed `select` at a number type has the type of the untyped one. -/
theorem select_ok {C : Context} {t : ValType} (ht : TyOk C.toTypeCtx (C.closeVal t)) :
    InstrOk C (lowerI (.select (some [t])))
      (.plain [C.closeVal t, C.closeVal t, .i32] [C.closeVal t]) := by
  rw [lowerI]
  split
  · rename_i hn
    cases t with
    | num n => exact .parametric (.selectImpl ht .num trivial)
    | vec v => simp [selectNum, isNumType] at hn
    | ref r => simp [selectNum, isNumType] at hn
  · exact .parametric (.selectExpl ht)

mutual
/-- **The rewrite keeps an instruction typing.** -/
theorem lowerI_ok {C : Context} {i : Instr} {it : InstrType} :
    InstrOk C i it → InstrOk C (lowerI i) it
  | .parametric h => by
    cases h with
    | selectExpl ht => exact select_ok ht
    | nop => exact keep (.parametric .nop) (by lower_id)
    | unreachable h => exact keep (.parametric (.unreachable h)) (by lower_id)
    | drop h => exact keep (.parametric (.drop h)) (by lower_id)
    | selectImpl h hs hnv => exact keep (.parametric (.selectImpl h hs hnv)) (by lower_id)
  | .numeric h => keep (.numeric h) (by cases h <;> lower_id)
  | .vector h => keep (.vector h) (by cases h <;> lower_id)
  | .variable h => keep (.variable h) (by cases h <;> lower_id)
  | .memory h => keep (.memory h) (by cases h <;> lower_id)
  | .table h => keep (.table h) (by cases h <;> lower_id)
  | .reference h => keep (.reference h) (by cases h <;> lower_id)
  | .block hbt hb => by rw [lowerI]; exact .block hbt (lowerL_ok hb)
  | .loop hbt hb => by rw [lowerI]; exact .loop hbt (lowerL_ok hb)
  | .if_ hbt h₁ h₂ => by rw [lowerI]; exact .if_ hbt (lowerL_ok h₁) (lowerL_ok h₂)
  | .tryTable hbt hb hc => by rw [lowerI]; exact .tryTable hbt (lowerL_ok hb) hc
  | h@(.br ..) => keep h (by lower_id)
  | h@(.brIf ..) => keep h (by lower_id)
  | h@(.brTable ..) => keep h (by lower_id)
  | h@(.brOnNull ..) => keep h (by lower_id)
  | h@(.brOnNonNull ..) => keep h (by lower_id)
  | h@(.brOnCast ..) => keep h (by lower_id)
  | h@(.brOnCastFail ..) => keep h (by lower_id)
  | h@(.call ..) => keep h (by lower_id)
  | h@(.callRef ..) => keep h (by lower_id)
  | h@(.callIndirect ..) => keep h (by lower_id)
  | h@(.return_ ..) => keep h (by lower_id)
  | h@(.returnCall ..) => keep h (by lower_id)
  | h@(.returnCallRef ..) => keep h (by lower_id)
  | h@(.returnCallIndirect ..) => keep h (by lower_id)
  | h@(.throw ..) => keep h (by lower_id)
  | h@(.throwRef ..) => keep h (by lower_id)

/-- **The rewrite keeps an instruction-sequence typing.** -/
theorem lowerL_ok {C : Context} {is : List Instr} {it : InstrType} :
    InstrsOk C is it → InstrsOk C (lowerL is) it
  | .nil => by rw [lowerL]; exact .nil
  | .instr h => by rw [lowerL, lowerL]; exact .instr (lowerI_ok h)
  | .seq h₁ hx h₂ => by rw [lowerL_append]; exact .seq (lowerL_ok h₁) hx (lowerL_ok h₂)
  | .cons hi hx hs => by rw [lowerL]; exact .cons (lowerI_ok hi) hx (lowerL_ok hs)
  | .sub h hs hok => .sub (lowerL_ok h) hs hok
  | .frame h hok => .frame (lowerL_ok h) hok
end

/-- The rewrite keeps a function typing. -/
theorem lowerFunc_ok {C : Context} {f : Func} {d : DefType} (h : FuncOk C f d) :
    FuncOk C (lowerFunc f) d := by
  obtain ⟨hd, he, hl, hb⟩ := h
  exact .mk hd he hl (lowerL_ok hb)

/-- **The lowering of a valid module is valid, with the same module type.** -/
theorem lowerModule_ok {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    ModuleOk (lowerModule m) mt := by
  obtain ⟨htypes, himports, hC', hC, htags, hglobals, hmems, htables, hfuncs, hdata, helems,
    hstart, hexports, hdisjoint⟩ := h
  have hf : List.Forall₂ (FuncOk _) (lowerModule m).funcs _ :=
    List.forall₂_map_left_iff.mpr (hfuncs.imp fun _ _ hf => lowerFunc_ok hf)
  exact .mk htypes himports hC' hC htags hglobals hmems htables hf hdata helems hstart hexports
    hdisjoint

end Silmaril.Proofs.Wasm.LimeCompile.Direct
