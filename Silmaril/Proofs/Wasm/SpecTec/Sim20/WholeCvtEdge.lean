module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveNum

/-!
# `cvtop` at a conversion V2 does not define: the 2.0 script computes, V2 traps

The 2.0 script's `$cvtop__` (`Scripts.Wasm20.Original.d224`) has a clause
`$cvtop__(Inn_1, Inn_2, EXTEND sx, iN_1) = $extend__($sizenn1(Inn_1), $sizenn2(Inn_2), sx, iN_1)`
for **every** pair of integer types, and likewise generic `WRAP`, `PROMOTE` and `DEMOTE` clauses.
The IL type of `CVTOP numtype_1 numtype_2 cvtop` only requires `numtype_1 ≠ numtype_2`, so
`CVTOP I32 I64 (EXTEND S)` ("extend an `i64` to an `i32`") is a typed `instr`, and
`Step_pure/cvtop-val` rewrites `CONST I64 x; CVTOP I32 I64 (EXTEND S)` to `CONST I32 x'`, `x'` the
sign extension of `x` from 64 to 32 bits (`fires_cvtBad`). V2 defines no such
conversion (`CvtOp.toShared` is `none`, so `CvtOpResult` is `False`); its only step is the trap
(`pureStep_cvtBad`).

So the per-rule obligations of the backward half are **false** at any builtins that interpret
`$extend__` as the spec does (`FloatB P B`): `not_bwdLive20_floatB`, `not_bwdParts20_floatB`.
Wasm validation rejects the instruction, and V2's validation (`CvtOp.toShared … isSome`) does too;
the obligation is restored by a hypothesis that the code converts only where V2 defines the
conversion (`Whole.CvtOkCode`, `WholeBwdQ`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim (Fires)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB floatCall)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (evalExp_list1Call)

variable {B : Builtins} {P : Profile}

set_option maxRecDepth 100000

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-- A conversion V2 does not define: signed `EXTEND` from `i64` to `i32`, encoded
`CVTOP I32 I64 (EXTEND S)`. -/
abbrev cvtBad : V2.Instr := .cvtOp (.int .i32) (.int .i64) (.extend .signed)

/-- V2 defines no `EXTEND` from `i64` to `i32`. -/
theorem toShared_cvtBad : V2.CvtOp.toShared (.int .i32) (.int .i64) (.extend .signed) = none := rfl

set_option maxRecDepth 100000 in
/-- `$cvtop__(I64, I32, EXTEND S, x)` is `[$extend__(64, 32, S, x)]` (the generic `EXTEND`
clause). -/
theorem applies_cvtBad (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv20 B) "cvtop__" (Pure.cvtArgs20 (.int .i32) (.int .i64) (.extend .signed) x)
      (.list [bvV (x.signExtend 32)]) := by
  have hc : floatCall P "extend__" [.val (natV 64), .val (natV 32), .val (sxV .signed),
      .val (pctV x.toNat)] = some (bvV (x.signExtend 32)) :=
    Sim.Floats.floatCall_extend P 64 32 .signed x
  refine ⟨_, _, _, Pure.findDef_cvtop20, Or.inl ?_⟩
  exact tryClauses_hit (Pure.matchArgs_kinds20 (.inl rfl) (.inl rfl) (by decide) (by decide)
    rfl rfl (Pure.matchArgs_opSx20 (by simp) (by simp))) premsHold_nil
    (evalExp_list1Call (Pure.callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (Pure.evalArgs_sizes20 (t₁ := .int .i64) (t₂ := .int .i32) (by simp) (by simp) rfl rfl
        (Pure.evalArgs_vars20 (by simp) (by simp; rfl))) hc))

/-- **`Step_pure/cvtop-val` fires at `CONST I64 x; CVTOP I32 I64 (EXTEND S)`**, to `CONST I32 x'`
with `x'` the sign extension of `x` from 64 to 32 bits. -/
theorem fires_cvtBad (hB : FloatB P B) (x : BitVec 64) :
    Fires (simEnv20 B) "Step_pure" 26 (.tuple [.list (adminsToV [.plain (.intConst .i64 x),
      .plain cvtBad]), .list (adminsToV [constI32 (x.signExtend 32)])]) := by
  have T := Pure.numTyped_simEnv20 B
  have hl : adminsToV [.plain (.intConst .i64 x), .plain cvtBad] =
      [.case "CONST" (.tuple [numTypeV (.int .i64), numV ⟨.int .i64, x⟩]),
        .case "CVTOP" (.tuple [numTypeV (.int .i32), numTypeV (.int .i64),
          cvtOpV (.extend .signed)])] :=
    Pure.adminsToV_cvt (.int .i32) (.int .i64) (.extend .signed) x
  rw [hl]
  exact (Pure.firesB_pure20_iff B).1 (Pure.cvtopVal_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
    (T.num (.int .i64) x "nt_1" _ ⟨rfl, rfl, rfl⟩ rfl) (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
    (Pure.cvtTyped_simEnv20 B _ _ ⟨rfl, rfl, rfl⟩)
    (T.num (.int .i32) (x.signExtend 32) "nt_2" _ ⟨rfl, rfl, rfl⟩ rfl) (applies_cvtBad hB x)
    (Pure.memValue_list_iff.2 (List.mem_singleton.2 rfl)))

set_option linter.unusedTactic false in
/-- **V2's only step from `i64.const x; cvtBad` is the trap.** -/
theorem pureStep_cvtBad {x : BitVec 64} {code' : List Admin}
    (h : PureStep P [.plain (.intConst .i64 x), .plain cvtBad] code') : code' = [.trap] := by
  generalize hc : [Admin.plain (.intConst .i64 x), Admin.plain cvtBad] = c at h
  cases h <;> try simp_all [vals, constI32, aref, vconst]
  rename_i h
  obtain ⟨-, rfl, rfl, rfl⟩ := hc
  exact absurd h (by simp [CvtOpResult])

set_option maxHeartbeats 4000000 in
/-- `CONST I64 0; CVTOP I32 I64 (EXTEND S)` is a typed `instr*`. -/
theorem typed_cvtBad :
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV [.plain (.intConst .i64 0), .plain cvtBad])) :=
  ⟨VarEnv.empty, ⟨rfl, rfl, rfl⟩, 100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
/-- `CONST I32 0` is a typed `instr*`. -/
theorem typed_const0 : TypedSome (simEnv20 B) instrsT20 (.list (adminsToV [constI32 0])) :=
  ⟨VarEnv.empty, ⟨rfl, rfl, rfl⟩, 100, by with_unfolding_all rfl⟩

/-- The `Step_pure` obligation of the backward half fails at `CONST I64 0; cvtBad`. -/
theorem not_pureObl_cvtBad :
    ¬ ∃ code', adminsToV [constI32 ((0 : BitVec 64).signExtend 32)] = adminsToV code' ∧
      PureStep P [.plain (.intConst .i64 0), .plain cvtBad] code' := by
  rintro ⟨code', hw, hs⟩
  rw [pureStep_cvtBad hs] at hw
  simp [adminsToV, adminToV, instrToV, valV, caseNilV] at hw

/-- **The live obligations of the backward half are false** at any builtins that interpret the
float and conversion primitives as the spec does. -/
theorem not_bwdLive20_floatB {H : Type} (hn : H → String) (host : HostSemantics H)
    (hB : FloatB P B) : ¬ BwdLive20 B hn P host := by
  intro L
  have h₀ : (0 : BitVec 64).signExtend 32 = 0 := by decide
  have ht := typed_const0 (B := B)
  rw [← h₀] at ht
  exact not_pureObl_cvtBad (L.pure 26 (by decide) _ _ typed_cvtBad ht (fires_cvtBad hB 0))

/-- The same for the obligations before the dead rules are removed. -/
theorem not_bwdParts20_floatB {H : Type} (hn : H → String) (host : HostSemantics H)
    (hB : FloatB P B) : ¬ BwdParts20 B hn P host := by
  intro Bk
  have h₀ : (0 : BitVec 64).signExtend 32 = 0 := by decide
  have ht := typed_const0 (B := B)
  rw [← h₀] at ht
  exact not_pureObl_cvtBad (Bk.pure 26 _ _ typed_cvtBad ht (fires_cvtBad hB 0))

end Silmaril.Wasm.SpecTec.Sim20.Whole
