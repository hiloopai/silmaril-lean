module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowTyping

/-!
# `Step` 8, 9, 19 and 20 fire forward at builtins that grow

`WholeGrowB` proves the backward half at `growB`, where `table.grow-succeed` (8) and
`memory.grow-succeed` (19) can fire. This module proves that they **do** fire, at the image of
every V2 `tableGrowSucceed`/`memoryGrowSucceed` step, and likewise the two `grow-fail` rules (9,
20) at every `tableGrowFail`/`memoryGrowFail` step.

* `GrowCalls20 B`: wherever V2's growth succeeds, `B` answers `$growtable`/`$growmemory` with its
  image (the converse of `GrowAnswers20`). `growB` has it (`growCalls20_growB`).
* The quantified grown instance `ti : tableinst` (`mi : meminst`) is typed by
  `typedV_tableInst20` (`typedV_memInst20`), and the state by the typing of the configuration
  (`typedV_state_of_typed20`).
* `fires_tableGrowSucceed`, `fires_tableGrowFail`, `fires_memGrowSucceed`, `fires_memGrowFail`:
  the four rules fire from the image of V2's left-hand side to the image of V2's successor.
* `memory.grow-succeed` returns `|bytes| / (64 · $Ki)`, computed in `rat` and converted to
  `nat`. The conversion is defined only for whole pages, so its forward firing needs
  `mi.bytes.size % 65536 = 0` (`cvt_pages`). V2 does not require it of a memory instance; every
  memory V2 allocates or grows has it (allocation and growth go by whole pages).
* `sstepB_of_fires20`: a firing `Step` rule is a SpecTec step under the backend reading.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk dderives_iff_fires
  evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Builtins that answer V2's growth -/

/-- **`B` answers V2's successful growth**: the converse of `GrowAnswers20`. -/
structure GrowCalls20 (B : Builtins) : Prop where
  table : ∀ (ti ti' : TableInst) (n : Nat) (r : Ref), ti.grow? n r = some ti' →
    B.call "growtable" [.val (tableInstV ti), .val (.num (.natN n)), .val (refV r)] =
      some (tableInstV ti')
  mem : ∀ (mi mi' : MemInst) (n : Nat), mi.grow? n = some mi' →
    B.call "growmemory" [.val (memInstV mi), .val (.num (.natN n))] = some (memInstV mi')

theorem growCalls20_growB (P : Profile) : GrowCalls20 (growB P) where
  table ti ti' n r h := by rw [growB_growtable, h]; rfl
  mem mi mi' n h := by rw [growB_growmemory, h]; rfl

/-- `$growtable(T, N, R)` evaluates to `B`'s answer, at any scope not shadowing it. -/
theorem evalExp_growtable20 {ρ : VarEnv} (hd : ρ.findDef? "growtable" = none) {e₁ e₂ e₃ : Exp}
    {T N R v : Value} (h₁ : EvalExp (simEnv20 B) ρ e₁ T) (h₂ : EvalExp (simEnv20 B) ρ e₂ N)
    (h₃ : EvalExp (simEnv20 B) ρ e₃ R)
    (hB : B.call "growtable" [.val T, .val N, .val R] = some v) :
    EvalExp (simEnv20 B) ρ (.callE "growtable" [.expA e₁, .expA e₂, .expA e₃]) v := by
  obtain ⟨ps, t, cs, hf, hu⟩ := growtable20_undef (growDefs_simEnv20 B) T N R
  have hA : Applies (simEnv20 B) "growtable" [.val T, .val N, .val R] v :=
    ⟨ps, t, cs, hf, .inr ⟨hu, by rwa [simEnv20, Env.builtins_withBuiltins]⟩⟩
  exact evalExp_callE_iff.2 ((applies_iff_callDef hd
    (evalArgs_cons h₁ (evalArgs_cons h₂ (evalArgs_cons h₃ evalArgs_nil)))).1 hA)

/-- `$growmemory(M, N)` evaluates to `B`'s answer, at any scope not shadowing it. -/
theorem evalExp_growmemory20 {ρ : VarEnv} (hd : ρ.findDef? "growmemory" = none) {e₁ e₂ : Exp}
    {M N v : Value} (h₁ : EvalExp (simEnv20 B) ρ e₁ M) (h₂ : EvalExp (simEnv20 B) ρ e₂ N)
    (hB : B.call "growmemory" [.val M, .val N] = some v) :
    EvalExp (simEnv20 B) ρ (.callE "growmemory" [.expA e₁, .expA e₂]) v := by
  obtain ⟨ps, t, cs, hf, hu⟩ := growmemory20_undef (growDefs_simEnv20 B) M N
  have hA : Applies (simEnv20 B) "growmemory" [.val M, .val N] v :=
    ⟨ps, t, cs, hf, .inr ⟨hu, by rwa [simEnv20, Env.builtins_withBuiltins]⟩⟩
  exact evalExp_callE_iff.2 ((applies_iff_callDef hd
    (evalArgs_cons h₁ (evalArgs_cons h₂ evalArgs_nil))).1 hA)

/-- An `if a = b` premise whose sides evaluate alike. -/
theorem evalExp_eqTrue {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h₁ : EvalExp env ρ e₁ v) (h₂ : EvalExp env ρ e₂ v) :
    EvalExp env ρ (.cmpE .eqOp .boolT e₁ e₂) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨v, v, h₁, h₂, cmpValues_eq_true_iff.2 rfl⟩

/-! ## From a firing rule to a step -/

/-- **A firing `Step` rule is a SpecTec step** under the backend reading. -/
theorem sstepB_of_fires20 {i : Nat} {v w : Value}
    (hf : Fires (simEnv20 B) "Step" i (.tuple [v, w])) : SStepB (simEnv20 B) v w := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_tableGrowSucceedV (B := B)
  exact (sstepB20_iff B).2 ((dderives_iff_fires hrel).2 ⟨i, hf⟩)

/-! ## The left-hand sides -/

/-- `CONST I32 (% n)` at `n` bound to the constant's payload. -/
theorem evalExp_constNE {env : Env} {ρ : VarEnv} {c : BitVec 32}
    (fn : ρ.findVal? "n" = some (.num (.natN c.toNat))) :
    EvalExp env ρ constNE (adminToV (constI32 c)) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var fn) evalExps_nil, rfl⟩)))

/-- `z; ref CONST I32 (% n) TABLE.GROW x`, the left-hand side of rules 8 and 9. -/
theorem evalExp_tableGrowLhs {env : Env} {ρ : VarEnv} {s : Store H} {f : Frame} {x : TableIdx}
    {n : BitVec 32} {r : Ref} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fr : ρ.findVal? "ref" = some (refV r)) (fn : ρ.findVal? "n" = some (.num (.natN n.toNat)))
    (fx : ρ.findVal? "x" = some (idxV x)) :
    EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .subE (.varE "ref") (.varT "ref" []) (.varT "admininstr" []), constNE,
      .caseE "TABLE.GROW" (.varE "x")]]))
      (configV hn ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩) := by
  have hr : adminToV (aref r) = refV r := Pure.adminToV_toAdmin (.ref r)
  refine evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_subE_iff.2 (evalExp_var fr)) (evalExps_cons (evalExp_constNE fn)
      (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil)), ?_⟩))
  simp only [adminsToV, hr]
  rfl

/-- `z; CONST I32 (% n) MEMORY.GROW`, the left-hand side of rules 19 and 20. -/
theorem evalExp_memGrowLhs {env : Env} {ρ : VarEnv} {s : Store H} {f : Frame} {n : BitVec 32}
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fn : ρ.findVal? "n" = some (.num (.natN n.toNat))) :
    EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [constNE,
      .caseE "MEMORY.GROW" (.tupE [])]]))
      (configV hn ⟨s, f, [constI32 n, .plain .memoryGrow]⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constNE fn) (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil,
      rfl⟩)) evalExps_nil), rfl⟩))

/-! ## Whole pages -/

/-- A whole number of pages, converted from `rat`, is the natural quotient. -/
theorem cvt_pages {k : Nat} (h : k % 65536 = 0) :
    Num.cvt .natT (.ratN ((k : Rat) / 65536)) = some (.natN (k / 65536)) := by
  obtain ⟨p, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  have hq : ((65536 * p : Nat) : Rat) / 65536 = (p : Rat) := by
    push_cast
    field_simp
  rw [hq, Nat.mul_div_cancel_left p (by norm_num)]
  simp [Num.cvt]

/-- `|$mem(z, 0).BYTES| / (64 · $Ki)` is the page count, for a memory of whole pages. -/
theorem evalExp_pagesE {ρ : VarEnv} {s : Store H} {f : Frame} {a : Nat} {mi : MemInst}
    (hρ : ρ.findDef? "mem" = none) (hk : ρ.findDef? "Ki" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hpg : mi.bytes.size % 65536 = 0) :
    EvalExp (simEnv20 B) ρ pagesE (.num (.natN mi.pages)) :=
  evalExp_cvtNum (evalExp_pagesQ hρ hk fz ha hm) (cvt_pages hpg)

/-! ## The four rules, forward -/

/-- **`Step/table.grow-succeed` fires forward** at the image of V2's `tableGrowSucceed`, at
builtins answering V2's growth, from a typed state. -/
theorem fires_tableGrowSucceed (hG : GrowCalls20 B) {s : Store H} {f : Frame} {x : TableIdx}
    {n : BitVec 32} {r : Ref} {a : Nat} {ti ti' : TableInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hg : ti.grow? n.toNat r = some ti') :
    Fires (simEnv20 B) "Step" 8 (.tuple [
      configV hn ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩,
      configV hn ⟨s.setTableInst a ti', f, [constI32 (BitVec.ofNat 32 ti.refs.length)]⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("ref", refV r),
    ("n", .num (.natN n.toNat)), ("x", idxV x), ("ti", tableInstV ti')]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refV r) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have fti : (VarEnv.empty.bindVals σ).findVal? "ti" = some (tableInstV ti') := rfl
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) [.expP "z" (.varT "state" []),
      .expP "ref" (.varT "ref" []), .expP "n" (.varT "n" []), .expP "x" (.varT "idx" []),
      .expP "ti" (.varT "tableinst" [])] :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fr (typedV_ref20 r _ hρ)
      (QuantsOk.cons fn (typedV_n20 _ _ hρ) (QuantsOk.cons fx (typedV_idx20 x _ hρ)
        (QuantsOk.cons fti (typedV_tableInst20 ti' _ hρ) QuantsOk.nil))))
  have et : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) tableE (tableInstV ti) :=
    evalExp_table20 rfl (evalExp_var fz) (evalExp_var fx) ha ht
  have ecall : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) growTableCallE (tableInstV ti') :=
    evalExp_growtable20 rfl et (evalExp_var fn) (evalExp_var fr) (hG.table ti ti' _ r hg)
  refine Pure.fires_of_ruleAt hasRuleAt_tableGrowSucceedV σ hq
    (evalExp_tup2 (evalExp_tableGrowLhs fz fr fn fx)
      (tableGrowRhs_eval rfl rfl fz fx fti ha ht (refs_lt_of_grow hg))) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue ecall (evalExp_var fti))

/-- **`Step/table.grow-fail` fires forward** at the image of V2's `tableGrowFail`, from a typed
state. It has no premise, so it fires at any builtins. -/
theorem fires_tableGrowFail {s : Store H} {f : Frame} {x : TableIdx} {n : BitVec 32} {r : Ref}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) :
    Fires (simEnv20 B) "Step" 9 (.tuple [
      configV hn ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩,
      configV hn ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("ref", refV r),
    ("n", .num (.natN n.toNat)), ("x", idxV x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refV r) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  exact Pure.fires_of_ruleAt hasRuleAt_tableGrowFail σ
    (QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fr (typedV_ref20 r _ hρ)
      (QuantsOk.cons fn (typedV_n20 _ _ hρ) (QuantsOk.cons fx (typedV_idx20 x _ hρ)
        QuantsOk.nil))))
    (evalExp_tup2 (evalExp_tableGrowLhs fz fr fn fx) (growFail_rhs rfl fz)) Pure.prems_nil

/-- **`Step/memory.grow-succeed` fires forward** at the image of V2's `memoryGrowSucceed`, at
builtins answering V2's growth, from a typed state, for a memory of whole pages. -/
theorem fires_memGrowSucceed (hG : GrowCalls20 B) {s : Store H} {f : Frame} {n : BitVec 32}
    {a : Nat} {mi mi' : MemInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hg : mi.grow? n.toNat = some mi') (hpg : mi.bytes.size % 65536 = 0) :
    Fires (simEnv20 B) "Step" 19 (.tuple [
      configV hn ⟨s, f, [constI32 n, .plain .memoryGrow]⟩,
      configV hn ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN n.toNat)),
    ("mi", memInstV mi')]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)) := rfl
  have fmi : (VarEnv.empty.bindVals σ).findVal? "mi" = some (memInstV mi') := rfl
  have em : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) mem0E (memInstV mi) :=
    evalExp_mem20 rfl (evalExp_var fz) evalExp_idx0 ha hm
  have ecall : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) growMemCallE (memInstV mi') :=
    evalExp_growmemory20 rfl em (evalExp_var fn) (hG.mem mi mi' _ hg)
  have hlt : mi.pages < 4294967296 := pages_lt_of_grow hg
  have hv : configV hn ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩ =
      .case "%;%" (.tuple [stateV hn (s.setMemInst a mi') f,
        .list [.case "CONST" (.tuple [caseNilV "I32", .case "%" (.tuple [.num (.natN mi.pages)])])]]) := by
    simp [configV, adminsToV, adminToV_constI32, Nat.mod_eq_of_lt hlt, pctV]
  have erhs : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [withMeminstE, .listE [constI32E pagesE]]))
      (configV hn ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩) := by
    rw [hv]
    exact evalExp_case (evalExp_tup2 (evalExp_withMeminst20 rfl (evalExp_var fz) evalExp_idx0
      (evalExp_var fmi) ha hm) (evalExp_list1 (evalExp_case (evalExp_tup2
        (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
          (evalExp_pagesE rfl rfl fz ha hm hpg) evalExps_nil, rfl⟩))))))
  refine Pure.fires_of_ruleAt hasRuleAt_memGrowSucceedV σ
    (QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fn (typedV_n20 _ _ hρ)
      (QuantsOk.cons fmi (typedV_memInst20 mi' _ hρ) QuantsOk.nil)))
    (evalExp_tup2 (evalExp_memGrowLhs fz fn) erhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue ecall (evalExp_var fmi))

/-- **`Step/memory.grow-fail` fires forward** at the image of V2's `memoryGrowFail`, from a typed
state, at any builtins. -/
theorem fires_memGrowFail {s : Store H} {f : Frame} {n : BitVec 32}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) :
    Fires (simEnv20 B) "Step" 20 (.tuple [configV hn ⟨s, f, [constI32 n, .plain .memoryGrow]⟩,
      configV hn ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN n.toNat))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)) := rfl
  exact Pure.fires_of_ruleAt (hasRuleAt_memGrowFail B) σ
    (QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fn (typedV_n20 _ _ hρ) QuantsOk.nil))
    (evalExp_tup2 (evalExp_memGrowLhs fz fn) (growFail_rhs rfl fz)) Pure.prems_nil

end Silmaril.Wasm.SpecTec.Sim20.Whole
