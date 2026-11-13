module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdCallAddr10T

/-!
# `memory.grow` that succeeds, forward in `simEnv10T`

Round 4's leaf at `FwdAt10T` and `bytesB10`. The grown memory instance is typed from the store
of the state typed in `simEnv10T` (`storeTy10_of_state10T`); `meminst` avoids `tbad10`, so its
typing moves back to `simEnv10` (`typedV_off10T`), where round 4's `typedV_memInst_grow10` grows
it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst MemAddr)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV stateT evalExp_case evalExp_tup2 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathSet_idx pathSet_dot
  pathSet_root evalExp_idxPayload HasClause1 idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memGrowSucceedRule sfxyPat withInstBody20 mem0E pagesE
  constNE growMemCallE evalExp_constN)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

open Silmaril.Wasm.SpecTec.Sim20.Whole (typedV_list_of_empty20 hasTypFields_cons_nil_iff
  hasTypFields_of_closed)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim (storeT)

theorem findTyp_storeF10T : (simEnv10T B).findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableinst" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "meminst" []) .list) [] []])]) := findTypT_ne findTyp_storeF10

/-- **A store image typed in `simEnv10T`, field by field.** -/
structure StoreTy10T (B : Builtins) (hn : H → String) (s : Store H) : Prop where
  funcs : TypedV (simEnv10T B) (.iterT (.varT "funcinst" []) .list)
    (.list (s.funcs.map (funcInstV hn)))
  globals : TypedV (simEnv10T B) (.iterT (.varT "globalinst" []) .list)
    (.list (s.globals.map globalInstV))
  tables : TypedV (simEnv10T B) (.iterT (.varT "tableinst" []) .list)
    (.list (s.tables.map tableInstV))
  mems : TypedV (simEnv10T B) (.iterT (.varT "meminst" []) .list)
    (.list (s.memories.map memInstV))

theorem typedV_storeV_iff10T {s : Store H} :
    TypedV (simEnv10T B) storeT (storeV hn s) ↔ StoreTy10T B hn s := by
  constructor
  · intro h
    have h₀ := hasTypFields_of_closed (findTyp_storeF10T (B := B)) h
    obtain ⟨h₁, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₂, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₃, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₄, -⟩ := hasTypFields_cons_nil_iff.1 h₀
    exact ⟨typedV_list_of_empty20 h₁, typedV_list_of_empty20 h₂, typedV_list_of_empty20 h₃,
      typedV_list_of_empty20 h₄⟩
  · intro h
    exact Sim20.Whole.typedV_structG (findTyp_storeF10T (B := B)) (Sim20.Whole.hasTypFields_consG h.funcs
      (Sim20.Whole.hasTypFields_consG h.globals (Sim20.Whole.hasTypFields_consG h.tables
        (Sim20.Whole.hasTypFields_oneG h.mems))))

/-- The store of a state typed in `simEnv10T`, field by field. -/
theorem storeTy10_of_state10T {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) : StoreTy10T B hn s :=
  typedV_storeV_iff10T.1 (typedV_stV_iff10T.1 hz).1

/-- The memories of a state typed in `simEnv10T` are typed in `simEnv10`. -/
theorem mems10_of_state10T {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) :
    TypedV (simEnv10 B) (.iterT (.varT "meminst" []) .list) (.list (s.memories.map memInstV)) :=
  typedV_off10T (goodT_of_all (by decide)) (storeTy10_of_state10T hz).mems

/-- **`memory.grow-succeed` fires forward** at `bytesB10`, at V1's successful growth. -/
theorem fires10_memGrowSucceedT {P : Profile} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    {c : BitVec 32} {d : Execution.Memory.Bytes}
    (hz : TypedV (simEnv10T (bytesB10 P)) stateT (stateV hn s f))
    (hm : frameMemory s f = some (a, m))
    (hg : Execution.Memory.grow? m.data m.max c.toNat = some d) :
    Fires (simEnv10T (bytesB10 P)) "Step" 11 (.tuple [
      configV hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩,
      configV hn ⟨setMemory s a {m with data := d}, f,
        [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩]) := by
  let σ := growScope10 (stateV hn s f) c {m with data := d}
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN c.toNat)) := rfl
  have fmi : (VarEnv.empty.bindVals σ).findVal? "mi" = some (memInstV {m with data := d}) := rfl
  obtain ⟨hal, hlt⟩ := grow_bounds10 hg
  have hmi : TypedV (simEnv10T (bytesB10 P)) (.varT "meminst" []) (memInstV {m with data := d}) :=
    typedV10T (typedV_memInst_grow10 (Sim20.Whole.typedV_of_getElem? (mems10_of_state10T hz)
      (frameMemory_some hm).2) hg)
  refine fires_of_ruleAtT (hasRuleAt10_memGrowSucceed _) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fn (typedV_n10T _ _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fmi (hmi _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (evalExp_tup2 (growLhs10 fz fn) (growRhs10 rfl rfl rfl fz fmi hm hal hlt))
    (prems_one (.ifPr (growPrem10 rfl rfl fz fn fmi hm hg)))

/-- **`memory.grow` that succeeds, forward, at `bytesB10`.** -/
theorem fwdAt10T_memGrowSucceed_bytesB10 {P : Profile} (s : Store H) (f : Frame) (a : MemAddr)
    (m : MemInst) (c : BitVec 32) (d : Execution.Memory.Bytes) (hm : frameMemory s f = some (a, m))
    (hg : Execution.Memory.grow? m.data m.max c.toNat = some d) :
    FwdAt10T (bytesB10 P) hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
      ⟨setMemory s a {m with data := d}, f,
        [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩ :=
  fun hz _ _ _ => sstepB10T_of_fires' (fires10_memGrowSucceedT hz hm hg)


end Silmaril.Wasm.SpecTec.Sim10.Whole
