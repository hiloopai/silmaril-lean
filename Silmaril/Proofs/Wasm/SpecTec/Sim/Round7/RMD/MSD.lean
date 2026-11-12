module

public import Silmaril.Wasm.SpecTec.Sim.Round7.RMD.Defs

/-!
# Round 7, `BD`: the memory SIMD rules and the backward dispatch at `BD`

Round 7 discharged the memory SIMD rules of the backward dispatch (`Step_read` 42–51,
`MemSimd.readMSD`; `Step` 22–25, `MemSimd.stepMSD`) at `BM`. At `BD`:

* rules other than 43 (`Step_read`) and 23 (`Step`) fire alike at `BD` and `BM`
  (`HAgree.fires_read_iff`, `HAgree.fires_step_iff`), so `readMSD` and `stepMSD` apply;
* rules 43 (`vload-num-val`) and 23 (`vstore-val`) call `$vbytes_`, which `BD` answers as `BM`
  does. Their leaves (`MemSimd.bwd_vloadFull`, `MemSimd.bwd_vstoreValF`) are stated for any
  builtins with `$vbytes_` answered (`VBytes`) and the state accessors and `$with_mem` not
  interpreted; `BD` has both (`vBytes_bd`, `noAcc_bd`, `withMem_bd`).

`readMSD_bd`, `stepMSD_bd`: the ten loads and four stores at `BD`, at every configuration.
`backward_upToD_restSD`: round 6's backward recursion at `configVD` and `BD`, from the
obligations of the rules without memory SIMD (`MemSimd.BackwardUpToDRestS` at `BD`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.RMD

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecStepRules (hasStepRules_wasm30)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd
open Round7.HostD (BD)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## What the two `$vbytes_` leaves need of `BD` -/

theorem bd_call_ne {x : IL.Id} (hx : x ≠ "hostcall") (ws : List ArgV) :
    (BD P hn host).call x ws = (BM P hn host).call x ws :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.bd_call_of_ne hx ws

/-- `BD` answers `$vbytes_` by the 16-byte little-endian encoding. -/
theorem vBytes_bd : VBytes (simEnv (BD P hn host)) := fun c =>
  Prims.applies_of_noClause (findDef_vbytes _)
    (by simp [simEnv, BD, withVBytes, vbytesCall, pctV, caseNilV])

/-- `BD` interprets none of the state accessors. -/
theorem noAcc_bd : BwdRead.NoAcc (BD P hn host) where
  local_ ws := (bd_call_ne (by decide) ws).trans (noAcc_vb.local_ ws)
  global ws := (bd_call_ne (by decide) ws).trans (noAcc_vb.global ws)
  table ws := (bd_call_ne (by decide) ws).trans (noAcc_vb.table ws)
  mem ws := (bd_call_ne (by decide) ws).trans (noAcc_vb.mem ws)
  elem ws := (bd_call_ne (by decide) ws).trans (noAcc_vb.elem ws)
  data ws := (bd_call_ne (by decide) ws).trans (noAcc_vb.data ws)

/-- `BD` does not interpret `$with_mem`. -/
theorem withMem_bd (ws : List ArgV) : (BD P hn host).call "with_mem" ws = none :=
  (bd_call_ne (by decide) ws).trans (call_withMem_vb ws)

/-! ## The loads -/

/-- `Step_read` 43 (`vload-num-val`) at a `configVD` image and `BD`. -/
theorem read43_bd (c : Config H) (w : Value)
    (hf : Fires (simEnv (BD P hn host)) "Step_read" 43 (.tuple [configVD hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  obtain ⟨s, f, code⟩ := c
  change Fires _ "Step_read" 43 (.tuple [cfgV (stateVF (.list (s.funcs.map (funcInstVD hn))) s f)
    (adminsToVD code), w]) at hf
  obtain ⟨a, b, op, x, arg, rfl⟩ :=
    decode_vloadD (State.hasReadRules_simEnv _).vloadNumVal (by simp) hf
  have hf₁ : Fires (simEnv (BD P hn host)) "Step_read" 43
      (.tuple [cfgV (stateVF (.list (s.funcs.map (funcInstVD hn))) s f)
        [adminToV (aconst a b), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w]) := hf
  have hf₂ := hf₁
  rw [State.adminToV_aconst, instrToVM_vecLoad] at hf₂
  obtain rfl := vload_kind_full (.inr rfl) hf₂
  obtain ⟨v, hw, hs⟩ := bwd_vloadFull noAcc_bd vBytes_bd hf₁
  exact readOblig_of (js := [.plain (.vecConst v)]) hw hs

/-- **The memory SIMD `Step_read` obligations at `BD`**, for every configuration: if one of rules
42–51 fires at the `configVD` image, the result is the image of a Core successor. -/
theorem readMSD_bd {i : Nat} (hi : i ∈ msReadRules) (c : Config H) (w : Value)
    (hf : Fires (simEnv (BD P hn host)) "Step_read" i (.tuple [configVD hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  by_cases h43 : i = 43
  · subst h43
    exact read43_bd c w hf
  · exact readMSD hi c w ((HAgree.fires_read_iff (HAgree.agreeOff_bd_bm P hn host) h43 _).1 hf)

/-! ## The stores -/

/-- `Step` 23 (`vstore-val`) at a `configVD` image and `BD`. -/
theorem step23_bd {s : Store H} {f : Frame} {code : List Admin} {w : Value}
    (hf : Fires (simEnv (BD P hn host)) "Step" 23 (.tuple [configVD hn ⟨s, f, code⟩, w])) :
    BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨a, b, cv, a₃, rfl, h₃⟩ := decode_vstoreD (
    hasStepRules_wasm30.vstoreVal |> hasRuleAt_simEnv _) (by simp) hf
  obtain ⟨x, arg, rfl⟩ := head_vecStore h₃
  rw [configVD_store3 s f a b cv rfl] at hf
  obtain ⟨s', he, hw, hs⟩ := bwd_vstoreValF vBytes_bd withMem_bd hf
  exact bwdUpTo_of_funcs he hw hs

/-- **The memory SIMD store obligations at `BD`**, for every configuration. -/
theorem stepMSD_bd {i : Nat} (hi : i ∈ stepMSRules) (c : Config H) (w : Value)
    (hf : Fires (simEnv (BD P hn host)) "Step" i (.tuple [configVD hn c, w])) :
    BwdUpToD hn P host c w := by
  by_cases h23 : i = 23
  · subst h23
    exact step23_bd hf
  · have hb : i ∉ HAgree.stepBad := by
      simp only [stepMSRules, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [HAgree.stepBad, List.mem_cons, List.not_mem_nil, or_false]
      omega
    exact stepMSD hi c w ((HAgree.fires_step_iff (HAgree.agreeOff_bd_bm P hn host) hb _).1 hf)

/-! ## The dispatch at `BD` -/

/-- **The per-rule obligations at `configVD` and `BD` from those of the rules without memory
SIMD.** -/
theorem backwardUpToD_of_restSD {V : Config H → Prop}
    (Rk : BackwardUpToDRestS V (simEnv (BD P hn host)) hn P host) :
    BackwardUpToD V (simEnv (BD P hn host)) hn P host where
  pure := Rk.pure
  read i c w hv hc hf := by
    by_cases hi : i ∈ msReadRules
    · exact readMSD_bd hi c w hf
    · exact Rk.read i hi c w hv hc hf
  step i h6 c w hv hc hf := by
    by_cases hi : i ∈ stepMSRules
    · exact stepMSD_bd hi c w hf
    · exact Rk.step i h6 hi c w hv hc hf

/-- **Round 6's backward recursion at `configVD` and `BD`**, with every memory SIMD rule
discharged, under any context-closed predicate. -/
theorem backward_upToD_restSD {V : Config H → Prop} (CV : Round6.Target.CtxClosedVals V)
    (Rk : BackwardUpToDRestS V (simEnv (BD P hn host)) hn P host)
    (c : Config H) (w : Value) (hv : V c) (hc : TypedD (simEnv (BD P hn host)) hn c)
    (hs : SStep (simEnv (BD P hn host)) (configVD hn c) w) :
    BwdUpToD hn P host c w :=
  backward_upToD CV (backwardUpToD_of_restSD Rk) (structDecodeD_simEnv _)
    (typingFactsD_simEnv _ hn) (hasStepRules_simEnv _)
    (Bwd.findRel_of_ruleAt (simEnv_execRules _).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules _).call) c w hv hc hs

end Silmaril.Wasm.SpecTec.Sim.Round7.RMD
