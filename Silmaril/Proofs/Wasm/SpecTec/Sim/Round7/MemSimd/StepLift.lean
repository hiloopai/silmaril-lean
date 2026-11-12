module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadLane

/-!
# Round 7, memory SIMD: the vector loads as `Step` steps

The load rules (`Step_read` 42–51) are reached from `Step` through `Step/read` (rule 1), which
needs the state and both instruction sequences typed. Every vector load's left-hand side
(`CONST at i`, possibly `VCONST V128 c`, then the load encoded by `instrToVM`) and result (`TRAP`
or `VCONST V128 c`) is a typed `instr*` (`typedV_instrs_of`, with `Typing.typedV_instr_val` and
round 6's `MemSimd.typedV_vecLoad`/`typedV_vecLoadLane`), so each `Step_read` lemma lifts:

* `step_of_read`: a `Step_read` step in both readings gives a `Step` step in both readings
  (round 5's `sstep_read` and round 6's `Reading.sstepB_read`);
* `stepFwd_vecLoadOob`, `stepFwd_vecLoadLaneOob`, `stepFwd_vecLoadFull`, `stepFwd_vecLoadZero`,
  `stepFwd_vecLoadSplat`, `stepFwd_vecLoadLane`: **Core's vector loads, forward, as SpecTec
  `Step` steps** at `withVBytes (Prims.builtins …)` (the out-of-bounds ones at every `B`), in
  the declarative reading and at round 6's backend reading `Round6.Int.backend`.

These are single-redex steps: the configuration is exactly the redex. Steps inside evaluation
contexts (`Step/ctxt-*`) are round 6's context lemmas, stated for `configV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (invLanes)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- An instruction sequence is a typed `instr*` when each element is a typed `instr`. -/
theorem typedV_instrs_of {env : Env} {l : List Value}
    (h : ∀ u ∈ l, TypedV env (.varT "instr" []) u) : TypedV env instrsT (.list l) :=
  fun ρ hρ => hasTyp_iterT_list_iff.2 ⟨l, rfl, hasTypList_iff.2 fun u hu => h u hu ρ hρ⟩

/-- **`Step/read`, in both readings**: a `Step_read` step from a typed state, between typed
instruction sequences, is a `Step` step, declaratively and at round 6's backend reading. -/
theorem step_of_read {z : Value} {is js : List Value} (hz : TypedV (simEnv B) stateT z)
    (his : ∀ u ∈ is, TypedV (simEnv B) (.varT "instr" []) u)
    (hjs : ∀ u ∈ js, TypedV (simEnv B) (.varT "instr" []) u)
    (h : SRead (simEnv B) (cfgV z is) js ∧ Round6.Reading.SReadB (simEnv B) (cfgV z is) js) :
    SStep (simEnv B) (cfgV z is) (cfgV z js) ∧
      (Round6.Int.backend).step B (cfgV z is) (cfgV z js) :=
  ⟨sstep_read (hasStepRules_simEnv B).read hz (typedV_instrs_of his) (typedV_instrs_of hjs) h.1,
    Round6.Reading.sstepB_read (hasStepRules_simEnv B).read hz (typedV_instrs_of his)
      (typedV_instrs_of hjs) h.2⟩

/-- A value instruction is a typed `instr`. -/
theorem typedV_instr_admin (v : Val) :
    TypedV (simEnv B) (.varT "instr" []) (adminToV v.toAdmin) := by
  rw [State.adminToV_toAdmin]; exact Typing.typedV_instr_val v

/-- `TRAP` is a typed `instr`. -/
theorem typedV_instr_trap : TypedV (simEnv B) (.varT "instr" []) (adminToV .trap) :=
  Round4.typedV_trap

/-- The left-hand side of a vector load, typed. -/
theorem typedV_vloadLhs (a : AddrType) (i : BitVec a.intType.width) (op : VecLoadOp) (x : MemIdx)
    (arg : MemArg) : ∀ u ∈ [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)],
      TypedV (simEnv B) (.varT "instr" []) u := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact typedV_instr_admin (.num ⟨.int a.intType, i⟩)
  · rw [List.mem_singleton.1 hu]; exact Round6.MemSimd.typedV_vecLoad op x arg

/-- The left-hand side of a lane load, typed. -/
theorem typedV_vloadLaneLhs (a : AddrType) (i : BitVec a.intType.width) (v : BitVec 128)
    (p : PackSize) (x : MemIdx) (arg : MemArg) (j : LaneIdx) :
    ∀ u ∈ [adminToV (aconst a i), valV (.vec v),
      Round6.MemSimd.instrToVM (.vecLoadLane p x arg j)],
      TypedV (simEnv B) (.varT "instr" []) u := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact typedV_instr_admin (.num ⟨.int a.intType, i⟩)
  rcases List.mem_cons.1 hu with rfl | hu
  · exact Typing.typedV_instr_val (.vec v)
  · rw [List.mem_singleton.1 hu]; exact Round6.MemSimd.typedV_vecLoadLane p x arg j

/-- A single `TRAP`, typed. -/
theorem typedV_trapRhs : ∀ u ∈ [adminToV .trap],
    TypedV (simEnv B) (.varT "instr" []) u := by
  intro u hu; rw [List.mem_singleton.1 hu]; exact typedV_instr_trap

/-- A single `VCONST`, typed. -/
theorem typedV_vconstRhs (r : BitVec 128) : ∀ u ∈ [adminToV (.plain (.vecConst r))],
    TypedV (simEnv B) (.varT "instr" []) u := by
  intro u hu; rw [List.mem_singleton.1 hu]; exact typedV_instr_admin (.vec r)

/-! ## Core's vector loads as `Step` steps -/

section Loads

variable {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
  {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}

/-- **`vecLoadOob` as a `Step` step**, in both readings, at every `B`. -/
theorem stepFwd_vecLoadOob {op : VecLoadOp}
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (h : mi.bytes.size < effAddr i.toNat arg + op.accessWidth / 8) :
    SStep (simEnv B) (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad op x arg)]) (cfgV (stateV hn s f) [adminToV .trap]) ∧
      (Round6.Int.backend).step B (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad op x arg)]) (cfgV (stateV hn s f) [adminToV .trap]) :=
  step_of_read hz (typedV_vloadLhs a i op x arg) typedV_trapRhs (fwd_vecLoadOob hz hm h)

/-- **`vecLoadLaneOob` as a `Step` step**, in both readings, at every `B`. -/
theorem stepFwd_vecLoadLaneOob {sz : PackSize} {j : LaneIdx} {v : BitVec 128}
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
    SStep (simEnv B) (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec v),
        Round6.MemSimd.instrToVM (.vecLoadLane sz x arg j)])
        (cfgV (stateV hn s f) [adminToV .trap]) ∧
      (Round6.Int.backend).step B (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec v),
        Round6.MemSimd.instrToVM (.vecLoadLane sz x arg j)])
        (cfgV (stateV hn s f) [adminToV .trap]) :=
  step_of_read hz (typedV_vloadLaneLhs a i v sz x arg j) typedV_trapRhs
    (fwd_vecLoadLaneOob hz hm h)

/-- **`v128.load` in bounds as a `Step` step**, in both readings, at `withVBytes B`. -/
theorem stepFwd_vecLoadFull {c : BitVec (8 * 16)}
    (hz : TypedV (simEnv (withVBytes B)) stateT (stateV hn s f))
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) 16 = some c) :
    let v := vecLoadResult .full c
    SStep (simEnv (withVBytes B)) (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad .full x arg)])
        (cfgV (stateV hn s f) [adminToV (.plain (.vecConst v))]) ∧
      (Round6.Int.backend).step (withVBytes B) (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad .full x arg)])
        (cfgV (stateV hn s f) [adminToV (.plain (.vecConst v))]) :=
  step_of_read hz (typedV_vloadLhs a i .full x arg) (typedV_vconstRhs _) (fwd_vecLoadFull hz hm hl)

/-- **`v128.loadN_zero` in bounds as a `Step` step**, in both readings. -/
theorem stepFwd_vecLoadZero {P : Numerics.Profile} (Bf : FwdMem.BytesFuns (simEnv B))
    (hF : Floats.FloatB P B) {N : Nat} (hN : N = 32 ∨ N = 64) {c : BitVec (8 * (N / 8))}
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (N / 8) = some c) :
    SStep (simEnv B) (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad (zeroOp N) x arg)])
        (cfgV (stateV hn s f) [adminToV (.plain (.vecConst (c.setWidth 128)))]) ∧
      (Round6.Int.backend).step B (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad (zeroOp N) x arg)])
        (cfgV (stateV hn s f) [adminToV (.plain (.vecConst (c.setWidth 128)))]) :=
  step_of_read hz (typedV_vloadLhs a i _ x arg) (typedV_vconstRhs _)
    (fwd_vecLoadZero Bf hF hN hz hm hl)

/-- **A splat load in bounds as a `Step` step**, in both readings, at the integer shape `sh`. -/
theorem stepFwd_vecLoadSplat {P : Numerics.Profile} {host : HostSemantics H} (sh : IntShape)
    {c : BitVec (8 * (sh.laneWidth / 8))}
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn s f))
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (sh.laneWidth / 8) =
      some c) :
    let r := invLanes sh.laneWidth (List.replicate sh.lanes (c.setWidth sh.laneWidth))
    SStep (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (.splat (packOf sh)) x arg)])
        (cfgV (stateV hn s f) [adminToV (.plain (.vecConst r))]) ∧
      (Round6.Int.backend).step (withVBytes (Prims.builtins P hn host)) (cfgV (stateV hn s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad (.splat (packOf sh)) x arg)])
        (cfgV (stateV hn s f) [adminToV (.plain (.vecConst r))]) :=
  step_of_read hz (typedV_vloadLhs a i _ x arg) (typedV_vconstRhs _)
    (fwd_vecLoadSplat_shape sh hz hm hl)

/-- **A lane load in bounds as a `Step` step**, in both readings, at the integer shape `sh` and
an in-range lane. -/
theorem stepFwd_vecLoadLane {P : Numerics.Profile} {host : HostSemantics H} (sh : IntShape)
    {j : LaneIdx} {v : BitVec 128} {k : BitVec (8 * (sh.laneWidth / 8))} (hj : j.val < sh.lanes)
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn s f))
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (sh.laneWidth / 8) =
      some k) :
    let r := Shape.invLanes (.int sh) ((Shape.lanesOf (.int sh) v).set j.val
      (k.setWidth (Shape.int sh).laneWidth))
    SStep (simEnv (withVBytes (Prims.builtins P hn host))) (cfgV (stateV hn s f)
        [adminToV (aconst a i), valV (.vec v),
          Round6.MemSimd.instrToVM (.vecLoadLane (packOf sh) x arg j)])
        (cfgV (stateV hn s f) [adminToV (.plain (.vecConst r))]) ∧
      (Round6.Int.backend).step (withVBytes (Prims.builtins P hn host)) (cfgV (stateV hn s f)
        [adminToV (aconst a i), valV (.vec v),
          Round6.MemSimd.instrToVM (.vecLoadLane (packOf sh) x arg j)])
        (cfgV (stateV hn s f) [adminToV (.plain (.vecConst r))]) :=
  step_of_read hz (typedV_vloadLaneLhs a i v _ x arg j) (typedV_vconstRhs _)
    (fwd_vecLoadLane_shape sh hj hz hm hl)

end Loads

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
