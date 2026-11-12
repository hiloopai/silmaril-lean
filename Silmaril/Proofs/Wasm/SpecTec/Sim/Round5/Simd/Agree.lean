module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Defs
public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Splat
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.AllTrue

/-!
# Round 5: `VecAgree` at the concrete builtins, from `VecAgreeOps`

The four bitwise fields come from round 3's `FwdSimdAgg` (`applies_vvunop`, …), the five lane
fields from this track (`extractNum`, `extractPack`, `splat`, `replaceLane`, `allTrue`); the rest
is `VecAgreeOps`. `Step_pure` 70–73 backward are this track's `bwd_vsplat`, `bwd_vextractLaneNum`,
`bwd_vextractLanePack` and `bwd_vreplaceLane`, so `BwdStep.PureOpenV` reduces to rule 64
(`pureOpenV_of_vtestop`), and `Round5.Int.Open` follows from `OpenS` (`open_of_openS`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

variable {H : Type}

/-- **Family V's `VecAgree` at the concrete builtins**, from its open part `VecAgreeOps`. -/
theorem vecAgree_of_ops {P : Profile} {hn : H → String} {host : HostSemantics H}
    (O : VecAgreeOps (simEnv (BI P hn host)) P) : Vec.VecAgree (simEnv (BI P hn host)) P where
  vvunop := FwdSimdAgg.applies_vvunop (FwdSimdAgg.vvB_builtins hn host)
  vvbinop := FwdSimdAgg.applies_vvbinop (Prims.intB_builtins hn host)
    (FwdSimdAgg.vvB_builtins hn host)
  vvternop := FwdSimdAgg.applies_vvternop (FwdSimdAgg.vvB_builtins hn host)
  vvtestop op a := by
    cases op
    exact ⟨_, FwdSimdAgg.applies_vsize, FwdSimdAgg.applies_inez a⟩
  intUnOp := O.intUnOp
  floatUnOp := O.floatUnOp
  intBinOp := O.intBinOp
  floatBinOp := O.floatBinOp
  intTernOp := O.intTernOp
  floatTernOp := O.floatTernOp
  intRelOp := O.intRelOp
  floatRelOp := O.floatRelOp
  shiftOp := O.shiftOp
  bitmask := O.bitmask
  swizzle := O.swizzle
  relaxedSwizzle := O.relaxedSwizzle
  shuffle := O.shuffle
  extUnOp := O.extUnOp
  extBinOp := O.extBinOp
  extTernOp := O.extTernOp
  narrow := O.narrow
  extractNum := extractNum P hn host
  extractPack := extractPack P hn host
  replaceLane := replaceLane P hn host
  splat := splat P hn host
  allTrue := allTrue P hn host
  convert := O.convert

/-- **`vecInstrV?` answers every SIMD instruction `Pos.SimdTyping` asks about**: the bounded ones
(`Round4.instrBnd` excludes the memory SIMD instructions, which stay on the provisional
`schemaInstrV`). -/
theorem vecInstrV?_isSome {i : Instr} (hs : Pos.InstrSimd i = true)
    (hb : Round4.instrBnd i = true) : (Vec.vecInstrV? i).isSome = true := by
  cases i <;> simp_all [Pos.InstrSimd, Round4.instrBnd, Vec.vecInstrV?]

/-- A backward rule without the `CodeEq` slack, in the shape of `BwdStep.PureOpenV`. -/
theorem codeEq_of {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {is : List Admin} {w : Value}
    (h : ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  let ⟨is', hw, hs⟩ := h
  ⟨is', is', Bwd.CodeEq.refl _, hw, hs⟩

/-- **`BwdStep.PureOpenV` from rule 64 alone**: 70–73 are proved at the concrete builtins. -/
theorem pureOpenV_of_vtestop {P : Profile} {hn : H → String} {host : HostSemantics H}
    (O : PureOpenVtestop hn P host) : BwdStep.PureOpenV hn P host := by
  intro i hi s f is w hv hc hf
  simp only [BwdStep.pureOpenR5, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact O s f is w hv hc hf
  · exact codeEq_of (bwd_vsplat hf)
  · exact codeEq_of (bwd_vextractLaneNum hf)
  · exact codeEq_of (bwd_vextractLanePack hf)
  · exact codeEq_of (bwd_vreplaceLane hf)

/-- **`Round5.Int.Open` from `OpenS`**: `vecAgree` reduces to `VecAgreeOps`, `pureOpen` to
`PureOpenVtestop`. -/
theorem open_of_openS {P : Profile} {hn : H → String} {host : HostSemantics H}
    (O : OpenS hn P host) : Int.Open hn P host where
  simd := O.simd
  refOk := O.refOk
  hostRespects := O.hostRespects
  vector := O.vector
  newDataNum := O.newDataNum
  vecAgree := vecAgree_of_ops O.vecOps
  pureOpen := pureOpenV_of_vtestop O.vtestop
  read := O.read

/-- **`Open.vector` from family V's `VecTyping` and `VecAgreeOps`**, at the concrete builtins
(`TypingFacts` is proved, `Typing.typingFacts_simEnv`). Caveat: `VecTyping.lanes` quantifies over
arbitrary lists, so `VecTyping` is presumably unsatisfiable as stated (not checked here). -/
theorem vectorFwd_of {P : Profile} {hn : H → String} {host : HostSemantics H}
    (Ty : Vec.VecTyping (simEnv (BI P hn host))) (O : VecAgreeOps (simEnv (BI P hn host)) P) :
    Int.VectorFwd hn P host := fun s f is is' h ha _ =>
  R4Fwd.open4Vector_of_agree (Typing.typingFacts_simEnv _ hn) Ty (vecAgree_of_ops O) s f is is'
    h ha

/-- **`Round5.Task.wholeStepValidOk` from `OpenS`**, at every injective encoding, finite `HostOk`
host and `Profile.spec nd r` (pass 1's `wholeStepValidOk_of_open` through `open_of_openS`). -/
theorem wholeStepValidOk_of_openS
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenS hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  Int.wholeStepValidOk_of_open fun H hn hinj host hfin hok nd r =>
    open_of_openS (h H hn hinj host hfin hok nd r)

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
