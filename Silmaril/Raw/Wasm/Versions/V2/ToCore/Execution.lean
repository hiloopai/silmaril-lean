module

public import Silmaril.Foundations.ForwardSim
public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Sim.Pure
public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Sim.Read
public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Sim.State

@[expose] public section

/-! # Wasm 2.0 execution is simulated by Core 3.0 execution

The execution half of the `2.0 ⊆ 3.0` subset theorem, the analogue of
`Silmaril/Wasm/Lime1/ToCore/Execution.lean`: a forward simulation from
`Silmaril.Wasm.V2.Execution.Step` into `Silmaril.Wasm.Execution.Core.Step` over
the relation `Sim` of `V2/ToCore/Runtime.lean`, with the consequences for finite
runs (`Steps.toCore`), divergence (`Diverges.toCore`) and results
(`Sim.result`).

## One 2.0 step is *one or more* Core steps

`Relation.TransGen`, not `Relation.ReflTransGen`, for two reasons.

1. `Diverges.toCore` needs at least one Core step per 2.0 step, exactly as in
   `Lime1`.
2. `Sim` relates a 2.0 configuration to Core configurations that are up to one
   `Step_read/ref.null` *behind* it, once per null reference on the stack: the
   2.0 value `REF.NULL rt` is the Core *instruction* `REF.NULL ht`, which takes
   a step to become the Core *value* `REF.NULL_ADDR`. `ToCoreSim.catchUp`
   (`Sim/Common.lean`) runs those steps before the simulating step; see the
   module docstring of `V2/ToCore/Runtime.lean`.

## Which rules are lock-step

Almost all of them. 2.0's bulk table and memory operations
(`table.fill/copy/init`, `memory.fill/copy/init`) reduce **one element or byte
per step** and emit the same residual sequence as Core 3.0's, so they are
lock-step — unlike `Lime1`, whose bulk operations are atomic and need the loop
inductions of `Lime1/ToCore/Sim/Memory{Bulk,Copy,Fill}.lean`. The exceptions,
listed in the docstrings of `Sim/Read.lean` and `Sim/State.lean`, are:

* `Step_read/call_indirect-call` — Core 3.0 expands `CALL_INDIRECT x y` to
  `TABLE.GET x; REF.CAST (ref null $y); CALL_REF y`, so three Core steps;
* `Step_read/call_indirect-trap` — one, two or three, depending on which premise
  fails;
* `Step_read/call` — still one Core step, but the Core `CALL_REF` annotation has
  to be read out of the store (`Store.funcDefType`), which needs `ModWF`.

## **Deviation from the unit brief: the profile is not fixed to `Profile.spec`**

The brief asked for `Core.Step coreProfile tgt` with
`coreProfile = Profile.spec`, as in `Lime1/ToCore/Execution.lean`. The `Lime1`
machine is *not* profile-indexed, so there `Profile.spec` is a genuine choice.
The 2.0 machine **is** profile-indexed (`Step P src`), and 2.0's
`FloatUnOpResult P`, `FloatBinOpResult P`, `VecFloatUnOpResult P`,
`VecFloatBinOpResult P` and `VecCvtOpResult P` are *definitionally* Core's
`floatUnOpP P`, `floatBinOpP P`, `VecFloatUnOpRel P`, `VecFloatBinOpRel P` and
`VecConvertRel P`. So the theorems are stated for a **common** `P`, which is
strictly stronger than the fixed-profile form and does not need a profile
refinement lemma. `coreProfile` is kept, and `Step.toCore_spec` is the
specialisation the brief asked for.

## `Step/local.set` and the range premise

The simulation was once **false** at `local.set`: 2.0's `Step.localSet` carried
no `x.toNat < |f.LOCALS|` premise, so for a configuration whose code is
`val (LOCAL.SET x)` with `x` out of range the 2.0 machine stepped (Lean's
`List.set` is the identity out of range) while Core 3.0's
`VariableStep.localSet`, which carries the premise, was stuck — no `c'` existed.
The repair was in the *source* rule, not here: SpecTec's `$with_local`
(`5-runtime-aux:104`) is a **partial** array update, so `Step.localSet` now
carries `hx : x.toNat < f.locals.length`, which is exactly what
`ToCoreSim.state_localSet` needs. See `V2/Execution/Step.lean`.

No other Core 3.0 rule targeted by this dispatch has a premise that the 2.0 rule
or `ConfigWF` fails to supply: every case below passes the 2.0 rule's own
premises (`‹_›`), the `Sim` hypothesis, and — for the two store-threading
context rules — `Step.storeExt`.
-/

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- Core profile used for the specialised subset theorems; the same choice as
`Silmaril.Wasm.Lime1.Execution.coreProfile`. -/
abbrev coreProfile : Profile := Profile.spec

/-- No 2.0 rule deallocates or retypes a function, and a host call extends the
store by hypothesis, so the function part of the store only grows. -/
theorem Step.storeExt {P : Profile} {src : HostSemantics H} (hosts : HostPreserves src)
    {a b : Config H} (h : Step P src a b) (hwf : StoreWF a.store) :
    StoreExt a.store b.store := by
  induction h with
  | ctxtInstrs _ _ ih => exact ih hwf
  | ctxtLabel _ ih => exact ih hwf
  | ctxtFrame _ ih => exact ih hwf
  | callAddrHost _ _ _ hhost => exact (hosts _ _ _ _ _ hhost hwf).2
  | _ => exact fun _ fi h => ⟨fi, h, rfl⟩

/-- **Milestone.** One Wasm 2.0 step is simulated by at least one Core 3.0 step. -/
theorem Step.toCore {P : Profile} {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {a b : Config H} {c : ToCore.CConfig H}
    (h : Step P src a b) (hs : Sim a c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧ Sim b c' := by
  induction h generalizing c with
  | pure hp =>
    cases hp with
    | unreachable => exact ToCoreSim.pure_unreachable hs
    | nop => exact ToCoreSim.pure_nop hs
    | drop => exact ToCoreSim.pure_drop hs
    | selectTrue => exact ToCoreSim.pure_selectTrue ‹_› hs
    | selectFalse => exact ToCoreSim.pure_selectFalse hs
    | ifTrue => exact ToCoreSim.pure_ifTrue ‹_› hs
    | ifFalse => exact ToCoreSim.pure_ifFalse hs
    | labelVals => exact ToCoreSim.pure_labelVals hs
    | brZero => exact ToCoreSim.pure_brZero ‹_› ‹_› hs
    | brSucc => exact ToCoreSim.pure_brSucc ‹_› hs
    | brIfTrue => exact ToCoreSim.pure_brIfTrue ‹_› hs
    | brIfFalse => exact ToCoreSim.pure_brIfFalse hs
    | brTableLt => exact ToCoreSim.pure_brTableLt ‹_› hs
    | brTableGe => exact ToCoreSim.pure_brTableGe ‹_› hs
    | frameVals => exact ToCoreSim.pure_frameVals ‹_› hs
    | returnFrame => exact ToCoreSim.pure_returnFrame ‹_› hs
    | returnLabel => exact ToCoreSim.pure_returnLabel hs
    | trapVals => exact ToCoreSim.pure_trapVals ‹_› hs
    | trapLabel => exact ToCoreSim.pure_trapLabel hs
    | trapFrame => exact ToCoreSim.pure_trapFrame hs
    | intUnOp => exact ToCoreSim.pure_intUnOp ‹_› hs
    | floatUnOp => exact ToCoreSim.pure_floatUnOp ‹_› hs
    | intUnOpTrap => exact ToCoreSim.pure_intUnOpTrap ‹_› hs
    | floatUnOpTrap => exact ToCoreSim.pure_floatUnOpTrap ‹_› hs
    | intBinOp => exact ToCoreSim.pure_intBinOp ‹_› hs
    | floatBinOp => exact ToCoreSim.pure_floatBinOp ‹_› hs
    | intBinOpTrap => exact ToCoreSim.pure_intBinOpTrap ‹_› hs
    | floatBinOpTrap => exact ToCoreSim.pure_floatBinOpTrap ‹_› hs
    | testOp => exact ToCoreSim.pure_testOp hs
    | intRelOp => exact ToCoreSim.pure_intRelOp hs
    | floatRelOp => exact ToCoreSim.pure_floatRelOp hs
    | cvtOp => exact ToCoreSim.pure_cvtOp ‹_› hs
    | cvtOpTrap => exact ToCoreSim.pure_cvtOpTrap ‹_› hs
    | refIsNullTrue => exact ToCoreSim.pure_refIsNullTrue hs
    | refIsNullFalse => exact ToCoreSim.pure_refIsNullFalse ‹_› hs
    | vvUnOp => exact ToCoreSim.pure_vvUnOp hs
    | vvBinOp => exact ToCoreSim.pure_vvBinOp hs
    | vvTernOp => exact ToCoreSim.pure_vvTernOp hs
    | vvTestOp => exact ToCoreSim.pure_vvTestOp hs
    | vecIntUnOp => exact ToCoreSim.pure_vecIntUnOp ‹_› hs
    | vecFloatUnOp => exact ToCoreSim.pure_vecFloatUnOp ‹_› hs
    | vecIntUnOpTrap => exact ToCoreSim.pure_vecIntUnOpTrap ‹_› hs
    | vecFloatUnOpTrap => exact ToCoreSim.pure_vecFloatUnOpTrap ‹_› hs
    | vecIntBinOp => exact ToCoreSim.pure_vecIntBinOp ‹_› hs
    | vecFloatBinOp => exact ToCoreSim.pure_vecFloatBinOp ‹_› hs
    | vecIntBinOpTrap => exact ToCoreSim.pure_vecIntBinOpTrap ‹_› hs
    | vecFloatBinOpTrap => exact ToCoreSim.pure_vecFloatBinOpTrap ‹_› hs
    | vecAllTrueTrue => exact ToCoreSim.pure_vecAllTrueTrue ‹_› hs
    | vecAllTrueFalse => exact ToCoreSim.pure_vecAllTrueFalse ‹_› hs
    | vecIntRelOp => exact ToCoreSim.pure_vecIntRelOp hs
    | vecFloatRelOp => exact ToCoreSim.pure_vecFloatRelOp hs
    | vecShiftOp => exact ToCoreSim.pure_vecShiftOp hs
    | vecBitmask => exact ToCoreSim.pure_vecBitmask hs
    | vecSwizzle => exact ToCoreSim.pure_vecSwizzle hs
    | vecShuffle => exact ToCoreSim.pure_vecShuffle ‹_› hs
    | vecSplat => exact ToCoreSim.pure_vecSplat hs
    | vecExtractLane => exact ToCoreSim.pure_vecExtractLane ‹_› hs
    | vecReplaceLane => exact ToCoreSim.pure_vecReplaceLane ‹_› hs
    | vecExtUnOp => exact ToCoreSim.pure_vecExtUnOp ‹_› hs
    | vecExtBinOp => exact ToCoreSim.pure_vecExtBinOp ‹_› hs
    | vecNarrow => exact ToCoreSim.pure_vecNarrow hs
    | vecCvtOp => exact ToCoreSim.pure_vecCvtOp ‹_› hs
    | localTee => exact ToCoreSim.pure_localTee hs
  | read hr =>
    cases hr with
    | block => exact ToCoreSim.read_block ‹_› ‹_› hs
    | loop => exact ToCoreSim.read_loop ‹_› ‹_› hs
    | call => exact ToCoreSim.read_call ‹_› hs
    | callIndirectCall => exact ToCoreSim.read_callIndirectCall ‹_› ‹_› ‹_› ‹_› hs
    | callIndirectTrap => exact ToCoreSim.read_callIndirectTrap ‹_› ‹_› hs
    | callAddr => exact ToCoreSim.read_callAddr ‹_› ‹_› ‹_› hs
    | refFunc => exact ToCoreSim.read_refFunc ‹_› hs
    | localGet => exact ToCoreSim.read_localGet ‹_› hs
    | globalGet => exact ToCoreSim.read_globalGet ‹_› hs
    | tableGetTrap => exact ToCoreSim.read_tableGetTrap ‹_› ‹_› hs
    | tableGetVal => exact ToCoreSim.read_tableGetVal ‹_› ‹_› hs
    | tableSize => exact ToCoreSim.read_tableSize ‹_› ‹_› hs
    | tableFillTrap => exact ToCoreSim.read_tableFillTrap ‹_› ‹_› hs
    | tableFillZero => exact ToCoreSim.read_tableFillZero ‹_› ‹_› hs
    | tableFillSucc => exact ToCoreSim.read_tableFillSucc ‹_› ‹_› ‹_› hs
    | tableCopyTrap => exact ToCoreSim.read_tableCopyTrap ‹_› ‹_› ‹_› hs
    | tableCopyZero => exact ToCoreSim.read_tableCopyZero ‹_› ‹_› ‹_› hs
    | tableCopyLe => exact ToCoreSim.read_tableCopyLe ‹_› ‹_› ‹_› ‹_› ‹_› hs
    | tableCopyGt => exact ToCoreSim.read_tableCopyGt ‹_› ‹_› ‹_› ‹_› ‹_› hs
    | tableInitTrap => exact ToCoreSim.read_tableInitTrap ‹_› ‹_› ‹_› hs
    | tableInitZero => exact ToCoreSim.read_tableInitZero ‹_› ‹_› ‹_› hs
    | tableInitSucc => exact ToCoreSim.read_tableInitSucc ‹_› ‹_› ‹_› ‹_› ‹_› hs
    | loadIntTrap => exact ToCoreSim.read_loadIntTrap ‹_› ‹_› hs
    | loadIntVal => exact ToCoreSim.read_loadIntVal ‹_› ‹_› hs
    | loadFloatTrap => exact ToCoreSim.read_loadFloatTrap ‹_› ‹_› hs
    | loadFloatVal => exact ToCoreSim.read_loadFloatVal ‹_› ‹_› hs
    | loadPackTrap => exact ToCoreSim.read_loadPackTrap ‹_› ‹_› hs
    | loadPackVal => exact ToCoreSim.read_loadPackVal ‹_› ‹_› hs
    | vecLoadOob => exact ToCoreSim.read_vecLoadOob ‹_› ‹_› hs
    | vecLoadVal => exact ToCoreSim.read_vecLoadVal ‹_› ‹_› hs
    | vecLoadLaneOob => exact ToCoreSim.read_vecLoadLaneOob ‹_› ‹_› hs
    | vecLoadLaneVal => exact ToCoreSim.read_vecLoadLaneVal ‹_› ‹_› ‹_› hs
    | memorySize => exact ToCoreSim.read_memorySize ‹_› ‹_› hs
    | memoryFillTrap => exact ToCoreSim.read_memoryFillTrap ‹_› ‹_› hs
    | memoryFillZero => exact ToCoreSim.read_memoryFillZero ‹_› ‹_› hs
    | memoryFillSucc => exact ToCoreSim.read_memoryFillSucc ‹_› ‹_› ‹_› hs
    | memoryCopyTrap => exact ToCoreSim.read_memoryCopyTrap ‹_› ‹_› hs
    | memoryCopyZero => exact ToCoreSim.read_memoryCopyZero ‹_› ‹_› hs
    | memoryCopyLe => exact ToCoreSim.read_memoryCopyLe ‹_› ‹_› ‹_› ‹_› hs
    | memoryCopyGt => exact ToCoreSim.read_memoryCopyGt ‹_› ‹_› ‹_› ‹_› hs
    | memoryInitTrap => exact ToCoreSim.read_memoryInitTrap ‹_› ‹_› ‹_› hs
    | memoryInitZero => exact ToCoreSim.read_memoryInitZero ‹_› ‹_› ‹_› hs
    | memoryInitSucc => exact ToCoreSim.read_memoryInitSucc ‹_› ‹_› ‹_› ‹_› ‹_› hs
  | @ctxtInstrs s s' f f' vs is is' rest hstep hne ih =>
    exact ToCoreSim.state_ctxtInstrs (fun _ hc => ih hc)
      (Step.storeExt hosts.1 hstep hs.2.1) hne hs
  | @ctxtLabel s s' f f' n cont is is' hstep ih =>
    exact ToCoreSim.state_ctxtLabel (fun _ hc => ih hc) hs
  | @ctxtFrame s s' f fi fi' n is is' hstep ih =>
    exact ToCoreSim.state_ctxtFrame (fun _ hc => ih hc) (Step.storeExt hosts.1 hstep hs.2.1) hs
  | callAddrHost => exact ToCoreSim.state_callAddrHost hosts ‹_› ‹_› ‹_› ‹_› hs
  | callAddrHostDiv => exact ToCoreSim.state_callAddrHostDiv hosts ‹_› ‹_› ‹_› ‹_› hs
  | localSet => exact ToCoreSim.state_localSet ‹_› hs
  | globalSet => exact ToCoreSim.state_globalSet ‹_› ‹_› hs
  | tableSetTrap => exact ToCoreSim.state_tableSetTrap ‹_› ‹_› ‹_› hs
  | tableSetVal => exact ToCoreSim.state_tableSetVal ‹_› ‹_› ‹_› hs
  | tableGrowSucceed => exact ToCoreSim.state_tableGrowSucceed ‹_› ‹_› ‹_› ‹_› hs
  | tableGrowFail => exact ToCoreSim.state_tableGrowFail ‹_› ‹_› ‹_› hs
  | elemDrop => exact ToCoreSim.state_elemDrop ‹_› ‹_› hs
  | storeIntTrap => exact ToCoreSim.state_storeIntTrap ‹_› ‹_› ‹_› hs
  | storeIntVal => exact ToCoreSim.state_storeIntVal ‹_› ‹_› ‹_› hs
  | storeFloatTrap => exact ToCoreSim.state_storeFloatTrap ‹_› ‹_› ‹_› hs
  | storeFloatVal => exact ToCoreSim.state_storeFloatVal ‹_› ‹_› ‹_› hs
  | storePackTrap => exact ToCoreSim.state_storePackTrap ‹_› ‹_› ‹_› hs
  | storePackVal => exact ToCoreSim.state_storePackVal ‹_› ‹_› ‹_› hs
  | vecStoreOob => exact ToCoreSim.state_vecStoreOob ‹_› ‹_› ‹_› hs
  | vecStoreVal => exact ToCoreSim.state_vecStoreVal ‹_› ‹_› ‹_› hs
  | vecStoreLaneOob => exact ToCoreSim.state_vecStoreLaneOob ‹_› ‹_› ‹_› hs
  | vecStoreLaneVal => exact ToCoreSim.state_vecStoreLaneVal ‹_› ‹_› ‹_› ‹_› hs
  | memoryGrowSucceed => exact ToCoreSim.state_memoryGrowSucceed ‹_› ‹_› ‹_› ‹_› hs
  | memoryGrowFail => exact ToCoreSim.state_memoryGrowFail ‹_› ‹_› ‹_› hs
  | dataDrop => exact ToCoreSim.state_dataDrop ‹_› ‹_› hs

/-- The specialisation the unit brief asked for: the simulation at
`coreProfile`. -/
theorem Step.toCore_spec {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {a b : Config H} {c : ToCore.CConfig H}
    (h : Step coreProfile src a b) (hs : Sim a c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step coreProfile tgt) c c' ∧ Sim b c' :=
  Step.toCore hosts h hs

/-- **Milestone.** Finite runs are simulated. -/
theorem Steps.toCore {P : Profile} {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {a b : Config H} {c : ToCore.CConfig H}
    (h : Steps P src a b) (hs : Sim a c) :
    ∃ c', Silmaril.Wasm.Execution.Core.Steps P tgt c c' ∧ Sim b c' :=
  LockstepSim.steps (R := Sim) ⟨Step.toCore hosts⟩ h hs

/-- **Milestone.** Divergence is preserved. This is why `Step.toCore` produces a
`TransGen`: a 2.0 step that makes no Core progress would not give an infinite
Core trace. -/
theorem Diverges.toCore {P : Profile} {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {a : Config H} {c : ToCore.CConfig H}
    (h : Diverges P src a) (hs : Sim a c) :
    Silmaril.Wasm.Execution.Core.Diverges P tgt c :=
  LockstepSim.diverges (R := Sim) ⟨Step.toCore hosts⟩ h hs

/-- **Milestone.** A terminal 2.0 result is a terminal Core result.

Unlike `Lime1.Execution.Sim.result`, which concludes `c.code = r.toCore.toAdmin`
outright, the Core configuration may still be holding the *instruction*
`REF.NULL ht` where the 2.0 result holds the *value* `REF.NULL rt`; it reaches
the Core result in that many `Step_read/ref.null` steps, with the store and the
frame untouched. -/
theorem Sim.result {P : Profile} {tgt : ToCore.CHostSemantics H} {a : Config H}
    {c : ToCore.CConfig H} {r : Result} (hs : Sim a c) (hr : a.code = r.toAdmin) :
    ∃ c' : ToCore.CConfig H, Silmaril.Wasm.Execution.Core.Steps P tgt c c' ∧
      c'.store = c.store ∧ c'.frame = c.frame ∧
      c'.code = r.toCore.toAdmin := by
  obtain ⟨s, f, code⟩ := a
  obtain ⟨cs, cf, cl⟩ := c
  subst hr
  have hcode := ToCoreSim.sim_code hs
  cases r with
  | values vs =>
    refine ⟨⟨cs, cf, Silmaril.Wasm.Execution.Core.vals (vs.map Val.toCore)⟩, ?_, rfl, rfl, rfl⟩
    have h0 : cl.map (ToCore.Admin.norm cf.module) =
        ToCoreSim.cvals (vs.map Val.toCore) ++ [] := by
      simpa [Result.toAdmin, ToCoreSim.cvals] using
        (Option.some.inj ((values_toCore s vs).symm.trans hcode)).symm
    simpa using ToCoreSim.catchUp (P := P) (tgt := tgt) (R := []) (by simp) h0
  | trap =>
    refine ⟨⟨cs, cf, [.trap]⟩, ?_, rfl, rfl, rfl⟩
    have h0 : cl.map (ToCore.Admin.norm cf.module) =
        ToCoreSim.cvals [] ++ [Silmaril.Wasm.Execution.Core.Admin.trap] := by
      simp only [Result.toAdmin, Admin.listToCore_cons, Admin.trap_toCore, Admin.listToCore_nil,
        Option.map_some, Option.bind_some, List.append_nil, Option.some.injEq] at hcode
      simpa [ToCoreSim.cvals] using hcode.symm
    simpa using ToCoreSim.catchUp (P := P) (tgt := tgt) (vs := []) (by simp [ToCore.Rigid]) h0

end Silmaril.Wasm.V2.Execution
