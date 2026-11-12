module

public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track target: definitions

Track simdty (pass 3) found that the evaluator types a float SIMD operator through the integer
instance of its family (`Round5.SimdTy.FloatMissel`), so the image of `f32x4.sqrt` is not a
typed `instr`. Track target (pass 4) turns this into a refutation of the restated target
`Round5.Task.wholeStepValidOk` (`Round5.Target.not_wholeStepValidOk`): every `Step` rule reads
the last instruction of its left-hand code through a typed quantifier or as a literal case other
than `VUNOP`, so SpecTec does not step from `v128.const; f32x4.sqrt`, which is valid, bounded
and export-free, and which Core steps.

This header states, additively, the target with that obstruction removed as well:

* `instrSel i`: no instruction of `i`, at any depth of block bodies, is `FloatMissel`;
* `NoMissel c`: no `FloatMissel` instruction occurs in `c`: in its code (plain instructions,
  label continuations, and the bodies of labels, handlers and frames, at every depth) or in the
  body of a Wasm function instance of its store;
* `Round5.Task.wholeStepValidSel`: `Round5.Task.wholeStepValidOk` for configurations that are
  also `NoMissel`, the successor also `NoMissel` in the forward conjunct (as for `NoExports`, a
  host may return a store that is not);
* `PosTypingSel`: `Pos.PosTypingNE` with `instr` and `store` restricted to `instrSel` code;
* `PartsSel`: `Round5.Read.PartsOkS` with `PosTypingSel` for `Pos.PosTypingNE`
  (what `Task.wholeStepValidSel` reduces to, `Round5.Target.wholeStepValidSel_of_partsSel`);
* `Open5`: pass 3's `Round5.Int3.Open4` without its `simd` leaf, which `Task.wholeStepValidSel`
  no longer needs (`Round5.Target.wholeStepValidSel_of_open5`);
* `BoundedReachSel`, `FwdRelSel`, `BwdRelSel`, `MultiSel`: `Multi.BoundedReachNE`,
  `Multi.FwdRel`, `Multi.BwdRel` and pass 2's `Round5.Int2.MultiOk2` with `BoundedSel` for
  `Pos.BoundedNE` (the multi-step corollaries, `Round5.Target.runsSel_of_open5`).

The earlier targets are unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

namespace Target

mutual
/-- **No `FloatMissel` instruction in `i`**, block bodies included. -/
def instrSel : Instr → Bool
  | .block _ body => instrsSel body
  | .loop _ body => instrsSel body
  | .if_ _ b₁ b₂ => instrsSel b₁ && instrsSel b₂
  | .tryTable _ _ body => instrsSel body
  | i => !SimdTy.FloatMissel i

/-- `instrSel` on a sequence. -/
def instrsSel : List Instr → Bool
  | [] => true
  | i :: is => instrSel i && instrsSel is
end

mutual
/-- No `FloatMissel` instruction inside an administrative instruction, at any depth. -/
def AdminSel : Admin → Prop
  | .plain i => instrSel i = true
  | .label _ cont body => instrsSel cont = true ∧ AdminsSel body
  | .handler _ _ body => AdminsSel body
  | .frame _ _ body => AdminsSel body
  | _ => True

/-- `AdminSel` on a sequence. -/
def AdminsSel : List Admin → Prop
  | [] => True
  | a :: l => AdminSel a ∧ AdminsSel l
end

/-- No Wasm function body of the store has a `FloatMissel` instruction. -/
def StoreSel (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ fn, fi.code = .wasm fn → instrsSel fn.body = true

/-- **No `FloatMissel` instruction occurs in the configuration.** -/
structure NoMissel (c : Config H) : Prop where
  /-- The function bodies of the store. -/
  store : StoreSel c.store
  /-- The code, at every depth. -/
  code : AdminsSel c.code

/-- Bounded, export-free (`Pos.BoundedNE`) and without `FloatMissel` code. -/
def BoundedSel (c : Config H) : Prop := Pos.BoundedNE c ∧ NoMissel c

/-- **`Pos.PosTypingNE` restricted to code without `FloatMissel` instructions.** -/
structure PosTypingSel (B : Builtins) (hn : H → String) : Prop where
  /-- A valid instruction within SpecTec's syntax and without `FloatMissel` code is typed. -/
  instr : ∀ (C : Context) (i : Instr) (it : InstrType), InstrOk C i it →
    Round4.instrBnd i = true → instrSel i = true →
    TypedV (simEnv B) (.varT "instr" []) (instrToV i)
  /-- A valid, bounded `CALL_REF dt` is a typed `instr`. -/
  callRefType : ∀ d : DefType, TyOk {} d → Round4.tyBnd d = true →
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.callRefType d))
  /-- A valid, bounded `RETURN_CALL_REF dt` is a typed `instr`. -/
  returnCallRefType : ∀ d : DefType, TyOk {} d → Round4.tyBnd d = true →
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.returnCallRefType d))
  /-- A valid, bounded, export-free module instance is a typed `moduleinst`. -/
  moduleinst : ∀ (s : Store H) (m : ModuleInst) (C : Context), ModuleInstOk s m C →
    Round4.ModuleBnd m → m.exports = [] →
    TypedV (simEnv B) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT m)
  /-- A valid, bounded store, export-free and without `FloatMissel` function bodies, is typed. -/
  store : ∀ s : Store H, StoreOk s → Integrate.StoreOk s → Round4.StoreBnd s → Pos.StoreNE s →
    StoreSel s → TypedV (simEnv B) storeT (storeV hn s)

open Round4Int (BI)

/-- **What `Task.wholeStepValidSel` reduces to**, at one encoding, host and profile: track
read's `Round5.Read.PartsOkS` with `PosTypingSel` for `Pos.PosTypingNE` (which is false,
`Round5.SimdTy.not_posTypingNE`). -/
structure PartsSel (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Positive typing of the leaves, export-free and without `FloatMissel` code. -/
  pos : PosTypingSel (BI P hn host) hn
  /-- The forward conjunct on valid, bounded, export-free sources. -/
  fwd : R4Fwd.Forward (BI P hn host) hn P host Pos.ValidNE
  /-- The host-call rules (`Step` 8, 9), backward. -/
  hostSteps : Bwd.HostStepsV (simEnv (BI P hn host)) hn P host
  /-- `Step_pure` outside the dispatched lists. -/
  pure : ∀ i, i ∉ Bwd.pureDone → i ∉ Integrate.floatDone → i ∉ BwdPureStep.pureDone →
    ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value), Bwd.ReadValidR ⟨s, f, is⟩ →
    Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- The remaining `Step_read` rules, under `ReadValidS`. -/
  read : Read.ReadOpenS hn P host
  /-- `Step` (index `≥ 6`) outside the dispatched lists. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ Bwd.stepDone → i ∉ BwdPureStep.stepDone →
    ∀ (c : Config H) (w : Value), Bwd.ReadValidR c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w]) →
    Bwd.BwdUpTo hn P host c w

/-- **The leaves `Task.wholeStepValidSel` still needs after pass 4**: pass 3's
`Round5.Int3.Open4` without `simd` (discharged on `FloatMissel`-free code by
`Round5.SimdTy.simdTypingSel`). -/
structure Open5 (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types.
  Argued false (nested `REC 1`), not refuted. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The lane-wise vector operators agree with Core. False under the spec NaN
  profile, through its `convert` field: `Round5.Simd.not_vecAgreeOps_spec`. -/
  vecOps : Simd.VecAgreeOps (simEnv (BI P hn host)) P

open Round4 (SimRel)

/-- Every configuration Core reaches from `c` is `BoundedSel`. -/
def BoundedReachSel (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c', Steps P host c c' → BoundedSel c'

/-- **The forward one-step simulation along `SimRel`**, for `Task.wholeStepValidSel`'s sources
and successors (`Multi.FwdRel` with `BoundedSel`). -/
def FwdRelSel (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (c d c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSel c →
    SimRel B hn c d → BoundedSel c' → Step P host c c' →
    ∃ d', SimRel B hn c' d' ∧ SStep (simEnv B) (configV hn d) (configV hn d')

/-- **The backward one-step simulation along `SimRel`**, from a source whose Core successors are
all `BoundedSel` (`Multi.BwdRel` with `BoundedSel`). -/
def BwdRelSel (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (c d : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → BoundedSel c →
    (∀ c', Step P host c c' → BoundedSel c') → SimRel B hn c d →
    SStep (simEnv B) (configV hn d) w →
    ∃ c' d', SimRel B hn c' d' ∧ w = configV hn d' ∧ Step P host c c'

/-- **The composable one-step simulations for `Task.wholeStepValidSel`**: `Round5.Int2.MultiOk2`
with `FwdRelSel` and `BwdRelSel`. -/
def MultiSel : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        FwdRelSel B hn (Profile.spec nd r) host ∧
          (Multi.SuccTyped B hn → Int2.WitnessBnd B hn →
            BwdRelSel B hn (Profile.spec nd r) host)

end Target

/-- **The restated round-5 target, pass 4** (frozen; track target): `Task.wholeStepValidOk`
for configurations that are also free of `SimdTy.FloatMissel` instructions (`Target.NoMissel`),
in the code at every depth and in the store's function bodies. The restriction is forced:
`Task.wholeStepValidOk` is false (`Round5.Target.not_wholeStepValidOk`, at
`v128.const; f32x4.sqrt`). -/
def Task.wholeStepValidSel : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Target.BoundedSel c →
          Target.BoundedSel c' → Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → Target.BoundedSel c →
          SStep (simEnv B) (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round5
