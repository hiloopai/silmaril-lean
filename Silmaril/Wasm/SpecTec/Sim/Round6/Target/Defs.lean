module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int4.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track target: definitions

Round 5 left `Round5.Task.wholeStepValidSel` open and argued it false for two reasons
(`docs/projects/spectec/README.md`):

1. under the declarative reading `DDerives`, an empty-domain `e?` in a rule conclusion never
   evaluates, so SpecTec's `Ref_ok` misses `Ref_ok/sub`, and at `ref.null; ref.test (ref null
   any)` SpecTec's `otherwise` rule yields `i32.const 0` where Core yields `i32.const 1`;
2. under `Profile.spec`, `f64x2.promote_low_f32x4` on a NaN lane has two Core successors, while
   SpecTec's `$vcvtop__` is a function.

This header states, additively, the restated round-6 target `Round6.Task.wholeStepValidR` that
survives both, and the leaves it is reduced to.

* `Reading`: an abstract reading of SpecTec's whole-machine `Step` at each `Builtins`. Track
  reading supplies the backend-style one (an empty-domain `e?` in a conclusion denotes `none` or
  `some e`); until then the target is stated over any `Reading`. `declarative` is round 5's
  `SStep (simEnv B)`.
* `CastRedex is`: the first non-value instruction of `is`, looking through the bodies of labels,
  handlers and frames, is a cast (`ref.test`, `ref.cast`, `br_on_cast`, `br_on_cast_fail`).
  These are the only `Step_read` rules whose premises reach `Ref_ok`.
* `Transfer Rd B hn`: **the transfer lemma**. Away from cast redexes, the reading's step from the
  image of a SpecTec witness of a valid, `BoundedSel` configuration is the declarative one.
  `declarative` satisfies it trivially (`Round6.Target.transfer_declarative`); it does not
  determine the reading at casts.
* `Casts Rd B hn P host`: **the cast leaf**, the target's two halves at configurations whose
  redex is a cast. It is what the reading must get right where `DDerives` does not.
* `Round6.Task.wholeStepValidR Rd`: the restated target, for the reading `Rd`: valid
  (`ConfigOk`), `BoundedSel` sources, finite `HostOk` hosts, `Profile.spec nd r`;
  - **forward up to Core's choice**: if every Core successor of `c` is `BoundedSel`, each Core
    step `c → c'` is matched by a reading step from `c`'s image to the image (up to `ConfigEq`)
    of *some* Core successor `c''`, and `c'' = c'` whenever `c'` is Core's only successor
    (`Round5.Convert.VectorFwdR`'s shape);
  - **backward up to `ConfigEq`**: every reading step from `c`'s image is the image of a Core
    step, as in `Round5.Task.wholeStepValidSel`.
* `DetSteps`, `BoundedReachSel` (round 5's), `RSteps`: for the multi-step corollary
  (`Round6.Target.runsR_of_open`).

`Round5.Task.wholeStepValidSel` and every earlier statement are unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

namespace Target

open Round4 (SimRel)
open Round5.Target (BoundedSel)

/-! ## Cast redexes -/

/-- The cast instructions: the only ones whose `Step_read` rules have a `Ref_ok` premise. -/
def castInstr : Instr → Bool
  | .refTest _ | .refCast _ | .brOnCast .. | .brOnCastFail .. => true
  | _ => false

/-- **The redex of `is` is a cast**: after a prefix of values, the first instruction is a cast,
or a label, handler or frame whose body's redex is a cast. -/
inductive CastRedex : List Admin → Prop where
  /-- Skip a value. -/
  | skip {v : Val} {l : List Admin} : CastRedex l → CastRedex (v.toAdmin :: l)
  /-- A cast instruction. -/
  | cast {i : Instr} {l : List Admin} : castInstr i = true → CastRedex (.plain i :: l)
  /-- Inside a label. -/
  | label {n : Nat} {cont : List Instr} {b l : List Admin} :
      CastRedex b → CastRedex (.label n cont b :: l)
  /-- Inside a handler. -/
  | handler {n : Nat} {cs : List Catch} {b l : List Admin} :
      CastRedex b → CastRedex (.handler n cs b :: l)
  /-- Inside a frame. -/
  | frame {n : Nat} {fi : Frame} {b l : List Admin} :
      CastRedex b → CastRedex (.frame n fi b :: l)

/-! ## Readings -/

/-- **An abstract reading of SpecTec's whole-machine `Step`**, at each choice of primitives. -/
structure Reading where
  /-- The step relation on encoded configurations, at the primitives `B`. -/
  step : Builtins → Value → Value → Prop

/-- Round 5's reading: `DDerives` with `otherwise`, on `simEnv B`. -/
def declarative : Reading := ⟨fun B => SStep (simEnv B)⟩

/-- **The transfer lemma**: away from cast redexes, the reading's step from the image of a
SpecTec witness `d` of a valid, `BoundedSel` configuration `c` is the declarative step. -/
structure Transfer (Rd : Reading) (B : Builtins) (hn : H → String) : Prop where
  /-- Declarative steps are reading steps. -/
  fwd : ∀ (c d : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → BoundedSel c →
    SimRel B hn c d → ¬ CastRedex d.code → SStep (simEnv B) (configV hn d) w →
      Rd.step B (configV hn d) w
  /-- Reading steps are declarative steps. -/
  bwd : ∀ (c d : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → BoundedSel c →
    SimRel B hn c d → ¬ CastRedex d.code → Rd.step B (configV hn d) w →
      SStep (simEnv B) (configV hn d) w

/-- **The cast leaf**: both halves of the target, along `SimRel`, at configurations whose redex
is a cast. Core's cast steps are deterministic, so the forward half is exact. -/
structure Casts (Rd : Reading) (B : Builtins) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  /-- Forward. -/
  fwd : ∀ (c d c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSel c →
    (∀ c₁, Step P host c c₁ → BoundedSel c₁) → SimRel B hn c d → CastRedex d.code →
    Step P host c c' → ∃ d', SimRel B hn c' d' ∧ Rd.step B (configV hn d) (configV hn d')
  /-- Backward; the witness of the successor is typed when the successor is. -/
  bwd : ∀ (c d : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → BoundedSel c →
    SimRel B hn c d → CastRedex d.code → Rd.step B (configV hn d) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ (Typed (simEnv B) hn c' → Typed (simEnv B) hn d') ∧
      w = configV hn d' ∧ Step P host c c'

/-- **What `Task.wholeStepValidR Rd` is reduced to**, at one encoding, host and profile, with
`B := Prims.builtins`: the transfer lemma and the cast leaf. -/
structure OpenR (Rd : Reading) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  /-- The transfer lemma. -/
  transfer : Transfer Rd (Round4Int.BI P hn host) hn
  /-- The cast leaf. -/
  casts : Casts Rd (Round4Int.BI P hn host) hn P host

/-! ## Runs -/

/-- One Core step to the only successor. -/
def DetStep (P : Profile) (host : HostSemantics H) (c c' : Config H) : Prop :=
  Step P host c c' ∧ ∀ c₃, Step P host c c₃ → c₃ = c'

/-- Core runs in which every step goes to the only successor. -/
abbrev DetSteps (P : Profile) (host : HostSemantics H) : Config H → Config H → Prop :=
  Relation.ReflTransGen (DetStep P host)

/-- Runs of a reading. -/
abbrev RSteps (Rd : Reading) (B : Builtins) : Value → Value → Prop :=
  Relation.ReflTransGen (Rd.step B)

end Target

/-- **The restated round-6 target** (frozen; track target), for a reading `Rd` of SpecTec's
`Step`: on valid (`ConfigOk`), `BoundedSel` configurations, under finite `HostOk` hosts and
`Profile.spec nd r`,

* forward, up to Core's choice: when every Core successor of `c` is `BoundedSel`, each Core step
  `c → c'` is matched by an `Rd` step to the image (up to `ConfigEq`) of a Core successor `c''`,
  which is `c'` whenever `c'` is the only one;
* backward, up to `ConfigEq`: each `Rd` step from the image of `c` is the image of a Core step.

Forced by the two obstructions to `Round5.Task.wholeStepValidSel` (module docstring); `Rd` is
to be track reading's backend-style reading. -/
def Task.wholeStepValidR (Rd : Target.Reading) : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Round5.Target.BoundedSel c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → Round5.Target.BoundedSel c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧ Rd.step B (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          Round5.Target.BoundedSel c → Rd.step B (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round6
