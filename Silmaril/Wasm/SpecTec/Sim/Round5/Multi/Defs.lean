module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track multi: definitions

The one-step target `Round5.Task.wholeStepValidOk` relates a Core step from a valid
configuration `c` to a SpecTec step from the image of `c` itself, up to `ConfigEq` on the
successor. Along a run, SpecTec is then at the image of a witness `d ≈ c` that need not be valid
in Core (after `return_call_ref` out of a frame SpecTec keeps an index annotation), so the
one-step target cannot be applied again. Composing needs **ConfigEq-respect on the SpecTec
side**: from the image of every typed `d ≈ c`, SpecTec steps as it does from the image of `c`.

This header states, additively, round 4's composable relations for the restated target
(`HostOk` hosts, `Pos.BoundedNE` configurations), along round 4's `Round4.SimRel` (witness
`d ≈ c`, `Typed`):

* `FwdResp env hn c c'`: SpecTec respects `ConfigEq` for one Core step `c → c'`: from the image
  of every typed `d ≈ c` it reaches the image of a typed `e ≈ c'` (if `c'` is typed).
* `BoundedReachNE`: every configuration Core reaches is bounded and export-free.
* `FwdRel`, `BwdRel`: the one-step simulations along `SimRel`, forward and backward.
* `SuccTyped`: SpecTec's successor of a typed witness, when it agrees with a typed configuration
  up to `ConfigEq`, is typed. The backward relation needs it (the successor witness must be
  `Typed` to step again); it is not proved. `SuccCallsTyped` is the same statement restricted
  to the only positions where the two configurations differ, the `CALL_REF` annotations.
* `MultiOk`: for every encoding, finite `HostOk` host and profile, some `B` makes `FwdRel` hold,
  and `BwdRel` under `SuccTyped`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Multi

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel)

variable {H : Type}

/-- **SpecTec respects `ConfigEq` along the Core step `c → c'`**: from the image of every typed
witness `d ≈ c`, SpecTec steps to the image of a typed `e ≈ c'`, provided `c'` is typed. -/
def FwdResp (env : Env) (hn : H → String) (c c' : Config H) : Prop :=
  ∀ d, Bwd.ConfigEq c d → Typed env hn d → Typed env hn c' →
    ∃ e, Bwd.ConfigEq c' e ∧ Typed env hn e ∧ SStep env (configV hn d) (configV hn e)

/-- **The two host `call_ref` rules forward**, for any `CALL_REF` and a bounded callee type:
the hypotheses of `Fwd.fwd_callRefHost5` and `Fwd.fwd_callRefHostDiv5` beyond `TypesB` and the
host (which give it from `Prims.HostRespects`, and `fwd_callRefHostT` from
`HostRespectsT`). -/
def HostCallsFwd (B : Builtins) (hn : H → String) (host : HostSemantics H) :
    Prop :=
  (∀ {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
      {ps rs : Ty (.list .val)} {h : H} {r : Result},
      c.IsCallRef → s.funcs[a]? = some fi → Expand fi.type (.func ps rs) →
      vs.length = ps.length → fi.code = .host h → host h s vs (.returned s' r) →
      Round4.tyBnd fi.type = true →
      FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩) ∧
  (∀ {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
      {ps rs : Ty (.list .val)} {h : H},
      c.IsCallRef → s.funcs[a]? = some fi → Expand fi.type (.func ps rs) →
      vs.length = ps.length → fi.code = .host h → host h s vs .diverged →
      Round4.tyBnd fi.type = true →
      FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)

/-- Every configuration Core reaches from `c` is bounded and export-free. -/
def BoundedReachNE (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c', Steps P host c c' → Pos.BoundedNE c'

/-- **The forward one-step simulation along `SimRel`**, for the restated target's sources and
successors. -/
def FwdRel (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (c d c' : Config H) (ts : List CValType), ConfigOk c ts → Pos.BoundedNE c →
    SimRel B hn c d → Pos.BoundedNE c' → Step P host c c' →
    ∃ d', SimRel B hn c' d' ∧ SStep (simEnv B) (configV hn d) (configV hn d')

/-- **The backward one-step simulation along `SimRel`**, from a source whose Core successors are
all bounded and export-free. -/
def BwdRel (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (c d : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → Pos.BoundedNE c →
    (∀ c', Step P host c c' → Pos.BoundedNE c') → SimRel B hn c d →
    SStep (simEnv B) (configV hn d) w →
    ∃ c' d', SimRel B hn c' d' ∧ w = configV hn d' ∧ Step P host c c'

/-- **SpecTec's successors of typed witnesses are typed**, when they agree with a typed
configuration up to `ConfigEq`. Not proved (module doc). -/
def SuccTyped (B : Builtins) (hn : H → String) : Prop :=
  ∀ d d' c' : Config H, Typed (simEnv B) hn d →
    SStep (simEnv B) (configV hn d) (configV hn d') → Bwd.ConfigEq c' d' →
    Typed (simEnv B) hn c' → Typed (simEnv B) hn d'

mutual
/-- Every `CALL_REF` of an administrative instruction, at every depth, is a typed `instr`. -/
def AdminCallsTyped (env : Env) : Admin → Prop
  | .label _ _ b => CodeCallsTyped env b
  | .handler _ _ b => CodeCallsTyped env b
  | .frame _ _ b => CodeCallsTyped env b
  | a => a.IsCallRef → TypedV env (.varT "instr" []) (adminToV a)

/-- `AdminCallsTyped` along a code sequence. -/
def CodeCallsTyped (env : Env) : List Admin → Prop
  | [] => True
  | a :: l => AdminCallsTyped env a ∧ CodeCallsTyped env l
end

/-- **The `CALL_REF`s of SpecTec's successors of typed witnesses are typed.** Not proved; it
gives `SuccTyped` (`Round5.Multi.succTyped_of_calls`). -/
def SuccCallsTyped (B : Builtins) (hn : H → String) : Prop :=
  ∀ d d' : Config H, Typed (simEnv B) hn d →
    SStep (simEnv B) (configV hn d) (configV hn d') → CodeCallsTyped (simEnv B) d'.code

/-- **The composable one-step simulations for the restated target**: for every injective
encoding, finite `HostOk` host and `Profile.spec nd r`, some `B` makes the forward relation hold,
and the backward one under `SuccTyped`. -/
def MultiOk : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        FwdRel B hn (Profile.spec nd r) host ∧
          (SuccTyped B hn → BwdRel B hn (Profile.spec nd r) host)

end Silmaril.Wasm.SpecTec.Sim.Round5.Multi
