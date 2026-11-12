module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: un-stripping exports (pass 6)

Pass 5 proved the Core half of the export-stripping route to `Round7.Task.wholeStepValidREH`
(`Round7.step_strip`, `Round7.step_of_strip`) and found the obstruction on the SpecTec half:
`stripConfig` is not injective on the module instances of a configuration, so a step of the
stripped configuration does not say which export lists the successor of `c` carries.

This header states, additively, what the route gives when the obstruction is assumed away, and
the two SpecTec facts it still needs.

* `ExportOnly μ`: `μ` rewrites only the export lists of module instances.
* `mapFI`, `mapStore`, `mapFrame`, `mapAdmin(s)`, `mapConfig`, `mapOutcome`: `μ` applied to every
  module instance of a function instance, store, frame, code or configuration (`stripConfig` is
  `mapConfig stripModule`).
* `HostModMap host μ`, `HostExportParam host`: the host relation is invariant under export-only
  rewritings of the store (the outcome is rewritten the same way). `HostExportParam` with
  `μ := stripModule` is the first half of `HostExportBlind`.
* `mods c`: the module instances of `c` (store, frame, frames in the code). `StripInj c`: two of
  them with the same stripped form are equal. This is the injectivity side condition.
* `unstrip c`: the inverse of `stripModule` on `mods c`, the identity elsewhere. Under
  `StripInj c` it is export-only and `mapConfig (unstrip c) (stripConfig c) = c`.

**The two SpecTec leaves** (frozen, open), at round 6's primitives `BI (Profile.spec nd r) hn host`:

* `Task.swapEquiv`: SpecTec's `Step` in `utf8Env B` commutes with un-stripping, read on images.
  Forward: a step from the image of `stripConfig c` to the image of an export-free `d` gives a
  step from the image of `c` to the image of `mapConfig (unstrip c) d`. Backward: a step from the
  image of `c` to `w` gives a step from the image of `stripConfig c` to some `w₀`, and whenever
  `w₀` is the image of an export-free `d`, `w` is the image of `mapConfig (unstrip c) d`. It is
  what equivariance of the interpreter under the value swap `m ↔ stripModule m` (`m ∈ mods c`)
  gives; under `StripInj c` that swap is a bijection, so negative `otherwise` premises and
  equality tests are preserved.
* `Task.envAgreeNE`: on round 6's domain (`ConfigOk`, `Round5.Target.BoundedSel`, which includes
  `NoExports`), `SStepB (utf8Env B)` and `SStepB (simEnv B)` agree. Positive derivations move
  from `simEnv B` to `utf8Env B` by `Round7.dderivesB_utf8Env`; the leaf also asks for the
  `otherwise` premises and for the converse.

**The target `Round7.Task.wholeStepValidREI`** (frozen): `Task.wholeStepValidREH` with
`HostExportParam host` added to the host hypotheses and `StripInj c` to both halves. It is
weaker than `Task.wholeStepValidREH` (`Round7.wholeStepValidREI_of_REH`) and follows from the two
leaves (`Round7.wholeStepValidREI_of_leaves`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

/-! ## Export-only rewritings -/

/-- **`μ` rewrites only export lists**: removing the exports of `μ m` gives those of `m`
removed. -/
def ExportOnly (μ : ModuleInst → ModuleInst) : Prop := ∀ m, stripModule (μ m) = stripModule m

/-- `μ` on a function instance's module. -/
def mapFI (μ : ModuleInst → ModuleInst) (fi : FuncInst H) : FuncInst H :=
  { fi with module := μ fi.module }

/-- `μ` on the modules of a store's function instances. -/
def mapStore (μ : ModuleInst → ModuleInst) (s : Store H) : Store H :=
  { s with funcs := s.funcs.map (mapFI μ) }

/-- `μ` on a frame's module. -/
def mapFrame (μ : ModuleInst → ModuleInst) (f : Frame) : Frame := { f with module := μ f.module }

mutual
/-- `μ` on the module of every frame inside an administrative instruction. -/
def mapAdmin (μ : ModuleInst → ModuleInst) : Admin → Admin
  | .label n cont body => .label n cont (mapAdmins μ body)
  | .handler n cs body => .handler n cs (mapAdmins μ body)
  | .frame n f body => .frame n (mapFrame μ f) (mapAdmins μ body)
  | a => a

/-- `mapAdmin` on a sequence. -/
def mapAdmins (μ : ModuleInst → ModuleInst) : List Admin → List Admin
  | [] => []
  | a :: l => mapAdmin μ a :: mapAdmins μ l
end

/-- **`μ` on every module instance of a configuration**: the store's function instances, the
frame and every frame in the code. -/
def mapConfig (μ : ModuleInst → ModuleInst) (c : Config H) : Config H :=
  ⟨mapStore μ c.store, mapFrame μ c.frame, mapAdmins μ c.code⟩

/-- `μ` on the store of a host outcome. -/
def mapOutcome (μ : ModuleInst → ModuleInst) :
    Silmaril.Wasm.Execution.Host.Outcome (Store H) Result →
      Silmaril.Wasm.Execution.Host.Outcome (Store H) Result
  | .returned s r => .returned (mapStore μ s) r
  | .diverged => .diverged

/-- **The host relation is invariant under `μ`**: rewriting the store it is called in rewrites
its outcome the same way. -/
def HostModMap (host : HostSemantics H) (μ : ModuleInst → ModuleInst) : Prop :=
  ∀ (h : H) (s : Store H) (vs : List Val)
    (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
    host h s vs o → host h (mapStore μ s) vs (mapOutcome μ o)

/-- **The host is parametric in export lists**: invariant under every export-only rewriting. -/
def HostExportParam (host : HostSemantics H) : Prop :=
  ∀ μ : ModuleInst → ModuleInst, ExportOnly μ → HostModMap host μ

/-! ## The module instances of a configuration, and the side condition -/

mutual
/-- The modules of the frames inside an administrative instruction. -/
def modsAdmin : Admin → List ModuleInst
  | .label _ _ body => modsAdmins body
  | .handler _ _ body => modsAdmins body
  | .frame _ f body => f.module :: modsAdmins body
  | _ => []

/-- `modsAdmin` on a sequence. -/
def modsAdmins : List Admin → List ModuleInst
  | [] => []
  | a :: l => modsAdmin a ++ modsAdmins l
end

/-- **The module instances of `c`**: those of the store's function instances, the frame's, and
those of the frames in the code. -/
def mods (c : Config H) : List ModuleInst :=
  c.store.funcs.map FuncInst.module ++ c.frame.module :: modsAdmins c.code

/-- **The injectivity side condition**: two module instances of `c` that differ only in their
export lists are equal. -/
def StripInj (c : Config H) : Prop :=
  ∀ m₁ ∈ mods c, ∀ m₂ ∈ mods c, stripModule m₁ = stripModule m₂ → m₁ = m₂

/-- **Un-stripping along `c`**: a module that is the stripped form of a module instance of `c`
goes back to (a chosen) one; every other module is unchanged. Under `StripInj c` the choice is
unique (`Round7.unstrip_strip`). -/
noncomputable def unstrip (c : Config H) (m₀ : ModuleInst) : ModuleInst :=
  open Classical in
  if h : ∃ m ∈ mods c, stripModule m = m₀ then h.choose else m₀

/-! ## The two SpecTec leaves (frozen, open) -/

/-- **SpecTec's `Step` commutes with un-stripping** (frozen, open), read on images, at round 6's
primitives, in the round-7 environment. See the module docstring. -/
def Task.swapEquiv : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostExportBlind host →
      HostExportParam host → ∀ (nd : Bool) (r : RelaxedChoice),
        ∀ (c : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c → StripInj c →
          (∀ d : Config H, Stripped d →
            Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
              (configV hn (stripConfig c)) (configV hn d) →
            Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
              (configV hn c) (configV hn (mapConfig (unstrip c) d))) ∧
          (∀ w : Value,
            Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
              (configV hn c) w →
            ∃ w₀, Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
                (configV hn (stripConfig c)) w₀ ∧
              ∀ d : Config H, Stripped d → w₀ = configV hn d →
                w = configV hn (mapConfig (unstrip c) d))

/-- **The two environments agree on round 6's domain** (frozen, open): at a valid,
`Round5.Target.BoundedSel` (so export-free) configuration, SpecTec's `Step` in `utf8Env B` is
SpecTec's `Step` in `simEnv B`, `otherwise` premises included. The host is export-blind: a host
that returns a store with exports from an export-free one would give a typed `utf8Env B` step
that `simEnv B` cannot type, so without `HostExportBlind` the leaf would be false. -/
def Task.envAgreeNE : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostExportBlind host →
      ∀ (nd : Bool) (r : RelaxedChoice),
        ∀ (c : Config H) (ts : List CValType), ConfigOk c ts → Round5.Target.BoundedSel c →
          ∀ w : Value,
            Round6.Reading.SStepB (utf8Env (Round4Int.BI (Profile.spec nd r) hn host))
                (configV hn c) w ↔
              Round6.Reading.SStepB (simEnv (Round4Int.BI (Profile.spec nd r) hn host))
                (configV hn c) w

/-! ## The target with the injectivity side condition -/

/-- **`Round7.Task.wholeStepValidREH` with the injectivity side condition** (frozen). The host is
also asked to be parametric in export lists (`HostExportParam`), and both halves are restricted
to configurations with `StripInj c`. -/
def Task.wholeStepValidREI : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostExportBlind host →
      HostExportParam host → ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c → StripInj c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧ backendE.step B (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          BoundedSelE c → StripInj c → backendE.step B (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round7
