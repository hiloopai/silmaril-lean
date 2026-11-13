module

public import Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.Thms

/-!
# Removing export lists from V1 configurations (definitions, round 8)

`Sim10.Utf8Fix` repaired the 1.0 `$utf8` defect as a fixed script `fixedU10`:
in `utf8Env10T B` every bounded string is a `name`, so configurations whose modules export
non-empty names are typed. Round 4's forward theorem is stated in `simEnv10T B`, where they are
not. This header gives the 1.0 form 's 2.0 strip decomposition (`Sim20.Utf8Strip`):

* `stripModule10 m`: `m` with no exports.
* `stripFrame10`, `stripFI10`, `stripStore10`: `stripModule10` on the module of a frame, of a
  defined function instance and of every function instance of a store.
* `stripAdmin10`, `stripAdmins10`: `stripFrame10` on every frame inside the code, at every depth.
* `stripConfig10 c`: all three on a configuration.

**The open leg** (frozen): `Task.unstripStep10`, a step of `utf8Env10T` between the stripped
images of a V1 step from a configuration typed in `utf8Env10T` is also a step between the images
themselves. It is the 1.0 form of `Sim20.Utf8Strip.Task.unstripStep20`. The other two legs are
proved for 1.0 (`Sim10.Utf8Strip10.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst)

variable {H : Type}

/-- **A module instance without exports.** -/
def stripModule10 (m : ModuleInst) : ModuleInst := { m with exports := [] }

/-- `stripModule10` on a frame's module. -/
def stripFrame10 (f : Frame) : Frame := { f with module := stripModule10 f.module }

/-- `stripModule10` on a defined function instance's module. -/
def stripFI10 : FuncInst V1.Func H → FuncInst V1.Func H
  | .wasm t m fn => .wasm t (stripModule10 m) fn
  | .host t h => .host t h

/-- `stripModule10` on the module of every function instance of a store. -/
def stripStore10 (s : Store H) : Store H := { s with funcs := s.funcs.map stripFI10 }

mutual
/-- `stripFrame10` on every frame inside an administrative instruction. -/
def stripAdmin10 : Admin → Admin
  | .label n cont body => .label n cont (stripAdmins10 body)
  | .frame n f body => .frame n (stripFrame10 f) (stripAdmins10 body)
  | a => a

/-- `stripAdmin10` on a sequence. -/
def stripAdmins10 : List Admin → List Admin
  | [] => []
  | a :: l => stripAdmin10 a :: stripAdmins10 l
end

/-- **A configuration with every export list removed**: the store's function instances, the
frame and every frame in the code. -/
def stripConfig10 (c : Config H) : Config H :=
  ⟨stripStore10 c.store, stripFrame10 c.frame, stripAdmins10 c.code⟩

/-! ## The open leg (frozen) -/

open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

/-- **Leg 3 for 1.0** (frozen): un-stripping a step of `utf8Env10T` between the stripped images
of a V1 step from a configuration typed in `utf8Env10T`. -/
def Task.unstripStep10 : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice)
    (host : HostSemantics H) (c c' : Config H),
    Typed10 (utf8Env10T (Whole.fwdB10 nd r)) hn c → Step host c c' →
      SStepB (utf8Env10T (Whole.fwdB10 nd r)) (configV hn (stripConfig10 c))
          (configV hn (stripConfig10 c')) →
        SStepB (utf8Env10T (Whole.fwdB10 nd r)) (configV hn c) (configV hn c')

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
