module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Else.Thms

/-!
# Removing export lists from V2 configurations (definitions)

`Utf8Mono.Task.fwdU20` asks for `SStepB (utf8Env20T _)` derivations at images of configurations
whose modules export non-empty names. The route through the proved forward theorem
`StoreBulk.fwd_good20B` removes every export list first, as round 7 does for Core 3.0
(`Round7.stripConfig`). This header gives the V2 form of that map:

* `stripModule20 m`: `m` with no exports.
* `stripFrame20`, `stripFI20`, `stripStore20`: `stripModule20` on the module of a frame, of a
  function instance and of every function instance of a store.
* `stripAdmin20`, `stripAdmins20`: `stripFrame20` on every frame inside the code, at every depth.
* `stripConfig20 c`: all three on a configuration.
* `NoHost20 s`: no function instance of `s` is a host function. `StoreBulk.StoreOkB` gives it.

**The legs of `Utf8Mono.Task.fwdU20`** (frozen). `Utf8Strip.fwdU20_of_legs` derives the target
from them, from `step_strip20` (proved), `StoreBulk.fwd_good20B` (proved) and
`Utf8Else.sstepB_utf8_20T` (proved):

* `Task.goodStrip20`: a `Good20BU` configuration with its exports removed is `Good20B`. This is a
  typing transfer from `utf8Env20` to `simEnv20` at export-free images (the names are gone, so
  `simEnv20`'s failure on non-empty names no longer applies), plus the non-typing parts of the
  invariant.
* `Task.goodUnstrip20`: the successor of a step from a `Good20BU` configuration is `Good20BU` when
  its stripped form is `Good20B`. The successor's modules are the source's, whose export names
  are typed in `utf8Env20`.
* `Task.unstripStep20`: a step of `utf8Env20T` between the stripped images of a V2 step from a
  `Good20BU` configuration is also a step between the images themselves. It is the 2.0 form of
  round 7's `Round7.Task.swapEquiv`, **without** its injectivity side condition
  (`Round7.StripInj`): two module instances of `c` may differ only in their exports.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution

variable {H : Type}

/-- **A module instance without exports.** -/
def stripModule20 (m : ModuleInst) : ModuleInst := { m with exports := [] }

/-- `stripModule20` on a frame's module. -/
def stripFrame20 (f : Frame) : Frame := { f with module := stripModule20 f.module }

/-- `stripModule20` on a function instance's module. -/
def stripFI20 (fi : FuncInst H) : FuncInst H := { fi with module := stripModule20 fi.module }

/-- `stripModule20` on the module of every function instance of a store. -/
def stripStore20 (s : Store H) : Store H := { s with funcs := s.funcs.map stripFI20 }

mutual
/-- `stripFrame20` on every frame inside an administrative instruction. -/
def stripAdmin20 : Admin → Admin
  | .label n cont body => .label n cont (stripAdmins20 body)
  | .frame n f body => .frame n (stripFrame20 f) (stripAdmins20 body)
  | a => a

/-- `stripAdmin20` on a sequence. -/
def stripAdmins20 : List Admin → List Admin
  | [] => []
  | a :: l => stripAdmin20 a :: stripAdmins20 l
end

/-- **A configuration with every export list removed**: the store's function instances, the
frame and every frame in the code. -/
def stripConfig20 (c : Config H) : Config H :=
  ⟨stripStore20 c.store, stripFrame20 c.frame, stripAdmins20 c.code⟩

/-- **No function instance of `s` is a host function.** -/
def NoHost20 (s : Store H) : Prop :=
  ∀ (a : FuncAddr) (fi : FuncInst H) (h : H), s.funcInst? a = some fi → fi.code ≠ .host h

/-! ## The legs of `Utf8Mono.Task.fwdU20` (frozen) -/

open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (Good20B)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (Good20BU utf8Env20T)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

/-- **Leg 2** (frozen): a `Good20BU` configuration without its exports is `Good20B`. -/
def Task.goodStrip20 : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile) (c : Config H),
    Good20BU hn P c → Good20B hn P (stripConfig20 c)

/-- **The successor half of leg 2** (frozen): the successor of a step from a `Good20BU`
configuration is `Good20BU` when its stripped form is `Good20B`. -/
def Task.goodUnstrip20 : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (c c' : Config H), Good20BU hn P c → Step P host c c' →
      Good20B hn P (stripConfig20 c') → Good20BU hn P c'

/-- **Leg 3** (frozen): un-stripping a step of `utf8Env20T` between the stripped images of a V2
step from a `Good20BU` configuration. -/
def Task.unstripStep20 : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (c c' : Config H), Good20BU hn P c → Step P host c c' →
      SStepB (utf8Env20T (Whole.storeB P)) (configV hn (stripConfig20 c))
          (configV hn (stripConfig20 c')) →
        SStepB (utf8Env20T (Whole.storeB P)) (configV hn c) (configV hn c')

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
