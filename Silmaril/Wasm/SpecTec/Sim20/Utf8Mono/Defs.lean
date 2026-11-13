module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreBulk.Thms

/-!
# The 2.0 `$utf8` erratum on top of the `STORE` erratum (definitions)

An earlier step  stated the `$utf8` erratum for the 2.0 script, `StoreBulk.utf8Env20 B`, on top
of `baseEnv20`. The forward invariant `StoreBulk.Good20B` is read in `simEnv20` and its steps in
`simEnv20T`, the script with round 4's `STORE` erratum (`StoreFix.fixedT20`). This header combines
the two errata:

* `utf8BaseEnv20T`: the environment of `fixedT20` with `$utf8` rebound to a declaration with the
  same parameters and result type (`Round7.utf8Params`, `Round7.utf8Res`) and **no clauses**.
  Every type, relation, grammar and other definition is unchanged.
* `utf8Env20T B`: that environment with the primitives `Round6.MemSimd.withUtf8 B`, which answer
  `$utf8` by the UTF-8 encoding of the characters and defer to `B` elsewhere.

`simEnv20T B` and `utf8Env20T B` differ only in `$utf8`, as `simEnv20 B` and `utf8Env20 B` do.

The forward invariant under both errata:

* `TypFU B hn c`: `StoreFn.TypF` read in `utf8Env20 B`: the state with its function bodies
  erased, and the erased code, typed there.
* `Good20BU hn P c`: `StoreBulk.Good20B` with `TypFU` for `TypF`. Every `Good20B` configuration
  is `Good20BU` (`Utf8Mono.good20BU_of_good20B`); a configuration whose module exports a non-empty
  name can be `Good20BU` but is never `Good20B` (an earlier `StoreBulk.not_good20B_single`).
* **`Task.fwdU20`** (frozen, open): every V2 step from a `Good20BU` configuration is a step of
  `utf8Env20T (storeB P)` between the images, and its successor is `Good20BU`. It is
  `StoreBulk.fwd_good20B` with both errata.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Mono

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res)
open Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd (withUtf8)

/-- **The `$utf8` erratum on the `STORE`-corrected 2.0 script**: `$utf8` keeps its signature and
loses its clauses. -/
noncomputable def utf8BaseEnv20T : Env :=
  (envOfScript StoreFix.fixedT20).bindDef "utf8" (utf8Params, utf8Res, [])

/-- **The 2.0 environment with both errata**: `$utf8` answered by the UTF-8 encoding of its
characters, every other primitive by `B`. -/
noncomputable def utf8Env20T (B : Builtins) : Env := utf8BaseEnv20T.withBuiltins (withUtf8 B)

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20 okB StoreOkB StoreSmall)

variable {H : Type}

/-- **The typing part of the invariant under the `$utf8` erratum**: `StoreFn.TypF` read in
`utf8Env20 B`. -/
structure TypFU (B : Builtins) (hn : H → String) (c : Config H) : Prop where
  state : TypedV (utf8Env20 B) stateT (stateV hn (StoreFn.eraseS c.store) c.frame)
  code : TypedV (utf8Env20 B) StepFix.adminsTy (.list (adminsToV (c.code.map StoreDeep.eDA)))

/-- **`Good20B` under the `$utf8` erratum.** -/
structure Good20BU (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile) (c : Config H) :
    Prop where
  typ : TypFU (Whole.storeB P) hn c
  plain : Whole.Plain20 c.store c.frame c.code
  ok : c.code.all (okB c.frame.module) = true
  store : StoreOkB c.store
  small : StoreSmall c.store

/-- **The 2.0 forward theorem under both errata** (frozen, open): `StoreBulk.fwd_good20B` with
`Good20BU` for `Good20B` and `utf8Env20T` for `simEnv20T`. -/
def Task.fwdU20 : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (c c' : Config H), Good20BU hn P c → Step P host c c' →
      Good20BU hn P c' ∧ SStepB (utf8Env20T (Whole.storeB P)) (configV hn c) (configV hn c')

end Silmaril.Wasm.SpecTec.Sim20.Utf8Mono
