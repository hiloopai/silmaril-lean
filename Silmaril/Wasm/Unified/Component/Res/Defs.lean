module

public import Silmaril.Wasm.Unified.Component.Inst.Defs
public import Silmaril.Wasm.Resource.CompToy.Defs

/-!
# Resource sentences of specific components: definitions

The resource-protocol sentences of the unified component institution
(`Silmaril.Wasm.Unified.Component.CSen.res`) read the **import** moves of a program's strategy as
handle events of a declared resource type (`resEv d`): the answer `[h]` of a call of `d.new` is
`alloc h`, a call of `d.drop` (resp. `d.rep`) with `[h]` is `free h` (resp. `use h`). This module
sets up the specific components about which `Silmaril.Wasm.Unified.Component.Res.Thms` proves or
refutes such sentences.

* `Quiet d P`: the program `P` over `sigU` never calls `d.drop` or `d.rep` (it may call `d.new`
  and anything else). `Impl.QuietFor d im`: the target of a wiring program is not a call of
  `d.drop` or `d.rep`.
* **The toy's resource** (`Silmaril.Wasm.Resource.CompToy`, the toy component defining a resource,
  a correct provider by `toy_compProvider`): `toyIface` is the toy's export interface `Xt`
  (`make`, `get`, `drop`, in that order, named by `CompToy.names`) seen as the import interface
  of a client component, with handles passed as flat `i32`s; `toyDecl` declares its resource
  type: `resource.new` is import `0` (`make`), `resource.rep` is import `1` (`get`, which
  answers the representation of a borrowed handle) and `resource.drop` is import `2` (`drop`).
  `toySig`: the CM feature signature with no adapters and this resource type.
* Clients of the toy, components without core instances over `toyIface`: `makeFwd` re-exports
  `make`, `dropFwd` re-exports `drop`, `getFwd` re-exports `get`.

Core modules of the unified institution are closed (`Silmaril.Wasm.Unified.Component.coreSem`
makes no import calls), so in `cinst` a component reaches its imports only through wiring, one
import call per export call. A client that allocates a handle and then uses it in the same
export call needs a core module with imports (`Silmaril.Wasm.Unified.Component.Open`).
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open Silmaril.Wasm.Component Silmaril.Wasm.Unified Silmaril.Wasm.Resource
open Silmaril.Games (Prog)

/-- `P` never calls `d.drop` or `d.rep`. -/
inductive Quiet (d : ResDecl) : Prog sigU (Option Payload) → Prop
  /-- A result. -/
  | pure (r : Option Payload) : Quiet d (.pure r)
  /-- A call of neither `d.drop` nor `d.rep`, continued quietly. -/
  | call (m : Nat × Payload) (k : Option Payload → Prog sigU (Option Payload))
      (hd : m.1 ≠ d.drop) (hr : m.1 ≠ d.rep) (hk : ∀ n, Quiet d (k n)) : Quiet d (.call m k)

/-- The target of the wiring program `im` is not a call of `d.drop` or `d.rep`. -/
def _root_.Silmaril.Wasm.Component.Impl.QuietFor (d : ResDecl) (im : Impl) : Prop :=
  match im.target with
  | .call r => r ≠ d.drop ∧ r ≠ d.rep
  | .const _ => True

/-- Handle events that are neither uses nor frees. -/
def _root_.Silmaril.Wasm.Resource.HEv.Quiet {Hd : Type} : HEv Hd → Prop
  | .alloc _ => True
  | .skip => True
  | _ => False

/-! ## The toy's resource -/

/-- The toy's export interface `make() -> handle`, `get(handle) -> u32`, `drop(handle)`, as the
import interface of a client (handles are flat `i32`s). -/
def toyIface : Iface :=
  [(CompToy.names CompToy.makeE, ⟨[], [.u32]⟩), (CompToy.names CompToy.getE, ⟨[.u32], [.u32]⟩),
    (CompToy.names CompToy.dropE, ⟨[.u32], []⟩)]

/-- The toy's resource type: `resource.new` is `make` (import `0`), `resource.drop` is `drop`
(import `2`), `resource.rep` is `get` (import `1`). -/
def toyDecl : ResDecl := ⟨0, 2, 1⟩

/-- No adapters, the toy's resource type. -/
def toySig : CMSig := withRes coreOnly {toyDecl}

variable {S : FSig}

/-- Re-export `make`. -/
def makeFwd : Comp (UMod S) := .mk toyIface [] [⟨"make", ⟨[], [.u32]⟩, .fwd 0⟩]

/-- Re-export `drop`. -/
def dropFwd : Comp (UMod S) := .mk toyIface [] [⟨"drop", ⟨[.u32], []⟩, .fwd 2⟩]

/-- Re-export `get`. -/
def getFwd : Comp (UMod S) := .mk toyIface [] [⟨"get", ⟨[.u32], [.u32]⟩, .fwd 1⟩]

end Silmaril.Wasm.Unified.Component
