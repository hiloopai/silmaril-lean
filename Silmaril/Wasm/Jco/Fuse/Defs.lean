module

public import Silmaril.Wasm.Jco.Fuse.Glue.Defs
public import Silmaril.Wasm.Component.Semantics.Defs

/-!
# Fusing an adaptor and a core module

The jco-style toolchain turns a core module `m` together with WIT metadata
into a component. In the **adaptor style** (part (a) of docs/projects/wasm-components.md) the
component has two core instances: `m` (its imports wired to the component's
imports) and a generated stateless adaptor module `g` (a `Glue` module whose
imports are `m`'s exports), and it exports `canon lift` of the adaptor's
functions. This module defines the two *fused* outputs of part (f):

* the **single core module** `JMod.fused m g`: the code of `m` together with
  the adaptor's functions, calling `m`'s functions internally; it imports what
  `m` imports and exports what `g` exports;
* the **wrapper-style single component** `wrapperComp`: one instance of the
  fused module, its imports wired as `m`'s, and the same `canon lift` exports.
  It is the trivial wrapping of the fused module.

## Modules

Components are over the module type `JMod M`: a core module of `M`
(`base`), an adaptor (`glue`) or a fused module (`fused`). Given a semantics
`C : CoreSem M`, `fuseSem C : CoreSem (JMod M)` interprets `base m` by
`C.sem m`, `glue g` by its handler, and `fused m g` by the denotation of the
two-instance component `inner m g` (an instance of `m`, then of `g` over
`m`'s exports; the exports are those of `g`), at the interface sizes. That is
the specification of a fused module for an *arbitrary* core semantics: `C` is
opaque, so the only thing a fused module can be required to do is to behave as
the linking of its parts. For a concrete core language the fusion is an actual
code transformation: for glue code it is inlining (`Glue.inline`, proved
correct in `Silmaril.Wasm.Jco.Fuse.Glue.Thms`).

## The simple FFI style

`simpleAdaptor W E` is the adaptor of the simplest calling convention: the
module exports, for each function `f : ft` of the world exports `W`, a core
function `f` of type `ft.flat` (flat values only, no memory, no `realloc`);
the adaptor's `f` delegates to `m`'s export named `f` (a missing export
traps). `simpleImports I E` wires each core import of `m` named `f` to the
`canon lower` of the world import `f` (a missing import traps).
`simpleComp`, `simpleCore` and `simpleWrapper` are the adaptor-style
component, the single core module and the wrapper-style component of this
style.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Fuse

open Silmaril.Games
open Silmaril.Wasm.Component

/-- Core modules of a jco-style toolchain over base modules `M`. -/
inductive JMod (M : Type) where
  /-- A given core module. -/
  | base (m : M)
  /-- A generated adaptor. -/
  | glue (g : Glue)
  /-- The fusion of a given module and an adaptor over its exports. -/
  | fused (m : M) (g : Glue)

namespace JMod

variable {M : Type} [CoreModule M]

/-- The imports of a module. -/
def imports : JMod M → CoreIface
  | .base m => CoreModule.imports m
  | .glue g => g.imports
  | .fused m _ => CoreModule.imports m

/-- The exports of a module. -/
def exports : JMod M → CoreIface
  | .base m => CoreModule.exports m
  | .glue g => g.exports
  | .fused _ g => g.exports

end JMod

instance {M : Type} [CoreModule M] : CoreModule (JMod M) where
  imports := JMod.imports
  exports := JMod.exports

variable {M : Type} [CoreModule M]

/-- Forward `n` functions, starting at `b`. -/
def fwdFrom (b n : Nat) : List Impl := (List.range n).map fun i => Impl.fwd (b + i)

/-- `canon lift` exports of the functions `W`, the `j`-th one implemented by
environment function `b + j`. -/
def liftExports : Iface → Nat → List Silmaril.Wasm.Component.Export
  | [], _ => []
  | x :: W, b => ⟨x.1, x.2, ⟨[.lift x.2], .call b⟩⟩ :: liftExports W (b + 1)

/-- An interface of `n` anonymous functions (only its length matters to the
semantics). -/
def anonIface (n : Nat) : Iface := List.replicate n ("", default)

/-- The two-instance component a fused module stands for: an instance of `m`
(forwarding the imports), an instance of `g` over `m`'s exports, and `g`'s
exports. -/
def inner (m : M) (g : Glue) : Comp (JMod M) :=
  .mk (anonIface (CoreModule.imports m).length)
    [.core (.base m) ((List.range (CoreModule.imports m).length).map Impl.fwd),
     .core (.glue g) (fwdFrom (CoreModule.imports m).length g.imports.length)]
    ((List.range g.exports.length).map fun j =>
      ⟨"", default, Impl.fwd ((CoreModule.imports m).length + (CoreModule.exports m).length + j)⟩)

/-- The semantics of base modules and adaptors (fused modules trap). -/
def baseSem (C : CoreSem M) : CoreSem (JMod M) where
  sem
    | .base m => C.sem m
    | .glue g => Strategy.ofHandler g.handler
    | .fused _ _ => Strategy.ofHandler fun _ => .pure none

/-- **The semantics of fused modules**: a fused module behaves as the linking
of its parts. -/
def fuseSem (C : CoreSem M) : CoreSem (JMod M) where
  sem
    | .base m => C.sem m
    | .glue g => Strategy.ofHandler g.handler
    | .fused m g => atSizes _ _ ((inner m g).denU (baseSem C))

/-! ## The adaptor-style and wrapper-style components -/

/-- **Adaptor style** (part (a)): imports `I`, an instance of `m` with the
import wiring `args`, an instance of the adaptor `g` over `m`'s exports, and
`canon lift` exports `W` of the adaptor's functions. -/
def adaptorComp (I W : Iface) (m : M) (g : Glue) (args : List Impl) : Comp (JMod M) :=
  .mk I [.core (.base m) args, .core (.glue g) (fwdFrom I.length g.imports.length)]
    (liftExports W (I.length + (CoreModule.exports m).length))

/-- **Wrapper style** (part (f)): one instance of the fused module, with the
same import wiring and `canon lift` exports. -/
def wrapperComp (I W : Iface) (m : M) (g : Glue) (args : List Impl) : Comp (JMod M) :=
  .mk I [.core (.fused m g) args] (liftExports W I.length)

/-! ## The simple FFI style -/

/-- The position of the function named `n` in a core interface (its length
when absent: calls of it trap). -/
def nameIdx (E : CoreIface) (n : String) : Nat := E.findIdx fun x => x.1 == n

/-- The position and type of the function named `n` of an interface. -/
def findFn : Iface → String → Option (Nat × FuncTy)
  | [], _ => none
  | x :: I, n => if x.1 = n then some (0, x.2) else (findFn I n).map fun r => (r.1 + 1, r.2)

/-- **The adaptor of the simple FFI style**: for each world export `f : ft`,
a core export `f : ft.flat` delegating to `m`'s export named `f`. -/
def simpleAdaptor (W : Iface) (E : CoreIface) : Glue where
  imports := E
  exports := W.map fun x => (x.1, x.2.flat)
  code := W.map fun x => Code.delegate (nameIdx E x.1)

/-- The import wiring of the simple FFI style: the core import `f` is the
`canon lower` of the world import `f` (a missing one traps). -/
def simpleImports (I : Iface) (E : CoreIface) : List Impl :=
  E.map fun x =>
    match findFn I x.1 with
    | some (i, ft) => ⟨[.lower ft], .call i⟩
    | none => Impl.trap

/-- The adaptor-style component of the simple FFI style. -/
def simpleComp (I W : Iface) (m : M) : Comp (JMod M) :=
  adaptorComp I W m (simpleAdaptor W (CoreModule.exports m)) (simpleImports I (CoreModule.imports m))

/-- **The single core module** of the simple FFI style. -/
def simpleCore (W : Iface) (m : M) : JMod M :=
  .fused m (simpleAdaptor W (CoreModule.exports m))

/-- **The wrapper-style single component** of the simple FFI style. -/
def simpleWrapper (I W : Iface) (m : M) : Comp (JMod M) :=
  wrapperComp I W m (simpleAdaptor W (CoreModule.exports m)) (simpleImports I (CoreModule.imports m))

end Silmaril.Wasm.Jco.Fuse
