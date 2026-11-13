module

public import Silmaril.Wasm.Resource.Protocol.Defs
public import Silmaril.Wasm.Spec.Wasm.Defs

@[expose] public section

/-!
# Handle protocols

Protocols (`Silmaril.Wasm.Resource.Protocol`) for resources named by **handles**, over an abstract
event alphabet, and classifiers reading Wasm events as handle events.

## Allocate / use / free (`HEv`, `handleProto`)

Events: `alloc h` (the allocator hands out `h`), `use h`, `free h`, `skip`. The state is the
list of live handles, or `none` once the **environment** broke the protocol (absorbing,
everything accepted afterwards). Two orientations (`Role`):

* `client`: the program *uses* handles that the environment allocates (imports
  `alloc() -> h`, `use(h)`, `free(h)`). A `use h`/`free h` of a handle that is not live (never
  allocated, already freed: use-before-alloc, use-after-free, double free, free of a
  never-allocated handle) is a violation; an `alloc h` returning a live handle (not fresh) is an
  environment fault.
* `provider`: the program *allocates* (exports `alloc`, `use`, `free`). An `alloc h` returning a
  live handle is a violation; a `use`/`free` of a dead handle is an environment (client) fault.

## Ownership and borrowing (`OEv`, `obProto`), client orientation

The program holds handles `owned` or `borrowed`:

* `alloc h`/`take h` (environment): the program receives an owned handle (allocation, or an
  ownership transfer to the program, e.g. an `own` argument of an export call);
* `lend h` (environment): `h` is lent to the program for the current export call (a `borrow`
  argument);
* `use h` (program): `h` must be held (owned or borrowed);
* `free h`, `give h` (program): `h` must be **owned** (a borrowed handle may not be dropped or
  transferred); it is no longer held;
* `endCall` (program): the export call returns, every borrow ends (a borrowed handle must not
  outlive the call that lent it: using it later is a use of a handle not held).

Environment faults (a handle handed over twice) lead to the absorbing state `none`.

## Wasm classifiers

Handles are Core values (`Val`): `i32` handles and `externref` handles (`.ref (.extern a)`)
are both covered.

* `clientEv ia iu if_`: the result `returns [h]` of import `ia` is `alloc h`; a call of `iu`
  (resp. `if_`) with the arguments `[h]` is `use h` (resp. `free h`).
* `providerEv ja ju jf`: the same at exports.
* `OBRoles`, `obEv`: which imports allocate, use, free or take ownership, which exports lend or
  transfer their argument; every export return is `endCall`.
* `clientSpec`, `providerSpec`, `obSpec`: the sentences (protocols over the events of an
  interface), formulas of `protoLogic`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-! ## Allocate / use / free -/

/-- Abstract handle events. -/
inductive HEv (Hd : Type) where
  | alloc (h : Hd)
  | use (h : Hd)
  | free (h : Hd)
  | skip
  deriving DecidableEq, Repr

/-- Which side the program is on. -/
inductive Role where
  /-- The program uses handles allocated by the environment. -/
  | client
  /-- The program allocates handles used by the environment. -/
  | provider
  deriving DecidableEq, Repr

/-- The outcome of a fault: a violation (`none`) if the program is to blame, otherwise the
absorbing environment-fault state. -/
def fault {Hd : Type} (byProgram : Bool) : Option (Option (List Hd)) :=
  if byProgram then none else some none

/-- One step of the handle protocol. -/
def handleStep {Hd : Type} [DecidableEq Hd] (r : Role) :
    Option (List Hd) → HEv Hd → Option (Option (List Hd))
  | none, _ => some none
  | some L, .alloc h => if h ∈ L then fault (r == .provider) else some (some (h :: L))
  | some L, .use h => if h ∈ L then some (some L) else fault (r == .client)
  | some L, .free h => if h ∈ L then some (some (L.erase h)) else fault (r == .client)
  | some L, .skip => some (some L)

/-- **The handle protocol** in orientation `r`: no handle is used or freed unless live, and no
live handle is allocated again. -/
def handleProto (Hd : Type) [DecidableEq Hd] (r : Role) : Protocol (Option (List Hd)) (HEv Hd) :=
  ⟨some [], handleStep r⟩

/-! ## Ownership and borrowing -/

/-- How the program holds a handle. -/
inductive Mode where
  | owned
  | borrowed
  deriving DecidableEq, Repr

/-- Ownership and borrowing events. -/
inductive OEv (Hd : Type) where
  | alloc (h : Hd)
  | take (h : Hd)
  | lend (h : Hd)
  | use (h : Hd)
  | free (h : Hd)
  | give (h : Hd)
  | endCall
  | skip
  deriving DecidableEq, Repr

/-- Is `h` held? -/
def held {Hd : Type} [DecidableEq Hd] (L : List (Hd × Mode)) (h : Hd) : Bool :=
  L.any fun p => p.1 == h

/-- Is `h` owned? -/
def owns {Hd : Type} [DecidableEq Hd] (L : List (Hd × Mode)) (h : Hd) : Bool :=
  L.contains (h, .owned)

/-- Drop every entry of `h`. -/
def release {Hd : Type} [DecidableEq Hd] (L : List (Hd × Mode)) (h : Hd) : List (Hd × Mode) :=
  L.filter fun p => p.1 != h

/-- One step of the ownership protocol (program = holder). -/
def obStep {Hd : Type} [DecidableEq Hd] :
    Option (List (Hd × Mode)) → OEv Hd → Option (Option (List (Hd × Mode)))
  | none, _ => some none
  | some L, .alloc h => if held L h then some none else some (some ((h, .owned) :: L))
  | some L, .take h => if held L h then some none else some (some ((h, .owned) :: L))
  | some L, .lend h => if held L h then some none else some (some ((h, .borrowed) :: L))
  | some L, .use h => if held L h then some (some L) else none
  | some L, .free h => if owns L h then some (some (release L h)) else none
  | some L, .give h => if owns L h then some (some (release L h)) else none
  | some L, .endCall => some (some (L.filter fun p => p.2 == .owned))
  | some L, .skip => some (some L)

/-- **The ownership and borrowing protocol**: handles are used only while held, dropped or
transferred only when owned, and borrows end with the call that lent them. -/
def obProto (Hd : Type) [DecidableEq Hd] : Protocol (Option (List (Hd × Mode))) (OEv Hd) :=
  ⟨some [], obStep⟩

/-! ## Wasm classifiers -/

/-- The handle allocated by a result: `returns [h]`. -/
def HEv.allocOf : Behaviour Val → HEv Val
  | .returns [h] => .alloc h
  | _ => .skip

/-- The handle used by arguments `[h]`. -/
def HEv.useOf : List Val → HEv Val
  | [h] => .use h
  | _ => .skip

/-- The handle freed by arguments `[h]`. -/
def HEv.freeOf : List Val → HEv Val
  | [h] => .free h
  | _ => .skip

section
variable {Ty : Type} {X : Iface Ty}

/-- Client classifier: imports `ia` (allocate), `iu` (use), `if_` (free). -/
def clientEv (ia iu if_ : X.Imp) : Event (List Val) (Behaviour Val) X → HEv Val
  | .inl (.ans i b) => if i = ia then HEv.allocOf b else .skip
  | .inl (.ask i a) => if i = iu then HEv.useOf a else if i = if_ then HEv.freeOf a else .skip
  | .inr _ => .skip

/-- Provider classifier: exports `ja` (allocate), `ju` (use), `jf` (free). -/
def providerEv (ja ju jf : X.Exp) : Event (List Val) (Behaviour Val) X → HEv Val
  | .inr (.ans j b) => if j = ja then HEv.allocOf b else .skip
  | .inr (.ask j a) => if j = ju then HEv.useOf a else if j = jf then HEv.freeOf a else .skip
  | .inl _ => .skip

/-- **The client handle sentence.** -/
def clientSpec (ia iu if_ : X.Imp) :
    Protocol (Option (List Val)) (Event (List Val) (Behaviour Val) X) :=
  (handleProto Val .client).comap (clientEv ia iu if_)

/-- **The provider handle sentence.** -/
def providerSpec (ja ju jf : X.Exp) :
    Protocol (Option (List Val)) (Event (List Val) (Behaviour Val) X) :=
  (handleProto Val .provider).comap (providerEv ja ju jf)

/-- The roles of the functions of an interface in the ownership protocol (client side). -/
structure OBRoles (X : Iface Ty) where
  /-- Imports returning a new owned handle. -/
  alloc : X.Imp → Bool
  /-- Imports using their handle argument. -/
  use : X.Imp → Bool
  /-- Imports dropping their (owned) handle argument. -/
  free : X.Imp → Bool
  /-- Imports taking ownership of their handle argument. -/
  give : X.Imp → Bool
  /-- Exports whose handle argument is borrowed for the call. -/
  lend : X.Exp → Bool
  /-- Exports whose handle argument is owned by the program from then on. -/
  take : X.Exp → Bool

/-- An ownership event from a result `returns [h]`. -/
def OEv.ofRes (k : Val → OEv Val) : Behaviour Val → OEv Val
  | .returns [h] => k h
  | _ => .skip

/-- An ownership event from arguments `[h]`. -/
def OEv.ofArgs (k : Val → OEv Val) : List Val → OEv Val
  | [h] => k h
  | _ => .skip

/-- Ownership classifier. -/
def obEv (ρ : OBRoles X) : Event (List Val) (Behaviour Val) X → OEv Val
  | .inl (.ans i b) => if ρ.alloc i then OEv.ofRes .alloc b else .skip
  | .inl (.ask i a) =>
    if ρ.use i then OEv.ofArgs .use a else if ρ.free i then OEv.ofArgs .free a
    else if ρ.give i then OEv.ofArgs .give a else .skip
  | .inr (.ask j a) =>
    if ρ.lend j then OEv.ofArgs .lend a else if ρ.take j then OEv.ofArgs .take a else .skip
  | .inr (.ans _ _) => .endCall

/-- **The ownership and borrowing sentence.** -/
def obSpec (ρ : OBRoles X) :
    Protocol (Option (List (Val × Mode))) (Event (List Val) (Behaviour Val) X) :=
  (obProto Val).comap (obEv ρ)

end

end Silmaril.Wasm.Resource
