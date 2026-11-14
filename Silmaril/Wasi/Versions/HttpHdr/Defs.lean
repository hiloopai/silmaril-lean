module

public import Silmaril.Wasi.Versions.HttpAttr.Defs

@[expose] public section

/-!
# WASI `wasi:http` headers of requests and responses: immutability and validity

A variant of the `fields` theory `fieldsTh` (`Silmaril.Wasi.Versions.HttpFields`) that also follows
the headers of requests and responses. Checked against `vendor/wasi/0.2.12/http/types.wit`
(the same signatures as `vendor/wasi/v0.2.9`) and `vendor/wasi/0.3.2/http/types.wit`:

* a request or response is constructed from a `headers` resource (0.2
  `[constructor]outgoing-request(headers)`, `[constructor]outgoing-response(headers)`; 0.3
  `[static]request.new(headers, …)`, `[static]response.new(headers, …)`), which it takes over;
* its headers accessor (0.2 `outgoing-request.headers`, `outgoing-response.headers`,
  `incoming-request.headers`, `incoming-response.headers`; 0.3 `request.get-headers`,
  `response.get-headers`) answers a child `fields` which "is immutable: `set`, `append`, and
  `delete` operations will fail with `header-error.immutable`";
* "An error result will be returned if any `field-name` or `field-value` is syntactically
  invalid" (`from-list`, `set`, `append`).

## The theory `hdrTh N`

Gated, generic in the names (`HdrFns`). Its state records, per `fields` handle, its contents
(`none`: unknown) and whether it is immutable, and, per request or response, the headers it was
constructed with (`none`: unknown, e.g. an incoming request). The steps:

* the `fields` operations move the contents as in `fieldsTh` (`opNext`), and their answers are
  checked as there (`opCheck`) when the contents are known;
* a constructor with headers records the headers' contents under the parent it answers and
  forgets the `fields` handle (taken over);
* an accessor records the child it answers as immutable, with the parent's headers;
* **a mutation (`set`, `delete`, `append`, `get-and-delete`) of an immutable `fields` must fail
  with `immutable`** (or trap);
* **a successful `from-list`, `set` or `append` has valid names and values**: a name is a
  non-empty RFC 9110 token (`tchar`s), a value has no NUL, LF or CR byte (`valueOk`; values with
  other control bytes are not rejected by every implementation and are not checked);
* drops, consuming calls (`eats`) and export calls forget the handles they take.

Traps are allowed; mutations of mutable fields may still fail (e.g. `forbidden`).

## Concrete host

`hdrImpl N`: as `fieldsImpl`, plus: mutations of immutable fields answer `immutable`, invalid
names or values `invalid-syntax`; constructors and accessors answer fresh handles.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Operations and slices -/

/-- An operation of a headers slice. -/
inductive HOp where
  /-- A `fields` operation. -/
  | f (o : FOp)
  /-- A constructor taking a `headers` first; `tup`: it answers a tuple (0.3 `new`). -/
  | mk (tup : Bool)
  /-- The headers accessor of a request or response. -/
  | hdrs
  /-- `[resource-drop]fields`. -/
  | dropF
  /-- The drop of a request or response. -/
  | dropP
  deriving DecidableEq

/-- A headers slice. -/
structure HdrFns where
  /-- The functions of the slice with their operations. -/
  ops : List (FnName × HOp)
  /-- Functions outside the slice that take over every handle they are passed. -/
  eats : List FnName

/-- The operation of a function name (`none`: not in the slice). -/
def HdrFns.op (N : HdrFns) (f : FnName) : Option HOp := (N.ops.find? (·.1 == f)).map (·.2)

/-- The functions of a headers slice. -/
def HdrFns.fns (N : HdrFns) : Set FnName := {f | (N.op f).isSome}

/-- The `fields` operations of a `FieldsFns` slice. -/
def fieldsOps (N : FieldsFns) : List (FnName × HOp) :=
  [(N.ctor, .f .ctor), (N.fromList, .f .fromList), (N.get, .f .get), (N.has, .f .has),
    (N.set, .f .set), (N.delete, .f .delete), (N.append, .f .append), (N.entries, .f .entries),
    (N.clone, .f .clone)] ++ (N.getDel.map (fun g => (g, HOp.f .getDel))).toList

/-- **The 0.2 headers slice.** -/
def hdrFns2 : HdrFns where
  ops := fieldsOps fieldsFns2 ++ [
    (ht2 "[resource-drop]fields", .dropF),
    (ht2 "[constructor]outgoing-request", .mk false),
    (ht2 "[constructor]outgoing-response", .mk false),
    (ht2 "[method]outgoing-request.headers", .hdrs),
    (ht2 "[method]outgoing-response.headers", .hdrs),
    (ht2 "[method]incoming-request.headers", .hdrs),
    (ht2 "[method]incoming-response.headers", .hdrs),
    (ht2 "[resource-drop]outgoing-request", .dropP),
    (ht2 "[resource-drop]outgoing-response", .dropP),
    (ht2 "[resource-drop]incoming-request", .dropP),
    (ht2 "[resource-drop]incoming-response", .dropP)]
  eats := [httpHandle, ht2 "[static]response-outparam.set", ht2 "[static]outgoing-body.finish"]

/-- **The 0.3 headers slice.** -/
def hdrFns3 : HdrFns where
  ops := fieldsOps fieldsFns3 ++ [
    (ht3 "[resource-drop]fields", .dropF),
    (ht3 "[static]request.new", .mk true),
    (ht3 "[static]response.new", .mk true),
    (ht3 "[method]request.get-headers", .hdrs),
    (ht3 "[method]response.get-headers", .hdrs),
    (ht3 "[resource-drop]request", .dropP),
    (ht3 "[resource-drop]response", .dropP)]
  eats := [send3, ⟨"wasi:http/handler@0.3.2", "handle"⟩, ht3 "[static]request.consume-body",
    ht3 "[static]response.consume-body"]

/-! ## Validity -/

/-- An RFC 9110 `tchar`. -/
def tchar (c : Char) : Bool := c.isAlphanum || "!#$%&'*+-.^_`|~".toList.contains c

/-- A valid field name: a non-empty token. -/
def nameOk (n : List Char) : Bool := !n.isEmpty && n.all tchar

/-- A field value without NUL, LF or CR. -/
def valueOk (v : List (BitVec 8)) : Bool := v.all fun b => b != 0 && b != 10 && b != 13

/-- A valid entry. -/
def entryOk (x : List Char × List (BitVec 8)) : Bool := nameOk x.1 && valueOk x.2

/-- The arguments of a `fields` operation are valid (only `from-list`, `set`, `append` are
checked; undecodable arguments count as valid). -/
def argsOk (o : FOp) (a : List Val) : Bool :=
  match o, a with
  | .set, _ :: nv :: vv :: _ =>
    match nameOf nv, valsOf vv with
    | some n, some vs => nameOk n && vs.all valueOk
    | _, _ => true
  | .append, _ :: nv :: vv :: _ =>
    match nameOf nv, valOf vv with
    | some n, some v => nameOk n && valueOk v
    | _, _ => true
  | .fromList, x :: _ =>
    match fieldsOf x with
    | some l => l.all entryOk
    | none => true
  | _, _ => true

/-! ## The theory -/

/-- A `fields` entry: its contents (`none`: unknown) and whether it is immutable. -/
abbrev HE : Type := Option Fields × Bool

/-- The theory state. -/
structure HdrSt where
  /-- Per `fields` handle. -/
  fs : List (BitVec 32 × HE) := []
  /-- Per request or response: the headers it was constructed with. -/
  par : List (BitVec 32 × Option Fields) := []

/-- Forget the handles `hs` (as `fields` and as parents). -/
def HdrSt.forget (q : HdrSt) (hs : List (BitVec 32)) : HdrSt :=
  { fs := hs.map (fun h => (h, ((none : Option Fields), false))) ++ q.fs,
    par := hs.map (fun h => (h, (none : Option Fields))) ++ q.par }

/-- `immutable` (or a trap). -/
def immOk : Option (List Val) → Bool
  | none => true
  | some [.variant 1 (some (.variant 2 none))] => true
  | _ => false

/-- The next state after the `fields` operation `o`. -/
def hNextF (o : FOp) (q : HdrSt) (a : List Val) (r : Option (List Val)) : HdrSt :=
  match o with
  | .ctor =>
    match handleOf r with
    | some h => { q with fs := (h, (some [], false)) :: q.fs }
    | none => q
  | .fromList =>
    match handleOf r, a with
    | some h, x :: _ => { q with fs := (h, (fieldsOf x, false)) :: q.fs }
    | _, _ => q
  | .clone =>
    match handleOf r, a with
    | some h', .u32 h :: _ => { q with fs := (h', ((lookup h q.fs).bind (·.1), false)) :: q.fs }
    | _, _ => q
  | o =>
    if o.mutates && isOkAns r then
      match a with
      | .u32 h :: a' =>
        match lookup h q.fs with
        | some (some m, imm) => { q with fs := (h, (mutate o m a', imm)) :: q.fs }
        | _ => q
      | _ => q
    else q

/-- The check of the `fields` operation `o`. -/
def hOkF (o : FOp) (q : HdrSt) (a : List Val) (r : Option (List Val)) : Bool :=
  (!isOkAns r || argsOk o a) &&
  match a with
  | .u32 h :: a' =>
    match lookup h q.fs with
    | some (m?, imm) =>
      (!(o.mutates && imm) || immOk r) &&
      match m? with
      | some m => opCheck o m a' r
      | none => true
    | none => true
  | _ => true

/-- The next state after the operation `o`. -/
def hNext (o : HOp) (q : HdrSt) (a : List Val) (r : Option (List Val)) : HdrSt :=
  match o with
  | .f o => hNextF o q a r
  | .mk _ =>
    match a, ctorH r with
    | .u32 hf :: _, some p =>
      { fs := (hf, (none, false)) :: q.fs, par := (p, (lookup hf q.fs).bind (·.1)) :: q.par }
    | _, _ => q
  | .hdrs =>
    match a, ctorH r with
    | .u32 p :: _, some h => { q with fs := (h, ((lookup p q.par).join, true)) :: q.fs }
    | _, _ => q
  | .dropF | .dropP => q.forget (handlesOf a)

/-- The check of the operation `o`. -/
def hOk (o : HOp) (q : HdrSt) (a : List Val) (r : Option (List Val)) : Bool :=
  match o with
  | .f o => hOkF o q a r
  | _ => true

/-- The next state. -/
def hNextE (N : HdrFns) (q : HdrSt) (e : WEv) : HdrSt :=
  match e with
  | .imp f a r =>
    match N.op f with
    | some o => hNext o q a r
    | none => if f ∈ N.eats then q.forget (handlesOf a) else q
  | .call _ a => q.forget (handlesOf a)
  | _ => q

/-- The check. -/
def hOkE (N : HdrFns) (q : HdrSt) (e : WEv) : Bool :=
  match e with
  | .imp f a r =>
    match N.op f with
    | some o => hOk o q a r
    | none => true
  | _ => true

/-- **The headers theory** of the slice `N`. -/
def hdrTh (N : HdrFns) : Protocol HdrSt WEv := gated {} (hNextE N) (hOkE N)

/-! ## The concrete host -/

/-- The state after the answers `p`. -/
def hdrState (N : HdrFns) (p : List WEv) : HdrSt := p.foldl (hNextE N) {}

/-- The contents of the `fields` handles, as a `fieldsTh` state. -/
def HdrSt.proj (q : HdrSt) : FSt := q.fs.map fun x => (x.1, x.2.1)

/-- The handle argument is immutable. -/
def selfImm (q : HdrSt) (a : List Val) : Bool :=
  match a with
  | .u32 h :: _ => ((lookup h q.fs).map (·.2)).getD false
  | _ => false

/-- The answer of the `fields` operation `o`. -/
def hAnsF (o : FOp) (q : HdrSt) (fresh : BitVec 32) (a : List Val) : Option (List Val) :=
  if o.mutates && selfImm q a then some [errV (some (.variant 2 none))]
  else if !argsOk o a then some [errV (some (.variant 0 none))]
  else opAns o q.proj fresh a

/-- The answer of the operation `o` in the state `q` after `n` events. -/
def hAns (o : HOp) (q : HdrSt) (n : Nat) (a : List Val) : Option (List Val) :=
  match o with
  | .f o => hAnsF o q (BitVec.ofNat 32 (2 * n)) a
  | .mk false | .hdrs => some [.u32 (BitVec.ofNat 32 (2 * n))]
  | .mk true => some [.record [.u32 (BitVec.ofNat 32 (2 * n)), .u32 (BitVec.ofNat 32 (2 * n + 1))]]
  | .dropF | .dropP => some []

/-- **The concrete headers host** of the slice `N`. -/
def hdrImpl (N : HdrFns) : Impl := fun p f a =>
  match N.op f with
  | some o => hAns o (hdrState N p) p.length a
  | none => none

end Silmaril.Wasi.Versions.Net
