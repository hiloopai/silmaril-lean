module

public import Silmaril.Wasi.Versions.HttpFields.Defs
public import Silmaril.Wasi.Versions.Http3.Defs

@[expose] public section

/-!
# WASI `wasi:http`: request, response and request-options attributes as a theory

Checked against `vendor/wasi/0.2.12/http/types.wit` (the same signatures as
`vendor/wasi/v0.2.9`) and `vendor/wasi/0.3.2/http/types.wit`.

The attributes of the HTTP resources are read and written by getters and setters:

| key | attribute | 0.2 | 0.3 | default |
| --- | --- | --- | --- | --- |
| 0 | method | `outgoing-request.method`/`set-method`, `incoming-request.method` | `request.get-method`/`set-method` | `get` |
| 1 | path with query | `…path-with-query`/`set-path-with-query` | `request.get-…`/`set-…` | `none` |
| 2 | scheme | `…scheme`/`set-scheme` | `request.get-scheme`/`set-scheme` | `none` |
| 3 | authority | `…authority`/`set-authority` | `request.get-authority`/`set-authority` | `none` |
| 4 | connect timeout | `request-options.connect-timeout`/`set-…` | `get-connect-timeout`/`set-…` | `none` |
| 5 | first-byte timeout | as above | as above | `none` |
| 6 | between-bytes timeout | as above | as above | `none` |
| 7 | status code | `outgoing-response.status-code`/`set-status-code` | `response.get-status-code`/`set-…` | `200` |

The defaults are the WIT documentation's ("a default `method` of `GET`, and `none` values for
`path-with-query`, `scheme`, and `authority`"; "a default `status-code` of `200`"; "a default
`request-options` value"). The `method` and `scheme` variants have the same cases in both
versions, `duration` is `u64` in both, `status-code` is `u16` in both (read from the two
`types.wit`).

## The theory `attrTh N`

Generic in the names (`AttrFns`: each function of the slice has an operation `AOp`). Gated.
Its state records, per handle, its attributes (`none`: not tracked, e.g. dropped):

* a constructor (`ctor`: 0.2 `[constructor]outgoing-request`, `request-options`,
  `outgoing-response`; 0.3 `[static]request.new`, `response.new`, `[constructor]request-options`)
  records the defaults for its keys under the handle it answers (the first component of a
  tuple for 0.3 `new`), and forgets the handles it takes over (its owned arguments: headers,
  body stream, trailers future, options);
* `clone` (0.3 `request-options.clone`) copies the attributes;
* a successful setter (`ok`) records the value; a failed one changes nothing (setters may fail:
  invalid syntax, unsupported timeouts);
* 0.3 `request.new` also copies the timeouts of its `options` argument, and
  `request.get-options` answers (when `some`) an **immutable** child with the request's
  timeouts ("The returned `request-options` resource is immutable: `set-*` operations will
  fail if invoked"): a setter of an immutable child must not answer `ok`; `clone` answers a
  mutable copy ("The resulting `request-options` is mutable");
* a getter must answer the recorded value; on a handle never seen (e.g. an incoming request
  handed to an export) the first answer is recorded, so **later answers must agree until a
  setter succeeds or the handle is dropped**;
* `[resource-drop]`s forget the handle, and so do the consuming functions of `eats` (0.2
  `outgoing-handler.handle`, `response-outparam.set`; 0.3 `client.send`, `handler.handle`,
  `request.consume-body`, `response.consume-body`) for every handle they take;
* an export call (`call`) starts every handle it hands in afresh (no attributes recorded).

Traps are allowed. Comparing values uses classical decidability (`Val` has a derived `BEq`
only), so the check is `noncomputable`; the host is computable.

## Concrete host

`attrImpl N`: fresh handles (`2n`, and `2n + 1` for the future of a 0.3 `new`), every setter
succeeds except on an immutable child (`immutable`), getters answer the recorded value or the
default, `get-options` always answers `some` child.

**Not modelled**: syntactic validity of methods, schemes, authorities and paths; whether
`get-options` answers `none` for a request made without options; which values a host
accepts.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Operations and slices -/

/-- The default value of an attribute key (`get` and `none` are both case 0 without payload). -/
def aDflt : Nat → Val
  | 7 => .u16 200
  | _ => noneV

/-- An operation of an attribute slice. -/
inductive AOp where
  /-- A constructor with the defaults of `keys`; `tup`: it answers a tuple (0.3 `new`). -/
  | ctor (keys : List Nat) (tup : Bool)
  /-- 0.3 `request.new`: a constructor answering a tuple, which also copies the timeouts of its
  `options` argument (the fourth). -/
  | ctorO (keys : List Nat)
  /-- 0.3 `request.get-options`: an immutable child with the request's timeouts. -/
  | opts
  /-- A deep copy. -/
  | clone
  /-- The getter of a key. -/
  | get (k : Nat)
  /-- The setter of a key. -/
  | set (k : Nat)
  /-- A resource drop. -/
  | drop
  deriving DecidableEq

/-- An attribute slice: the operations of its functions, and the consuming functions it
watches (not part of the slice). -/
structure AttrFns where
  /-- The functions of the slice with their operations. -/
  ops : List (FnName × AOp)
  /-- Functions outside the slice that take over every handle they are passed. -/
  eats : List FnName

/-- The operation of a function name (`none`: not in the slice). -/
def AttrFns.op (N : AttrFns) (f : FnName) : Option AOp := (N.ops.find? (·.1 == f)).map (·.2)

/-- The functions of an attribute slice. -/
def AttrFns.fns (N : AttrFns) : Set FnName := {f | (N.op f).isSome}

/-- The keys of a request. -/
def reqKeys : List Nat := [0, 1, 2, 3]
/-- The keys of request options. -/
def optKeys : List Nat := [4, 5, 6]
/-- The keys of a response. -/
def respKeys : List Nat := [7]

/-- A 0.2 `wasi:http/types` function. -/
def ht2 (s : String) : FnName := ⟨"wasi:http/types", s⟩
/-- A 0.3 `wasi:http/types` function. -/
def ht3 (s : String) : FnName := ⟨"wasi:http/types@0.3.2", s⟩

/-- **The 0.2 attribute slice** (`vendor/wasi/0.2.12/http/types.wit`). -/
def attrFns2 : AttrFns where
  ops := [
    (ht2 "[constructor]outgoing-request", .ctor reqKeys false),
    (ht2 "[method]outgoing-request.method", .get 0),
    (ht2 "[method]outgoing-request.set-method", .set 0),
    (ht2 "[method]outgoing-request.path-with-query", .get 1),
    (ht2 "[method]outgoing-request.set-path-with-query", .set 1),
    (ht2 "[method]outgoing-request.scheme", .get 2),
    (ht2 "[method]outgoing-request.set-scheme", .set 2),
    (ht2 "[method]outgoing-request.authority", .get 3),
    (ht2 "[method]outgoing-request.set-authority", .set 3),
    (ht2 "[resource-drop]outgoing-request", .drop),
    (ht2 "[method]incoming-request.method", .get 0),
    (ht2 "[method]incoming-request.path-with-query", .get 1),
    (ht2 "[method]incoming-request.scheme", .get 2),
    (ht2 "[method]incoming-request.authority", .get 3),
    (ht2 "[resource-drop]incoming-request", .drop),
    (ht2 "[constructor]request-options", .ctor optKeys false),
    (ht2 "[method]request-options.connect-timeout", .get 4),
    (ht2 "[method]request-options.set-connect-timeout", .set 4),
    (ht2 "[method]request-options.first-byte-timeout", .get 5),
    (ht2 "[method]request-options.set-first-byte-timeout", .set 5),
    (ht2 "[method]request-options.between-bytes-timeout", .get 6),
    (ht2 "[method]request-options.set-between-bytes-timeout", .set 6),
    (ht2 "[resource-drop]request-options", .drop),
    (ht2 "[constructor]outgoing-response", .ctor respKeys false),
    (ht2 "[method]outgoing-response.status-code", .get 7),
    (ht2 "[method]outgoing-response.set-status-code", .set 7),
    (ht2 "[resource-drop]outgoing-response", .drop)]
  eats := [httpHandle, ht2 "[static]response-outparam.set"]

/-- **The 0.3 attribute slice** (`vendor/wasi/0.3.2/http/types.wit`). -/
def attrFns3 : AttrFns where
  ops := [
    (ht3 "[static]request.new", .ctorO reqKeys),
    (ht3 "[method]request.get-method", .get 0),
    (ht3 "[method]request.set-method", .set 0),
    (ht3 "[method]request.get-path-with-query", .get 1),
    (ht3 "[method]request.set-path-with-query", .set 1),
    (ht3 "[method]request.get-scheme", .get 2),
    (ht3 "[method]request.set-scheme", .set 2),
    (ht3 "[method]request.get-authority", .get 3),
    (ht3 "[method]request.set-authority", .set 3),
    (ht3 "[method]request.get-options", .opts),
    (ht3 "[resource-drop]request", .drop),
    (ht3 "[constructor]request-options", .ctor optKeys false),
    (ht3 "[method]request-options.get-connect-timeout", .get 4),
    (ht3 "[method]request-options.set-connect-timeout", .set 4),
    (ht3 "[method]request-options.get-first-byte-timeout", .get 5),
    (ht3 "[method]request-options.set-first-byte-timeout", .set 5),
    (ht3 "[method]request-options.get-between-bytes-timeout", .get 6),
    (ht3 "[method]request-options.set-between-bytes-timeout", .set 6),
    (ht3 "[method]request-options.clone", .clone),
    (ht3 "[resource-drop]request-options", .drop),
    (ht3 "[static]response.new", .ctor respKeys true),
    (ht3 "[method]response.get-status-code", .get 7),
    (ht3 "[method]response.set-status-code", .set 7),
    (ht3 "[resource-drop]response", .drop)]
  eats := [send3, ⟨"wasi:http/handler@0.3.2", "handle"⟩, ht3 "[static]request.consume-body",
    ht3 "[static]response.consume-body"]

/-! ## The theory -/

/-- Attributes: key, value; the first entry of a key counts. -/
abbrev Attrs : Type := List (Nat × Val)

/-- The theory state: per handle, its attributes (`none`: not tracked). -/
abbrev AttrSt : Type := List (BitVec 32 × Option Attrs)

/-- The value of a key. -/
def attrOf (m : Attrs) (k : Nat) : Option Val := (m.find? (·.1 == k)).map (·.2)

/-- The handles an argument list hands over: top-level handles and handles under a case
(`option<own<…>>`, `result<own<…>, _>`). -/
def handlesOf : List Val → List (BitVec 32)
  | [] => []
  | .u32 h :: t => h :: handlesOf t
  | .variant _ (some (.u32 h)) :: t => h :: handlesOf t
  | _ :: t => handlesOf t

/-- Forget the handles `hs`. -/
def forgetH (q : AttrSt) (hs : List (BitVec 32)) : AttrSt := hs.map (fun h => (h, none)) ++ q

/-- The handle a constructor answers (alone, or first in a tuple). -/
def ctorH : Option (List Val) → Option (BitVec 32)
  | some [.u32 h] => some h
  | some [.record (.u32 h :: _)] => some h
  | _ => none

/-- Record the value `v` of the key `k` of the handle `h` (unless it is not tracked). -/
def putA (q : AttrSt) (h : BitVec 32) (k : Nat) (v : Val) : AttrSt :=
  match lookup h q with
  | some (some m) => (h, some ((k, v) :: m)) :: q
  | some none => q
  | none => (h, some [(k, v)]) :: q

/-- The key marking an immutable `request-options` child. -/
def immKey : Nat := 8

/-- The timeouts of a record. -/
def optAttrs (m : Attrs) : Attrs := m.filter (·.1 ∈ optKeys)

/-- The timeouts of the `options` argument of 0.3 `request.new` (`option<request-options>`). -/
def optsArg (q : AttrSt) (a : List Val) : Attrs :=
  match a with
  | _ :: _ :: _ :: .variant 1 (some (.u32 o)) :: _ => optAttrs ((lookup o q).join.getD [])
  | _ => []

/-- The record is an immutable child. -/
def isImm (m : Attrs) : Bool :=
  match attrOf m immKey with
  | some (.bool true) => true
  | _ => false

/-- The next state after the operation `o`. -/
def aNext (o : AOp) (q : AttrSt) (a : List Val) (r : Option (List Val)) : AttrSt :=
  match o with
  | .ctor ks _ =>
    match ctorH r with
    | some h => (h, some (ks.map fun k => (k, aDflt k))) :: forgetH q (handlesOf a)
    | none => q
  | .ctorO ks =>
    match ctorH r with
    | some h => (h, some (ks.map (fun k => (k, aDflt k)) ++ optsArg q a)) :: forgetH q (handlesOf a)
    | none => q
  | .clone =>
    match ctorH r, a with
    | some h', .u32 h :: _ => (h', some (((lookup h q).join.getD []).filter (·.1 != immKey))) :: q
    | _, _ => q
  | .opts =>
    match a, r with
    | .u32 h :: _, some [.variant 1 (some (.u32 o))] =>
      (o, some ((immKey, .bool true) :: optAttrs ((lookup h q).join.getD []))) :: q
    | _, _ => q
  | .get k =>
    match a, r with
    | .u32 h :: _, some [x] =>
      match lookup h q with
      | some (some m) => if (attrOf m k).isSome then q else putA q h k x
      | _ => putA q h k x
    | _, _ => q
  | .set k =>
    match a with
    | .u32 h :: v :: _ => if isOkAns r then putA q h k v else q
    | _ => q
  | .drop => forgetH q (handlesOf a)

/-- The check of an answer of the operation `o`: a getter answers the recorded value, a setter
of an immutable child fails. -/
noncomputable def aOk (o : AOp) (q : AttrSt) (a : List Val) (r : Option (List Val)) : Bool :=
  match o, a, r with
  | .get k, .u32 h :: _, some ans =>
    match lookup h q with
    | some (some m) =>
      match attrOf m k with
      | some v => @decide (ans = [v]) (Classical.propDecidable _)
      | none => true
    | _ => true
  | .set _, .u32 h :: _, r =>
    match lookup h q with
    | some (some m) => !(isImm m && isOkAns r)
    | _ => true
  | _, _, _ => true

/-- The next state. -/
def aNextE (N : AttrFns) (q : AttrSt) (e : WEv) : AttrSt :=
  match e with
  | .imp f a r =>
    match N.op f with
    | some o => aNext o q a r
    | none => if f ∈ N.eats then forgetH q (handlesOf a) else q
  | .call _ a => (handlesOf a).map (fun h => (h, some [])) ++ q
  | _ => q

/-- The check. -/
noncomputable def aOkE (N : AttrFns) (q : AttrSt) (e : WEv) : Bool :=
  match e with
  | .imp f a r =>
    match N.op f with
    | some o => aOk o q a r
    | none => true
  | _ => true

/-- **The attribute theory** of the slice `N`. -/
noncomputable def attrTh (N : AttrFns) : Protocol AttrSt WEv := gated [] (aNextE N) (aOkE N)

/-! ## The concrete host -/

/-- The state after the answers `p`. -/
def attrState (N : AttrFns) (p : List WEv) : AttrSt := p.foldl (aNextE N) []

/-- The tracked attributes of the handle argument, if any. -/
def selfAttrs (q : AttrSt) (a : List Val) : Option Attrs := (lookup (selfH a) q).join

/-- The answer of the operation `o` in the state `q` after `n` events. -/
def aAns (o : AOp) (q : AttrSt) (n : Nat) (a : List Val) : Option (List Val) :=
  match o with
  | .ctor _ false | .clone => some [.u32 (BitVec.ofNat 32 (2 * n))]
  | .ctor _ true | .ctorO _ =>
    some [.record [.u32 (BitVec.ofNat 32 (2 * n)), .u32 (BitVec.ofNat 32 (2 * n + 1))]]
  | .opts => some [.variant 1 (some (.u32 (BitVec.ofNat 32 (2 * n))))]
  | .get k => some [((selfAttrs q a).bind (attrOf · k)).getD (aDflt k)]
  | .set _ =>
    if ((selfAttrs q a).map isImm).getD false then some [errV (some (.variant 1 none))]
    else some [okV none]
  | .drop => some []

/-- **The concrete attribute host** of the slice `N`. -/
def attrImpl (N : AttrFns) : Impl := fun p f a =>
  match N.op f with
  | some o => aAns o (attrState N p) p.length a
  | none => none

end Silmaril.Wasi.Versions.Net
