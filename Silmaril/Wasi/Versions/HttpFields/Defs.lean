module

public import Silmaril.Wasi.Versions.HttpBody2Over.Defs

@[expose] public section

/-!
# WASI `wasi:http` headers: the `fields` resource as a theory

Checked against `vendor/wasi/0.2.12/http/types.wit` (the same signatures as
`vendor/wasi/v0.2.9`) and `vendor/wasi/0.3.2/http/types.wit`. Both versions have the resource
`fields` with

* `constructor()`, `[static]fields.from-list(entries) -> result<fields, header-error>`,
  `clone() -> fields`;
* `get(name) -> list<field-value>`, `has(name) -> bool`;
* `set(name, values) -> result<_, header-error>`, `delete(name) -> result<_, header-error>`,
  `append(name, value) -> result<_, header-error>`;
* `entries() -> list<tuple<field-name, field-value>>` (0.2) / `copy-all()` (0.3, same type);
* 0.3 only: `get-and-delete(name) -> result<list<field-value>, header-error>`.

`field-name = string` (a list of `char`s), `field-value = list<u8>`. The theory is generic in
the function names (`FieldsFns`): `fieldsFns2` and `fieldsFns3` name the two versions, and
the 0.3-only `get-and-delete` is an optional name.

## The theory `fieldsTh N`

Gated. Its state records, per handle that the slice hands out (`constructor`, `from-list`,
`clone`), the fields (`none`: not tracked, e.g. undecodable). Names are compared after
`Char.toLower` (`low`): WIT says names are case-insensitive. A successful `set` / `delete` /
`append` / `get-and-delete` updates the tracked fields (`set` and `delete` remove every entry
of the name; `set` and `append` add at the end); a failed one changes nothing. The check:

* `get(name)`: the values of the name, in order;
* `has(name)`: whether the name has a value;
* `entries` / `copy-all`: the entries, as a permutation, names compared after `low` (an
  implementation may group them by name or normalise their case);
* `get-and-delete(name)`: `ok` of the values of the name, or an error.

The theory is loose: mutations may fail (`header-error`; e.g. immutable fields), and traps are
allowed.

## Concrete host

`fieldsImpl N`: fresh handles, every mutation succeeds, `from-list` fails with
`invalid-syntax` exactly on undecodable entries, answers from the theory state.

**Not modelled**: syntactic validity and forbidden names, immutability of the fields handed out
by `outgoing-request.headers` and friends, resource drops (a handle handed out outside the
slice is assumed not to reuse a tracked one).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Function names -/

/-- The function names of a `fields` slice. -/
structure FieldsFns where
  /-- `[constructor]fields`. -/
  ctor : FnName
  /-- `[static]fields.from-list`. -/
  fromList : FnName
  /-- `[method]fields.get`. -/
  get : FnName
  /-- `[method]fields.has`. -/
  has : FnName
  /-- `[method]fields.set`. -/
  set : FnName
  /-- `[method]fields.delete`. -/
  delete : FnName
  /-- `[method]fields.append`. -/
  append : FnName
  /-- `[method]fields.entries` (0.2) / `copy-all` (0.3). -/
  entries : FnName
  /-- `[method]fields.clone`. -/
  clone : FnName
  /-- `[method]fields.get-and-delete` (0.3 only). -/
  getDel : Option FnName

/-- The 0.2 names (`vendor/wasi/0.2.12/http/types.wit`). -/
def fieldsFns2 : FieldsFns where
  ctor := ⟨"wasi:http/types", "[constructor]fields"⟩
  fromList := ⟨"wasi:http/types", "[static]fields.from-list"⟩
  get := ⟨"wasi:http/types", "[method]fields.get"⟩
  has := ⟨"wasi:http/types", "[method]fields.has"⟩
  set := ⟨"wasi:http/types", "[method]fields.set"⟩
  delete := ⟨"wasi:http/types", "[method]fields.delete"⟩
  append := ⟨"wasi:http/types", "[method]fields.append"⟩
  entries := entries2
  clone := ⟨"wasi:http/types", "[method]fields.clone"⟩
  getDel := none

/-- The 0.3 names (`vendor/wasi/0.3.2/http/types.wit`). -/
def fieldsFns3 : FieldsFns where
  ctor := ⟨"wasi:http/types@0.3.2", "[constructor]fields"⟩
  fromList := ⟨"wasi:http/types@0.3.2", "[static]fields.from-list"⟩
  get := ⟨"wasi:http/types@0.3.2", "[method]fields.get"⟩
  has := ⟨"wasi:http/types@0.3.2", "[method]fields.has"⟩
  set := ⟨"wasi:http/types@0.3.2", "[method]fields.set"⟩
  delete := ⟨"wasi:http/types@0.3.2", "[method]fields.delete"⟩
  append := ⟨"wasi:http/types@0.3.2", "[method]fields.append"⟩
  entries := copyAll3
  clone := ⟨"wasi:http/types@0.3.2", "[method]fields.clone"⟩
  getDel := some ⟨"wasi:http/types@0.3.2", "[method]fields.get-and-delete"⟩

/-- The operations of a `fields` slice. -/
inductive FOp where
  | ctor | fromList | get | has | set | delete | append | entries | clone | getDel
  deriving DecidableEq

/-- The operation of a function name (`none`: not in the slice). -/
def FieldsFns.op (N : FieldsFns) (f : FnName) : Option FOp :=
  if f = N.ctor then some .ctor
  else if f = N.fromList then some .fromList
  else if f = N.get then some .get
  else if f = N.has then some .has
  else if f = N.set then some .set
  else if f = N.delete then some .delete
  else if f = N.append then some .append
  else if f = N.entries then some .entries
  else if f = N.clone then some .clone
  else if some f = N.getDel then some .getDel
  else none

/-- The functions of a `fields` slice. -/
def FieldsFns.fns (N : FieldsFns) : Set FnName := {f | (N.op f).isSome}

/-! ## Names and values -/

/-- A name, compared case-insensitively. -/
def low (n : List Char) : List Char := n.map Char.toLower

/-- The values of the name `n`, in order. -/
def valsOfName (m : Fields) (n : List Char) : List (List (BitVec 8)) :=
  (m.filter (fun x => low x.1 == low n)).map (·.2)

/-- The fields without the name `n`. -/
def dropName (m : Fields) (n : List Char) : Fields := m.filter (fun x => low x.1 != low n)

/-- `list<field-value>`. -/
def valsV (l : List (List (BitVec 8))) : Val := .record (l.map bytesV)

/-- Decode a `list<field-value>`. -/
def valsOfL : List Val → Option (List (List (BitVec 8)))
  | [] => some []
  | .record bs :: t =>
    match u8sOf bs, valsOfL t with
    | some b, some l => some (b :: l)
    | _, _ => none
  | _ => none

/-- Decode a name. -/
def nameOf : Val → Option (List Char)
  | .record cs => charsOf cs
  | _ => none

/-- Decode a value. -/
def valOf : Val → Option (List (BitVec 8))
  | .record bs => u8sOf bs
  | _ => none

/-- Decode a `list<field-value>`. -/
def valsOf : Val → Option (List (List (BitVec 8)))
  | .record vs => valsOfL vs
  | _ => none

/-- An entry with its name compared case-insensitively. -/
def lowE (x : List Char × List (BitVec 8)) : List Char × List (BitVec 8) := (low x.1, x.2)

/-! ## The theory -/

/-- The theory state: per handle, its fields (`none`: not tracked). -/
abbrev FSt : Type := List (BitVec 32 × Option Fields)

/-- `ok(handle)` of `from-list`, or the handle of `constructor` / `clone`. -/
def handleOf : Option (List Val) → Option (BitVec 32)
  | some [.u32 h] => some h
  | some [.variant 0 (some (.u32 h))] => some h
  | _ => none

/-- `ok` of a mutation (`result<_, header-error>` or `result<list<field-value>, _>`). -/
def isOkAns : Option (List Val) → Bool
  | some [.variant 0 _] => true
  | _ => false

/-- The new fields after a successful mutation `o` with the arguments `a` (after the handle). -/
def mutate (o : FOp) (m : Fields) (a : List Val) : Option Fields :=
  match o, a with
  | .set, nv :: vv :: _ =>
    match nameOf nv, valsOf vv with
    | some n, some vs => some (dropName m n ++ vs.map (n, ·))
    | _, _ => none
  | .delete, nv :: _ => (nameOf nv).map (dropName m)
  | .getDel, nv :: _ => (nameOf nv).map (dropName m)
  | .append, nv :: vv :: _ =>
    match nameOf nv, valOf vv with
    | some n, some v => some (m ++ [(n, v)])
    | _, _ => none
  | _, _ => none

/-- A mutating operation. -/
def FOp.mutates : FOp → Bool
  | .set | .delete | .append | .getDel => true
  | _ => false

/-- The next state after the operation `o`. -/
def opNext (o : FOp) (q : FSt) (a : List Val) (r : Option (List Val)) : FSt :=
  match o with
  | .ctor => match handleOf r with
    | some h => (h, some []) :: q
    | none => q
  | .fromList => match handleOf r, a with
    | some h, x :: _ => (h, fieldsOf x) :: q
    | _, _ => q
  | .clone => match handleOf r, a with
    | some h', .u32 h :: _ => (h', (lookup h q).join) :: q
    | _, _ => q
  | o => if o.mutates && isOkAns r then
      match a with
      | .u32 h :: a' =>
        match lookup h q with
        | some (some m) => (h, mutate o m a') :: q
        | _ => q
      | _ => q
    else q

/-- The check of an answer of the operation `o` on the fields `m`. -/
def opCheck (o : FOp) (m : Fields) (a' : List Val) (r : Option (List Val)) : Bool :=
  match o, a', r with
  | _, _, none => true
  | .get, nv :: _, some ans =>
    match nameOf nv with
    | some n => match ans with
      | [x] => valsOf x == some (valsOfName m n)
      | _ => false
    | none => true
  | .has, nv :: _, some ans =>
    match nameOf nv with
    | some n => match ans with
      | [.bool b] => b == !(valsOfName m n).isEmpty
      | _ => false
    | none => true
  | .entries, _, some [x] =>
    match fieldsOf x with
    | some l => decide ((l.map lowE).Perm (m.map lowE))
    | none => false
  | .entries, _, some _ => false
  | .getDel, nv :: _, some [.variant 0 (some x)] =>
    match nameOf nv with
    | some n => valsOf x == some (valsOfName m n)
    | none => true
  | _, _, _ => true

/-- The check of an answer of the operation `o`. -/
def opOk (o : FOp) (q : FSt) (a : List Val) (r : Option (List Val)) : Bool :=
  match a with
  | .u32 h :: a' =>
    match lookup h q with
    | some (some m) => opCheck o m a' r
    | _ => true
  | _ => true

/-- The next state. -/
def fNext (N : FieldsFns) (q : FSt) (e : WEv) : FSt :=
  match e with
  | .imp f a r =>
    match N.op f with
    | some o => opNext o q a r
    | none => q
  | _ => q

/-- The check. -/
def fOk (N : FieldsFns) (q : FSt) (e : WEv) : Bool :=
  match e with
  | .imp f a r =>
    match N.op f with
    | some o => opOk o q a r
    | none => true
  | _ => true

/-- **The `fields` theory** of the slice `N`. -/
def fieldsTh (N : FieldsFns) : Protocol FSt WEv := gated [] (fNext N) (fOk N)

/-! ## The concrete host -/

/-- The state after the answers `p`. -/
def fieldsState (N : FieldsFns) (p : List WEv) : FSt := p.foldl (fNext N) []

/-- The tracked fields of the handle argument, if any. -/
def selfFields (q : FSt) (a : List Val) : Option Fields := (lookup (selfH a) q).join

/-- The answer of the operation `o` from the state `q`; `fresh` is a fresh handle. -/
def opAns (o : FOp) (q : FSt) (fresh : BitVec 32) (a : List Val) : Option (List Val) :=
  let m := (selfFields q a).getD []
  let n := (match a with | _ :: nv :: _ => nameOf nv | _ => none).getD []
  match o with
  | .ctor | .clone => some [.u32 fresh]
  | .fromList =>
    match a with
    | x :: _ => if (fieldsOf x).isSome then some [okV (some (.u32 fresh))]
      else some [errV (some (.variant 0 none))]
    | [] => some [errV (some (.variant 0 none))]
  | .get => some [valsV (valsOfName m n)]
  | .has => some [.bool !(valsOfName m n).isEmpty]
  | .set | .delete | .append => some [okV none]
  | .entries => some [fieldsV m]
  | .getDel => some [okV (some (valsV (valsOfName m n)))]

/-- **The concrete `fields` host** of the slice `N`. -/
def fieldsImpl (N : FieldsFns) : Impl := fun p f a =>
  match N.op f with
  | some o => opAns o (fieldsState N p) (BitVec.ofNat 32 p.length) a
  | none => none

end Silmaril.Wasi.Versions.Net
