module

public import Silmaril.Wasi.Versions.HttpAttr.Defs

@[expose] public section

/-!
# WASI `wasi:http` 0.2: bodies are handed out at most once

Checked against `vendor/wasi/0.2.12/http/types.wit` (the same signatures as
`vendor/wasi/v0.2.9`). Four methods hand out the body of a request or response:
`incoming-request.consume`, `incoming-response.consume` ("Gives the `incoming-body` associated
with this request. Will only return success at most once, and subsequent calls will return
error."), `outgoing-request.body` and `outgoing-response.body` ("Returns success on the first
call: the `outgoing-body` resource for this `outgoing-response` can be retrieved at most once.
Subsequent calls will return error."). All four answer `result<own<…-body>>`.

## The theory `onceTh`

Gated. Its state is the list of handles whose body was handed out. A body method answering
`ok` on a handle in the list is refused; an `ok` answer adds the handle. The drops of the four
resources, the consuming calls (`outgoing-handler.handle`, `response-outparam.set`) and export
calls (which hand in an incoming request) remove the handles they take, so a reused handle
number may hand out a body again. Traps and errors are always allowed.

0.3 has no such method: `request.consume-body` and `response.consume-body` take the resource
itself (`static func(this: request, …)`), so "at most once" is ownership there.

## Concrete host

`onceImpl`: answers `ok` with a fresh handle the first time, `error` afterwards.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- The body methods. -/
def onceTakes : List FnName :=
  [ht2 "[method]incoming-request.consume", ht2 "[method]incoming-response.consume",
    ht2 "[method]outgoing-request.body", ht2 "[method]outgoing-response.body"]

/-- The drops of the four resources. -/
def onceDrops : List FnName :=
  [ht2 "[resource-drop]incoming-request", ht2 "[resource-drop]incoming-response",
    ht2 "[resource-drop]outgoing-request", ht2 "[resource-drop]outgoing-response"]

/-- The consuming calls outside the slice. -/
def onceEats : List FnName := [httpHandle, ht2 "[static]response-outparam.set"]

/-- The functions of the slice. -/
def onceFns : Set FnName := {f | f ∈ onceTakes ∨ f ∈ onceDrops}

/-- The next state. -/
def onceNext (q : List (BitVec 32)) (e : WEv) : List (BitVec 32) :=
  match e with
  | .imp f a r =>
    if f ∈ onceTakes then (if isOkAns r then selfH a :: q else q)
    else if f ∈ onceDrops ∨ f ∈ onceEats then q.filter (· ∉ handlesOf a)
    else q
  | .call _ a => q.filter (· ∉ handlesOf a)
  | _ => q

/-- The check: no second `ok`. -/
def onceOk (q : List (BitVec 32)) (e : WEv) : Bool :=
  match e with
  | .imp f a r => !(f ∈ onceTakes && isOkAns r && selfH a ∈ q)
  | _ => true

/-- **The at-most-once theory of 0.2 bodies.** -/
def onceTh : Protocol (List (BitVec 32)) WEv := gated [] onceNext onceOk

/-- **The concrete host**: `ok` with a fresh handle the first time, `error` afterwards. -/
def onceImpl : Impl := fun p f a =>
  if f ∈ onceTakes then
    if selfH a ∈ p.foldl onceNext [] then some [errV none]
    else some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f ∈ onceDrops then some []
  else none

end Silmaril.Wasi.Versions.Net
