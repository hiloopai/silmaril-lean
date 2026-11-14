module

public import Silmaril.Project.WasmP3Rust.Den.Defs

/-!
# `den` with data-carrying events, stdin reads and `wasi:cli/environment`

`Silmaril.Project.WasmP3Rust.Den` denotes async components in the WASI 0.3 slice `p3World`, whose
encoding of `waitable-set.wait` answers carries no data: a `stream.read` that blocks and
completes through an event stores nothing, so no faithful model of `cat` (which reads stdin)
can meet `catG1` there. This module extends the world and the encoding, and re-states `den`
over them (`DenX.den`); `Den` is left as it is.

## The world `p3xWorld`

`p3World`'s imports and `wasi:cli/environment@0.3.2` `get-arguments: func() -> list<string>`
(`getArgs3`, `vendor/wasi/0.3.2/cli/environment.wit`; the examples import the same function
at `@0.3.0`). The export is `run`.

## The encoding of events

`waitable-set.wait(s)` answers `[code, index, payload]` as before, or **`[code, index, payload,
data]`**, where `data` is what the completed copy delivered:

* `STREAM_READ` (`code = 2`) on a readable end with a blocked `stream.read`: `data` is the
  `list<u8>` of the items copied (`bytesV`); `payload` is the packed copy result
  (`result | count << 4`) as in `definitions.py` (`StreamEvent`, L1530–1560 at `d095e2f`);
* `FUTURE_READ` (`code = 4`) on a future with a blocked `future.read`: `data` is the value read.

`den` keeps the buffer of each blocked read (`DConf.pend`: event code, handle and pointer, from
the `stream.read` or `future.read` that answered `BLOCKED`) and, when the event of that code
arrives for that handle, stores the
data there before the callback (or the sync `waitable-set.wait` built-in) sees the event, as the
Canonical ABI's `ReadableStreamGuestEnd`/`CopyState` write into the reader's buffer when the
copy completes. A theory that wants the data must require the 4-element form
(`Silmaril.Project.WasmP3Rust.TasksX.waitTh3x` does, for stream reads).

## Lowering `get-arguments`

A sync `canon lower` of `get-arguments` (options `memory`, `realloc`, `string-encoding=utf8`)
answers `[list]` with `list = .record vs` (each `v` a `string`, `.record` of `.char`s). `den`
lowers it as the Canonical ABI's `store_list` / `store_string` do (`definitions.py`
L1700–1790 at `d095e2f`): `realloc` an array of `8 n` bytes (align 4), then per element
`realloc` the string's UTF-8 bytes (align 1), store them, store `(ptr, len)` at
`array + 8 i`; finally store `(array, n)` at the return pointer (the last argument).
`realloc` is a call into core code; here it is the core layer's `alloc` (`CoreExecX`),
an abstraction of that call (stated, as `CoreExec` abstracts the rest of core execution).

## Lowers of `stdin` and `stdout`

Typed by the function, unlike `Den`: `read-via-stream()` is called with no arguments (the
core function's only parameter is the return pointer) and must answer `[record [r, f]]`, which
is stored at the return pointer; `write-via-stream(r)` must answer one `u32`. Other answers
trap.

## Everything else

As in `Silmaril.Project.WasmP3Rust.Den` (index spaces, the callback driver, the other
built-ins, traps outside the fragment, one `run` call from `init`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.DenX

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.BinaryP3 (Ast Canon)
open Silmaril.Wasm.Component.Binary (CanonOpt)
open Silmaril.Wasm.Component.Async.Cabi (unpackCallback)
open Silmaril.Project.WasmP3Rust.Den (Spaces spaces runLift cbOf Builtin builtin CoreExec le32
  packEnds Mode runResult)

/-! ## The world -/

/-- `wasi:cli/environment@0.3.2.get-arguments`. -/
def getArgs3 : FnName := ⟨"wasi:cli/environment@0.3.2", "get-arguments"⟩

/-- **The WASI 0.3 slice with `wasi:cli/environment`'s `get-arguments`.** -/
def p3xWorld : World := ⟨p3World.imports ∪ {getArgs3}, {run3}⟩

/-- An import of `p3xWorld`. -/
abbrev XOp : Type := (nsig p3xWorld.imports).Op

/-- An import of `p3World` as one of `p3xWorld`. -/
def up (m : P3Op) : XOp := (⟨m.1.1, Or.inl m.1.2⟩, m.2)

/-- `get-arguments()`. -/
def opArgs : XOp := (⟨getArgs3, Or.inr rfl⟩, [])

/-- The event code `STREAM_READ`. -/
def evStreamRead : Nat := 2

/-- The event code `FUTURE_READ`. -/
def evFutureRead : Nat := 4

/-! ## Strings -/

/-- The UTF-8 bytes of a character. -/
def charBytes (c : Char) : List (BitVec 8) :=
  (String.utf8EncodeChar c).map fun b => BitVec.ofNat 8 b.toNat

/-- The UTF-8 bytes of a `string` value (`.record` of `.char`s; other items contribute
nothing). -/
def strBytes : Val → List (BitVec 8)
  | .record cs => cs.flatMap fun
    | .char c => charBytes c
    | _ => []
  | _ => []

/-- The byte strings of a `list<string>` answer. -/
def argsOf : Option (List Val) → Option (List (List (BitVec 8)))
  | some [.record vs] => some (vs.map strBytes)
  | _ => none

/-! ## Core execution with `realloc` -/

/-- **A semantics of the core layer, with `realloc`.** `alloc x size align` is the call
`realloc(0, 0, align, size)` into the core layer: the new configuration and the pointer
(`none`: a trap). -/
structure CoreExecX extends CoreExec where
  alloc : Conf → Nat → Nat → Option (Conf × Nat)

/-! ## Built-ins -/

/-- `canon lower` of `get-arguments` through an imported instance
`wasi:cli/environment@0.3.0`, sync. -/
def isGetArgs (S : Spaces) (k : Nat) : Bool :=
  match S.coreFns[k]? with
  | some (.canon (.lower f os)) =>
    if CanonOpt.async ∈ os then false
    else match S.fns[f]? with
      | some (.alias i n) =>
        match S.insts[i]? with
        | some (.imported iface) =>
          decide (iface = "wasi:cli/environment@0.3.0") && decide (n = "get-arguments")
        | _ => false
      | _ => false
  | _ => false

/-- What a core function defined by `canon` does in `DenX.den`. -/
inductive BuiltinX where
  /-- As in `Den`. -/
  | base (b : Builtin)
  /-- The sync lower of `get-arguments`. -/
  | getArgs
  deriving DecidableEq

/-- The built-in of the core function `k`. -/
def builtinX (S : Spaces) (k : Nat) : BuiltinX :=
  if isGetArgs S k then .getArgs else .base (builtin S k)

/-! ## Configurations -/

variable (K : CoreExecX)

/-- A configuration of `den`: as in `Den`, and the buffers of the blocked reads (event code
`2` or `4`, handle, pointer). -/
structure DConf where
  core : K.Conf
  mode : Mode := .run
  ctx : Nat × Nat := (0, 0)
  result : Option (List Nat) := none
  pend : List (Nat × Nat × Nat) := []

variable {K}

/-- Trap. -/
def DConf.trapped (d : DConf K) : DConf K := { d with mode := .trap }

/-- Resume core code with flat results. -/
def DConf.resume (d : DConf K) (vs : List Nat) : DConf K := { d with core := K.resume d.core vs }

/-- Store bytes into the core layer's memory (`none`: out of bounds). -/
def DConf.store (d : DConf K) (p : Nat) (bs : List (BitVec 8)) : Option (DConf K) :=
  (K.store d.core p bs).map fun y => { d with core := y }

/-- Record a blocked read of `h` into the buffer `p`, completed by events of code `c`. -/
def DConf.block (d : DConf K) (c h p : Nat) : DConf K := { d with pend := (c, h, p) :: d.pend }

/-- The byte of a `result<_, _>` value as `future.read` stores it. -/
def discByte (v : Val) : BitVec 8 := if v matches .variant 0 none then 0 else 1

/-- An event of `waitable-set.wait`: `(code, index, payload, data)`. -/
def evOf : Option (List Val) → Option (Nat × Nat × Nat × Option Val)
  | some [cv, iv, pv] =>
    match natOf cv, natOf iv, natOf pv with
    | some c, some i, some q => some (c, i, q, none)
    | _, _, _ => none
  | some [cv, iv, pv, v] =>
    match natOf cv, natOf iv, natOf pv with
    | some c, some i, some q => some (c, i, q, some v)
    | _, _, _ => none
  | _ => none

/-- **Deliver the data of a completed read** to the buffer of the blocked read of `i`. -/
def deliver (d : DConf K) (c i : Nat) (v : Option Val) : Option (DConf K) :=
  if c = evStreamRead ∨ c = evFutureRead then
    match d.pend.find? (fun e => e.1 = c ∧ e.2.1 = i) with
    | some (_, _, p) =>
      let d' : DConf K := { d with pend := d.pend.filter (fun e => ¬ (e.1 = c ∧ e.2.1 = i)) }
      match v with
      | some v => d'.store p (if c = evStreamRead then bytesOf v else [discByte v])
      | none => some d'
    | none => some d
  else some d

/-! ## Lowering `list<string>` -/

variable (K)

/-- Store the strings `ss` as the elements `i, i + 1, …` of the array at `arr`. -/
def lowerStrs (arr : Nat) : Nat → List (List (BitVec 8)) → K.Conf → Option K.Conf
  | _, [], x => some x
  | i, s :: ss, x =>
    (K.alloc x s.length 1).bind fun (x, p) =>
      (K.store x p s).bind fun x =>
        (K.store x (arr + 8 * i) (le32 p ++ le32 s.length)).bind fun x =>
          lowerStrs arr (i + 1) ss x

/-- **Lower a `list<string>`** to the return pointer `ret`. -/
def lowerArgs (x : K.Conf) (ret : Nat) (ss : List (List (BitVec 8))) : Option K.Conf :=
  (K.alloc x (8 * ss.length) 4).bind fun (x, arr) =>
    (lowerStrs K arr 0 ss x).bind fun x => K.store x ret (le32 arr ++ le32 ss.length)

variable {K}

/-! ## Forwarded built-ins -/

/-- **A forwarded built-in**: the world import it calls, and how the answer resumes
(`none`: a trap). -/
def forward (B : BuiltinX) (args : List Nat) (d : DConf K) :
    Option (XOp × (Option (List Val) → Option (DConf K))) :=
  match B, args with
  | .base .streamNew, [] => some (up Den.opNew, fun
      | some [rv, wv] => match natOf rv, natOf wv with
        | some r, some w => some (d.resume [packEnds r w])
        | _, _ => none
      | _ => none)
  | .base .streamWrite, [w, p, n] =>
    (K.load d.core p n).map fun bs => (up (Den.opWrite w bs), fun
      | some [pv] => (natOf pv).map fun c => d.resume [c]
      | _ => none)
  | .base .streamRead, [r, p, n] => some (up (Den.opRead r n), fun
      | some [pv, items] =>
        match natOf pv with
        | some c => (d.store p (bytesOf items)).map fun d' =>
            (if c = Silmaril.Wasm.Component.Async.blocked then d'.block evStreamRead r p else d').resume [c]
        | none => none
      | _ => none)
  | .base .streamDropR, [r] => some (up (Den.opDropR r), fun
      | some [] => some (d.resume [])
      | _ => none)
  | .base .streamDropW, [w] => some (up (Den.opDropW w), fun
      | some [] => some (d.resume [])
      | _ => none)
  | .base .futureRead, [f, p] => some (up (Den.opFRead f), fun
      | some [pv] => (natOf pv).map fun c =>
          (if c = Silmaril.Wasm.Component.Async.blocked then d.block evFutureRead f p else d).resume [c]
      | some [pv, v] =>
        match natOf pv with
        | some c => (d.store p [discByte v]).map fun d' => d'.resume [c]
        | none => none
      | _ => none)
  | .base .futureDropR, [f] => some (up (Den.opFDropR f), fun
      | some [] => some (d.resume [])
      | _ => none)
  | .base .wsNew, [] => some (up Den.opWsNew, fun
      | some [sv] => (natOf sv).map fun s => d.resume [s]
      | _ => none)
  | .base .join, [w, s] => some (up (Den.opJoin w s), fun
      | some [] => some (d.resume [])
      | _ => none)
  | .base .wsWait, [s, p] => some (up (Den.opWait s), fun n =>
      match evOf n with
      | some (c, i, q, v) =>
        (deliver d c i v).bind fun d' => (d'.store p (le32 i ++ le32 q)).map fun d'' => d''.resume [c]
      | none => none)
  | .base (.wasi f), args =>
    if f.1 = stdinRead3 then
      match args with
      | [p] => some ((⟨f.1, Or.inl f.2⟩, []), fun
          | some [.record [a, b]] =>
            match natOf a, natOf b with
            | some a', some b' => (d.store p (le32 a' ++ le32 b')).map fun d' => d'.resume []
            | _, _ => none
          | _ => none)
      | _ => none
    else if f.1 = stdoutWrite3 then
      match args with
      | [r] => some ((⟨f.1, Or.inl f.2⟩, [natV r]), fun
          | some [v] => (natOf v).map fun n => d.resume [n]
          | _ => none)
      | _ => none
    else none
  | .getArgs, [ret] => some (opArgs, fun n =>
      match argsOf n with
      | some ss => (lowerArgs K d.core ret ss).map fun y => { d with core := K.resume y [] }
      | none => none)
  | _, _ => none

/-- A built-in local to the task (`some`), with its effect (`none` inside: a trap). -/
def internal (B : BuiltinX) (args : List Nat) (d : DConf K) : Option (Option (DConf K)) :=
  match B, args with
  | .base (.ctxGet 0), [] => some (some (d.resume [d.ctx.1]))
  | .base (.ctxGet 1), [] => some (some (d.resume [d.ctx.2]))
  | .base (.ctxSet 0), [v] => some (some { d.resume [] with ctx := (v, d.ctx.2) })
  | .base (.ctxSet 1), [v] => some (some { d.resume [] with ctx := (d.ctx.1, v) })
  | .base .taskReturn, vs =>
    match d.result with
    | none => some (some { d.resume [] with result := some vs })
    | some _ => some none
  | .base .wsDrop, [_] => some (some (d.resume []))
  | _, _ => none

/-! ## The callback driver -/

/-- Re-enter the callback `cb` with an event. -/
def reenter (cb : Nat) (d : DConf K) (ev : List Nat) : DConf K :=
  match K.enter d.core cb ev with
  | some y => { d with core := y, mode := .run }
  | none => d.trapped

/-- How the answer to a forwarded built-in resumes core code. -/
def contWith (d : DConf K) (kont : Option (List Val) → Option (DConf K)) (n : Option (List Val)) :
    DConf K :=
  match kont n with
  | some d' => d'
  | none => d.trapped

/-- After `waitable-set.wait` answered: deliver the data, re-enter the callback. -/
def afterWait (cb : Nat) (d : DConf K) (n : Option (List Val)) : DConf K :=
  match evOf n with
  | some (c, i, q, v) =>
    match deliver d c i v with
    | some d' => reenter cb d' [c, i, q]
    | none => d.trapped
  | none => d.trapped

variable (K)

/-- Silent steps (as in `Den.DStep`). -/
inductive DStep (S : Spaces) (cb : Nat) : DConf K → DConf K → Prop
  | core {d : DConf K} {y : K.Conf} : d.mode = .run → K.step d.core y →
      DStep S cb d { d with core := y }
  | internal {d d' : DConf K} {k : Nat} {args : List Nat} : d.mode = .run →
      K.callOut d.core k args → internal (builtinX S k) args d = some (some d') →
      DStep S cb d d'
  | bad {d : DConf K} {k : Nat} {args : List Nat} : d.mode = .run → K.callOut d.core k args →
      internal (builtinX S k) args d = some none ∨
        (internal (builtinX S k) args d = none ∧ forward (builtinX S k) args d = none) →
      DStep S cb d d.trapped
  | yield {d : DConf K} {p : Nat} {s : Nat} : d.mode = .run → K.ret d.core [p] →
      unpackCallback p = .ok (.yield, s) → DStep S cb d (reenter cb d [0, 0, 0])
  | wait {d : DConf K} {p s : Nat} : d.mode = .run → K.ret d.core [p] →
      unpackCallback p = .ok (.wait, s) → DStep S cb d { d with mode := .wait s }
  | exit {d : DConf K} {p s : Nat} : d.mode = .run → K.ret d.core [p] →
      unpackCallback p = .ok (.exit, s) → DStep S cb d { d with mode := .exit }
  | badRet {d : DConf K} {vs : List Nat} : d.mode = .run → K.ret d.core vs →
      (∀ p, vs = [p] → ∃ e, unpackCallback p = .error e) → DStep S cb d d.trapped
  | trap {d : DConf K} : d.mode = .run → K.trap d.core → DStep S cb d d.trapped

/-- Calls to the world. -/
inductive DCall (S : Spaces) (cb : Nat) :
    DConf K → (m : XOp) → (Option (List Val) → DConf K) → Prop
  | fwd {d : DConf K} {k : Nat} {args : List Nat} {m : XOp}
      {kont : Option (List Val) → Option (DConf K)} : d.mode = .run → K.callOut d.core k args →
      internal (builtinX S k) args d = none → forward (builtinX S k) args d = some (m, kont) →
      DCall S cb d m (contWith d kont)
  | wait {d : DConf K} {s : Nat} : d.mode = .wait s →
      DCall S cb d (up (Den.opWait s)) (afterWait cb d)

/-- Returns. -/
inductive DDone : DConf K → Option (List Val) → Prop
  | exit {d : DConf K} : d.mode = .exit → DDone d (runResult d.result)
  | trap {d : DConf K} : d.mode = .trap → DDone d none

/-- The first configuration of a `run` call. -/
def start (S : Spaces) : DConf K :=
  match runLift S with
  | some (cf, _) =>
    match K.enter K.init cf [] with
    | some x => { core := x }
    | none => { core := K.init, mode := .trap }
  | none => { core := K.init, mode := .trap }

/-- **The reduction semantics**, question by question. -/
def red (c : Ast) : Reduction (nsig p3xWorld.imports) (nsig p3xWorld.exports) where
  Conf _ := DConf K
  start _ := start K (spaces c)
  step := DStep K (spaces c) (cbOf (spaces c))
  call := DCall K (spaces c) (cbOf (spaces c))
  done := DDone K

/-- The denotation with the core layer semantics `K`. -/
def denWith (c : Ast) : p3xWorld.Model := Strategy.ofLTS (red K c).toLTS

/-- **The denotation of async components in `p3xWorld`**, given a core layer semantics `Ks c`
of each component `c`. -/
def den (Ks : Ast → CoreExecX) (c : Ast) : p3xWorld.Model := denWith (Ks c) c

end Silmaril.Project.WasmP3Rust.DenX

end
