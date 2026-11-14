module

public import Silmaril.Project.WasmP3Rust.Den.Defs
public import Silmaril.Project.WasmP3Rust.TasksP3.Defs

/-!
# A model of `hello`'s core layer, at the canonical ABI boundary

`helloK : CoreExec` is what the core code of `examples/wasip3-rust/hello` does, written as a
transition system over the calls it makes to `canon`-defined functions (indices of `hello.wasm`'s
core function index space, `HelloWiring`):

1. `run` (core function 29, `[async-lift]wasi:cli/run@0.3.0#run`): `stream.new` (7),
   `write-via-stream(r)` (21, a `canon lower`), `waitable-set.new` (3);
2. `stream.write(w, off, 17 - off)` (27, async) of the rest of `Hello, WASI 0.3!\n`, which sits
   at address 0 of memory; `COMPLETED k` advances by `k`; `BLOCKED` joins `w` to the set (4) and
   returns `WAIT`; `DROPPED`, `CANCELLED` or anything else gives up with `error`;
3. the callback (30) on `STREAM_WRITE` for `w` continues as after a completed write; other
   events return `WAIT` again;
4. after the last byte: `stream.drop-writable(w)` (19), `future.read(f)` (26, async, result at
   address 64); `BLOCKED` joins `f` and returns `WAIT`, the callback on `FUTURE_READ` for `f`
   reads the result;
5. `task.return` (22) of `ok` (the future's result) or `error`, and `EXIT`.

This is the behaviour of `write_all` and `write_via_stream(rx).await` in the Rust source, as
`wit-bindgen`'s async runtime drives it, abstracted: the real core code also calls
`context.get/set`, keeps wakers and may poll; whether the core modules of `hello.wasm` refine
`helloK` is the open target `Task.helloCore` (`Silmaril.Project.WasmP3Rust.HelloDen.Thms`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.HelloDen

open Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Project.WasmP3Rust.Den
open Silmaril.Wasm.Component.Async (CopyResult blocked)

/-! ## Where the built-ins are -/

/-- **The wiring of `hello.wasm`**: the lift of `run` and the `canon` definitions `helloK` calls,
in the component's core function index space. -/
structure HelloWiring (S : Spaces) : Prop where
  run : runLift S = some (29, 30)
  streamNew : builtin S 7 = .streamNew
  wvs : builtin S 21 = .wasi ⟨stdoutWrite3, stdoutWrite3_mem⟩
  wsNew : builtin S 3 = .wsNew
  write : builtin S 27 = .streamWrite
  join : builtin S 4 = .join
  dropW : builtin S 19 = .streamDropW
  fread : builtin S 26 = .futureRead
  taskReturn : builtin S 22 = .taskReturn

/-! ## The model -/

/-- The length of the message. -/
def len : Nat := 17

/-- Where `helloK` is. -/
inductive Pc where
  | init | new | wvs | wsNew | write | joinW | dropW | fread | joinF
  | ret (v : Nat)
  /-- Returned `WAIT` blocked on the write / on the future. -/
  | waitW | waitF
  /-- Returned `EXIT`. -/
  | exit
  | trapped
  deriving DecidableEq, Repr

/-- `helloK`'s configuration: the program point, the stream ends, the future, the waitable set,
the bytes written, and the future's result read from memory. -/
structure HConf where
  pc : Pc
  r : Nat := 0
  w : Nat := 0
  f : Nat := 0
  s : Nat := 0
  off : Nat := 0
  res : Nat := 0

/-- The call each program point makes. -/
def callOf (c : HConf) : Option (Nat × List Nat) :=
  match c.pc with
  | .new => some (7, [])
  | .wvs => some (21, [c.r])
  | .wsNew => some (3, [])
  | .write => some (27, [c.w, c.off, len - c.off])
  | .joinW => some (4, [c.w, c.s])
  | .dropW => some (19, [c.w])
  | .fread => some (26, [c.f, 64])
  | .joinF => some (4, [c.f, c.s])
  | .ret v => some (22, [v])
  | _ => none

/-- `k` more bytes were written. -/
def advance (c : HConf) (k : Nat) : HConf :=
  if c.off + k < len then { c with off := c.off + k, pc := .write }
  else { c with off := len, pc := .dropW }

/-- After a write reported the packed copy result `code`. -/
def afterWrite (c : HConf) (code : Nat) : HConf :=
  match copyOf code with
  | some none => { c with pc := .joinW }
  | some (some (.completed, k)) => advance c k
  | _ => { c with pc := .ret 1 }

/-- After a future read reported the packed copy result `code`. -/
def afterRead (c : HConf) (code : Nat) : HConf :=
  match copyOf code with
  | some none => { c with pc := .joinF }
  | some (some (.completed, _)) => { c with pc := .ret c.res }
  | _ => { c with pc := .ret 1 }

/-- The answer of a call. -/
def afterCall (c : HConf) (vs : List Nat) : HConf :=
  match c.pc, vs with
  | .new, [p] => { c with pc := .wvs, r := p % 2 ^ 32, w := p / 2 ^ 32 }
  | .wvs, [fv] => { c with pc := .wsNew, f := fv }
  | .wsNew, [sv] => { c with pc := .write, s := sv }
  | .write, [code] => afterWrite c code
  | .joinW, [] => { c with pc := .waitW }
  | .dropW, [] => { c with pc := .fread }
  | .fread, [code] => afterRead c code
  | .joinF, [] => { c with pc := .waitF }
  | .ret _, [] => { c with pc := .exit }
  | _, _ => { c with pc := .trapped }

/-- A `STREAM_WRITE` event for the blocked write, with payload `p`. -/
def writeEvent (c : HConf) (p : Nat) : HConf :=
  match copyOf p with
  | some (some (.completed, k)) => advance c k
  | _ => { c with pc := .ret 1 }

/-- A `FUTURE_READ` event for the future, with payload `p`. -/
def readEvent (c : HConf) (p : Nat) : HConf :=
  match copyOf p with
  | some (some (.completed, _)) => { c with pc := .ret c.res }
  | _ => { c with pc := .ret 1 }

/-- The callback, on the event `(code, index, payload)`. -/
def onEvent (c : HConf) (ev : List Nat) : HConf :=
  match c.pc, ev with
  | .waitW, [3, i, p] => if i = c.w then writeEvent c p else c
  | .waitF, [4, i, p] => if i = c.f then readEvent c p else c
  | _, _ => c

/-- The packed code `helloK` returns. -/
def retOf (c : HConf) : Option Nat :=
  match c.pc with
  | .waitW | .waitF => some (2 + 16 * c.s)
  | .exit => some 0
  | _ => none

/-- **`hello`'s core layer, as a model.** -/
def helloK : CoreExec where
  Conf := HConf
  init := { pc := .init }
  enter c k args :=
    if k = 29 ∧ c.pc = .init ∧ args = [] then some { c with pc := .new }
    else if k = 30 ∧ (c.pc = .waitW ∨ c.pc = .waitF) then some (onEvent c args)
    else none
  step _ _ := False
  callOut c k args := callOf c = some (k, args)
  resume := afterCall
  ret c vs := ∃ p, retOf c = some p ∧ vs = [p]
  trap c := c.pc = .trapped
  load _ p n := some ((helloMsg.drop p).take n)
  store c _ bs := some { c with res := (bs.head?.map BitVec.toNat).getD 0 }

end Silmaril.Project.WasmP3Rust.HelloDen

end
