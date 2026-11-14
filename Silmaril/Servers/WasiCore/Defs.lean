module

public import Silmaril.Servers.WasiHttp.Defs
public import Silmaril.Wasm.Modules

@[expose] public section

/-!
# Core modules of `wasi:http` components, read as bodies

A `wasi:http` proxy component built by `wasm-tools component new` from one core module is that
module with canonical-ABI adapters: each import of the core module is `canon lower` of a WIT
function (reading its string and list arguments from linear memory and writing its results
there), and the export `handle` is `canon lift` of a core function. This module gives such a core
module (`Silmaril.Wasm.Module`, as the WAT frontend `wat3!` or a decoder produces it) a
denotation as a body over the proxy imports (`coreBody m fuel`), so that the statements of
`Silmaril.Servers.WasiHttp` and `Silmaril.Servers.WasiExamples` can be made about the module's
code.

**The core fragment** (`run`): a small big-step interpreter in continuation-passing style,
whose import calls are the moves of the body (`Silmaril.Games.Prog.call`). It covers what the
example components use: `i32`/`i64` constants, locals, globals, the integer arithmetic,
comparison and test operators (`binop`, `relop`; not signed division, remainder or rotations),
`i32`/`i64` loads and stores (packed or not) on memory `0`, `memory.size`, `memory.grow`
(which succeeds up to the maximum, as `wasmtime` does), `memory.copy`, `drop`, `nop`,
`unreachable`, `block`/`loop`/`if` with an empty or single-value block type, `br`, `br_if`,
`return` and direct `call`s. Anything else traps (`trap`): such a module is outside the
fragment and the denotation says nothing about it. Each instruction and call consumes one
unit of `fuel`; running out traps, so `coreBody m fuel` describes the runs of at most `fuel`
steps.

**The canonical ABI of the imports** (`glue`): for each import of the slice, by its versioned
core name (`wasi:http/types@0.2.12`, `wasi:io/streams@0.2.12`), the flat parameters are lifted
to the WIT arguments of the call (`liftBytes`, `liftStr`: lists and strings read from memory;
strings must be ASCII, other strings are outside the fragment) and the answer is lowered back
(`Low`): direct results as flat values, larger results through the return pointer (the last
flat parameter), with the layouts of the canonical ABI (`result<own<T>>`: discriminant byte at
`0`, handle at `4`; `result<_, header-error>`: discriminant at `0`, case at `1`;
`result<_, stream-error>`: discriminant at `0`, case at `4`, handle at `8`;
`result<list<u8>, stream-error>` and `option<string>`: pointer at `4`, length at `8`). Lists and
strings answered by the host are copied into memory allocated by the module's `cabi_realloc`
export (`Low.alloc`). Results the module only stores are lowered without inspecting the answer
(`Wr.part`, `discOf`, `hOf`): on answers of the WIT result type these are the canonical bytes
and values; on other answers, which a component runtime never gives and `RunsTy` excludes, they
are some bytes. Handles through the return pointer, strings and lists trap on an answer of
another shape. **Simplifications**: the payload of an `error-code` (from `outgoing-body.finish`)
is not written, only the discriminant; `response-outparam.set` with an error response is outside
the fragment; the flat parameter counts are the canonical ones and are not checked against the
module's declared import types.

**Memory** is the list of writes since a memory of zeros (`Wr`, newest first; `byteAt` reads a
byte), so that a 32-bit value stored and loaded back at the same address is that value
(`wordAt`), not its reassembled bytes: a proof can follow a host's handle through memory without
arithmetic.

**Instances.** `freshInst m`: the globals (initialized by constants), one memory of its minimum
size, and the active data segments written into it. Each call of `handle` runs on a fresh
instance (as `wasmtime serve` runs a `wasi:http` 0.2 component); its arguments are lowered by
`reqOf` and `outOf`, as the bodies read them.

**Typed hosts.** `AnsTy f n`: the answer `n` of the import `f` has the WIT result type of `f`
(`TyEv` on events). A component runtime only gives typed answers. `Sim AnsTy p p'`: the program
`p` makes the import calls of `p'`, and after every typed answer continues as `p'` does (the
same result at the end). `RunsTy σ h`: every play of `σ` whose answers are typed is a play of the
body `h`. `wasiServerTy σ`: the component read as a server over typed hosts.

That `run` and `glue` agree with Core 3.0 (`Silmaril.Wasm.Game`) and the reference canonical ABI
(`Silmaril.Wasm.Component.Reference.Canon`) on modules of the fragment is not proved here.

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiCore

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.Calls
open Silmaril.Wasm (Module Instr IntType IntBinOp IntRelOp IntTestOp BlockType ValType PackSize
  Signedness MemArg)
open Silmaril.Wasm.Component (Val)

/-! ## Typed answers -/

/-- **The answer `n` of the import `f` has the WIT result type of `f`** (`wasi:http` 0.2.12;
`error-code` payloads are not constrained; functions no component here calls are not
constrained). -/
def AnsTy (f : FnName) (n : Option (List Val)) : Prop :=
  if f = newFields ∨ f = newResp ∨ f = reqHeaders then ∃ h, n = some [.u32 h]
  else if f = fieldsAppend then
    n = some [okV none] ∨ ∃ k : Nat, k < 3 ∧ n = some [errV (some (.variant k none))]
  else if f = setStatus then n = some [okV none] ∨ n = some [errV none]
  else if f = respBody ∨ f = bodyWrite ∨ f = reqConsume ∨ f = inStream then
    (∃ h, n = some [okV (some (.u32 h))]) ∨ n = some [errV none]
  else if f = outSet ∨ f = streamDrop then n = some []
  else if f = bodyFinish then n = some [okV none] ∨ ∃ e, n = some [errV e]
  else if f = streamWrite then
    n = some [okV none] ∨ n = some [errV (some (.variant 1 none))] ∨
      ∃ e, n = some [errV (some (.variant 0 (some (.u32 e))))]
  else if f = inRead then
    (∃ bs, n = some [okV (some (bytesV bs))]) ∨ n = some [errV (some (.variant 1 none))] ∨
      ∃ e, n = some [errV (some (.variant 0 (some (.u32 e))))]
  else if f = reqPath then
    n = some [.variant 0 none] ∨ ∃ cs : List Char, n = some [.variant 1 (some (.record (cs.map .char)))]
  else if f = fieldsGet then ∃ vs : List (List (BitVec 8)), n = some [.record (vs.map bytesV)]
  else True

/-- An event whose answer, if any, is typed. -/
def TyEv : WEv → Prop
  | .imp f _ n => AnsTy f n
  | _ => True

/-- **A proxy component read as an HTTP server over typed hosts.** -/
def wasiServerTy {X : Set FnName} (σ : Strategy (nsig proxyImports) (nsig X)) :
    Exchange.Model httpIface :=
  model TyEv answered Obs σ

/-- The same, reading request bodies. -/
def wasiServerTyB {X : Set FnName} (σ : Strategy (nsig proxyImports) (nsig X)) :
    Exchange.Model httpIface :=
  model TyEv answered ObsB σ

/-- **`σ` runs the body `h` over typed hosts**: every play of `σ` whose answers are typed is a
play of `ofBody h`. -/
def RunsTy {X : Set FnName} (σ : Strategy (nsig proxyImports) (nsig X))
    (h : Body proxyImports X) : Prop :=
  ∀ s ∈ σ, (∀ e ∈ wtrace s, TyEv e) → s ∈ ofBody h

/-- **`p` simulates `p'` on the answers `T` allows**: the same import calls, and after each
allowed answer the same continuation, up to the same result. -/
inductive Sim {I : Set FnName} (T : FnName → Option (List Val) → Prop) : BProg I → BProg I → Prop
  | pure (r : Option (List Val)) : Sim T (.pure r) (.pure r)
  | call (m : (nsig I).Op) (k k' : Option (List Val) → BProg I)
      (h : ∀ n, T m.1.1 n → Sim T (k n) (k' n)) : Sim T (.call m k) (.call m k')

/-- The next import call of a program. -/
def next {I : Set FnName} : BProg I → Option (nsig I).Op
  | .pure _ => none
  | .call m _ => some m

/-- The continuation of a program after an answer. -/
def cont {I : Set FnName} : BProg I → Option (List Val) → BProg I
  | .pure r => fun _ => .pure r
  | .call _ k => k

/-! ## Values and instances -/

/-- A core value of the fragment. -/
inductive CVal where
  | i32 (v : BitVec 32)
  | i64 (v : BitVec 64)

/-- A write to linear memory. -/
inductive Wr where
  /-- The bytes `bs` at `a`. -/
  | bytes (a : Nat) (bs : List UInt8)
  /-- A 32-bit value at `a`, little-endian. -/
  | word (a : Nat) (v : BitVec 32)
  /-- The `n` low bytes of `v` at `a`, little-endian. -/
  | num (a n v : Nat)
  /-- `memory.copy`: the `n` bytes at `s`, as they were, at `d`. -/
  | copy (d s n : Nat)
  /-- In `[a, a + n)`, the byte `f i` at `a + i` where it is `some`; the other bytes keep their
  value (a lowered result whose layout depends on the answer). -/
  | part (a n : Nat) (f : Nat → Option UInt8)

/-- The range written by a write. -/
def Wr.range : Wr → Nat × Nat
  | .bytes a bs => (a, bs.length)
  | .word a _ => (a, 4)
  | .num a n _ => (a, n)
  | .copy d _ n => (d, n)
  | .part a n _ => (a, n)

/-- **The byte at `x`** after the writes `l` (newest first) to a memory of zeros. -/
def byteAt : List Wr → Nat → UInt8
  | [], _ => 0
  | .bytes a bs :: l, x => if a ≤ x ∧ x < a + bs.length then bs.getD (x - a) 0 else byteAt l x
  | .word a v :: l, x =>
    if a ≤ x ∧ x < a + 4 then (v.toNat / 256 ^ (x - a) % 256).toUInt8 else byteAt l x
  | .num a n v :: l, x => if a ≤ x ∧ x < a + n then (v / 256 ^ (x - a) % 256).toUInt8 else byteAt l x
  | .copy d s n :: l, x => if d ≤ x ∧ x < d + n then byteAt l (s + (x - d)) else byteAt l x
  | .part a n f :: l, x => if a ≤ x ∧ x < a + n then (f (x - a)).getD (byteAt l x) else byteAt l x

/-- The value of a 32-bit write at exactly `a` that no later write overlaps, if any (then the
four bytes at `a` are that value's: `wordAt` is a shortcut of `byteAt`). -/
def wordAt : List Wr → Nat → Option (BitVec 32)
  | [], _ => none
  | w :: l, a =>
    match w with
    | .word a' v => if a' = a then some v else if a' < a + 4 ∧ a < a' + 4 then none else wordAt l a
    | w => if w.range.1 < a + 4 ∧ a < w.range.1 + w.range.2 then none else wordAt l a

/-- The state of an instance: linear memory `0` (the writes since a memory of zeros, newest
first, and its size in pages) and the globals. -/
structure Inst where
  /-- The writes to the memory, newest first. -/
  log : List Wr
  /-- The size of the memory, in pages of 65536 bytes. -/
  pages : Nat
  /-- The values of the globals. -/
  globals : List CVal

/-- The byte at `x`. -/
def Inst.mem (c : Inst) (x : Nat) : UInt8 := byteAt c.log x

/-- A frame: the locals and the operand stack (top first). -/
structure Frame where
  /-- The locals (parameters first). -/
  locals : List CVal
  /-- The operand stack, top first. -/
  stack : List CVal

/-- Programs over the proxy imports. -/
abbrev P : Type := BProg proxyImports

/-- A continuation. -/
abbrev K : Type := Inst → Frame → P

/-- A trap: the call ends without results. -/
def trap : P := .pure none

/-- The `n` bytes at `a`, little-endian, as a number. -/
def readN (m : Nat → UInt8) : Nat → Nat → Nat
  | _, 0 => 0
  | a, n + 1 => (m a).toNat + 256 * readN m (a + 1) n

/-- `[a, a + n)` lies in the memory. -/
def Inst.fits (c : Inst) (a n : Nat) : Bool := a + n ≤ c.pages * 65536

/-- Add a write, in bounds. -/
def Inst.put (c : Inst) (w : Wr) : Option Inst :=
  if c.fits w.range.1 w.range.2 then some { c with log := w :: c.log } else none

/-- Write the `n` low bytes of `v` at `a`, in bounds. -/
def Inst.write (c : Inst) (a n v : Nat) : Option Inst := c.put (.num a n v)

/-! ## Arithmetic -/

/-- The integer binary operators of the fragment. -/
def binop {w : Nat} : IntBinOp → BitVec w → BitVec w → Option (BitVec w)
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .and, a, b => some (a &&& b)
  | .or, a, b => some (a ||| b)
  | .xor, a, b => some (a ^^^ b)
  | .shl, a, b => some (a <<< (b.toNat % w))
  | .shr .unsigned, a, b => some (a >>> (b.toNat % w))
  | .shr .signed, a, b => some (a.sshiftRight (b.toNat % w))
  | .div .unsigned, a, b => if b = 0 then none else some (a / b)
  | .rem .unsigned, a, b => if b = 0 then none else some (a % b)
  | _, _, _ => none

/-- The integer comparisons. -/
def relop {w : Nat} : IntRelOp → BitVec w → BitVec w → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt .unsigned, a, b => a.ult b
  | .lt .signed, a, b => a.slt b
  | .gt .unsigned, a, b => b.ult a
  | .gt .signed, a, b => b.slt a
  | .le .unsigned, a, b => a.ule b
  | .le .signed, a, b => a.sle b
  | .ge .unsigned, a, b => b.ule a
  | .ge .signed, a, b => b.sle a

/-- A Boolean as an `i32`. -/
def ofBool (b : Bool) : CVal := .i32 (if b then 1 else 0)

/-- The width in bytes of an access. -/
def accessBytes (t : IntType) : Option PackSize → Nat
  | some p => p.width / 8
  | none => t.width / 8

/-- A loaded value. -/
def loaded (t : IntType) (packed : Option (PackSize × Signedness)) (raw : Nat) : CVal :=
  match t, packed with
  | .i32, some (p, .signed) => .i32 ((BitVec.ofNat p.width raw).signExtend 32)
  | .i64, some (p, .signed) => .i64 ((BitVec.ofNat p.width raw).signExtend 64)
  | .i32, _ => .i32 (BitVec.ofNat 32 raw)
  | .i64, _ => .i64 (BitVec.ofNat 64 raw)

/-- The default value of a local. -/
def zeroOf : ValType → CVal
  | .num (.int .i64) => .i64 0
  | _ => .i32 0

/-! ## The module -/

/-- The function imports, by core name. -/
def funcImports (m : Module) : List (String × String) :=
  m.imports.filterMap fun i => match i.type with
    | .func _ => some (i.moduleName, i.name)
    | _ => none

/-- The number of parameters and results of a type. -/
def funcArity (m : Module) (t : Silmaril.Wasm.TypeIdx) : Option (Nat × Nat) :=
  match m.typeDefinitions[t.toNat]? with
  | some ⟨_, _, .func ft⟩ => some (ft.params.length, ft.results.length)
  | _ => none

/-- The arity of a block type: its results (its parameters are `0` in the fragment). -/
def blockArity : BlockType → Option Nat
  | .empty => some 0
  | .value _ => some 1
  | .typeIdx _ => none

/-- The function exported under `name`. -/
def exportFunc (m : Module) (name : String) : Option Nat :=
  (m.exports.find? (·.name == name)).bind fun e => match e.index with
    | .func i => some i.toNat
    | _ => none

/-- The value of a constant initializer. -/
def constOf : List Instr → Option CVal
  | [.intConst .i32 v] => some (.i32 v)
  | [.intConst .i64 v] => some (.i64 v)
  | _ => none

/-- Write the active data segments. -/
def initData (c : Inst) : List Silmaril.Wasm.Data → Option Inst
  | [] => some c
  | d :: ds =>
    match d.mode with
    | .active ⟨⟨0, _⟩⟩ off =>
      match constOf off with
      | some (.i32 a) =>
        match c.put (.bytes a.toNat d.bytes.data.toList) with
        | some c => initData c ds
        | none => none
      | _ => none
    | .passive => initData c ds
    | _ => none

/-- **A fresh instance** of the module (no start function, at most one memory). -/
def freshInst (m : Module) : Option Inst :=
  if m.start.isSome then none else
  match m.globals.mapM fun g => constOf g.init with
  | none => none
  | some gs =>
    match m.memories with
    | [] => initData ⟨[], 0, gs⟩ m.data
    | [mt] => initData ⟨[], mt.limits.min.val, gs⟩ m.data
    | _ => none

/-! ## The canonical ABI of the imports -/

/-- The bytes `[p, p + n)` of the memory. -/
def liftBytes (c : Inst) (p n : Nat) : Option (List (BitVec 8)) :=
  if c.fits p n then some ((List.range n).map fun i => (c.mem (p + i)).toBitVec) else none

/-- An ASCII string `[p, p + n)` of the memory (other strings are outside the fragment). -/
def liftStr (c : Inst) (p n : Nat) : Option Val :=
  match liftBytes c p n with
  | some bs =>
    if bs.all (·.toNat < 128) then some (.record (bs.map fun b => .char (Char.ofNat b.toNat)))
    else none
  | none => none

/-- How an answer is lowered: done, with the new instance and the flat results, or after
allocating `len` bytes aligned to `align` with the module's `cabi_realloc`. -/
inductive Low where
  | done (c : Inst) (res : List CVal)
  | alloc (c : Inst) (align len : Nat) (k : BitVec 32 → Inst → Option Low)

/-- Write a byte at `a`, then go on. -/
def Low.wr8 (c : Inst) (a : Nat) (v : Nat) (k : Inst → Option Low) : Option Low :=
  (c.write a 1 v).bind k

/-- Write a 32-bit value at `a` (aligned), then go on. -/
def Low.wr32 (c : Inst) (a : Nat) (v : BitVec 32) (k : Inst → Option Low) : Option Low :=
  if a % 4 = 0 then (c.put (.word a v)).bind k else none

/-- `result<own<T>>` at the return pointer `r`. -/
def lowHandleR (r : Nat) (n : Option (List Val)) (c : Inst) : Option Low :=
  match n with
  | some [.variant 0 (some (.u32 h))] =>
    Low.wr8 c r 0 fun c => Low.wr32 c (r + 4) h fun c => some (.done c [])
  | some [.variant 1 none] => Low.wr8 c r 1 fun c => some (.done c [])
  | _ => none

/-- The case of a variant answer (`0` otherwise). -/
def discOf : Option (List Val) → Nat
  | some [.variant k _] => k
  | _ => 0

/-- The case of the payload of an error answer (`0` otherwise). -/
def errCase : Option (List Val) → Nat
  | some [.variant 1 (some (.variant k _))] => k
  | _ => 0

/-- The handle in the payload of an error answer (`0` otherwise). -/
def errHandle : Option (List Val) → BitVec 32
  | some [.variant 1 (some (.variant _ (some (.u32 e))))] => e
  | _ => 0

/-- Byte `i` of a 32-bit value. -/
def byteOf (v : BitVec 32) (i : Nat) : UInt8 := (v.toNat / 256 ^ i % 256).toUInt8

/-- `result<_, E>` at `r`, for an `E` without payload stored (`error-code`'s payload is not
written): the discriminant. -/
def resUnit (r : Nat) (n : Option (List Val)) : Wr :=
  .part r 1 fun _ => some (discOf n).toUInt8

/-- `result<_, header-error>` at `r`: the discriminant, then the error's case. -/
def resHeaderErr (r : Nat) (n : Option (List Val)) : Wr :=
  .part r 2 fun i => if i = 0 then some (discOf n).toUInt8
    else if discOf n = 1 then some (errCase n).toUInt8 else none

/-- `result<_, stream-error>` at `r`: the discriminant at `0`, the error's case at `4`, the
handle of `last-operation-failed` at `8`. -/
def resStreamErr (r : Nat) (n : Option (List Val)) : Wr :=
  .part r 12 fun i => if i = 0 then some (discOf n).toUInt8
    else if discOf n = 1 ∧ i = 4 then some (errCase n).toUInt8
    else if discOf n = 1 ∧ errCase n = 0 ∧ 8 ≤ i then some (byteOf (errHandle n) (i - 8))
    else none

/-- A result written at the return pointer, with no flat results. -/
def lowPart (w : Wr) (c : Inst) : Option Low := (c.put w).map (.done · [])

/-- Copy `bs` into fresh memory, then go on with its address. -/
def lowList (c : Inst) (bs : List UInt8) (k : BitVec 32 → Inst → Option Low) : Low :=
  .alloc c 1 bs.length fun p c => (c.put (.bytes p.toNat bs)).bind (k p)

/-- Lists of byte lists into fresh memory (the elements first, then the array of pointers and
lengths), then go on with the array's address. -/
def lowLists : List (List UInt8) → List (BitVec 32 × Nat) → (BitVec 32 → Inst → Option Low) →
    Inst → Option Low
  | [], acc, k, c =>
    some (.alloc c 4 (8 * acc.length) fun p c =>
      let rec go : List (BitVec 32 × Nat) → Nat → Inst → Option Low
        | [], _, c => k p c
        | (q, l) :: r, a, c =>
          Low.wr32 c a q fun c => Low.wr32 c (a + 4) (BitVec.ofNat 32 l) fun c => go r (a + 8) c
      go acc.reverse p.toNat c)
  | v :: vs, acc, k, c => some (lowList c v fun q c => lowLists vs ((q, v.length) :: acc) k c)

/-- **The canonical ABI of an import call**: the WIT function, its arguments, and how its
answer is lowered. -/
structure Glue where
  /-- The WIT function. -/
  fn : FnName
  /-- Its arguments. -/
  args : List Val
  /-- Lower an answer (`none`: it is not of the result type). -/
  low : Option (List Val) → Inst → Option Low

/-- Lower a direct handle result. -/
def lowHandle (n : Option (List Val)) (c : Inst) : Option Low := some (.done c [.i32 (hOf n)])

/-- Lower an empty result. -/
def lowUnit (_ : Option (List Val)) (c : Inst) : Option Low := some (.done c [])

/-- The interface of a versioned core import module name. -/
def ifaceOf : String → Option String
  | "wasi:http/types@0.2.12" => some "wasi:http/types"
  | "wasi:io/streams@0.2.12" => some "wasi:io/streams"
  | _ => none

/-- **The imports of the slice**, by interface and function name, on their flat arguments. -/
def glue (c : Inst) (f : FnName) (args : List CVal) : Option Glue :=
  if f = newFields then
    match args with
    | [] => some ⟨f, [], lowHandle⟩
    | _ => none
  else if f = fieldsAppend then
    match args with
    | [.i32 h, .i32 np, .i32 nl, .i32 vp, .i32 vl, .i32 r] =>
      match liftStr c np.toNat nl.toNat, liftBytes c vp.toNat vl.toNat with
      | some s, some v => some ⟨f, [.u32 h, s, bytesV v], fun n => lowPart (resHeaderErr r.toNat n)⟩
      | _, _ => none
    | _ => none
  else if f = newResp ∨ f = reqHeaders then
    match args with
    | [.i32 h] => some ⟨f, [.u32 h], lowHandle⟩
    | _ => none
  else if f = setStatus then
    match args with
    | [.i32 h, .i32 s] => some ⟨f, [.u32 h, .u16 (BitVec.ofNat 16 s.toNat)], fun n c =>
        some (.done c [.i32 (BitVec.ofNat 32 (discOf n))])⟩
    | _ => none
  else if f = respBody ∨ f = bodyWrite ∨ f = reqConsume ∨ f = inStream then
    match args with
    | [.i32 h, .i32 r] => some ⟨f, [.u32 h], lowHandleR r.toNat⟩
    | _ => none
  else if f = outSet then
    match args with
    | [.i32 o, .i32 0, .i32 h, .i32 _, .i64 _, .i32 _, .i32 _, .i32 _, .i32 _] =>
      some ⟨f, [.u32 o, okV (some (.u32 h))], lowUnit⟩
    | _ => none
  else if f = bodyFinish then
    match args with
    | [.i32 b, .i32 d, .i32 t, .i32 r] =>
      some ⟨f, [.u32 b, if d = 0 then .variant 0 none else .variant 1 (some (.u32 t))],
        fun n => lowPart (resUnit r.toNat n)⟩
    | _ => none
  else if f = streamWrite then
    match args with
    | [.i32 s, .i32 p, .i32 l, .i32 r] =>
      match liftBytes c p.toNat l.toNat with
      | some v => some ⟨f, [.u32 s, bytesV v], fun n => lowPart (resStreamErr r.toNat n)⟩
      | none => none
    | _ => none
  else if f = streamDrop then
    match args with
    | [.i32 s] => some ⟨f, [.u32 s], lowUnit⟩
    | _ => none
  else if f = inRead then
    match args with
    | [.i32 s, .i64 len, .i32 r] => some ⟨f, [.u32 s, .u64 len], fun n c =>
        match n with
        | some [.variant 0 (some v)] =>
          let bs := (bytesOf v).map UInt8.ofBitVec
          some (lowList c bs fun p c => Low.wr8 c r.toNat 0 fun c => Low.wr32 c (r.toNat + 4) p
            fun c => Low.wr32 c (r.toNat + 8) (BitVec.ofNat 32 bs.length) fun c => some (.done c []))
        | _ => lowPart (resStreamErr r.toNat n) c⟩
    | _ => none
  else if f = reqPath then
    match args with
    | [.i32 h, .i32 r] => some ⟨f, [.u32 h], fun n c =>
        match n with
        | some [.variant 0 none] => Low.wr8 c r.toNat 0 fun c => some (.done c [])
        | some [.variant 1 (some (.record cs))] =>
          let bs := (cs.filterMap fun | .char ch => some ch | _ => none).flatMap
            fun ch => (String.singleton ch).toUTF8.toList
          if cs.all fun | .char _ => true | _ => false then
            some (lowList c bs fun p c => Low.wr8 c r.toNat 1 fun c => Low.wr32 c (r.toNat + 4) p
              fun c => Low.wr32 c (r.toNat + 8) (BitVec.ofNat 32 bs.length) fun c => some (.done c []))
          else none
        | _ => none⟩
    | _ => none
  else if f = fieldsGet then
    match args with
    | [.i32 h, .i32 np, .i32 nl, .i32 r] =>
      match liftStr c np.toNat nl.toNat with
      | some s => some ⟨f, [.u32 h, s], fun n c =>
          match n with
          | some [.record vs] =>
            lowLists (vs.map fun v => (bytesOf v).map UInt8.ofBitVec) []
              (fun p c => Low.wr32 c r.toNat p fun c => Low.wr32 c (r.toNat + 4) (BitVec.ofNat 32 vs.length)
                fun c => some (.done c [])) c
          | _ => none⟩
      | none => none
    | _ => none
  else none

/-- The number of flat parameters of an import of the slice. -/
def arityOf (f : FnName) : Option Nat :=
  if f = newFields then some 0
  else if f = newResp ∨ f = reqHeaders ∨ f = streamDrop then some 1
  else if f = setStatus ∨ f = respBody ∨ f = bodyWrite ∨ f = reqConsume ∨ f = inStream ∨
    f = reqPath then some 2
  else if f = inRead then some 3
  else if f = bodyFinish ∨ f = streamWrite ∨ f = fieldsGet then some 4
  else if f = fieldsAppend then some 6
  else if f = outSet then some 9
  else none

/-! ## The interpreter -/

/-- **An import call** on the stack `s`: lift the flat arguments, call the WIT function, lower
its answer (with `lower`), and go on with the results on the stack. -/
def callImport (lower : Low → (Inst → List CVal → P) → P) (g : FnName) (c : Inst)
    (ls : List CVal) (s : List CVal) (k : K) : P :=
  match arityOf g with
  | some ps =>
    match glue c g (s.take ps).reverse with
    | some gl =>
      if hg : gl.fn ∈ proxyList then
        .call (⟨gl.fn, hg⟩, gl.args) fun ans =>
          match gl.low ans c with
          | some lo => lower lo fun c res => k c ⟨ls, res.reverse ++ s.drop ps⟩
          | none => trap
      else trap
    | none => trap
  | none => trap

mutual

/-- **Run the instructions** `is` with `fuel`, in the instance `c` and frame `f`: `ls` are the
continuations of the enclosing labels (innermost first), `kr` the return continuation, `k` the
continuation after `is`. -/
def run (m : Module) : Nat → List Instr → Inst → Frame → List K → K → K → P
  | 0, _, _, _, _, _, _ => trap
  | _ + 1, [], c, f, _, _, k => k c f
  | n + 1, i :: is, c, f, ls, kr, k =>
    let k' : K := fun c f => run m n is c f ls kr k
    let push (v : CVal) (s : List CVal) : P := k' c ⟨f.locals, v :: s⟩
    match i, f.stack with
    | .nop, _ => k' c f
    | .drop, _ :: s => k' c ⟨f.locals, s⟩
    | .intConst .i32 v, s => push (.i32 v) s
    | .intConst .i64 v, s => push (.i64 v) s
    | .localGet x, s =>
      match f.locals[x.toNat]? with
      | some v => push v s
      | none => trap
    | .localSet x, v :: s =>
      if x.toNat < f.locals.length then k' c ⟨f.locals.set x.toNat v, s⟩ else trap
    | .localTee x, v :: s =>
      if x.toNat < f.locals.length then k' c ⟨f.locals.set x.toNat v, v :: s⟩ else trap
    | .globalGet x, s =>
      match c.globals[x.toNat]? with
      | some v => push v s
      | none => trap
    | .globalSet x, v :: s =>
      if x.toNat < c.globals.length then k' { c with globals := c.globals.set x.toNat v } ⟨f.locals, s⟩
      else trap
    | .intBinOp .i32 op, .i32 b :: .i32 a :: s =>
      match binop op a b with
      | some v => push (.i32 v) s
      | none => trap
    | .intBinOp .i64 op, .i64 b :: .i64 a :: s =>
      match binop op a b with
      | some v => push (.i64 v) s
      | none => trap
    | .intTestOp .i32 .eqz, .i32 a :: s => push (ofBool (a == 0)) s
    | .intTestOp .i64 .eqz, .i64 a :: s => push (ofBool (a == 0)) s
    | .intRelOp .i32 op, .i32 b :: .i32 a :: s => push (ofBool (relop op a b)) s
    | .intRelOp .i64 op, .i64 b :: .i64 a :: s => push (ofBool (relop op a b)) s
    | .intLoad t packed ⟨⟨0, _⟩⟩ arg, .i32 a :: s =>
      let ea := a.toNat + arg.offset.val
      let w := accessBytes t (packed.map (·.1))
      if c.fits ea w then
        match t, packed, wordAt c.log ea with
        | .i32, none, some v => push (.i32 v) s
        | _, _, _ => push (loaded t packed (readN c.mem ea w)) s
      else trap
    | .intStore .i32 packed ⟨⟨0, _⟩⟩ arg, .i32 v :: .i32 a :: s =>
      match c.put (if packed.isNone then .word (a.toNat + arg.offset.val) v
          else .num (a.toNat + arg.offset.val) (accessBytes .i32 packed) v.toNat) with
      | some c => k' c ⟨f.locals, s⟩
      | none => trap
    | .intStore .i64 packed ⟨⟨0, _⟩⟩ arg, .i64 v :: .i32 a :: s =>
      match c.write (a.toNat + arg.offset.val) (accessBytes .i64 packed) v.toNat with
      | some c => k' c ⟨f.locals, s⟩
      | none => trap
    | .memorySize ⟨⟨0, _⟩⟩, s => push (.i32 (BitVec.ofNat 32 c.pages)) s
    | .memoryGrow ⟨⟨0, _⟩⟩, .i32 d :: s =>
      if c.pages + d.toNat ≤ 65536 then
        k' { c with pages := c.pages + d.toNat } ⟨f.locals, .i32 (BitVec.ofNat 32 c.pages) :: s⟩
      else push (.i32 (-1)) s
    | .memoryCopy ⟨⟨0, _⟩⟩ ⟨⟨0, _⟩⟩, .i32 len :: .i32 src :: .i32 dst :: s =>
      if c.fits src.toNat len.toNat ∧ c.fits dst.toNat len.toNat then
        k' { c with log := .copy dst.toNat src.toNat len.toNat :: c.log } ⟨f.locals, s⟩
      else trap
    | .block bt body, s =>
      match blockArity bt with
      | some a => run m n body c f ((fun c f' => k' c ⟨f'.locals, f'.stack.take a ++ s⟩) :: ls) kr k'
      | none => trap
    | .loop bt body, s =>
      match blockArity bt with
      | some _ =>
        run m n body c f ((fun c f' => run m n [.loop bt body] c ⟨f'.locals, s⟩ ls kr k') :: ls) kr k'
      | none => trap
    | .if_ bt th el, .i32 v :: s =>
      match blockArity bt with
      | some a =>
        run m n (if v = 0 then el else th) c ⟨f.locals, s⟩
          ((fun c f' => k' c ⟨f'.locals, f'.stack.take a ++ s⟩) :: ls) kr k'
      | none => trap
    | .br l, _ =>
      match ls[l.toNat]? with
      | some lab => lab c f
      | none => trap
    | .brIf l, .i32 v :: s =>
      if v = 0 then k' c ⟨f.locals, s⟩ else
      match ls[l.toNat]? with
      | some lab => lab c ⟨f.locals, s⟩
      | none => trap
    | .return_, _ => kr c f
    | .call fi, s =>
      let imps := funcImports m
      if fi.toNat < imps.length then
        match imps[fi.toNat]? with
        | some (mn, nm) =>
          match ifaceOf mn with
          | some ifc => callImport (lower m n) ⟨ifc, nm⟩ c f.locals s k'
          | none => trap
        | none => trap
      else
        match m.funcs[fi.toNat - imps.length]? with
        | some fn =>
          match funcArity m fn.type with
          | some (ps, rs) =>
            let kret : K := fun c f' => k' c ⟨f.locals, f'.stack.take rs ++ s.drop ps⟩
            run m n fn.body c ⟨(s.take ps).reverse ++ fn.locals.map zeroOf, []⟩ [kret] kret kret
          | none => trap
        | none => trap
    | _, _ => trap

/-- Carry out a lowering, calling `cabi_realloc` for its allocations. -/
def lower (m : Module) : Nat → Low → (Inst → List CVal → P) → P
  | 0, _, _ => trap
  | _ + 1, .done c res, k => k c res
  | n + 1, .alloc c al len lk, k =>
    match exportFunc m "cabi_realloc" with
    | some fi =>
      run m n [.call ⟨⟨fi % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩] c
        ⟨[], [.i32 (BitVec.ofNat 32 len), .i32 (BitVec.ofNat 32 al), .i32 0, .i32 0]⟩ []
        (fun _ _ => trap) fun c f =>
          match f.stack with
          | [.i32 p] =>
            match lk p c with
            | some lo => lower m n lo k
            | none => trap
          | _ => trap
    | none => trap

end

/-! ## The denotation -/

/-- The core name of the export `handle`. -/
def handleName : String := "wasi:http/incoming-handler@0.2.12#handle"

/-- **The body of a core module**: each call `handle(r, o)` runs the export `handle` on a fresh
instance, with at most `fuel` steps. -/
def coreBody (m : Module) (fuel : Nat) : Body proxyImports proxyWorld.exports := fun q =>
  match freshInst m, exportFunc m handleName with
  | some c, some fi =>
    if h : fi < 2 ^ 32 then
      run m fuel [.call ⟨⟨fi, h⟩⟩] c ⟨[], [.i32 (outOf q.2), .i32 (reqOf q.2)]⟩ []
        (fun _ _ => .pure (some [])) (fun _ _ => .pure (some []))
    else trap
  | _, _ => trap

end Silmaril.Servers.WasiCore
