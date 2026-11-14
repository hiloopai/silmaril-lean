module

public import Silmaril.Machine.X86.Open9.Defs
public import Silmaril.Machine.X86.Safe.Defs

/-!
# `Str9`: the open `Ext9` machine with three string forms

musl's
`memcpy` uses `movsb` and `rep movsq`, its `memset` and startup (`aux[]`) use `rep stosq`;
none of them is decoded by `X86.Ext`, `Ext8` or `Ext9`. `Str9.step` is `Open9.step`, except
on bytes that `Ext8` and `Ext9` both reject, where it decodes:

| Form | Bytes | `Str` |
| --- | --- | --- |
| `movsb` (`movs byte [rdi], [rsi]`) | `A4` | `movsb` |
| `rep movsq` | `F3 48 A5` | `repMovsq` |
| `rep stosq` | `F3 48 AB` | `repStosq` |

Only these exact encodings are accepted: no other prefix (segment override, `66`, `67`, a REX
other than `48`, `F2`), no `rep movsb`/`movsq`/`stosb`/`stosd`. This is a **sibling** of `Sse9`
over `Open9` (AD-6), not stacked on it; its opcode table is checked disjoint from `Sse9`'s and
from `Atomic9`'s planned table by `decide` (`Str9/Thms.lean`).

## Semantics, and the documented choices

* **One element per step** (the microstep discipline of the LPS `X86RepStosq` model, and the
  architectural interrupt point of a `rep` string instruction, SDM Vol. 2 "REP/REPE/…"): with
  `rcx = 0`, `rep movsq`/`rep stosq` only advance RIP. Otherwise one quadword is moved or stored,
  `rsi`/`rdi` advance by 8, `rcx` decreases by one, and RIP stays on the instruction unless the
  new `rcx` is `0`, in which case it advances. So `k > 0` elements take exactly `k` steps
  (`rep_movsq_copy`, `rep_stosq_fill`).
* **DF is clear.** `Silmaril.X86.State` has no direction flag; the System V ABI requires DF
  clear on function entry and exit, and the model assumes it throughout (pointers increase).
* No string form here reads or writes RFLAGS.
* Each element is a little-endian `loadN`/`storeN` of 1 or 8 bytes, byte-checked like `Ext`'s
  accesses: an element whose source is not readable or whose destination is not writable
  faults (`dataFault`, no step) **before** any register changes, so a fault leaves the state of
  the last completed element (as on hardware, where `rep` faults are restartable).
* Overlap: each element reads, then writes, in order. For overlapping `rep movsq` with
  `rdi > rsi` this is the element-by-element architectural result; fast-string hardware is
  specified to produce the same final result (SDM Vol. 1 §7.3.9.3, FROM MEMORY), which DT2's
  overlap difftests arbitrate.
* Address-size is 64 bits (`rsi`, `rdi`, `rcx` in full), as for these encodings in 64-bit
  mode without `67`.

This is a handwritten model of the SDM, not proved to match hardware; its difftest belongs to
(`tools/ext9-difftest`), not to this package.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Str9

open Silmaril.X86 (State MState Word Byte Reg maxInstrLength fetchWindow)
open Silmaril.X86.Ext (Result loadN storeN)
open Silmaril.Process (Memory)

/-! ## Machines that extend `Open9` -/

/-- **The machine extends the open machine over `Ext9`**: every `Open9.step` step is one of it
(: no such class existed before Z3a). -/
class ExtendsOpen9 (step : MState → Option MState) : Prop where
  ext : Safe.Refines Open9.step step

/-! ## Instructions -/

/-- The three string forms. -/
inductive Str where
  /-- `movsb` (`A4`): one byte from `[rsi]` to `[rdi]`. -/
  | movsb
  /-- `rep movsq` (`F3 48 A5`): `rcx` quadwords from `[rsi]` to `[rdi]`. -/
  | repMovsq
  /-- `rep stosq` (`F3 48 AB`): `rcx` copies of `rax` to `[rdi]`. -/
  | repStosq
  deriving DecidableEq, Repr

/-- The instructions of the machine: an `Ext9` instruction or a string form. -/
inductive Instr where
  | open9 (i : Ext9.Instr)
  | str (i : Str)
  deriving DecidableEq, Repr

/-- The encoding of a string form. -/
def Str.bytes : Str → List Byte
  | .movsb => [0xA4]
  | .repMovsq => [0xF3, 0x48, 0xA5]
  | .repStosq => [0xF3, 0x48, 0xAB]

/-! ## Decoding -/

/-- Decode a string form; the form and the number of bytes consumed. -/
def decodeStr : List Byte → Option (Str × Nat)
  | 0xA4 :: _ => some (.movsb, 1)
  | 0xF3 :: 0x48 :: 0xA5 :: _ => some (.repMovsq, 3)
  | 0xF3 :: 0x48 :: 0xAB :: _ => some (.repStosq, 3)
  | _ => none

/-- `Ext9`'s new-form parser rejects (and so rejects every extension). -/
def ext9Bad (bytes : List Byte) : Bool :=
  match Ext9.pNew bytes with
  | .bad => true
  | _ => false

/-- The listing decoder of a string form: `Ext` rejects the slice, the parsers of `Ext8`'s
and `Ext9`'s new forms reject it, the `Ext` length decoder finishes inside it, and
`decodeStr` reads a form at its front; the length returned is the form's, not the slice's
(`decodeL [F3, 48, A5, 90] = some (repMovsq, 3)`), so the listing laws, which ask for
`some (i, l)` on a slice of length `l`, use it only on the form's own bytes. Checked on each
listing by `decide`. -/
def decodeL (bytes : List Byte) : Option (Str × Nat) :=
  match decodeStr bytes with
  | some (i, n) =>
    if Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
        Open9.rawNotEof bytes = true ∧ ext9Bad bytes = true ∧ n ≤ maxInstrLength then
      some (i, n)
    else none
  | none => none

/-- The listing decoder of the machine: `Open9.decode` first, then a string form. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match Open9.decode bytes with
  | some (i, n) => some (.open9 i, n)
  | none => (decodeL bytes).map fun (i, n) => (.str i, n)

/-! ## Semantics -/

/-- One element of `rep movsq`/`rep stosq` (`rcx ≠ 0`): store `v` at `rdi`, advance `rdi` (and
`rsi` when `src`), decrease `rcx`, and leave RIP on the instruction unless `rcx` reaches `0`. -/
def repElem (src : Bool) (v : Word) (s : State) (memory : Memory) (next : Word) : Result :=
  match storeN memory (s.read .rdi) 8 v with
  | none => .dataFault
  | some memory' =>
    let c := s.read .rcx - 1
    let t := ((if src then s.write .rsi (s.read .rsi + 8) else s).write .rdi
      (s.read .rdi + 8)).write .rcx c
    .ok { t with rip := if c = 0 then next else s.rip } memory'

/-- **Execute one step of a string form**, given the address of the next instruction. -/
def execStr (i : Str) (s : State) (memory : Memory) (next : Word) : Result :=
  match i with
  | .movsb =>
    match loadN memory (s.read .rsi) 1 with
    | none => .dataFault
    | some v =>
      match storeN memory (s.read .rdi) 1 v with
      | none => .dataFault
      | some memory' =>
        .ok { (s.write .rsi (s.read .rsi + 1)).write .rdi (s.read .rdi + 1) with rip := next }
          memory'
  | .repMovsq =>
    if s.read .rcx = 0 then .ok { s with rip := next } memory
    else
      match loadN memory (s.read .rsi) 8 with
      | none => .dataFault
      | some v => repElem true v s memory next
  | .repStosq =>
    if s.read .rcx = 0 then .ok { s with rip := next } memory
    else repElem false (s.read .rax) s memory next

/-- The executor of the machine's instructions (the `SegVC` shape: the encoded length). -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .open9 i => Ext9.exec i s memory length
  | .str i => execStr i s memory (s.rip + BitVec.ofNat 64 length)

/-! ## Fetch and step -/

/-- Fetch a string form: `decodeStr` reads the fetch window and the bytes it consumed are
executable. `none` if not decodable as a string form; `some none` if not fetchable. -/
def fetchStr (memory : Memory) (address : Nat) : Option (Option (Str × Nat)) :=
  (decodeStr (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- **One step**: `Open9.step`; on bytes that neither `Ext8` nor `Ext9` decodes, a string
form. -/
def step (m : MState) : Option MState :=
  match Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with
  | .inl .undecodable =>
    match Ext9.fetchNew m.memory m.core.rip.toNat with
    | some (some (i, n)) =>
      Open.ofResult (Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
    | some none => none
    | none =>
      match fetchStr m.memory m.core.rip.toNat with
      | some (some (i, n)) =>
        Open.ofResult (execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
      | _ => none
  | _ => Open.step m

/-! ## What a `rep` run computes -/

/-- `k` quadwords copied from `src` to `dst`, one element at a time (read, then write). -/
def copyQ : Nat → Word → Word → Memory → Option Memory
  | 0, _, _, memory => some memory
  | k + 1, src, dst, memory => do
    let v ← loadN memory src 8
    let memory' ← storeN memory dst 8 v
    copyQ k (src + 8) (dst + 8) memory'

/-- `k` copies of the quadword `v` stored from `dst` upwards. -/
def fillQ : Nat → Word → Word → Memory → Option Memory
  | 0, _, _, memory => some memory
  | k + 1, v, dst, memory => do
    let memory' ← storeN memory dst 8 v
    fillQ k v (dst + 8) memory'

/-- The core after a finished `rep movsq` (`src = true`) or `rep stosq` (`src = false`) of
`k` elements started from `c`: RIP past the 3-byte instruction, `rcx = 0`, `rdi` (and `rsi`
when `src`) advanced by `8 k`, every other register, the flags and the FS base unchanged. -/
def RepDone (src : Bool) (k : Nat) (c c' : State) : Prop :=
  c'.rip = c.rip + BitVec.ofNat 64 3 ∧ c'.read .rcx = 0 ∧
    c'.read .rdi = c.read .rdi + BitVec.ofNat 64 (8 * k) ∧
    c'.read .rsi = (if src then c.read .rsi + BitVec.ofNat 64 (8 * k) else c.read .rsi) ∧
    (∀ r : Reg, r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → c'.read r = c.read r) ∧
    c'.flags = c.flags ∧ c'.fsBase = c.fsBase

/-- A byte the memory lets a store write. -/
def Writable (memory : Memory) (address : Nat) : Prop :=
  memory.permits .write address = true

/-! ## Opcode tables (-6) -/

/-- Two opcode tables are **disjoint**: no key of one is a prefix of a key of the other. A
decoder that commits only on a key of its table then never reads bytes the other decodes. -/
def TableDisjoint (t u : List (List Byte)) : Bool :=
  t.all fun a => u.all fun b => !(a.isPrefixOf b) && !(b.isPrefixOf a)

/-- The opcode keys of `Str9`: exactly the three encodings. -/
def table : List (List Byte) := [Str.movsb.bytes, Str.repMovsq.bytes, Str.repStosq.bytes]

/-- The opcode keys of `Sse9` (`Silmaril/Machine/X86/Sse9/Defs.lean`, table and `pBody`): the
legacy prefix, the optional REX byte (`40`–`4F`, with `W` only on `66 0F 6E/7E`), and the
`0F`-escaped opcode. Listed with every REX byte that `Sse9.pBody` accepts. -/
def sse9Table : List (List Byte) :=
  let rexAny : List Byte := (List.range 16).map fun r => BitVec.ofNat 8 (0x40 + r)
  let rexNoW : List Byte := (List.range 8).map fun r => BitVec.ofNat 8 (0x40 + r)
  let keys (pfx : List Byte) (rexs : List Byte) (ops : List Byte) : List (List Byte) :=
    ops.flatMap fun o => (pfx ++ [0x0F, o]) :: rexs.map fun r => pfx ++ [r, 0x0F, o]
  keys [] rexNoW [0x10, 0x11, 0x28, 0x29, 0x57] ++
    keys [0xF3] rexNoW [0x6F, 0x7F, 0x7E] ++
    keys [0x66] rexAny [0x6E, 0x7E] ++
    keys [0x66] rexNoW [0x6F, 0x7F, 0xD6, 0xEF, 0x6C, 0x62]

/-- The opcode keys of the planned `Atomic9` (`concurrency.md` §2.2, not merged when
Z3a was written): the `F0` prefix, `86`/`87` (with any REX), `0F B0/B1/C0/C1/C7`,
`0F AE F0/E8/F8` and `F3 90`. DT2 re-checks this against `Atomic9.decode` once K1 lands. -/
def atomic9Table : List (List Byte) :=
  let rexAny : List Byte := (List.range 16).map fun r => BitVec.ofNat 8 (0x40 + r)
  let withRex (ops : List (List Byte)) : List (List Byte) :=
    ops ++ ops.flatMap fun o => rexAny.map fun r => r :: o
  [[0xF0], [0xF3, 0x90]] ++
    withRex [[0x86], [0x87], [0x0F, 0xB0], [0x0F, 0xB1], [0x0F, 0xC0], [0x0F, 0xC1],
      [0x0F, 0xC7]] ++
    [[0x0F, 0xAE, 0xF0], [0x0F, 0xAE, 0xE8], [0x0F, 0xAE, 0xF8]]

end Silmaril.Machine.X86.Str9
