module

public import Silmaril.X86.Atomic9.Defs
public import Silmaril.X86.Sep.Spec.Defs
public import Silmaril.X86.Open.Thms

/-!
# Memory events and locality

The interface is
"instruction = access list + local function": every instruction of the open machines has a
list of memory events (`Event`: a load, a store, a read-modify-write or a fence, with an
address, a size and a `locked` tag), computed from the **core only** (x86 has no double
indirection; the fetch is separate), and the executor is **local** for it (`Local`): its
outcome depends only on the mapping list and on the bytes of the read set, and it changes only
the bytes of the write set, each of which it really writes.

Under SC the events are implicit: an executor runs on one `Memory`, as today. A TSO machine
can run the *unchanged* executor on a buffer-overlaid view and diff the write set into the
store buffer. Sequential proofs never mention events.

## What is defined here

* `Kind`, `Event`, `Event.singleCopy`, `readSet`, `writeSet`;
* `Agree R m m'`: same mapping list and the same bytes on `R`;
* `Patched W m m₁ m' m₁'`: `m ↦ m₁` and `m' ↦ m₁'` keep the mapping list, change bytes only
  on `W`, write the same bytes on `W`, and every byte of `W` was write-permitted in `m` and is
  backed in `m₁` (the write really happened: write sets are **exact**, because under TSO an
  extra store of an unchanged value is observable);
* `Rel W m m'`: two outcomes (viewed as a fault or a payload with a memory) are the same fault,
  or the same payload with `Patched` memories;
* `Local view exec es`: **locality** of an executor (a function of the memory) for the events
  `es`;
* the access lists `extAccesses`, `ext8NewAccesses`, `ext8Accesses`, `ext9NewAccesses`,
  `ext9Accesses`, `atomic9NewAccesses`, `atomic9Accesses` (using `Atomic9.tag`) and
  `sse9Accesses`, and the result views `extView`, `sse9View`.

Read sets may over-approximate (they cost only extra `load` events); write sets are exact.
String instructions (`rep movs/stos`) are not decoded today;
when they are, they become multi-event, iteration-indexed access lists.

The theorems (`ext_local`, `ext8_local`, `ext9_local`, `atomic9_local`, `sse9_local`,
`open9_step_sc`, `triple_step_of_local`) are in `MemEvent/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.MemEvent

open Silmaril.X86 (State Word Reg)
open Silmaril.X86.Ext (RM Mem Sz Narrow)
open Silmaril.Process (Memory)

/-! ## Events -/

/-- The kind of a memory event. -/
inductive Kind where
  | load
  | store
  | rmw
  | fence (k : Atomic9.FenceKind)
  deriving DecidableEq, Repr

/-- The event reads memory. -/
def Kind.reads : Kind → Bool
  | .load | .rmw => true
  | _ => false

/-- The event writes memory. -/
def Kind.writes : Kind → Bool
  | .store | .rmw => true
  | _ => false

/-- A memory event: kind, first byte address, size in bytes (`0` for fences; 1, 2, 4, 8 or
16 otherwise) and the `locked` tag (from `Atomic9.tag`). -/
structure Event where
  kind : Kind
  addr : Nat
  size : Nat
  locked : Bool
  deriving DecidableEq, Repr

/-- The event touches byte `a`. -/
def Event.Covers (e : Event) (a : Nat) : Prop := e.addr ≤ a ∧ a < e.addr + e.size

/-- Single-copy atomic on x86 (SDM Vol. 3A §9.1.1, FROM MEMORY): naturally aligned and at
most eight bytes. -/
def Event.singleCopy (e : Event) : Bool := e.size ≤ 8 && e.addr % e.size == 0

/-- The bytes an event list reads. -/
def readSet (es : List Event) (a : Nat) : Prop := ∃ e ∈ es, e.kind.reads = true ∧ e.Covers a

/-- The bytes an event list writes. -/
def writeSet (es : List Event) (a : Nat) : Prop := ∃ e ∈ es, e.kind.writes = true ∧ e.Covers a

/-! ## Locality -/

/-- Two memories have the same mapping list and the same bytes on `R`. -/
def Agree (R : Nat → Prop) (m m' : Memory) : Prop :=
  m.regions = m'.regions ∧ ∀ a, R a → m.bytes[a]? = m'.bytes[a]?

/-- The transitions `m ↦ m₁` and `m' ↦ m₁'` keep the mapping list, change bytes only on `W`,
agree on `W` afterwards, and really wrote `W` (write-permitted in `m`, backed in `m₁`). -/
structure Patched (W : Nat → Prop) (m m₁ m' m₁' : Memory) : Prop where
  regions : m₁.regions = m.regions
  regions' : m₁'.regions = m'.regions
  inside : ∀ a, W a → m₁'.bytes[a]? = m₁.bytes[a]?
  outside : ∀ a, ¬ W a → m₁.bytes[a]? = m.bytes[a]?
  outside' : ∀ a, ¬ W a → m₁'.bytes[a]? = m'.bytes[a]?
  wrote : ∀ a, W a → m.permits .write a = true ∧ (m₁.bytes[a]?).isSome = true

/-- Two optional successors: both fail, or both succeed with the same payload and `Patched`
memories. -/
def OptRel {α : Type} (W : Nat → Prop) (m m' : Memory) :
    Option (α × Memory) → Option (α × Memory) → Prop
  | none, none => True
  | some p, some p' => p.1 = p'.1 ∧ Patched W m p.2 m' p'.2
  | _, _ => False

/-- Two outcomes, viewed as a fault or a payload with a memory: the same fault, or the same
payload with `Patched` memories. -/
def Rel {ε α : Type} (W : Nat → Prop) (m m' : Memory) :
    ε ⊕ (α × Memory) → ε ⊕ (α × Memory) → Prop
  | .inl e, .inl e' => e = e'
  | .inr p, .inr p' => p.1 = p'.1 ∧ Patched W m p.2 m' p'.2
  | _, _ => False

/-- **Locality** of an executor `exec` (a function of the memory, everything else fixed) for
the events `es`: on two memories with the same mapping list and the same bytes on the read
set, the outcomes are the same fault, or the same payload with memories patched on exactly the
write set. Taking `m' = m` gives the frame (`Local.frame`) and the exactness of the write set
(`Local.exact`), in `MemEvent/Thms.lean`. -/
structure Local {ρ ε α : Type} (view : ρ → ε ⊕ (α × Memory)) (exec : Memory → ρ)
    (es : List Event) : Prop where
  congr : ∀ m m', Agree (readSet es) m m' → Rel (writeSet es) m m' (view (exec m)) (view (exec m'))

/-! ## Result views -/

/-- An `Ext.Result` as a fault or a successor core with a memory. -/
def extView : Silmaril.X86.Ext.Result → Silmaril.X86.Ext.Result ⊕ (State × Memory)
  | .ok c m => .inr (c, m)
  | r => .inl r

/-- An `Sse9.XResult` as a fault or a successor core and XMM file with a memory. -/
def sse9View : Sse9.XResult → Sse9.XResult ⊕ ((State × Sse9.XFile) × Memory)
  | .ok c x m => .inr ((c, x), m)
  | r => .inl r

/-! ## Event builders -/

/-- One event at an effective address. -/
def memEv (k : Kind) (lk : Bool) (size : Nat) (a : Ext.Mem) (s : State) (next : Word) :
    List Event :=
  [⟨k, (a.addr s next).toNat, size, lk⟩]

/-- The event of an `r/m` operand: none for a register. -/
def rmEv (k : Kind) (lk : Bool) (size : Nat) (op : RM) (s : State) (next : Word) :
    List Event :=
  match op with
  | .reg _ => []
  | .mem a => memEv k lk size a s next

/-- The event of an `r/m8` operand: none for a register. -/
def rm8Ev (k : Kind) (lk : Bool) (op : Silmaril.X86.Ext8.RM8) (s : State) (next : Word) :
    List Event :=
  match op with
  | .reg _ => []
  | .mem a => memEv k lk 1 a s next

/-- The event of an `xmm/m` operand: none for a register. -/
def xrmEv (k : Kind) (size : Nat) (op : Sse9.XRM) (s : State) (next : Word) : List Event :=
  match op with
  | .reg _ => []
  | .mem a => memEv k false size a s next

/-- The store of `push`/`call`: eight bytes at `rsp - 8`. -/
def pushEv (s : State) : List Event := [⟨.store, (s.read .rsp - 8#64).toNat, 8, false⟩]

/-- The load of `pop`/`ret`: eight bytes at `rsp`. -/
def popEv (s : State) : List Event := [⟨.load, (s.read .rsp).toNat, 8, false⟩]

/-- A two-operand ALU destination: a load for `cmp` (which writes nothing), else a
read-modify-write. -/
def aluKind (op : Silmaril.X86.AluOp) : Kind := if op = .cmp then .load else .rmw

/-! ## Access lists -/

/-- The access list of an `Ext` instruction executed with length `len`. -/
def extAccesses (i : Silmaril.X86.Ext.Instr) (s : State) (len : Nat) : List Event :=
  let next := s.rip + BitVec.ofNat 64 len
  match i with
  | .mov sz dst _ => rmEv .store false sz.bytes dst s next
  | .movI sz dst _ => rmEv .store false sz.bytes dst s next
  | .movI16 dst _ => rmEv .store false 2 dst s next
  | .movI32 .. => []
  | .movabs .. => []
  | .load sz _ src => memEv .load false sz.bytes src s next
  | .store n dst _ => rmEv .store false n.bytes dst s next
  | .movx _ _ n _ src => rmEv .load false n.bytes src s next
  | .movsxd _ src => rmEv .load false 4 src s next
  | .lea .. => []
  | .alu sz op dst _ => rmEv (aluKind op) false sz.bytes dst s next
  | .aluR sz _ _ src => rmEv .load false sz.bytes src s next
  | .aluI sz op dst _ => rmEv (aluKind op) false sz.bytes dst s next
  | .aluI8 sz op dst _ => rmEv (aluKind op) false sz.bytes dst s next
  | .aluA .. => []
  | .test sz dst _ => rmEv .load false sz.bytes dst s next
  | .test8 dst _ => rmEv .load false 1 dst s next
  | .testI8 dst _ => rmEv .load false 1 dst s next
  | .testA8 _ => []
  | .cmpI8 dst _ => rmEv .load false 1 dst s next
  | .cmpA8 _ => []
  | .testA .. => []
  | .incdec sz _ dst => rmEv .rmw false sz.bytes dst s next
  | .pushRM src => rmEv .load false 8 src s next ++ pushEv s
  | .bswap .. => []
  | .unary sz _ dst => rmEv .rmw false sz.bytes dst s next
  | .imul sz _ src => rmEv .load false sz.bytes src s next
  | .mul sz src => rmEv .load false sz.bytes src s next
  | .shift sz _ dst _ => rmEv .rmw false sz.bytes dst s next
  | .cxd _ => []
  | .cxe _ => []
  | .div sz _ src => rmEv .load false sz.bytes src s next
  | .cmov sz _ _ src => rmEv .load false sz.bytes src s next
  | .setcc _ dst => rmEv .store false 1 dst s next
  | .jmp _ => []
  | .jmp8 _ => []
  | .jcc8 .. => []
  | .jcc .. => []
  | .call _ => pushEv s
  | .ret => popEv s
  | .push _ => pushEv s
  | .pop _ => popEv s
  | .ud2 => []
  | .nop _ => []
  | .endbr64 => []
  | .mov8 _ src => rmEv .load false 1 src s next
  | .movI8 dst _ => rmEv .store false 1 dst s next
  | .leave => [⟨.load, (s.read .rbp).toNat, 8, false⟩]
  | .bitcount _ sz _ src => rmEv .load false sz.bytes src s next

/-- The access list of a new `Ext8` form, given the address of the next instruction. -/
def ext8NewAccesses (i : Silmaril.X86.Ext8.New) (s : State) (next : Word) : List Event :=
  match i with
  | .alu op dst _ => rm8Ev (aluKind op) false dst s next
  | .aluR _ _ src => rm8Ev .load false src s next
  | .aluA .. => []
  | .aluI op dst _ => rm8Ev (aluKind op) false dst s next
  | .test dst _ => rm8Ev .load false dst s next
  | .shift _ dst count =>
    if (count.raw s).toNat % 32 = 0 then rm8Ev .load false dst s next
    else rm8Ev .rmw false dst s next
  | .mov dst _ => rm8Ev .store false dst s next
  | .movR _ src => rm8Ev .load false src s next
  | .movx _ _ _ src => rm8Ev .load false src s next
  | .setcc _ dst => rm8Ev .store false dst s next

/-- The access list of an `Ext8` instruction executed with length `len`. -/
def ext8Accesses (i : Silmaril.X86.Ext8.Instr) (s : State) (len : Nat) : List Event :=
  match i with
  | .base i => extAccesses i s len
  | .new i => ext8NewAccesses i s (s.rip + BitVec.ofNat 64 len)

/-- The access list of a new `Ext9` form, given the address of the next instruction. -/
def ext9NewAccesses (i : Ext9.New) (s : State) (next : Word) : List Event :=
  match i with
  | .imulI sz _ src _ => rmEv .load false sz.bytes src s next
  | .imul1 sz src => rmEv .load false sz.bytes src s next
  | .bsf sz _ src => rmEv .load false sz.bytes src s next
  | .bsr sz _ src => rmEv .load false sz.bytes src s next
  | .adc sz _ dst _ => rmEv .rmw false sz.bytes dst s next
  | .adcR sz _ _ src => rmEv .load false sz.bytes src s next
  | .adcI sz _ dst _ => rmEv .rmw false sz.bytes dst s next
  | .callInd src => rmEv .load false 8 src s next ++ pushEv s
  | .jmpInd src => rmEv .load false 8 src s next
  | .pushI _ => pushEv s
  | .alu16 op dst _ => rmEv (aluKind op) false 2 dst s next
  | .alu16R _ _ src => rmEv .load false 2 src s next
  | .alu16I op dst _ => rmEv (aluKind op) false 2 dst s next
  | .alu16A .. => []
  | .test16 dst _ => rmEv .load false 2 dst s next
  | .test16I dst _ => rmEv .load false 2 dst s next
  | .test16A _ => []
  | .testI sz dst _ => rmEv .load false sz.bytes dst s next
  | .testI8 dst _ => rm8Ev .load false dst s next
  | .bt .. => []
  | .repRet => extAccesses .ret s 2

/-- The access list of an `Ext9` instruction executed with length `len`. -/
def ext9Accesses (i : Ext9.Instr) (s : State) (len : Nat) : List Event :=
  match i with
  | .ext8 i => ext8Accesses i s len
  | .new i => ext9NewAccesses i s (s.rip + BitVec.ofNat 64 len)

/-- The access list of an atomic form, given the address of the next instruction. The
`locked` tag is `(Atomic9.tag i).locked`; a fence is one `fence` event of size 0. -/
def atomic9NewAccesses (i : Atomic9.New) (s : State) (next : Word) : List Event :=
  let lk := (Atomic9.tag i).locked
  match i with
  | .lockAlu sz op dst _ => memEv (aluKind op) lk sz.bytes dst s next
  | .lockAluI sz op dst _ => memEv (aluKind op) lk sz.bytes dst s next
  | .lockAlu8I op dst _ => memEv (aluKind op) lk 1 dst s next
  | .lockIncDec sz _ dst => memEv .rmw lk sz.bytes dst s next
  | .lockBts sz dst _ => memEv .rmw lk sz.bytes dst s next
  | .xadd sz _ dst _ => rmEv .rmw lk sz.bytes dst s next
  | .cmpxchg sz _ dst _ => rmEv .rmw lk sz.bytes dst s next
  | .cmpxchg8 _ dst _ => rm8Ev .rmw lk dst s next
  | .xchg sz dst _ => rmEv .rmw lk sz.bytes dst s next
  | .xchg8 dst _ => rm8Ev .rmw lk dst s next
  | .fence k => [⟨.fence k, 0, 0, lk⟩]
  | .pause => []

/-- The access list of an `Atomic9` instruction executed with length `len`. -/
def atomic9Accesses (i : Atomic9.Instr) (s : State) (len : Nat) : List Event :=
  match i with
  | .open9 i => ext9Accesses i s len
  | .new i => atomic9NewAccesses i s (s.rip + BitVec.ofNat 64 len)

/-- The access list of an SSE form, given the address of the next instruction. -/
def sse9Accesses (i : Sse9.Instr) (s : State) (next : Word) : List Event :=
  match i with
  | .load _ _ src => xrmEv .load 16 src s next
  | .store _ dst _ => xrmEv .store 16 dst s next
  | .movToX sz _ src => rmEv .load false sz.bytes src s next
  | .movFromX sz dst _ => rmEv .store false sz.bytes dst s next
  | .movqLoad _ src => xrmEv .load 8 src s next
  | .movqStore dst _ => xrmEv .store 8 dst s next
  | .pxor _ src => xrmEv .load 16 src s next
  | .xorps _ src => xrmEv .load 16 src s next
  | .punpcklqdq _ src => xrmEv .load 16 src s next
  | .punpckldq _ src => xrmEv .load 16 src s next

/-! ## Fetch, as the first half of a step

Each open machine's step is "fetch, then execute the decoded instruction on the one memory"
(`open_step_eq`, `open9_step_eq`, `atomic9_step_eq` in `MemEvent/Thms.lean`). These are the
fetches, with the length the executor is run with (`Ext` forms: the canonical length, as in
`Open.step`). -/

/-- The fetch of `Open.step`. -/
def openFetch (memory : Memory) (addr : Nat) : Option (Silmaril.X86.Ext8.Instr × Nat) :=
  match Silmaril.X86.Ext8.fetch memory addr with
  | .inl (.decoded i _) => some (.base i, i.length)
  | .inr (i, n) => some (.new i, n)
  | .inl _ => none

/-- The fetch of `Open9.step`. -/
def open9Fetch (memory : Memory) (addr : Nat) : Option (Ext9.Instr × Nat) :=
  match Silmaril.X86.Ext8.fetch memory addr with
  | .inl .undecodable =>
    match Ext9.fetchNew memory addr with
    | some (some (i, n)) => some (.new i, n)
    | _ => none
  | _ => (openFetch memory addr).map fun p => (.ext8 p.1, p.2)

/-- The fetch of `Atomic9.step`. -/
def atomic9Fetch (memory : Memory) (addr : Nat) : Option (Atomic9.Instr × Nat) :=
  match Silmaril.X86.Ext8.fetch memory addr with
  | .inl .undecodable =>
    match Ext9.fetchNew memory addr with
    | some (some (i, n)) => some (.open9 (.new i), n)
    | some none => none
    | none =>
      match Atomic9.fetchNew memory addr with
      | some (some (i, n)) => some (.new i, n)
      | _ => none
  | _ => (openFetch memory addr).map fun p => (.open9 (.ext8 p.1), p.2)

/-! ## Footprints of one step, for the `Sep` frame rule -/

/-- A core transition changes only registers, `rip` and flags owned by the fragment `h`. -/
def CoreWithin (h : Silmaril.X86.Sep.Frag) (c c' : State) : Prop :=
  (∀ r, c'.read r ≠ c.read r → (h (.reg r)).isSome = true) ∧
    (c'.rip ≠ c.rip → (h .rip).isSome = true) ∧
    (c'.flags ≠ c.flags → (h .flags).isSome = true)

/-- A machine transition changes only locations owned by the fragment `h`. -/
def ChangesWithin (h : Silmaril.X86.Sep.Frag) (m m' : Silmaril.X86.MState) : Prop :=
  ∀ l, h l = none → Silmaril.X86.Sep.toFrag m' l = Silmaril.X86.Sep.toFrag m l

end Silmaril.X86.MemEvent
