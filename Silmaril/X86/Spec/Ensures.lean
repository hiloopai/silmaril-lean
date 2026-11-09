module

public import Silmaril.X86.Ext.Machine
public import Silmaril.X86.Ext.Lemmas

/-!
# An s2n-bignum-style footprint vocabulary over `X86.Ext`

A footprint vocabulary for the memory-backed machine of
`Silmaril/X86/Ext/Machine.lean`. It is modelled on the
*design* of AWS's s2n-bignum (`awslabs2026s2nbignum`) and of ACL2's
x86isa (`goel2016slides`); no HOL Light or ACL2 code is translated,
and `cslib-community/bignum`'s Lean port is AArch64-only and not vendored here.

## The vocabulary

* `Loc` — a location of the machine: a general-purpose register, `rip`, one
  status flag, or a memory range. s2n-bignum's component lenses, flattened to
  a first-order inductive because `Ext.MState` is a concrete pair of a
  register file and a `Process.Memory`.
* `Range` and `Range.Covers` — a `(base, len)` byte range, read **modulo
  2^64**, so the vocabulary is wrap-aware from the start.
* `Separate` (s2n-bignum spells it `nonoverlapping`, x86isa `separate`) — two
  ranges share no byte address. `separate_iff_disjoint` proves it equivalent,
  for ranges that do not wrap, to the interval test
  `b₁ + n₁ ≤ b₂ ∨ b₂ + n₂ ≤ b₁`, which is the shape of
  `Silmaril.Crypto.X86.Regions.Disjoint`; `Silmaril/X86/Spec/EnsuresSysV.lean`
  proves that correspondence against that definition itself.
* `ProgramAt` (s2n-bignum's `bytes_loaded`, x86isa's `program-at`) — the code
  bytes are fetchable *and* readable at an address.
* `MayChange` — everything **not** named by a list of locations agrees between
  two states: the footprint is stated as what may
  change, never as what is preserved; callee-saved preservation is then the
  absence of those registers from the list (`MayChange.reg_eq`).
* `Rel.seq`, written `,,` — relational composition, s2n-bignum's
  `MAYCHANGE ,, MAYCHANGE`. `MayChange.seq_subsumed` is the law that makes a
  chain of per-instruction footprints collapse into one list.
* `Ensures` — partial correctness over `Ext.Returns`, the finite returning run
  already defined in `Ext/Machine.lean`.

## Proof style

Everything in this file is proved by hand in the sense that each lemma has an
explicit proof term or tactic script; but the *work* splits sharply:

* **Automated.** Every arithmetic side condition (`Range` interval reasoning,
  `toNat` bounds, address offsets) goes to `omega`. Register and flag case
  splits go to `decide` or `cases … <;> simp`. No `bv_decide` is needed here:
  the only bitvector content is `BitVec.toNat`, which `omega` handles after
  `simp [BitVec.toNat_add]`.
* **Hand-sequenced.** The read/write algebra (`readBacking_congr`,
  `readWith_sub`, `ProgramAt.fetch_sub`) is written out, because it is an
  induction over a recursive `Option`-valued reader that no tactic finds.
  `Returns.det` — the clock argument that turns "some returning run exists"
  into "this is *the* returning run" — is likewise a hand case split on three
  orderings of the two run lengths.

No proof here uses native evaluation or `bv_decide`.
-/

@[expose] public section

namespace Silmaril.X86.Spec

open Silmaril.X86 (Reg Word Byte State MState Flags)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (loadN storeN storeN_writesOnly)
open Silmaril.Machine.Execution (run run_add)

/-! ## Flags, named -/

/-- The six status flags, as names. `X86.Flags` is a record of six
`Option Bool` fields; a footprint has to talk about them one at a time. -/
inductive FlagName where
  | carry | parity | adjust | zero | sign | overflow
  deriving DecidableEq, Repr

namespace FlagName

/-- Read one named flag. -/
def get : FlagName → Flags → Option Bool
  | .carry, f => f.carry
  | .parity, f => f.parity
  | .adjust, f => f.adjust
  | .zero, f => f.zero
  | .sign, f => f.sign
  | .overflow, f => f.overflow

/-- All six flags. -/
def all : List FlagName := [.carry, .parity, .adjust, .zero, .sign, .overflow]

@[simp] theorem mem_all (f : FlagName) : f ∈ all := by cases f <;> decide

/-- Two flag records agreeing at every name are equal. -/
theorem flags_ext {f g : Flags} (h : ∀ n : FlagName, n.get f = n.get g) : f = g := by
  obtain ⟨c₁, p₁, a₁, z₁, s₁, o₁⟩ := f
  obtain ⟨c₂, p₂, a₂, z₂, s₂, o₂⟩ := g
  have hc := h .carry
  have hp := h .parity
  have ha := h .adjust
  have hz := h .zero
  have hs := h .sign
  have ho := h .overflow
  simp only [get] at hc hp ha hz hs ho
  subst hc; subst hp; subst ha; subst hz; subst hs; subst ho
  rfl

end FlagName

/-! ## Ranges and separation -/

/-- A contiguous byte range `[base, base + len)`, read modulo `2 ^ 64`. -/
structure Range where
  base : Word
  len : Nat
  deriving DecidableEq, Repr

namespace Range

/-- The byte addresses the range covers. Addresses are `Nat` below `2 ^ 64`,
as in `Process.Memory`, and the range wraps there: this is s2n-bignum's
`nonoverlapping_modulo (2 EXP 64)`. -/
def Covers (r : Range) (address : Nat) : Prop :=
  ∃ i, i < r.len ∧ (r.base.toNat + i) % 2 ^ 64 = address

/-- A range that does not wrap past the top of the address space. Every range
a `Process.Memory` access can name is of this kind, because `checkSpan`
rejects `address + length > addressLimit`. -/
def NoWrap (r : Range) : Prop := r.base.toNat + r.len ≤ 2 ^ 64

@[simp] theorem base_mk (b : Word) (n : Nat) : (Range.mk b n).base = b := rfl

@[simp] theorem len_mk (b : Word) (n : Nat) : (Range.mk b n).len = n := rfl

theorem covers_of_lt {r : Range} {i : Nat} (h : i < r.len) :
    r.Covers ((r.base.toNat + i) % 2 ^ 64) := ⟨i, h, rfl⟩

/-- Inside a non-wrapping range, covering is the plain interval test. -/
theorem covers_iff_of_noWrap {r : Range} (hw : r.NoWrap) (address : Nat) :
    r.Covers address ↔ r.base.toNat ≤ address ∧ address < r.base.toNat + r.len := by
  have hb : r.base.toNat < 2 ^ 64 := r.base.isLt
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Nat.mod_eq_of_lt (by unfold NoWrap at hw; omega)]
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨address - r.base.toNat, by omega, ?_⟩
    rw [show r.base.toNat + (address - r.base.toNat) = address by omega]
    exact Nat.mod_eq_of_lt (by unfold NoWrap at hw; omega)

theorem covers_of_mem_noWrap {r : Range} (hw : r.NoWrap) {address : Nat}
    (hlo : r.base.toNat ≤ address) (hhi : address < r.base.toNat + r.len) : r.Covers address :=
  (covers_iff_of_noWrap hw address).mpr ⟨hlo, hhi⟩

@[simp] theorem not_covers_empty (b : Word) (address : Nat) : ¬ (Range.mk b 0).Covers address := by
  rintro ⟨i, hi, -⟩
  exact absurd hi (Nat.not_lt_zero i)

/-- One range sits inside another. -/
def Subset (r s : Range) : Prop := ∀ address, r.Covers address → s.Covers address

theorem subset_of_interval {r s : Range} (hr : r.NoWrap) (hs : s.NoWrap)
    (hlo : s.base.toNat ≤ r.base.toNat)
    (hhi : r.base.toNat + r.len ≤ s.base.toNat + s.len) : r.Subset s := by
  intro address hcov
  rw [covers_iff_of_noWrap hr] at hcov
  exact covers_of_mem_noWrap hs (by omega) (by omega)

end Range

/-- Two ranges share no byte address. This is s2n-bignum's `nonoverlapping`
and x86isa's `separate`, stated semantically so that it is wrap-aware without
a case split in the definition. -/
def Separate (r s : Range) : Prop := ∀ address, r.Covers address → ¬ s.Covers address

/-- s2n-bignum's spelling. -/
abbrev Nonoverlapping : Range → Range → Prop := Separate

namespace Separate

theorem symm {r s : Range} (h : Separate r s) : Separate s r :=
  fun address hs hr => h address hr hs

theorem mono_left {r r' s : Range} (h : Separate r' s) (hsub : r.Subset r') : Separate r s :=
  fun address hr => h address (hsub address hr)

theorem mono_right {r s s' : Range} (h : Separate r s') (hsub : s.Subset s') : Separate r s :=
  fun address hr hs => h address hr (hsub address hs)

@[simp] theorem empty_left (b : Word) (s : Range) : Separate ⟨b, 0⟩ s := by
  intro address hcov
  exact absurd hcov (Range.not_covers_empty b address)

@[simp] theorem empty_right (r : Range) (b : Word) : Separate r ⟨b, 0⟩ :=
  (empty_left b r).symm

end Separate

/-- The interval test of `Silmaril.Crypto.X86.Regions.Disjoint`, in `Nat`. -/
def Range.Disjoint (r s : Range) : Prop :=
  r.base.toNat + r.len ≤ s.base.toNat ∨ s.base.toNat + s.len ≤ r.base.toNat

/-- Disjoint non-wrapping intervals are separate. -/
theorem separate_of_disjoint {r s : Range} (hr : r.NoWrap) (hs : s.NoWrap)
    (h : r.Disjoint s) : Separate r s := by
  intro address hcr hcs
  rw [Range.covers_iff_of_noWrap hr] at hcr
  rw [Range.covers_iff_of_noWrap hs] at hcs
  unfold Range.Disjoint at h
  omega

/-- The converse, for nonempty ranges: `Separate` *is* interval disjointness.
Emptiness is the only obstruction — an empty range is separate from
everything but need not sit outside it. -/
theorem disjoint_of_separate {r s : Range} (hr : r.NoWrap) (hs : s.NoWrap)
    (hrpos : 0 < r.len) (hspos : 0 < s.len) (h : Separate r s) : r.Disjoint s := by
  by_contra hcon
  have h1 : ¬ (r.base.toNat + r.len ≤ s.base.toNat) := fun hd => hcon (Or.inl hd)
  have h2 : ¬ (s.base.toNat + s.len ≤ r.base.toNat) := fun hd => hcon (Or.inr hd)
  -- the two intervals overlap, so pick a common address
  rcases Nat.le_total r.base.toNat s.base.toNat with hle | hle
  · exact h s.base.toNat (Range.covers_of_mem_noWrap hr hle (by omega))
      (Range.covers_of_mem_noWrap hs (Nat.le_refl _) (by omega))
  · exact h r.base.toNat (Range.covers_of_mem_noWrap hr (Nat.le_refl _) (by omega))
      (Range.covers_of_mem_noWrap hs hle (by omega))

/-- `Separate` and interval disjointness agree on nonempty non-wrapping
ranges (the interval test of `Regions.Disjoint`). -/
theorem separate_iff_disjoint {r s : Range} (hr : r.NoWrap) (hs : s.NoWrap)
    (hrpos : 0 < r.len) (hspos : 0 < s.len) : Separate r s ↔ r.Disjoint s :=
  ⟨disjoint_of_separate hr hs hrpos hspos, separate_of_disjoint hr hs⟩

/-! ## Locations -/

/-- A location of the machine state. s2n-bignum's components, as data. -/
inductive Loc where
  /-- One of the sixteen general-purpose registers. -/
  | reg (r : Reg)
  /-- The instruction pointer. -/
  | rip
  /-- One status flag. -/
  | flag (f : FlagName)
  /-- A range of memory bytes. -/
  | mem (r : Range)
  deriving DecidableEq, Repr

namespace Loc

/-- `Loc.mem` from a base and a length. -/
abbrev bytes (base : Word) (len : Nat) : Loc := .mem ⟨base, len⟩

/-- All six flags, as locations. -/
def allFlags : List Loc := FlagName.all.map Loc.flag

theorem mem_allFlags (f : FlagName) : Loc.flag f ∈ allFlags := by
  cases f <;> decide

/-- This location holds the same value in both states. -/
def Preserved : Loc → MState → MState → Prop
  | .reg r, a, b => b.core.read r = a.core.read r
  | .rip, a, b => b.core.rip = a.core.rip
  | .flag f, a, b => f.get b.core.flags = f.get a.core.flags
  | .mem r, a, b => ∀ address, r.Covers address →
      b.memory.bytes.get? address = a.memory.bytes.get? address

end Loc

/-- Some memory location in the list covers this byte address. -/
def Locs.CoversAddr (locs : List Loc) (address : Nat) : Prop :=
  ∃ r : Range, Loc.mem r ∈ locs ∧ r.Covers address

theorem Locs.coversAddr_of_mem {locs : List Loc} {r : Range} (hmem : Loc.mem r ∈ locs)
    {address : Nat} (hcov : r.Covers address) : Locs.CoversAddr locs address :=
  ⟨r, hmem, hcov⟩

theorem Locs.coversAddr_mono {locs locs' : List Loc} (hsub : ∀ l ∈ locs, l ∈ locs')
    {address : Nat} (h : Locs.CoversAddr locs address) : Locs.CoversAddr locs' address := by
  obtain ⟨r, hmem, hcov⟩ := h
  exact ⟨r, hsub _ hmem, hcov⟩

/-! ## The read/write algebra

The four families of `goel2016slides`, at the level this model needs: a
congruence for the recursive backing reader, a sub-span rule for checked
reads, and the transfer of permissions across a `MayChange`. -/

namespace Memory

open Silmaril.Process

/-- Byte-wise agreement over a span gives the same backing read. -/
theorem readBacking_congr {m₁ m₂ : Process.ByteMemory} (address length : Nat)
    (h : ∀ i, i < length → m₁.get? (address + i) = m₂.get? (address + i)) :
    Process.Memory.readBacking m₁ address length =
      Process.Memory.readBacking m₂ address length := by
  induction length generalizing address with
  | zero => rfl
  | succ length ih =>
    have head := h 0 (by omega)
    have tail : ∀ i, i < length → m₁.get? (address + 1 + i) = m₂.get? (address + 1 + i) := by
      intro i hi
      have := h (i + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    simp only [Process.Memory.readBacking, Nat.add_zero] at head ⊢
    rw [head, ih (address + 1) tail]

/-- A checked read of a sub-span of a successful checked read succeeds and
returns the corresponding slice. This is x86isa's `rb-rb-split-reads`. -/
theorem readWith_sub {memory : Process.Memory} {access : Process.Access} {address length : Nat}
    {bs : List Byte} (h : memory.readWith access address length = some bs)
    {off n : Nat} (hn : 0 < n) (hle : off + n ≤ length) :
    memory.readWith access (address + off) n = some ((bs.drop off).take n) := by
  have hlen : bs.length = length := Process.Memory.readWith_length h
  have hperm := Process.Memory.readWith_permitted h
  rw [Process.Memory.Permitted, Process.Memory.checkSpan_iff] at hperm
  obtain ⟨hstart, hlimit, hpermits⟩ := hperm
  have hsliceLen : ((bs.drop off).take n).length = n := by
    simp only [List.length_take, List.length_drop, hlen]
    omega
  have hsub : memory.Permitted access (address + off) n := by
    rw [Process.Memory.Permitted, Process.Memory.checkSpan_iff]
    refine ⟨by omega, by omega, ?_⟩
    intro offset hoffset
    have := hpermits (off + offset) (by omega)
    simpa [Nat.add_assoc] using this
  have hbacking : ∀ index (bound : index < ((bs.drop off).take n).length),
      memory.bytes.get? (address + off + index) = some (((bs.drop off).take n)[index]) := by
    intro index bound
    rw [hsliceLen] at bound
    have hidx : off + index < bs.length := by omega
    have := Process.Memory.readWith_get h (off + index) hidx
    rw [show address + (off + index) = address + off + index by omega] at this
    rw [this]
    congr 1
    simp [List.getElem_take, List.getElem_drop]
  have := Process.Memory.readWith_eq memory access (address + off) ((bs.drop off).take n)
    (by rw [hsliceLen]; exact hsub) hbacking
  rwa [hsliceLen] at this

end Memory

/-! ## `ProgramAt` -/

/-- The code bytes are loaded at `addr`: fetchable (hence mapped executable and
backed) and readable. s2n-bignum's `bytes_loaded`, x86isa's `program-at`. -/
structure ProgramAt (m : MState) (addr : Word) (code : List Byte) : Prop where
  /-- The bytes fetch, so they are mapped executable and backed. -/
  fetch : m.memory.fetchBytes addr.toNat code.length = some code
  /-- The same span is readable, which is what a `.rodata`-adjacent constant
  pool or a self-inspecting routine needs. -/
  readable : m.memory.Permitted .read addr.toNat code.length

namespace ProgramAt

variable {m : MState} {addr : Word} {code : List Byte}

/-- A loaded program does not wrap. -/
theorem noWrap (h : ProgramAt m addr code) : (Range.mk addr code.length).NoWrap := by
  have := Process.Memory.readWith_permitted h.fetch
  rw [Process.Memory.Permitted, Process.Memory.checkSpan_iff] at this
  exact this.2.1

/-- Each instruction's bytes fetch on their own. This is the step that lets a
symbolic run use `Ext.step_of_fetch` without unfolding `fetch`. -/
theorem fetch_sub (h : ProgramAt m addr code) {off n : Nat} (hn : 0 < n)
    (hle : off + n ≤ code.length) :
    m.memory.fetchBytes (addr.toNat + off) n = some ((code.drop off).take n) :=
  Memory.readWith_sub h.fetch hn hle

/-- One symbolic step of a loaded program: at `rip = addr + off`, the machine
executes exactly the instruction the code bytes decode to there. -/
theorem step_eq {exit : Word} (h : ProgramAt m addr code) {off n : Nat} {instr : Ext.Instr}
    (hrip : m.core.rip.toNat = addr.toNat + off) (hle : off + n ≤ code.length)
    (hdec : Ext.decode ((code.drop off).take n) = some (instr, n)) :
    Ext.step exit m =
      match Ext.exec instr m.core m.memory with
      | .ok core memory =>
        if instr = Ext.Instr.ret ∧ core.rip = exit then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault instr
      | .divideError => .divideFault
      | .undefinedCondition c => .undefinedCondition c
      | .trap => .trapped := by
  obtain ⟨-, hpos, -, -⟩ := Ext.decode_length hdec
  refine Ext.step_of_fetch ?_ hdec
  rw [hrip]
  exact h.fetch_sub hpos hle

/-- `ProgramAt` depends only on the memory: any state whose mapping and code
bytes agree is still loaded. -/
theorem congr {m' : MState} (h : ProgramAt m addr code)
    (hregions : m'.memory.regions = m.memory.regions)
    (hbytes : ∀ i, i < code.length →
      m'.memory.bytes.get? (addr.toNat + i) = m.memory.bytes.get? (addr.toNat + i)) :
    ProgramAt m' addr code := by
  have hperm : m'.memory.Permitted .execute addr.toNat code.length := by
    show m'.memory.checkSpan .execute addr.toNat code.length = true
    rw [X86.Memory.checkSpan_congr hregions]
    exact Process.Memory.readWith_permitted h.fetch
  refine ⟨Process.Memory.readWith_eq m'.memory .execute addr.toNat code hperm ?_, ?_⟩
  · intro index bound
    rw [hbytes index bound]
    exact Process.Memory.readWith_get h.fetch index bound
  · show m'.memory.checkSpan .read addr.toNat code.length = true
    rw [X86.Memory.checkSpan_congr hregions]
    exact h.readable

/-- Only the memory matters. -/
theorem of_memory_eq {m' : MState} (h : ProgramAt m addr code) (he : m'.memory = m.memory) :
    ProgramAt m' addr code := h.congr (by rw [he]) (fun _ _ => by rw [he])

/-- The retiring case, packaged: at a decoded non-`ret` instruction whose
execution succeeds, the machine retires into the computed state. -/
theorem step_retired {exit : Word} (h : ProgramAt m addr code) {off n : Nat} {instr : Ext.Instr}
    {t : State} {mem' : Process.Memory}
    (hrip : m.core.rip.toNat = addr.toNat + off) (hle : off + n ≤ code.length)
    (hdec : Ext.decode ((code.drop off).take n) = some (instr, n)) (hne : instr ≠ Ext.Instr.ret)
    (hexec : Ext.exec instr m.core m.memory = .ok t mem') :
    Ext.step exit m = .retired ⟨t, mem'⟩ := by
  rw [h.step_eq hrip hle hdec, hexec]
  simp [hne]

/-- The returning case: a `ret` whose popped target is the designated exit. -/
theorem step_returned {exit : Word} (h : ProgramAt m addr code) {off n : Nat}
    {t : State} {mem' : Process.Memory}
    (hrip : m.core.rip.toNat = addr.toNat + off) (hle : off + n ≤ code.length)
    (hdec : Ext.decode ((code.drop off).take n) = some (Ext.Instr.ret, n))
    (hexec : Ext.exec Ext.Instr.ret m.core m.memory = .ok t mem') (hexit : t.rip = exit) :
    Ext.step exit m = .returned ⟨t, mem'⟩ := by
  rw [h.step_eq hrip hle hdec, hexec]
  simp [hexit]

end ProgramAt

/-! ## Address arithmetic

Two facts that every symbolic run needs: `rip + length` stays `rip + length` in
`Nat` as long as the code does not reach the top of the address space, and
successive increments add. -/

/-- A non-wrapping `Word` offset is `Nat` addition. -/
theorem toNat_add_ofNat {b : Word} {off : Nat} (h : b.toNat + off < 2 ^ 64) :
    (b + BitVec.ofNat 64 off).toNat = b.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt h

/-- Successive `rip` increments accumulate. -/
theorem add_ofNat_add (b : Word) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

/-- Widening a 64-bit word to 64 bits changes nothing; `exec_store` phrases a
stored 64-bit value this way. -/
@[simp] theorem setWidth64_self (x : Word) : BitVec.setWidth 64 x = x := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth]
  omega

/-- Truncating a zero-extended 32-bit value gives it back; this is what a
32-bit argument spilled to a four-byte slot and reloaded does. -/
@[simp] theorem setWidth32_setWidth64 (b : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 b) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

/-! ## The `clang -O0` frame idiom

Every `-O0` function in the benchmark set spills its arguments to `rbp`-relative
slots and reloads them. Naming the operand shape once keeps the `decide`d
decodes and the `bv_decide`d address identities syntactically equal across
benchmarks. -/

/-- `-d(%rbp)`: a `clang -O0` frame slot. -/
def fslot (d : BitVec 32) : Ext.Mem := Ext.Mem.ofReg .rbp none d

theorem fslot_addr (s : State) (next : Word) (d : BitVec 32) :
    (fslot d).addr s next = s.read .rbp + d.signExtend 64 := by
  simp [fslot, Ext.Mem.addr, Ext.Mem.ofReg]

/-- Successive `rip` increments, with the sum checked by `rfl` at the call
site. -/
theorem ripStep (b : Word) (x y z : Nat) (h : x + y = z) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 z := by
  rw [add_ofNat_add, h]

/-- `rip = addr + off` in `Nat`, which is what `ProgramAt.step_retired`
consumes. The `hlen` argument lets a benchmark pass its own `code_length`. -/
theorem ProgramAt.ripNat {m : MState} {addr : Word} {code : List Byte} {off n : Nat}
    (h : ProgramAt m addr code) (hlen : code.length = n)
    (hrip : m.core.rip = addr + BitVec.ofNat 64 off) (hoff : off < n) :
    m.core.rip.toNat = addr.toNat + off := by
  have hw := h.noWrap
  rw [Range.NoWrap] at hw
  simp only [hlen] at hw
  rw [hrip, toNat_add_ofNat (by omega)]

/-! ## The write algebra of `Process.Memory`

Existence of a store from a write permission, transfer of permissions across a
store, and sub-span permissions. These are the remaining members of the
`goel2016slides` rule families that this model needs. -/

/-- A sub-span of a permitted span is permitted. -/
theorem permitted_sub {memory : Process.Memory} {access : Process.Access} {a n b k : Nat}
    (h : memory.Permitted access a n) (hpos : 0 < k) (hlo : a ≤ b) (hhi : b + k ≤ a + n) :
    memory.Permitted access b k := by
  rw [Process.Memory.Permitted, Process.Memory.checkSpan_iff] at h ⊢
  obtain ⟨hstart, hlimit, hpermits⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  intro offset hoffset
  have := hpermits (b - a + offset) (by omega)
  rwa [show a + (b - a + offset) = b + offset by omega] at this

/-- A write-permitted span can be stored to. -/
theorem storeN_of_permitted {memory : Process.Memory} {address : Word} {k : Nat} (v : Word)
    (h : memory.Permitted .write address.toNat k) :
    ∃ after, storeN memory address k v = some after := by
  have hc : memory.checkSpan .write address.toNat (Ext.leBytes v k).length = true := by
    rw [Ext.length_leBytes]; exact h
  refine ⟨{ memory with
    bytes := Process.Memory.install memory.bytes address.toNat (Ext.leBytes v k) }, ?_⟩
  simp only [storeN, Process.Memory.writeBytes, hc, ite_true]

/-- A store does not change any permission. -/
theorem storeN_permitted {memory after : Process.Memory} {address : Word} {k : Nat} {v : Word}
    (hst : storeN memory address k v = some after) {access : Process.Access} {a n : Nat}
    (hp : memory.Permitted access a n) : after.Permitted access a n := by
  show after.checkSpan access a n = true
  rw [X86.Memory.checkSpan_congr (storeN_writesOnly hst).1]
  exact hp

/-- A store names a span `Process.Memory` accepted, so it does not wrap. -/
theorem storeN_noWrap {memory after : Process.Memory} {address : Word} {k : Nat} {v : Word}
    (hst : storeN memory address k v = some after) : (Range.mk address k).NoWrap := by
  have := Process.Memory.writeBytes_permitted hst
  rw [Ext.length_leBytes, Process.Memory.Permitted, Process.Memory.checkSpan_iff] at this
  exact this.2.1

/-- A loaded program survives a store separate from its bytes. x86isa's
`program-at-wb-disjoint`, in the form a symbolic run uses. -/
theorem ProgramAt.of_storeN {m m' : MState} {addr target : Word} {code : List Byte} {k : Nat}
    {v : Word} (h : ProgramAt m addr code) (hst : storeN m.memory target k v = some m'.memory)
    (hsep : Separate ⟨target, k⟩ ⟨addr, code.length⟩) : ProgramAt m' addr code := by
  have hframe := storeN_writesOnly hst
  have hwrap := storeN_noWrap hst
  refine h.congr hframe.1 ?_
  intro i hi
  refine hframe.2 _ ?_
  by_contra hcon
  refine hsep (addr.toNat + i) ?_ (Range.covers_of_mem_noWrap h.noWrap
    (show addr.toNat ≤ addr.toNat + i from Nat.le_add_right _ _)
    (show addr.toNat + i < addr.toNat + code.length from by omega))
  exact Range.covers_of_mem_noWrap hwrap
    (show target.toNat ≤ addr.toNat + i by omega)
    (show addr.toNat + i < target.toNat + k by omega)

/-- Read-over-write, disjoint, at the level of raw byte reads. -/
theorem readBytes_storeN_disjoint {memory after : Process.Memory} {address : Word} {k : Nat}
    {v : Word} (hst : storeN memory address k v = some after) (a n : Nat)
    (hd : a + n ≤ address.toNat ∨ address.toNat + k ≤ a) :
    after.readBytes a n = memory.readBytes a n :=
  X86.Memory.readWith_writesOnly (storeN_writesOnly hst) .read a n hd

/-! ## The stack: `push` and `pop` as stores and loads

`X86.pushWord` writes `encodeWords [v]`, which is exactly `storeN … 8 v`
(`leBytes_eight`), so the whole store algebra applies to the stack too.
`WordAt` names the eight bytes a `pop` or a `ret` will read. -/

/-- `pushWord` is an eight-byte `storeN` at `rsp − 8`. -/
theorem pushWord_eq_storeN (s : State) (memory : Process.Memory) (v : Word) :
    X86.pushWord s memory v =
      (storeN memory (s.read .rsp - 8#64) 8 v).map
        fun after => (s.write .rsp (s.read .rsp - 8#64), after) := by
  simp [X86.pushWord, storeN, Ext.leBytes_eight]

/-- The eight bytes at `address` are the little-endian encoding `popWord`
reads as `v`. -/
def WordAt (memory : Process.Memory) (address : Word) (v : Word) : Prop :=
  ∃ bs, memory.readBytes address.toNat 8 = some bs ∧ X86.wordOfBytes? bs = some v

namespace WordAt

/-- What a `pop` or a `ret` sees. -/
theorem popWord {s : State} {memory : Process.Memory} {v : Word}
    (h : WordAt memory (s.read .rsp) v) :
    X86.popWord s memory = some (v, s.write .rsp (s.read .rsp + 8#64)) := by
  obtain ⟨bs, hread, hword⟩ := h
  simp [X86.popWord, hread, hword]

/-- A `push` establishes `WordAt` at the new top of stack. -/
theorem of_pushWord {s t : State} {memory after : Process.Memory} {v : Word}
    (h : X86.pushWord s memory v = some (t, after))
    (readable : memory.Permitted .read (s.read .rsp - 8#64).toNat 8) :
    WordAt after (s.read .rsp - 8#64) v :=
  ⟨Machine.LittleEndian.encodeWords [v], X86.pushWord_readBytes h readable, by simp⟩

/-- An eight-byte `storeN` establishes `WordAt`. -/
theorem of_storeN {memory after : Process.Memory} {address v : Word}
    (hst : storeN memory address 8 v = some after)
    (readable : memory.Permitted .read address.toNat 8) : WordAt after address v := by
  have hst' : memory.writeBytes address.toNat (Machine.LittleEndian.encodeWords [v]) =
      some after := by rw [← Ext.leBytes_eight v]; exact hst
  have hlen : (Machine.LittleEndian.encodeWords [v]).length = 8 := by simp
  have key := Process.Memory.readWith_eq after .read address.toNat
    (Machine.LittleEndian.encodeWords [v]) (by rw [hlen]; exact storeN_permitted hst readable)
    (fun index bound => Process.Memory.writeBytes_get hst' index bound)
  rw [hlen] at key
  exact ⟨_, key, by simp⟩

/-- `WordAt` survives a disjoint store. -/
theorem of_storeN_disjoint {memory after : Process.Memory} {address target : Word} {k : Nat}
    {v w : Word} (h : WordAt memory target w) (hst : storeN memory address k v = some after)
    (hd : target.toNat + 8 ≤ address.toNat ∨ address.toNat + k ≤ target.toNat) :
    WordAt after target w := by
  obtain ⟨bs, hread, hword⟩ := h
  exact ⟨bs, by rw [readBytes_storeN_disjoint hst target.toNat 8 hd]; exact hread, hword⟩

end WordAt

/-! ## Readable ranges

`Process.Memory` can permit a read and still have no backing byte, in which
case the load faults. A precondition that says "this buffer reads" is
therefore `Readable`, not `Permitted .read`; s2n-bignum's
`read (memory :> bytes (x,n)) s = a` presupposes the same thing. -/

/-- Every byte of the range is permitted and backed. -/
def Readable (memory : Process.Memory) (r : Range) : Prop :=
  ∃ bs, memory.readBytes r.base.toNat r.len = some bs

namespace Readable

theorem permitted {memory : Process.Memory} {r : Range} (h : Readable memory r) :
    memory.Permitted .read r.base.toNat r.len := by
  obtain ⟨bs, hbs⟩ := h
  exact Process.Memory.readWith_permitted hbs

theorem noWrap {memory : Process.Memory} {r : Range} (h : Readable memory r) : r.NoWrap := by
  have := h.permitted
  rw [Process.Memory.Permitted, Process.Memory.checkSpan_iff] at this
  exact this.2.1

/-- Each byte of a readable range loads. -/
theorem loadByte {memory : Process.Memory} {r : Range} (h : Readable memory r) {j : Nat}
    (hj : j < r.len) : ∃ b, loadN memory (r.base + BitVec.ofNat 64 j) 1 = some b := by
  have hw := h.noWrap
  obtain ⟨bs, hbs⟩ := h
  have hjlt : r.base.toNat + j < 2 ^ 64 := by
    have := r.base.isLt
    unfold Range.NoWrap at hw
    omega
  have := Memory.readWith_sub hbs (n := 1) (off := j) (by omega) (by omega)
  refine ⟨BitVec.ofNat 64 (Ext.leValue ((bs.drop j).take 1)), ?_⟩
  simp only [loadN, Process.Memory.readBytes, toNat_add_ofNat hjlt, this, Option.map_some]

/-- Readability survives a disjoint store. -/
theorem of_storeN_disjoint {memory after : Process.Memory} {address : Word} {k : Nat}
    {v : Word} {r : Range} (h : Readable memory r) (hst : storeN memory address k v = some after)
    (hd : r.base.toNat + r.len ≤ address.toNat ∨ address.toNat + k ≤ r.base.toNat) :
    Readable after r := by
  obtain ⟨bs, hbs⟩ := h
  exact ⟨bs, by rw [readBytes_storeN_disjoint hst r.base.toNat r.len hd]; exact hbs⟩

end Readable

/-- A non-wrapping subtraction is `Nat` subtraction. -/
theorem toNat_sub_ofNat {b : Word} {k : Nat} (hk : k ≤ b.toNat) (hlt : k < 2 ^ 64) :
    (b - BitVec.ofNat 64 k).toNat = b.toNat - k := by
  have := b.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  omega

/-! ## Instruction forms `Ext/Lemmas.lean` does not cover

`Silmaril/X86/Ext/Lemmas.lean` states the register-direct forms a code
generator emits. A `clang -O0` frame uses four more shapes: an immediate store,
a byte load from an indexed address, a compare against memory, and the three
stack instructions expressed through the store algebra above. -/

/-- `mov dword ptr [m], imm32` / `mov qword ptr [m], imm32` (`C7 /0 id`). -/
theorem exec_movI_mem (sz : Ext.Sz) (mm : Ext.Mem) (imm : BitVec 32) (s : State)
    (memory : Process.Memory) :
    Ext.exec (.movI sz (.mem mm) imm) s memory =
      (match storeN memory
          (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.movI sz (.mem mm) imm).length))
          sz.bytes ((imm.signExtend sz.bits).setWidth 64) with
        | some after => .ok { s with
            rip := s.rip + BitVec.ofNat 64 (Ext.Instr.movI sz (.mem mm) imm).length } after
        | none => .dataFault) := by
  simp only [Ext.exec, Ext.writeRM]
  cases storeN memory
      (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.movI sz (.mem mm) imm).length))
      sz.bytes ((imm.signExtend sz.bits).setWidth 64) <;> rfl

/-- `mov r8, byte ptr [m]` (`8A /r` with a memory operand). -/
theorem exec_mov8_mem (dst : Reg) (mm : Ext.Mem) (s : State) (memory : Process.Memory) :
    Ext.exec (.mov8 dst (.mem mm)) s memory =
      (match loadN memory
          (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.mov8 dst (.mem mm)).length)) 1 with
        | some v => .ok { Ext.writeByte s dst (v.setWidth 8) with
            rip := s.rip + BitVec.ofNat 64 (Ext.Instr.mov8 dst (.mem mm)).length } memory
        | none => .dataFault) := by
  have hb : Ext.Narrow.b.bytes = 1 := rfl
  simp only [Ext.exec, Ext.readNarrow, hb]
  cases loadN memory
      (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.mov8 dst (.mem mm)).length)) 1 <;> rfl

/-- `op reg, [m]` for a non-compare `op` (`03 0B 23 2B 33 /r`). -/
theorem exec_aluR_mem (sz : Ext.Sz) (op : X86.AluOp) (dst : Reg) (mm : Ext.Mem) (s : State)
    (memory : Process.Memory) (hop : op ≠ .cmp) :
    Ext.exec (.aluR sz op dst (.mem mm)) s memory =
      (match loadN memory
          (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz op dst (.mem mm)).length))
          sz.bytes with
        | some v => .ok { sz.write s dst (Ext.AluOp.resultN op (sz.read s dst) (v.setWidth sz.bits))
            with
            flags := Ext.AluOp.flagsN op (sz.read s dst) (v.setWidth sz.bits)
            rip := s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz op dst (.mem mm)).length } memory
        | none => .dataFault) := by
  simp only [Ext.exec, Ext.aluStepR, Ext.readRM]
  cases loadN memory
      (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz op dst (.mem mm)).length))
      sz.bytes with
  | none => rfl
  | some v =>
    simp only [Option.map_some, hop, reduceIte]
    rfl

/-- `cmp reg, [m]` (`3B /r`), the direction-1 compare against memory. -/
theorem exec_cmpR_mem (sz : Ext.Sz) (dst : Reg) (mm : Ext.Mem) (s : State)
    (memory : Process.Memory) :
    Ext.exec (.aluR sz .cmp dst (.mem mm)) s memory =
      (match loadN memory
          (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz .cmp dst (.mem mm)).length))
          sz.bytes with
        | some v => .ok { s with
            flags := Ext.subFlagsN (sz.read s dst) (v.setWidth sz.bits)
            rip := s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz .cmp dst (.mem mm)).length } memory
        | none => .dataFault) := by
  simp only [Ext.exec, Ext.aluStepR, Ext.readRM, Ext.AluOp.flagsN]
  cases loadN memory
      (mm.addr s (s.rip + BitVec.ofNat 64 (Ext.Instr.aluR sz .cmp dst (.mem mm)).length))
      sz.bytes <;> rfl

/-- `push r64`, as an eight-byte store at `rsp − 8`. -/
theorem exec_push_eq {s : State} {memory after : Process.Memory} {src : Reg} {n : Nat}
    (hlen : (Ext.Instr.push src).length = n)
    (hst : storeN memory (s.read .rsp - 8#64) 8 (s.read src) = some after) :
    Ext.exec (.push src) s memory =
      .ok { s.write .rsp (s.read .rsp - 8#64) with
            rip := s.rip + BitVec.ofNat 64 n } after := by
  have hl : (X86.Insn.push src).length = n := by
    rw [← hlen]; exact (Ext.length_ofInsn (X86.Insn.push src)).symm
  rw [Ext.exec_push]
  simp only [X86.Insn.exec, hl, pushWord_eq_storeN, hst, Option.map_some]

/-- `pop r64`, as an eight-byte load at `rsp`. -/
theorem exec_pop_eq {s : State} {memory : Process.Memory} {dst : Reg} {v : Word} {n : Nat}
    (hlen : (Ext.Instr.pop dst).length = n) (hw : WordAt memory (s.read .rsp) v) :
    Ext.exec (.pop dst) s memory =
      .ok { (s.write .rsp (s.read .rsp + 8#64)).write dst v with
            rip := s.rip + BitVec.ofNat 64 n } memory := by
  have hl : (X86.Insn.pop dst).length = n := by
    rw [← hlen]; exact (Ext.length_ofInsn (X86.Insn.pop dst)).symm
  rw [Ext.exec_pop]
  simp only [X86.Insn.exec, hl, hw.popWord, Option.map_some]

/-- `ret`, as an eight-byte load at `rsp` followed by a jump to it. -/
theorem exec_ret_eq {s : State} {memory : Process.Memory} {v : Word}
    (hw : WordAt memory (s.read .rsp) v) :
    Ext.exec .ret s memory =
      .ok { s.write .rsp (s.read .rsp + 8#64) with rip := v } memory := by
  rw [Ext.exec_ret]
  simp only [X86.Insn.exec, hw.popWord, Option.map_some]

/-! ## Record-update simp lemmas

A symbolic run builds a nest of `State` updates; these let `simp` read a
register, a flag or `rip` straight off it. -/

/-- A record update keeps the register file, whatever it does to the other
fields. This is the lemma that lets `simp` read a register off a nest of
`{ … with rip := … }` updates: the elaborated form is a `State.mk` whose first
field is `s.regs`, so the pattern has to be stated that way.

Every field after `regs` is quantified rather than pinned to `s`'s, so that
adding a field to `X86.State` cannot silently stop this matching — it only
costs one more binder (as `fsBase` once did). -/
@[simp] theorem read_mk (s : State) (rip : Word) (flags : Flags) (fsBase : Word) (r : Reg) :
    (State.mk s.regs rip flags fsBase).read r = s.read r := rfl

@[simp] theorem rip_write (s : State) (r : Reg) (v : Word) : (s.write r v).rip = s.rip := rfl

@[simp] theorem flags_write (s : State) (r : Reg) (v : Word) : (s.write r v).flags = s.flags := rfl

/-! ## `MayChange` -/

/-- Everything *not* named by `locs` agrees between `before` and `after`. A
footprint is a may-change set, and preservation of a
register, a flag or a byte is its absence from that set.

The memory clause also fixes the mapping metadata, because a routine that
remapped memory would change what every other address means. -/
structure MayChange (locs : List Loc) (before after : MState) : Prop where
  /-- A register not in the list is unchanged. -/
  regs : ∀ r : Reg, Loc.reg r ∉ locs → after.core.read r = before.core.read r
  /-- `rip` is unchanged unless listed. -/
  rip : Loc.rip ∉ locs → after.core.rip = before.core.rip
  /-- A flag not in the list is unchanged. -/
  flags : ∀ f : FlagName, Loc.flag f ∉ locs →
    f.get after.core.flags = f.get before.core.flags
  /-- No mapping is created, destroyed or repermissioned. -/
  regions : after.memory.regions = before.memory.regions
  /-- A byte no listed range covers is unchanged. -/
  bytes : ∀ address : Nat, ¬ Locs.CoversAddr locs address →
    after.memory.bytes.get? address = before.memory.bytes.get? address

namespace MayChange

variable {locs locs' : List Loc} {a b c : MState}

@[refl] theorem refl (locs : List Loc) (m : MState) : MayChange locs m m :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

theorem trans (h₁ : MayChange locs a b) (h₂ : MayChange locs b c) : MayChange locs a c :=
  ⟨fun r hr => (h₂.regs r hr).trans (h₁.regs r hr),
   fun hr => (h₂.rip hr).trans (h₁.rip hr),
   fun f hf => (h₂.flags f hf).trans (h₁.flags f hf),
   h₂.regions.trans h₁.regions,
   fun address hcov => (h₂.bytes address hcov).trans (h₁.bytes address hcov)⟩

/-- Monotone in the location list: a larger footprint claims less. -/
theorem mono (h : MayChange locs a b) (hsub : ∀ l ∈ locs, l ∈ locs') : MayChange locs' a b :=
  ⟨fun r hr => h.regs r fun hm => hr (hsub _ hm),
   fun hr => h.rip fun hm => hr (hsub _ hm),
   fun f hf => h.flags f fun hm => hf (hsub _ hm),
   h.regions,
   fun address hcov => h.bytes address fun hc => hcov (Locs.coversAddr_mono hsub hc)⟩

/-- Shrink the footprint by exhibiting, for each location dropped, that it was
preserved after all. This is how a `push`/`pop` pair removes a callee-saved
register from the body's may-change set — s2n-bignum does the same inside
`X86_PROMOTE_RETURN_STACK_TAC`. -/
theorem narrow (h : MayChange locs a b)
    (hpres : ∀ l ∈ locs, l ∉ locs' → l.Preserved a b) : MayChange locs' a b := by
  refine ⟨?_, ?_, ?_, h.regions, ?_⟩
  · intro r hr
    by_cases hm : Loc.reg r ∈ locs
    · exact hpres _ hm hr
    · exact h.regs r hm
  · intro hr
    by_cases hm : Loc.rip ∈ locs
    · exact hpres _ hm hr
    · exact h.rip hm
  · intro f hf
    by_cases hm : Loc.flag f ∈ locs
    · exact hpres _ hm hf
    · exact h.flags f hm
  · intro address hcov
    by_cases hc : Locs.CoversAddr locs address
    · obtain ⟨r, hmem, hcovr⟩ := hc
      have hnot : Loc.mem r ∉ locs' := fun hm => hcov ⟨r, hm, hcovr⟩
      exact hpres _ hmem hnot address hcovr
    · exact h.bytes address hc

/-- The general monotonicity law: a footprint claims less whenever it leaves
fewer registers, flags and byte addresses out. `mono` is the special case of a
larger list, `widen_range` the special case of a larger range. -/
theorem mono_cover (h : MayChange locs a b)
    (hreg : ∀ r : Reg, Loc.reg r ∉ locs' → Loc.reg r ∉ locs)
    (hrip : Loc.rip ∉ locs' → Loc.rip ∉ locs)
    (hflag : ∀ f : FlagName, Loc.flag f ∉ locs' → Loc.flag f ∉ locs)
    (hmem : ∀ address, ¬ Locs.CoversAddr locs' address → ¬ Locs.CoversAddr locs address) :
    MayChange locs' a b :=
  ⟨fun r hr => h.regs r (hreg r hr), fun hr => h.rip (hrip hr),
   fun f hf => h.flags f (hflag f hf), h.regions,
   fun address hcov => h.bytes address (hmem address hcov)⟩

/-- Widen a memory range inside the footprint. The red-zone statement is this
lemma applied to `[rsp − 32, rsp) ⊆ [rsp − 128, rsp)`. -/
theorem widen_range {r r' : Range} {rest : List Loc}
    (h : MayChange (Loc.mem r :: rest) a b) (hsub : r.Subset r') :
    MayChange (Loc.mem r' :: rest) a b := by
  refine h.mono_cover ?_ ?_ ?_ ?_
  · intro q hq hmem
    exact hq (by rcases List.mem_cons.mp hmem with h | h
                 · exact absurd h (by simp)
                 · exact List.mem_cons_of_mem _ h)
  · intro hq hmem
    exact hq (by rcases List.mem_cons.mp hmem with h | h
                 · exact absurd h (by simp)
                 · exact List.mem_cons_of_mem _ h)
  · intro f hf hmem
    exact hf (by rcases List.mem_cons.mp hmem with h | h
                 · exact absurd h (by simp)
                 · exact List.mem_cons_of_mem _ h)
  · rintro address hq ⟨q, hmem, hcov⟩
    rcases List.mem_cons.mp hmem with heq | hrest
    · cases heq
      exact hq ⟨r', List.mem_cons_self .., hsub address hcov⟩
    · exact hq ⟨q, List.mem_cons_of_mem _ hrest, hcov⟩

/-! ### Reading a `MayChange` off -/

/-- A register absent from the footprint is preserved. Callee-saved
preservation is this lemma, six times. -/
theorem reg_eq (h : MayChange locs a b) {r : Reg} (hr : Loc.reg r ∉ locs) :
    b.core.read r = a.core.read r := h.regs r hr

/-- A flag absent from the footprint is preserved. -/
theorem flag_eq (h : MayChange locs a b) {f : FlagName} (hf : Loc.flag f ∉ locs) :
    f.get b.core.flags = f.get a.core.flags := h.flags f hf

/-- With no flag listed, the whole flag record is preserved. -/
theorem flags_eq (h : MayChange locs a b) (hf : ∀ f : FlagName, Loc.flag f ∉ locs) :
    b.core.flags = a.core.flags := FlagName.flags_ext fun n => h.flags n (hf n)

/-- Permissions ride along: the regions are fixed, so every checked span keeps
its verdict. -/
theorem permitted (h : MayChange locs a b) {access : Process.Access} {address length : Nat}
    (hp : a.memory.Permitted access address length) :
    b.memory.Permitted access address length := by
  rwa [Process.Memory.Permitted, X86.Memory.checkSpan_congr h.regions]

/-- Read-over-write, disjoint: a load from a range separate from every range in
the footprint sees the old memory. This is x86isa's `rb-wb-disjoint` and the
workhorse of every frame proof. -/
theorem loadN_eq (h : MayChange locs a b) {address : Word} {n : Nat}
    (hw : (Range.mk address n).NoWrap)
    (hsep : ∀ r : Range, Loc.mem r ∈ locs → Separate r ⟨address, n⟩) :
    loadN b.memory address n = loadN a.memory address n := by
  have hbytes : ∀ i, i < n →
      b.memory.bytes.get? (address.toNat + i) = a.memory.bytes.get? (address.toNat + i) := by
    intro i hi
    refine h.bytes _ ?_
    rintro ⟨r, hmem, hcov⟩
    exact hsep r hmem _ hcov (Range.covers_of_mem_noWrap hw
      (show address.toNat ≤ address.toNat + i from Nat.le_add_right _ _)
      (show address.toNat + i < address.toNat + n from by omega))
  simp only [loadN, Process.Memory.readBytes, Process.Memory.readWith,
    X86.Memory.checkSpan_congr h.regions]
  rw [Memory.readBacking_congr address.toNat n (fun i hi => (hbytes i hi).symm)]

/-- A loaded program survives a footprint separate from its bytes. x86isa's
`program-at-wb-disjoint`. -/
theorem programAt (h : MayChange locs a b) {addr : Word} {code : List Byte}
    (hprog : ProgramAt a addr code)
    (hsep : ∀ r : Range, Loc.mem r ∈ locs → Separate r ⟨addr, code.length⟩) :
    ProgramAt b addr code := by
  have hw := hprog.noWrap
  have hbacking : ∀ index (bound : index < code.length),
      b.memory.bytes.get? (addr.toNat + index) = some (code[index]) := by
    intro index bound
    have hold := Process.Memory.readWith_get hprog.fetch index (by simpa using bound)
    rw [h.bytes _ ?_]
    · exact hold
    · rintro ⟨r, hmem, hcov⟩
      exact hsep r hmem _ hcov (Range.covers_of_mem_noWrap hw
        (show addr.toNat ≤ addr.toNat + index from Nat.le_add_right _ _)
        (show addr.toNat + index < addr.toNat + code.length from by omega))
  refine ⟨?_, h.permitted hprog.readable⟩
  exact Process.Memory.readWith_eq b.memory .execute addr.toNat code
    (h.permitted (Process.Memory.readWith_permitted hprog.fetch)) hbacking

/-! ### Building a `MayChange` -/

/-- A change confined to the register file, `rip` and the flags. -/
theorem ofCore {s t : State} {mem : Process.Memory}
    (hr : ∀ r : Reg, Loc.reg r ∉ locs → t.read r = s.read r)
    (hrip : Loc.rip ∉ locs → t.rip = s.rip)
    (hf : ∀ f : FlagName, Loc.flag f ∉ locs → f.get t.flags = f.get s.flags) :
    MayChange locs ⟨s, mem⟩ ⟨t, mem⟩ := ⟨hr, hrip, hf, rfl, fun _ _ => rfl⟩

/-- A change confined to memory, given a `Process.Memory.WritesOnly` witness
whose interval the footprint covers. `storeN_writesOnly` supplies the witness
for every store of the model. -/
theorem ofWrite {s : State} {before after : Process.Memory} {address length : Nat}
    (hw : Process.Memory.WritesOnly before after address length)
    (hcov : ∀ i, i < length → Locs.CoversAddr locs (address + i)) :
    MayChange locs ⟨s, before⟩ ⟨s, after⟩ := by
  refine ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, hw.1, ?_⟩
  intro location hnot
  refine hw.2 location ?_
  by_cases hin : address ≤ location ∧ location < address + length
  · exact absurd (by
      have := hcov (location - address) (by omega)
      rwa [show address + (location - address) = location by omega] at this) hnot
  · omega

/-- The `storeN` form of `ofWrite`. -/
theorem ofStore {s : State} {before after : Process.Memory} {address : Word} {k : Nat}
    {v : Word} (hst : storeN before address k v = some after)
    (hcov : ∀ i, i < k → Locs.CoversAddr locs (address.toNat + i)) :
    MayChange locs ⟨s, before⟩ ⟨s, after⟩ :=
  ofWrite (storeN_writesOnly hst) hcov

/-- The common case: the store lands inside one listed, non-wrapping range. -/
theorem ofStore_range {s : State} {before after : Process.Memory} {address : Word} {k : Nat}
    {v : Word} {r : Range} (hst : storeN before address k v = some after)
    (hmem : Loc.mem r ∈ locs) (hw : r.NoWrap)
    (hlo : r.base.toNat ≤ address.toNat) (hhi : address.toNat + k ≤ r.base.toNat + r.len) :
    MayChange locs ⟨s, before⟩ ⟨s, after⟩ :=
  ofStore hst fun i hi =>
    ⟨r, hmem, Range.covers_of_mem_noWrap hw (by omega) (by omega)⟩

end MayChange

/-! ## Sequencing: s2n-bignum's `,,` -/

namespace Rel

/-- Relational composition of two state relations. -/
def seq (R S : MState → MState → Prop) (a c : MState) : Prop := ∃ b, R a b ∧ S b c

@[inherit_doc] scoped infixl:65 " ,, " => Rel.seq

theorem seq_assoc (R S T : MState → MState → Prop) (a b : MState) :
    seq (seq R S) T a b ↔ seq R (seq S T) a b := by
  constructor
  · rintro ⟨y, ⟨x, hr, hs⟩, ht⟩; exact ⟨x, hr, y, hs, ht⟩
  · rintro ⟨x, hr, y, hs, ht⟩; exact ⟨y, ⟨x, hr, hs⟩, ht⟩

theorem seq_mono {R R' S S' : MState → MState → Prop} {a b : MState}
    (hR : ∀ x y, R x y → R' x y) (hS : ∀ x y, S x y → S' x y) (h : seq R S a b) :
    seq R' S' a b := by
  obtain ⟨x, hr, hs⟩ := h
  exact ⟨x, hR _ _ hr, hS _ _ hs⟩

end Rel

open scoped Rel

/-- `MAYCHANGE l₁ ,, MAYCHANGE l₂` is subsumed by `MAYCHANGE (l₁ ++ l₂)`: a
chain of per-instruction footprints collapses into one list. This is the
rewrite s2n-bignum's `MAYCHANGE` normaliser performs. -/
theorem MayChange.seq_subsumed {l₁ l₂ : List Loc} {a b : MState}
    (h : (MayChange l₁ ,, MayChange l₂) a b) : MayChange (l₁ ++ l₂) a b := by
  obtain ⟨x, h₁, h₂⟩ := h
  exact (h₁.mono fun l hl => List.mem_append_left _ hl).trans
    (h₂.mono fun l hl => List.mem_append_right _ hl)

/-- The converse direction that always holds: a single footprint factors
through itself, because `MayChange` is reflexive. -/
theorem MayChange.to_seq {l : List Loc} {a b : MState} (h : MayChange l a b) :
    (MayChange l ,, MayChange l) a b := ⟨b, h, MayChange.refl l b⟩

/-- `,,` of equal footprints is that footprint, up to the `++` on the left. -/
theorem MayChange.seq_self_iff {l : List Loc} {a b : MState} :
    (MayChange l ,, MayChange l) a b ↔ MayChange l a b :=
  ⟨fun h => (MayChange.seq_subsumed h).narrow (fun loc hloc hnot =>
      absurd (by rcases List.mem_append.mp hloc with h | h <;> exact h) hnot),
   MayChange.to_seq⟩

/-! ## `Ensures` -/

/-- Partial correctness of a finite returning run, in the shape of
s2n-bignum's `ensures`: from any state satisfying `P`, any run that returns to
`exit` lands in a state satisfying `Q`, and the pair is related by the
footprint `R`.

It is `Returns`, not a step-indexed recursion, because `Ext.Returns` is
already the finite-run primitive of this model, and because the three
components `P`, `Q`, `R` are exactly what a subroutine theorem states. -/
def Ensures (exit : Word) (P Q : MState → Prop) (R : MState → MState → Prop) : Prop :=
  ∀ initial final, P initial → Ext.Returns exit initial final → Q final ∧ R initial final

namespace Ensures

variable {exit : Word} {P P' Q Q' : MState → Prop} {R R' : MState → MState → Prop}

/-- Strengthen the precondition, weaken the postcondition and the footprint. -/
theorem mono (h : Ensures exit P Q R) (hP : ∀ m, P' m → P m) (hQ : ∀ m, Q m → Q' m)
    (hR : ∀ a b, R a b → R' a b) : Ensures exit P' Q' R' := by
  intro initial final hp hret
  obtain ⟨hq, hr⟩ := h initial final (hP initial hp) hret
  exact ⟨hQ final hq, hR initial final hr⟩

/-- Two postconditions proved from the same precondition can be combined. -/
theorem and (h : Ensures exit P Q R) (h' : Ensures exit P Q' R') :
    Ensures exit P (fun m => Q m ∧ Q' m) (fun a b => R a b ∧ R' a b) := by
  intro initial final hp hret
  obtain ⟨hq, hr⟩ := h initial final hp hret
  obtain ⟨hq', hr'⟩ := h' initial final hp hret
  exact ⟨⟨hq, hq'⟩, hr, hr'⟩

end Ensures

/-! ### A bridge to a program logic

Three approaches to x86 function proofs coexist: this footprint
vocabulary, a Myreen-style decompiler (`Silmaril.X86.Decompile.Cert`), and a
separation logic (`Silmaril.X86.Sep`). The three
need not share a proof method, but they should share a *notion of footprint*,
or a client of one cannot reuse a theorem proved in another.

`Triple` is the common surface: partial correctness over `Ext.Returns`, with no
footprint. Every `Ensures` gives one (`Ensures.toTriple`), and the footprint is
what makes the frame rule below provable. An Iris-style `wp` over the same
machine relates to `Triple` by a single lemma on the Iris side — "`wp` implies
`Triple`", or the converse for the fragment where the two agree — and then
`Ensures.frame` is directly usable there, because a `MayChange` list is exactly
the information a separating frame rule needs.

Nothing here depends on a program logic; these are four short lemmas that
make the connection cheap. -/

/-- Partial correctness over the returning runs, with the footprint forgotten.
The shape an Iris-style `wp` is easiest to compare against. -/
def Triple (exit : Word) (P Q : MState → Prop) : Prop :=
  ∀ initial final, P initial → Ext.Returns exit initial final → Q final

/-- Every subroutine theorem gives a triple. -/
theorem Ensures.toTriple {exit : Word} {P Q : MState → Prop} {R : MState → MState → Prop}
    (h : Ensures exit P Q R) : Triple exit P Q :=
  fun initial final hp hret => (h initial final hp hret).1

/-- …and a triple that remembers the relational part, by pinning the initial
state. -/
theorem Ensures.toTriple_rel {exit : Word} {P Q : MState → Prop} {R : MState → MState → Prop}
    (h : Ensures exit P Q R) (m₀ : MState) :
    Triple exit (fun m => m = m₀ ∧ P m) (fun m => Q m ∧ R m₀ m) := by
  rintro initial final ⟨rfl, hp⟩ hret
  exact h initial final hp hret

/-- **The frame rule.** A `MayChange locs` footprint carries every memory
assertion about a non-wrapping range separate from `locs` from the
precondition to the postcondition. This is what a separation-logic frame rule
delivers for free and what a footprint has to deliver by hand; stating it here
means the two readings agree on what "separate" means. -/
theorem Ensures.frame {exit : Word} {P Q : MState → Prop} {locs : List Loc}
    (h : Ensures exit P Q (MayChange locs)) {r : Range} (hw : r.NoWrap)
    (hsep : ∀ q : Range, Loc.mem q ∈ locs → Separate q r) (v : Word) :
    Ensures exit (fun m => P m ∧ loadN m.memory r.base r.len = some v)
      (fun m => Q m ∧ loadN m.memory r.base r.len = some v) (MayChange locs) := by
  rintro initial final ⟨hp, hv⟩ hret
  obtain ⟨hq, hmc⟩ := h initial final hp hret
  exact ⟨⟨hq, by rw [hmc.loadN_eq hw hsep]; exact hv⟩, hmc⟩

/-- The same, for the code: a loaded program survives any footprint separate
from it. -/
theorem Ensures.frame_program {exit : Word} {P Q : MState → Prop} {locs : List Loc}
    (h : Ensures exit P Q (MayChange locs)) {addr : Word} {code : List Byte}
    (hsep : ∀ q : Range, Loc.mem q ∈ locs → Separate q ⟨addr, code.length⟩) :
    Ensures exit (fun m => P m ∧ ProgramAt m addr code)
      (fun m => Q m ∧ ProgramAt m addr code) (MayChange locs) := by
  rintro initial final ⟨hp, hprog⟩ hret
  obtain ⟨hq, hmc⟩ := h initial final hp hret
  exact ⟨⟨hq, hmc.programAt hprog hsep⟩, hmc⟩

/-! ### The clock argument

`Returns` only says that *some* finite run returns. `Returns.det` upgrades a
single exhibited run to a statement about every run, which is what turns a
clock-style symbolic execution into an `Ensures`; the proof is a hand case split on the
three orderings of the two run lengths, using determinism of `step`. -/

/-- Running past a returning state fails. -/
theorem stepOpt_eq_none_of_returned {exit : Word} {m final : MState}
    (h : Ext.step exit m = .returned final) : Ext.stepOpt exit m = none := by
  unfold Ext.stepOpt
  rw [h]

private theorem run_none_of_returned {exit : Word} {m final : MState} {j : Nat}
    (h : Ext.step exit m = .returned final) (hj : 0 < j) :
    run (Ext.stepOpt exit) j m = none := by
  obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp [stepOpt_eq_none_of_returned h]

/-- Determinism of the returning run: one exhibited run fixes the final state
of every `Returns`. -/
theorem Returns.det {exit : Word} {initial mid final₀ : MState} {N : Nat}
    (hrun : run (Ext.stepOpt exit) N initial = some mid)
    (hret : Ext.step exit mid = .returned final₀)
    {final : MState} (h : Ext.Returns exit initial final) : final = final₀ := by
  obtain ⟨n, mid', hrun', hret'⟩ := h
  rcases Nat.lt_trichotomy n N with hlt | rfl | hgt
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, N = n + (d + 1) := ⟨N - n - 1, by omega⟩
    rw [run_add, hrun', Option.bind_some, run_none_of_returned hret' (Nat.succ_pos d)] at hrun
    simp at hrun
  · rw [hrun'] at hrun
    cases Option.some.inj hrun
    rw [hret] at hret'
    exact (Ext.Outcome.returned.inj hret').symm
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, n = N + (d + 1) := ⟨n - N - 1, by omega⟩
    rw [run_add, hrun, Option.bind_some, run_none_of_returned hret (Nat.succ_pos d)] at hrun'
    simp at hrun'

/-- Build an `Ensures` from a clock: for every state satisfying `P`, exhibit a
run of some length that returns, and check `Q` and `R` on its result. -/
theorem Ensures.of_run {exit : Word} {P Q : MState → Prop} {R : MState → MState → Prop}
    (h : ∀ initial, P initial → ∃ (N : Nat) (mid final : MState),
      run (Ext.stepOpt exit) N initial = some mid ∧ Ext.step exit mid = .returned final ∧
        Q final ∧ R initial final) :
    Ensures exit P Q R := by
  intro initial final hp hret
  obtain ⟨N, mid, final₀, hrun, hstep, hq, hr⟩ := h initial hp
  rw [Returns.det hrun hstep hret]
  exact ⟨hq, hr⟩

/-! ### Chaining retirements

A symbolic execution is built backwards: `run_cons` prepends one retirement to
an already-built run. -/

/-- Prepend one retirement to a run. -/
theorem run_cons {exit : Word} {m next final : MState} {N : Nat}
    (hstep : Ext.step exit m = .retired next) (hrun : run (Ext.stepOpt exit) N next = some final) :
    run (Ext.stepOpt exit) (N + 1) m = some final := by
  have h1 : run (Ext.stepOpt exit) 1 m = some next := by
    simp [Ext.stepOpt_eq_some_iff.mpr hstep]
  rw [show N + 1 = 1 + N by omega, run_add, h1, Option.bind_some]
  exact hrun

/-- Concatenate two runs. -/
theorem run_append {exit : Word} {a b c : MState} {N M : Nat}
    (h₁ : run (Ext.stepOpt exit) N a = some b) (h₂ : run (Ext.stepOpt exit) M b = some c) :
    run (Ext.stepOpt exit) (N + M) a = some c := by
  rw [run_add, h₁]
  exact h₂

/-- Append one retirement to a run. This is the forward form a symbolic
execution uses: build the run left to right as each step is discharged. -/
theorem run_snoc {exit : Word} {a b c : MState} {N : Nat}
    (h₁ : run (Ext.stepOpt exit) N a = some b) (h₂ : Ext.step exit b = .retired c) :
    run (Ext.stepOpt exit) (N + 1) a = some c :=
  run_append h₁ (run_cons h₂ rfl)

end Silmaril.X86.Spec
