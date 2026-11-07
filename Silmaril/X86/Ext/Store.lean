module

public import Silmaril.X86.Ext.SymExec

/-!
# Stores, slots and footprints

The memory half of the symbolic-execution layer. `Silmaril.X86.Ext.Semantics`
performs every store through `storeN`, which goes through
`Process.Memory.writeBytes`, which rebuilds the whole byte map. Reasoning
about a function with a hundred stores by unfolding `Memory.install` a hundred
times is not viable, so this module replaces the *term* "memory after a store"
by a *characterisation*: what the store put there, and what it left alone.

## `Stored`

`Stored before after address bytes` says `after` is `before` with `bytes` at
`address` and nothing else touched. It is the only thing a proof ever needs to
know about a store:

* `Stored.readWith_self` — read-after-write;
* `Stored.readWith_disjoint` — read-after-disjoint-write;
* `Stored.permitted_iff` — a store never changes what is mapped, so a
  permission established once survives every later store;
* `Stored.writesWithin` — a store whose span lies inside a footprint is a
  `WritesWithin` step, and `Memory.WritesWithin.trans` composes those. This is
  how a modifies-set claim is *carried* through an execution rather than
  recovered at the end.

## Little-endian slots

`HoldsLE memory address k v` is "the `k` bytes at `address` are the low `k`
bytes of `v`, little-endian" — the shape every `uint32` and `uint64` frame
slot has. `loadN_of_holdsLE` turns it into the `loadN` the semantics
performs, and `holdsLE_of_stored` is the read-back after a `storeN`. Together
they are the read/write algebra of a stack slot.

## Scope

Everything here is about `Silmaril.Process.Memory` and
`Silmaril.X86.Ext.Semantics` as this repository defines them. There is no
claim about hardware, and nothing here is specific to SHA-256 or to an
optimisation level.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.Machine.LittleEndian (encodeWords)

/-! ## A store, by what it changed -/

/-- `after` is `before` with `bytes` written at `address`: nothing else
changed, and the span reads back as `bytes`. -/
structure Stored (before after : Memory) (address : Nat) (bytes : List Byte) : Prop where
  /-- Mapping metadata and every byte outside the span are unchanged. -/
  frame : Memory.WritesOnly before after address bytes.length
  /-- The span holds exactly `bytes`. -/
  installed : ∀ index, (h : index < bytes.length) → after.bytes.get? (address + index) =
    some bytes[index]

theorem Stored.of_writeBytes {before after : Memory} {address : Nat} {bytes : List Byte}
    (written : before.writeBytes address bytes = some after) : Stored before after address bytes :=
  ⟨Memory.writeBytes_writesOnly written, fun index h => Memory.writeBytes_get written index h⟩

/-- Every store the semantics performs is a `Stored`. -/
theorem Stored.of_storeN {before after : Memory} {address : Word} {k : Nat} {v : Word}
    (stored : storeN before address k v = some after) :
    Stored before after address.toNat (leBytes v k) :=
  Stored.of_writeBytes stored

/-- A `PUSH` is a `Stored` at the new stack pointer. -/
theorem Stored.of_pushWord {s t : State} {before after : Memory} {v : Word}
    (pushed : X86.pushWord s before v = some (t, after)) :
    Stored before after (s.read .rsp - 8#64).toNat (encodeWords [v]) := by
  simp only [X86.pushWord, Option.map_eq_some_iff, Prod.mk.injEq] at pushed
  obtain ⟨_, written, _, rfl⟩ := pushed
  exact Stored.of_writeBytes written

theorem Stored.regions {before after : Memory} {address : Nat} {bytes : List Byte}
    (h : Stored before after address bytes) : after.regions = before.regions := h.frame.1

/-- A store never changes what is mapped, so a permission proved once is good
for the rest of the run. -/
theorem Stored.permitted_iff {before after : Memory} {address : Nat} {bytes : List Byte}
    (h : Stored before after address bytes) (access : Access) (start count : Nat) :
    after.Permitted access start count ↔ before.Permitted access start count := by
  unfold Memory.Permitted
  rw [Memory.checkSpan_congr h.regions]

theorem Stored.permitted {before after : Memory} {address : Nat} {bytes : List Byte}
    (h : Stored before after address bytes) {access : Access} {start count : Nat}
    (p : before.Permitted access start count) : after.Permitted access start count :=
  (h.permitted_iff access start count).mpr p

/-- Read after a disjoint write. -/
theorem Stored.readWith_disjoint {before after : Memory} {address : Nat} {bytes : List Byte}
    (h : Stored before after address bytes) (access : Access) (start count : Nat)
    (disjoint : start + count ≤ address ∨ address + bytes.length ≤ start) :
    after.readWith access start count = before.readWith access start count :=
  Memory.readWith_writesOnly h.frame access start count disjoint

/-- Read after the write itself. The permission is the one `before` had: a
store does not change permissions. -/
theorem Stored.readWith_self {before after : Memory} {address : Nat} {bytes : List Byte}
    (h : Stored before after address bytes) {access : Access}
    (permitted : before.Permitted access address bytes.length) :
    after.readWith access address bytes.length = some bytes :=
  Memory.readWith_eq after access address bytes (h.permitted permitted) h.installed

/-! ## Stores succeed when they are permitted

The point of these two is that the successor memory stays *opaque*: a proof
names it by an existential and characterises it with `Stored`, instead of
carrying a tower of `Memory.install` applications through the run. -/

/-- A permitted store succeeds, and `Stored` is everything that is then known
about the result. -/
theorem storeN_isSome {memory : Memory} {address : Word} {k : Nat} {v : Word}
    (permitted : memory.Permitted .write address.toNat k) :
    ∃ after, storeN memory address k v = some after ∧
      Stored memory after address.toNat (leBytes v k) := by
  have check : memory.checkSpan .write address.toNat k = true := permitted
  have stored : storeN memory address k v =
      some { memory with bytes := Memory.install memory.bytes address.toNat (leBytes v k) } := by
    unfold storeN Memory.writeBytes
    rw [length_leBytes, ite_eq_left check]
  exact ⟨_, stored, Stored.of_storeN stored⟩

/-- A permitted `PUSH` succeeds, with the successor memory left opaque. -/
theorem pushWord_isSome {s : State} {memory : Memory} {v : Word}
    (permitted : memory.Permitted .write (s.read .rsp - 8#64).toNat 8) :
    ∃ after, X86.pushWord s memory v = some (s.write .rsp (s.read .rsp - 8#64), after) ∧
      Stored memory after (s.read .rsp - 8#64).toNat (encodeWords [v]) := by
  have pushed := X86.pushWord_eq_some (value := v) permitted
  exact ⟨_, pushed, Stored.of_pushWord pushed⟩

/-! ## The image survives a store

A function that writes only to its own frame still has its own code. This is
the fact a symbolic execution needs at *every* store, because `Loaded` is a
statement about the memory it is executing in. -/

/-- A loaded image survives a store that misses it. -/
theorem Loaded.of_stored {before after : Memory} {base : Word} {bytes : List Byte}
    (loaded : Loaded before base bytes) {address : Nat} {written : List Byte}
    (stored : Stored before after address written)
    (disjoint : base.toNat + bytes.length ≤ address ∨ address + written.length ≤ base.toNat) :
    Loaded after base bytes := by
  rw [Loaded] at loaded ⊢
  rw [show after.fetchBytes base.toNat bytes.length
      = before.fetchBytes base.toNat bytes.length from
    stored.readWith_disjoint .execute base.toNat bytes.length (by omega)]
  exact loaded

/-! ## A push from a loaded image

`PUSH` is the one instruction whose memory operand is implicit, so it is worth
one packaged lemma: the permission goes in, the successor state and a `Stored`
characterisation of the successor memory come out. -/

/-- One `push r` from a loaded image, with the pushed memory left opaque. -/
theorem stepOpt_push_mk {exit base : Word} {bytes : List Byte} {m : MState} {offset len : Nat}
    {r : Silmaril.X86.Reg}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.push r, len))
    (permitted : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8) :
    ∃ after, stepOpt exit m =
        some ⟨{ m.core.write .rsp (m.core.read .rsp - 8#64) with
                rip := base + BitVec.ofNat 64 (offset + len) }, after⟩ ∧
      Stored m.memory after (m.core.read .rsp - 8#64).toNat (encodeWords [m.core.read r]) := by
  obtain ⟨after, pushed, stored⟩ := pushWord_isSome (v := m.core.read r) permitted
  refine ⟨after, ?_, stored⟩
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  simp only [exec, pushed, retire, at_offset, Instr.length,
    (decode_length decoded).1.symm, rip_advance base rfl]

/-! ## Packaged steps that touch memory

The four shapes a compiled function reads and writes locals with. As with the
fault-free steps in `SymExec.lean`, each takes the effective address, the
access width and the value as *equations* supplied by the caller, so the
conclusion arrives in the caller's normal form and no normalisation happens at
the use site.

That is not only tidiness. Discharging a store inline with
`simp only [exec, …]` against a *concrete* `Mem` makes `simp` evaluate the
encoder and leaves a goal whose defeq check does not terminate in practice;
the same step through these lemmas elaborates in about a second, because the
operand stays a variable. -/

/-- One `mov m, r`: a `sz.bytes`-wide store of a register to memory. -/
theorem stepOpt_store_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {mm : Mem} {r : Silmaril.X86.Reg}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.mov sz (.mem mm) r, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (value_eq : (sz.read m.core r).setWidth 64 = value)
    (permitted : m.memory.Permitted .write address width) :
    ∃ after,
      stepOpt exit m =
        some ⟨{ m.core with rip := base + BitVec.ofNat 64 (offset + len) }, after⟩ ∧
      Stored m.memory after address (leBytes value width) := by
  subst eff width_eq value_eq
  obtain ⟨after, written, stored⟩ :=
    storeN_isSome (v := (sz.read m.core r).setWidth 64) (k := sz.bytes) permitted
  refine ⟨after, ?_, stored⟩
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.mov sz (.mem mm) r).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, writeRM, written, Option.map_some,
    retire]

/-- One `movl $imm, m`: a `sz.bytes`-wide store of a sign-extended
immediate. -/
theorem stepOpt_store_imm_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {mm : Mem} {imm : BitVec 32}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movI sz (.mem mm) imm, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (value_eq : (imm.signExtend sz.bits).setWidth 64 = value)
    (permitted : m.memory.Permitted .write address width) :
    ∃ after,
      stepOpt exit m =
        some ⟨{ m.core with rip := base + BitVec.ofNat 64 (offset + len) }, after⟩ ∧
      Stored m.memory after address (leBytes value width) := by
  subst eff width_eq value_eq
  obtain ⟨after, written, stored⟩ :=
    storeN_isSome (v := (imm.signExtend sz.bits).setWidth 64) (k := sz.bytes) permitted
  refine ⟨after, ?_, stored⟩
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.movI sz (.mem mm) imm).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, writeRM, written, Option.map_some,
    retire]

/-! ## Carrying a footprint

Every store of a well-behaved function lands inside its modifies set. These
two lemmas say that, and `Memory.WritesWithin.trans` chains them, so the
footprint claim is *maintained* across an execution instead of being
reconstructed from a list of stores at the end. -/

/-- A store inside the footprint is a step of the footprint claim. -/
theorem Stored.writesWithin {before after : Memory} {address : Nat} {bytes : List Byte}
    (h : Stored before after address bytes) {inside : Nat → Prop}
    (within : ∀ offset < bytes.length, inside (address + offset)) :
    Memory.WritesWithin before after inside := by
  refine ⟨h.frame.1, fun location hout => h.frame.2 location ?_⟩
  by_cases hin : address ≤ location ∧ location < address + bytes.length
  · exact absurd (by
      have := within (location - address) (by omega)
      rwa [show address + (location - address) = location by omega] at this) hout
  · omega

/-- Footprints compose: a run that is `WritesWithin` up to here and takes a
step inside the footprint is `WritesWithin` after the step. -/
theorem _root_.Silmaril.Process.Memory.WritesWithin.step
    {first second third : Memory} {inside : Nat → Prop}
    (sofar : Memory.WritesWithin first second inside) {address : Nat} {bytes : List Byte}
    (stored : Stored second third address bytes)
    (within : ∀ offset < bytes.length, inside (address + offset)) :
    Memory.WritesWithin first third inside :=
  sofar.trans (stored.writesWithin within)

/-! ## Little-endian slots -/

/-- The `k` bytes at `address` are the low `k` bytes of `v`, little-endian:
the shape of a `uint32` or `uint64` stack slot. -/
def HoldsLE (memory : Memory) (address : Nat) (k : Nat) (v : Word) : Prop :=
  memory.readBytes address k = some (leBytes v k)

/-- The semantics' load, from a slot fact. A `k`-byte load zero-extends, so it
sees `v` truncated to `8 * k` bits. -/
theorem loadN_of_holdsLE {memory : Memory} {address : Word} {k : Nat} {v : Word}
    (h : HoldsLE memory address.toNat k v) :
    loadN memory address k = some (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * k))) := by
  rw [HoldsLE] at h
  rw [loadN, h, Option.map_some, leValue_leBytes]

/-- An eight-byte slot loads back exactly. -/
theorem loadN_of_holdsLE_eight {memory : Memory} {address : Word} {v : Word}
    (h : HoldsLE memory address.toNat 8 v) : loadN memory address 8 = some v := by
  rw [loadN_of_holdsLE h]
  simp [Nat.mod_eq_of_lt v.isLt]

/-- Read-after-write for a slot: what `storeN` wrote is what the slot holds. -/
theorem holdsLE_of_stored {before after : Memory} {address : Word} {k : Nat} {v : Word}
    (stored : storeN before address k v = some after)
    (readable : before.Permitted .read address.toNat k) :
    HoldsLE after address.toNat k v := by
  have h := Stored.of_storeN stored
  have := h.readWith_self (access := .read) (by simpa using readable)
  simpa [HoldsLE, Memory.readBytes] using this

/-- Read-after-write, phrased over a `Stored` rather than a `storeN`: the form
a packaged step lemma leaves behind. -/
theorem HoldsLE.of_stored_self {before after : Memory} {address k : Nat} {v : Word}
    (stored : Stored before after address (leBytes v k))
    (readable : before.Permitted .read address k) : HoldsLE after address k v := by
  have hw := stored.readWith_self (access := .read) (by rwa [length_leBytes])
  rw [length_leBytes] at hw
  exact hw

/-- Read-after-disjoint-write for a slot. -/
theorem HoldsLE.of_stored_disjoint {before after : Memory} {address : Nat} {bytes : List Byte}
    (stored : Stored before after address bytes) {start k : Nat} {v : Word}
    (h : HoldsLE before start k v)
    (disjoint : start + k ≤ address ∨ address + bytes.length ≤ start) :
    HoldsLE after start k v := by
  have := stored.readWith_disjoint .read start k disjoint
  simpa [HoldsLE, Memory.readBytes, this] using h

/-! ## From a `readBytes` precondition to a slot fact

A calling convention states its input buffers as `readBytes … = some bytes` —
that is the only form that rules out a mapped-but-unbacked page. Every load
lemma, however, consumes `HoldsLE`, which says the bytes *are* the
little-endian bytes of some word. The two are the same fact for any access of
at most eight bytes, and this is the bridge: `leValue` turns the list into a
word and `leBytes` turns it back.

Without it a proof ends up carrying a bespoke "these bytes hold these words"
invariant alongside the precondition it already has. -/

/-- `loadN` directly from a `readBytes` fact. -/
theorem loadN_of_readBytes {memory : Memory} {address : Word} {k : Nat} {bytes : List Byte}
    (read : memory.readBytes address.toNat k = some bytes) :
    loadN memory address k = some (BitVec.ofNat 64 (leValue bytes)) := by
  rw [loadN, read, Option.map_some]

private theorem wordByte_shift (v : Word) (i : Nat) :
    Silmaril.Machine.LittleEndian.wordByte v (i + 1)
      = Silmaril.Machine.LittleEndian.wordByte (v >>> 8) i := by
  simp only [Silmaril.Machine.LittleEndian.wordByte]
  ext j hj
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  congr 1
  omega

/-- A byte list's little-endian value is below `2 ^ (8 * length)`. -/
theorem leValue_lt : ∀ bs : List Byte, leValue bs < 2 ^ (8 * bs.length)
  | [] => by simp [leValue]
  | b :: rest => by
    have ih := leValue_lt rest
    have hb : b.toNat < 256 := by simpa using b.isLt
    have hpow : 2 ^ (8 * (rest.length + 1)) = 256 * 2 ^ (8 * rest.length) := by
      rw [show 8 * (rest.length + 1) = 8 + 8 * rest.length by omega, Nat.pow_add,
        show (2 : Nat) ^ 8 = 256 from rfl]
    simp only [leValue, List.length_cons, hpow]
    omega

/-- Up to eight bytes, `leBytes` inverts `leValue`: the list really is the
little-endian spelling of a word. -/
theorem leBytes_leValue : ∀ bs : List Byte, bs.length ≤ 8 →
    leBytes (BitVec.ofNat 64 (leValue bs)) bs.length = bs
  | [], _ => by simp [leBytes]
  | b :: rest, hlen => by
    have hrest : rest.length ≤ 7 := by simp only [List.length_cons] at hlen; omega
    have ih := leBytes_leValue rest (by omega)
    have hV := leValue_lt rest
    have hb : b.toNat < 256 := by simpa using b.isLt
    have hpow : 2 ^ (8 * rest.length) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) (by omega)
    have hbig : (2 : Nat) ^ 64 = 256 * 2 ^ 56 := by
      rw [show (64 : Nat) = 8 + 56 from rfl, Nat.pow_add, show (2 : Nat) ^ 8 = 256 from rfl]
    have ht : b.toNat + 256 * leValue rest < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 (b.toNat + 256 * leValue rest)).toNat
        = b.toNat + 256 * leValue rest := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt ht
    have hhead : Silmaril.Machine.LittleEndian.wordByte
        (BitVec.ofNat 64 (b.toNat + 256 * leValue rest)) 0 = b := by
      refine BitVec.eq_of_toNat_eq ?_
      simp only [Silmaril.Machine.LittleEndian.wordByte, Nat.mul_zero,
        BitVec.ushiftRight_zero, BitVec.toNat_setWidth, htoNat]
      omega
    have htail : (BitVec.ofNat 64 (b.toNat + 256 * leValue rest)) >>> (8 : Nat)
        = BitVec.ofNat 64 (leValue rest) := by
      refine BitVec.eq_of_toNat_eq ?_
      simp only [BitVec.toNat_ushiftRight, htoNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [leBytes, List.length_cons, List.ofFn_succ, Fin.val_zero, Fin.val_succ,
      leValue, wordByte_shift, hhead, htail, List.cons.injEq, true_and]
    simpa [leBytes] using ih

/-- **The bridge.** Bytes read from memory are the little-endian spelling of a
word, so a `readBytes` precondition yields the `HoldsLE` slot fact every load
lemma consumes. -/
theorem holdsLE_of_readBytes {memory : Memory} {address k : Nat} {bytes : List Byte}
    (read : memory.readBytes address k = some bytes) (small : k ≤ 8) :
    HoldsLE memory address k (BitVec.ofNat 64 (leValue bytes)) := by
  have hlen : bytes.length = k := Memory.readWith_length read
  show memory.readBytes address k = some (leBytes (BitVec.ofNat 64 (leValue bytes)) k)
  rw [← hlen, leBytes_leValue bytes (by omega)]
  rw [hlen]
  exact read

/-- **One byte of a read buffer, as a slot fact.** A calling convention names
an input buffer with a single `readBytes`; compiled code reads it a byte at a
time (`movzbl (%rax,%rcx,1),%ecx`). This is that case.

Stated over `List.getD` rather than any spec-level byte accessor, so it stays
free of any particular image. That costs nothing at the call sites: a spec's
`byteAt bytes i` is typically *defined* as `bytes.getD i 0`, and the two then
unify definitionally.

**This is not the way to a wider slot fact.** `HoldsLE address k v` unfolds to
a *single* `k`-byte read, so `HoldsLE address 4 _` is not four of these: going
from four one-byte reads to one four-byte read needs an adjacency-join —
"reads of abutting spans compose into a read of their union" — which this
layer deliberately does not have, because `Memory.readBytes_sub_range` at
`len = 4` gives the four-byte fact in one rewrite and no track has needed the
join. Use the sub-range lemma at the width the instruction actually reads.

The join is worth writing only when something needs to go the *other* way:
from several narrow writes to one wide read. A feed-forward epilogue that
stores eight words and must then satisfy a 32-byte `readBytes` postcondition
is the shape that would force it. -/
theorem holdsLE_byte_of_readBytes {memory : Memory} {base length : Nat} {bytes : List Byte}
    (read : memory.readBytes base length = some bytes) {k : Nat} (hk : k < length) :
    HoldsLE memory (base + k) 1 ((bytes.getD k 0).setWidth 64) := by
  have hlen : bytes.length = length := Memory.readWith_length read
  have hk' : k < bytes.length := by omega
  have hslice : (bytes.drop k).take 1 = [bytes.getD k 0] := by
    rw [List.drop_eq_getElem_cons hk', List.take_succ_cons, List.take_zero,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
  have hsub := Memory.readBytes_sub_range read (offset := k) (len := 1) hk (by omega)
  rw [hslice] at hsub
  have hval : BitVec.ofNat 64 (leValue [bytes.getD k 0]) = (bytes.getD k 0).setWidth 64 := by
    refine BitVec.eq_of_toNat_eq ?_
    simp only [leValue, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mul_zero, Nat.add_zero]
  rw [← hval]
  exact holdsLE_of_readBytes hsub (by omega)

/-- A four-byte slot only records the low thirty-two bits of the value stored
in it, so `leBytes` cannot tell a `Word` from its truncation. -/
theorem leBytes_setWidth32 (v : Word) :
    leBytes v 4 = leBytes ((v.setWidth 32 : BitVec 32).setWidth 64 : Word) 4 := by
  simp only [leBytes, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    Silmaril.Machine.LittleEndian.wordByte, List.cons.injEq, and_true]
  and_intros <;> (refine BitVec.eq_of_toNat_eq ?_; simp [Nat.shiftRight_eq_div_pow] <;> omega)

/-- **Normalising a four-byte slot fact.** Any witness to a four-byte slot can
be replaced by its 32-bit truncation, widened back.

This is what lets a *weak* invariant — "some value is there" — be turned into
a *valued* one at a definite shape, and so lets a single symbolic-execution
chain serve both a liveness proof and a data invariant. Without it the two
would need separate chains over the same instructions. -/
theorem HoldsLE.norm32 {memory : Memory} {address : Nat} {v : Word}
    (h : HoldsLE memory address 4 v) :
    HoldsLE memory address 4 ((v.setWidth 32 : BitVec 32).setWidth 64 : Word) := by
  rw [HoldsLE, ← leBytes_setWidth32]
  exact h

/-- **A four-byte slot determines its value mod 2³².** Two slot facts at the
same address agree on the low thirty-two bits, because both unfold to the same
`readBytes` and `leBytes` is injective on them.

This is the lemma that lets a *wide* read be identified with the *narrow*
writes that produced it without any bit-level reasoning: widen the stores with
`Memory.readBytes_run`, read the wide result back a word at a time, and use
this to see the two agree. -/
theorem HoldsLE.unique32 {memory : Memory} {address : Nat} {x y : Word}
    (hx : HoldsLE memory address 4 x) (hy : HoldsLE memory address 4 y) :
    x.setWidth 32 = y.setWidth 32 := by
  have h : leBytes x 4 = leBytes y 4 := by
    rw [HoldsLE] at hx hy
    rw [hx] at hy
    exact Option.some.inj hy
  have hv : leValue (leBytes x 4) = leValue (leBytes y 4) := by rw [h]
  rw [leValue_leBytes, leValue_leBytes] at hv
  refine BitVec.eq_of_toNat_eq ?_
  simpa using hv

/-! ## Packaged steps that read a slot

These two need `HoldsLE`, so they sit after it. A load's slot fact is both
its fault-freedom fact and its value fact: nothing extra is needed to know
that the access does not fault. -/

/-- One `mov r, m`: a `sz.bytes`-wide load, zero-extended to 64 bits. The
memory is unchanged, and `held` is simultaneously the fault-freedom fact and
the value fact. -/
theorem stepOpt_load_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {mm : Mem} {r : Silmaril.X86.Reg}
    {address width : Nat} {value result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.load sz r mm, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value)
    (result_eq : ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits).setWidth 64
      = result) :
    stepOpt exit m = some ⟨{ m.core.write r result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst eff width_eq result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.load sz r mm).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, readRM, loadN_of_holdsLE held,
    Option.map_some, retire, Sz.write]

/-- One `cmp m, imm8` (`83 /7 ib`): reads a slot, sets the flags, writes
nothing. This is the head of every clang `-O0` counted loop, whose counter
lives in a stack slot rather than a register. -/
theorem stepOpt_cmpI8_mem_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {mm : Mem} {imm : BitVec 8}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI8 sz .cmp (.mem mm) imm, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value) :
    stepOpt exit m = some ⟨{ m.core with
      flags := AluOp.flagsN .cmp
        ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits)
        (imm.signExtend sz.bits),
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst eff width_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluI8 sz .cmp (.mem mm) imm).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM,
    loadN_of_holdsLE held, Option.map_some, ite_true, retire]

/-- One `movsxd r64, m32` (`REX.W 63 /r` with a memory operand): load four
bytes and sign-extend. -/
theorem stepOpt_movsxd_mem_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {mm : Mem} {dst : Silmaril.X86.Reg}
    {address width : Nat} {value result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movsxd dst (.mem mm), len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : Sz.d.bytes = width)
    (held : HoldsLE m.memory address width value)
    (result_eq :
      ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth 32).signExtend 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst eff width_eq result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.movsxd dst (.mem mm)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, readRM, loadN_of_holdsLE held,
    Option.map_some, retire, Sz.bits_d]

/-- One `movzx`/`movsx` from memory (`0F B6`, `0F B7`, `0F BE`, `0F BF`).
`movzbl (%rax,%rcx,1),%ecx` — a byte of the input block, indexed by a
register — is this form, and it is how clang `-O0` builds each big-endian
message word. -/
theorem stepOpt_movx_mem_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sx : Bool} {sz : Sz} {nw : Narrow} {dst : Silmaril.X86.Reg} {mm : Mem}
    {address width : Nat} {value result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movx sx sz nw dst (.mem mm), len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : nw.bytes = width)
    (held : HoldsLE m.memory address width value)
    (result_eq :
      (if sx then
          ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth nw.bits).signExtend sz.bits
        else
          ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth nw.bits).setWidth
            sz.bits).setWidth 64 = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst eff width_eq result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.movx sx sz nw dst (.mem mm)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, readNarrow, loadN_of_holdsLE held,
    Option.map_some, retire, Sz.write]

/-- `op r, m` (`03 0B 23 2B 33 3B /r` with a memory operand), `op ≠ cmp`:
the direction-1 ALU form reading from memory, as in
`add -0x7c(%rsp,%rax,4),%r8d`. -/
theorem stepOpt_aluR_mem_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {dst : Silmaril.X86.Reg} {mm : Mem}
    {address width : Nat} {value result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluR sz op dst (.mem mm), len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value)
    (not_cmp : op ≠ .cmp)
    (result_eq : (AluOp.resultN op (sz.read m.core dst)
      ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits)).setWidth 64
        = result) :
    stepOpt exit m = some ⟨{ m.core.write dst result with
        flags := AluOp.flagsN op (sz.read m.core dst)
          ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst eff width_eq result_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluR sz op dst (.mem mm)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStepR, readRM,
    loadN_of_holdsLE held, Option.map_some, not_cmp, ite_false, retire, Sz.write]

/-- One `op r, m`, with the successor left opaque. -/
theorem stepOpt_aluR_mem {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {op : Silmaril.X86.AluOp} {dst : Silmaril.X86.Reg} {mm : Mem}
    {address width : Nat} {value result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluR sz op dst (.mem mm), len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value)
    (not_cmp : op ≠ .cmp)
    (result_eq : (AluOp.resultN op (sz.read m.core dst)
      ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits)).setWidth 64
        = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = AluOp.flagsN op (sz.read m.core dst)
        ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits) ∧
      next.memory = m.memory :=
  opaque_writeReg
    (stepOpt_aluR_mem_mk loaded at_offset fits decoded eff width_eq held not_cmp result_eq)

/-! ## Comparisons against memory

`CMP` writes nothing, so these need a slot fact and no permission — the rule
in `SymExec.lean`. Both directions, since a spilled counter can appear on
either side. -/

/-- `cmp r, m` (`3B /r`), the direction-1 form. -/
theorem stepOpt_cmpR_mem_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dst : Silmaril.X86.Reg} {mm : Mem}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluR sz .cmp dst (.mem mm), len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value) :
    stepOpt exit m = some ⟨{ m.core with
        flags := AluOp.flagsN .cmp (sz.read m.core dst)
          ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst eff width_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.aluR sz .cmp dst (.mem mm)).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStepR, readRM,
    loadN_of_holdsLE held, Option.map_some, ite_true, retire]

/-- `cmp m, r` (`39 /r`), the direction-0 form. -/
theorem stepOpt_cmp_mem_reg_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {src : Silmaril.X86.Reg} {mm : Mem}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.alu sz .cmp (.mem mm) src, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value) :
    stepOpt exit m = some ⟨{ m.core with
        flags := AluOp.flagsN .cmp
          ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits)
          (sz.read m.core src),
        rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  subst eff width_eq
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.alu sz .cmp (.mem mm) src).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, aluStep, readRM,
    loadN_of_holdsLE held, Option.map_some, ite_true, retire]

/-- One `cmp r, m`, with the successor left opaque. -/
theorem stepOpt_cmpR_mem {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {dst : Silmaril.X86.Reg} {mm : Mem}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluR sz .cmp dst (.mem mm), len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = AluOp.flagsN .cmp (sz.read m.core dst)
        ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits) ∧
      next.memory = m.memory :=
  opaque_flagsOnly (stepOpt_cmpR_mem_mk loaded at_offset fits decoded eff width_eq held)

/-- One `cmp m, r`, with the successor left opaque. -/
theorem stepOpt_cmp_mem_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {src : Silmaril.X86.Reg} {mm : Mem}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.alu sz .cmp (.mem mm) src, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = AluOp.flagsN .cmp
        ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits)
        (sz.read m.core src) ∧
      next.memory = m.memory :=
  opaque_flagsOnly (stepOpt_cmp_mem_reg_mk loaded at_offset fits decoded eff width_eq held)

/-! ## Returning

`POP` and `RET` both read the word at `%rsp`, so both take a slot fact there,
which is again simultaneously the fault-freedom fact and the value fact. These
two are what an epilogue is made of, and between them they discharge a
contract's `%rsp` and callee-saved clauses without touching the function's
mathematics. -/

/-- One `pop r` from a loaded image. -/
theorem stepOpt_pop_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {r : Silmaril.X86.Reg} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.pop r, len))
    (held : HoldsLE m.memory (m.core.read .rsp).toNat 8 value) :
    stepOpt exit m = some ⟨{ (m.core.write .rsp (m.core.read .rsp + 8#64)).write r value with
      rip := base + BitVec.ofNat 64 (offset + len) }, m.memory⟩ := by
  have popped : X86.popWord m.core m.memory =
      some (value, m.core.write .rsp (m.core.read .rsp + 8#64)) := by
    refine X86.popWord_of_readBytes ?_
    rw [← leBytes_eight]
    exact held
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  have hl : (Instr.pop r).length = len := (decode_length decoded).1.symm
  simp only [exec, hl, at_offset, rip_advance base rfl, popped, Option.map_some, retire]

/-- The `ret` that returns to the designated exit: the word at `%rsp` is
`exit`, so the machine reports `returned` rather than retiring. -/
theorem step_returned_ret_mk {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.ret, len))
    (held : HoldsLE m.memory (m.core.read .rsp).toNat 8 exit) :
    step exit m =
      .returned ⟨{ m.core.write .rsp (m.core.read .rsp + 8#64) with rip := exit }, m.memory⟩ := by
  have popped : X86.popWord m.core m.memory =
      some (exit, m.core.write .rsp (m.core.read .rsp + 8#64)) := by
    refine X86.popWord_of_readBytes ?_
    rw [← leBytes_eight]
    exact held
  refine step_returned_of_loaded (len := len) loaded at_offset fits decoded ?_ rfl
  simp only [exec, popped]

/-! ## The opaque forms

The same steps, with the successor existentially bound and described by
projections instead of named by a structure-update term. These are the forms
to chain; the `…_mk` variants above name the successor and are kept for
callers that want it. -/

/-- One `mov r, m`, with the successor left opaque. -/
theorem stepOpt_load {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {mm : Mem} {r : Silmaril.X86.Reg}
    {address width : Nat} {value result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.load sz r mm, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value)
    (result_eq : ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits).setWidth 64
      = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core r result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_load_mk loaded at_offset fits decoded eff width_eq held result_eq)

/-- One `cmp m, imm8`, with the successor left opaque. -/
theorem stepOpt_cmpI8_mem {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {mm : Mem} {imm : BitVec 8}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluI8 sz .cmp (.mem mm) imm, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : HoldsLE m.memory address width value) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = AluOp.flagsN .cmp
        ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits)
        (imm.signExtend sz.bits) ∧
      next.memory = m.memory :=
  opaque_flagsOnly (stepOpt_cmpI8_mem_mk loaded at_offset fits decoded eff width_eq held)

/-- One `movsxd r64, m32`, with the successor left opaque. -/
theorem stepOpt_movsxd_mem {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {mm : Mem} {dst : Silmaril.X86.Reg}
    {address width : Nat} {value result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movsxd dst (.mem mm), len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : Sz.d.bytes = width)
    (held : HoldsLE m.memory address width value)
    (result_eq :
      ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth 32).signExtend 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_movsxd_mem_mk loaded at_offset fits decoded eff width_eq held result_eq)

/-- One `movzx`/`movsx` from memory, with the successor left opaque. -/
theorem stepOpt_movx_mem {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sx : Bool} {sz : Sz} {nw : Narrow} {dst : Silmaril.X86.Reg} {mm : Mem}
    {address width : Nat} {value result : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movx sx sz nw dst (.mem mm), len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : nw.bytes = width)
    (held : HoldsLE m.memory address width value)
    (result_eq :
      (if sx then
          ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth nw.bits).signExtend sz.bits
        else
          ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth nw.bits).setWidth
            sz.bits).setWidth 64 = result) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core dst result ∧
      next.core.flags = m.core.flags ∧
      next.memory = m.memory :=
  opaque_writeReg_noFlags (stepOpt_movx_mem_mk loaded at_offset fits decoded eff width_eq held result_eq)

/-- One `push r`, with the successor left opaque. -/
theorem stepOpt_push {exit base : Word} {bytes : List Byte} {m : MState} {offset len : Nat}
    {r : Silmaril.X86.Reg}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.push r, len))
    (permitted : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      WritesReg m.core next.core .rsp (m.core.read .rsp - 8#64) ∧
      next.core.flags = m.core.flags ∧
      Stored m.memory next.memory (m.core.read .rsp - 8#64).toNat
        (encodeWords [m.core.read r]) := by
  obtain ⟨after, stepped, stored⟩ := stepOpt_push_mk loaded at_offset fits decoded permitted
  obtain ⟨next, h1, h2, h3, h4, h5⟩ := opaque_writeRegStore stepped
  exact ⟨next, h1, h2, h3, h4, h5 ▸ stored⟩

/-- One store, with the successor left opaque. -/
theorem stepOpt_store_reg {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {mm : Mem} {r : Silmaril.X86.Reg}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.mov sz (.mem mm) r, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (value_eq : (sz.read m.core r).setWidth 64 = value)
    (permitted : m.memory.Permitted .write address width) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = m.core.flags ∧
      Stored m.memory next.memory address (leBytes value width) := by
  obtain ⟨after, stepped, stored⟩ := stepOpt_store_reg_mk loaded at_offset fits decoded eff width_eq value_eq permitted
  obtain ⟨next, h1, h2, h3, h4, h5⟩ := opaque_storeOnly stepped
  exact ⟨next, h1, h2, h3, h4, h5 ▸ stored⟩

/-- One store, with the successor left opaque. -/
theorem stepOpt_store_imm {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {sz : Sz} {mm : Mem} {imm : BitVec 32}
    {address width : Nat} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movI sz (.mem mm) imm, len))
    (eff : (mm.addr m.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (value_eq : (imm.signExtend sz.bits).setWidth 64 = value)
    (permitted : m.memory.Permitted .write address width) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      SameRegs m.core next.core ∧
      next.core.flags = m.core.flags ∧
      Stored m.memory next.memory address (leBytes value width) := by
  obtain ⟨after, stepped, stored⟩ := stepOpt_store_imm_mk loaded at_offset fits decoded eff width_eq value_eq permitted
  obtain ⟨next, h1, h2, h3, h4, h5⟩ := opaque_storeOnly stepped
  exact ⟨next, h1, h2, h3, h4, h5 ▸ stored⟩

/-- One `pop r`, with the successor left opaque. `POP` writes two registers,
so the projections name both. -/
theorem stepOpt_pop {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat} {r : Silmaril.X86.Reg} {value : Word}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.pop r, len))
    (held : HoldsLE m.memory (m.core.read .rsp).toNat 8 value) :
    ∃ next, stepOpt exit m = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      next.core.read r = value ∧
      (r ≠ .rsp → next.core.read .rsp = m.core.read .rsp + 8#64) ∧
      (∀ q, q ≠ r → q ≠ .rsp → next.core.read q = m.core.read q) ∧
      next.core.flags = m.core.flags ∧ next.memory = m.memory :=
  opaque_writeTwo (stepOpt_pop_mk loaded at_offset fits decoded held)

/-- The returning `ret`, with the final state left opaque. -/
theorem step_returned_ret {exit base : Word} {bytes : List Byte} {m : MState}
    {offset len : Nat}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.ret, len))
    (held : HoldsLE m.memory (m.core.read .rsp).toNat 8 exit) :
    ∃ final, step exit m = .returned final ∧
      final.core.rip = exit ∧
      WritesReg m.core final.core .rsp (m.core.read .rsp + 8#64) ∧
      final.core.flags = m.core.flags ∧ final.memory = m.memory :=
  opaque_returned (step_returned_ret_mk loaded at_offset fits decoded held)

end Silmaril.X86.Ext
