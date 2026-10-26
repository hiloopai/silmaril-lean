module

public import Mathlib.Data.BitVec
public import Std.Data.ExtHashMap.Lemmas

/-!
Finite process mappings and byte memory. Addresses are natural numbers with
explicit 64-bit bounds. The mapping granularity is a parameter of well-formedness;
permissions are checked for every byte of an access, including spans crossing
adjacent mappings. An empty access requires a valid address but no mapped bytes.
-/

@[expose] public section

namespace Silmaril.Process

abbrev Byte := BitVec 8
abbrev ByteMemory := Std.ExtHashMap Nat Byte

def addressLimit : Nat := 2 ^ 64

inductive Access where
  | read | write | execute
  deriving DecidableEq, Repr

structure Permissions where
  read : Bool
  write : Bool
  execute : Bool
  deriving DecidableEq, Repr

def Permissions.allows (permissions : Permissions) : Access → Bool
  | .read => permissions.read
  | .write => permissions.write
  | .execute => permissions.execute

structure Region where
  base : Nat
  size : Nat
  permissions : Permissions
  deriving DecidableEq, Repr

def Region.Contains (region : Region) (address : Nat) : Prop :=
  region.base ≤ address ∧ address < region.base + region.size

instance (region : Region) (address : Nat) : Decidable (region.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Region.Disjoint (first second : Region) : Prop :=
  first.base + first.size ≤ second.base ∨ second.base + second.size ≤ first.base

instance (first second : Region) : Decidable (Region.Disjoint first second) :=
  inferInstanceAs (Decidable (_ ∨ _))

structure Memory where
  regions : List Region
  bytes : ByteMemory

namespace Memory

/-- A mapped byte with the requested permission. -/
def permits (memory : Memory) (access : Access) (address : Nat) : Bool :=
  memory.regions.any fun region => decide (region.Contains address) && region.permissions.allows access

/-- Check the entire non-wrapping span before carrying out an access. -/
def checkSpan (memory : Memory) (access : Access) (address length : Nat) : Bool :=
  decide (address < addressLimit ∧ address + length ≤ addressLimit) &&
    (List.range length).all (fun offset => memory.permits access (address + offset))

def Permitted (memory : Memory) (access : Access) (address length : Nat) : Prop :=
  memory.checkSpan access address length = true

instance (memory : Memory) (access : Access) (address length : Nat) :
    Decidable (memory.Permitted access address length) := inferInstanceAs (Decidable (_ = _))

@[simp] theorem checkSpan_iff (memory : Memory) (access : Access) (address length : Nat) :
    memory.checkSpan access address length = true ↔
      address < addressLimit ∧ address + length ≤ addressLimit ∧
        ∀ offset < length, memory.permits access (address + offset) = true := by
  simp [checkSpan, List.all_eq_true, and_assoc]

/-- Read backing bytes after the permission check; missing backing also faults. -/
def readBacking (bytes : ByteMemory) (address : Nat) : Nat → Option (List Byte)
  | 0 => some []
  | length + 1 => do
      let byte ← bytes.get? address
      let tail ← readBacking bytes (address + 1) length
      pure (byte :: tail)

def readWith (memory : Memory) (access : Access) (address length : Nat) : Option (List Byte) :=
  if memory.checkSpan access address length then readBacking memory.bytes address length else none

def readBytes (memory : Memory) (address length : Nat) : Option (List Byte) :=
  memory.readWith .read address length

def fetchBytes (memory : Memory) (address length : Nat) : Option (List Byte) :=
  memory.readWith .execute address length

/-- Total finite overwrite; permissions are enforced by `writeBytes`. -/
def install (memory : ByteMemory) (base : Nat) : List Byte → ByteMemory
  | [] => memory
  | byte :: bytes => (install memory (base + 1) bytes).insert base byte

def writeBytes (memory : Memory) (address : Nat) (bytes : List Byte) : Option Memory :=
  if memory.checkSpan .write address bytes.length then
    some { memory with bytes := install memory.bytes address bytes }
  else none

/-- Both mapping metadata and every byte outside the interval are unchanged. -/
def WritesOnly (before after : Memory) (address length : Nat) : Prop :=
  after.regions = before.regions ∧
    ∀ location, location < address ∨ address + length ≤ location →
      after.bytes.get? location = before.bytes.get? location

/-! ### Modifies sets

`WritesOnly` names one interval. A procedure contract generally has a
footprint that is a *union* of intervals — an output buffer and a stack frame,
say — so the primitive below takes the set of writable addresses as a
predicate. `writesOnly_iff_writesWithin` shows the single-interval case is an
instance.

As in `WritesOnly`, mapping metadata being unchanged is part of the claim:
a step that unmapped a region would otherwise count as writing nothing. -/

/-- Mapping metadata is unchanged, and every byte outside `inside` is
unchanged. -/
def WritesWithin (before after : Memory) (inside : Nat → Prop) : Prop :=
  after.regions = before.regions ∧
    ∀ location, ¬ inside location → after.bytes.get? location = before.bytes.get? location

theorem writesOnly_iff_writesWithin (before after : Memory) (address length : Nat) :
    WritesOnly before after address length ↔
      WritesWithin before after (fun location => address ≤ location ∧ location < address + length) := by
  constructor
  · exact fun h => ⟨h.1, fun l hl => h.2 l (by omega)⟩
  · exact fun h => ⟨h.1, fun l hl => h.2 l (by omega)⟩

theorem WritesWithin.refl (memory : Memory) (inside : Nat → Prop) :
    WritesWithin memory memory inside := ⟨rfl, fun _ _ => rfl⟩

/-- A larger footprint is a weaker claim. -/
theorem WritesWithin.mono {before after : Memory} {inside wider : Nat → Prop}
    (h : WritesWithin before after inside) (hsub : ∀ location, inside location → wider location) :
    WritesWithin before after wider :=
  ⟨h.1, fun l hl => h.2 l (fun hin => hl (hsub l hin))⟩

theorem WritesWithin.trans {first second third : Memory} {inside : Nat → Prop}
    (h1 : WritesWithin first second inside) (h2 : WritesWithin second third inside) :
    WritesWithin first third inside :=
  ⟨h2.1.trans h1.1, fun l hl => (h2.2 l hl).trans (h1.2 l hl)⟩

/-- Permissions are a function of `regions`, which `WritesWithin` freezes. -/
theorem WritesWithin.permits {before after : Memory} {inside : Nat → Prop}
    (h : WritesWithin before after inside) (access : Access) (address : Nat) :
    after.permits access address = before.permits access address := by
  unfold Memory.permits; rw [h.1]

theorem WritesWithin.permitted_iff {before after : Memory} {inside : Nat → Prop}
    (h : WritesWithin before after inside) (access : Access) (address length : Nat) :
    after.Permitted access address length ↔ before.Permitted access address length := by
  unfold Permitted checkSpan
  simp only [h.permits]

/-- Backing reads depend only on the bytes they touch. -/
theorem readBacking_congr {first second : ByteMemory} {address length : Nat}
    (h : ∀ offset < length, first.get? (address + offset) = second.get? (address + offset)) :
    readBacking first address length = readBacking second address length := by
  induction length generalizing address with
  | zero => rfl
  | succ length ih =>
    have head := h 0 (by omega)
    have tail : ∀ offset < length,
        first.get? (address + 1 + offset) = second.get? (address + 1 + offset) := by
      intro offset hoffset
      have := h (offset + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 offset] using this
    simp only [readBacking, Nat.add_zero] at head ⊢
    rw [head, ih tail]

/-- A read that touches no written byte returns exactly what it would have
before: the permission check agrees because `regions` is unchanged, and the
bytes agree because none of them is in the footprint. -/
theorem WritesWithin.readWith {before after : Memory} {inside : Nat → Prop}
    (h : WritesWithin before after inside) {access : Access} {address length : Nat}
    (hout : ∀ offset < length, ¬ inside (address + offset)) :
    after.readWith access address length = before.readWith access address length := by
  unfold Memory.readWith
  have hcheck : after.checkSpan access address length = before.checkSpan access address length := by
    unfold checkSpan; simp only [h.permits]
  rw [hcheck, readBacking_congr (fun offset hoffset => h.2 _ (hout offset hoffset))]

theorem WritesWithin.readBytes {before after : Memory} {inside : Nat → Prop}
    (h : WritesWithin before after inside) {address length : Nat}
    (hout : ∀ offset < length, ¬ inside (address + offset)) :
    after.readBytes address length = before.readBytes address length :=
  h.readWith hout

theorem WritesWithin.fetchBytes {before after : Memory} {inside : Nat → Prop}
    (h : WritesWithin before after inside) {address length : Nat}
    (hout : ∀ offset < length, ¬ inside (address + offset)) :
    after.fetchBytes address length = before.fetchBytes address length :=
  h.readWith hout

/-- Nonempty, aligned, bounded disjoint regions, with backing for every mapped byte. -/
structure WellFormed (memory : Memory) (pageSize : Nat) : Prop where
  pageSize_pos : 0 < pageSize
  region_valid : ∀ region ∈ memory.regions,
    0 < region.size ∧ region.base % pageSize = 0 ∧ region.size % pageSize = 0 ∧
      region.base + region.size ≤ addressLimit
  disjoint : memory.regions.Pairwise Region.Disjoint
  backed : ∀ region ∈ memory.regions, ∀ address, region.Contains address →
    (memory.bytes.get? address).isSome = true

theorem install_get (memory : ByteMemory) (base : Nat) (bytes : List Byte)
    (index : Nat) (bound : index < bytes.length) :
    (install memory base bytes).get? (base + index) = some (bytes[index]) := by
  induction bytes generalizing base index with
  | nil => simp at bound
  | cons byte bytes ih =>
    cases index with
    | zero => simp [install]
    | succ index =>
      have different : base ≠ base + (index + 1) := by omega
      simpa [install, Std.ExtHashMap.getElem?_insert, different, Nat.add_assoc,
        Nat.add_comm 1 index] using ih (base + 1) index (by simpa using bound)

theorem install_outside (memory : ByteMemory) (base : Nat) (bytes : List Byte)
    (address : Nat) (outside : address < base ∨ base + bytes.length ≤ address) :
    (install memory base bytes).get? address = memory.get? address := by
  induction bytes generalizing base with
  | nil => rfl
  | cons byte bytes ih =>
    have different : base ≠ address := by simp only [List.length_cons] at outside; omega
    have remaining : address < base + 1 ∨ base + 1 + bytes.length ≤ address := by
      simp only [List.length_cons] at outside
      omega
    simpa [install, Std.ExtHashMap.getElem?_insert, different] using ih (base + 1) remaining

theorem writeBytes_permitted {before after : Memory} {address : Nat} {bytes : List Byte}
    (written : before.writeBytes address bytes = some after) :
    before.Permitted .write address bytes.length := by
  unfold writeBytes at written
  split at written
  · assumption
  · contradiction

theorem writeBytes_writesOnly {before after : Memory} {address : Nat} {bytes : List Byte}
    (written : before.writeBytes address bytes = some after) :
    WritesOnly before after address bytes.length := by
  unfold writeBytes at written
  split at written
  · cases written
    exact ⟨rfl, fun location outside => install_outside _ _ _ _ outside⟩
  · contradiction

theorem writeBytes_get {before after : Memory} {address : Nat} {bytes : List Byte}
    (written : before.writeBytes address bytes = some after)
    (index : Nat) (bound : index < bytes.length) :
    after.bytes.get? (address + index) = some (bytes[index]) := by
  unfold writeBytes at written
  split at written
  · cases written
    exact install_get _ _ _ _ bound
  · contradiction

theorem writeBytes_wellFormed {before after : Memory} {address pageSize : Nat}
    {bytes : List Byte} (wellFormed : before.WellFormed pageSize)
    (written : before.writeBytes address bytes = some after) : after.WellFormed pageSize := by
  unfold writeBytes at written
  split at written
  · cases written
    refine ⟨wellFormed.pageSize_pos, wellFormed.region_valid, wellFormed.disjoint, ?_⟩
    intro region member location inside
    by_cases overwritten : address ≤ location ∧ location < address + bytes.length
    · have bound : location - address < bytes.length := by omega
      have lookup := install_get before.bytes address bytes (location - address) bound
      have eq : address + (location - address) = location := by omega
      rw [eq] at lookup
      change ((install before.bytes address bytes).get? location).isSome = true
      rw [lookup]
      rfl
    · have outside : location < address ∨ address + bytes.length ≤ location := by omega
      change ((install before.bytes address bytes).get? location).isSome = true
      rw [install_outside _ _ _ _ outside]
      exact wellFormed.backed region member location inside
  · contradiction

theorem readBacking_length {memory : ByteMemory} {address length : Nat} {bytes : List Byte}
    (read : readBacking memory address length = some bytes) : bytes.length = length := by
  induction length generalizing address bytes with
  | zero => simp [readBacking] at read; subst bytes; rfl
  | succ length ih =>
    simp only [readBacking, Option.bind_eq_bind] at read
    cases first : memory[address]? with
    | none => simp [first] at read
    | some byte =>
      cases rest : readBacking memory (address + 1) length with
      | none => simp [first, rest] at read
      | some tail =>
        simp [first, rest] at read
        subst bytes
        simp [ih rest]

theorem readBacking_eq (memory : ByteMemory) (address : Nat) (bytes : List Byte)
    (installed : ∀ index (bound : index < bytes.length),
      memory.get? (address + index) = some (bytes[index])) :
    readBacking memory address bytes.length = some bytes := by
  induction bytes generalizing address with
  | nil => rfl
  | cons byte bytes ih =>
    have first := installed 0 (by simp)
    change memory.get? (address + 0) = some byte at first
    simp only [Nat.add_zero, Std.ExtHashMap.get?_eq_getElem?] at first
    have rest : ∀ index (bound : index < bytes.length),
        memory.get? (address + 1 + index) = some (bytes[index]) := by
      intro index bound
      have value := installed (index + 1) (by simp; omega)
      change memory.get? (address + (index + 1)) = some (bytes[index]) at value
      simpa only [Nat.add_assoc, Nat.add_comm 1 index] using value
    simp [readBacking, first, ih (address + 1) rest]

theorem readWith_permitted {memory : Memory} {access : Access} {address length : Nat}
    {bytes : List Byte} (read : memory.readWith access address length = some bytes) :
    memory.Permitted access address length := by
  unfold readWith at read
  split at read
  · assumption
  · contradiction

theorem readWith_length {memory : Memory} {access : Access} {address length : Nat}
    {bytes : List Byte} (read : memory.readWith access address length = some bytes) :
    bytes.length = length := by
  unfold readWith at read
  split at read
  · exact readBacking_length read
  · contradiction

theorem readWith_eq (memory : Memory) (access : Access) (address : Nat) (bytes : List Byte)
    (permitted : memory.Permitted access address bytes.length)
    (installed : ∀ index (bound : index < bytes.length),
      memory.bytes.get? (address + index) = some (bytes[index])) :
    memory.readWith access address bytes.length = some bytes := by
  have check : memory.checkSpan access address bytes.length = true := permitted
  simp only [readWith, check, ↓reduceIte]
  exact readBacking_eq _ _ _ installed

/-- Successful reads expose exactly the backing byte at every requested offset. -/
theorem readBacking_get {memory : ByteMemory} {address length : Nat} {bytes : List Byte}
    (read : readBacking memory address length = some bytes)
    (index : Nat) (bound : index < bytes.length) :
    memory.get? (address + index) = some (bytes[index]) := by
  induction length generalizing address bytes index with
  | zero => simp [readBacking] at read; subst bytes; simp at bound
  | succ length ih =>
    simp only [readBacking, Option.bind_eq_bind] at read
    cases first : memory[address]? with
    | none => simp [first] at read
    | some byte =>
      cases rest : readBacking memory (address + 1) length with
      | none => simp [first, rest] at read
      | some tail =>
        simp [first, rest] at read
        subst bytes
        cases index with
        | zero => simpa using first
        | succ index =>
          have value := ih rest index (by simpa using bound)
          simpa only [Nat.add_assoc, Nat.add_comm 1 index, List.getElem_cons_succ] using value

/-- A successful access lies below the address limit. -/
theorem readWith_bound {memory : Memory} {access : Access} {address length : Nat}
    {bytes : List Byte} (read : memory.readWith access address length = some bytes) :
    address + length ≤ addressLimit := by
  have permitted := readWith_permitted read
  rw [Permitted, checkSpan_iff] at permitted
  exact permitted.2.1

theorem readWith_get {memory : Memory} {access : Access} {address length : Nat}
    {bytes : List Byte} (read : memory.readWith access address length = some bytes)
    (index : Nat) (bound : index < bytes.length) :
    memory.bytes.get? (address + index) = some (bytes[index]) := by
  unfold readWith at read
  split at read
  · exact readBacking_get read index bound
  · contradiction

/-! ## Sub-ranges of a successful read

A calling convention hands an input buffer over as **one** read — `block[]` is
`readBytes block 64 = some blockBytes` — while the compiled code loads four
bytes at a time. These two lemmas are the bridge, and they are the first thing
in the way of any data invariant over a buffer.

Note the `start : offset < length` hypothesis. It cannot be dropped: a
zero-length read at `addressLimit` fails `checkSpan`'s `address <
addressLimit` conjunct, so `readWith access addressLimit 0 = none` while
`(bytes.drop offset).take 0 = []`. Requiring `offset < length` rules that out
and, unlike requiring `0 < len`, still covers the empty sub-range. -/

/-- A successful read contains its sub-reads. -/
theorem readWith_sub_range {memory : Memory} {access : Access} {address length : Nat}
    {bytes : List Byte} (read : memory.readWith access address length = some bytes)
    {offset len : Nat} (start : offset < length) (fits : offset + len ≤ length) :
    memory.readWith access (address + offset) len = some ((bytes.drop offset).take len) := by
  have hlen : bytes.length = length := readWith_length read
  have hspan : memory.Permitted access address length := readWith_permitted read
  rw [Permitted, checkSpan_iff] at hspan
  obtain ⟨hstart, hlimit, hperm⟩ := hspan
  have hslice : ((bytes.drop offset).take len).length = len := by
    simp only [List.length_take, List.length_drop, hlen]
    omega
  have hpermitted : memory.Permitted access (address + offset)
      ((bytes.drop offset).take len).length := by
    rw [hslice, Permitted, checkSpan_iff]
    refine ⟨by omega, by omega, fun o ho => ?_⟩
    have := hperm (offset + o) (by omega)
    rwa [show address + (offset + o) = address + offset + o by omega] at this
  have key : memory.readWith access (address + offset)
      ((bytes.drop offset).take len).length = some ((bytes.drop offset).take len) := by
    refine readWith_eq memory access (address + offset) _ hpermitted ?_
    intro index bound
    rw [hslice] at bound
    have hget := readWith_get read (offset + index) (by omega)
    rw [show address + (offset + index) = address + offset + index by omega] at hget
    rw [hget]
    congr 1
    rw [List.getElem_take, List.getElem_drop]
  rwa [hslice] at key

/-- A successful `readBytes` contains its sub-reads: the form a data
invariant over an input buffer wants, since every load in compiled code is a
sub-range of the buffer the precondition names. -/
theorem readBytes_sub_range {memory : Memory} {address length : Nat} {bytes : List Byte}
    (read : memory.readBytes address length = some bytes)
    {offset len : Nat} (start : offset < length) (fits : offset + len ≤ length) :
    memory.readBytes (address + offset) len = some ((bytes.drop offset).take len) :=
  readWith_sub_range read start fits

/-! ### Joining abutting reads

Narrowing a read is free at any width (`readWith_sub_range` and friends).
**Widening is not**, and it is what a write-back needs: a postcondition that
names one wide buffer — SHA-256's `state[0..32)`, say — has to be assembled
from the narrow stores the compiled code actually performs, eight four-byte
ones in that case.

These are stated over two abutting `readWith`s at arbitrary widths rather than
at one concrete width, and `readBytes_run` iterates them. Nothing here mentions
an instruction set.

Note the empty case is genuinely special: `readWith access address 0` is
`some []` only when `address < addressLimit`, because `checkSpan` tests that
strictly. `readBytes_run` is therefore stated for `count + 1` chunks, so the
degenerate case never arises. -/

/-- Two abutting backing reads concatenate. -/
theorem readBacking_append {bytes : ByteMemory} {address first second : Nat}
    {xs ys : List Byte}
    (hx : readBacking bytes address first = some xs)
    (hy : readBacking bytes (address + first) second = some ys) :
    readBacking bytes address (first + second) = some (xs ++ ys) := by
  induction first generalizing address xs with
  | zero =>
    simp only [readBacking, Option.some.injEq] at hx
    subst hx
    simpa using hy
  | succ first ih =>
    rw [readBacking] at hx
    cases hb : bytes.get? address with
    | none => rw [hb] at hx; simp at hx
    | some byte =>
      rw [hb] at hx
      cases ht : readBacking bytes (address + 1) first with
      | none => rw [ht] at hx; simp at hx
      | some tail =>
        rw [ht] at hx
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hx
        subst hx
        have hy' : readBacking bytes (address + 1 + first) second = some ys := by
          rw [show address + 1 + first = address + (first + 1) by omega]; exact hy
        have joined := ih ht hy'
        rw [show first + 1 + second = first + second + 1 by omega, readBacking, hb, joined]
        simp

/-- Two abutting permitted spans make one permitted span. -/
theorem checkSpan_append {memory : Memory} {access : Access} {address first second : Nat}
    (hx : memory.checkSpan access address first = true)
    (hy : memory.checkSpan access (address + first) second = true) :
    memory.checkSpan access address (first + second) = true := by
  rw [checkSpan_iff] at hx hy ⊢
  obtain ⟨lo, hi, perm⟩ := hx
  obtain ⟨-, hi', perm'⟩ := hy
  refine ⟨lo, by omega, fun offset bound => ?_⟩
  rcases Nat.lt_or_ge offset first with inside | beyond
  · exact perm offset inside
  · have := perm' (offset - first) (by omega)
    rwa [show address + first + (offset - first) = address + offset by omega] at this

/-- **Widening.** Two abutting successful reads join into one wide read. -/
theorem readWith_append {memory : Memory} {access : Access} {address first second : Nat}
    {xs ys : List Byte}
    (hx : memory.readWith access address first = some xs)
    (hy : memory.readWith access (address + first) second = some ys) :
    memory.readWith access address (first + second) = some (xs ++ ys) := by
  have cx : memory.checkSpan access address first = true := readWith_permitted hx
  have cy : memory.checkSpan access (address + first) second = true := readWith_permitted hy
  have cz := checkSpan_append cx cy
  simp only [readWith, cx, cy, cz, ite_true] at hx hy ⊢
  exact readBacking_append hx hy

theorem readBytes_append {memory : Memory} {address first second : Nat} {xs ys : List Byte}
    (hx : memory.readBytes address first = some xs)
    (hy : memory.readBytes (address + first) second = some ys) :
    memory.readBytes address (first + second) = some (xs ++ ys) :=
  readWith_append hx hy

theorem fetchBytes_append {memory : Memory} {address first second : Nat} {xs ys : List Byte}
    (hx : memory.fetchBytes address first = some xs)
    (hy : memory.fetchBytes (address + first) second = some ys) :
    memory.fetchBytes address (first + second) = some (xs ++ ys) :=
  readWith_append hx hy

/-- **Widening, iterated.** A run of `count + 1` abutting equal-width reads is
one read of the whole run. This is the shape a feed-forward write-back wants:
with `width = 4` and `count = 7` it turns eight four-byte stores at
`address + 4 * i` into the single 32-byte read a postcondition names. -/
theorem readBytes_run {memory : Memory} {width : Nat} :
    ∀ (count address : Nat) (chunk : Nat → List Byte),
      (∀ i ≤ count, memory.readBytes (address + width * i) width = some (chunk i)) →
      memory.readBytes address (width * (count + 1))
        = some ((List.range (count + 1)).flatMap chunk) := by
  intro count
  induction count with
  | zero =>
    intro address chunk h
    have := h 0 (Nat.le_refl 0)
    simpa using this
  | succ count ih =>
    intro address chunk h
    have head := ih address chunk (fun i hi => h i (by omega))
    have tail := h (count + 1) (Nat.le_refl _)
    have joined := readBytes_append head tail
    rw [← Nat.mul_succ] at joined
    rw [joined]
    simp [List.range_succ]

/-- A single permitting region suffices for a fully contained access. -/
theorem permitted_of_region (memory : Memory) (access : Access) (address length : Nat)
    (region : Region) (member : region ∈ memory.regions)
    (allowed : region.permissions.allows access = true)
    (start : address < addressLimit) (limit : address + length ≤ addressLimit)
    (lower : region.base ≤ address) (upper : address + length ≤ region.base + region.size) :
    memory.Permitted access address length := by
  rw [Permitted, checkSpan_iff]
  refine ⟨start, limit, ?_⟩
  intro offset bound
  simp only [permits, List.any_eq_true]
  refine ⟨region, member, ?_⟩
  have inside : region.Contains (address + offset) := by unfold Region.Contains; omega
  simp [inside, allowed]

/-- Initializers may install finite byte blocks while retaining all existing backing. -/
theorem install_wellFormed {memory : Memory} {pageSize : Nat}
    (wellFormed : memory.WellFormed pageSize) (address : Nat) (bytes : List Byte) :
    ({ memory with bytes := install memory.bytes address bytes } : Memory).WellFormed pageSize := by
  refine ⟨wellFormed.pageSize_pos, wellFormed.region_valid, wellFormed.disjoint, ?_⟩
  intro region member location inside
  by_cases overwritten : address ≤ location ∧ location < address + bytes.length
  · have bound : location - address < bytes.length := by omega
    have lookup := install_get memory.bytes address bytes (location - address) bound
    have eq : address + (location - address) = location := by omega
    rw [eq] at lookup
    change ((install memory.bytes address bytes).get? location).isSome = true
    rw [lookup]
    rfl
  · have outside : location < address ∨ address + bytes.length ≤ location := by omega
    change ((install memory.bytes address bytes).get? location).isSome = true
    rw [install_outside _ _ _ _ outside]
    exact wellFormed.backed region member location inside

end Memory
end Silmaril.Process
