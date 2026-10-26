module

public import Silmaril.X86.Ext.Machine
public import Silmaril.X86.Ext.Decode
public import Mathlib.Data.List.Chain

/-!
# Addressed code regions

`Ext.decodeAll` walks a byte string and returns instructions; it never mentions
an address. Partitioning a code image into functions needs addresses: a branch
target is an address, a function extent is a range of addresses, and the
machine fetches at an address. `Region` adds the missing datum — the virtual
address of the first byte — and `Region.decode?` returns a listing in which
every instruction carries its own address and encoded length.

## What a successful listing says

The listing is not a disassembly in the usual sense. `Ext.decode` re-encodes
what it reads and demands that the result is a prefix of the input
(`Ext.decode_eq_some_iff`), so a successful walk gives, in addition to the
instructions:

* `decode?_covers` — the region's bytes are exactly the concatenation of the
  canonical encodings, so no byte is skipped and no instruction is spelled
  differently from the way `Ext.encode` spells it;
* `decode?_chain` and `decode?_addr_pairwise` — the addresses start at `base`,
  each is the previous one plus the previous size, and they strictly increase;
* `decode?_fetch` — in any memory holding the region, the machine's
  `Ext.fetch` at each listed address returns exactly the listed instruction and
  length. This is the bridge from the static listing to `Ext.step`.

## Holding a region in memory

`Region.LoadedIn` is stated as "every span inside the region fetches to the
corresponding bytes" rather than as the single span `fetchBytes base
bytes.length = some bytes`. The two are equivalent for a well-formed memory,
but the span form is what every use needs, and deriving it from the single
span would require sub-span lemmas about `Memory.readBacking` that are not
otherwise needed here.

Addresses are plain `Nat`, not `BitVec 64`. A region whose bytes run past
`2^64` is not excluded by the type; `Decoded.next` takes the wrap into account
where it matters (see `Decompile.Edges`).
-/

@[expose] public section

namespace Silmaril.X86.Decompile

open Silmaril.X86 (Byte)
open Silmaril.Process (Memory)

/-! ## Regions and listings -/

/-- A region of code: `base` is the virtual address of `bytes[0]`. -/
structure Region where
  /-- The virtual address of the first byte. -/
  base : Nat
  /-- The bytes of the region, in increasing address order. -/
  bytes : List Byte
  deriving DecidableEq, Repr

/-- One decoded instruction, with its address and encoded length. -/
structure Decoded where
  /-- The address of the instruction's first byte. -/
  addr : Nat
  /-- The instruction. -/
  instr : Ext.Instr
  /-- The number of bytes the instruction occupies. -/
  size : Nat
  deriving DecidableEq, Repr

/-- Why decoding a region failed. -/
inductive DecodeError where
  /-- No instruction of the model starts at this address. -/
  | undecodable (addr : Nat)
  /-- The fuel ran out before the bytes did. -/
  | outOfFuel
  deriving DecidableEq, Repr

/-- Decode `bytes` from the front, repeatedly, recording the address of each
instruction starting from `addr`. -/
def decodeFrom : Nat → Nat → List Byte → Except DecodeError (List Decoded)
  | _, _, [] => .ok []
  | 0, _, _ => .error .outOfFuel
  | fuel + 1, addr, bytes =>
    match Ext.decode bytes with
    | none => .error (.undecodable addr)
    | some (i, n) =>
      if n = 0 then .error (.undecodable addr)
      else (decodeFrom fuel (addr + n) (bytes.drop n)).map (⟨addr, i, n⟩ :: ·)

/-- Decode a whole region from its base, recording addresses. The error names
the address at which decoding stopped, or reports exhausted fuel. -/
def Region.decode (r : Region) (fuel : Nat) : Except DecodeError (List Decoded) :=
  decodeFrom fuel r.base r.bytes

/-- Decode a whole region from its base, recording addresses. `none` if any
byte range fails to decode or the fuel runs out. -/
def Region.decode? (r : Region) (fuel : Nat) : Option (List Decoded) :=
  (r.decode fuel).toOption

/-! ## Instruction boundaries -/

/-- The addresses at which a listing has an instruction. -/
def starts (ds : List Decoded) : List Nat := ds.map Decoded.addr

/-- `addr` is the address of an instruction of the listing. -/
def IsStart (ds : List Decoded) (addr : Nat) : Prop := addr ∈ starts ds

instance (ds : List Decoded) (addr : Nat) : Decidable (IsStart ds addr) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- The instruction of the listing at `addr`, if there is one. -/
def at? (ds : List Decoded) (addr : Nat) : Option Decoded :=
  ds.find? fun d => d.addr == addr

/-- A memory holds the region: every span inside it fetches, with execute
permission, to the region's own bytes. -/
def Region.LoadedIn (r : Region) (memory : Memory) : Prop :=
  ∀ offset length, offset + length ≤ r.bytes.length →
    memory.fetchBytes (r.base + offset) length = some ((r.bytes.drop offset).take length)

/-! ## Holding a region: `LoadedIn` is inhabited -/

/-- A memory holding exactly this region, mapped readable and executable and
backed by the region's own bytes. -/
def Region.load (r : Region) : Memory where
  regions := [⟨r.base, r.bytes.length, ⟨true, false, true⟩⟩]
  bytes := Memory.install ∅ r.base r.bytes

/-- **`LoadedIn` is inhabited.** `Region.load` holds the region, for every
region that ends strictly below the address limit.

The inequality is strict only because of the empty span at the very end:
`Memory.checkSpan` requires the start address itself to be below
`Process.addressLimit`, so a region butted exactly against `2^64` would fail
`LoadedIn` at `offset = bytes.length, length = 0`. No real region is, and every
hypothesis `r.LoadedIn m.memory` elsewhere in this directory is therefore
satisfiable. -/
theorem Region.loadedIn_load (r : Region) (h : r.base + r.bytes.length < Process.addressLimit) :
    r.LoadedIn r.load := by
  intro offset length hle
  have hlen : ((r.bytes.drop offset).take length).length = length := by
    simp only [List.length_take, List.length_drop]
    omega
  have hspan : Memory.checkSpan r.load .execute (r.base + offset) length = true := by
    simp only [Memory.checkSpan, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
    refine ⟨⟨by omega, by omega⟩, fun k hk => ?_⟩
    simp only [Memory.permits, Region.load, List.any_cons, List.any_nil, Bool.or_false,
      Bool.and_eq_true, Process.Region.Contains, Process.Permissions.allows]
    exact ⟨decide_eq_true (by omega), trivial⟩
  show (if Memory.checkSpan _ _ _ _ = true then _ else _) = _
  simp only [hspan, ite_true]
  conv_lhs => rw [← hlen]
  refine Memory.readBacking_eq _ _ _ fun index bound => ?_
  rw [hlen] at bound
  have hget := Memory.install_get (∅ : Process.ByteMemory) r.base r.bytes (offset + index)
    (by omega)
  rw [show r.base + offset + index = r.base + (offset + index) by omega]
  simp only [Region.load]
  rw [hget]
  congr 1
  simp [List.getElem_take, List.getElem_drop]

/-! ## What a successful listing says -/

/-- `decode?` succeeds exactly when `decode` does. -/
theorem Region.decode?_eq_some_iff {r : Region} {fuel : Nat} {ds : List Decoded} :
    r.decode? fuel = some ds ↔ r.decode fuel = .ok ds := by
  unfold Region.decode?
  cases r.decode fuel <;> simp [Except.toOption]

/-- The shape of a successful walk: the bytes are the concatenation of the
canonical encodings, each size is an encoded length, each address is the
previous one plus the previous size, and the first is the one walked from. -/
theorem decodeFrom_spec : ∀ (fuel addr : Nat) (bytes : List Byte) (ds : List Decoded),
    decodeFrom fuel addr bytes = .ok ds →
    bytes = (ds.map fun d => Ext.encode d.instr).flatten ∧
      (∀ d ∈ ds, d.size = (Ext.encode d.instr).length) ∧
      List.IsChain (fun d e => e.addr = d.addr + d.size) ds ∧
      (∀ d ∈ ds.head?, d.addr = addr) := by
  intro fuel
  induction fuel with
  | zero =>
    intro addr bytes ds h
    cases bytes with
    | nil => simp only [decodeFrom, Except.ok.injEq] at h; subst h; simp
    | cons b t => simp [decodeFrom] at h
  | succ fuel ih =>
    intro addr bytes ds h
    cases bytes with
    | nil => simp only [decodeFrom, Except.ok.injEq] at h; subst h; simp
    | cons b t =>
      simp only [decodeFrom] at h
      split at h
      · simp at h
      · rename_i i n hd
        split at h
        · simp at h
        · cases hrest : decodeFrom fuel (addr + n) ((b :: t).drop n) with
          | error e => rw [hrest] at h; simp [Except.map] at h
          | ok tail =>
            rw [hrest] at h
            simp only [Except.map, Except.ok.injEq] at h
            subst h
            obtain ⟨hb, hsize, hchain, hhead⟩ := ih (addr + n) ((b :: t).drop n) tail hrest
            obtain ⟨hn, hsplit⟩ := Ext.decode_sound hd
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [List.map_cons, List.flatten_cons, ← hb]
              exact hsplit
            · intro d hdmem
              rcases List.mem_cons.mp hdmem with rfl | hm
              · exact hn
              · exact hsize d hm
            · cases tail with
              | nil => exact List.IsChain.singleton _
              | cons e rest =>
                exact List.IsChain.cons_cons (hhead e (by simp)) hchain
            · intro d hd'
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd'
              subst hd'
              rfl

/-- Every instruction of a successful walk lies inside the bytes walked, at the
offset its address names, and the bytes there are its canonical encoding. -/
theorem decodeFrom_mem : ∀ (fuel addr : Nat) (bytes : List Byte) (ds : List Decoded),
    decodeFrom fuel addr bytes = .ok ds →
    ∀ d ∈ ds, addr ≤ d.addr ∧ d.addr + d.size ≤ addr + bytes.length ∧
      (bytes.drop (d.addr - addr)).take d.size = Ext.encode d.instr := by
  intro fuel
  induction fuel with
  | zero =>
    intro addr bytes ds h
    cases bytes with
    | nil => simp only [decodeFrom, Except.ok.injEq] at h; subst h; simp
    | cons b t => simp [decodeFrom] at h
  | succ fuel ih =>
    intro addr bytes ds h
    cases bytes with
    | nil => simp only [decodeFrom, Except.ok.injEq] at h; subst h; simp
    | cons b t =>
      simp only [decodeFrom] at h
      split at h
      · simp at h
      · rename_i i n hd
        split at h
        · simp at h
        · cases hrest : decodeFrom fuel (addr + n) ((b :: t).drop n) with
          | error e => rw [hrest] at h; simp [Except.map] at h
          | ok tail =>
            rw [hrest] at h
            simp only [Except.map, Except.ok.injEq] at h
            subst h
            obtain ⟨hn, hsplit⟩ := Ext.decode_sound hd
            obtain ⟨-, -, -, hle⟩ := Ext.decode_length hd
            intro d hdmem
            rcases List.mem_cons.mp hdmem with rfl | hm
            · refine ⟨Nat.le_refl _, by simpa using hle, ?_⟩
              simp only [Nat.sub_self, List.drop_zero]
              conv_lhs => rw [hsplit]
              rw [hn, List.take_left]
            · obtain ⟨h1, h2, h3⟩ := ih (addr + n) ((b :: t).drop n) tail hrest d hm
              rw [List.length_drop] at h2
              refine ⟨by omega, by omega, ?_⟩
              rw [List.drop_drop] at h3
              rwa [show n + (d.addr - (addr + n)) = d.addr - addr by omega] at h3

/-- The addresses of a successful walk strictly increase. -/
theorem decodeFrom_pairwise : ∀ (fuel addr : Nat) (bytes : List Byte) (ds : List Decoded),
    decodeFrom fuel addr bytes = .ok ds → (starts ds).Pairwise (· < ·) := by
  intro fuel
  induction fuel with
  | zero =>
    intro addr bytes ds h
    cases bytes with
    | nil => simp only [decodeFrom, Except.ok.injEq] at h; subst h; simp [starts]
    | cons b t => simp [decodeFrom] at h
  | succ fuel ih =>
    intro addr bytes ds h
    cases bytes with
    | nil => simp only [decodeFrom, Except.ok.injEq] at h; subst h; simp [starts]
    | cons b t =>
      simp only [decodeFrom] at h
      split at h
      · simp at h
      · rename_i i n hd
        split at h
        · simp at h
        · rename_i hn0
          cases hrest : decodeFrom fuel (addr + n) ((b :: t).drop n) with
          | error e => rw [hrest] at h; simp [Except.map] at h
          | ok tail =>
            rw [hrest] at h
            simp only [Except.map, Except.ok.injEq] at h
            subst h
            simp only [starts, List.map_cons, List.pairwise_cons]
            refine ⟨?_, ih (addr + n) ((b :: t).drop n) tail hrest⟩
            intro a ha
            simp only [List.mem_map] at ha
            obtain ⟨d, hdmem, rfl⟩ := ha
            have := (decodeFrom_mem fuel (addr + n) ((b :: t).drop n) tail hrest d hdmem).1
            have hn : 0 < n := Nat.pos_of_ne_zero hn0
            omega

/-- Every listed size is the encoded length of the listed instruction. -/
theorem Region.decode?_size {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) : ∀ d ∈ ds, d.size = (Ext.encode d.instr).length :=
  (decodeFrom_spec fuel r.base r.bytes ds (Region.decode?_eq_some_iff.mp h)).2.1

/-- Every listed instruction occupies at least one byte. -/
theorem Region.decode?_size_pos {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) : ∀ d ∈ ds, 0 < d.size := by
  intro d hd
  rw [Region.decode?_size h d hd]
  exact (Ext.encode_length d.instr).1

/-- The listing starts at the region's base. -/
theorem Region.decode?_head {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) : ∀ d ∈ ds.head?, d.addr = r.base :=
  (decodeFrom_spec fuel r.base r.bytes ds (Region.decode?_eq_some_iff.mp h)).2.2.2

/-- Each address is the previous address plus the previous size. -/
theorem Region.decode?_chain {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) :
    List.IsChain (fun d e => e.addr = d.addr + d.size) ds :=
  (decodeFrom_spec fuel r.base r.bytes ds (Region.decode?_eq_some_iff.mp h)).2.2.1

/-- The listed addresses strictly increase, so no two instructions share an
address. -/
theorem Region.decode?_addr_pairwise {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) : (starts ds).Pairwise (· < ·) :=
  decodeFrom_pairwise fuel r.base r.bytes ds (Region.decode?_eq_some_iff.mp h)

/-- Every listed instruction lies inside the region. -/
theorem Region.decode?_within {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) :
    ∀ d ∈ ds, r.base ≤ d.addr ∧ d.addr + d.size ≤ r.base + r.bytes.length := fun d hd =>
  let w := decodeFrom_mem fuel r.base r.bytes ds (Region.decode?_eq_some_iff.mp h) d hd
  ⟨w.1, w.2.1⟩

/-- The bytes at a listed address are the canonical encoding of the listed
instruction. -/
theorem Region.decode?_bytes {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) :
    ∀ d ∈ ds, (r.bytes.drop (d.addr - r.base)).take d.size = Ext.encode d.instr := fun d hd =>
  (decodeFrom_mem fuel r.base r.bytes ds (Region.decode?_eq_some_iff.mp h) d hd).2.2

/-- The region's bytes are exactly the concatenation of the canonical
encodings of the listed instructions. -/
theorem Region.decode?_covers {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) :
    (ds.map fun d => Ext.encode d.instr).flatten = r.bytes :=
  (decodeFrom_spec fuel r.base r.bytes ds (Region.decode?_eq_some_iff.mp h)).1.symm

/-- A region that decodes is covered in the sense of `Ext.Covered`. -/
theorem Region.decode?_covered {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) : Ext.Covered r.bytes :=
  ⟨ds.map Decoded.instr, by rw [← Region.decode?_covers h, List.map_map]; rfl⟩

/-- The listed sizes sum to the length of the region. -/
theorem Region.decode?_sum_size {r : Region} {fuel : Nat} {ds : List Decoded}
    (h : r.decode? fuel = some ds) : (ds.map Decoded.size).sum = r.bytes.length := by
  have hmap : ds.map Decoded.size = ds.map fun d => (Ext.encode d.instr).length :=
    List.map_congr_left (Region.decode?_size h)
  rw [hmap, ← Region.decode?_covers h, List.length_flatten, List.map_map]
  rfl

/-- In a memory holding the region, the machine fetches each listed
instruction at its listed address. Nothing is assumed about memory past
`base + bytes.length`: `Ext.fetch_eq_decoded_iff` needs only that the
instruction's own bytes fetch, so the last instruction of the region is as
well served as the first. -/
theorem Region.decode?_fetch {r : Region} {fuel : Nat} {ds : List Decoded} {memory : Memory}
    (h : r.decode? fuel = some ds) (hload : r.LoadedIn memory) {d : Decoded} (hd : d ∈ ds) :
    Ext.fetch memory d.addr = .decoded d.instr d.size := by
  obtain ⟨hlo, hhi⟩ := Region.decode?_within h d hd
  have hbytes := Region.decode?_bytes h d hd
  have hsz := Region.decode?_size h d hd
  rw [Ext.fetch_eq_decoded_iff]
  refine ⟨Ext.encode d.instr, ?_, ?_⟩
  · have hf := hload (d.addr - r.base) d.size (by omega)
    rw [hbytes, show r.base + (d.addr - r.base) = d.addr by omega] at hf
    exact hf
  · rw [hsz]
    exact Ext.decode_encode d.instr

/-! ## Lookup -/

/-- A listing has an instruction at every address `at?` finds, and `at?` finds
the instruction's own address. -/
theorem at?_eq_some {ds : List Decoded} {addr : Nat} {d : Decoded} (h : at? ds addr = some d) :
    d ∈ ds ∧ d.addr = addr := by
  unfold at? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- When addresses are distinct, `at?` finds every listed instruction. -/
theorem at?_eq_some_of_mem {ds : List Decoded} (hp : (starts ds).Pairwise (· < ·))
    {d : Decoded} (hd : d ∈ ds) : at? ds d.addr = some d := by
  induction ds with
  | nil => cases hd
  | cons e rest ih =>
    simp only [starts, List.map_cons, List.pairwise_cons] at hp
    rcases List.mem_cons.mp hd with rfl | hmem
    · simp [at?]
    · have hlt : e.addr < d.addr := hp.1 d.addr (List.mem_map_of_mem hmem)
      have hne : (e.addr == d.addr) = false := by simp; omega
      rw [at?, List.find?_cons, hne]
      exact ih (by simpa [starts] using hp.2) hmem

/-- An instruction start is an address `at?` finds. -/
theorem at?_isSome_of_isStart {ds : List Decoded} {addr : Nat} (h : IsStart ds addr) :
    (at? ds addr).isSome = true := by
  induction ds with
  | nil => simp [IsStart, starts] at h
  | cons e rest ih =>
    rw [at?, List.find?_cons]
    cases he : (e.addr == addr) with
    | true => rfl
    | false =>
      refine ih ?_
      simp only [IsStart, starts, List.map_cons, List.mem_cons] at h ⊢
      rcases h with heq | h
      · simp [heq] at he
      · exact h

end Silmaril.X86.Decompile
