module

public import Silmaril.Raw.Elf.Link.Dyn.Crt.ConstMain
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Progress
public import Silmaril.Elf.Link.Dyn.Image.Thms

/-! # Non-vacuity of the small-executable theorems: a concrete loaded process

A generic construction, used for each of the six executables: the executable at `b0`,
`libc.so.6` at `lb0`, `ld.so` at `ldb0`, glibc files that hold the pinned chunks and zeros
elsewhere (`blobOf`), and a memory (`memOf`) holding exactly the loader relation's image
(each `PT_LOAD` with its permissions, `PT_GNU_RELRO` read-only, every byte as
`expectedByte` says), a stack page pair around `sp0` with `argc = 1` at `sp0`, and a
thread-control block at `fs0` (zeros, so the stack guard is `0`).

* `imageOk_of_table`: the image part of `ExeLoaded`, from one boolean table check
  (`tableOk`, per binary by `decide +kernel`);
* `atEntry0`: `AtEntry` for the start state `sOf` in any world whose kept addresses avoid
  the stack;
* `tlsAt0`: the thread pointer and a readable guard word.

The per-binary instances are in `NonVacuous/Ret.lean` and `NonVacuous/Adder.lean`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small.NonVacuous

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.DynElf.Elf
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt

/-- A file holding the chunks, zeros elsewhere. -/
def blobOf (cs : List Chunk) : Blob :=
  ⟨cs.foldr (fun c n => n ||| ((c.n % 2 ^ (8 * c.len)) <<< (8 * c.off))) 0,
    (cs.map fun c => c.off + c.len).foldr max 0⟩

/-! ## The placement -/

def b0 : Word := 0x555555554000#64
def lb0 : Word := 0x7ffff7c00000#64
def ldb0 : Word := 0x7ffff7fc5000#64
def gate0 : Word := 0x7ffff7c29d90#64
def sp0 : Word := 0x7ffffffde000#64
def fs0 : Word := 0x7ffff7d86740#64
def ifn0 : Word → Option Word := fun _ => none
def res0 : Word := 0#64

theorem b0_toNat : b0.toNat = 0x555555554000 := rfl
theorem sp0_toNat : sp0.toNat = 0x7ffffffde000 := rfl
theorem fs0_toNat : fs0.toNat = 0x7ffff7d86740 := rfl

/-- The slot table a slot list gives at these bases. -/
def tableOf (D : List (Nat × Val)) : List (Nat × Option Word) :=
  (D.mapM fun (e : Nat × Val) => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)).getD []

/-- Under lazy binding: the resolver (`GOT[2]`) at `resL0`, inside `ld.so`. -/
def resL0 : Word := 0x7ffff7fdc180#64

def tableOfL (D : List (Nat × Val)) : List (Nat × Option Word) :=
  (D.mapM fun (e : Nat × Val) => (e.2.word [b0, lb0, ldb0] ifn0 resL0).map fun w => (e.1, w)).getD []

/-! ## The image -/

/-- The `PT_LOAD` headers. -/
def loadsOf (i : DynInfo) : List Phdr := i.phs.filter (·.kind == 1)

/-- The segment holding `v`. -/
def segOf (i : DynInfo) (v : Nat) : Option Phdr :=
  (loadsOf i).find? fun ph => ph.vaddr ≤ v && v < ph.vaddr + ph.memsz

/-- The byte the loader relation asks for at `v` (`0` where it leaves it open). -/
def byteAt (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) (v : Nat) : Byte :=
  match segOf i v with
  | some ph => match expectedByte f T ph v with
    | some (some x) => x
    | _ => 0
  | none => 0

/-- The image bytes, offsets `0 … n - 1`. -/
@[irreducible] def imgOf (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) (n : Nat) :
    List Byte :=
  (List.range n).map (byteAt f i T)

theorem imgOf_length (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) (n : Nat) :
    (imgOf f i T n).length = n := by
  unfold imgOf; simp

theorem imgOf_get? (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) {n v : Nat}
    (hv : v < n) : (imgOf f i T n)[v]? = some (byteAt f i T v) := by
  unfold imgOf; simp [hv]

/-- The `PT_GNU_RELRO` page range `[lo, hi)` (empty if none). -/
def relroOf (i : DynInfo) : Nat × Nat :=
  match i.phs.find? (·.kind == 0x6474e552) with
  | some ph => (ph.vaddr / 4096 * 4096, (ph.vaddr + ph.memsz) / 4096 * 4096)
  | none => (0, 0)

/-- The regions of one segment at base `b`: its pages before, inside and after the
`PT_GNU_RELRO` range, the middle one without write permission. -/
def segRegions (i : DynInfo) (b : Nat) (ph : Phdr) : List Region :=
  let v := ph.vaddr
  let e := ph.vaddr + ph.memsz
  let lo := min e (max v (relroOf i).1)
  let hi := max lo (min e (relroOf i).2)
  let r := ph.flags / 4 % 2 == 1
  let w := ph.flags / 2 % 2 == 1
  let x := ph.flags % 2 == 1
  ([(v, lo - v, w), (lo, hi - lo, false), (hi, e - hi, w)].filter (·.2.1 != 0)).map
    fun (a, n, w') => ⟨b + a, n, ⟨r, w', x⟩⟩

/-- All the image's regions at base `b`. -/
def imgRegions (i : DynInfo) (b : Nat) : List Region := (loadsOf i).flatMap (segRegions i b)

/-! ## The stack and the thread-control block -/

/-- `argv[0] = sp0 + 16`, little-endian (`0x7ffffffde010`). -/
def argv0Bytes : List Byte := [0x10#8, 0xe0#8, 0xfd#8, 0xff#8, 0xff#8, 0x7f#8, 0#8, 0#8]

/-- The stack's byte at `sp0 - 4096 + k`: `argc = 1` at `sp0`, `argv[0] = sp0 + 16` at `sp0 + 8`,
zeros elsewhere (so `argv[1]` is `NULL` and `argv[0]` is the empty string, both at `sp0 + 16`). -/
def stackByte (k : Nat) : Byte :=
  if k = 4096 then 1#8 else if 4104 ≤ k ∧ k < 4112 then argv0Bytes.getD (k - 4104) 0#8 else 0#8

/-- The stack (`sp0 - 4096 … sp0 + 4095`): `argc = 1`, `argv = [""]`, zeros elsewhere. -/
@[irreducible] def stack0 : List Byte :=
  (List.range 8192).map stackByte

/-- The thread-control block at `fs0`: zeros (the stack guard at `fs0 + 0x28` is `0`). -/
@[irreducible] def tcb0 : List Byte := List.replicate 0x100 0#8

def permRW : Permissions := ⟨true, true, false⟩

def stackRegion : Region := ⟨sp0.toNat - 4096, 8192, permRW⟩
def tcbRegion : Region := ⟨fs0.toNat, 0x100, permRW⟩

/-- **The memory**: the image of `f` (`n` bytes from `b0`), the stack and the TCB. -/
@[irreducible] def memOf (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) (n : Nat) :
    Memory :=
  ⟨imgRegions i b0.toNat ++ [stackRegion, tcbRegion],
    Memory.install (Memory.install (Memory.install ∅ (sp0.toNat - 4096) stack0) fs0.toNat tcb0)
      b0.toNat (imgOf f i T n)⟩

theorem memOf_regions (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) (n : Nat) :
    (memOf f i T n).regions = imgRegions i b0.toNat ++ [stackRegion, tcbRegion] := by
  unfold memOf; rfl

/-- The per-byte table: every byte of every segment lies in that segment alone, below `n`,
has a value in the model, and has the segment's permissions in the memory. -/
def tableOk (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) (n : Nat) : Bool :=
  (loadsOf i).all fun ph => decide (ph.vaddr + ph.memsz ≤ n) && (List.range ph.memsz).all fun k =>
    let v := ph.vaddr + k
    let m := memOf f i T n
    segOf i v == some ph && (expectedByte f T ph v).isSome &&
    m.permits .read (b0.toNat + v) == (ph.flags / 4 % 2 == 1) &&
    m.permits .execute (b0.toNat + v) == (ph.flags % 2 == 1) &&
    m.permits .write (b0.toNat + v) == (ph.flags / 2 % 2 == 1 && !inRelro i v)

theorem img_get {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n v : Nat} (hv : v < n) :
    (memOf f i T n).bytes.get? (b0.toNat + v) = some (byteAt f i T v) := by
  unfold memOf
  dsimp only
  rw [Memory.install_get _ _ _ _ (by rw [imgOf_length]; exact hv), ← List.getElem?_eq_getElem]
  exact imgOf_get? _ _ _ hv

/-- **The image part of the loader relation**, from the table check. -/
theorem imageOk_of_table {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) (htab : tableOk f i T n = true) :
    ImageOk ⟨f, b0⟩ i T (memOf f i T n) := by
  intro ph hph hk v h1 h2
  have hl : ph ∈ loadsOf i := List.mem_filter.mpr ⟨hph, by simp [hk]⟩
  have ht0 := List.all_eq_true.mp htab ph hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht0
  obtain ⟨hlt, ht1⟩ := ht0
  have ht := List.all_eq_true.mp ht1 (v - ph.vaddr) (List.mem_range.mpr (by omega))
  simp only [Nat.add_sub_cancel' h1, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨hseg, hsome⟩, hr⟩, hx⟩, hw⟩ := ht
  have haddr : (b0 + BitVec.ofNat 64 v).toNat = b0.toNat + v := addr_toNat (by rw [b0_toNat]; omega)
  dsimp only
  rw [haddr]
  refine ⟨by rw [b0_toNat]; omega, hr, hx, hw, ?_⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨e, he, by rw [img_get (by omega)]; rfl, fun x hx' => ?_⟩
  rw [img_get (by omega)]
  subst hx'
  simp [byteAt, hseg, he]

/-! ## The start state -/

/-- The start state: `rip` at `start`, `rsp = sp0`, `fsBase = fs0`, other registers `0`, the
library state fresh with `stdin` = `inp`. -/
def sOf (mem : Memory) (start : Nat) (inp : List Byte) : PState :=
  ⟨⟨⟨fun r => if r = .rsp then sp0 else 0, b0 + BitVec.ofNat 64 start,
      ⟨none, none, none, none, none, none⟩, fs0⟩, mem⟩,
    { jobs := [], out := [], atexit := [], done := none, inp := inp }⟩

theorem stack_len : stack0.length = 8192 := by
  unfold stack0; rw [List.length_map, List.length_range]

theorem tcb_len : tcb0.length = 0x100 := by
  unfold tcb0; exact List.length_replicate

theorem stack0_get? (k : Nat) :
    stack0[k]? = if k < 8192 then some (stackByte k) else none := by
  unfold stack0
  by_cases h : k < 8192
  · simp [h]
  · simp [h]

theorem stack_get {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) {k : Nat} (hk : k < 8192) :
    (memOf f i T n).bytes.get? (sp0.toNat - 4096 + k) = stack0[k]? := by
  unfold memOf
  dsimp only
  rw [Memory.install_outside _ _ _ _ (Or.inr (by rw [imgOf_length, b0_toNat, sp0_toNat]; omega)),
    Memory.install_outside _ _ _ _ (Or.inr (by rw [tcb_len, fs0_toNat, sp0_toNat]; omega)),
    Memory.install_get _ _ _ _ (by rw [stack_len]; exact hk), List.getElem?_eq_getElem]

theorem tcb_get {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) {k : Nat} (hk : k < 0x100) :
    (memOf f i T n).bytes.get? (fs0.toNat + k) = some 0#8 := by
  unfold memOf
  dsimp only
  rw [Memory.install_outside _ _ _ _ (Or.inr (by rw [imgOf_length, b0_toNat, fs0_toNat]; omega)),
    Memory.install_get _ _ _ _ (by rw [tcb_len]; exact hk)]
  unfold tcb0; rw [List.getElem_replicate]

theorem rw_permits {mem : Memory} {r : Region} (hr : r ∈ mem.regions) (hrw : r.permissions = permRW)
    {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat} (h1 : r.base ≤ a)
    (h2 : a < r.base + r.size) : mem.permits acc a = true := by
  unfold Memory.permits
  rw [List.any_eq_true]
  refine ⟨r, hr, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨h1, h2⟩, ?_⟩
  rw [hrw]
  rcases hacc with rfl | rfl <;> rfl

theorem stack_permits {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : sp0.toNat - 4096 ≤ a) (h2 : a < sp0.toNat + 4096) : (memOf f i T n).permits acc a = true :=
  rw_permits (r := stackRegion) (by rw [memOf_regions]; simp) rfl hacc h1
    (by show a < sp0.toNat - 4096 + 8192; rw [sp0_toNat] at h2 ⊢; omega)

theorem tcb_permits {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : fs0.toNat ≤ a) (h2 : a < fs0.toNat + 0x100) : (memOf f i T n).permits acc a = true :=
  rw_permits (r := tcbRegion) (by rw [memOf_regions]; simp) rfl hacc h1 h2

/-- **`AtEntry` for the start state**, in every world whose kept addresses avoid the
stack page pair. -/
theorem atEntry0 {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) (L : Layout) (W : World) (inp : List Byte)
    (hK : ∀ a, W.Kept a → a < sp0.toNat - 4096 ∨ sp0.toNat + 4096 ≤ a) :
    AtEntry L W b0 (sOf (memOf f i T n) L.start inp) := by
  have hsp : (sOf (memOf f i T n) L.start inp).m.core.read .rsp = sp0 := rfl
  refine ⟨rfl, rfl, rfl, by rw [hsp, sp0_toNat], ?_, ?_⟩
  · refine ⟨by rw [hsp, sp0_toNat]; decide, by rw [hsp, sp0_toNat]; decide, fun a h1 h2 => ?_⟩
    rw [hsp] at h1 h2
    have h3 : a < sp0.toNat + 4096 := by rw [sp0_toNat] at h2 ⊢; omega
    refine ⟨stack_permits (Or.inl rfl) h1 h3, stack_permits (Or.inr rfl) h1 h3, fun hk => ?_⟩
    rcases hK a hk with h | h <;> omega
  · refine ⟨1#64, ?_⟩
    rw [hsp]
    show (memOf f i T n).readBytes sp0.toNat 8 = _
    have := readWith_of_points (mem := memOf f i T n) (acc := .read)
      (l := Silmaril.Machine.LittleEndian.encodeWords [1#64]) (a := sp0.toNat)
      (by simp [sp0_toNat]) (by simp [sp0_toNat]) (fun k hk => by
        simp only [Silmaril.X86.length_encodeWords_singleton] at hk
        refine ⟨stack_permits (Or.inl rfl) (by rw [sp0_toNat]; omega) (by rw [sp0_toNat]; omega), ?_⟩
        have := stack_get (f := f) (i := i) (T := T) hn (k := 4096 + k) (by omega)
        rw [show sp0.toNat - 4096 + (4096 + k) = sp0.toNat + k by rw [sp0_toNat]; omega] at this
        rw [this, stack0_get?]
        simp only [stackByte]
        have h1 : Silmaril.Machine.LittleEndian.encodeWords [1#64] =
            [1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := by decide
        simp only [h1]
        interval_cases k <;> rfl)
    simpa [Memory.readBytes] using this

/-- The stack guard word at `fs0 + 0x28` reads `0`. -/
theorem guard0 {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) : loadN (memOf f i T n) (fs0 + 40#64) 8 = some 0#64 := by
  have h40 : (fs0 + 40#64).toNat = fs0.toNat + 40 := rfl
  have := readWith_of_points (mem := memOf f i T n) (acc := .read)
    (l := List.replicate 8 0#8) (a := fs0.toNat + 40)
    (by simp [fs0_toNat]) (by simp [fs0_toNat]) (fun k hk => by
      simp only [List.length_replicate] at hk
      refine ⟨tcb_permits (Or.inl rfl) (by omega) (by omega), ?_⟩
      rw [show fs0.toNat + 40 + k = fs0.toNat + (40 + k) by omega, tcb_get hn (by omega)]
      interval_cases k <;> rfl)
  simp only [List.length_replicate] at this
  simp [loadN, h40, Memory.readBytes, this]
  decide

/-! ## A memory with a given stack

`memOfS stk` is `memOf` with the 8192 stack bytes `stk` (from `sp0 - 4096`) instead of
`stack0`: the same regions, image and TCB, so the table check `tableOk` (which reads only
permissions) serves both. Used for programs called with more than one argument. -/

/-- **The memory with the stack `stk`**: the image of `f`, the stack `stk`, the TCB. -/
@[irreducible] def memOfS (stk : List Byte) (f : Blob) (i : DynInfo) (T : List (Nat × Option Word))
    (n : Nat) : Memory :=
  ⟨imgRegions i b0.toNat ++ [stackRegion, tcbRegion],
    Memory.install (Memory.install (Memory.install ∅ (sp0.toNat - 4096) stk) fs0.toNat tcb0)
      b0.toNat (imgOf f i T n)⟩

theorem memOfS_regions (stk : List Byte) (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) (n : Nat) :
    (memOfS stk f i T n).regions = imgRegions i b0.toNat ++ [stackRegion, tcbRegion] := by
  unfold memOfS; rfl

theorem memOfS_permits (stk : List Byte) (f : Blob) (i : DynInfo) (T : List (Nat × Option Word)) (n : Nat)
    (acc : Access) (a : Nat) : (memOfS stk f i T n).permits acc a = (memOf f i T n).permits acc a := by
  unfold Memory.permits; rw [memOfS_regions, memOf_regions]

theorem imgS_get {stk : List Byte} {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n v : Nat}
    (hv : v < n) : (memOfS stk f i T n).bytes.get? (b0.toNat + v) = some (byteAt f i T v) := by
  unfold memOfS
  dsimp only
  rw [Memory.install_get _ _ _ _ (by rw [imgOf_length]; exact hv), ← List.getElem?_eq_getElem]
  exact imgOf_get? _ _ _ hv

/-- **The image part of the loader relation** for `memOfS`, from the table check. -/
theorem imageOk_of_tableS {stk : List Byte} {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) (htab : tableOk f i T n = true) :
    ImageOk ⟨f, b0⟩ i T (memOfS stk f i T n) := by
  intro ph hph hk v h1 h2
  have hl : ph ∈ loadsOf i := List.mem_filter.mpr ⟨hph, by simp [hk]⟩
  have ht0 := List.all_eq_true.mp htab ph hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht0
  obtain ⟨hlt, ht1⟩ := ht0
  have ht := List.all_eq_true.mp ht1 (v - ph.vaddr) (List.mem_range.mpr (by omega))
  simp only [Nat.add_sub_cancel' h1, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨hseg, hsome⟩, hr⟩, hx⟩, hw⟩ := ht
  have haddr : (b0 + BitVec.ofNat 64 v).toNat = b0.toNat + v := addr_toNat (by rw [b0_toNat]; omega)
  dsimp only
  rw [haddr, memOfS_permits, memOfS_permits, memOfS_permits]
  refine ⟨by rw [b0_toNat]; omega, hr, hx, hw, ?_⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨e, he, by rw [imgS_get (by omega)]; rfl, fun x hx' => ?_⟩
  rw [imgS_get (by omega)]
  subst hx'
  simp [byteAt, hseg, he]

theorem stackS_get {stk : List Byte} {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) (hs : stk.length = 8192) {k : Nat} (hk : k < 8192) :
    (memOfS stk f i T n).bytes.get? (sp0.toNat - 4096 + k) = stk[k]? := by
  unfold memOfS
  dsimp only
  rw [Memory.install_outside _ _ _ _ (Or.inr (by rw [imgOf_length, b0_toNat, sp0_toNat]; omega)),
    Memory.install_outside _ _ _ _ (Or.inr (by rw [tcb_len, fs0_toNat, sp0_toNat]; omega)),
    Memory.install_get _ _ _ _ (by rw [hs]; exact hk), List.getElem?_eq_getElem]

theorem tcbS_get {stk : List Byte} {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) {k : Nat} (hk : k < 0x100) :
    (memOfS stk f i T n).bytes.get? (fs0.toNat + k) = some 0#8 := by
  unfold memOfS
  dsimp only
  rw [Memory.install_outside _ _ _ _ (Or.inr (by rw [imgOf_length, b0_toNat, fs0_toNat]; omega)),
    Memory.install_get _ _ _ _ (by rw [tcb_len]; exact hk)]
  unfold tcb0; rw [List.getElem_replicate]

theorem stackS_permits {stk : List Byte} {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : sp0.toNat - 4096 ≤ a) (h2 : a < sp0.toNat + 4096) : (memOfS stk f i T n).permits acc a = true := by
  rw [memOfS_permits]; exact stack_permits hacc h1 h2

/-- The stack guard word at `fs0 + 0x28` reads `0` in `memOfS`. -/
theorem guardS {stk : List Byte} {f : Blob} {i : DynInfo} {T : List (Nat × Option Word)} {n : Nat}
    (hn : n < 2 ^ 32) : loadN (memOfS stk f i T n) (fs0 + 40#64) 8 = some 0#64 := by
  have h40 : (fs0 + 40#64).toNat = fs0.toNat + 40 := rfl
  have := readWith_of_points (mem := memOfS stk f i T n) (acc := .read)
    (l := List.replicate 8 0#8) (a := fs0.toNat + 40)
    (by simp [fs0_toNat]) (by simp [fs0_toNat]) (fun k hk => by
      simp only [List.length_replicate] at hk
      refine ⟨by rw [memOfS_permits]; exact tcb_permits (Or.inl rfl) (by omega) (by omega), ?_⟩
      rw [show fs0.toNat + 40 + k = fs0.toNat + (40 + k) by omega, tcbS_get hn (by omega)]
      interval_cases k <;> rfl)
  simp only [List.length_replicate] at this
  simp [loadN, h40, Memory.readBytes, this]
  decide

/-! ## Worlds of the C runtime -/

/-- What a C-runtime world keeps: its image and its `tls`. -/
theorem crt_kept {L : Layout} {gate : Word} {lazy : Option (Word × List (Nat × Word))}
    {fns : List (Word × Fn)} {rel : Bool} {named : Name → PState → Silmaril.X86.RelIsa.Res PState → Prop}
    {tls : Nat → Prop} {a : Nat} (h : (crtWorld L b0 gate lazy fns rel named tls).Kept a) :
    (b0.toNat ≤ a ∧ a < b0.toNat + L.size) ∨ tls a := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact absurd h id
  · exact Or.inr h

/-- Kept addresses of a C-runtime world with a small image and `tls` away from the stack
avoid the stack. -/
theorem crt_kept_stack {L : Layout} {gate : Word} {lazy : Option (Word × List (Nat × Word))}
    {fns : List (Word × Fn)} {rel : Bool} {named : Name → PState → Silmaril.X86.RelIsa.Res PState → Prop}
    {tls : Nat → Prop} (hL : L.size < 2 ^ 32)
    (ht : ∀ a, tls a → a < sp0.toNat - 4096 ∨ sp0.toNat + 4096 ≤ a) :
    ∀ a, (crtWorld L b0 gate lazy fns rel named tls).Kept a →
      a < sp0.toNat - 4096 ∨ sp0.toNat + 4096 ≤ a := by
  intro a h
  rcases crt_kept h with h | h
  · left; rw [b0_toNat] at h; rw [sp0_toNat]; omega
  · exact ht a h

/-- **The process machine of an eagerly bound C-runtime world always has an outcome**, when
its named functions do. -/
theorem crt_progress {L : Layout} {gate : Word} {fns : List (Word × Fn)} {rel : Bool}
    {named : Name → PState → Silmaril.X86.RelIsa.Res PState → Prop} {tls : Nat → Prop}
    (hL : L.size < 2 ^ 32) (ht : ∀ a, tls a → a < 2 ^ 62) (hN : ∀ n s, ∃ r, named n s r) :
    Silmaril.X86.RelIsa.Progress (proc (crtWorld L b0 gate none fns rel named tls)) :=
  proc_progress _ (by show b0.toNat + L.size ≤ 2 ^ 62; rw [b0_toNat]; omega)
    (fun a h => by rcases h with h | h; exact absurd h id; exact ht a h)
    (fun _ _ h => by cases h) hN

end Silmaril.Elf.Link.Dyn.Small.NonVacuous
