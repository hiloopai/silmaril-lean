module

public import Silmaril.Apps.Sha256sum.Binary.Digest.FinalCode
public import Silmaril.Apps.Sha256sum.Binary.Digest.Facts
public import Silmaril.X86.SegVC.Mono
public import Silmaril.X86.SegVC.Ext8
public import Silmaril.Process.CLI.Sha256Cli.LongTailPaddingReference

/-! # `sha_final` in `digest_file`

The segment from `0x403034` (the last `read` returned 0; the `struct sha` holds the chaining
value `H` of the full blocks and the buffered `tail`, the total `T` in `rdx`) to `0x40310a`
(the digest copied out big-endian to the caller's buffer `out`), over the `Ext8` instance
`X86Sys.Isa.sys8` (the output loop's `movzbl %ah,%ebx` is a new form).

Cut points: `71` (the zero fill's setup, shared by both paddings), `94` (the zero fill, two
bytes a round), `120` (the length store, one byte a round), `166` (the output loop, one state
word a round), `368` (the long padding's zero fill to the end of the first block). Two
contracted calls of `sha256_compress` (`compressCall8` at `0x4030c6` and `0x4031be`).

The ghost target is the specification's padding: the blocks `TailPaddingReference.blocks tail
T` (one block for `tail.length < 56`, else two), and every cut point says what remains to be
compressed to reach `Hfin = (blocks tail T).foldl compressBlock H`.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest.Final

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Crypto.X86.Sha256O2 (StateHolds compressBlock stateOf)
open Silmaril.Crypto.SHA256.Kernel (InitHash)
open Silmaril.Process.CLI.Sha256Cli

/-! ## `sha256_compress` on the `Ext8` machine -/

/-- The linked `sha256_compress` as a contracted call of the `Ext8` instance: the contract of
`compressCall` (its run is made of `X86.Ext` steps, which are retiring steps of the variant). -/
def compressCall8 : Call Isa.sys8 where
  pre := (compressCall (fun _ => 0)).pre
  post := (compressCall (fun _ => 0)).post
  runs := fun s hlv hpre => by
    obtain ⟨t, hr, hp⟩ := (compressCall (fun _ => 0)).runs s hlv hpre
    exact ⟨t, reaches_rStep8 hr, hp⟩

/-! ## The ghost context -/

/-- The ghost context of one `sha_final`. -/
structure Ctx where
  /-- `digest_file`'s stack pointer. -/
  sp : Word
  /-- The caller's 32-byte digest buffer (`digest_file`'s second argument, at `[sp + 0x10]`). -/
  out : Word
  /-- The chaining value of the full blocks absorbed. -/
  H : InitHash
  /-- The buffered bytes. -/
  tail : List Byte
  /-- The stored total (bytes, modulo `2 ^ 64`). -/
  T : Word
  /-- The registers at the entry. -/
  r0 : Silmaril.X86.Reg → Word
  /-- The memory at the entry. -/
  m0 : Memory

/-- The padding blocks of the specification (one or two). -/
def Ctx.blocks (c : Ctx) : List (List Byte) := TailPaddingReference.blocks c.tail c.T

/-- The chaining value after the padding. -/
def Ctx.Hfin (c : Ctx) : InitHash := c.blocks.foldl compressBlock c.H

/-- What `sha_final` may write: the callee frames below `sp`, the spill slot at `sp + 0x18`,
`state[]`, `blk[]`, `blen`, and the digest buffer. -/
def finSpan (c : Ctx) (a : Nat) : Prop :=
  (c.sp.toNat - 400 ≤ a ∧ a < c.sp.toNat) ∨ (c.sp.toNat + 0x18 ≤ a ∧ a < c.sp.toNat + 0x88) ∨
    (c.out.toNat ≤ a ∧ a < c.out.toNat + 32)

/-- The static facts of the entry memory and the geometry. -/
structure Geo (c : Ctx) : Prop where
  spAlign : c.sp.toNat % 16 = 0
  spLow : 0x420000 ≤ c.sp.toNat
  spHigh : c.sp.toNat + 0x1000 < 2 ^ 64
  stackW : c.m0.Permitted .write (c.sp.toNat - 400) 552
  stackR : c.m0.Permitted .read (c.sp.toNat - 400) 552
  ccode : c.m0.fetchBytes Binary.textBase.toNat Silmaril.Crypto.X86.Sha256O2.size =
    some (Silmaril.Crypto.X86.Sha256O2.image Binary.textBase Binary.rodataBase)
  kTable : c.m0.readBytes Binary.rodataBase.toNat Silmaril.Crypto.X86.Sha256O2.kSize =
    some Silmaril.Crypto.X86.Sha256O2.kBytes
  loaded : Loaded c.m0 base code
  outSlot : loadN c.m0 (c.sp + 0x10#64) 8 = some c.out
  outW : c.m0.Permitted .write c.out.toNat 32
  outR : c.m0.Permitted .read c.out.toNat 32
  outLow : 0x420000 ≤ c.out.toNat
  outHigh : c.out.toNat + 32 < 2 ^ 64
  outApart : c.out.toNat + 32 ≤ c.sp.toNat - 400 ∨ c.sp.toNat + 152 ≤ c.out.toNat
  room : c.tail.length < 64

/-- What every point of the segment knows about the registers it keeps and the memory. -/
structure Frame (c : Ctx) (s : XState) : Prop where
  rsp : s.core.read .rsp = c.sp
  rbp : s.core.read .rbp = c.r0 .rbp
  r13 : s.core.read .r13 = c.r0 .r13
  writes : Memory.WritesWithin c.m0 s.memory (finSpan c)

/-! ## Byte-wise contents -/

/-- The first `J` bytes of `blk[]` are those of `B`. -/
def BlkHas (m : Memory) (sp : Word) (J : Nat) (B : List Byte) : Prop :=
  ∀ j < J, loadN m (sp + BitVec.ofNat 64 (64 + j)) 1 = some (BitVec.ofNat 64 (B.getD j 0).toNat)

/-- The source byte of output byte `k`: the output loop reverses each state word. -/
def srcIdx (k : Nat) : Nat := 4 * (k / 4) + (3 - k % 4)

/-- The digest bytes of the state bytes `sb`. -/
def outBytes (sb : List Byte) : List Byte := (List.range 32).map fun k => sb.getD (srcIdx k) 0

/-- The first `J` bytes of the digest buffer are the digest of the state bytes `sb`. -/
def OutHas (m : Memory) (out : Word) (J : Nat) (sb : List Byte) : Prop :=
  ∀ k < J, loadN m (out + BitVec.ofNat 64 k) 1 = some (BitVec.ofNat 64 (sb.getD (srcIdx k) 0).toNat)


/-! ## Helpers -/

theorem toNat_sp {sp : Word} (h : sp.toNat + 0x1000 < 2 ^ 64) {n : Nat} (hn : n ≤ 0x1000) :
    (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := Digest.toNat_sp_add h hn

/-- The four bytes of state word `i`. -/
def wordBytes (sb : List Byte) (i : Nat) : Nat :=
  (sb.getD (4 * i) 0).toNat + 256 * ((sb.getD (4 * i + 1) 0).toNat +
    256 * ((sb.getD (4 * i + 2) 0).toNat + 256 * (sb.getD (4 * i + 3) 0).toNat))

theorem wordBytes_lt (sb : List Byte) (i : Nat) : wordBytes sb i < 2 ^ 32 := by
  have := (sb.getD (4 * i) 0).isLt; have := (sb.getD (4 * i + 1) 0).isLt
  have := (sb.getD (4 * i + 2) 0).isLt; have := (sb.getD (4 * i + 3) 0).isLt
  simp only [wordBytes]; omega

/-- State word `i`, through the output loop's 32-bit load. -/
theorem word_load {m : Memory} {sp : Word} {sb : List Byte} {i : Nat}
    (spHigh : sp.toNat + 0x1000 < 2 ^ 64) (hsb : m.readBytes (sp + 0x20#64).toNat 32 = some sb)
    (hi : i < 8) :
    loadN m (sp + BitVec.ofNat 64 (32 + 4 * i)) 4 = some (BitVec.ofNat 64 (wordBytes sb i)) := by
  have hlen : sb.length = 32 := Memory.readWith_length hsb
  have hr := Memory.readBytes_sub_range hsb (offset := 4 * i) (len := 4) (by omega) (by omega)
  rw [toNat_sp spHigh (by decide)] at hr
  rw [loadN, toNat_sp spHigh (by omega), show sp.toNat + (32 + 4 * i) = sp.toNat + 32 + 4 * i by omega,
    hr]
  simp only [Option.map_some, Option.some.injEq]
  congr 1
  have e : (sb.drop (4 * i)).take 4 =
      [sb.getD (4 * i) 0, sb.getD (4 * i + 1) 0, sb.getD (4 * i + 2) 0, sb.getD (4 * i + 3) 0] := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, hlen, List.length_cons, List.length_nil]; omega
    · intro n h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      simp only [List.getElem_take, List.getElem_drop]
      rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] <;>
        rw [List.getD_eq_getElem _ _ (by omega)]
  rw [e]
  simp only [leValue, wordBytes]
  omega

/-! ## The segment's annotation -/

/-- `0x403034`: `read` returned 0; the struct holds `H` and `tail`, `rdx` the total. -/
def pre (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ s.memory = c.m0 ∧ s.core.read .rdx = c.T ∧
    StateHolds s.memory (c.sp + 0x20#64) c.H ∧
    s.memory.readBytes (c.sp + 0x40#64).toNat c.tail.length = some c.tail ∧
    loadN s.memory (c.sp + 0x80#64) 8 = some (BitVec.ofNat 64 c.tail.length)

/-- `0x40310a`: the digest of the chaining value `Hfin` is in `out`. -/
def post (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∃ sb, s.memory.readBytes (c.sp + 0x20#64).toNat 32 = some sb ∧
    stateOf sb = c.Hfin ∧ s.memory.readBytes c.out.toNat 32 = some (outBytes sb)

/-- The common registers of the padding cut points: `rbx` the bit length, `rdi` `state[]`. -/
def Regs (c : Ctx) (s : XState) : Prop :=
  s.core.read .rbx = c.T * 8#64 ∧ s.core.read .rdi = c.sp + 0x20#64 ∧
    s.core.read .rsi = c.sp + 0x40#64

/-- `0x40307b` (`lea 1(%rax,%rcx),%rdx`): `j` bytes of the last block are in place, `rcx`
`55 - j`; compressing the block completed with zeros and the length gives `Hfin`. -/
def inv71 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ Regs c s ∧ ∃ j H B, j ≤ 55 ∧ B.length = 56 ∧ B.drop j = List.replicate (56 - j) 0 ∧
    s.core.read .rax = c.sp + BitVec.ofNat 64 (64 + j) ∧
    s.core.read .rcx = BitVec.ofNat 64 (55 - j) ∧
    StateHolds s.memory (c.sp + 0x20#64) H ∧ BlkHas s.memory c.sp j B ∧
    compressBlock H (B ++ LengthStore.encoded c.T) = c.Hfin

/-- `0x403092`, the zero fill to `blk + 56`, two bytes a round. -/
def inv94 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ Regs c s ∧ ∃ j H B, j + 2 ≤ 56 ∧ (56 - j) % 2 = 0 ∧ B.length = 56 ∧
    B.drop j = List.replicate (56 - j) 0 ∧
    s.core.read .rax = c.sp + BitVec.ofNat 64 (64 + j) ∧
    s.core.read .rdx = c.sp + BitVec.ofNat 64 120 ∧
    StateHolds s.memory (c.sp + 0x20#64) H ∧ BlkHas s.memory c.sp j B ∧
    compressBlock H (B ++ LengthStore.encoded c.T) = c.Hfin

/-- `0x4030ac`, the length store, byte `i` of the big-endian bit length. -/
def inv120 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ Regs c s ∧ ∃ i H B, i < 8 ∧ B.length = 64 ∧
    B.drop 56 = LengthStore.encoded c.T ∧
    s.core.read .rax = c.sp + BitVec.ofNat 64 (120 + i) ∧
    s.core.read .rcx = BitVec.ofNat 64 (56 - 8 * i) ∧
    StateHolds s.memory (c.sp + 0x20#64) H ∧ BlkHas s.memory c.sp (56 + i) B ∧
    compressBlock H B = c.Hfin

/-- `0x4030da`, the output loop, state word `i`. -/
def inv166 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∃ i sb, i < 8 ∧ s.core.read .rdi = c.sp + BitVec.ofNat 64 (32 + 4 * i) ∧
    s.core.read .r12 = c.out + BitVec.ofNat 64 (4 * i) ∧
    s.core.read .rcx = c.sp + 0x40#64 ∧
    s.memory.readBytes (c.sp + 0x20#64).toNat 32 = some sb ∧ stateOf sb = c.Hfin ∧
    OutHas s.memory c.out (4 * i) sb

/-- `0x4031a4`, the long padding's zero fill to `blk + 64`, two bytes a round. -/
def inv368 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ (s.core.read .rbx = c.T * 8#64 ∧ s.core.read .rsi = c.sp + 0x40#64) ∧
    56 ≤ c.tail.length ∧ ∃ j, c.tail.length + 1 ≤ j ∧ j + 2 ≤ 64 ∧
    (64 - j) % 2 = 0 ∧
    s.core.read .rax = c.sp + BitVec.ofNat 64 (64 + j) ∧
    s.core.read .rdx = c.sp + BitVec.ofNat 64 128 ∧
    StateHolds s.memory (c.sp + 0x20#64) c.H ∧ BlkHas s.memory c.sp j (PaddingExtra.block c.tail)

/-- `0x4031b4`, the long padding's first block complete: `tail`, `0x80`, zeros. -/
def inv384 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ s.core.read .rbx = c.T * 8#64 ∧ s.core.read .rsi = c.sp + 0x40#64 ∧
    56 ≤ c.tail.length ∧ StateHolds s.memory (c.sp + 0x20#64) c.H ∧
    BlkHas s.memory c.sp 64 (PaddingExtra.block c.tail)

def raxOff (c : Ctx) (s : XState) : Nat := ((s.core.read .rax) - c.sp).toNat
def rdiOff (c : Ctx) (s : XState) : Nat := ((s.core.read .rdi) - c.sp).toNat

/-- The cut points and their measures: a single ranking, decreasing along the long padding,
the zero fill, the length store and the output loop. -/
def cuts (c : Ctx) : List (Nat × Cut (σ := XState)) :=
  [(71, { inv := inv71 c, measure := fun s => 2000 + 2 * (200 - raxOff c s) + 1 }),
   (94, { inv := inv94 c, measure := fun s => 2000 + 2 * (200 - raxOff c s) }),
   (120, { inv := inv120 c, measure := fun s => 1000 + (200 - raxOff c s) }),
   (166, { inv := inv166 c, measure := fun s => 200 - rdiOff c s }),
   (368, { inv := inv368 c, measure := fun s => 5000 + (200 - raxOff c s) }),
   (384, { inv := inv384 c, measure := fun _ => 4000 })]

def stops (c : Ctx) : List (Nat × (XState → Prop)) :=
  [(214, post c), (570, fun _ => False)]

def calls : List (Nat × Nat × Call Isa.sys8) :=
  [(146, 151, compressCall8), (394, 399, compressCall8)]

def subs : List (Nat × Nat × Call Isa.sys8) := []

/-! ## Memory steps -/

theorem base_toNat : base.toNat = 0x403034 := rfl

theorem Geo.codeApart {c : Ctx} (hg : Geo c) {a : Nat} (ha : finSpan c a) : 0x41f000 ≤ a := by
  have := hg.spLow; have := hg.outLow
  simp only [finSpan] at ha; omega

theorem loaded_of_writes {c : Ctx} (hg : Geo c) {m : Memory}
    (hw : Memory.WritesWithin c.m0 m (finSpan c)) : Loaded m base code := by
  unfold Loaded; rw [hw.fetchBytes]; · exact hg.loaded
  intro o ho hin; have := hg.codeApart hin; rw [code_length] at ho; rw [base_toNat] at this; omega

theorem writes_store {c : Ctx} {m m' : Memory} {a : Word} {k : Nat} {v : Word}
    (hw : Memory.WritesWithin c.m0 m (finSpan c)) (hs : storeN m a k v = some m')
    (hin : ∀ o < k, finSpan c (a.toNat + o)) : Memory.WritesWithin c.m0 m' (finSpan c) :=
  hw.trans ((Stored.of_storeN hs).writesWithin (fun o ho => hin o (by simpa using ho)))

theorem store_within {m m' : Memory} {a : Word} {k : Nat} {v : Word}
    (hs : storeN m a k v = some m') :
    Memory.WritesWithin m m' (fun x => a.toNat ≤ x ∧ x < a.toNat + k) :=
  (Stored.of_storeN hs).writesWithin (fun o ho => by simp only [length_leBytes] at ho; omega)

theorem perm_of {c : Ctx} {m : Memory} {P : Nat → Prop} (hw : Memory.WritesWithin c.m0 m P)
    {acc : Silmaril.Process.Access} {a n : Nat} (h : c.m0.Permitted acc a n) : m.Permitted acc a n :=
  (hw.permitted_iff _ _ _).mpr h

/-- A one-byte load after a one-byte store. -/
theorem load1_store1 {m m' : Memory} {a : Word} {v : Word} (hs : storeN m a 1 v = some m')
    (hr : m.Permitted .read a.toNat 1) (b : Word) :
    loadN m' b 1 = if b.toNat = a.toNat then some (BitVec.ofNat 64 (v.toNat % 256))
      else loadN m b 1 := by
  split
  · rename_i h
    have : b = a := BitVec.eq_of_toNat_eq h
    subst this
    rw [loadN_storeN hs hr]
    simp
  · rename_i h
    exact loadN_storeN_disjoint hs (by omega)

theorem toNat_out {c : Ctx} (hg : Geo c) {n : Nat} (hn : n ≤ 32) :
    (c.out + BitVec.ofNat 64 n).toNat = c.out.toNat + n := by
  have := hg.outHigh
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem out_in_span {c : Ctx} {a : Nat} (h1 : c.out.toNat ≤ a) (h2 : a < c.out.toNat + 32) :
    finSpan c a := .inr (.inr ⟨h1, h2⟩)


theorem ccode_of_writes {c : Ctx} (hg : Geo c) {m : Memory}
    (hw : Memory.WritesWithin c.m0 m (finSpan c)) :
    m.fetchBytes Binary.textBase.toNat Silmaril.Crypto.X86.Sha256O2.size =
      some (Silmaril.Crypto.X86.Sha256O2.image Binary.textBase Binary.rodataBase) := by
  rw [hw.fetchBytes]; · exact hg.ccode
  intro o ho hin; have := hg.codeApart hin
  simp only [Binary.textBase, Silmaril.Crypto.X86.Sha256O2.size, BitVec.toNat_ofNat] at ho this
  omega

theorem kTable_of_writes {c : Ctx} (hg : Geo c) {m : Memory}
    (hw : Memory.WritesWithin c.m0 m (finSpan c)) :
    m.readBytes Binary.rodataBase.toNat Silmaril.Crypto.X86.Sha256O2.kSize =
      some Silmaril.Crypto.X86.Sha256O2.kBytes := by
  rw [hw.readBytes]; · exact hg.kTable
  intro o ho hin; have := hg.codeApart hin
  simp only [Binary.rodataBase, Silmaril.Crypto.X86.Sha256O2.kSize, BitVec.toNat_ofNat] at ho this
  omega

/-- A byte stored into `blk[J]` extends what `blk[]` holds. -/
theorem blkHas_store {m m' : Memory} {sp a v : Word} {J : Nat} {B : List Byte}
    (spHigh : sp.toNat + 0x1000 < 2 ^ 64) (h : BlkHas m sp J B) (hJ : J < 64)
    (hs : storeN m a 1 v = some m') (ha : a.toNat = sp.toNat + 64 + J)
    (hr : m.Permitted .read a.toNat 1) (hv : v.toNat % 256 = (B.getD J 0).toNat) :
    BlkHas m' sp (J + 1) B := by
  intro j hj
  rw [load1_store1 hs hr, toNat_sp spHigh (by omega), ha]
  split_ifs with e
  · obtain rfl : j = J := by omega
    rw [hv]
  · exact h j (by omega)

/-- `blk[]` survives writes outside it. -/
theorem blkHas_transfer {m m' : Memory} {sp : Word} {J : Nat} {B : List Byte} {P : Nat → Prop}
    (spHigh : sp.toNat + 0x1000 < 2 ^ 64) (h : BlkHas m sp J B) (hJ : J ≤ 64)
    (hw : Memory.WritesWithin m m' P)
    (hout : ∀ a, sp.toNat + 64 ≤ a → a < sp.toNat + 64 + J → ¬ P a) : BlkHas m' sp J B := by
  intro j hj
  have e := toNat_sp spHigh (show 64 + j ≤ 0x1000 by omega)
  rw [Digest.loadN_transfer hw (fun o ho hin => by
    rw [e] at hin; exact hout _ (by omega) (by omega) hin)]
  exact h j hj

/-- `blk[]` as a span. -/
theorem readBytes_of_blkHas {m : Memory} {sp : Word} {B : List Byte}
    (spHigh : sp.toNat + 0x1000 < 2 ^ 64) (hB : B.length = 64) (h : BlkHas m sp 64 B) :
    m.readBytes (sp + 0x40#64).toNat 64 = some B := by
  have := readBytes_of_loads (m := m) (a := sp + 0x40#64) (bs := B)
    (by rw [toNat_sp spHigh (by decide)]; omega) (fun j hj => by
      have e := h j (by omega)
      rw [List.getD_eq_getElem _ _ hj] at e
      rw [← e]; congr 1; rw [BitVec.add_assoc, ← BitVec.ofNat_add])
  rwa [hB] at this

/-- The bytes of the length field: byte `i` of `encoded T` is bits `56 - 8 i` of `8 T`. -/
theorem encoded_getD (T : Word) (i : Nat) (hi : i < 8) :
    ((LengthStore.encoded T).getD i 0).toNat = ((T * 8#64).toNat >>> (56 - 8 * i)) % 256 := by
  have e : T <<< 3 = T * 8#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  simp only [LengthStore.encoded, LengthStore.swapped, LengthStore.swapped_bytes, e]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Silmaril.Machine.LittleEndian.wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]


theorem getD_of_drop {B : List Byte} {j n k : Nat} (h : B.drop j = List.replicate n 0)
    (hk : j ≤ k) : B.getD k 0 = 0 := by
  have := congrArg (fun l => l.getD (k - j) 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_replicate] at this ⊢
  rw [show j + (k - j) = k by omega] at this
  rw [this]; split <;> rfl

theorem blkHas_append {m : Memory} {sp : Word} {J : Nat} {B : List Byte} (E : List Byte)
    (h : BlkHas m sp J B) (hJ : J ≤ B.length) : BlkHas m sp J (B ++ E) := by
  intro j hj
  rw [h j hj, List.getD_append _ _ _ _ (by omega)]


theorem stkW {c : Ctx} (hg : Geo c) {m : Memory} (hw : Memory.WritesWithin c.m0 m (finSpan c))
    {a n : Nat} (h1 : c.sp.toNat - 400 ≤ a) (h2 : a + n ≤ c.sp.toNat + 152) (hn : 0 < n := by decide) :
    m.Permitted .write a n :=
  have := hg.spLow
  perm_of hw (Memory.Permitted.sub hg.stackW (by omega) (by omega) (by omega))

theorem stkR {c : Ctx} (hg : Geo c) {m : Memory} (hw : Memory.WritesWithin c.m0 m (finSpan c))
    {a n : Nat} (h1 : c.sp.toNat - 400 ≤ a) (h2 : a + n ≤ c.sp.toNat + 152) (hn : 0 < n := by decide) :
    m.Permitted .read a n :=
  have := hg.spLow
  perm_of hw (Memory.Permitted.sub hg.stackR (by omega) (by omega) (by omega))

theorem sp_add_eq {sp : Word} (_h : sp.toNat + 0x1000 < 2 ^ 64) {x y : Word}
    (hx : x.toNat < 0x1000) (hy : y.toNat < 0x1000) : sp + x = sp + y ↔ x.toNat = y.toNat := by
  constructor
  · intro e; have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_add] at this; omega
  · intro e; rw [BitVec.eq_of_toNat_eq e]


theorem and_one_eq (n : Nat) (h : n < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 n) &&& 1#32) = BitVec.ofNat 32 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.and_one_is_mod]
  omega


theorem extra_getD (tail : List Byte) {k : Nat} (hk : tail.length + 1 ≤ k) :
    (PaddingExtra.block tail).getD k 0 = 0 := by
  simp only [PaddingExtra.block, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (show tail.length ≤ k by omega)]
  rw [show k - tail.length = (k - tail.length - 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_replicate]
  split <;> rfl


/-- Close a bit-vector equation of `sp`-relative addresses or small constants through `toNat`. -/
macro "bv_eq" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]; omega))

theorem base_none_value (s : State) (next : Word) : (Base.none).value s next = 0#64 := rfl

theorem blkHas_prefix {m : Memory} {sp : Word} {J : Nat} {P B : List Byte} (h : BlkHas m sp J P)
    (hPB : ∀ j < J, B.getD j 0 = P.getD j 0) : BlkHas m sp J B := by
  intro j hj; rw [hPB j hj]; exact h j hj

/-- One byte of a successful span read, through a one-byte load. -/
theorem loadN_one_of_readBytes {m : Memory} {a n : Nat} {bs : List Byte}
    (h : m.readBytes a n = some bs) {w : Word} {j : Nat} (hj : j < n) (hw : w.toNat = a + j) :
    loadN m w 1 = some (BitVec.ofNat 64 (bs.getD j 0).toNat) := by
  have hlen : bs.length = n := Memory.readWith_length h
  unfold loadN
  rw [hw, Memory.readBytes_sub_range h hj (by omega)]
  have : (bs.drop j).take 1 = [bs.getD j 0] := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [this]
  simp [leValue]

theorem blkHas_of_readBytes {m : Memory} {sp : Word} {bs : List Byte}
    (spHigh : sp.toNat + 0x1000 < 2 ^ 64) (h : m.readBytes (sp + 0x40#64).toNat bs.length = some bs)
    (hlen : bs.length ≤ 64) : BlkHas m sp bs.length bs := by
  intro j hj
  exact loadN_one_of_readBytes h hj (by
    rw [toNat_sp spHigh (by omega), toNat_sp spHigh (by decide)]; omega)


theorem getD_pad (tail R R' : List Byte) {j : Nat} (h : j ≤ tail.length) :
    (tail ++ 0x80 :: R).getD j 0 = (tail ++ 0x80 :: R').getD j 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge j tail.length with h' | h'
  · rw [List.getElem?_append_left h', List.getElem?_append_left h']
  · obtain rfl : j = tail.length := by omega
    rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right (le_refl _)]
    simp

theorem drop_pad (tail R : List Byte) : (tail ++ 0x80 :: R).drop (tail.length + 1) = R := by
  rw [List.append_cons, List.drop_left' (by simp)]

/-- What the output loop stores, byte by byte. -/
theorem srcIdx_lane (i d : Nat) (hd : d < 4) : srcIdx (4 * i + d) = 4 * i + (3 - d) := by
  simp only [srcIdx]; omega

set_option maxRecDepth 20000 in
theorem vc_166 (c : Ctx) (hg : Geo c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 166 → inv166 c s →
      wpN Isa.sys8 code listing (cuts c) (stops c) calls subs base
        (some (200 - rdiOff c s)) 16 166 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, i, sb, hi, hdi, h12, hcx, hsb, hst, hout⟩ := hinv
  have hld := word_load hg.spHigh hsb hi
  seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hdi, h12,
    hcx, hld, Count.raw, ShiftOp.result]
  have hWl := wordBytes_lt sb i
  have oH := hg.outHigh
  have spH := hg.spHigh
  have hlen : sb.length = 32 := Memory.readWith_length hsb
  have eo : ∀ d, d ≤ 4 → (c.out + (BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 d)).toNat =
      c.out.toNat + 4 * i + d := fun d hd => by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eo0 : (c.out + BitVec.ofNat 64 (4 * i)).toNat = c.out.toNat + 4 * i := by
    rw [toNat_out hg (by omega)]
  have pw : ∀ m : Memory, Memory.WritesWithin c.m0 m (finSpan c) → ∀ d, d < 4 →
      m.Permitted .write (c.out.toNat + 4 * i + d) 1 := fun m hw d hd =>
    perm_of hw (Memory.Permitted.sub hg.outW (by omega) (by omega) (by omega))
  have pr : ∀ m : Memory, Memory.WritesWithin c.m0 m (finSpan c) → ∀ d, d < 4 →
      m.Permitted .read (c.out.toNat + 4 * i + d) 1 := fun m hw d hd =>
    perm_of hw (Memory.Permitted.sub hg.outR (by omega) (by omega) (by omega))
  have hW0 := hF.writes
  rw [eo 3 (by omega)]
  refine ⟨pw _ hW0 3 (by omega), fun m1 hs1 => ?_⟩
  have hW1 := writes_store hW0 hs1 (fun o ho => out_in_span (by rw [eo 3 (by omega)]; omega)
    (by rw [eo 3 (by omega)]; omega))
  have hL1 := loaded_of_writes hg hW1
  rw [eo 2 (by omega)]
  refine ⟨hL1, hL1, pw _ hW1 2 (by omega), fun m2 hs2 => ?_⟩
  have hW2 := writes_store hW1 hs2 (fun o ho => out_in_span (by rw [eo 2 (by omega)]; omega)
    (by rw [eo 2 (by omega)]; omega))
  have hL2 := loaded_of_writes hg hW2
  rw [eo0]
  refine ⟨hL2, pw _ hW2 0 (by omega), fun m3 hs3 => ?_⟩
  have hW3 := writes_store hW2 hs3 (fun o ho => out_in_span (by rw [eo0]; omega)
    (by rw [eo0]; omega))
  have hL3 := loaded_of_writes hg hW3
  rw [eo 1 (by omega)]
  refine ⟨hL3, hL3, hL3, pw _ hW3 1 (by omega), fun m4 hs4 => ?_⟩
  have hW4 := writes_store hW3 hs4 (fun o ho => out_in_span (by rw [eo 1 (by omega)]; omega)
    (by rw [eo 1 (by omega)]; omega))
  have hL4 := loaded_of_writes hg hW4
  have hb := fun k => (sb.getD k 0).isLt
  have hout4 : OutHas m4 c.out (4 * i + 4) sb := by
    intro k hk
    rw [load1_store1 hs4 (by rw [eo 1 (by omega)]; exact pr _ hW3 1 (by omega)),
      load1_store1 hs3 (by rw [eo0]; exact pr _ hW2 0 (by omega)),
      load1_store1 hs2 (by rw [eo 2 (by omega)]; exact pr _ hW1 2 (by omega)),
      load1_store1 hs1 (by rw [eo 3 (by omega)]; exact pr _ hW0 3 (by omega))]
    rw [toNat_out hg (by omega : k ≤ 32), eo 1 (by omega), eo 2 (by omega), eo 3 (by omega), eo0]
    have hb0 := hb (4 * i); have hb1 := hb (4 * i + 1); have hb2 := hb (4 * i + 2)
    have hb3 := hb (4 * i + 3)
    split_ifs with e1 e2 e3 e4
    · obtain rfl : k = 4 * i + 1 := by omega
      rw [srcIdx_lane i 1 (by omega)]
      simp only [Nat.reduceSub, Option.some.injEq]
      congr 1
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, Nat.reducePow]
      simp only [wordBytes] at hWl ⊢; omega
    · obtain rfl : k = 4 * i := by omega
      have e0 := srcIdx_lane i 0 (by omega)
      simp only [Nat.add_zero] at e0
      rw [e0]
      try simp only at *
      simp only [Nat.reduceSub, Option.some.injEq]
      congr 1
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, Nat.reducePow]
      simp only [wordBytes] at hWl ⊢; omega
    · obtain rfl : k = 4 * i + 2 := by omega
      rw [srcIdx_lane i 2 (by omega)]
      simp only [Nat.reduceSub, Option.some.injEq]
      congr 1
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat,
        Nat.shiftRight_eq_div_pow, Nat.reducePow]
      simp only [wordBytes] at hWl ⊢; omega
    · obtain rfl : k = 4 * i + 3 := by omega
      rw [srcIdx_lane i 3 (by omega)]
      simp only [Nat.reduceSub, Nat.add_zero, Option.some.injEq]
      congr 1
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
      simp only [wordBytes] at hWl ⊢; omega
    · exact hout k (by omega)
  have hWo : Memory.WritesWithin s.memory m4
      (fun x => c.out.toNat + 4 * i ≤ x ∧ x < c.out.toNat + 4 * i + 4) := by
    refine (((store_within hs1).mono ?_).trans ((store_within hs2).mono ?_)).trans
      (((store_within hs3).mono ?_).trans ((store_within hs4).mono ?_)) <;>
      intro x hx <;> simp only [eo 1 (by omega), eo 2 (by omega), eo 3 (by omega), eo0] at hx <;> omega
  have hsb4 : m4.readBytes (c.sp + 0x20#64).toNat 32 = some sb := by
    rw [hWo.readBytes]; · exact hsb
    intro o ho hin; rw [toNat_sp spH (by decide)] at hin; have := hg.outApart; omega
  have hF4 : Frame c { s with core := s.core, memory := m4 } := ⟨hF.rsp, hF.rbp, hF.r13, hW4⟩
  refine ⟨hL4, hL4, fun hne => ⟨hL4, ⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp],
    by seg_read [hF.r13], hW4⟩, i + 1, sb, ?_, ?_, ?_, by seg_read [hcx], hsb4, hst, ?_⟩, ?_⟩,
    fun heq => ⟨hL4, ⟨by seg_read [hF.rsp], by seg_read [hF.rbp], by seg_read [hF.r13], hW4⟩, sb,
      hsb4, hst, ?_⟩⟩
  · rcases Nat.lt_or_ge (i + 1) 8 with h | h
    · exact h
    · exfalso
      obtain rfl : i = 7 := by omega
      simp at hne
  · seg_read []
    congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · seg_read []
    congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rw [show 4 * (i + 1) = 4 * i + 4 by omega]; exact hout4
  · simp only [rdiOff]
    seg_read [hdi]
    rw [add_sub_self_left, add_sub_self_left]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · have h7 : i = 7 := by
      simp only [Bool.not_eq_false', beq_iff_eq] at heq
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    subst h7
    have := readBytes_of_loads (m := m4) (a := c.out) (bs := outBytes sb)
      (by simp only [outBytes, List.length_map, List.length_range]; omega)
      (fun j hj => by
        simp only [outBytes, List.length_map, List.length_range] at hj
        rw [hout4 j (by omega)]
        simp only [outBytes, List.getElem_map, List.getElem_range])
    simpa only [outBytes, List.length_map, List.length_range] using this

set_option maxRecDepth 20000 in
theorem vc_120 (c : Ctx) (hg : Geo c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 120 → inv120 c s →
      wpN Isa.sys8 code listing (cuts c) (stops c) calls subs base
        (some (1000 + (200 - raxOff c s))) 16 120 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, ⟨hbx, hdi, hsi⟩, i, H, B, hi, hB, hBd, hax, hcx, hst, hblk, hfin⟩ := hinv
  seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hbx, hdi,
    hsi, hax, hcx, Count.raw, ShiftOp.result, hF.rsp]
  have spH := hg.spHigh
  have spL := hg.spLow
  have hBl := hB
  have hsh : (BitVec.setWidth 8 (BitVec.ofNat 64 (56 - 8 * i))).toNat % 64 = 56 - 8 * i := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have ea : (c.sp + BitVec.ofNat 64 (120 + i)).toNat = c.sp.toNat + 64 + (56 + i) := by
    rw [toNat_sp spH (by omega)]; omega
  have hW0 := hF.writes
  rw [hsh, ea]
  refine ⟨perm_of hW0 (Memory.Permitted.sub hg.stackW (by omega) (by omega) (by omega)),
    fun m1 hs1 => ?_⟩
  have hW1 := writes_store hW0 hs1 (fun o ho => .inr (.inl (by rw [ea]; omega)))
  have hL1 := loaded_of_writes hg hW1
  have hblk1 : BlkHas m1 c.sp (56 + i + 1) B := blkHas_store spH hblk (by omega) hs1 ea
    (by rw [ea]; exact perm_of hW0 (Memory.Permitted.sub hg.stackR (by omega) (by omega) (by omega)))
    (by
      have e1 : B.getD (56 + i) 0 = (LengthStore.encoded c.T).getD i 0 := by
        rw [← hBd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [e1, encoded_getD c.T i hi]
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
      omega)
  have hst1 : StateHolds m1 (c.sp + 0x20#64) H :=
    Digest.StateHolds.transfer hst (store_within hs1) (fun o ho hin => by
      rw [toNat_sp spH (show 32 ≤ 0x1000 by decide)] at hin; rw [ea] at hin; omega)
  have hcx' : (BitVec.setWidth 32 (BitVec.ofNat 64 (56 - 8 * i))).toNat = 56 - 8 * i := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  refine ⟨hL1, hL1, fun hne => ⟨hL1, ⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp],
    by seg_read [hF.r13], hW1⟩, ⟨by seg_read [hbx], by seg_read [hdi], by seg_read [hsi]⟩,
    i + 1, H, B, ?_, hB, hBd, ?_, ?_, hst1, by rw [show 56 + (i + 1) = 56 + i + 1 by omega]; exact hblk1,
    hfin⟩, ?_⟩, fun heq => ?_⟩
  · rcases Nat.lt_or_ge (i + 1) 8 with h | h
    · exact h
    · exfalso
      obtain rfl : i = 7 := by omega
      simp at hne
  · seg_read []
    congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · have hi7 : i ≠ 7 := by rintro rfl; simp at hne
    seg_read []
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, hcx']
    omega
  · simp only [raxOff]
    seg_read [hax]
    rw [add_sub_self_left, add_sub_self_left]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · have h7 : i = 7 := by
      simp only [Bool.not_eq_false', beq_iff_eq] at heq
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_sub, hcx', BitVec.toNat_ofNat] at this
      omega
    subst h7
    have e18 : (c.sp + 24#64).toNat = c.sp.toNat + 24 := toNat_sp spH (by decide)
    have e8 : (c.sp - 8#64).toNat = c.sp.toNat - 8 := Digest.toNat_sp_sub spL (by decide)
    rw [e18]
    refine ⟨hL1, perm_of hW1 (Memory.Permitted.sub hg.stackW (by omega) (by omega) (by omega)),
      fun m2 hs2 => ?_⟩
    have hW2 := writes_store hW1 hs2 (fun o ho => .inr (.inl (by rw [e18]; omega)))
    have hL2 := loaded_of_writes hg hW2
    have hw2 := store_within hs2
    rw [e18] at hw2
    rw [e8]
    refine ⟨hL2, perm_of hW2 (Memory.Permitted.sub hg.stackW (by omega) (by omega) (by omega)),
      fun m3 hs3 => ?_⟩
    have hS3 := Stored.of_writeBytes hs3
    have hw3 : Memory.WritesWithin m2 m3 (fun a => c.sp.toNat - 8 ≤ a ∧ a < c.sp.toNat) :=
      hS3.writesWithin (fun o ho => by
        simp only [X86.length_encodeWords_singleton] at ho; omega)
    have hW3 : Memory.WritesWithin c.m0 m3 (finSpan c) :=
      hW2.trans (hw3.mono fun a ha => .inl ⟨by omega, ha.2⟩)
    have hL3 := loaded_of_writes hg hW3
    have hret : m3.readBytes (c.sp - 8#64).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [base + 151#64]) := by
      rw [e8]
      have := hS3.readWith_self (access := .read) (by
        simp only [X86.length_encodeWords_singleton]
        exact perm_of hW2 (Memory.Permitted.sub hg.stackR (by omega) (by omega) (by omega)))
      simp only [X86.length_encodeWords_singleton] at this
      exact this
    have e20 : (c.sp + 0x20#64).toNat = c.sp.toNat + 32 := toNat_sp spH (by decide)
    have hst3 : StateHolds m3 (c.sp + 0x20#64) H :=
      Digest.StateHolds.transfer (Digest.StateHolds.transfer hst1 hw2
        (fun o ho hin => by rw [e20] at hin; omega)) hw3 (fun o ho hin => by rw [e20] at hin; omega)
    have hblk3 : BlkHas m3 c.sp 64 B :=
      blkHas_transfer spH (blkHas_transfer spH hblk1 (by omega) hw2 (fun a h1 h2 h3 => by omega))
        (by omega) hw3 (fun a h1 h2 h3 => by omega)
    have hl18 : loadN m3 (c.sp + 24#64) 8 = some (c.sp + 32#64) := by
      rw [Digest.loadN_transfer hw3 (fun o ho hin => by rw [e18] at hin; omega),
        loadN_storeN hs2 (by
          rw [e18]
          exact perm_of hW1 (Memory.Permitted.sub hg.stackR (by omega) (by omega) (by omega)))]
      congr 1; apply BitVec.eq_of_toNat_eq
      have := (c.sp + 32#64).isLt
      simp only [BitVec.toNat_ofNat, Nat.reduceMul, Nat.reducePow] at this ⊢; omega
    refine ⟨hL3, compress_vc (fun _ => 0) (sp := c.sp) (blk := c.sp + 64#64) (ret := base + 151#64)
      (by rfl) (by seg_read [hdi]) (by seg_read [hsi]) (by seg_read []) hret
      (ccode_of_writes hg hW3) (kTable_of_writes hg hW3) hst3 (readBytes_of_blkHas spH hB hblk3)
      (perm_of hW3 hg.stackW) (perm_of hW3 hg.stackR) hg.spAlign spL spH
      (.inr (toNat_sp spH (by decide))) ?_⟩
    intro fin hst4 hsp4 hsv4 hWc hrip4
    have hWfin : Memory.WritesWithin c.m0 fin.memory (finSpan c) :=
      hW3.trans (hWc.mono fun a ha => by
        simp only [Digest.calleeSpan] at ha; simp only [finSpan]; omega)
    have hL4 := loaded_of_writes hg hWfin
    have hl18' : loadN fin.memory (c.sp + 24#64) 8 = some (c.sp + 32#64) := by
      rw [Digest.loadN_transfer hWc (fun o ho hin => by
        simp only [Digest.calleeSpan] at hin; rw [e18] at hin; omega)]
      exact hl18
    have hl10 : loadN fin.memory (c.sp + 16#64) 8 = some c.out := by
      rw [Digest.loadN_transfer hWfin (fun o ho hin => by
        simp only [finSpan] at hin; rw [toNat_sp spH (show 16 ≤ 0x1000 by decide)] at hin
        have := hg.outApart; omega)]
      exact hg.outSlot
    have hbp4 : fin.core.read .rbp = c.r0 .rbp := by
      rw [hsv4 .rbp (by decide)]; seg_read [hF.rbp]
    have h134 : fin.core.read .r13 = c.r0 .r13 := by
      rw [hsv4 .r13 (by decide)]; seg_read [hF.r13]
    obtain ⟨sb, hsb, hsbH⟩ := hst4
    simp only [withExtState]
    refine ⟨hrip4, hL4, ?_⟩
    seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hL4, hsp4, hl18',
      hl10]
    refine ⟨⟨⟨by seg_read [hsp4], by seg_read [hbp4], by seg_read [h134], hWfin⟩,
      0, sb, by omega, by seg_read [], by seg_read []; simp, by seg_read [], hsb,
      hsbH.trans hfin, fun k hk => absurd hk (by omega)⟩, by omega⟩

set_option maxRecDepth 20000 in
theorem vc_94 (c : Ctx) (hg : Geo c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 94 → inv94 c s →
      wpN Isa.sys8 code listing (cuts c) (stops c) calls subs base
        (some (2000 + 2 * (200 - raxOff c s))) 16 94 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, ⟨hbx, hdi, hsi⟩, j, H, B, hj, hev, hB, hBd, hax, hdx, hst, hblk, hfin⟩ := hinv
  seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hbx, hdi,
    hsi, hax, hdx, hF.rsp]
  have spH := hg.spHigh
  have hW0 := hF.writes
  have e20 : (c.sp + 0x20#64).toNat = c.sp.toNat + 32 := toNat_sp spH (by decide)
  have z1 := getD_of_drop hBd (show j ≤ j by omega)
  have z2 := getD_of_drop hBd (show j ≤ j + 1 by omega)
  refine ⟨stkW hg hW0 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega), fun m1 hs1 => ?_⟩
  have hW1 := writes_store hW0 hs1 (fun o ho => by
    simp only [finSpan, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hL1 := loaded_of_writes hg hW1
  have hb1 := blkHas_store spH hblk (by omega) hs1
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (stkR hg hW0 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) (by rw [z1]; simp)
  have hs1w := store_within hs1
  repeat (refine ⟨hL1, ?_⟩)
  refine ⟨stkW hg hW1 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega), fun m2 hs2 => ?_⟩
  have hW2 := writes_store hW1 hs2 (fun o ho => by
    simp only [finSpan, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hL2 := loaded_of_writes hg hW2
  have hb2 := blkHas_store spH hb1 (by omega) hs2
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (stkR hg hW1 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) (by rw [z2]; simp)
  have hs2w := store_within hs2
  have hst2 : StateHolds m2 (c.sp + 0x20#64) H :=
    Digest.StateHolds.transfer (Digest.StateHolds.transfer hst hs1w (fun o ho hin => by
      rw [e20] at hin; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hin; omega)) hs2w
      (fun o ho hin => by rw [e20] at hin; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hin; omega)
  have hF2 : ∀ core : State, core.read .rsp = c.sp → core.read .rbp = c.r0 .rbp →
      core.read .r13 = c.r0 .r13 → Frame c { s with core := core, memory := m2 } :=
    fun _ a b d => ⟨a, b, d, hW2⟩
  repeat (refine ⟨hL2, ?_⟩)
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hj2 : j + 2 ≠ 56 := by
      intro e
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hne
      apply hne
      rw [sp_add_eq spH (by simp only [BitVec.toNat_ofNat]; omega)
        (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    repeat (refine ⟨hL2, ?_⟩)
    refine ⟨⟨hF2 _ (by seg_read [hF.rsp]) (by seg_read [hF.rbp]) (by seg_read [hF.r13]),
      ⟨by seg_read [hbx], by seg_read [hdi], by seg_read [hsi]⟩, j + 2, H, B, by omega, by omega, hB,
      ?_, ?_, by seg_read [hdx], hst2, by rw [show j + 2 = j + 1 + 1 by omega]; exact hb2, hfin⟩, ?_⟩
    · have : B.drop (j + 2) = (B.drop j).drop 2 := by rw [List.drop_drop]
      rw [this, hBd, List.drop_replicate]; congr 1
    · seg_read []
      congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simp only [raxOff]
      seg_read [hax]
      rw [add_sub_self_left, add_sub_self_left]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
  · have hj2 : j + 2 = 56 := by
      simp only [Bool.not_eq_false', beq_iff_eq] at heq
      rw [sp_add_eq spH (by simp only [BitVec.toNat_ofNat]; omega)
        (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] at heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at heq; omega
    repeat (refine ⟨hL2, ?_⟩)
    refine ⟨⟨hF2 _ (by seg_read [hF.rsp]) (by seg_read [hF.rbp]) (by seg_read [hF.r13]),
      ⟨by seg_read [hbx], by seg_read [hdi], by seg_read [hsi]⟩, 0, H, B ++ LengthStore.encoded c.T,
      by omega, by simp [hB, LengthStore.encoded_length], by rw [List.drop_append_of_le_length (by omega)]; simp [hB],
      by seg_read [], by seg_read [], hst2, ?_, hfin⟩, by omega⟩
    exact blkHas_append _ (by rw [show 56 + 0 = j + 1 + 1 by omega]; exact hb2) (by omega)

set_option maxRecDepth 20000 in
theorem vc_71 (c : Ctx) (hg : Geo c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 71 → inv71 c s →
      wpN Isa.sys8 code listing (cuts c) (stops c) calls subs base
        (some (2000 + 2 * (200 - raxOff c s) + 1)) 16 71 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, ⟨hbx, hdi, hsi⟩, j, H, B, hj, hB, hBd, hax, hcx, hst, hblk, hfin⟩ := hinv
  have spH := hg.spHigh
  have hW0 := hF.writes
  have e20 : (c.sp + 0x20#64).toNat = c.sp.toNat + 32 := toNat_sp spH (by decide)
  have hand := and_one_eq (55 - j) (by omega)
  rcases Nat.mod_two_eq_zero_or_one (55 - j) with hpar | hpar <;> rw [hpar] at hand
  · -- `j` odd: one byte, then the loop or the length
    seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hbx, hdi,
      hsi, hax, hcx, hF.rsp, hand, BitVec.reduceBEq, BitVec.reduceEq, Bool.not_true,
      Bool.not_false, false_implies, true_implies]
    have z1 := getD_of_drop hBd (show j ≤ j by omega)
    refine ⟨stkW hg hW0 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega), fun m1 hs1 => ?_⟩
    have hW1 := writes_store hW0 hs1 (fun o ho => by
      simp only [finSpan, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    have hL1 := loaded_of_writes hg hW1
    have hb1 := blkHas_store spH hblk (by omega) hs1
      (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (stkR hg hW0 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) (by rw [z1]; simp)
    have hst1 : StateHolds m1 (c.sp + 0x20#64) H :=
      Digest.StateHolds.transfer hst (store_within hs1) (fun o ho hin => by
        rw [e20] at hin; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hin; omega)
    repeat (refine ⟨hL1, ?_⟩)
    refine ⟨fun heq => ?_, fun hne => ?_⟩
    · have hj1 : j + 1 = 56 := by
        simp only [beq_iff_eq] at heq
        rw [sp_add_eq spH (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
          (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)] at heq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at heq; omega
      repeat (refine ⟨hL1, ?_⟩)
      refine ⟨⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp], by seg_read [hF.r13], hW1⟩,
        ⟨by seg_read [hbx], by seg_read [hdi], by seg_read [hsi]⟩, 0, H, B ++ LengthStore.encoded c.T,
        by omega, by simp [hB, LengthStore.encoded_length],
        by rw [List.drop_append_of_le_length (by omega)]; simp [hB],
        by seg_read [], by seg_read [], hst1, ?_, hfin⟩, by omega⟩
      exact blkHas_append _ (by rw [show 56 + 0 = j + 1 by omega]; exact hb1) (by omega)
    · have hj1 : j + 1 ≠ 56 := by
        intro e
        simp only [beq_eq_false_iff_ne, ne_eq] at hne
        apply hne
        rw [sp_add_eq spH (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
          (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      repeat (refine ⟨hL1, ?_⟩)
      refine ⟨⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp], by seg_read [hF.r13], hW1⟩,
        ⟨by seg_read [hbx], by seg_read [hdi], by seg_read [hsi]⟩, j + 1, H, B, by omega, by omega, hB,
        ?_, ?_, ?_, hst1, hb1, hfin⟩, ?_⟩
      · rw [← List.drop_drop, hBd, List.drop_replicate]; congr 1
      · seg_read []
        congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      · seg_read []
        congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      · simp only [raxOff]
        seg_read [hax]
        rw [add_sub_self_left, add_sub_self_left]
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
  · -- `j` even: straight into the loop
    seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hbx, hdi,
      hsi, hax, hcx, hF.rsp, hand, BitVec.reduceBEq, BitVec.reduceEq, Bool.not_true,
      Bool.not_false, false_implies, true_implies]
    refine ⟨⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp], by seg_read [hF.r13], hW0⟩,
      ⟨by seg_read [hbx], by seg_read [hdi], by seg_read [hsi]⟩, j, H, B, by omega, by omega, hB,
      hBd, by seg_read [hax], ?_, hst, hblk, hfin⟩, ?_⟩
    · seg_read []
      congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simp only [raxOff]
      seg_read [hax]
      omega

set_option maxRecDepth 20000 in
theorem vc_368 (c : Ctx) (hg : Geo c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 368 → inv368 c s →
      wpN Isa.sys8 code listing (cuts c) (stops c) calls subs base
        (some (5000 + (200 - raxOff c s))) 16 368 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, ⟨hbx, hsi⟩, hlong, j, hj1, hj, hev, hax, hdx, hst, hblk⟩ := hinv
  seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hbx,
    hsi, hax, hdx, hF.rsp]
  have spH := hg.spHigh
  have hW0 := hF.writes
  have e20 : (c.sp + 0x20#64).toNat = c.sp.toNat + 32 := toNat_sp spH (by decide)
  have z1 := extra_getD c.tail (show c.tail.length + 1 ≤ j by omega)
  have z2 := extra_getD c.tail (show c.tail.length + 1 ≤ j + 1 by omega)
  refine ⟨stkW hg hW0 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega), fun m1 hs1 => ?_⟩
  have hW1 := writes_store hW0 hs1 (fun o ho => by
    simp only [finSpan, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hL1 := loaded_of_writes hg hW1
  have hb1 := blkHas_store spH hblk (by omega) hs1
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (stkR hg hW0 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) (by rw [z1]; simp)
  have hs1w := store_within hs1
  repeat (refine ⟨hL1, ?_⟩)
  refine ⟨stkW hg hW1 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega), fun m2 hs2 => ?_⟩
  have hW2 := writes_store hW1 hs2 (fun o ho => by
    simp only [finSpan, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hL2 := loaded_of_writes hg hW2
  have hb2 := blkHas_store spH hb1 (by omega) hs2
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (stkR hg hW1 (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) (by rw [z2]; simp)
  have hs2w := store_within hs2
  have hst2 : StateHolds m2 (c.sp + 0x20#64) c.H :=
    Digest.StateHolds.transfer (Digest.StateHolds.transfer hst hs1w (fun o ho hin => by
      rw [e20] at hin; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hin; omega)) hs2w
      (fun o ho hin => by rw [e20] at hin; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hin; omega)
  repeat (refine ⟨hL2, ?_⟩)
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hj2 : j + 2 ≠ 64 := by
      intro e
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hne
      apply hne
      rw [sp_add_eq spH (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (by simp only [BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    repeat (refine ⟨hL2, ?_⟩)
    refine ⟨⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp], by seg_read [hF.r13], hW2⟩,
      ⟨by seg_read [hbx], by seg_read [hsi]⟩, hlong, j + 2, by omega, by omega,
      by omega, ?_, by seg_read [hdx], hst2, by rw [show j + 2 = j + 1 + 1 by omega]; exact hb2⟩, ?_⟩
    · seg_read []
      congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simp only [raxOff]
      seg_read [hax]
      rw [add_sub_self_left, add_sub_self_left]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
  · have hj2 : j + 2 = 64 := by
      simp only [Bool.not_eq_false', beq_iff_eq] at heq
      rw [sp_add_eq spH (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (by simp only [BitVec.toNat_ofNat]; omega)] at heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at heq; omega
    repeat (refine ⟨hL2, ?_⟩)
    exact ⟨⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp], by seg_read [hF.r13], hW2⟩,
      by seg_read [hbx], by seg_read [hsi], hlong, hst2,
      by have := hb2; rwa [show j + 1 + 1 = 64 by omega] at this⟩, by omega⟩

set_option maxRecDepth 20000 in
theorem vc_384 (c : Ctx) (hg : Geo c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 384 → inv384 c s →
      wpN Isa.sys8 code listing (cuts c) (stops c) calls subs base (some 4000) 16 384 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, hbx, hsi, hlong, hst, hblk⟩ := hinv
  seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hbx,
    hsi, hF.rsp]
  have spH := hg.spHigh
  have spL := hg.spLow
  have hW1 := hF.writes
  have hL1 := hl
  have e18 : (c.sp + 24#64).toNat = c.sp.toNat + 24 := toNat_sp spH (by decide)
  have e8 : (c.sp - 8#64).toNat = c.sp.toNat - 8 := Digest.toNat_sp_sub spL (by decide)
  have e20 : (c.sp + 0x20#64).toNat = c.sp.toNat + 32 := toNat_sp spH (by decide)
  have e80 : (c.sp + 128#64).toNat = c.sp.toNat + 128 := toNat_sp spH (by decide)
  rw [e18]
  refine ⟨perm_of hW1 (Memory.Permitted.sub hg.stackW (by omega) (by omega) (by omega)),
    fun m2 hs2 => ?_⟩
  have hW2 := writes_store hW1 hs2 (fun o ho => .inr (.inl (by rw [e18]; omega)))
  have hL2 := loaded_of_writes hg hW2
  have hw2 := store_within hs2
  rw [e18] at hw2
  rw [e8]
  refine ⟨hL2, perm_of hW2 (Memory.Permitted.sub hg.stackW (by omega) (by omega) (by omega)),
    fun m3 hs3 => ?_⟩
  have hS3 := Stored.of_writeBytes hs3
  have hw3 : Memory.WritesWithin m2 m3 (fun a => c.sp.toNat - 8 ≤ a ∧ a < c.sp.toNat) :=
    hS3.writesWithin (fun o ho => by
      simp only [X86.length_encodeWords_singleton] at ho; omega)
  have hW3 : Memory.WritesWithin c.m0 m3 (finSpan c) :=
    hW2.trans (hw3.mono fun a ha => .inl ⟨by omega, ha.2⟩)
  have hL3 := loaded_of_writes hg hW3
  have hret : m3.readBytes (c.sp - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [base + 399#64]) := by
    rw [e8]
    have := hS3.readWith_self (access := .read) (by
      simp only [X86.length_encodeWords_singleton]
      exact perm_of hW2 (Memory.Permitted.sub hg.stackR (by omega) (by omega) (by omega)))
    simp only [X86.length_encodeWords_singleton] at this
    exact this
  have hst3 : StateHolds m3 (c.sp + 0x20#64) c.H :=
    Digest.StateHolds.transfer (Digest.StateHolds.transfer hst hw2
      (fun o ho hin => by rw [e20] at hin; omega)) hw3 (fun o ho hin => by rw [e20] at hin; omega)
  have hblk3 : BlkHas m3 c.sp 64 (PaddingExtra.block c.tail) :=
    blkHas_transfer spH (blkHas_transfer spH hblk (by omega) hw2 (fun a h1 h2 h3 => by omega))
      (by omega) hw3 (fun a h1 h2 h3 => by omega)
  have hl18 : loadN m3 (c.sp + 24#64) 8 = some (c.sp + 32#64) := by
    rw [Digest.loadN_transfer hw3 (fun o ho hin => by rw [e18] at hin; omega),
      loadN_storeN hs2 (by
        rw [e18]
        exact perm_of hW1 (Memory.Permitted.sub hg.stackR (by omega) (by omega) (by omega)))]
    congr 1; apply BitVec.eq_of_toNat_eq
    have := (c.sp + 32#64).isLt
    simp only [BitVec.toNat_ofNat, Nat.reduceMul, Nat.reducePow] at this ⊢; omega
  refine ⟨hL3, compress_vc (fun _ => 0) (sp := c.sp) (blk := c.sp + 64#64) (ret := base + 399#64)
    (by rfl) (by seg_read []) (by seg_read [hsi]) (by seg_read []) hret
    (ccode_of_writes hg hW3) (kTable_of_writes hg hW3) hst3
    (readBytes_of_blkHas spH (PaddingExtra.block_length _ (by have := hg.room; omega)) hblk3)
    (perm_of hW3 hg.stackW) (perm_of hW3 hg.stackR) hg.spAlign spL spH
    (.inr (toNat_sp spH (by decide))) ?_⟩
  intro fin hst4 hsp4 hsv4 hWc hrip4
  have hWfin : Memory.WritesWithin c.m0 fin.memory (finSpan c) :=
    hW3.trans (hWc.mono fun a ha => by
      simp only [Digest.calleeSpan] at ha; simp only [finSpan]; omega)
  have hL4 := loaded_of_writes hg hWfin
  have hl18' : loadN fin.memory (c.sp + 24#64) 8 = some (c.sp + 32#64) := by
    rw [Digest.loadN_transfer hWc (fun o ho hin => by
      simp only [Digest.calleeSpan] at hin; rw [e18] at hin; omega)]
    exact hl18
  have hbp4 : fin.core.read .rbp = c.r0 .rbp := by
    rw [hsv4 .rbp (by decide)]; seg_read [hF.rbp]
  have h134 : fin.core.read .r13 = c.r0 .r13 := by
    rw [hsv4 .r13 (by decide)]; seg_read [hF.r13]
  have hbx4 : fin.core.read .rbx = c.T * 8#64 := by
    rw [hsv4 .rbx (by decide)]; seg_read [hbx]
  simp only [withExtState]
  refine ⟨hrip4, hL4, ?_⟩
  seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hL4, hsp4, hl18',
    hbx4]
  rw [e80]
  refine ⟨perm_of hWfin (Memory.Permitted.sub hg.stackW (by omega) (by omega) (by omega)),
    fun m5 hs5 => ?_⟩
  have hW5 := writes_store hWfin hs5 (fun o ho => .inr (.inl (by rw [e80]; omega)))
  have hL5 := loaded_of_writes hg hW5
  have hst5 : StateHolds m5 (c.sp + 0x20#64) (compressBlock c.H (PaddingExtra.block c.tail)) :=
    Digest.StateHolds.transfer hst4 (store_within hs5) (fun o ho hin => by
      rw [e20] at hin; rw [e80] at hin; omega)
  repeat (refine ⟨hL5, ?_⟩)
  refine ⟨⟨⟨by seg_read [hsp4], by seg_read [hbp4], by seg_read [h134], hW5⟩,
    ⟨by seg_read [hbx4], by seg_read [], by seg_read []⟩, 0, _, List.replicate 56 0, by omega,
    by simp, by simp, by seg_read [], by seg_read [], hst5, fun k hk => absurd hk (by omega), ?_⟩,
    by omega⟩
  have hlen := hg.room
  have hfin : c.Hfin = compressBlock (compressBlock c.H (PaddingExtra.block c.tail))
      (SecondPaddingFrame.block c.T) := by
    simp only [Ctx.Hfin, Ctx.blocks, TailPaddingReference.blocks,
      show ¬ c.tail.length < 56 by omega, ite_false, List.foldl_cons, List.foldl_nil,
      PaddingExtra.block, List.append_assoc, List.singleton_append]
    rfl
  rw [hfin]; rfl

set_option maxRecDepth 20000 in
theorem vc_entry (c : Ctx) (hg : Geo c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 0 → pre c s →
      wpN Isa.sys8 code listing (cuts c) (stops c) calls subs base none 24 0 s := by
  intro s hlv hl hrip hpre
  obtain ⟨hF, hm0, hdx, hst, htail, hblen⟩ := hpre
  seg_vc8 [listing, cuts, stops, calls, subs, Mem.ofReg, Mem.ofIndex, Silmaril.X86.Lift.ix, hrip,
    hl, hdx, hblen, hF.rsp, base_none_value]
  have spH := hg.spHigh
  have hn := hg.room
  have hW0 := hF.writes
  have e20 : (c.sp + 0x20#64).toNat = c.sp.toNat + 32 := toNat_sp spH (by decide)
  have e80 : (c.sp + 128#64).toNat = c.sp.toNat + 128 := toNat_sp spH (by decide)
  have ea : (c.sp + (BitVec.ofNat 64 c.tail.length + 64#64)).toNat = c.sp.toNat + 64 + c.tail.length := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb0 : BlkHas s.memory c.sp c.tail.length c.tail := blkHas_of_readBytes spH htail (by omega)
  rw [ea]
  refine ⟨stkW hg hW0 (by omega) (by omega), fun m1 hs1 => ?_⟩
  have hW1 := writes_store hW0 hs1 (fun o ho => by simp only [finSpan]; rw [ea]; omega)
  have hL1 := loaded_of_writes hg hW1
  have hb1 : BlkHas m1 c.sp (c.tail.length + 1) (c.tail ++ [0x80]) :=
    blkHas_store spH (blkHas_prefix hb0 (fun j hj => by rw [List.getD_append _ _ _ _ hj])) hn hs1 ea
      (stkR hg hW0 (by rw [ea]; omega) (by rw [ea]; omega)) (by
        rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]; rfl)
  rw [e80]
  refine ⟨hL1, stkW hg hW1 (by omega) (by omega), fun m2 hs2 => ?_⟩
  have hW2 := writes_store hW1 hs2 (fun o ho => by simp only [finSpan]; rw [e80]; omega)
  have hL2 := loaded_of_writes hg hW2
  have hw2 := store_within hs2
  rw [e80] at hw2
  have hb2 : BlkHas m2 c.sp (c.tail.length + 1) (c.tail ++ [0x80]) :=
    blkHas_transfer spH hb1 (by omega) hw2 (fun a h1 h2 h3 => by omega)
  have hst2 : StateHolds m2 (c.sp + 0x20#64) c.H := by
    exact Digest.StateHolds.transfer (Digest.StateHolds.transfer hst (store_within hs1)
      (fun o ho hin => by rw [e20, ea] at hin; omega)) hw2 (fun o ho hin => by rw [e20] at hin; omega)
  have hn1 : (BitVec.ofNat 64 c.tail.length + 1#64).toNat = c.tail.length + 1 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hF2 : ∀ core : State, core.read .rsp = c.sp → core.read .rbp = c.r0 .rbp →
      core.read .r13 = c.r0 .r13 → Frame c { s with core := core, memory := m2 } :=
    fun _ a b d => ⟨a, b, d, hW2⟩
  repeat (refine ⟨hL2, ?_⟩)
  refine ⟨fun hgt => ?_, fun hle => ?_⟩
  · have hlong : 56 ≤ c.tail.length := by
      simp only [Bool.not_eq_true', BitVec.ule, hn1, decide_eq_false_iff_not] at hgt
      simp at hgt; omega
    repeat (refine ⟨hL2, ?_⟩)
    refine ⟨fun h64 => ?_, fun h64 => ?_⟩
    · have hn63 : c.tail.length = 63 := by
        simp only [beq_iff_eq] at h64; have := congrArg BitVec.toNat h64; rw [hn1] at this
        simp at this; omega
      refine ⟨hL2, hF2 _ (by seg_read [hF.rsp]) (by seg_read [hF.rbp]) (by seg_read [hF.r13]),
        by seg_read []; bv_eq, by seg_read [], hlong, hst2, ?_⟩
      have := blkHas_prefix (B := PaddingExtra.block c.tail) hb2 (fun j hj => getD_pad _ _ _ (by omega))
      rwa [hn63] at this
    · have hn63 : c.tail.length ≠ 63 := by
        intro e; simp only [beq_eq_false_iff_ne, ne_eq] at h64; apply h64; bv_eq
      have hpar : (BitVec.setWidth 8 (c.sp + (64#64 + (BitVec.ofNat 64 c.tail.length + 1#64))) &&&
          (1 : BitVec 8)).toNat = (c.tail.length + 1) % 2 := by
        have := hg.spAlign
        have h1 : (1 : BitVec 8).toNat = 1 := rfl
        rw [BitVec.toNat_and, h1, Nat.and_one_is_mod]
        simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        omega
      repeat (refine ⟨hL2, ?_⟩)
      refine ⟨fun hev => ?_, fun hodd => ?_⟩
      · have he : (c.tail.length + 1) % 2 = 0 := by
          simp only [beq_iff_eq] at hev; have := congrArg BitVec.toNat hev; rw [hpar] at this
          simpa using this
        refine ⟨hL2, hF2 _ (by seg_read [hF.rsp]) (by seg_read [hF.rbp]) (by seg_read [hF.r13]),
          ⟨by seg_read []; bv_eq, by seg_read []⟩, hlong, c.tail.length + 1, by omega, by omega,
          by omega, by seg_read []; bv_eq, by seg_read [], hst2, ?_⟩
        exact blkHas_prefix hb2 (fun j hj => getD_pad _ _ _ (by omega))
      · have ho : (c.tail.length + 1) % 2 = 1 := by
          simp only [beq_eq_false_iff_ne, ne_eq] at hodd
          have : (c.tail.length + 1) % 2 ≠ 0 := fun e => hodd (by
            apply BitVec.eq_of_toNat_eq; rw [hpar, e]; rfl)
          omega
        have ea1 : (c.sp + (64#64 + (BitVec.ofNat 64 c.tail.length + 1#64))).toNat =
            c.sp.toNat + 64 + (c.tail.length + 1) := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [ea1]
        refine ⟨hL2, hL2, stkW hg hW2 (by omega) (by omega), fun m3 hs3 => ?_⟩
        have hW3 := writes_store hW2 hs3 (fun o ho => by simp only [finSpan]; rw [ea1]; omega)
        have hL3 := loaded_of_writes hg hW3
        have hb2' : BlkHas m2 c.sp (c.tail.length + 1) (PaddingExtra.block c.tail) :=
          blkHas_prefix hb2 (fun j hj => getD_pad _ _ _ (by omega))
        have hb3 := blkHas_store spH hb2' (by omega) hs3 ea1 (stkR hg hW2 (by rw [ea1]; omega)
          (by rw [ea1]; omega)) (show (0#64).toNat % 256 = _ by
            rw [extra_getD c.tail (le_refl _)]; rfl)
        have hst3 : StateHolds m3 (c.sp + 0x20#64) c.H :=
          Digest.StateHolds.transfer hst2 (store_within hs3) (fun o ho hin => by
            rw [e20, ea1] at hin; omega)
        repeat (refine ⟨hL3, ?_⟩)
        refine ⟨fun h384 => ?_, fun h368 => ?_⟩
        · have h62 : c.tail.length = 62 := by
            simp only [beq_iff_eq] at h384
            rw [sp_add_eq spH (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
              (by simp only [BitVec.toNat_ofNat]; omega)] at h384
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h384; omega
          repeat (refine ⟨hL3, ?_⟩)
          refine ⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp], by seg_read [hF.r13], hW3⟩,
            by seg_read []; bv_eq, by seg_read [], hlong, hst3, ?_⟩
          have := hb3
          rwa [show c.tail.length + 1 + 1 = 64 by omega] at this
        · have h62 : c.tail.length ≠ 62 := by
            intro e
            simp only [beq_eq_false_iff_ne, ne_eq] at h368
            apply h368
            rw [sp_add_eq spH (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
              (by simp only [BitVec.toNat_ofNat]; omega)]
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
          repeat (refine ⟨hL3, ?_⟩)
          exact ⟨⟨by seg_read [hF.rsp], by seg_read [hF.rbp], by seg_read [hF.r13], hW3⟩,
            ⟨by seg_read []; bv_eq, by seg_read []⟩, hlong, c.tail.length + 2, by omega, by omega,
            by omega, by seg_read []; bv_eq, by seg_read [], hst3, hb3⟩
  · have hle56 : c.tail.length + 1 ≤ 56 := by
      simp only [Bool.not_eq_false', BitVec.ule, hn1] at hle
      simp at hle; omega
    have hfin1 : ∀ R : List Byte, R = List.replicate (55 - c.tail.length) 0 →
        compressBlock c.H ((c.tail ++ 0x80 :: R) ++ LengthStore.encoded c.T) = c.Hfin := by
      rintro R rfl
      simp only [Ctx.Hfin, Ctx.blocks, TailPaddingReference.blocks,
        show c.tail.length < 56 by omega, ite_true, List.foldl_cons, List.foldl_nil,
        TailPaddingFrame.block]
    repeat (refine ⟨hL2, ?_⟩)
    refine ⟨fun h56 => ?_, fun h56 => ?_⟩
    · have h55 : c.tail.length = 55 := by
        simp only [beq_iff_eq] at h56; have := congrArg BitVec.toNat h56; rw [hn1] at this
        simp at this; omega
      repeat (refine ⟨hL2, ?_⟩)
      refine ⟨hF2 _ (by seg_read [hF.rsp]) (by seg_read [hF.rbp]) (by seg_read [hF.r13]),
        ⟨by seg_read []; bv_eq, by seg_read [], by seg_read []⟩, 0, c.H,
        c.tail ++ 0x80 :: LengthStore.encoded c.T, by omega,
        by simp [LengthStore.encoded_length, h55], ?_, by seg_read [], by seg_read [],
        hst2, ?_, ?_⟩
      · rw [show 56 = c.tail.length + 1 by omega, drop_pad]
      · have := blkHas_prefix (B := c.tail ++ 0x80 :: LengthStore.encoded c.T) hb2
          (fun j hj => getD_pad _ _ _ (by omega))
        rwa [show c.tail.length + 1 = 56 + 0 by omega] at this
      · have := hfin1 [] (by rw [h55]; rfl)
        simpa using this
    · have h55 : c.tail.length ≠ 55 := by
        intro e; simp only [beq_eq_false_iff_ne, ne_eq] at h56; apply h56; bv_eq
      repeat (refine ⟨hL2, ?_⟩)
      refine ⟨hF2 _ (by seg_read [hF.rsp]) (by seg_read [hF.rbp]) (by seg_read [hF.r13]),
        ⟨by seg_read []; bv_eq, by seg_read [], by seg_read []⟩, c.tail.length + 1, c.H,
        c.tail ++ 0x80 :: List.replicate (55 - c.tail.length) 0, by omega,
        by simp; omega, ?_, by seg_read []; bv_eq, by seg_read []; bv_eq,
        hst2, ?_, hfin1 _ rfl⟩
      · rw [drop_pad]; congr 1; omega
      · exact blkHas_prefix hb2 (fun j hj => getD_pad _ _ _ (by omega))

/-- All the VCs of the `sha_final` segment. -/
theorem vc_all (c : Ctx) (hg : Geo c) :
    vc Isa.sys8 code listing (cuts c) (stops c) calls subs base 0 (pre c) 24 := by
  refine ⟨vc_entry c hg, ?_⟩
  intro oc hoc
  simp only [cuts, List.mem_cons, List.not_mem_nil, or_false] at hoc
  rcases hoc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_71 c hg s hlv hl hrip hinv)
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_94 c hg s hlv hl hrip hinv)
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_120 c hg s hlv hl hrip hinv)
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_166 c hg s hlv hl hrip hinv)
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_368 c hg s hlv hl hrip hinv)
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_384 c hg s hlv hl hrip hinv)

/-- **VERIFIED. `sha_final` in `sha256sum-min`.** From the padding (`0x403034`: the last `read`
returned 0, the `struct sha` holding the chaining value `H` of the full blocks absorbed and the
buffered `tail`, the total `T` in `rdx`), the process reaches by retiring steps of the `Ext8`
machine (the silent steps of `GStep`; no system call) the output stage `0x40310a`, with the
digest of `Hfin = (TailPaddingReference.blocks tail T).foldl compressBlock H` copied out
big-endian to the caller's buffer, and writes only inside `finSpan` (the callee frames, the spill
slot, the struct, the buffer). -/
theorem final_runs (c : Ctx) (hg : Geo c) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 0)
    (hpre : pre c s) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep8 s t ∧ t.faulted = false ∧
      Loaded t.memory base code ∧ t.core.rip = base + BitVec.ofNat 64 214 ∧ post c t := by
  obtain ⟨o, q, t, hq, ht, hr, hrip', hl', hlv'⟩ :=
    sound (I := Isa.sys8) listing_valid (vc_all c hg) s hlv hl hrip hpre
  refine ⟨t, reaches_sys8 hr, hlv', hl', ?_⟩
  simp only [stops, List.lookup_cons, List.lookup_nil] at hq
  split at hq
  · rename_i he; cases hq; simp only [beq_iff_eq] at he; subst he; exact ⟨hrip', ht⟩
  · split at hq
    · cases hq; exact ht.elim
    · cases hq

end Silmaril.Apps.Sha256sum.Binary.Digest.Final
