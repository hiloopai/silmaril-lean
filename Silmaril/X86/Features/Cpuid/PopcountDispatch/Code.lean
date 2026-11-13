module

public import Silmaril.X86.SegVC.Tactic
public import Silmaril.X86.Features.State

/-!
# The pinned POPCNT-dispatching function

`apps/popcount-dispatch/src/popcount_dispatch.c`, built by
`apps/popcount-dispatch/build.sh` (gcc 13.3.0 `-O2`, freestanding): the 127 bytes
of its `.text` (sha256 `f78522f9…4c6d`, CIDv1
`bafkreihxqurpsee5yszau3tqaw7efotq7nfu72ghdzckxwlyfwib542mnu`; the object file is
pinned in `problems/x86/popcount-dispatch/problem.toml`), its listing, and the
SWAR identity its fallback relies on.

```
   0: push rbx                 1: mov eax, 1               6: xor ecx, ecx
   8: cpuid                    a: and ecx, 0x800000       10: jne 0x78
  12: movabs rdx, 0x5555…     1c: mov rax, rdi            1f: shr rdi, 1
  22: pop rbx                 23: movabs rcx, 0x3333…     2d: and rax, rdx
  30: and rdi, rdx            33: add rax, rdi            36: mov rdx, rax
  39: shr rax, 2              3d: and rax, rcx            40: and rdx, rcx
  43: movabs rcx, 0x0f0f…     4d: add rdx, rax            50: mov rax, rdx
  53: shr rdx, 4              57: and rdx, rcx            5a: and rax, rcx
  5d: add rax, rdx            60: movabs rdx, 0x0101…     6a: imul rax, rdx
  6e: shr rax, 56             72: ret
  78: popcnt rax, rdi         7d: pop rbx                 7e: ret
```

## The SWAR identity, without native evaluation

Every level of the fallback is a masked add, `lvl m s x = (x & m) + ((x >> s) & m)`.
For a value split into its high bytes and its low byte, `y ++ z`, a level splits
the same way (`lvl_append8`) when the mask hides the bits that the shift moves across
the byte boundary and the low byte's sum does not carry. Both are checked by `decide`
over the 256 bytes, so the three levels act byte-wise (`lanes_succ`), and each byte
ends up holding its own popcount (`lanes8_eq`, by `decide`). The multiply by
`0x0101…01` then sums the eight byte counts into the top byte (`mul_lanes`, by
`ring` and `omega`). `swar_eq_popcnt` is the result.
-/

@[expose] public section

namespace Silmaril.X86.Features.Cpuid.PopcountDispatch

open Silmaril.X86 (Word Byte Reg AluOp)
open Silmaril.X86.Ext

set_option maxRecDepth 8000 in
/-- The `.text` of `popcount_dispatch.o`. -/
def code : List Byte := [
  0x53, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x31, 0xC9, 0x0F, 0xA2, 0x81, 0xE1, 0x00, 0x00, 0x80, 0x00,
  0x75, 0x66, 0x48, 0xBA, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x48, 0x89, 0xF8, 0x48,
  0xD1, 0xEF, 0x5B, 0x48, 0xB9, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x48, 0x21, 0xD0,
  0x48, 0x21, 0xD7, 0x48, 0x01, 0xF8, 0x48, 0x89, 0xC2, 0x48, 0xC1, 0xE8, 0x02, 0x48, 0x21, 0xC8,
  0x48, 0x21, 0xCA, 0x48, 0xB9, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x48, 0x01, 0xC2,
  0x48, 0x89, 0xD0, 0x48, 0xC1, 0xEA, 0x04, 0x48, 0x21, 0xCA, 0x48, 0x21, 0xC8, 0x48, 0x01, 0xD0,
  0x48, 0xBA, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x48, 0x0F, 0xAF, 0xC2, 0x48, 0xC1,
  0xE8, 0x38, 0xC3, 0x0F, 0x1F, 0x44, 0x00, 0x00, 0xF3, 0x48, 0x0F, 0xB8, 0xC7, 0x5B, 0xC3]

set_option maxRecDepth 8000 in
theorem code_length : code.length = 127 := rfl

/-- The listing: every instruction but the CPUID at 8, which is a summary. -/
def listing : List (Nat × Silmaril.X86.Ext.Instr × Nat) :=
  [(0x00, .push .rbx, 1),
   (0x01, .movI32 .rax 1, 5),
   (0x06, .alu .d .xor (.reg .rcx) .rcx, 2),
   (0x0a, .aluI .d .and (.reg .rcx) 0x00800000, 6),
   (0x10, .jcc8 .ne 0x66, 2),
   (0x12, .movabs .rdx 0x5555555555555555, 10),
   (0x1c, .mov .q (.reg .rax) .rdi, 3),
   (0x1f, .shift .q .shr (.reg .rdi) .one, 3),
   (0x22, .pop .rbx, 1),
   (0x23, .movabs .rcx 0x3333333333333333, 10),
   (0x2d, .alu .q .and (.reg .rax) .rdx, 3),
   (0x30, .alu .q .and (.reg .rdi) .rdx, 3),
   (0x33, .alu .q .add (.reg .rax) .rdi, 3),
   (0x36, .mov .q (.reg .rdx) .rax, 3),
   (0x39, .shift .q .shr (.reg .rax) (.imm 2), 4),
   (0x3d, .alu .q .and (.reg .rax) .rcx, 3),
   (0x40, .alu .q .and (.reg .rdx) .rcx, 3),
   (0x43, .movabs .rcx 0x0f0f0f0f0f0f0f0f, 10),
   (0x4d, .alu .q .add (.reg .rdx) .rax, 3),
   (0x50, .mov .q (.reg .rax) .rdx, 3),
   (0x53, .shift .q .shr (.reg .rdx) (.imm 4), 4),
   (0x57, .alu .q .and (.reg .rdx) .rcx, 3),
   (0x5a, .alu .q .and (.reg .rax) .rcx, 3),
   (0x5d, .alu .q .add (.reg .rax) .rdx, 3),
   (0x60, .movabs .rdx 0x0101010101010101, 10),
   (0x6a, .imul .q .rax (.reg .rdx), 4),
   (0x6e, .shift .q .shr (.reg .rax) (.imm 0x38), 4),
   (0x72, .ret, 1),
   (0x78, .bitcount .popcnt .q .rax (.reg .rdi), 5),
   (0x7d, .pop .rbx, 1),
   (0x7e, .ret, 1)]

set_option maxRecDepth 8000 in
/-- Every listed instruction is what `X86.Ext` decodes at its offset. -/
theorem listing_decodes :
    listing.all (fun e => decide (Silmaril.X86.Ext.decode ((code.drop e.1).take e.2.2) =
      some (e.2.1, e.2.2)) && decide (e.1 + e.2.2 ≤ code.length)) = true := by
  decide

set_option maxRecDepth 8000 in
/-- The CPUID at offset 8. -/
theorem code_cpuid : (code.drop 8).take 2 = [0x0F, 0xA2] := rfl

/-! ## The fallback's arithmetic -/

/-- One SWAR level: the lanes of `x` and of `x >>> s`, masked, added. -/
def lvl {w : Nat} (m : BitVec w) (s : Nat) (x : BitVec w) : BitVec w :=
  (x &&& m) + ((x >>> s) &&& m)

theorem toNat_append8 {n : Nat} (y : BitVec n) (z : BitVec 8) :
    (y ++ z).toNat = y.toNat * 256 + z.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, ← Nat.shiftLeft_eq]
  rw [← Nat.shiftLeft_add_eq_or_of_lt z.isLt, Nat.shiftLeft_eq]

theorem and_append8 {n : Nat} (y M : BitVec n) (z m : BitVec 8) :
    (y ++ z) &&& (M ++ m) = (y &&& M) ++ (z &&& m) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append]
  split <;> rfl

theorem shift_and_append8 {n : Nat} (y M : BitVec n) (z m : BitVec 8) (s : Nat)
    (hm : ∀ i, i < 8 → 8 ≤ s + i → m.getLsbD i = false) :
    ((y ++ z) >>> s) &&& (M ++ m) = ((y >>> s) &&& M) ++ ((z >>> s) &&& m) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 8
  · simp only [h]
    by_cases h2 : s + i < 8
    · simp [h2]
    · simp [h2, hm i h (by omega)]
  · simp only [h]
    have : s + i - 8 = s + (i - 8) := by omega
    simp [show ¬ (s + i < 8) by omega, this]

theorem add_append8 {n : Nat} (y u : BitVec n) (z w : BitVec 8) (h : z.toNat + w.toNat < 256) :
    (y ++ z) + (u ++ w) = (y + u) ++ (z + w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_append8, toNat_append8, toNat_append8, BitVec.toNat_add,
    BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt h]
  have hpow : 2 ^ (n + 8) = 2 ^ n * 256 := by rw [Nat.pow_add]
  rw [hpow, Nat.mul_comm (2 ^ n) 256, Nat.mod_mul]
  have hy := y.isLt; have hu := u.isLt
  have e1 : (y.toNat * 256 + z.toNat + (u.toNat * 256 + w.toNat)) % 256 = z.toNat + w.toNat := by
    omega
  have e2 : (y.toNat * 256 + z.toNat + (u.toNat * 256 + w.toNat)) / 256 = y.toNat + u.toNat := by
    omega
  rw [e1, e2]; ring

theorem lvl_append8 {n : Nat} (y M : BitVec n) (z m : BitVec 8) (s : Nat)
    (hm : ∀ i, i < 8 → 8 ≤ s + i → m.getLsbD i = false)
    (hz : (z &&& m).toNat + ((z >>> s) &&& m).toNat < 256) :
    lvl (M ++ m) s (y ++ z) = lvl M s y ++ lvl m s z := by
  unfold lvl
  rw [and_append8, shift_and_append8 y M z m s hm, add_append8 _ _ _ _ hz]

/-- A byte repeated `k` times. -/
def rep (b : BitVec 8) : (k : Nat) → BitVec (8 * k)
  | 0 => 0#0
  | k + 1 => rep b k ++ b

/-- The three SWAR levels on `k` bytes, and on one byte. -/
def lanes (k : Nat) (x : BitVec (8 * k)) : BitVec (8 * k) :=
  lvl (rep 0x0F k) 4 (lvl (rep 0x33 k) 2 (lvl (rep 0x55 k) 1 x))

def lanes8 (z : BitVec 8) : BitVec 8 := lvl 0x0F 4 (lvl 0x33 2 (lvl 0x55 1 z))

theorem lanes_succ (k : Nat) (y : BitVec (8 * k)) (z : BitVec 8) :
    lanes (k + 1) (y ++ z) = lanes k y ++ lanes8 z := by
  unfold lanes lanes8
  show lvl (rep 0x0F k ++ 0x0F) 4 (lvl (rep 0x33 k ++ 0x33) 2 (lvl (rep 0x55 k ++ 0x55) 1 (y ++ z))) = _
  rw [lvl_append8 _ _ _ _ _ (by decide) (by revert z; decide),
    lvl_append8 _ _ _ _ _ (by decide) (by generalize lvl 0x55#8 1 z = z; revert z; decide),
    lvl_append8 _ _ _ _ _ (by decide)
      (by generalize lvl 0x33#8 2 (lvl 0x55#8 1 z) = z; revert z; decide)]

theorem lanes8_eq (z : BitVec 8) : (lanes8 z).toNat = popcntN z := by
  revert z; decide

theorem popcntN_append8 {n : Nat} (y : BitVec n) (z : BitVec 8) :
    popcntN (y ++ z) = popcntN y + popcntN z := by
  unfold popcntN
  have hr : List.range (n + 8) = List.range 8 ++ (List.range n).map (8 + ·) := by
    rw [Nat.add_comm, List.range_add]
  rw [hr, List.countP_append, List.countP_map, Nat.add_comm]
  congr 1
  · apply List.countP_congr
    intro i hi
    simp [BitVec.getLsbD_append, Function.comp]
  · apply List.countP_congr
    intro i hi
    have : i < 8 := List.mem_range.mp hi
    simp [BitVec.getLsbD_append, this]

/-- The high bytes and the low byte. -/
def hi {k : Nat} (x : BitVec (8 * (k + 1))) : BitVec (8 * k) := x.extractLsb' 8 (8 * k)
def lo {k : Nat} (x : BitVec (8 * (k + 1))) : BitVec 8 := x.extractLsb' 0 8

theorem split8 {k : Nat} (x : BitVec (8 * (k + 1))) : x = hi x ++ lo x :=
  (Silmaril.X86.Features.extractLsb'_append_extractLsb' (n := 8 * k) (m := 8) x).symm

/-- The lane values, most significant byte first, as a base-256 number. -/
def laneVal : (k : Nat) → BitVec (8 * k) → Nat
  | 0, _ => 0
  | k + 1, x => laneVal k (hi x) * 256 + popcntN (lo x)

def popSum : (k : Nat) → BitVec (8 * k) → Nat
  | 0, _ => 0
  | k + 1, x => popSum k (hi x) + popcntN (lo x)

theorem lanes_toNat : ∀ (k : Nat) (x : BitVec (8 * k)), (lanes k x).toNat = laneVal k x
  | 0, x => by simp [laneVal, BitVec.toNat_of_zero_length]
  | k + 1, x => by
    rw [split8 x, lanes_succ, toNat_append8, lanes_toNat k, lanes8_eq, laneVal, ← split8 x]

theorem popcntN_bytes : ∀ (k : Nat) (x : BitVec (8 * k)), popcntN x = popSum k x
  | 0, x => by simp [popSum, popcntN]
  | k + 1, x => by
    rw [popSum, ← popcntN_bytes k, split8 x, popcntN_append8, ← split8 x]

theorem popcntN_le8 (z : BitVec 8) : popcntN z ≤ 8 := by revert z; decide


/-- Multiplying eight byte lanes (each at most 8) by `0x0101…01` puts their sum in the
top byte. -/
theorem mul_lanes (a b c d e f g h : Nat) (ha : a ≤ 8) (hb : b ≤ 8) (hc : c ≤ 8) (hd : d ≤ 8)
    (he : e ≤ 8) (hf : f ≤ 8) (hg : g ≤ 8) (hh : h ≤ 8) :
    ((((((((0 * 256 + h) * 256 + g) * 256 + f) * 256 + e) * 256 + d) * 256 + c) * 256 + b) *
      256 + a) * 72340172838076673 % 18446744073709551616 / 72057594037927936 =
      (0 + h + g + f + e + d + c + b + a) % 18446744073709551616 := by
  have key : ((((((((0 * 256 + h) * 256 + g) * 256 + f) * 256 + e) * 256 + d) * 256 + c) *
      256 + b) * 256 + a) * 72340172838076673 =
      (a + 256 * (a + b) + 65536 * (a + b + c) + 16777216 * (a + b + c + d) +
        4294967296 * (a + b + c + d + e) + 1099511627776 * (a + b + c + d + e + f) +
        281474976710656 * (a + b + c + d + e + f + g) +
        72057594037927936 * (a + b + c + d + e + f + g + h)) +
      18446744073709551616 * ((b + c + d + e + f + g + h) + 256 * (c + d + e + f + g + h) +
        65536 * (d + e + f + g + h) + 16777216 * (e + f + g + h) + 4294967296 * (f + g + h) +
        1099511627776 * (g + h) + 281474976710656 * h) := by
    ring
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega


/-- The fallback's three levels and its result, as the instructions compute them. -/
def swarA (x : Word) : Word :=
  (x &&& 0x5555555555555555#64) + ((x >>> 1) &&& 0x5555555555555555#64)

def swarB (x : Word) : Word :=
  (swarA x &&& 0x3333333333333333#64) + ((swarA x >>> 2) &&& 0x3333333333333333#64)

def swarC (x : Word) : Word :=
  (swarB x &&& 0x0F0F0F0F0F0F0F0F#64) + ((swarB x >>> 4) &&& 0x0F0F0F0F0F0F0F0F#64)

def swar (x : Word) : Word := (swarC x * 0x0101010101010101#64) >>> 56

theorem swar_eq_lanes (x : BitVec 64) : swar x = (lanes 8 x * 0x0101010101010101#64) >>> 56 := by
  have h1 : rep 0x55 8 = 0x5555555555555555#64 := by decide
  have h2 : rep 0x33 8 = 0x3333333333333333#64 := by decide
  have h3 : rep 0x0F 8 = 0x0F0F0F0F0F0F0F0F#64 := by decide
  unfold lanes lvl
  rw [h1, h2, h3]
  rfl

/-- **The SWAR popcount is the popcount** (kernel-checked: no native evaluation). -/
theorem swar_eq_popcnt (x : BitVec 64) : swar x = BitVec.ofNat 64 (popcntN x) := by
  rw [swar_eq_lanes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, lanes_toNat, BitVec.toNat_ofNat,
    popcntN_bytes 8]
  simp only [laneVal, popSum, Nat.shiftRight_eq_div_pow]
  have b0 := popcntN_le8 (lo (k := 7) x)
  have b1 := popcntN_le8 (lo (k := 6) (hi (k := 7) x))
  have b2 := popcntN_le8 (lo (k := 5) (hi (k := 6) (hi (k := 7) x)))
  have b3 := popcntN_le8 (lo (k := 4) (hi (k := 5) (hi (k := 6) (hi (k := 7) x))))
  have b4 := popcntN_le8 (lo (k := 3) (hi (k := 4) (hi (k := 5) (hi (k := 6) (hi (k := 7) x)))))
  have b5 := popcntN_le8
    (lo (k := 2) (hi (k := 3) (hi (k := 4) (hi (k := 5) (hi (k := 6) (hi (k := 7) x))))))
  have b6 := popcntN_le8 (lo (k := 1) (hi (k := 2)
    (hi (k := 3) (hi (k := 4) (hi (k := 5) (hi (k := 6) (hi (k := 7) x)))))))
  have b7 := popcntN_le8 (lo (k := 0) (hi (k := 1) (hi (k := 2)
    (hi (k := 3) (hi (k := 4) (hi (k := 5) (hi (k := 6) (hi (k := 7) x))))))))
  simp only [BitVec.toNat_ofNat, show (8 * 8 : Nat) = 64 from rfl, Nat.reducePow,
    Nat.reduceMod] at *
  exact mul_lanes _ _ _ _ _ _ _ _ b0 b1 b2 b3 b4 b5 b6 b7

end Silmaril.X86.Features.Cpuid.PopcountDispatch
