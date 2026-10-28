module

public import Silmaril.X86.TVIR.Core
public import Silmaril.X86.Stencils.HexLoop
public import Silmaril.Apps.Sha256sum.IOLayer.Write

/-! # `output_file` of `sha256sum-min` (stdin record) as a TVIR program, and its correctness

Status: **VERIFIED** (no `sorry`, standard axioms only).

The record `hex(digest) ++ "  -\n"` of GNU `sha256sum` on standard input
(`output_file("-", binary = 0, bin, tagged = 0, '\n')`, inlined in `cmain`) as a program of
the translation-validation IR `X86.TVIR`:

```
do {                                   -- 0x4045ae … 0x4045ac
  b  := mem[p]                         -- movzbl (%rbx),%r15d
  hi := mem[hexd + ((b >> 4) & 15)]    -- shr $4,%dl; and $0xf,%edx; movzbl hexd(%rdx),%ebp
  putc hi                              -- inlined out_putc  (0x4045c2 → 0x404578)
  lo := mem[hexd + (b & 15)]           -- and $0xf,%r15d; movzbl hexd(%r15),%r15d
  putc lo                              -- inlined out_putc  (0x404584 → 0x4045a5)
  p  := p + 1                          -- add $1,%rbx
} while (p != e)                       -- cmp %rbx,%r14; je
putc ' '; putc ' '; putc '-'; putc '\n'
```

The output layer is GNU's buffered `out_putc` (`Buffered`: the buffer `(putcBuf 4096 buf c).2`
of `Sys.IOLayer`, and the stream emitted so far); the read-only memory `roMem d bin` holds the
digest `d` at `bin` and the table `"0123456789abcdef"` at `hexd = 0x4072c0`.

`format_correct`: from `p = bin`, `e = bin + 32` and nothing emitted, the program terminates
having emitted exactly `hexLower d ++ "  -\n"`, the stdin record. The proof is the `wp` VC
generator of `TVIR` with the loop invariant `emitted = hexLower (d.take k)`, `p = bin + k`;
the generated VCs are closed by `simp` and `omega` (`body_wp`, `loop_vcs`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Apps.Sha256sum.TV

open Silmaril.X86.TVIR
open Silmaril.X86.Stencils.HexLoop (hexTable hexPair hexLower_take_succ hexTable_getD)

/-- GNU's buffered output layer: the buffer `obuf[0, olen)` (capacity 4096, flushed when full
and after a newline, `Sys.IOLayer.putcBuf`) and the bytes emitted so far. -/
def Buffered : IOLayer where
  S := Bytes × Bytes
  putc s c := ((Sys.IOLayer.putcBuf 4096 s.1 c).2, s.2 ++ [c])
  out s := s.2
  out_putc _ _ := rfl

/-- The variables of the record program: the digest pointer and its end, the current byte,
the two digits. -/
inductive HV where
  | p | e | b | hi | lo
  deriving DecidableEq

/-- The address of the `hexd` table. -/
def hexd : Nat := 0x4072c0

/-- The read-only memory: the digest `d` at `bin`, the hex table at `hexd`. -/
def roMem (d : Bytes) (bin : Nat) (a : Nat) : UInt8 :=
  if bin ≤ a ∧ a < bin + 32 then d.getD (a - bin) 0
  else if hexd ≤ a ∧ a < hexd + 16 then hexTable.getD (a - hexd) 0 else 0

/-- IR states of the record program. -/
abbrev HSt := Silmaril.X86.TVIR.St HV Buffered

/-- The loop body. -/
def body : Stmt HV Buffered :=
  .seq (.set .b (.ld8 (.var .p))) <|
  .seq (.set .hi (.ld8 (.add (.lit (BitVec.ofNat 64 hexd)) (.band (.shr (.var .b) 4) (.lit 15))))) <|
  .seq (.putc (.var .hi)) <|
  .seq (.set .lo (.ld8 (.add (.lit (BitVec.ofNat 64 hexd)) (.band (.var .b) (.lit 15))))) <|
  .seq (.putc (.var .lo)) <|
  .set .p (.add (.var .p) (.lit 1))

/-- The loop invariant (after `k` bytes, `1 ≤ k ≤ 32`). -/
def Inv (d : Bytes) (bin : Nat) (out0 : Bytes) (τ : HSt) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ 32 ∧ τ.env .p = BitVec.ofNat 64 (bin + k) ∧
    τ.env .e = BitVec.ofNat 64 (bin + 32) ∧ τ.io.2 = out0 ++ hexLower (d.take k)

/-- The loop variant: the bytes left. -/
def variant (τ : HSt) : Nat := (τ.env .e - τ.env .p).toNat

/-- The hex loop. -/
def hexLoop (d : Bytes) (bin : Nat) (out0 : Bytes) : Stmt HV Buffered :=
  .loop (Inv d bin out0) variant body (.ne (.var .p) (.var .e))

/-- The separator, the file name `-` and the delimiter. -/
def suffix : Stmt HV Buffered :=
  .seq (.putc (.lit 0x20)) <| .seq (.putc (.lit 0x20)) <| .seq (.putc (.lit 0x2d)) <|
    .putc (.lit 0x0a)

/-- **The record program.** -/
def format (d : Bytes) (bin : Nat) (out0 : Bytes) : Stmt HV Buffered :=
  .seq (hexLoop d bin out0) suffix

/-! ## The verification conditions -/

theorem byteOf_zext (c : UInt8) : byteOf (zext c) = c := by
  simp only [byteOf, zext]
  apply UInt8.toBitVec_inj.mp
  ext i hi; simp

theorem toNat_zext (c : UInt8) : (zext c).toNat = c.toNat := by
  rw [zext, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, Nat.mod_eq_of_lt (by have := c.toNat_lt; omega)]

theorem zext_shr_and (c : UInt8) : ((zext c >>> 4) &&& (15 : BitVec 64)).toNat = c.toNat / 16 := by
  have := c.toNat_lt
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, toNat_zext, Nat.shiftRight_eq_div_pow,
    show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (by omega)]

theorem zext_and (c : UInt8) : (zext c &&& (15 : BitVec 64)).toNat = c.toNat % 16 := by
  rw [BitVec.toNat_and, toNat_zext, show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- A table lookup of the read-only memory. -/
theorem roMem_table (d : Bytes) {bin : Nat} (hbin : hexd + 16 ≤ bin) {k : Nat} (hk : k < 16) :
    roMem d bin (hexd + k) = hexDigit k := by
  simp only [roMem]
  rw [ite_eq_right_of_eq_false _ _ (by simp; omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
  exact hexTable_getD k hk

/-- A digest read of the read-only memory. -/
theorem roMem_digest {d : Bytes} {bin : Nat} {k : Nat} (hk : k < 32) (hd : d.length = 32) :
    roMem d bin (bin + k) = d[k]'(by omega) := by
  simp only [roMem]
  rw [ite_eq_left (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem table_addr (x : BitVec 64) (hx : x.toNat < 16) :
    (BitVec.ofNat 64 hexd + x).toNat = hexd + x.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [hexd]; omega

/-- **The body VC**: one iteration from `p = bin + k` emits `hexPair d[k]` and moves to
`p = bin + k + 1`. -/
theorem body_wp {d : Bytes} {bin : Nat} (hd : d.length = 32) (hbin : hexd + 16 ≤ bin)
    (hfit : bin + 32 < 2 ^ 64) {k : Nat} (hk : k < 32) (Q : HSt → Prop)
    (τ : HSt) (hp : τ.env .p = BitVec.ofNat 64 (bin + k))
    (hq : ∀ τ' : HSt, τ'.env .p = BitVec.ofNat 64 (bin + (k + 1)) →
      τ'.env .e = τ.env .e → τ'.io.2 = τ.io.2 ++ hexPair (d[k]'(by omega)) → Q τ') :
    wp (roMem d bin) body Q τ := by
  simp only [body, wp, Exp.eval, St.set, St.putc, Function.update_self, ne_eq, reduceCtorEq,
    not_false_eq_true, Function.update_of_ne, hp]
  refine hq _ ?_ ?_ ?_
  · simp only [Function.update_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne]
  · simp only [Buffered, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bin + k < 2 ^ 64 by omega)]
    have hdk := roMem_digest (bin := bin) hk hd
    have := (d[k]'(by omega)).toNat_lt
    rw [hdk, byteOf_zext, byteOf_zext, table_addr _ (by rw [zext_shr_and]; omega),
      table_addr _ (by rw [zext_and]; omega), zext_shr_and, zext_and,
      roMem_table d hbin (by omega), roMem_table d hbin (by omega)]
    simp [hexPair]

/-- **Correctness of the record program** (the `wp` VCs of `format`): from `p = bin`,
`e = bin + 32` and `out0` emitted, it terminates having emitted `out0 ++ hexLower d ++
"  -\n"`. -/
theorem format_correct {d : Bytes} {bin : Nat} (hd : d.length = 32) (hbin : hexd + 16 ≤ bin)
    (hfit : bin + 32 < 2 ^ 64) (out0 : Bytes) (σ : HSt)
    (hp : σ.env .p = BitVec.ofNat 64 bin) (he : σ.env .e = BitVec.ofNat 64 (bin + 32))
    (ho : σ.io.2 = out0) :
    wp (roMem d bin) (format d bin out0)
      (fun σ' => σ'.io.2 = out0 ++ hexLower d ++ lit "  -\n") σ := by
  simp only [format, hexLoop, wp]
  refine ⟨?_, ?_, ?_⟩
  · -- the first iteration establishes the invariant
    refine body_wp hd hbin hfit (k := 0) (by omega) _ σ (by simpa using hp) ?_
    intro τ' hp' he' ho'
    refine ⟨1, le_refl _, by omega, hp', he'.trans he, ?_⟩
    rw [ho', ho, show d.take 1 = [d[0]'(by omega)] by
      rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl]
    simp [hexLower, hexPair]
  · -- the invariant is kept, and the variant decreases
    rintro τ ⟨k, hk1, hk32, hp, he, ho⟩ hc
    have hk : k < 32 := by
      rcases Nat.lt_or_ge k 32 with h | h
      · exact h
      · have : k = 32 := by omega
        subst this; simp [BExp.eval, Exp.eval, hp, he] at hc
    refine body_wp hd hbin hfit hk _ τ hp ?_
    intro τ' hp' he' ho'
    refine ⟨⟨k + 1, by omega, by omega, hp', he'.trans he, ?_⟩, ?_⟩
    · rw [ho', ho, hexLower_take_succ d k (by omega), List.append_assoc]
    · simp only [variant, hp', he', he, hp, BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
  · -- at the exit, the suffix finishes the record
    rintro τ ⟨k, hk1, hk32, hp, he, ho⟩ hc
    have : k = 32 := by
      by_contra hne
      simp only [BExp.eval, Exp.eval, hp, he, bne_eq_false_iff_eq] at hc
      have := congrArg BitVec.toNat hc
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
    subst this
    simp only [suffix, wp, Exp.eval, St.putc, Buffered, ho, ← hd, List.take_length]
    simp [byteOf, lit]

end Silmaril.Apps.Sha256sum.TV
