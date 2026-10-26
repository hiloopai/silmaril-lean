module

public import Mathlib.Data.BitVec

/-!
# SHA-256 block compression on `BitVec 32` (FIPS 180-4 §6.2)

A register-level view of the SHA-256 block compression, used by the x86-64 work:
every word is a `BitVec 32` with wrapping addition, the round constants are named
`K0`…`K63` individually, and `roundsUnrolled` writes out all sixty-four rounds as a
straight-line sequence with the eight working variables `a`…`h` carried explicitly.

This is *not* a second SHA-256: `Silmaril.Crypto.SHA256.Equiv.processBlock_eq_compress`
proves that `compress` agrees with the canonical `Silmaril.Crypto.SHA256.processBlock`
for every initial state and every block, so the two cannot drift apart.  This module
covers §6.2.2 only — padding (§5.1.1), block parsing (§5.2.1), multi-block iteration
and digest serialisation (§6.2.3) live in `Silmaril.Crypto.SHA256`.

## Theorems
- `roundsUnrolled_eq_rounds`: the straight-line 64-round form equals the `List.foldl`
  form (a definitional restructuring; it is what lets the equivalence proof in
  `Equiv.lean` reason about the rounds by induction).
- `compress_abc`: the FIPS 180-4 §B.1 one-block test vector, checked by the kernel.

## References
* FIPS PUB 180-4, August 2015.
-/

@[expose] public section

namespace Silmaril.Crypto.SHA256.Kernel

abbrev Word := BitVec 32

/-- The eight working variables `a`–`h` (§6.2.2). -/
abbrev State := Word × Word × Word × Word × Word × Word × Word × Word

/-! ### Functions (§4.1.2) -/

def Ch (x y z : Word) : Word := (x &&& y) ^^^ ((~~~x) &&& z)

def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def Sigma0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

def Sigma1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

def sigma0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

def sigma1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-! ### Constants (§4.2.2) -/

def K0  : Word := 0x428a2f98#32
def K1  : Word := 0x71374491#32
def K2  : Word := 0xb5c0fbcf#32
def K3  : Word := 0xe9b5dba5#32
def K4  : Word := 0x3956c25b#32
def K5  : Word := 0x59f111f1#32
def K6  : Word := 0x923f82a4#32
def K7  : Word := 0xab1c5ed5#32
def K8  : Word := 0xd807aa98#32
def K9  : Word := 0x12835b01#32
def K10 : Word := 0x243185be#32
def K11 : Word := 0x550c7dc3#32
def K12 : Word := 0x72be5d74#32
def K13 : Word := 0x80deb1fe#32
def K14 : Word := 0x9bdc06a7#32
def K15 : Word := 0xc19bf174#32
def K16 : Word := 0xe49b69c1#32
def K17 : Word := 0xefbe4786#32
def K18 : Word := 0x0fc19dc6#32
def K19 : Word := 0x240ca1cc#32
def K20 : Word := 0x2de92c6f#32
def K21 : Word := 0x4a7484aa#32
def K22 : Word := 0x5cb0a9dc#32
def K23 : Word := 0x76f988da#32
def K24 : Word := 0x983e5152#32
def K25 : Word := 0xa831c66d#32
def K26 : Word := 0xb00327c8#32
def K27 : Word := 0xbf597fc7#32
def K28 : Word := 0xc6e00bf3#32
def K29 : Word := 0xd5a79147#32
def K30 : Word := 0x06ca6351#32
def K31 : Word := 0x14292967#32
def K32 : Word := 0x27b70a85#32
def K33 : Word := 0x2e1b2138#32
def K34 : Word := 0x4d2c6dfc#32
def K35 : Word := 0x53380d13#32
def K36 : Word := 0x650a7354#32
def K37 : Word := 0x766a0abb#32
def K38 : Word := 0x81c2c92e#32
def K39 : Word := 0x92722c85#32
def K40 : Word := 0xa2bfe8a1#32
def K41 : Word := 0xa81a664b#32
def K42 : Word := 0xc24b8b70#32
def K43 : Word := 0xc76c51a3#32
def K44 : Word := 0xd192e819#32
def K45 : Word := 0xd6990624#32
def K46 : Word := 0xf40e3585#32
def K47 : Word := 0x106aa070#32
def K48 : Word := 0x19a4c116#32
def K49 : Word := 0x1e376c08#32
def K50 : Word := 0x2748774c#32
def K51 : Word := 0x34b0bcb5#32
def K52 : Word := 0x391c0cb3#32
def K53 : Word := 0x4ed8aa4a#32
def K54 : Word := 0x5b9cca4f#32
def K55 : Word := 0x682e6ff3#32
def K56 : Word := 0x748f82ee#32
def K57 : Word := 0x78a5636f#32
def K58 : Word := 0x84c87814#32
def K59 : Word := 0x8cc70208#32
def K60 : Word := 0x90befffa#32
def K61 : Word := 0xa4506ceb#32
def K62 : Word := 0xbef9a3f7#32
def K63 : Word := 0xc67178f2#32

/-- The round constants in order, `K t` for `t = 0 … 63`. -/
def Ks : List Word :=
  [K0, K1, K2, K3, K4, K5, K6, K7,
   K8, K9, K10, K11, K12, K13, K14, K15,
   K16, K17, K18, K19, K20, K21, K22, K23,
   K24, K25, K26, K27, K28, K29, K30, K31,
   K32, K33, K34, K35, K36, K37, K38, K39,
   K40, K41, K42, K43, K44, K45, K46, K47,
   K48, K49, K50, K51, K52, K53, K54, K55,
   K56, K57, K58, K59, K60, K61, K62, K63]

/-! ### Initial hash values (§5.3.3) -/

structure InitHash where
  h0 : Word := 0x6a09e667#32
  h1 : Word := 0xbb67ae85#32
  h2 : Word := 0x3c6ef372#32
  h3 : Word := 0xa54ff53a#32
  h4 : Word := 0x510e527f#32
  h5 : Word := 0x9b05688c#32
  h6 : Word := 0x1f83d9ab#32
  h7 : Word := 0x5be0cd19#32
  deriving BEq, DecidableEq, Repr

def initHash : InitHash := {}

/-- The eight words of an `InitHash` as a `State`. -/
def InitHash.state (H : InitHash) : State := (H.h0, H.h1, H.h2, H.h3, H.h4, H.h5, H.h6, H.h7)

/-! ### Message schedule (§6.2.2 step 1) -/

/-- A §5.2.1 block is exactly sixteen 32-bit words: short inputs are zero-extended,
over-long inputs truncated. -/
def blockWords (M : List Word) : List Word := (M ++ List.replicate 16 0).take 16

/-- One step of the schedule recurrence
`W t = σ₁ (W (t-2)) + W (t-7) + σ₀ (W (t-15)) + W (t-16)`,
where `acc` holds the words produced so far in reverse order, so `acc[i]` is `W (t-1-i)`. -/
def nextScheduleWord (acc : List Word) : Word :=
  sigma1 (acc.getD 1 0) + acc.getD 6 0 + sigma0 (acc.getD 14 0) + acc.getD 15 0

/-- Extend a reversed schedule by `n` further words. -/
def expandSchedule : Nat → List Word → List Word
  | 0, acc => acc
  | n + 1, acc => expandSchedule n (nextScheduleWord acc :: acc)

/-- The 64-word message schedule `W 0 … W 63` of a 512-bit block. -/
def messageSchedule (M : List Word) : List Word :=
  (expandSchedule 48 (blockWords M).reverse).reverse

/-! ### Round function (§6.2.2 steps 2–3) -/

def round (a b c d e f g h Kt Wt : Word) : State :=
  let T1 := h + Sigma1 e + Ch e f g + Kt + Wt
  let T2 := Sigma0 a + Maj a b c
  (T1 + T2, a, b, c, d + T1, e, f, g)

/-- One round, taking the pair `(K t, W t)`. -/
def roundStep (st : State) (kw : Word × Word) : State :=
  let (Kt, Wt) := kw
  let (a, b, c, d, e, f, g, h) := st
  round a b c d e f g h Kt Wt

/-- The sixty-four rounds driven by a schedule. -/
def rounds (st : State) (W : List Word) : State := (Ks.zip W).foldl roundStep st

/-- The sixty-four rounds written out as straight-line code, with the message
schedule already expanded into `w0 … w63`.  This is the register-level form the
x86-64 kernel is meant to implement: `a`–`h` are the eight live registers and each
line is one round. -/
def roundsUnrolled (a b c d e f g h : Word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
     w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47
     w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 w60 w61 w62 w63 : Word) : State :=
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K0 w0
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K1 w1
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K2 w2
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K3 w3
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K4 w4
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K5 w5
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K6 w6
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K7 w7
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K8 w8
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K9 w9
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K10 w10
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K11 w11
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K12 w12
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K13 w13
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K14 w14
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K15 w15
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K16 w16
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K17 w17
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K18 w18
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K19 w19
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K20 w20
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K21 w21
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K22 w22
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K23 w23
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K24 w24
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K25 w25
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K26 w26
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K27 w27
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K28 w28
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K29 w29
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K30 w30
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K31 w31
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K32 w32
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K33 w33
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K34 w34
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K35 w35
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K36 w36
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K37 w37
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K38 w38
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K39 w39
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K40 w40
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K41 w41
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K42 w42
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K43 w43
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K44 w44
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K45 w45
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K46 w46
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K47 w47
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K48 w48
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K49 w49
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K50 w50
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K51 w51
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K52 w52
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K53 w53
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K54 w54
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K55 w55
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K56 w56
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K57 w57
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K58 w58
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K59 w59
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K60 w60
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K61 w61
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K62 w62
  let (a, b, c, d, e, f, g, h) := round a b c d e f g h K63 w63
  (a, b, c, d, e, f, g, h)

/-- The straight-line form and the `List.foldl` form compute the same thing.  This is
a definitional restructuring (`rfl`), not an independent check of the round function;
its value is that it lets `Equiv.lean` reason about the rounds by induction while the
x86 work keeps the unrolled form. -/
theorem roundsUnrolled_eq_rounds (a b c d e f g h : Word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
     w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47
     w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 w60 w61 w62 w63 : Word) :
    roundsUnrolled a b c d e f g h
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
      w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47
      w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 w60 w61 w62 w63
      = rounds (a, b, c, d, e, f, g, h)
        [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
          w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23,
          w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35,
          w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47,
          w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59,
          w60, w61, w62, w63] := rfl

/-! ### Compression of one 512-bit block (§6.2) -/

/-- Compression of a block given as a list of sixteen big-endian words. -/
def compressBlock (H : InitHash) (M : List Word) : InitHash :=
  let (a, b, c, d, e, f, g, h) := rounds H.state (messageSchedule M)
  { h0 := a + H.h0, h1 := b + H.h1, h2 := c + H.h2, h3 := d + H.h3,
    h4 := e + H.h4, h5 := f + H.h5, h6 := g + H.h6, h7 := h + H.h7 }

/-- Compression of one 512-bit block, taking the sixteen message words
`M₀ … M₁₅` in big-endian order (§6.2.2). -/
def compress (H : InitHash)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Word) : InitHash :=
  compressBlock H [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15]

/-! ### Test vector (§B.1)

`"abc"` padded to one 512-bit block: `0x61626380`, thirteen zero words, then the
bit length `24 = 0x18`.  The expected digest is the one printed in FIPS 180-4 §B.1,
not a value read back out of this implementation. -/

def abc_msg0  : Word := 0x61626380#32
def abc_msg15 : Word := 0x00000018#32

def test_abc_hash : InitHash :=
  { h0 := 0xba7816bf#32
    h1 := 0x8f01cfea#32
    h2 := 0x414140de#32
    h3 := 0x5dae2223#32
    h4 := 0xb00361a3#32
    h5 := 0x96177a9c#32
    h6 := 0xb410ff61#32
    h7 := 0xf20015ad#32 }

theorem compress_abc :
    compress initHash abc_msg0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 abc_msg15 = test_abc_hash := by
  decide +kernel

end Silmaril.Crypto.SHA256.Kernel
