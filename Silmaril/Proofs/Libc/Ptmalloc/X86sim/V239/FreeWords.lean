module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.FreeFront
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.TcPut
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.FreeRep

/-!
# ptmalloc x86sim, glibc 2.39: the words `free`'s tcache path computes, from the model's numbers

The register and memory words of the machine runs (`free_front`, the put block) expressed by
the abstract chunk (`Chunk`: address `c`, size `s`) and tcache bin:

* `sz_bits`: the size word `s + f` (`f` the `PREV_INUSE` bit) has `IS_MMAPPED`, `NON_MAIN_ARENA`
  and bit 3 clear, and `csize` of it is `s`; `ftidx_ofNat`: the code's `csize2tidx` is the
  model's `Config.tidx`;
* `tcWalk_of`: a represented tcache bin is the list the double-free walk follows (`TcWalk`):
  so the walk of `e->key == tcache_key` (a client's payload may hold the key by chance) ends
  without meeting the freed chunk when the chunk is not parked;
* address arithmetic at a load base (`freeAt`, `intA_freeAt`) without kernel evaluation of
  `base + _` (x86sim finding 6).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Data
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.V239

/-- `__libc_free`'s address at load base `base`. -/
def freeAt (base : Nat) : Word := BitVec.ofNat 64 (base + 0xade30)

theorem freeAt_entry : pin239.entries.free = 0xade30 := rfl

theorem intA_freeAt (base : Nat) : intA (freeAt base) = intFreeAt base := by
  have : freeAt base = intFreeAt base + 0x2be0#64 := by
    unfold freeAt intFreeAt
    rw [ofNat_add_lit (c := 0xade30) rfl]
  rw [this, intA, BitVec.add_sub_cancel]

/-! ## Words -/

theorem w_sub {a k : Nat} (hk : k ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 k = BitVec.ofNat 64 (a - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem and_low (x k : Nat) (hk : k < 16) : x &&& k = (x % 16) &&& k := by
  have hk' : k = (2 ^ 4 - 1) &&& k := by
    rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hk]
  conv_lhs => rw [hk']
  rw [← Nat.and_assoc, Nat.and_two_pow_sub_one_eq_mod]

-- copied from Silmaril.Proofs.Libc.Ptmalloc.E2e.V239 (`nat_and_mask16`), at 8
/-- `x &&& (2^64 - 8)` clears the low three bits. -/
theorem nat_and_mask8 (x : Nat) (hx : x < 2 ^ 64) : x &&& (2 ^ 64 - 8) = x / 8 * 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have h8 : (2 ^ 64 - 8 : Nat) = (2 ^ 61 - 1) * 2 ^ 3 := by decide
  have h8' : x / 8 * 8 = x / 2 ^ 3 * 2 ^ 3 := rfl
  rw [h8, h8', Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hi : 3 ≤ i
  · simp only [hi, decide_true, Bool.true_and]
    rw [Nat.sub_add_cancel hi]
    by_cases h64 : i < 64
    · simp [show i - 3 < 61 by omega]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]
  · simp [hi]

/-- **The size word of a chunk** (`s` a multiple of 16, `f` the `PREV_INUSE` bit): not
`IS_MMAPPED`, not `NON_MAIN_ARENA`, bit 3 clear, and `csize` of it is `s`. -/
theorem sz_bits {s f : Nat} (hs : s % 16 = 0) (hf : f = 0 ∨ f = 1) (hv : s + f < 2 ^ 64) :
    (BitVec.ofNat 64 (s + f)).setWidth 8 &&& 2#8 = 0 ∧ (BitVec.ofNat 64 (s + f)).setWidth 8 &&& 4#8 = 0 ∧
      (BitVec.ofNat 64 (s + f)).setWidth 32 &&& 8#32 = 0 ∧
      csize (BitVec.ofNat 64 (s + f)) = BitVec.ofNat 64 s := by
  have h16 : (s + f) % 16 = f := by rcases hf with rfl | rfl <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (2 : Nat) % 2 ^ 8 = 2 by rfl, and_low _ 2 (by omega),
      show (s + f) % 2 ^ 64 % 2 ^ 8 % 16 = f by omega]
    rcases hf with rfl | rfl <;> rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (4 : Nat) % 2 ^ 8 = 4 by rfl, and_low _ 4 (by omega),
      show (s + f) % 2 ^ 64 % 2 ^ 8 % 16 = f by omega]
    rcases hf with rfl | rfl <;> rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (8 : Nat) % 2 ^ 32 = 8 by rfl, and_low _ 8 (by omega),
      show (s + f) % 2 ^ 64 % 2 ^ 32 % 16 = f by omega]
    rcases hf with rfl | rfl <;> rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [csize, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (0xfffffffffffffff8 : Nat) % 2 ^ 64 = 2 ^ 64 - 8 by rfl, Nat.mod_eq_of_lt hv,
      nat_and_mask8 _ hv, Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega)]
    omega

/-- **The code's `csize2tidx` is the model's** (`(s - 17) >> 4`). -/
theorem ftidx_ofNat {s : Nat} (h32 : 32 ≤ s) (hs : s < 2 ^ 64) :
    ftidx (BitVec.ofNat 64 s) = BitVec.ofNat 64 (pin239.config.tidx s) := by
  have ht : pin239.config.tidx s = (s - 32 + 16 - 1) / 16 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [ftidx, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, ht]
  omega

theorem count_ofNat {n : Nat} (h : n < 2 ^ 16) :
    (((BitVec.ofNat 64 n).setWidth 16).setWidth 32).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem ext32_ofNat {n : Nat} (h : n < 2 ^ 32) :
    ((((BitVec.ofNat 64 n).setWidth 32).setWidth 64).setWidth 32).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem protect_word {x n : Nat} (hx : x < 2 ^ 64) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (x / 4096 ^^^ n) = (BitVec.ofNat 64 x >>> 12) ^^^ BitVec.ofNat 64 n := by
  have h1 : x / 4096 < 2 ^ 64 := by omega
  have h2 : x / 4096 ^^^ n < 2 ^ 64 := Nat.xor_lt_two_pow h1 hn
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h2, Nat.shiftRight_eq_div_pow]

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun e => h (by
  have := congrArg BitVec.toNat e
  rwa [toNat_ofNat_lt ha, toNat_ofNat_lt hb] at this)

theorem getD_map_ofNat (l : List Nat) (j : Nat) :
    (l.map (BitVec.ofNat 64)).getD j 0 = BitVec.ofNat 64 (l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

/-! ## The double-free walk -/

/-- **A represented tcache bin is the list the double-free walk follows** (`TcWalk`), from its
head, for any `e` that is no entry's payload. -/
theorem tcWalk_of {C : Config} {L : Layout} {key : Nat} {tc : TcacheSt} {i e : Nat} {m : Memory}
    (hS : TcShape C L) (hw : TcacheWF C tc) (hi : i < C.tcacheBins)
    (hT : (tcacheFrag C L key tc).Holds (memView m)) (he : ∀ c ∈ tc.bins i, c.1 + C.hdr ≠ e)
    (he64 : e < 2 ^ 64) :
    TcWalk m (BitVec.ofNat 64 (((tc.bins i).map (·.1 + C.hdr)).headD 0)) (BitVec.ofNat 64 e)
      (BitVec.ofNat 64 C.tcacheCount) (((tc.bins i).map (·.1 + C.hdr)).map (BitVec.ofNat 64)) := by
  have hok := hS.ok
  have hhdr : C.hdr = 16 := by simp [Config.hdr, hok.sizeSz]
  have hcnt := hok.tcache.2.2.2
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · cases (tc.bins i).map (·.1 + C.hdr) <;> rfl
  · simp only [List.length_map]
    rw [toNat_ofNat_lt (by omega)]
    exact (hw.nodup i).2
  · simp only [List.length_map] at hj
    have hm := mem_tcacheFrag_linkAt (L := L) (key := key) hi hj
    simp only [Nat.add_zero] at hm
    obtain ⟨lL, bL, -, -, vL⟩ := cell_load (hT _ hm) (by simp)
    have hc := List.getElem_mem hj
    have hps : ((tc.bins i).map (·.1 + C.hdr)).getD j 0 = (tc.bins i)[j].1 + C.hdr := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hps] at lL bL vL
    simp only [addressLimit] at bL
    have hnn := hw.nonNull i _ hc
    have ha16 : (tc.bins i)[j].1 % 16 = 0 := by rw [← hok.align]; exact hnn.2
    have hx : (tc.bins i)[j].1 + C.hdr < 2 ^ 64 := by omega
    have hprot : C.protect ((tc.bins i)[j].1 + C.hdr) (((tc.bins i).map (·.1 + C.hdr)).getD (j + 1) 0) =
        ((tc.bins i)[j].1 + C.hdr) / 4096 ^^^ ((tc.bins i).map (·.1 + C.hdr)).getD (j + 1) 0 := by
      simp [Config.protect, hS.safe]
    rw [hprot] at lL vL
    have hn : ((tc.bins i).map (·.1 + C.hdr)).getD (j + 1) 0 < 2 ^ 64 := by
      have h1 : ((tc.bins i)[j].1 + C.hdr) / 4096 < 2 ^ 64 := by omega
      have vL' : ((tc.bins i)[j].1 + C.hdr) / 4096 ^^^ ((tc.bins i).map (·.1 + C.hdr)).getD (j + 1) 0 <
          2 ^ 64 := vL
      have := Nat.xor_lt_two_pow h1 vL'
      rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
    rw [getD_map_ofNat, getD_map_ofNat, hps]
    refine ⟨fun h0 => ofNat_ne (b := 0) hx (by decide) (by rw [hhdr]; omega) h0, aligned_ofNat (by rw [hhdr]; omega),
      ofNat_ne hx he64 (he _ hc), ?_⟩
    rw [← hps, ← protect_word (by rw [hps]; exact hx) hn, hps]
    exact lL

end Silmaril.Libc.Ptmalloc.X86sim.V239
