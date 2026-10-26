module

public import Silmaril.Crypto.SHA256
public import Silmaril.Crypto.SHA256.Kernel

/-!
# The `UInt32` and `BitVec 32` SHA-256 specifications agree (#829)

`Silmaril.Crypto.SHA256` (the canonical, list-based, `UInt32` FIPS 180-4
implementation that every consumer calls) and `Silmaril.Crypto.SHA256.Kernel` (the
register-level `BitVec 32` form used by the x86-64 work) were written independently:
separate `K` tables, separate initial hash values, separate `Ch`/`Maj`/`Σ`/`σ`
definitions, separate schedule and round code.  Nothing related them, so a fix or a
typo in one was silently not a fix or a typo in the other.

This module closes that gap.  `processBlock_eq_compressBlock` is proved for *all*
states and *all* blocks by induction on the schedule and on the round list; it is not
an unfolding of one definition into the other, and it fails if either side's `K`
table, round constant order, schedule indices or round function changes.

## Theorems
- `processBlock_eq_compressBlock`: for every state and every block,
  `SHA256.processBlock` equals `Kernel.compressBlock` read back through `UInt32`.
- `compress_eq_processBlock`: the sixteen-argument form of the same statement — the
  literal content of issue #829.
-/

@[expose] public section

namespace Silmaril.Crypto.SHA256

/-! ### Transfer between the two word representations -/

/-- The `BitVec 32` reading of a `UInt32` state. -/
def State.toBitVec (st : State) : Kernel.State :=
  (st.1.toBitVec, st.2.1.toBitVec, st.2.2.1.toBitVec, st.2.2.2.1.toBitVec,
   st.2.2.2.2.1.toBitVec, st.2.2.2.2.2.1.toBitVec, st.2.2.2.2.2.2.1.toBitVec,
   st.2.2.2.2.2.2.2.toBitVec)

/-- A `UInt32` state as an `InitHash`. -/
def State.toInitHash (st : State) : Kernel.InitHash :=
  ⟨st.1.toBitVec, st.2.1.toBitVec, st.2.2.1.toBitVec, st.2.2.2.1.toBitVec,
   st.2.2.2.2.1.toBitVec, st.2.2.2.2.2.1.toBitVec, st.2.2.2.2.2.2.1.toBitVec,
   st.2.2.2.2.2.2.2.toBitVec⟩

/-- An `InitHash` read back as a `UInt32` state. -/
def _root_.Silmaril.Crypto.SHA256.Kernel.InitHash.toState (H : Kernel.InitHash) : State :=
  (UInt32.ofBitVec H.h0, UInt32.ofBitVec H.h1, UInt32.ofBitVec H.h2, UInt32.ofBitVec H.h3,
   UInt32.ofBitVec H.h4, UInt32.ofBitVec H.h5, UInt32.ofBitVec H.h6, UInt32.ofBitVec H.h7)

/-! ### The §4.1.2 functions agree -/

theorem rotr_toBitVec (n : Nat) (x : UInt32) :
    (rotr n x).toBitVec = x.toBitVec.rotateRight (n % 32) := by
  simp only [rotr]
  apply BitVec.eq_of_toNat_eq
  show (UInt32.ofNat (x.toBitVec.rotateRight (n % 32)).toNat).toNat = _
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (x.toBitVec.rotateRight (n % 32)).isLt

theorem shr_toBitVec (n : Nat) (x : UInt32) : (shr n x).toBitVec = x.toBitVec >>> n := by
  simp only [shr]
  apply BitVec.eq_of_toNat_eq
  show (UInt32.ofNat (x.toNat >>> n)).toNat = _
  rw [UInt32.toNat_ofNat', BitVec.toNat_ushiftRight]
  have h : x.toNat >>> n ≤ x.toNat := Nat.shiftRight_le _ _
  have h2 : x.toNat < 2 ^ 32 := x.toBitVec.isLt
  have h3 : x.toBitVec.toNat = x.toNat := rfl
  rw [h3]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h h2)

theorem Ch_toBitVec (x y z : UInt32) :
    (Ch x y z).toBitVec = Kernel.Ch x.toBitVec y.toBitVec z.toBitVec := by
  simp [Ch, Kernel.Ch]

theorem Maj_toBitVec (x y z : UInt32) :
    (Maj x y z).toBitVec = Kernel.Maj x.toBitVec y.toBitVec z.toBitVec := by
  simp [Maj, Kernel.Maj]

theorem Sigma0_toBitVec (x : UInt32) : (Sigma0 x).toBitVec = Kernel.Sigma0 x.toBitVec := by
  simp [Sigma0, Kernel.Sigma0, rotr_toBitVec]

theorem Sigma1_toBitVec (x : UInt32) : (Sigma1 x).toBitVec = Kernel.Sigma1 x.toBitVec := by
  simp [Sigma1, Kernel.Sigma1, rotr_toBitVec]

theorem sigma0_toBitVec (x : UInt32) : (sigma0 x).toBitVec = Kernel.sigma0 x.toBitVec := by
  simp [sigma0, Kernel.sigma0, rotr_toBitVec, shr_toBitVec]

theorem sigma1_toBitVec (x : UInt32) : (sigma1 x).toBitVec = Kernel.sigma1 x.toBitVec := by
  simp [sigma1, Kernel.sigma1, rotr_toBitVec, shr_toBitVec]

/-! ### The §6.2.2 message schedules agree -/

theorem nextScheduleWord_toBitVec (acc : List UInt32) :
    (nextScheduleWord acc).toBitVec = Kernel.nextScheduleWord (acc.map UInt32.toBitVec) := by
  simp [nextScheduleWord, Kernel.nextScheduleWord, sigma0_toBitVec, sigma1_toBitVec]

theorem expandSchedule_toBitVec (n : Nat) (acc : List UInt32) :
    (expandSchedule n acc).map UInt32.toBitVec
      = Kernel.expandSchedule n (acc.map UInt32.toBitVec) := by
  induction n generalizing acc with
  | zero => rfl
  | succ m ih =>
    simp [expandSchedule, Kernel.expandSchedule, ih, nextScheduleWord_toBitVec]

theorem blockWords_toBitVec (M : List UInt32) :
    (blockWords M).map UInt32.toBitVec = Kernel.blockWords (M.map UInt32.toBitVec) := by
  simp [blockWords, Kernel.blockWords]

theorem messageSchedule_toBitVec (M : List UInt32) :
    (messageSchedule M).map UInt32.toBitVec
      = Kernel.messageSchedule (M.map UInt32.toBitVec) := by
  rw [messageSchedule, Kernel.messageSchedule, List.map_reverse, expandSchedule_toBitVec,
    List.map_reverse, blockWords_toBitVec]

/-- The two round-constant tables are the same sixty-four words. -/
theorem K_toBitVec : K.map UInt32.toBitVec = Kernel.Ks := by decide +kernel

/-! ### The §6.2.2 rounds agree -/

theorem compressRound_toBitVec (a b c d e f g h Kt Wt : UInt32) :
    State.toBitVec (compressRound a b c d e f g h Kt Wt)
      = Kernel.round a.toBitVec b.toBitVec c.toBitVec d.toBitVec e.toBitVec f.toBitVec
          g.toBitVec h.toBitVec Kt.toBitVec Wt.toBitVec := by
  simp [compressRound, Kernel.round, State.toBitVec, Ch_toBitVec, Maj_toBitVec,
    Sigma0_toBitVec, Sigma1_toBitVec]

theorem roundStep_toBitVec (st : State) (kw : UInt32 × UInt32) :
    State.toBitVec (roundStep st kw)
      = Kernel.roundStep (State.toBitVec st) (kw.1.toBitVec, kw.2.toBitVec) := by
  obtain ⟨Kt, Wt⟩ := kw
  obtain ⟨a, b, c, d, e, f, g, h⟩ := st
  simpa [roundStep, Kernel.roundStep, State.toBitVec] using
    compressRound_toBitVec a b c d e f g h Kt Wt

theorem foldl_roundStep_toBitVec (kw : List (UInt32 × UInt32)) (st : State) :
    State.toBitVec (kw.foldl roundStep st)
      = (kw.map (Prod.map UInt32.toBitVec UInt32.toBitVec)).foldl Kernel.roundStep
          (State.toBitVec st) := by
  induction kw generalizing st with
  | nil => rfl
  | cons p ps ih => simp [List.foldl_cons, ih, roundStep_toBitVec, Prod.map]

/-! ### The block compressions agree -/

/-- **Issue #829.**  For every eight-word state and every block, the canonical
`UInt32` block compression and the `BitVec 32` kernel compute the same eight words. -/
theorem processBlock_eq_compressBlock (st : State) (blk : List UInt32) :
    processBlock st blk
      = (Kernel.compressBlock (State.toInitHash st) (blk.map UInt32.toBitVec)).toState := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := st
  have hfold := foldl_roundStep_toBitVec (K.zip (messageSchedule blk)) (a, b, c, d, e, f, g, h)
  rw [← List.zip_map, K_toBitVec, messageSchedule_toBitVec] at hfold
  simp only [State.toBitVec] at hfold
  simp only [processBlock, Kernel.compressBlock, Kernel.rounds, Kernel.InitHash.state,
    State.toInitHash, Kernel.InitHash.toState]
  rw [← hfold]
  rfl

/-- **Issue #829**, in the sixteen-word form: `Kernel.compress` applied to the sixteen
words of a block gives the same eight words as `processBlock` on that block. -/
theorem compress_eq_processBlock
    (s0 s1 s2 s3 s4 s5 s6 s7 : UInt32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt32) :
    processBlock (s0, s1, s2, s3, s4, s5, s6, s7)
        [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]
      = (Kernel.compress
          ⟨s0.toBitVec, s1.toBitVec, s2.toBitVec, s3.toBitVec,
           s4.toBitVec, s5.toBitVec, s6.toBitVec, s7.toBitVec⟩
          b0.toBitVec b1.toBitVec b2.toBitVec b3.toBitVec
          b4.toBitVec b5.toBitVec b6.toBitVec b7.toBitVec
          b8.toBitVec b9.toBitVec b10.toBitVec b11.toBitVec
          b12.toBitVec b13.toBitVec b14.toBitVec b15.toBitVec).toState :=
  processBlock_eq_compressBlock _ _

end Silmaril.Crypto.SHA256
