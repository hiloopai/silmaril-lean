module

public import Silmaril.Proofs.Parse.ByteParse.Basic

/-!
# LEB128 and little-endian numbers: soundness and completeness

The tail-recursive readers `uN N`/`sN N` accept exactly silmaril's Wasm grammar
`UN N`/`SN N` (`Silmaril.Wasm.Binary`), including its length bound and the
range check on the last byte; non-minimal ("padded") encodings within the
length bound are accepted, as the Wasm specification requires. `le n` reads
`n` little-endian bytes (`Spec.le`, silmaril's `littleEndian`).
-/

@[expose] public section

namespace Silmaril.Parse.ByteParse

open Silmaril.Wasm.Binary (UN SN littleEndian)

/-- A non-empty segment: its first byte and the rest. -/
theorem seg_head {bs : ByteArray} {i : Nat} {b : UInt8} {l : Bytes}
    (hs : i + (b :: l).length ≤ bs.size) (hseg : seg bs i (i + (b :: l).length) = b :: l) :
    ∃ hsz : i < bs.size, bs[i] = b ∧ seg bs (i + 1) (i + 1 + l.length) = l := by
  have hsz : i < bs.size := by simp only [List.length_cons] at hs; omega
  have hc : seg bs i (i + (b :: l).length) = bs[i] :: seg bs (i + 1) (i + 1 + l.length) := by
    rw [seg_cons bs hsz (by simp), List.length_cons, show i + (l.length + 1) = i + 1 + l.length by omega]
  have hc' : bs[i] :: seg bs (i + 1) (i + 1 + l.length) = b :: l := hc.symm.trans hseg
  exact ⟨hsz, List.head_eq_of_cons_eq hc', List.tail_eq_of_cons_eq hc'⟩

/-- Inversion of a successful `uAux` step (the only `split at` of the LEB proofs). -/
theorem uAux_ok {budget shift acc : Nat} {bs : ByteArray} {st i v j : Nat}
    (h : uAux budget shift acc bs st i = .ok v j) :
    ∃ hsz : i < bs.size, i < st ∧
      ((bs[i].toNat < 128 ∧ bs[i].toNat < 2 ^ budget ∧ v = acc + 2 ^ shift * bs[i].toNat ∧
          j = i + 1) ∨
       (128 ≤ bs[i].toNat ∧ 7 < budget ∧
          uAux (budget - 7) (shift + 7) (acc + 2 ^ shift * (bs[i].toNat - 128)) bs st (i + 1) =
            .ok v j)) := by
  rw [uAux] at h
  split at h
  · split at h
    · split at h
      · split at h
        · cases h; exact ⟨‹_›, ‹_›, .inl ⟨‹_›, ‹_›, rfl, rfl⟩⟩
        · cases h
      · split at h
        · exact ⟨‹_›, ‹_›, .inr ⟨by omega, ‹_›, h⟩⟩
        · cases h
    · cases h
  · cases h

theorem two_pow_seven : (2 : Nat) ^ 7 = 128 := rfl

/-- One continuation step of `uAux`. -/
theorem uAux_cont {budget shift acc : Nat} {bs : ByteArray} {st i : Nat} (hst : i < st)
    (hsz : i < bs.size) (hb : 128 ≤ bs[i].toNat) (hN : 7 < budget) :
    uAux budget shift acc bs st i =
      uAux (budget - 7) (shift + 7) (acc + 2 ^ shift * (bs[i].toNat - 128)) bs st (i + 1) := by
  rw [uAux]
  simp only [hst, hsz, show ¬ bs[i].toNat < 128 by omega, hN, ↓reduceDIte, ↓reduceIte]

/-- One continuation step of `sAux`. -/
theorem sAux_cont {budget shift : Nat} {acc : Int} {bs : ByteArray} {st i : Nat} (hst : i < st)
    (hsz : i < bs.size) (hb : 128 ≤ bs[i].toNat) (hN : 7 < budget) :
    sAux budget shift acc bs st i =
      sAux (budget - 7) (shift + 7) (acc + 2 ^ shift * ((bs[i].toNat : Int) - 2 ^ 7)) bs st (i + 1) := by
  rw [sAux]
  simp only [hst, hsz, show ¬ bs[i].toNat < 128 by omega, show ¬ bs[i].toNat < 64 by omega, hN,
    ↓reduceDIte, ↓reduceIte]

theorem uAux_sound (budget : Nat) : ∀ (shift acc : Nat) {bs : ByteArray} {st i v j : Nat},
    i ≤ st → st ≤ bs.size → uAux budget shift acc bs st i = .ok v j →
    i ≤ j ∧ j ≤ st ∧ ∃ m, v = acc + 2 ^ shift * m ∧ UN budget (seg bs i j) m := by
  induction budget using Nat.strong_induction_on with
  | _ budget ih =>
  intro shift acc bs st i v j hi hs h
  obtain ⟨hsz, hst, hcase⟩ := uAux_ok h
  have hc : seg bs i (i + 1) = [bs[i]] := by rw [seg_cons bs hsz (by omega), seg_self]
  rcases hcase with ⟨hb, hN, hv, hj⟩ | ⟨hb, hN, hrec⟩
  · have hu : UN budget [bs[i]] bs[i].toNat := UN.byte _ (by rw [two_pow_seven]; exact hb) hN
    exact ⟨by omega, by omega, _, hv, by rw [hj, hc]; exact hu⟩
  · show i ≤ j ∧ j ≤ st ∧ ∃ m, v = acc + 2 ^ shift * m ∧ UN budget (seg bs i j) m
    obtain ⟨h1, h2, m, hv, hu⟩ : i + 1 ≤ j ∧ j ≤ st ∧ ∃ m,
        v = acc + 2 ^ shift * (bs[i].toNat - 128) + 2 ^ (shift + 7) * m ∧
          UN (budget - 7) (seg bs (i + 1) j) m :=
      ih (budget - 7) (by omega) (shift + 7) (acc + 2 ^ shift * (bs[i].toNat - 128))
        (Nat.succ_le_of_lt hst) hs hrec
    have hval : v = acc + 2 ^ shift * (2 ^ 7 * m + (bs[i].toNat - 2 ^ 7)) := by
      rw [hv, pow_add, two_pow_seven]; ring
    have hu' : UN budget (bs[i] :: seg bs (i + 1) j) (2 ^ 7 * m + (bs[i].toNat - 2 ^ 7)) :=
      UN.cont _ (by rw [two_pow_seven]; exact hb) hN hu
    exact ⟨by omega, h2, _, hval, by rw [seg_cons bs hsz (by omega)]; exact hu'⟩

theorem uAux_complete {budget : Nat} {l : Bytes} {m : Nat} (hu : UN budget l m) :
    ∀ (shift acc : Nat) {bs : ByteArray} {st i : Nat}, i + l.length ≤ st → st ≤ bs.size →
      seg bs i (i + l.length) = l → uAux budget shift acc bs st i = .ok (acc + 2 ^ shift * m) (i + l.length) := by
  induction hu with
  | byte n h1 h2 =>
    intro shift acc bs st i hl hs hseg
    obtain ⟨hsz, hb, -⟩ := seg_head (l := []) (by omega) hseg
    have hst : i < st := by simp only [List.length_singleton] at hl; omega
    have hn : n.toNat < 128 := by rw [← two_pow_seven]; exact h1
    rw [uAux]
    simp [hst, hsz, hb, hn, h2]
  | @cont N n b m h1 h2 rest ih =>
    intro shift acc bs st i hl hs hseg
    obtain ⟨hsz, hb, hr⟩ := seg_head (by omega) hseg
    have hst : i + 1 + b.length ≤ st := by simp only [List.length_cons] at hl; omega
    have hrec := ih (shift + 7) (acc + 2 ^ shift * (n.toNat - 128)) hst hs hr
    rw [uAux_cont (by omega) hsz (hb ▸ two_pow_seven ▸ h1) h2, hb, hrec]
    exact congrArg₂ (fun a b => Res.ok a b) (by rw [pow_add, two_pow_seven]; ring)
      (by simp only [List.length_cons]; omega)

theorem sound_uN (N : Nat) : Sound (UN N) (uN N) := by
  intro bs st i v j hi hs h
  obtain ⟨h1, h2, m, hv, hu⟩ := uAux_sound N 0 0 hi hs h
  have hv' : v = m := by simpa only [pow_zero, one_mul, zero_add] using hv
  exact ⟨h1, h2, hv' ▸ hu⟩

theorem complete_uN (N : Nat) : Complete (UN N) (uN N) := by
  intro l v bs st i hu hl hs hseg
  have := uAux_complete hu 0 0 hl hs hseg
  simpa [uN] using this

/-- Inversion of a successful `sAux` step. -/
theorem sAux_ok {budget shift : Nat} {acc : Int} {bs : ByteArray} {st i j : Nat} {v : Int}
    (h : sAux budget shift acc bs st i = .ok v j) :
    ∃ hsz : i < bs.size, i < st ∧
      ((bs[i].toNat < 64 ∧ bs[i].toNat < 2 ^ (budget - 1) ∧
          v = acc + 2 ^ shift * (bs[i].toNat : Int) ∧ j = i + 1) ∨
       (64 ≤ bs[i].toNat ∧ bs[i].toNat < 128 ∧ (2 : Int) ^ 7 - 2 ^ (budget - 1) ≤ bs[i].toNat ∧
          v = acc + 2 ^ shift * ((bs[i].toNat : Int) - 2 ^ 7) ∧ j = i + 1) ∨
       (128 ≤ bs[i].toNat ∧ 7 < budget ∧
          sAux (budget - 7) (shift + 7) (acc + 2 ^ shift * ((bs[i].toNat : Int) - 2 ^ 7)) bs st
            (i + 1) = .ok v j)) := by
  rw [sAux] at h
  split at h
  · split at h
    · split at h
      · split at h
        · cases h; exact ⟨‹_›, ‹_›, .inl ⟨‹_›, ‹_›, rfl, rfl⟩⟩
        · cases h
      · split at h
        · split at h
          · cases h; exact ⟨‹_›, ‹_›, .inr (.inl ⟨by omega, ‹_›, ‹_›, rfl, rfl⟩)⟩
          · cases h
        · split at h
          · exact ⟨‹_›, ‹_›, .inr (.inr ⟨by omega, ‹_›, h⟩)⟩
          · cases h
    · cases h
  · cases h

theorem sAux_sound (budget : Nat) : ∀ (shift : Nat) (acc : Int) {bs : ByteArray} {st i j : Nat}
    {v : Int}, i ≤ st → st ≤ bs.size → sAux budget shift acc bs st i = .ok v j →
    i ≤ j ∧ j ≤ st ∧ ∃ m, v = acc + 2 ^ shift * m ∧ SN budget (seg bs i j) m := by
  induction budget using Nat.strong_induction_on with
  | _ budget ih =>
  intro shift acc bs st i j v hi hs h
  obtain ⟨hsz, hst, hcase⟩ := sAux_ok h
  have hc : seg bs i (i + 1) = [bs[i]] := by rw [seg_cons bs hsz (by omega), seg_self]
  rcases hcase with ⟨hb, hN, hv, hj⟩ | ⟨hb, hb', hN, hv, hj⟩ | ⟨hb, hN, hrec⟩
  · have hu : SN budget [bs[i]] (bs[i].toNat : Int) := SN.pos _ (by norm_num; omega) hN
    exact ⟨by omega, by omega, _, hv, by rw [hj, hc]; exact hu⟩
  · have hu : SN budget [bs[i]] ((bs[i].toNat : Int) - 2 ^ 7) :=
      SN.neg _ (by norm_num; omega) (by norm_num; omega) hN
    exact ⟨by omega, by omega, _, hv, by rw [hj, hc]; exact hu⟩
  · show i ≤ j ∧ j ≤ st ∧ ∃ m, v = acc + 2 ^ shift * m ∧ SN budget (seg bs i j) m
    obtain ⟨h1, h2, m, hv, hu⟩ : i + 1 ≤ j ∧ j ≤ st ∧ ∃ m,
        v = acc + 2 ^ shift * ((bs[i].toNat : Int) - 2 ^ 7) + 2 ^ (shift + 7) * m ∧
          SN (budget - 7) (seg bs (i + 1) j) m :=
      ih (budget - 7) (by omega) (shift + 7) (acc + 2 ^ shift * ((bs[i].toNat : Int) - 2 ^ 7))
        (Nat.succ_le_of_lt hst) hs hrec
    have hval : v = acc + 2 ^ shift * (2 ^ 7 * m + ((bs[i].toNat : Int) - 2 ^ 7)) := by
      rw [hv, pow_add]; ring
    have hu' : SN budget (bs[i] :: seg bs (i + 1) j) (2 ^ 7 * m + ((bs[i].toNat : Int) - 2 ^ 7)) :=
      SN.cont _ (by rw [two_pow_seven]; exact hb) hN hu
    exact ⟨by omega, h2, _, hval, by rw [seg_cons bs hsz (by omega)]; exact hu'⟩

theorem sAux_complete {budget : Nat} {l : Bytes} {m : Int} (hu : SN budget l m) :
    ∀ (shift : Nat) (acc : Int) {bs : ByteArray} {st i : Nat}, i + l.length ≤ st → st ≤ bs.size →
      seg bs i (i + l.length) = l →
      sAux budget shift acc bs st i = .ok (acc + 2 ^ shift * m) (i + l.length) := by
  induction hu with
  | pos n h1 h2 =>
    intro shift acc bs st i hl hs hseg
    obtain ⟨hsz, hb, -⟩ := seg_head (l := []) (by omega) hseg
    have hst : i < st := by simp only [List.length_singleton] at hl; omega
    have hn : n.toNat < 64 := by simpa using h1
    rw [sAux]
    simp [hst, hsz, hb, hn, h2]
  | @neg N n h1 h2 h3 =>
    intro shift acc bs st i hl hs hseg
    obtain ⟨hsz, hb, -⟩ := seg_head (l := []) (by omega) hseg
    have hst : i < st := by simp only [List.length_singleton] at hl; omega
    have hn : ¬ n.toNat < 64 ∧ n.toNat < 128 := ⟨by norm_num at h1; omega, by simpa using h2⟩
    have h3' : (128 : Int) ≤ n.toNat + 2 ^ (N - 1) := by linarith [(by norm_num : (2 : Int) ^ 7 = 128) ▸ h3]
    rw [sAux]
    simp [hst, hsz, hb, hn, h3']
  | @cont N n b m h1 h2 rest ih =>
    intro shift acc bs st i hl hs hseg
    obtain ⟨hsz, hb, hr⟩ := seg_head (by omega) hseg
    have hst : i + 1 + b.length ≤ st := by simp only [List.length_cons] at hl; omega
    have hrec := ih (shift + 7) (acc + 2 ^ shift * ((n.toNat : Int) - 2 ^ 7)) hst hs hr
    rw [sAux_cont (by omega) hsz (hb ▸ two_pow_seven ▸ h1) h2, hb, hrec]
    exact congrArg₂ (fun a b => Res.ok a b) (by rw [pow_add]; ring)
      (by simp only [List.length_cons]; omega)

theorem sound_sN (N : Nat) : Sound (SN N) (sN N) := by
  intro bs st i v j hi hs h
  obtain ⟨h1, h2, m, hv, hu⟩ := sAux_sound N 0 0 hi hs h
  simp only [pow_zero, one_mul, zero_add] at hv
  exact ⟨h1, h2, hv ▸ hu⟩

theorem complete_sN (N : Nat) : Complete (SN N) (sN N) := by
  intro l v bs st i hu hl hs hseg
  have := sAux_complete hu 0 0 hl hs hseg
  simpa [sN] using this

/-! ## Little-endian -/

theorem leAux_sound (n : Nat) : ∀ (shift acc : Nat) {bs : ByteArray} {st i v j : Nat},
    i ≤ st → st ≤ bs.size → leAux n shift acc bs st i = .ok v j →
    j = i + n ∧ j ≤ st ∧ v = acc + 2 ^ shift * littleEndian (seg bs i j) := by
  induction n with
  | zero =>
    intro shift acc bs st i v j hi hs h
    simp only [leAux] at h
    cases h
    simp [littleEndian, hi]
  | succ n ih =>
    intro shift acc bs st i v j hi hs h
    simp only [leAux] at h
    split at h
    · next hst =>
      split at h
      · next hsz =>
        obtain ⟨h1, h2, h3⟩ := ih _ _ (by omega) hs h
        refine ⟨by omega, h2, ?_⟩
        rw [h3, seg_cons bs hsz (by omega), littleEndian, pow_add]
        ring
      · cases h
    · cases h

theorem leAux_complete {l : Bytes} : ∀ (shift acc : Nat) {bs : ByteArray} {st i : Nat},
    i + l.length ≤ st → st ≤ bs.size → seg bs i (i + l.length) = l →
    leAux l.length shift acc bs st i = .ok (acc + 2 ^ shift * littleEndian l) (i + l.length) := by
  induction l with
  | nil => intro shift acc bs st i _ _ _; simp [leAux, littleEndian]
  | cons b l ih =>
    intro shift acc bs st i hl hs hseg
    simp only [List.length_cons] at hl hseg ⊢
    have hsz : i < bs.size := by omega
    rw [seg_cons bs hsz (by omega)] at hseg
    injection hseg with hb hrest
    simp only [leAux, show i < st by omega, hsz, hb, ↓reduceDIte]
    rw [ih _ _ (by omega) hs (by rw [show i + 1 + l.length = i + (l.length + 1) by omega]; exact hrest)]
    exact congrArg₂ (fun a b => Res.ok a b) (by rw [littleEndian, pow_add]; ring) (by omega)

theorem sound_le (n : Nat) : Sound (Spec.le n) (le n) := by
  intro bs st i v j hi hs h
  obtain ⟨h1, h2, h3⟩ := leAux_sound n 0 0 hi hs h
  refine ⟨by omega, h2, ?_, by simpa using h3⟩
  rw [length_seg]; omega

theorem complete_le (n : Nat) : Complete (Spec.le n) (le n) := by
  intro l v bs st i hg hl hs hseg
  obtain ⟨rfl, rfl⟩ := hg
  simpa [le] using leAux_complete 0 0 hl hs hseg

/-! ## Big-endian -/

theorem beAux_sound (n : Nat) : ∀ (acc : Nat) {bs : ByteArray} {st i v j : Nat},
    i ≤ st → st ≤ bs.size → beAux n acc bs st i = .ok v j →
    j = i + n ∧ j ≤ st ∧ v = (seg bs i j).foldl (fun a b => a * 256 + b.toNat) acc := by
  induction n with
  | zero =>
    intro acc bs st i v j hi hs h
    simp only [beAux] at h
    cases h
    simp [hi]
  | succ n ih =>
    intro acc bs st i v j hi hs h
    simp only [beAux] at h
    split at h
    · next hst =>
      split at h
      · next hsz =>
        obtain ⟨h1, h2, h3⟩ := ih _ (by omega) hs h
        refine ⟨by omega, h2, ?_⟩
        rw [h3, seg_cons bs hsz (by omega), List.foldl_cons]
      · cases h
    · cases h

theorem beAux_complete {l : Bytes} : ∀ (acc : Nat) {bs : ByteArray} {st i : Nat},
    i + l.length ≤ st → st ≤ bs.size → seg bs i (i + l.length) = l →
    beAux l.length acc bs st i = .ok (l.foldl (fun a b => a * 256 + b.toNat) acc) (i + l.length) := by
  induction l with
  | nil => intro acc bs st i _ _ _; simp [beAux]
  | cons b l ih =>
    intro acc bs st i hl hs hseg
    simp only [List.length_cons] at hl hseg ⊢
    have hsz : i < bs.size := by omega
    rw [seg_cons bs hsz (by omega)] at hseg
    injection hseg with hb hrest
    simp only [beAux, show i < st by omega, hsz, hb, ↓reduceDIte]
    rw [ih _ (by omega) hs (by rw [show i + 1 + l.length = i + (l.length + 1) by omega]; exact hrest)]
    exact congrArg₂ (fun a b => Res.ok a b) rfl (by omega)

theorem sound_be (n : Nat) : Sound (Spec.be n) (be n) := by
  intro bs st i v j hi hs h
  obtain ⟨h1, h2, h3⟩ := beAux_sound n 0 hi hs h
  refine ⟨by omega, h2, ?_, h3⟩
  rw [length_seg]; omega

theorem complete_be (n : Nat) : Complete (Spec.be n) (be n) := by
  intro l v bs st i hg hl hs hseg
  obtain ⟨rfl, rfl⟩ := hg
  simpa [be, Spec.bigEndian] using beAux_complete 0 hl hs hseg


namespace Grammar

/-- `n` big-endian bytes. -/
instance lawful_be (n : Nat) : (be n).Lawful := ⟨sound_be n, complete_be n⟩

end Grammar

end Silmaril.Parse.ByteParse
