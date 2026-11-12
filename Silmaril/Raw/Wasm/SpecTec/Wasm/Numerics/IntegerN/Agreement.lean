module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Numerics.IntegerN
public import Silmaril.Wasm.Numerics.Float

@[expose] public section

/-! # Agreement of the width-parametric spec transcription with `BitVec` and the 32/64-bit numerics

The spec-literal definitions of `IntegerN` coincide with `BitVec` operations,
and their dispatchers (`iunop_`, `ibinop_`, `itestop_`, `irelop_`) instantiated at
`t.width` coincide with `intUnOp`, `intBinOp`, `intTestOp` and `intRelOp`.
-/

namespace Silmaril.Wasm.Numerics

/-! ## Representation lemmas -/

theorem signed_toNat {N : Nat} (x : BitVec N) : signed_ N x.toNat = x.toInt := by
  have hx := x.isLt
  rcases N with _ | n
  · have h0 : x.toNat = 0 := by simpa using hx
    simp [signed_, BitVec.toInt_eq_toNat_cond, h0]
  · have hp : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := Nat.pow_succ'
    have c1 : (2 : Int) ^ (n + 1) = ((2 ^ (n + 1) : Nat) : Int) := by norm_cast
    have c2 : (2 : Int) ^ n = ((2 ^ n : Nat) : Int) := by norm_cast
    rw [BitVec.toInt_eq_toNat_cond]
    simp only [signed_, Nat.add_sub_cancel, c1]
    split <;> split <;> omega

theorem ofNat_invSigned (N : Nat) (j : Int) :
    BitVec.ofNat N (invSigned_ N j) = BitVec.ofInt N j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt, invSigned_]
  have hpos : (0 : Int) < ((2 ^ N : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos N
  have h1 := Int.emod_nonneg j (ne_of_gt hpos)
  have h2 := Int.emod_lt_of_pos j hpos
  generalize j % ((2 ^ N : Nat) : Int) = k at *
  apply Nat.mod_eq_of_lt
  omega

theorem bv_beq_eq_decide {N : Nat} (x y : BitVec N) : (x == y) = decide (x = y) := rfl

theorem u32OfBool_eq_bool32 (b : Bool) : u32OfBool b = bool32 b := by cases b <;> rfl

theorem toNat_eq_zero_iff {N : Nat} (x : BitVec N) : x.toNat = 0 ↔ x = 0 := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by simpa using h)
  · rintro rfl; simp

/-! ## Operations agree with `BitVec` -/

variable {N : Nat}

theorem iadd_eq (a b : BitVec N) : iadd_ N a b = a + b := by
  apply BitVec.eq_of_toNat_eq; simp [iadd_, BitVec.toNat_add]

theorem isub_eq (a b : BitVec N) : isub_ N a b = a - b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [isub_, BitVec.toNat_ofNat, BitVec.toNat_sub, Nat.mod_mod]
  congr 1; omega

theorem imul_eq (a b : BitVec N) : imul_ N a b = a * b := by
  apply BitVec.eq_of_toNat_eq; simp [imul_, BitVec.toNat_mul]

theorem ineg_eq (a : BitVec N) : ineg_ N a = -a := by
  apply BitVec.eq_of_toNat_eq; simp [ineg_, BitVec.toNat_neg]

theorem iextend_signed_eq (K : Nat) (x : BitVec N) :
    iextend_ N K .signed x = (x.setWidth K).signExtend N := by
  rw [iextend_, ← BitVec.toNat_setWidth, signed_toNat, ofNat_invSigned]
  rfl

theorem extend_signed_eq (M N : Nat) (x : BitVec M) : extend_ M N .signed x = x.signExtend N := by
  rw [extend_, signed_toNat, ofNat_invSigned]
  rfl

theorem extend_unsigned_eq (M N : Nat) (x : BitVec M) : extend_ M N .unsigned x = x.setWidth N := by
  apply BitVec.eq_of_toNat_eq; simp [extend_]

theorem wrap_eq (M N : Nat) (x : BitVec M) : wrap_ M N x = x.setWidth N := by
  apply BitVec.eq_of_toNat_eq; simp [wrap_]

theorem idiv_unsigned_eq (a b : BitVec N) :
    idiv_ N .unsigned a b = if b = 0 then none else some (a / b) := by
  simp only [idiv_, toNat_eq_zero_iff, BitVec.udiv_def]

theorem irem_unsigned_eq (a b : BitVec N) :
    irem_ N .unsigned a b = if b = 0 then none else some (a % b) := by
  simp only [irem_, toNat_eq_zero_iff]
  split
  · rfl
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_umod, ← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt)

theorem irem_signed_eq (a b : BitVec N) :
    irem_ N .signed a b = if b = 0 then none else some (a.srem b) := by
  simp only [irem_, toNat_eq_zero_iff, signed_toNat]
  split
  · rfl
  · congr 1
    rw [ofNat_invSigned, ← Int.tmod_def, ← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem tdiv_eq_half_iff (a b : BitVec N) (hN : 0 < N) :
    a.toInt.tdiv b.toInt = 2 ^ (N - 1) ↔ a = BitVec.intMin N ∧ b = -1 := by
  constructor
  · intro h
    by_contra hne
    have hov : a ≠ BitVec.intMin N ∨ b ≠ -1 := by
      by_cases ha : a = BitVec.intMin N
      · exact .inr fun hb => hne ⟨ha, hb⟩
      · exact .inl ha
    have hlt := BitVec.toInt_lt (x := a.sdiv b)
    rw [BitVec.toInt_sdiv_of_ne_or_ne a b hov, h] at hlt
    have : ((2 ^ (N - 1) : Nat) : Int) = 2 ^ (N - 1) := by norm_cast
    omega
  · rintro ⟨rfl, rfl⟩
    simp [BitVec.toInt_intMin_of_pos hN, BitVec.neg_one_eq_allOnes, hN]

theorem idiv_signed_eq (a b : BitVec N) :
    idiv_ N .signed a b =
      if b = 0 then none else if a = BitVec.intMin N ∧ b = -1 then none else some (a.sdiv b) := by
  simp only [idiv_, toNat_eq_zero_iff, signed_toNat]
  by_cases hb : b = 0
  · simp [hb]
  · have hN : 0 < N := by
      rcases N with _ | n
      · exact absurd (Subsingleton.elim b 0) hb
      · omega
    rw [ite_eq_right hb, ite_eq_right hb]
    by_cases hov : a = BitVec.intMin N ∧ b = -1
    · rw [ite_eq_left ((tdiv_eq_half_iff a b hN).2 hov), ite_eq_left hov]
    · rw [ite_eq_right (mt (tdiv_eq_half_iff a b hN).1 hov), ite_eq_right hov, ofNat_invSigned]
      have hov' : a ≠ BitVec.intMin N ∨ b ≠ -1 := by
        by_cases ha : a = BitVec.intMin N
        · exact .inr fun hb' => hov ⟨ha, hb'⟩
        · exact .inl ha
      rw [← BitVec.toInt_sdiv_of_ne_or_ne a b hov', BitVec.ofInt_toInt]

/-! ## Agreement with the 32/64-bit numerics -/

theorem iunop_agree (t : IntType) (op : IntUnOp) (x : IntValue t) :
    iunop_ t.width op x = intUnOp t op x := by
  cases op with
  | extend size => exact iextend_signed_eq _ x
  | _ => rfl

theorem ibinop_agree (t : IntType) (op : IntBinOp) (x y : IntValue t) :
    ibinop_ t.width op x y = (intBinOp t op x y).toOption := by
  cases op with
  | add => simp [ibinop_, intBinOp, iadd_eq, Except.toOption]
  | sub => simp [ibinop_, intBinOp, isub_eq, Except.toOption]
  | mul => simp [ibinop_, intBinOp, imul_eq, Except.toOption]
  | div s =>
    cases s
    · rw [ibinop_, idiv_signed_eq]; simp only [intBinOp]; split_ifs <;> rfl
    · rw [ibinop_, idiv_unsigned_eq]; simp only [intBinOp]; split_ifs <;> rfl
  | rem s =>
    cases s
    · rw [ibinop_, irem_signed_eq]; simp only [intBinOp]; split_ifs <;> rfl
    · rw [ibinop_, irem_unsigned_eq]; simp only [intBinOp]; split_ifs <;> rfl
  | shr s => cases s <;> rfl
  | _ => rfl

theorem itestop_agree (t : IntType) (op : IntTestOp) (x : IntValue t) :
    itestop_ t.width op x = intTestOp t op x := by
  cases op
  simp only [itestop_, ieqz_, intTestOp, u32OfBool_eq_bool32]
  simp [bv_beq_eq_decide, toNat_eq_zero_iff]

theorem irelop_agree (t : IntType) (op : IntRelOp) (x y : IntValue t) :
    irelop_ t.width op x y = intRelOp t op x y := by
  cases op with
  | eq => simp [irelop_, ieq_, intRelOp, u32OfBool_eq_bool32, bv_beq_eq_decide]
  | ne => simp [irelop_, ine_, intRelOp, u32OfBool_eq_bool32, bne, bv_beq_eq_decide]
  | lt s => cases s <;> simp [irelop_, ilt_, intRelOp, u32OfBool_eq_bool32, signed_toNat]
  | gt s => cases s <;> simp [irelop_, igt_, intRelOp, u32OfBool_eq_bool32, signed_toNat]
  | le s => cases s <;> simp [irelop_, ile_, intRelOp, u32OfBool_eq_bool32, signed_toNat]
  | ge s => cases s <;> simp [irelop_, ige_, intRelOp, u32OfBool_eq_bool32, signed_toNat]

theorem convert_wrap_agree (x : BitVec 64) : convert .wrap x = .ok (wrap_ 64 32 x) := by
  rw [wrap_eq]; rfl

theorem convert_extend_agree (s : Signedness) (x : BitVec 32) :
    convert (.extend s) x = .ok (extend_ 32 64 s x) := by
  cases s
  · rw [extend_signed_eq]; rfl
  · rw [extend_unsigned_eq]; rfl

/-! ## Sanity checks -/

example : iq15mulr_sat_ 16 .signed 0x8000#16 0x8000#16 = 0x7fff#16 := by decide
example : iq15mulr_sat_ 16 .signed 0x4000#16 0x4000#16 = 0x2000#16 := by decide
example : irelaxed_q15mulr_ 16 true 1 .signed 0x8000#16 0x8000#16 = [0x8000#16] := by decide
example : irelaxed_q15mulr_ 16 false 1 .signed 0x8000#16 0x8000#16 = [0x7fff#16] := by decide
example : iadd_sat_ 8 .signed 100#8 100#8 = 127#8 := by decide
example : isub_sat_ 8 .unsigned 1#8 2#8 = 0#8 := by decide
example : narrow_ 16 8 .signed 0xff00#16 = 0x80#8 := by decide
example : narrow_ 16 8 .unsigned 0xffff#16 = 0#8 := by decide
example : narrow_ 16 8 .unsigned 0x0100#16 = 0xff#8 := by decide
example : iavgr_ 8 .unsigned 255#8 254#8 = 255#8 := by decide
example : iabs_ 8 0x80#8 = 0x80#8 := by decide
example : idiv_ 8 .signed 0x80#8 0xff#8 = none := by decide
example : ivdot_ 16 [1#16, 2, 3, 4] [5#16, 6, 7, 8] = [17#16, 53] := by decide
example : irelaxed_laneselect_ 8 false 0 0xf0#8 0x0f#8 0x81#8 = [0x8e#8] := by decide
example : irelaxed_laneselect_ 8 true 1 0xf0#8 0x0f#8 0x81#8 = [0xf0#8] := by decide

end Silmaril.Wasm.Numerics
