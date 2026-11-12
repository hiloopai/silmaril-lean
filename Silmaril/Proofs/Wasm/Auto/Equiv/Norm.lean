module

public import Silmaril.Wasm.Auto.Equiv.Defs
public import Mathlib.Data.BitVec
public import Mathlib.Tactic.Ring

/-!
# Soundness of the normaliser

`ev_norm`: the normaliser of `Silmaril.Wasm.Auto.Equiv.Defs` preserves the value of a term
in every environment, at every type. The pieces: linear combinations (`Lin.ev_add`,
`Lin.ev_scale`, `Lin.ev_canon`: sorting is a permutation, merging adds coefficients,
reduction drops zero coefficients modulo `2^w`), reading and rebuilding them
(`ev_linOf`, `ev_rebuild`), and one lemma per operator family (`ev_normBin`,
`ev_normRel`). Also `safeBin_ok`: an admitted division or remainder does not trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Numerics

variable (ρ : Env)

/-! ## Constants -/

theorem ofNat_mOne (t : IntType) : BitVec.ofNat t.width (mOne t) = -1 := by
  cases t <;> decide

theorem ofNat_mOne_allOnes (t : IntType) :
    BitVec.ofNat t.width (mOne t) = BitVec.allOnes t.width := by
  cases t <;> decide

theorem ofNat_mod_pow (w c : Nat) : BitVec.ofNat w (c % 2 ^ w) = BitVec.ofNat w c := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem ofNat_eq_zero {w c : Nat} (h : c % 2 ^ w = 0) : BitVec.ofNat w c = 0 := by
  apply BitVec.eq_of_toNat_eq
  simpa using h

theorem ofNat_toNat_self {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  simp

theorem ofNat_twoPow (w n : Nat) : BitVec.ofNat w (2 ^ n) = BitVec.twoPow w n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow]

theorem mod_width_mod (t : IntType) (k : Nat) : k % 2 ^ t.width % t.width = k % t.width := by
  cases t <;> simp only [IntType.width] <;> omega

@[simp] theorem binV_add (t : IntType) (x y : BitVec t.width) : binV t .add x y = x + y := rfl
@[simp] theorem binV_sub (t : IntType) (x y : BitVec t.width) : binV t .sub x y = x - y := rfl
@[simp] theorem binV_mul (t : IntType) (x y : BitVec t.width) : binV t .mul x y = x * y := rfl
@[simp] theorem binV_and (t : IntType) (x y : BitVec t.width) : binV t .and x y = (x &&& y) := rfl
@[simp] theorem binV_or (t : IntType) (x y : BitVec t.width) : binV t .or x y = (x ||| y) := rfl
@[simp] theorem binV_xor (t : IntType) (x y : BitVec t.width) : binV t .xor x y = (x ^^^ y) := rfl
@[simp] theorem binV_shl (t : IntType) (x y : BitVec t.width) :
    binV t .shl x y = x <<< (y.toNat % t.width) := rfl

theorem binV_shrU (t : IntType) (x y : BitVec t.width) :
    binV t (.shr .unsigned) x y = x >>> (y.toNat % t.width) := rfl

theorem binV_shrS (t : IntType) (x y : BitVec t.width) :
    binV t (.shr .signed) x y = x.sshiftRight (y.toNat % t.width) := rfl

theorem binV_divU {t : IntType} {x y : BitVec t.width} (hy : y ≠ 0#t.width) :
    binV t (.div .unsigned) x y = x / y := by
  simp [binV, intBinOp, hy]

theorem binV_remU {t : IntType} {x y : BitVec t.width} (hy : y ≠ 0#t.width) :
    binV t (.rem .unsigned) x y = x % y := by
  simp [binV, intBinOp, hy]

/-! ## Linear combinations -/

namespace Lin

open Silmaril.Wasm.Auto.Equiv.Lin

variable {ρ} {t : IntType}

@[simp] theorem evMs_nil : evMs ρ t [] = 0 := rfl

@[simp] theorem evMs_cons (m : Nat × Term) (ms : List (Nat × Term)) :
    evMs ρ t (m :: ms) = BitVec.ofNat t.width m.1 * Equiv.ev ρ t m.2 + evMs ρ t ms := rfl

theorem evMs_append (l₁ l₂ : List (Nat × Term)) :
    evMs ρ t (l₁ ++ l₂) = evMs ρ t l₁ + evMs ρ t l₂ := by
  induction l₁ with
  | nil => simp
  | cons m ms ih => simp [ih, add_assoc]

theorem ev_add (p q : Lin) : ev ρ t (add p q) = ev ρ t p + ev ρ t q := by
  simp only [Lin.ev, add, evMs_append, BitVec.ofNat_add]
  ring

theorem evMs_scale (c : Nat) (ms : List (Nat × Term)) :
    evMs ρ t (ms.map fun m => (c * m.1, m.2)) = BitVec.ofNat t.width c * evMs ρ t ms := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, evMs_cons, ih, BitVec.ofNat_mul]
    ring

theorem ev_scale (c : Nat) (p : Lin) : ev ρ t (scale c p) = BitVec.ofNat t.width c * ev ρ t p := by
  simp only [Lin.ev, scale, evMs_scale, BitVec.ofNat_mul]
  ring

theorem evMs_perm {l₁ l₂ : List (Nat × Term)} (h : l₁.Perm l₂) : evMs ρ t l₁ = evMs ρ t l₂ := by
  induction h with
  | nil => rfl
  | cons m _ ih => simp [ih]
  | swap a b l => simp only [evMs_cons]; ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem ins_perm (m : Nat × Term) (l : List (Nat × Term)) : (ins m l).Perm (m :: l) := by
  induction l with
  | nil => simp [ins]
  | cons n ns ih =>
    simp only [ins]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons n ih).trans (List.Perm.swap m n ns)

theorem isort_perm (l : List (Nat × Term)) : (isort l).Perm l := by
  induction l with
  | nil => simp [isort]
  | cons m ms ih => exact (ins_perm m _).trans (List.Perm.cons m ih)

theorem evMs_mergeAdj (l : List (Nat × Term)) : evMs ρ t (mergeAdj l) = evMs ρ t l := by
  induction l with
  | nil => rfl
  | cons m ms ih =>
    simp only [mergeAdj]
    split
    · rename_i n rest h
      rw [h] at ih
      split
      · rename_i hmn
        simp only [evMs_cons, BitVec.ofNat_add, ← ih, hmn]
        ring
      · simp [← ih]
    · rename_i h
      rw [h] at ih
      simp [← ih]

theorem evMs_reduce (l : List (Nat × Term)) :
    evMs ρ t (reduce (2 ^ t.width) l) = evMs ρ t l := by
  induction l with
  | nil => rfl
  | cons m ms ih =>
    simp only [reduce]
    split
    · rename_i h
      simp [ih, ofNat_eq_zero h]
    · simp [ih, ofNat_mod_pow]

theorem ev_canon (p : Lin) : ev ρ t (canon t p) = ev ρ t p := by
  simp only [Lin.ev, Lin.canon, evMs_reduce, evMs_mergeAdj, evMs_perm (isort_perm _), ofNat_mod_pow]

end Lin

/-! ## Reading and rebuilding -/

variable {ρ}

theorem ev_linOf (t : IntType) (e : Term) : Lin.ev ρ t (linOf e) = ev ρ t e := by
  fun_induction linOf e with
  | case1 a b iha ihb => simp [Lin.ev_add, iha, ihb, ev]
  | case2 c a ih => simp [Lin.ev_scale, ih, ev]
  | case3 c => simp [Lin.ev, ev]
  | case4 e => simp [Lin.ev]

theorem ev_mono (t : IntType) (c : Nat) (a : Term) :
    ev ρ t (mono c a) = BitVec.ofNat t.width c * ev ρ t a := by
  unfold mono
  split
  · rename_i h
    subst h
    simp
  · simp [ev]

theorem ev_sumMs (t : IntType) (ms : List (Nat × Term)) : ev ρ t (sumMs ms) = Lin.evMs ρ t ms := by
  fun_induction sumMs ms with
  | case1 => simp [ev]
  | case2 m => simp [ev_mono]
  | case3 m ms hne ih => simp [ev, ev_mono, ih]

theorem ev_rebuild (t : IntType) (p : Lin) : ev ρ t (rebuild p) = Lin.ev ρ t p := by
  unfold rebuild
  split
  · rename_i h
    simp [Lin.ev, h, ev]
  · split
    · rename_i h
      simp [Lin.ev, h, ev_sumMs]
    · simp only [ev, binV_add, ev_sumMs, Lin.ev]
      ring

theorem ev_linNorm (t : IntType) (p : Lin) : ev ρ t (linNorm t p) = Lin.ev ρ t p := by
  simp [linNorm, ev_rebuild, Lin.ev_canon]

/-! ## Operators -/

theorem ev_ord2 (t : IntType) (op : IntBinOp)
    (hc : ∀ x y : BitVec t.width, binV t op x y = binV t op y x) (a b : Term) :
    ev ρ t (ord2 op a b) = binV t op (ev ρ t a) (ev ρ t b) := by
  unfold ord2
  split
  · rfl
  · exact hc _ _

theorem ev_const_binV (t : IntType) (op : IntBinOp) (x y : Nat) :
    ev ρ t (.const (binV t op (BitVec.ofNat _ x) (BitVec.ofNat _ y)).toNat) =
      binV t op (ev ρ t (.const x)) (ev ρ t (.const y)) := by
  simp [ev]

theorem ev_normBitwise (t : IntType) (op : IntBinOp) (hop : op = .and ∨ op = .or ∨ op = .xor)
    (a b : Term) : ev ρ t (normBitwise t op a b) = binV t op (ev ρ t a) (ev ρ t b) := by
  have hc : ∀ x y : BitVec t.width, binV t op x y = binV t op y x := by
    rcases hop with rfl | rfl | rfl
    · exact fun x y => BitVec.and_comm x y
    · exact fun x y => BitVec.or_comm x y
    · exact fun x y => BitVec.xor_comm x y
  have hm := ofNat_mOne_allOnes t
  unfold normBitwise
  split
  · exact ev_const_binV t op _ _
  · split
    · rename_i hab
      subst hab
      rcases hop with rfl | rfl | rfl <;> simp [ev]
    · split
      all_goals first
        | exact ev_ord2 t _ hc _ _
        | (simp_all [ev]; done)
        | (split <;> first | exact ev_ord2 t _ hc _ _ | simp_all [ev])

theorem ushiftRight_width {w : Nat} (x : BitVec w) : x >>> w = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt x.isLt]

theorem shiftLeft_width {w : Nat} (x : BitVec w) : x <<< w = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem ev_normOther (t : IntType) (op : IntBinOp) (a b : Term) :
    ev ρ t (normOther t op a b) = binV t op (ev ρ t a) (ev ρ t b) := by
  unfold normOther
  split
  · exact ev_const_binV t op _ _
  · split
    · rename_i k _ h
      obtain ⟨hid, hk⟩ := h
      cases op <;> simp [idAtZero] at hid
      · rename_i s
        cases s <;> simp [ev, binV, intBinOp, mod_width_mod, hk]
      · simp only [ev, binV, intBinOp, BitVec.toNat_ofNat]
        rw [← BitVec.rotateLeft_mod_eq_rotateLeft, mod_width_mod, hk]
        simp [BitVec.rotateLeft, BitVec.rotateLeftAux, ushiftRight_width]
      · simp only [ev, binV, intBinOp, BitVec.toNat_ofNat]
        rw [← BitVec.rotateRight_mod_eq_rotateRight, mod_width_mod, hk]
        simp [BitVec.rotateRight, BitVec.rotateRightAux]
    · rfl
  · rfl

theorem ev_normBin (t : IntType) (op : IntBinOp) (a b : Term) :
    ev ρ t (normBin t op a b) = binV t op (ev ρ t a) (ev ρ t b) := by
  cases op with
  | add => simp [normBin, ev_linNorm, Lin.ev_add, ev_linOf]
  | sub =>
    simp only [normBin, ev_linNorm, Lin.ev_add, Lin.ev_scale, ev_linOf, ofNat_mOne, binV_sub]
    ring
  | mul =>
    simp only [normBin]
    split
    · simp [ev_linNorm, Lin.ev_scale, ev_linOf, ev]
    · simp only [ev_linNorm, Lin.ev_scale, ev_linOf, ev, binV_mul]
      ring
    · exact ev_ord2 t .mul (fun x y => BitVec.mul_comm x y) _ _
  | shl =>
    simp only [normBin]
    split
    · simp only [ev_linNorm, Lin.ev_scale, ev_linOf, ev, binV_shl, BitVec.toNat_ofNat,
        mod_width_mod, BitVec.shiftLeft_eq_mul_twoPow, ofNat_twoPow]
      ring
    · rfl
  | and => exact ev_normBitwise t .and (Or.inl rfl) a b
  | or => exact ev_normBitwise t .or (Or.inr (Or.inl rfl)) a b
  | xor => exact ev_normBitwise t .xor (Or.inr (Or.inr rfl)) a b
  | div s => exact ev_normOther t _ a b
  | rem s => exact ev_normOther t _ a b
  | shr s => exact ev_normOther t _ a b
  | rotl => exact ev_normOther t _ a b
  | rotr => exact ev_normOther t _ a b

theorem beq_sub {w : Nat} (x y : BitVec w) : (x == y) = (x - y == 0) := by
  by_cases h : x = y
  · subst h
    simp
  · have h' : ¬x - y = 0 := fun e => h (sub_eq_zero.mp e)
    rw [beq_false_of_ne h, beq_false_of_ne h']

theorem beq_neg {w : Nat} (z : BitVec w) : (-z == 0) = (z == 0) := by
  by_cases h : z = 0
  · subst h
    simp
  · have h' : ¬-z = 0 := fun e => h (neg_eq_zero.mp e)
    rw [beq_false_of_ne h, beq_false_of_ne h']

theorem intRelOp_eq_sub (t : IntType) (x y : BitVec t.width) :
    intRelOp t .eq x y = intRelOp t .eq (x - y) 0 := by
  simp only [intRelOp]
  rw [beq_sub x y]

theorem intRelOp_ne_sub (t : IntType) (x y : BitVec t.width) :
    intRelOp t .ne x y = intRelOp t .ne (x - y) 0 := by
  simp only [intRelOp, bne]
  rw [beq_sub x y]

theorem intRelOp_neg (t : IntType) (op : IntRelOp) (hop : op = .eq ∨ op = .ne) (z : BitVec t.width) :
    intRelOp t op (-z) 0 = intRelOp t op z 0 := by
  rcases hop with rfl | rfl
  · simp only [intRelOp]
    rw [beq_neg]
  · simp only [intRelOp, bne]
    rw [beq_neg]

theorem ev_diffNorm (t : IntType) (a b : Term) :
    Lin.ev ρ t (diffNorm t a b) = ev ρ t a - ev ρ t b := by
  simp only [diffNorm, Lin.ev_canon, Lin.ev_add, Lin.ev_scale, ev_linOf, ofNat_mOne]
  ring

theorem intRelOp_sub_of (t : IntType) {op : IntRelOp} (hop : op = .eq ∨ op = .ne)
    (x y : BitVec t.width) : intRelOp t op x y = intRelOp t op (x - y) 0 := by
  rcases hop with h | h
  · exact h ▸ intRelOp_eq_sub t x y
  · exact h ▸ intRelOp_ne_sub t x y

theorem ev_normEqNe (t t' : IntType) (op : IntRelOp) (hop : op = .eq ∨ op = .ne) (a b : Term) :
    ev ρ t (normEqNe t t' op a b) =
      (intRelOp t' op (ev ρ t' a) (ev ρ t' b)).setWidth t.width := by
  have hd : Lin.ev ρ t' (diffNorm t' a b) = ev ρ t' a - ev ρ t' b := ev_diffNorm t' a b
  have hsub : intRelOp t' op (ev ρ t' a) (ev ρ t' b) =
      intRelOp t' op (ev ρ t' a - ev ρ t' b) 0 := intRelOp_sub_of t' hop _ _
  unfold normEqNe
  dsimp only
  split
  · next hnil =>
    have h₀ : Lin.ev ρ t' (diffNorm t' a b) = BitVec.ofNat _ (diffNorm t' a b).1 := by
      simp [Lin.ev, hnil]
    simp [ev, hsub, ← hd, h₀, ofNat_mod_pow]
  · show ev ρ t (if _ then _ else _) = _
    have h₁ : ev ρ t' (rebuild (diffNorm t' a b)) = ev ρ t' a - ev ρ t' b := by
      rw [ev_rebuild, hd]
    have h₂ : ev ρ t' (rebuild (Lin.canon t' (Lin.scale (mOne t') (diffNorm t' a b)))) =
        -(ev ρ t' a - ev ρ t' b) := by
      rw [ev_rebuild, Lin.ev_canon, Lin.ev_scale, hd, ofNat_mOne]
      ring
    split
    · simp only [ev, h₁, hsub]
      rfl
    · simp only [ev, h₂, hsub]
      rw [← intRelOp_neg t' op hop (ev ρ t' a - ev ρ t' b)]
      rfl

theorem eqz_bool32 (t : IntType) (c : Bool) :
    ((bool32 c).setWidth t.width == 0) = !c := by
  cases t <;> cases c <;> decide

theorem nez_bool32 (t : IntType) (c : Bool) :
    ((bool32 c).setWidth t.width != 0) = c := by
  cases t <;> cases c <;> decide

theorem ev_rel (t t' : IntType) (op : IntRelOp) (a b : Term) :
    ev ρ t (.rel t' op a b) = (intRelOp t' op (ev ρ t' a) (ev ρ t' b)).setWidth t.width := rfl

theorem ev_negRel {r r' : Term} (h : negRel r = some r') (t t' : IntType) :
    ev ρ t r' = (intRelOp t' .eq (ev ρ t' r) 0).setWidth t.width := by
  rcases r with _ | _ | _ | _ | ⟨t'', op, x, y⟩ <;> simp only [negRel, reduceCtorEq] at h
  rcases op with _ | _ | s | s | s | s <;> simp only [Option.some.injEq] at h <;> subst h
  all_goals (try cases s)
  all_goals
    simp only [ev_rel, intRelOp]
    rw [eqz_bool32]
    first
      | rfl
      | (simp [bne]; done)
      | (congr 2
         rw [← decide_not]
         simp only [decide_eq_decide, gt_iff_lt, ge_iff_le]
         constructor <;> intro <;> omega)

theorem ev_isRel {r : Term} (h : isRel r = true) (t t' : IntType) :
    ev ρ t r = (intRelOp t' .ne (ev ρ t' r) 0).setWidth t.width := by
  rcases r with _ | _ | _ | _ | ⟨t'', op, x, y⟩ <;> simp only [isRel, reduceCtorEq] at h
  simp only [ev_rel]
  conv => rhs; simp only [intRelOp]
  rw [nez_bool32]
  rfl

theorem intRelOp_eq_comm (t : IntType) (x y : BitVec t.width) :
    intRelOp t .eq x y = intRelOp t .eq y x := by
  simp only [intRelOp]
  rw [Bool.beq_comm]

theorem intRelOp_ne_comm (t : IntType) (x y : BitVec t.width) :
    intRelOp t .ne x y = intRelOp t .ne y x := by
  simp only [intRelOp]
  rw [bne_comm]

theorem ev_boolEqZero {op : IntRelOp} {a b r : Term} (h : boolEqZero op a b = some r)
    (t t' : IntType) :
    ev ρ t r = (intRelOp t' op (ev ρ t' a) (ev ρ t' b)).setWidth t.width := by
  unfold boolEqZero at h
  split at h
  · rw [ev_negRel h t t']
    rfl
  · rw [ev_negRel h t t', intRelOp_eq_comm]
    rfl
  · split at h
    · rename_i hr
      cases h
      rw [ev_isRel hr t t']
      rfl
    · cases h
  · split at h
    · rename_i hr
      cases h
      rw [ev_isRel hr t t', intRelOp_ne_comm]
      rfl
    · cases h
  · cases h

theorem ev_normRel (t t' : IntType) (op : IntRelOp) (a b : Term) :
    ev ρ t (normRel t t' op a b) = (intRelOp t' op (ev ρ t' a) (ev ρ t' b)).setWidth t.width := by
  unfold normRel
  split
  · simp [ev, ofNat_mod_pow]
  · split
    · rename_i r hr
      exact ev_boolEqZero hr t t'
    · cases op with
      | eq => exact ev_normEqNe t t' .eq (Or.inl rfl) a b
      | ne => exact ev_normEqNe t t' .ne (Or.inr rfl) a b
      | lt s => rfl
      | le s => rfl
      | gt s => cases s <;> rfl
      | ge s => cases s <;> rfl

/-- **The normaliser preserves values.** -/
theorem ev_norm (t : IntType) (e : Term) : ev ρ t (norm t e) = ev ρ t e := by
  induction e generalizing t with
  | var n => rfl
  | const c => simp [norm, ev, ofNat_mod_pow]
  | un op a ih =>
    simp only [norm]
    split
    · rename_i c hc
      have h := ih t
      rw [hc] at h
      simp [ev, ← h]
    · simp [ev, ih]
  | bin op a b iha ihb => simp [norm, ev_normBin, ev, iha, ihb]
  | rel t' op a b iha ihb => simp [norm, ev_normRel, ev, iha, ihb]

theorem ofNat_ne_zero {w c : Nat} (h : ¬c % 2 ^ w = 0) : BitVec.ofNat w c ≠ 0#w := fun h' =>
  h (by simpa using congrArg BitVec.toNat h')

theorem ofNat_ne_mOne (t : IntType) {c : Nat} (h : ¬c % 2 ^ t.width = mOne t) :
    BitVec.ofNat t.width c ≠ -1#t.width := by
  intro h'
  apply h
  have h1 := congrArg BitVec.toNat h'
  cases t <;> simp [mOne] at h1 ⊢ <;> omega

theorem divU_ok (t : IntType) (x y : BitVec t.width) (hy : y ≠ 0#t.width) :
    ∃ z, intBinOp t (.div .unsigned) x y = .ok z := ⟨x / y, by simp [intBinOp, hy]⟩

theorem remU_ok (t : IntType) (x y : BitVec t.width) (hy : y ≠ 0#t.width) :
    ∃ z, intBinOp t (.rem .unsigned) x y = .ok z := ⟨x % y, by simp [intBinOp, hy]⟩

theorem remS_ok (t : IntType) (x y : BitVec t.width) (hy : y ≠ 0#t.width) :
    ∃ z, intBinOp t (.rem .signed) x y = .ok z := ⟨x.srem y, by simp [intBinOp, hy]⟩

theorem divS_ok (t : IntType) (x y : BitVec t.width) (hy : y ≠ 0#t.width) (hy' : y ≠ -1#t.width) :
    ∃ z, intBinOp t (.div .signed) x y = .ok z := ⟨x.sdiv y, by simp [intBinOp, hy, hy']⟩

/-- An admitted division or remainder does not trap. -/
theorem safeBin_ok (t : IntType) (op : IntBinOp) (b : Term) (hs : safeBin t op b = true)
    (x : BitVec t.width) : ∃ z, intBinOp t op x (ev ρ t b) = .ok z := by
  have hb := ev_norm (ρ := ρ) t b
  unfold safeBin at hs
  generalize norm t b = nb at hs hb
  rw [← hb]
  cases op with
  | div s =>
    cases nb <;> cases s <;> simp at hs
    · exact divS_ok t x _ (ofNat_ne_zero hs.1) (ofNat_ne_mOne t hs.2)
    · exact divU_ok t x _ (ofNat_ne_zero hs)
  | rem s =>
    cases nb <;> cases s <;> simp at hs
    · exact remS_ok t x _ (ofNat_ne_zero hs)
    · exact remU_ok t x _ (ofNat_ne_zero hs)
  | shr s => cases s <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

end Silmaril.Proofs.Wasm.Auto.Equiv