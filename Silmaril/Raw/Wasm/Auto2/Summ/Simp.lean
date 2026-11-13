module

public import Silmaril.Wasm.Auto2.Summ.Defs
public import Silmaril.Wasm.Auto.Equiv.Thms

/-!
# The second simplifier and the guard keys preserve values (unrefined)

`evX_simp2`, `evX_canon2`: `simp2` and `canon2` (`Silmaril.Wasm.Auto2.Summ.Defs`) preserve the value
of every value term at every type, in every environment and initial memory. `holds_gkey`: a
guard and its key hold together; `holds_of_gdead`: a dead guard never holds.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Summ

open Silmaril.Wasm Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (Env binV)

variable {ρ : Env} {B0 : ByteArray}

theorem ofNat_eq_zero_of_mod {w c : Nat} (h : c % 2 ^ w = 0) : BitVec.ofNat w c = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, h]

theorem evX_zeroC {t : IntType} {a : XT} (h : zeroC t a = true) : evX ρ B0 t a = 0 := by
  cases a with
  | const c =>
    simp only [zeroC, beq_iff_eq] at h
    simp only [evX]
    exact ofNat_eq_zero_of_mod h
  | _ => simp [zeroC] at h

theorem setWidth_one (t : IntType) : (1#32).setWidth t.width = BitVec.ofNat t.width 1 := by
  cases t <;> decide

theorem bool32_setWidth (β : Bool) (t : IntType) :
    (bool32 β).setWidth t.width = 0 ∨ (bool32 β).setWidth t.width = 1 := by
  cases β <;> cases t <;> decide

theorem rel_cases (t t' : IntType) (op : IntRelOp) (a b : XT) :
    evX ρ B0 t (.rel t' op a b) = 0 ∨ evX ρ B0 t (.rel t' op a b) = 1 := by
  simp only [evX]
  unfold intRelOp
  exact bool32_setWidth _ t

theorem binV_rem_rel {t : IntType} {s : Signedness} {x y : BitVec t.width} (hy : y = 0 ∨ y = 1) :
    binV t (.rem s) x y = 0 := by
  rcases hy with rfl | rfl
  · cases s <;> simp [binV, intBinOp]
  · have h1 : (1 : BitVec t.width) ≠ 0 := by cases t <;> decide
    cases s
    · simp only [binV, intBinOp, h1, ↓reduceIte]
      exact BitVec.srem_one
    · simp only [binV, intBinOp, h1, ↓reduceIte]
      exact BitVec.umod_one

theorem absorb_spec {op : IntBinOp} {a b r : XT} (h : absorb op a b = some r) :
    ∃ c d, b = .bin op c d ∧ (a = c ∨ a = d) ∧ r = b := by
  unfold absorb at h
  split at h
  · rename_i op' c d
    split at h
    · rename_i hc
      obtain ⟨rfl, hc⟩ := hc
      exact ⟨c, d, rfl, hc, (Option.some.inj h).symm⟩
    · cases h
  · cases h

theorem cancelX_spec {a b r : XT} (h : cancelX a b = some r) :
    ∃ c d, b = .bin .xor c d ∧ ((a = c ∧ r = d) ∨ (a = d ∧ r = c)) := by
  unfold cancelX at h
  split at h
  · rename_i c d
    split at h
    · exact ⟨c, d, rfl, Or.inl ⟨by assumption, (Option.some.inj h).symm⟩⟩
    · split at h
      · exact ⟨c, d, rfl, Or.inr ⟨by assumption, (Option.some.inj h).symm⟩⟩
      · cases h
  · cases h

theorem evX_and_absorb {t : IntType} {a b r : XT} (h : absorb .and a b = some r) :
    evX ρ B0 t r = evX ρ B0 t (.bin .and a b) := by
  obtain ⟨c, d, rfl, hc, rfl⟩ := absorb_spec h
  simp only [evX, binV, intBinOp]
  rcases hc with rfl | rfl
  · rw [← BitVec.and_assoc, BitVec.and_self]
  · rw [BitVec.and_comm (evX ρ B0 t c), ← BitVec.and_assoc, BitVec.and_self]

theorem evX_and_absorb' {t : IntType} {a b r : XT} (h : absorb .and b a = some r) :
    evX ρ B0 t r = evX ρ B0 t (.bin .and a b) := by
  rw [evX_and_absorb h]
  simp only [evX, binV, intBinOp, BitVec.and_comm]

theorem evX_or_absorb {t : IntType} {a b r : XT} (h : absorb .or a b = some r) :
    evX ρ B0 t r = evX ρ B0 t (.bin .or a b) := by
  obtain ⟨c, d, rfl, hc, rfl⟩ := absorb_spec h
  simp only [evX, binV, intBinOp]
  rcases hc with rfl | rfl
  · rw [← BitVec.or_assoc, BitVec.or_self]
  · rw [BitVec.or_comm (evX ρ B0 t c), ← BitVec.or_assoc, BitVec.or_self]

theorem evX_or_absorb' {t : IntType} {a b r : XT} (h : absorb .or b a = some r) :
    evX ρ B0 t r = evX ρ B0 t (.bin .or a b) := by
  rw [evX_or_absorb h]
  simp only [evX, binV, intBinOp, BitVec.or_comm]

theorem evX_cancelX {t : IntType} {a b r : XT} (h : cancelX a b = some r) :
    evX ρ B0 t r = evX ρ B0 t (.bin .xor a b) := by
  obtain ⟨c, d, rfl, hc⟩ := cancelX_spec h
  simp only [evX, binV, intBinOp]
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · rw [BitVec.xor_comm (evX ρ B0 t r), ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem evX_cancelX' {t : IntType} {a b r : XT} (h : cancelX b a = some r) :
    evX ρ B0 t r = evX ρ B0 t (.bin .xor a b) := by
  rw [evX_cancelX h]
  simp only [evX, binV, intBinOp, BitVec.xor_comm]

theorem pow2?_spec {t : IntType} {b : XT} {k : Nat} (h : pow2? t b = some k) :
    ∃ c, b = .const c ∧ 0 < k ∧ k < t.width ∧ 2 ^ k = c % 2 ^ t.width := by
  unfold pow2? at h
  split at h
  · rename_i c
    simp only at h
    split at h
    · rename_i hk
      obtain rfl := Option.some.inj h
      exact ⟨c, rfl, hk.1, hk.2.1, hk.2.2⟩
    · cases h
  · cases h

theorem evX_div_pow2 {t : IntType} {a b : XT} {k : Nat} (h : pow2? t b = some k) :
    evX ρ B0 t (.bin (.shr .unsigned) a (.const k)) = evX ρ B0 t (.bin (.div .unsigned) a b) := by
  obtain ⟨c, rfl, hk0, hkw, hkc⟩ := pow2?_spec h
  have hw : t.width < 2 ^ t.width := Nat.lt_two_pow_self
  have hb : BitVec.ofNat t.width c = BitVec.twoPow t.width k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_twoPow, ← hkc, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right
      (by decide) hkw)]
  have hne : BitVec.twoPow t.width k ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hkw)] at this
    simp at this
  have hk2 : k < 2 ^ t.width := Nat.lt_trans hkw hw
  have hkn : (BitVec.ofNat t.width k).toNat % t.width = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2, Nat.mod_eq_of_lt hkw]
  simp only [evX, binV, intBinOp, hb, hne, ↓reduceIte, hkn, BitVec.udiv_twoPow_eq_of_lt hkw]

/-! ## Associative commutative chains -/

/-- The unit of `add` (`0`) and `mul` (`1`). -/
def unitOf (t : IntType) : IntBinOp → BitVec t.width
  | .mul => 1
  | _ => 0

/-- The laws of an associative commutative operator with a unit. -/
structure ACLaws (t : IntType) (op : IntBinOp) : Prop where
  assoc : ∀ x y z, binV t op (binV t op x y) z = binV t op x (binV t op y z)
  comm : ∀ x y, binV t op x y = binV t op y x
  unit : ∀ x, binV t op x (unitOf t op) = x

theorem acLaws_add (t : IntType) : ACLaws t .add where
  assoc x y z := by simp only [binV, intBinOp, BitVec.add_assoc]
  comm x y := by simp only [binV, intBinOp, BitVec.add_comm]
  unit x := by simp only [binV, intBinOp, unitOf]; exact BitVec.add_zero x

theorem acLaws_mul (t : IntType) : ACLaws t .mul where
  assoc x y z := by simp only [binV, intBinOp, BitVec.mul_assoc]
  comm x y := by simp only [binV, intBinOp, BitVec.mul_comm]
  unit x := by simp only [binV, intBinOp, unitOf]; exact BitVec.mul_one x

/-- The value of a list of operands combined by `op`. -/
def acVal (t : IntType) (op : IntBinOp) (l : List XT) : BitVec t.width :=
  l.foldr (fun x acc => binV t op (evX ρ B0 t x) acc) (unitOf t op)

theorem foldr_acc {t : IntType} {op : IntBinOp} (hl : ACLaws t op) (y : BitVec t.width) :
    ∀ l : List XT, l.foldr (fun x acc => binV t op (evX ρ B0 t x) acc) y =
      binV t op (acVal (ρ := ρ) (B0 := B0) t op l) y
  | [] => by simp only [List.foldr_nil, acVal]; rw [hl.comm, hl.unit]
  | x :: l => by
    simp only [List.foldr_cons, acVal] at *
    rw [foldr_acc hl y l, hl.assoc]
    rfl

theorem acVal_append {t : IntType} {op : IntBinOp} (hl : ACLaws t op) (l₁ l₂ : List XT) :
    acVal (ρ := ρ) (B0 := B0) t op (l₁ ++ l₂) =
      binV t op (acVal (ρ := ρ) (B0 := B0) t op l₁) (acVal (ρ := ρ) (B0 := B0) t op l₂) := by
  simp only [acVal, List.foldr_append]
  exact foldr_acc hl _ l₁

theorem acVal_leaves {t : IntType} {op : IntBinOp} (hl : ACLaws t op) :
    ∀ e : XT, acVal (ρ := ρ) (B0 := B0) t op (leaves op e) = evX ρ B0 t e := by
  intro e
  cases e with
  | bin op' a b =>
    simp only [leaves]
    split
    · rename_i h
      subst h
      rw [acVal_append hl, acVal_leaves hl a, acVal_leaves hl b]
      rfl
    · simp only [acVal, List.foldr_cons, List.foldr_nil, hl.unit]
  | _ => simp only [leaves, acVal, List.foldr_cons, List.foldr_nil, hl.unit]

theorem acVal_chain {t : IntType} {op : IntBinOp} (hl : ACLaws t op) :
    ∀ l : List XT, l ≠ [] → evX ρ B0 t (chain op l) = acVal (ρ := ρ) (B0 := B0) t op l
  | [], h => absurd rfl h
  | [x], _ => by simp only [chain, acVal, List.foldr_cons, List.foldr_nil, hl.unit]
  | x :: y :: ys, _ => by
    simp only [chain]
    show binV t op (evX ρ B0 t x) (evX ρ B0 t (chain op (y :: ys))) = _
    rw [acVal_chain hl (y :: ys) (List.cons_ne_nil _ _)]
    rfl

theorem insLe_perm (x : XT) : ∀ l : List XT, (insLe x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    simp only [insLe]
    split
    · exact List.Perm.refl _
    · exact ((insLe_perm x ys).cons y).trans (List.Perm.swap x y ys)

theorem sortLe_perm : ∀ l : List XT, (sortLe l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insLe_perm x (sortLe xs)).trans ((sortLe_perm xs).cons x)

theorem acVal_perm {t : IntType} {op : IntBinOp} (hl : ACLaws t op) {l₁ l₂ : List XT}
    (p : l₁.Perm l₂) : acVal (ρ := ρ) (B0 := B0) t op l₁ = acVal (ρ := ρ) (B0 := B0) t op l₂ := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp only [acVal, List.foldr_cons] at *; rw [ih]
  | swap x y l =>
    simp only [acVal, List.foldr_cons]
    rw [← hl.assoc, hl.comm (evX ρ B0 t y), hl.assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem leaves_ne_nil (op : IntBinOp) : ∀ e : XT, leaves op e ≠ [] := by
  intro e
  cases e with
  | bin op' a b =>
    simp only [leaves]
    split
    · simp [leaves_ne_nil op a]
    · simp
  | _ => simp [leaves]

/-- **An associative commutative chain preserves values.** -/
theorem evX_mkAC {t : IntType} {op : IntBinOp} (hl : ACLaws t op) (a b : XT) :
    evX ρ B0 t (mkAC op a b) = evX ρ B0 t (.bin op a b) := by
  have hne : sortLe (leaves op a ++ leaves op b) ≠ [] := by
    intro h
    have := (sortLe_perm (leaves op a ++ leaves op b)).length_eq
    rw [h] at this
    have h₁ := leaves_ne_nil op a
    simp only [List.length_nil, List.length_append] at this
    exact h₁ (List.eq_nil_of_length_eq_zero (by omega))
  rw [mkAC, acVal_chain hl _ hne, acVal_perm hl (sortLe_perm _), acVal_append hl,
    acVal_leaves hl, acVal_leaves hl]
  rfl

/-- **`mkBin2` preserves values.** -/
theorem evX_mkBin2 (t : IntType) (op : IntBinOp) (a b : XT) :
    evX ρ B0 t (mkBin2 t op a b) = evX ρ B0 t (.bin op a b) := by
  unfold mkBin2
  split
  · rename_i s
    split
    · rename_i hb
      cases b with
      | rel t' op' c d =>
        simp only [evX]
        exact (binV_rem_rel (rel_cases t t' op' c d)).symm
      | _ => simp [isRel] at hb
    · rfl
  · split
    · rename_i ha
      simp only [evX, evX_zeroC ha, binV, intBinOp]
      exact (BitVec.zero_shiftLeft _).symm
    · rfl
  · rename_i s
    split
    · rename_i ha
      cases s <;> simp only [evX, evX_zeroC ha, binV, intBinOp]
      · exact BitVec.zero_sshiftRight.symm
      · exact BitVec.zero_ushiftRight.symm
    · rfl
  · split
    · rename_i hab
      subst hab
      simp only [evX, binV, intBinOp, BitVec.and_self]
    · cases h₁ : absorb .and a b with
      | some r => exact evX_and_absorb h₁
      | none =>
        cases h₂ : absorb .and b a with
        | some r => exact evX_and_absorb' h₂
        | none => rfl
  · split
    · rename_i hab
      subst hab
      simp only [evX, binV, intBinOp, BitVec.or_self]
    · cases h₁ : absorb .or a b with
      | some r => exact evX_or_absorb h₁
      | none =>
        cases h₂ : absorb .or b a with
        | some r => exact evX_or_absorb' h₂
        | none => rfl
  · split
    · rename_i hab
      subst hab
      simp only [evX, binV, intBinOp, BitVec.xor_self]
    · cases h₁ : cancelX a b with
      | some r => exact evX_cancelX h₁
      | none =>
        cases h₂ : cancelX b a with
        | some r => exact evX_cancelX' h₂
        | none => rfl
  · split
    · rename_i k hk
      exact evX_div_pow2 hk
    · rfl
  · exact evX_mkAC (acLaws_add t) a b
  · exact evX_mkAC (acLaws_mul t) a b
  · rfl

theorem reflRel_val (t t' : IntType) (op : IntRelOp) (x : BitVec t'.width) :
    (intRelOp t' op x x).setWidth t.width = BitVec.ofNat t.width (reflRel op) := by
  cases op <;> (try rename_i s; cases s) <;>
    simp [intRelOp, bool32, reflRel, setWidth_one]

/-- **`mkRel2` preserves values.** -/
theorem evX_mkRel2 (t t' : IntType) (op : IntRelOp) (a b : XT) :
    evX ρ B0 t (mkRel2 t' op a b) = evX ρ B0 t (.rel t' op a b) := by
  unfold mkRel2
  split
  · rename_i hab
    subst hab
    simp only [evX]
    exact (reflRel_val t t' op _).symm
  · split
    · split
      · rename_i hb
        simp [evX, evX_zeroC hb, intRelOp, bool32]
      · rfl
    · rfl

/-- **The second simplifier preserves values.** -/
theorem evX_simp2 : ∀ (e : XT) (t : IntType), evX ρ B0 t (simp2 t e) = evX ρ B0 t e := by
  intro e
  induction e with
  | un op a ih => intro t; simp only [simp2, evX, ih]
  | bin op a b iha ihb => intro t; rw [simp2, evX_mkBin2]; simp only [evX, iha, ihb]
  | rel t' op a b iha ihb => intro t; rw [simp2, evX_mkRel2]; simp only [evX, iha, ihb]
  | wrap a ih => intro t; simp only [simp2, evX, ih]
  | ext sx a ih => intro t; simp only [simp2, evX, ih]
  | sel c a b ihc iha ihb => intro t; simp only [simp2, evX, ihc, iha, ihb]
  | var n => intro t; rfl
  | const c => intro t; rfl
  | load m t' p a arg _ _ => intro t; rfl
  | minit => intro t; rfl
  | mstore m t' p a arg v _ _ _ => intro t; rfl

theorem evX_simpRound (t : IntType) (e : XT) : evX ρ B0 t (simpRound t e) = evX ρ B0 t e := by
  rw [simpRound, evX_canon, evX_simp2]

/-- **The combined simplifier preserves values.** -/
theorem evX_canon2 (t : IntType) (e : XT) : evX ρ B0 t (canon2 t e) = evX ρ B0 t e := by
  rw [canon2, evX_simpRound, evX_simpRound, evX_canon]

theorem map_denX_slots2 (ρ : Env) (B0 : ByteArray) (l : List (IntType × XT)) :
    (slots2 l).map (denX ρ B0) = l.map (denX ρ B0) := by
  simp [slots2, denX, evX_canon2]

/-! ## Guards -/

/-- **A guard and its key hold together.** -/
theorem holds_gkey (g : Guard) : (gkey g).holds ρ B0 = g.holds ρ B0 := by
  cases g with
  | inb a arg n => simp only [gkey, Guard.holds, evX_canon2]
  | binOk t op a b =>
    by_cases hop : nzOp op = true
    · simp only [gkey, hop, ↓reduceIte, Guard.holds, evX_canon2]
      by_cases hy : evX ρ B0 t b = 0 <;>
        cases op <;> (try rename_i s; cases s) <;> simp_all [nzOp, intBinOp]
    · simp only [gkey, hop, Bool.false_eq_true, ↓reduceIte, Guard.holds, evX_canon2]

/-- **A dead guard never holds.** -/
theorem holds_of_gdead {g : Guard} (h : gdead g = true) : g.holds ρ B0 = false := by
  cases g with
  | inb a arg n => simp [gdead] at h
  | binOk t op a b =>
    simp only [gdead, Bool.and_eq_true] at h
    obtain ⟨hop, hz⟩ := h
    have hb : evX ρ B0 t b = 0 := by rw [← evX_canon2 t b]; exact evX_zeroC hz
    cases op <;> (try rename_i s; cases s) <;> simp only [isDivRem, Bool.false_eq_true] at hop <;>
      simp [Guard.holds, intBinOp, hb]

end Silmaril.Wasm.Auto2.Summ
