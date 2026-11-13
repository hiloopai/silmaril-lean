module

public import Silmaril.Proofs.Wasm.LimeCompile.PassiveData.Run

/-!
# The passive-data container: symbolic execution of straight-line code

`sexec F rs code` runs straight-line code made of constants, `local.get`, `i32`/`i64` binary and
relational operators, `i64.extend_i32_u` and the untyped `select` on a reversed value stack `rs`
(top first), in frame `F`. `sexec_sound` turns a successful run into Core 3.0 `Steps`, so a
straight-line segment of the helper is one lemma application plus a definitional computation.

* `chainVal`: the value the `select` chain leaves; `sexec_chain` runs the chain;
* `chainVal_get`: on a byte list shorter than `2 ^ 32`, the chain started at 0 with
  accumulator 0 returns the byte at position `j`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.PassiveData

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.LimeCompile.PassiveData

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Symbolic execution of straight-line code on a reversed stack. -/
def sexec (F : Frame) : List Val → List Instr → Option (List Val)
  | rs, [] => some rs
  | rs, .intConst it c :: is => sexec F (.num ⟨.int it, c⟩ :: rs) is
  | rs, .localGet x :: is =>
    match F.local? x with
    | some (some v) => sexec F (v :: rs) is
    | _ => none
  | .num ⟨.int .i32, y⟩ :: .num ⟨.int .i32, x⟩ :: rs, .intBinOp .i32 op :: is =>
    match intBinOp .i32 op x y with
    | .ok z => sexec F (I32 z :: rs) is
    | .error _ => none
  | .num ⟨.int .i64, y⟩ :: .num ⟨.int .i64, x⟩ :: rs, .intBinOp .i64 op :: is =>
    match intBinOp .i64 op x y with
    | .ok z => sexec F (I64 z :: rs) is
    | .error _ => none
  | .num ⟨.int .i32, y⟩ :: .num ⟨.int .i32, x⟩ :: rs, .intRelOp .i32 op :: is =>
    sexec F (I32 (intRelOp .i32 op x y) :: rs) is
  | .num ⟨.int .i64, y⟩ :: .num ⟨.int .i64, x⟩ :: rs, .intRelOp .i64 op :: is =>
    sexec F (I32 (intRelOp .i64 op x y) :: rs) is
  | .num ⟨.int .i32, x⟩ :: rs, .convert (.extend .unsigned) :: is =>
    sexec F (I64 (x.setWidth 64) :: rs) is
  | .num ⟨.int .i32, c⟩ :: b :: a :: rs, .select none :: is =>
    sexec F ((if c = 0 then b else a) :: rs) is
  | _, _ => none

/-- `sexec` is sound for the code `is`: every successful run is a Core run. -/
def SoundFor (P : Profile) (host : HostSemantics H) (t : Store H) (F : Frame)
    (is : List Instr) : Prop :=
  ∀ (rs rs' : List Val) (rest : List Admin), sexec F rs is = some rs' →
    Steps P host ⟨t, F, vals rs.reverse ++ (expression is ++ rest)⟩ ⟨t, F, vals rs'.reverse ++ rest⟩

/-- One arm of the soundness induction: a step for the head, then the run of the tail. -/
theorem arm {t : Store H} {F : Frame} {i i' : Instr} {is is' : List Instr}
    {rs rs₁ rs' : List Val} {rest : List Admin} (ih : SoundFor P host t F is)
    (heq : i :: is = i' :: is')
    (hstep : Steps P host ⟨t, F, vals rs.reverse ++ (.plain i' :: (expression is' ++ rest))⟩
      ⟨t, F, vals rs₁.reverse ++ (expression is' ++ rest)⟩)
    (h : sexec F rs₁ is' = some rs') :
    Steps P host ⟨t, F, vals rs.reverse ++ (expression (i :: is) ++ rest)⟩
      ⟨t, F, vals rs'.reverse ++ rest⟩ := by
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  exact hstep.trans (ih _ _ _ h)

theorem st_const {t : Store H} {F : Frame} {rs : List Val} {R : List Admin} (it : IntType)
    (c : BitVec it.width) :
    Steps P host ⟨t, F, vals rs.reverse ++ (.plain (.intConst it c) :: R)⟩
      ⟨t, F, vals (.num ⟨.int it, c⟩ :: rs).reverse ++ R⟩ := by
  simpa using r_const (P := P) (host := host) (t := t) (F := F) (vs := rs.reverse) (rest := R) it c

theorem st_localGet {t : Store H} {F : Frame} {rs : List Val} {R : List Admin} {x : LocalIdx}
    {v : Val} (hv : F.local? x = some (some v)) :
    Steps P host ⟨t, F, vals rs.reverse ++ (.plain (.localGet x) :: R)⟩
      ⟨t, F, vals (v :: rs).reverse ++ R⟩ := by
  simpa using r_localGet (P := P) (host := host) (t := t) (vs := rs.reverse) (rest := R) hv

theorem st_binop {t : Store H} {F : Frame} {rs : List Val} {R : List Admin} {it : IntType}
    {op : IntBinOp} {x y z : BitVec it.width} (hz : intBinOp it op x y = .ok z) :
    Steps P host ⟨t, F, vals (.num ⟨.int it, y⟩ :: .num ⟨.int it, x⟩ :: rs).reverse ++
        (.plain (.intBinOp it op) :: R)⟩
      ⟨t, F, vals (.num ⟨.int it, z⟩ :: rs).reverse ++ R⟩ := by
  simpa using r_binop (P := P) (host := host) (t := t) (F := F) (vs := rs.reverse) (rest := R) hz

theorem st_relop {t : Store H} {F : Frame} {rs : List Val} {R : List Admin} (it : IntType)
    (op : IntRelOp) (x y : BitVec it.width) :
    Steps P host ⟨t, F, vals (.num ⟨.int it, y⟩ :: .num ⟨.int it, x⟩ :: rs).reverse ++
        (.plain (.intRelOp it op) :: R)⟩
      ⟨t, F, vals (I32 (intRelOp it op x y) :: rs).reverse ++ R⟩ := by
  simpa using r_relop (P := P) (host := host) (t := t) (F := F) (vs := rs.reverse) (rest := R) op x y

theorem st_extend {t : Store H} {F : Frame} {rs : List Val} {R : List Admin} (x : BitVec 32) :
    Steps P host ⟨t, F, vals (I32 x :: rs).reverse ++
        (.plain (.convert (.extend .unsigned)) :: R)⟩
      ⟨t, F, vals (I64 (x.setWidth 64) :: rs).reverse ++ R⟩ := by
  simpa using r_extend (P := P) (host := host) (t := t) (F := F) (vs := rs.reverse) (rest := R) x

theorem st_select {t : Store H} {F : Frame} {rs : List Val} {R : List Admin} (a b : Val)
    (c : BitVec 32) :
    Steps P host ⟨t, F, vals (I32 c :: b :: a :: rs).reverse ++ (.plain (.select none) :: R)⟩
      ⟨t, F, vals ((if c = 0 then b else a) :: rs).reverse ++ R⟩ := by
  simpa using r_select (P := P) (host := host) (t := t) (F := F) (vs := rs.reverse) (rest := R) a b c

theorem soundFor_nil {t : Store H} {F : Frame} : SoundFor P host t F [] := by
  intro rs rs' rest h
  have hr : rs = rs' := Option.some.inj h
  rw [← hr]
  exact .refl

theorem arm_localGet {t : Store H} {F : Frame} {i : Instr} {x : LocalIdx} {is is' : List Instr}
    {rs rs' : List Val} {rest : List Admin} (ih : SoundFor P host t F is)
    (heq : i :: is = .localGet x :: is')
    (h : (match F.local? x with
      | some (some v) => sexec F (v :: rs) is'
      | _ => none) = some rs') :
    Steps P host ⟨t, F, vals rs.reverse ++ (expression (i :: is) ++ rest)⟩
      ⟨t, F, vals rs'.reverse ++ rest⟩ := by
  split at h
  next _ hv => exact arm ih heq (st_localGet hv) h
  next => simp at h

theorem arm_bin32 {t : Store H} {F : Frame} {i : Instr} {op : IntBinOp} {x y : BitVec 32}
    {is is' : List Instr} {rs₀ rs' : List Val} {rest : List Admin}
    (ih : SoundFor P host t F is) (heq : i :: is = .intBinOp .i32 op :: is')
    (h : (match intBinOp .i32 op x y with
      | .ok z => sexec F (I32 z :: rs₀) is'
      | .error _ => none) = some rs') :
    Steps P host ⟨t, F, vals (I32 y :: I32 x :: rs₀).reverse ++ (expression (i :: is) ++ rest)⟩
      ⟨t, F, vals rs'.reverse ++ rest⟩ := by
  split at h
  next _ hz => exact arm ih heq (st_binop hz) h
  next => simp at h

theorem arm_bin64 {t : Store H} {F : Frame} {i : Instr} {op : IntBinOp} {x y : BitVec 64}
    {is is' : List Instr} {rs₀ rs' : List Val} {rest : List Admin}
    (ih : SoundFor P host t F is) (heq : i :: is = .intBinOp .i64 op :: is')
    (h : (match intBinOp .i64 op x y with
      | .ok z => sexec F (I64 z :: rs₀) is'
      | .error _ => none) = some rs') :
    Steps P host ⟨t, F, vals (I64 y :: I64 x :: rs₀).reverse ++ (expression (i :: is) ++ rest)⟩
      ⟨t, F, vals rs'.reverse ++ rest⟩ := by
  split at h
  next _ hz => exact arm ih heq (st_binop hz) h
  next => simp at h

theorem sexec_sound {t : Store H} {F : Frame} :
    ∀ (code : List Instr), SoundFor P host t F code := by
  intro code
  induction code with
  | nil => exact soundFor_nil
  | cons i is ih =>
    intro rs rs' rest h
    rw [sexec.eq_def] at h
    split at h
    next _ _ _ heq => exact absurd heq (by simp)
    next _ _ _ it c _ heq => exact arm ih heq (st_const it c) h
    next _ _ _ _ _ heq => exact arm_localGet ih heq h
    next _ _ _ _ _ _ _ heq => exact arm_bin32 ih heq h
    next _ _ _ _ _ _ _ heq => exact arm_bin64 ih heq h
    next _ _ y x _ op _ heq => exact arm ih heq (st_relop .i32 op x y) h
    next _ _ y x _ op _ heq => exact arm ih heq (st_relop .i64 op x y) h
    next _ _ x _ _ heq => exact arm ih heq (st_extend x) h
    next _ _ c b a _ _ heq => exact arm ih heq (st_select a b c) h
    next => simp at h

/-! ## The byte lookup -/

/-- The value the `select` chain leaves, from accumulator `acc`, for `j`, over bytes from
position `k`. -/
def chainVal (j : BitVec 32) : BitVec 32 → List UInt8 → Nat → BitVec 32
  | acc, [], _ => acc
  | acc, b :: bs, k =>
    chainVal j (if j - BitVec.ofNat 32 k = 0 then BitVec.ofNat 32 b.toNat
      else acc) bs (k + 1)

theorem sexec_chain {F : Frame} {j : BitVec 32} (hj : F.local? (idx 1) = some (some (I32 j))) :
    ∀ (bs : List UInt8) (k : Nat) (acc : BitVec 32) (rs : List Val) (is : List Instr),
      sexec F (I32 acc :: rs) (chain bs k ++ is) = sexec F (I32 (chainVal j acc bs k) :: rs) is := by
  intro bs
  induction bs with
  | nil => intro k acc rs is; rfl
  | cons b bs ih =>
    intro k acc rs is
    simp only [chain, List.cons_append, List.nil_append, sexec, byteConst, hj, chainVal, intBinOp]
    split <;> split <;> first | exact ih _ _ _ _ | (rename_i h1 h2; exact absurd h1 h2) |
      (rename_i h1 h2; exact absurd h2 h1)

theorem bv_sub_eq_zero (x y : BitVec 32) : x - y = 0 ↔ x = y := sub_eq_zero

theorem chainVal_past {j : BitVec 32} :
    ∀ (bs : List UInt8) (acc : BitVec 32) (k : Nat), j.toNat < k → k + bs.length ≤ 2 ^ 32 →
      chainVal j acc bs k = acc := by
  intro bs
  induction bs with
  | nil => intro acc k _ _; rfl
  | cons b bs ih =>
    intro acc k hk hb
    simp only [List.length_cons] at hb
    have hne : j ≠ BitVec.ofNat 32 k := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    simp only [chainVal]
    have hc : ¬ j - BitVec.ofNat 32 k = 0 := by
      rw [bv_sub_eq_zero]; exact hne
    simp only [hc, ↓reduceIte]
    exact ih acc (k + 1) (by omega) (by omega)

theorem chainVal_hit {j : BitVec 32} {b : UInt8} {bs : List UInt8} {acc : BitVec 32} {k : Nat}
    (hjk : j.toNat = k) (hb : k + 1 + bs.length ≤ 2 ^ 32) :
    chainVal j acc (b :: bs) k = BitVec.ofNat 32 b.toNat := by
  have hj : j = BitVec.ofNat 32 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hjk
  have hz : j - BitVec.ofNat 32 k = 0 := (bv_sub_eq_zero _ _).mpr hj
  show chainVal j (if j - BitVec.ofNat 32 k = 0 then BitVec.ofNat 32 b.toNat else acc) bs (k + 1) =
    BitVec.ofNat 32 b.toNat
  simp only [hz, ↓reduceIte]
  exact chainVal_past bs _ (k + 1) (by omega) (by omega)

theorem chainVal_miss {j : BitVec 32} {b : UInt8} {bs : List UInt8} {acc : BitVec 32} {k : Nat}
    (hjk : j.toNat ≠ k) (hk : k < 2 ^ 32) :
    chainVal j acc (b :: bs) k = chainVal j acc bs (k + 1) := by
  have hne : j ≠ BitVec.ofNat 32 k := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
    exact hjk this
  have hc : ¬ j - BitVec.ofNat 32 k = 0 := by
    rw [bv_sub_eq_zero]; exact hne
  show chainVal j (if j - BitVec.ofNat 32 k = 0 then BitVec.ofNat 32 b.toNat else acc) bs (k + 1) =
    chainVal j acc bs (k + 1)
  simp only [hc, ↓reduceIte]

theorem chainVal_get {j : BitVec 32} {byte : UInt8} :
    ∀ (bs : List UInt8) (acc : BitVec 32) (k : Nat), k ≤ j.toNat → k + bs.length ≤ 2 ^ 32 →
      bs[j.toNat - k]? = some byte → chainVal j acc bs k = BitVec.ofNat 32 byte.toNat := by
  intro bs
  induction bs with
  | nil => intro acc k _ _ h; simp at h
  | cons b bs ih =>
    intro acc k hk hb hget
    have hb' : k + 1 + bs.length ≤ 2 ^ 32 := by simpa [Nat.add_assoc, Nat.add_comm 1] using hb
    by_cases hjk : j.toNat = k
    · have h0 : j.toNat - k = 0 := by omega
      have hbyte : b = byte := by simpa [h0] using hget
      rw [chainVal_hit hjk hb', hbyte]
    · have h1 : j.toNat - k = (j.toNat - (k + 1)) + 1 := by omega
      have hget' : bs[j.toNat - (k + 1)]? = some byte := by simpa [h1] using hget
      rw [chainVal_miss hjk (by omega)]
      exact ih acc (k + 1) (by omega) (by omega) hget'

end Silmaril.Proofs.Wasm.LimeCompile.PassiveData
