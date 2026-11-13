module

public import Silmaril.Compiler.Mir.DeadCode.Defs
/-! # Strength reduction on Mir

`StrengthReduce.run` rewrites, in each function, the operations by a power of two whose
divisor or factor is loaded by the instruction just before them:

* `c := 2^k; d := a * c` becomes `c := k; d := a << c`;
* `c := 2^k; d := a /u c` becomes `c := k; d := a >>u c`;
* `c := 2^k; d := a %u c` becomes `c := 2^k - 1; d := a & c`

(64-bit `mul`, `divu` and `remu`, `k < 64`; signed division and remainder are kept). The
pair is rewritten only when `c` is **dead before the rewritten operation** (not live after it,
and not its first operand), so no later instruction reads the changed constant.

**Liveness, checked.** As in `Mir.DeadCode`, the registers live at the start of each block
are computed by an unverified backward fixpoint (`iterate`) and checked (`check`); a function
whose certificate fails is left unchanged. The backward pass over a block (`srList`)
computes, from the registers live after each instruction, whether its pair is rewritten,
and the registers live before it: a rewritten operation does not read its constant
(`liveOp`).

**Simulation.** Every instruction stays at its index. An input point `(l, i)` is related to
the output point `(l, i)` with frames that have the same slots and agree on the registers
live there, and, when instruction `i` is a rewritten operation, hold `2^k` and its
replacement in `c` (`SRel`). Each rewritten operation computes the same `Binop.eval` result
(`reduce_eval`: `x * 2^k = x << k`, `x /u 2^k = x >>u k`, `x %u 2^k = x & (2^k - 1)`), every
other instruction runs the same on agreeing frames (`DeadCode.op_agree`). `StrengthReduce.correct`
proves `Contract.mirPass` through `FuncPass.mirPass`. -/

@[expose] public section

namespace Silmaril.Compile.Mir.StrengthReduce

open Silmaril.Machine
open Silmaril.Compile.Mir.FuncPass
open Silmaril.Compile.Mir.DeadCode

/-! ## The rewrite -/

/-- `k` when `v = 2^k` with `k < 64`. -/
def pow2 (v : Lir.Word) : Option Nat :=
  if v.toNat.log2 < 64 ∧ v = BitVec.twoPow 64 v.toNat.log2 then some v.toNat.log2 else none

/-- The operator and the constant that replace `op` with the constant operand `v`. -/
def reduce : Lir.Binop → Lir.Word → Option (Lir.Binop × Lir.Word)
  | .mul, v => (pow2 v).map fun k => (.shl, BitVec.ofNat 64 k)
  | .divu, v => (pow2 v).map fun k => (.shru, BitVec.ofNat 64 k)
  | .remu, v => (pow2 v).map fun _ => (.and, v - 1)
  | _, _ => none

/-- A rewritable pair: the constant register, its constant, and their replacements. -/
structure Pat where
  reg : Nat
  val : Lir.Word
  op : Lir.Binop
  val' : Lir.Word

/-- The pair ending at instruction `i` of a block: `const c v` at `i - 1`, an operation with
second operand `c` at `i`, and `reduce` applies. -/
def patAt (b : Block) : Nat → Option Pat
  | 0 => none
  | i + 1 =>
    match b.instrs[i]?, b.instrs[i + 1]? with
    | some (.op (.const c v)), some (.op (.binary op _ _ c')) =>
      if c = c' then (reduce op v).map fun p => ⟨c, v, p.1, p.2⟩ else none
    | _, _ => none


/-- The pair whose operation is `x`, instruction `i` of a block, when its constant register
is dead before the rewritten operation (`L`: the registers live after it). -/
def actOf (b : Block) (i : Nat) (L : RSet) : Instr → Option Pat
  | .op (.binary _ d a c) =>
    match patAt b i with
    | some p => if c = p.reg ∧ ((L.erase d).insert a).testBit p.reg = false then some p else none
    | none => none
  | _ => none

/-- The constant of a rewritten pair. -/
def rwConst (p : Pat) : Instr → Instr
  | .op (.const c _) => .op (.const c p.val')
  | x => x

/-- The operation of a rewritten pair. -/
def rwOp (p : Pat) : Instr → Instr
  | .op (.binary _ d a c) => .op (.binary p.op d a c)
  | x => x

/-- The registers live before a rewritten operation: it no longer needs its constant. -/
def liveOp (L : RSet) : Instr → RSet
  | .op (.binary _ d a _) => (L.erase d).insert a
  | x => instrLive L x

/-- Backward over the instructions of a block from index `i`, from the registers `L` live
after them: the rewritten instructions, the registers live before them, and the rewritten
pair whose operation is the first of them. -/
def srList (b : Block) (L : RSet) : Nat → List Instr → List Instr × RSet × Option Pat
  | _, [] => ([], L, none)
  | i, x :: xs =>
    let r := srList b L (i + 1) xs
    match r.2.2 with
    | some p => (rwConst p x :: r.1, instrLive r.2.1 x, none)
    | none =>
      match actOf b i r.2.1 x with
      | some p => (rwOp p x :: r.1, liveOp r.2.1 x, some p)
      | none => (x :: r.1, instrLive r.2.1 x, none)

/-- The registers live at the start of a block, from the claimed sets of its successors. -/
def blockLive (cert : Array RSet) (b : Block) : RSet := (srList b (liveEnd cert b) 0 b.instrs.toList).2.1

/-- One backward sweep over the blocks, last first. -/
def sweep (f : Func) (cert : Array RSet) : Array RSet :=
  (List.range f.blocks.size).foldr (fun l c =>
    match f.blocks[l]? with
    | some b => c.set! l (blockLive c b ||| c.getD l 0)
    | none => c) cert

/-- The fixpoint iteration (unverified; `check` validates its result). -/
def iterate (f : Func) : Nat → Array RSet → Array RSet
  | 0, cert => cert
  | fuel + 1, cert =>
    let cert' := sweep f cert
    if cert' == cert then cert else iterate f fuel cert'

/-- The claimed live registers at the start of each block. -/
def certOf (f : Func) : Array RSet := iterate f 64 (Array.replicate f.blocks.size 0)

/-- The certificate covers every block. -/
def check (cert : Array RSet) (f : Func) : Bool :=
  (List.range f.blocks.size).all fun l =>
    match f.blocks[l]? with
    | some b => RSet.subset (blockLive cert b) (cert.getD l 0)
    | none => true

def srBlock (cert : Array RSet) (b : Block) : Block :=
  ⟨(srList b (liveEnd cert b) 0 b.instrs.toList).1.toArray, b.term⟩

/-- The pass on one function: the pairs rewritten when the liveness certificate checks,
otherwise the function unchanged. -/
def srFunc (f : Func) : Func :=
  let cert := certOf f
  if check cert f then { f with blocks := f.blocks.map (srBlock cert) } else f

/-- The pass on units. -/
def run : Array Mir.Unit → Array Mir.Unit := mapFuncs srFunc

/-! ## The identities -/

theorem pow2_spec {v : Lir.Word} {k : Nat} (h : pow2 v = some k) : k < 64 ∧ v = BitVec.twoPow 64 k := by
  unfold pow2 at h
  split at h
  · cases h; assumption
  · cases h

theorem twoPow_ne {k : Nat} (hk : k < 64) : BitVec.twoPow 64 k ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_twoPow_of_lt hk] at this
  simp at this

theorem shift_amount {k : Nat} (hk : k < 64) : (BitVec.ofNat 64 k).toNat % 64 = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hk (by decide)), Nat.mod_eq_of_lt hk]

theorem and_twoPow_sub_one (x : Lir.Word) {k : Nat} (hk : k < 64) :
    x &&& (BitVec.twoPow 64 k - 1) = x % BitVec.twoPow 64 k := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.twoPow 64 k).toNat = 2 ^ k := BitVec.toNat_twoPow_of_lt hk
  have h2 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h4 : (BitVec.twoPow 64 k - 1).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_sub, h1]
    show (2 ^ 64 - 1 + 2 ^ k) % 2 ^ 64 = 2 ^ k - 1
    generalize 2 ^ k = K at *
    omega
  rw [BitVec.toNat_and, h4, BitVec.toNat_umod, h1, Nat.and_two_pow_sub_one_eq_mod]

/-- **A rewritten operation computes the same value.** -/
theorem reduce_eval {op op' : Lir.Binop} {v v' x z : Lir.Word} (h : reduce op v = some (op', v'))
    (he : op.eval x v = some z) : op'.eval x v' = some z := by
  cases op <;> simp only [reduce, reduceCtorEq, Option.map_eq_some_iff, Prod.mk.injEq] at h
  · obtain ⟨k, hk, rfl, rfl⟩ := h
    obtain ⟨hk', rfl⟩ := pow2_spec hk
    simp only [Lir.Binop.eval, Option.some.injEq] at he ⊢
    rw [shift_amount hk', BitVec.shiftLeft_eq_mul_twoPow, he]
  · obtain ⟨k, hk, rfl, rfl⟩ := h
    obtain ⟨hk', rfl⟩ := pow2_spec hk
    simp only [Lir.Binop.eval, Lir.divOp, twoPow_ne hk', ↓reduceIte, Bool.false_eq_true,
      Option.some.injEq] at he ⊢
    rw [shift_amount hk', ← BitVec.udiv_twoPow_eq_of_lt hk', he]
  · obtain ⟨k, hk, rfl, rfl⟩ := h
    obtain ⟨hk', rfl⟩ := pow2_spec hk
    simp only [Lir.Binop.eval, Lir.divOp, twoPow_ne hk', ↓reduceIte, Bool.false_eq_true,
      Option.some.injEq] at he ⊢
    rw [and_twoPow_sub_one x hk', he]

theorem patAt_spec {b : Block} {i : Nat} {p : Pat} (h : patAt b i = some p) :
    ∃ j op d a, i = j + 1 ∧ b.instrs[j]? = some (.op (.const p.reg p.val)) ∧
      b.instrs[i]? = some (.op (.binary op d a p.reg)) ∧ reduce op p.val = some (p.op, p.val') := by
  cases i with
  | zero => cases h
  | succ j =>
    simp only [patAt] at h
    split at h
    · rename_i c v op d a c' h₁ h₂
      split at h
      · subst c'
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨q, hq, rfl⟩ := h
        exact ⟨j, op, d, a, rfl, h₁, h₂, hq⟩
      · cases h
    · cases h

theorem agree_set_out {L : RSet} {fr fr' : Lir.Frame Nat} (h : Agree L fr fr') {c : Nat}
    (hc : L.testBit c = false) (w w' : Lir.Word) : Agree L (fr.set c w) (fr'.set c w') := by
  refine ⟨h.1, fun r hr => ?_⟩
  by_cases hrc : r = c
  · subst hrc; rw [hc] at hr; cases hr
  · simp only [Lir.Frame.get_set, hrc, ite_false]
    exact h.2 r hr

/-! ## The backward pass -/

theorem srList_A {b : Block} {L : RSet} {i : Nat} {x : Instr} {xs : List Instr} {p : Pat}
    (h : (srList b L (i + 1) xs).2.2 = some p) :
    srList b L i (x :: xs) = (rwConst p x :: (srList b L (i + 1) xs).1,
      instrLive (srList b L (i + 1) xs).2.1 x, none) := by
  simp only [srList, h]

theorem srList_B {b : Block} {L : RSet} {i : Nat} {x : Instr} {xs : List Instr} {p : Pat}
    (h : (srList b L (i + 1) xs).2.2 = none) (ha : actOf b i (srList b L (i + 1) xs).2.1 x = some p) :
    srList b L i (x :: xs) = (rwOp p x :: (srList b L (i + 1) xs).1,
      liveOp (srList b L (i + 1) xs).2.1 x, some p) := by
  simp only [srList, h, ha]

theorem srList_C {b : Block} {L : RSet} {i : Nat} {x : Instr} {xs : List Instr}
    (h : (srList b L (i + 1) xs).2.2 = none) (ha : actOf b i (srList b L (i + 1) xs).2.1 x = none) :
    srList b L i (x :: xs) = (x :: (srList b L (i + 1) xs).1, instrLive (srList b L (i + 1) xs).2.1 x, none) := by
  simp only [srList, h, ha]

theorem srList_cons_fst (b : Block) (L : RSet) (i : Nat) (x : Instr) (xs : List Instr) :
    ∃ y, refKey y = refKey x ∧ (srList b L i (x :: xs)).1 = y :: (srList b L (i + 1) xs).1 := by
  cases h : (srList b L (i + 1) xs).2.2 with
  | some p =>
    rw [srList_A h]
    exact ⟨_, by unfold rwConst; split <;> rfl, rfl⟩
  | none =>
    cases ha : actOf b i (srList b L (i + 1) xs).2.1 x with
    | some p => rw [srList_B h ha]; exact ⟨_, by unfold rwOp; split <;> rfl, rfl⟩
    | none => rw [srList_C h ha]; exact ⟨_, rfl, rfl⟩

theorem srList_refs (b : Block) (L : RSet) (i : Nat) (xs : List Instr) :
    (srList b L i xs).1.filterMap refKey = xs.filterMap refKey := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨y, hy, e⟩ := srList_cons_fst b L i x xs
    rw [e, List.filterMap_cons, List.filterMap_cons, hy, ih]

theorem srList_length (b : Block) (L : RSet) (i : Nat) (xs : List Instr) :
    (srList b L i xs).1.length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨y, -, e⟩ := srList_cons_fst b L i x xs
    rw [e, List.length_cons, ih, List.length_cons]

theorem srList_drop (b : Block) (L : RSet) (n : Nat) :
    ∀ (k : Nat) (xs : List Instr), (srList b L k xs).1.drop n = (srList b L (k + n) (xs.drop n)).1 := by
  induction n with
  | zero => intro k xs; rfl
  | succ n ih =>
    intro k xs
    cases xs with
    | nil => rfl
    | cons x xs =>
      obtain ⟨y, -, e⟩ := srList_cons_fst b L k x xs
      rw [e, List.drop_succ_cons, ih, List.drop_succ_cons, Nat.add_right_comm, Nat.add_assoc]

theorem actOf_spec {b : Block} {i : Nat} {L : RSet} {x : Instr} {p : Pat} (h : actOf b i L x = some p) :
    patAt b i = some p ∧ ∃ op d a, x = .op (.binary op d a p.reg) ∧
      ((L.erase d).insert a).testBit p.reg = false := by
  unfold actOf at h
  split at h
  · rename_i op d a c
    split at h
    · rename_i q hq
      split at h
      · rename_i hc
        cases h
        obtain ⟨rfl, hl⟩ := hc
        exact ⟨hq, op, d, a, rfl, hl⟩
      · cases h
    · cases h
  · cases h

theorem srList_some {b : Block} {L : RSet} {k : Nat} {xs : List Instr} {p : Pat}
    (h : (srList b L k xs).2.2 = some p) : (srList b L k xs).2.1.testBit p.reg = false ∧ patAt b k = some p := by
  cases xs with
  | nil => cases h
  | cons y ys =>
    cases h₁ : (srList b L (k + 1) ys).2.2 with
    | some q => rw [srList_A h₁] at h; cases h
    | none =>
      cases ha : actOf b k (srList b L (k + 1) ys).2.1 y with
      | some q =>
        rw [srList_B h₁ ha] at h ⊢
        cases h
        obtain ⟨hp, op, d, a, rfl, hl⟩ := actOf_spec ha
        exact ⟨hl, hp⟩
      | none => rw [srList_C h₁ ha] at h; cases h

theorem srList_zero (b : Block) (L : RSet) (xs : List Instr) : (srList b L 0 xs).2.2 = none := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases h : (srList b L 1 xs).2.2 with
    | some p => rw [srList_A h]
    | none =>
      cases ha : actOf b 0 (srList b L 1 xs).2.1 x with
      | some p => have := (actOf_spec ha).1; simp [patAt] at this
      | none => rw [srList_C h ha]

/-! ## Correctness -/

theorem shape : Shape srFunc where
  name f := by simp only [srFunc]; split <;> rfl
  params f := by simp only [srFunc]; split <;> rfl
  results f := by simp only [srFunc]; split <;> rfl
  weak f := by simp only [srFunc]; split <;> rfl
  size f := by simp only [srFunc]; split <;> simp
  refs f := by
    simp only [srFunc]; split
    · simp only [funcRefs, Array.toList_map, List.flatMap_map, srBlock, List.toList_toArray, srList_refs]
    · rfl

theorem check_spec {cert : Array RSet} {f : Func} (h : check cert f = true) {l : Nat} {b : Block}
    (hb : f.blocks[l]? = some b) : RSet.subset (blockLive cert b) (cert.getD l 0) = true := by
  simp only [check, List.all_eq_true, List.mem_range] at h
  have := h l (Array.getElem?_eq_some_iff.mp hb).1
  simpa [hb] using this

/-- The relation on a checked function: the same index, frames agreeing on the registers
live there, and at a rewritten operation the constant and its replacement in its register. -/
def SRel (cert : Array RSet) (f : Func) (l i : Nat) (fr : Lir.Frame Nat) (i' : Nat) (fr' : Lir.Frame Nat) :
    Prop :=
  match f.blocks[l]? with
  | some b =>
    i' = i ∧ Agree (srList b (liveEnd cert b) i (b.instrs.toList.drop i)).2.1 fr fr' ∧
      ∀ p, (srList b (liveEnd cert b) i (b.instrs.toList.drop i)).2.2 = some p →
        fr.get p.reg = some p.val ∧ fr'.get p.reg = some p.val'
  | none => fr'.slots = fr.slots

/-- The point relation: `SRel` when the certificate checks, otherwise the identity. -/
def PR : PointRel := fun f =>
  if check (certOf f) f then SRel (certOf f) f else idRel

theorem srFunc_block {cert : Array RSet} {f : Func} {l : Nat} {b b' : Block} (hb : f.blocks[l]? = some b)
    (hb' : ({ f with blocks := f.blocks.map (srBlock cert) } : Func).blocks[l]? = some b') :
    b' = srBlock cert b := by
  simp only [Array.getElem?_map, hb, Option.map_some, Option.some.injEq] at hb'
  exact hb'.symm

theorem srBlock_get (cert : Array RSet) (b : Block) (i : Nat) :
    (srBlock cert b).instrs[i]? = (srList b (liveEnd cert b) i (b.instrs.toList.drop i)).1[0]? := by
  have := congrArg (·[0]?) (srList_drop b (liveEnd cert b) i 0 b.instrs.toList)
  simp only [List.getElem?_drop, Nat.add_zero, Nat.zero_add] at this
  simpa [srBlock] using this

theorem agree_entry {cert : Array RSet} {f : Func} (hc : check cert f = true) {l : Nat}
    {fr fr' : Lir.Frame Nat} (h : Agree (cert.getD l 0) fr fr') : SRel cert f l 0 fr 0 fr' := by
  unfold SRel
  split
  · rename_i b hb
    refine ⟨rfl, h.mono fun r hr => RSet.mem_of_subset (check_spec hc hb) ?_, fun p hp => ?_⟩
    · simpa [blockLive] using hr
    · rw [List.drop_zero, srList_zero] at hp; cases hp
  · exact h.1

theorem erase_sub {L : RSet} {d r : Nat} (hr : (L.erase d).testBit r = true) : L.testBit r = true := by
  rw [RSet.mem_erase] at hr; exact ((Bool.and_eq_true _ _).mp hr).1

theorem fsim (f : Func) (hc : check (certOf f) f = true) :
    FSim f { f with blocks := f.blocks.map (srBlock (certOf f)) } (SRel (certOf f) f) where
  entry fr := by
    unfold SRel
    split
    · exact ⟨by trivial, ⟨by trivial, fun _ _ => by trivial⟩, fun p hp => by
        rw [List.drop_zero, srList_zero] at hp; cases hp⟩
    · rfl
  instr l b b' i fr i' fr' x hb hb' hp hx := by
    obtain rfl := srFunc_block hb hb'
    simp only [SRel, hb] at hp
    obtain ⟨hi, hag, hfact⟩ := hp
    rw [hi]
    have hxs : b.instrs.toList.drop i = x :: b.instrs.toList.drop (i + 1) := by
      have hx' : b.instrs.toList[i]? = some x := by simpa using hx
      obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hx'
      rw [List.drop_eq_getElem_cons hi, hget]
    rw [hxs] at hag hfact
    rw [srBlock_get, hxs]
    have hnext : ∀ fr₂ fr₂', Agree (srList b (liveEnd (certOf f) b) (i + 1) (b.instrs.toList.drop (i + 1))).2.1 fr₂ fr₂' →
        (∀ p, (srList b (liveEnd (certOf f) b) (i + 1) (b.instrs.toList.drop (i + 1))).2.2 = some p →
          fr₂.get p.reg = some p.val ∧ fr₂'.get p.reg = some p.val') →
        SRel (certOf f) f l (i + 1) fr₂ (i + 1) fr₂' := fun fr₂ fr₂' h₁ h₂ => by
      simp only [SRel, hb]; exact ⟨trivial, h₁, h₂⟩
    generalize hR : srList b (liveEnd (certOf f) b) (i + 1) (b.instrs.toList.drop (i + 1)) = R at hnext
    cases hA : R.2.2 with
    | some p =>
      -- the constant of a rewritten pair
      have hA' : (srList b (liveEnd (certOf f) b) (i + 1) (b.instrs.toList.drop (i + 1))).2.2 = some p := by
        rw [hR, hA]
      obtain ⟨hlive, hpat⟩ := srList_some hA'
      obtain ⟨j, op, d, a, hj, hc, -, -⟩ := patAt_spec hpat
      obtain rfl : i = j := by omega
      rw [hx] at hc; cases hc
      rw [srList_A hA'] at hag ⊢
      simp only [instrLive, opDef, opUses] at hag
      have hag₁ : Agree (srList b (liveEnd (certOf f) b) (i + 1) (b.instrs.toList.drop (i + 1))).2.1 fr fr' :=
        hag.mono fun r hr => by
          have hne : r ≠ p.reg := fun e => by subst e; rw [hlive] at hr; cases hr
          rw [RSet.addAll, List.foldl_nil, RSet.mem_erase]; simp [hr, hne]
      simp only [List.getElem?_cons_zero, rwConst]
      intro m fr₁ m₁ he
      simp only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine .inr ⟨_, rfl, _, rfl, hnext _ _ ?_ fun q hq => ?_⟩
      · rw [← hR]; exact agree_set_out hag₁ hlive _ _
      · rw [hA] at hq; cases hq; simp
    | none =>
    have hA' : (srList b (liveEnd (certOf f) b) (i + 1) (b.instrs.toList.drop (i + 1))).2.2 = none := by
      rw [hR, hA]
    have hnone : ∀ fr₂ fr₂', Agree R.2.1 fr₂ fr₂' → SRel (certOf f) f l (i + 1) fr₂ (i + 1) fr₂' :=
      fun fr₂ fr₂' h => hnext fr₂ fr₂' h fun q hq => by rw [hA] at hq; cases hq
    rw [← hR] at hnone
    cases ha : actOf b i (srList b (liveEnd (certOf f) b) (i + 1) (b.instrs.toList.drop (i + 1))).2.1 x with
    | some p =>
      -- the operation of a rewritten pair
      rw [srList_B hA' ha] at hag hfact ⊢
      obtain ⟨hp, op, d, a, rfl, -⟩ := actOf_spec ha
      obtain ⟨j, op', d', a', -, -, hx', hred⟩ := patAt_spec hp
      rw [hx] at hx'
      simp only [Option.some.injEq, Instr.op.injEq, Lir.Op.binary.injEq] at hx'
      obtain ⟨rfl, -, -, -⟩ := hx'
      obtain ⟨hv, hv'⟩ := hfact p rfl
      simp only [liveOp] at hag
      simp only [List.getElem?_cons_zero, rwOp]
      intro m fr₁ m₁ he
      simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨xa, hxa, y, hy, z, hz, rfl, rfl⟩ := he
      rw [hv] at hy; cases hy
      have ha₁ : fr'.get a = fr.get a := hag.2 a (by simp [RSet.mem_insert])
      refine .inr ⟨_, rfl, fr'.set d z, ?_, hnone _ _ (Agree.set (hag.mono fun r hr => ?_) z)⟩
      · simp [Lir.Op.exec, ha₁, hxa, hv', reduce_eval hred hz]
      · simp [RSet.mem_insert, hr]
    | none =>
      -- an unchanged instruction
      rw [srList_C hA' ha] at hag ⊢
      simp only [List.getElem?_cons_zero]
      cases x with
      | op o =>
        intro m fr₁ m₁ he
        obtain ⟨fr₁', he', hag'⟩ := op_agree hag he
        exact .inr ⟨o, rfl, fr₁', he', hnone _ _ hag'⟩
      | fop op d a c =>
        intro fr₁ he
        simp only [instrLive] at hag
        refine ⟨op, d, a, c, rfl, ?_⟩
        simp only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
        obtain ⟨x, hx₁, y, hy, rfl⟩ := he
        have hc : fr'.get c = fr.get c := hag.2 c (by simp [RSet.mem_insert])
        have ha' : fr'.get a = fr.get a := hag.2 a (by simp [RSet.mem_insert])
        refine ⟨fr'.set d (op.eval x y), by simp [Lir.FOp.exec, ha', hc, hx₁, hy], hnone _ _ ?_⟩
        refine Agree.set (hag.mono fun r hr => ?_) _
        simp [RSet.mem_insert, hr]
      | addr d s off =>
        simp only [instrLive] at hag
        exact ⟨rfl, fun w => hnone _ _ (hag.set w)⟩
      | call c args res =>
        simp only [instrLive] at hag
        intro vals hv
        exact ⟨args, rfl, by rw [readAll_regs_agree hag, hv], fun vals' fr₁ fr₁' hw hw' =>
          hnone _ _ (hag.base.writeAll hw hw')⟩
      | callIndirect t args res =>
        simp only [instrLive] at hag
        intro v vals ht hv
        have ht' : fr'.get t = fr.get t := hag.2 t (by simp [RSet.mem_insert])
        have hag₂ : Agree ((((srList b (liveEnd (certOf f) b) (i + 1)
            (b.instrs.toList.drop (i + 1))).2.1).eraseAll res).addAll args) fr fr' :=
          hag.mono fun r hr => by simp [RSet.mem_insert, hr]
        refine ⟨t, args, rfl, by rw [ht', ht], by rw [readAll_regs_agree hag₂, hv],
          fun vals' fr₁ fr₁' hw hw' => hnone _ _ (hag₂.base.writeAll hw hw')⟩
  term l b b' i fr i' fr' hb hb' hp hi := by
    obtain rfl := srFunc_block hb hb'
    simp only [SRel, hb] at hp
    obtain ⟨rfl, hag, -⟩ := hp
    rw [hi, List.drop_eq_nil_of_le (as := b.instrs.toList) (by simp)] at hag
    simp only [srList] at hag
    refine ⟨by simp [srBlock, srList_length, hi], fun _ => ?_⟩
    simp only [srBlock]
    have huse : ∀ r ∈ termUses b.term, fr'.get r = fr.get r := fun r hr => hag.get hr
    have hout : termOut fr' b.term = termOut fr b.term := by
      cases ht : b.term with
      | jump l => rfl
      | trap => rfl
      | branch c l₁ l₂ =>
        simp only [termOut]; rw [huse c (by simp [ht, termUses])]
      | ret locs =>
        simp only [termOut]
        rw [readAll_agree hag.1 fun r hr => huse r (by simp [ht, termUses]; exact ⟨_, hr, rfl⟩)]
    refine ⟨hout, fun l' hl' => agree_entry hc (hag.base.mono fun r hr => ?_)⟩
    cases ht : b.term with
    | jump l => simp [ht, termOut] at hl'; subst hl'; simpa [liveOut, ht] using hr
    | trap => simp [ht, termOut] at hl'
    | ret locs => simp only [ht, termOut] at hl'; split at hl' <;> cases hl'
    | branch c l₁ l₂ =>
      simp only [ht, termOut] at hl'
      split at hl'
      · simp only [TermOut.goto.injEq] at hl'
        simp only [liveOut, Nat.testBit_or, Bool.or_eq_true]
        split at hl' <;> subst hl'
        · exact .inr hr
        · exact .inl hr
      · cases hl'

theorem sim : Sim srFunc PR := fun f => by
  by_cases hc : check (certOf f) f = true
  · have e₁ : srFunc f = { f with blocks := f.blocks.map (srBlock (certOf f)) } := by
      simp [srFunc, hc]
    have e₂ : PR f = SRel (certOf f) f := by simp [PR, hc]
    rw [e₁, e₂]; exact fsim f hc
  · have e₁ : srFunc f = f := by simp [srFunc, hc]
    have e₂ : PR f = idRel := by simp [PR, hc]
    rw [e₁, e₂]; exact FSim.id f

/-- **Strength reduction refines its input** (`Contract.mirPass`). -/
theorem correct : Contract.mirPass run := FuncPass.mirPass shape sim

end Silmaril.Compile.Mir.StrengthReduce
