module

public import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Sw

/-!
# The SPSC ring on TSO: FIFO, nothing lost (`Task.spscFifoTso`)

Proved with the single-writer logic `Sw`. The producer (thread `0`) owns `tail` (`q + 4`), the
two slots (`q + 8`, `q + 12`) and its result cells; the consumer (thread `1`) owns `head` (`q`)
and its output cells.

**The producer's log.** Every prefix `p` of it (every state memory can be in) satisfies `Pfx`:
`tail` holds the number of `tail` stores in `p`, at most one slot store is unpublished, and for
every published push `H` whose slot has not been reused in `p` (at most `H + 2` slot stores),
the slot `H mod 2` holds the `H`-th slot value. The producer keeps `Pfx` because its `tail`
store comes right after its slot store, and it reuses a slot only after `head` passed it.

**The cross-thread invariant** (`gpS`):
* the slot stores issued are at most `head` in memory plus `2` (a push needs `tail − head ≠ 2`
  with the `head` it read, and memory's `head` only grows);
* the `head` stores issued are at most `tail` in memory (a pop needs `head ≠ tail` with the
  `tail` it read).

**A pop** that read `tail > H` then reads slot `H mod 2` from memory: there `H` is published,
and at most `H + 2` slot stores exist, since the consumer's own `head` store `H + 1` has not
been issued yet. So the slot holds the `H`-th pushed value (TSO: the slot store reached memory
before the `tail` store that published it, and the consumer's loads read memory in order).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Spsc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.TvCfg (setB notE mask32 idxE)
open Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Sw

/-! ## Counting stores -/

section Pure

variable (q : Nat)

/-- A `tail` store. -/
def isT (e : Nat × Nat) : Bool := e.1 == q + 4
/-- A slot store. -/
def isS (e : Nat × Nat) : Bool := e.1 == q + 8 || e.1 == q + 12
/-- A `head` store. -/
def isH (e : Nat × Nat) : Bool := e.1 == q

/-- The number of `tail` stores. -/
def cntT (l : List (Nat × Nat)) : Nat := (l.filter (isT q)).length
/-- The number of slot stores. -/
def cntS (l : List (Nat × Nat)) : Nat := (l.filter (isS q)).length
/-- The number of `head` stores. -/
def cntH (l : List (Nat × Nat)) : Nat := (l.filter (isH q)).length
/-- The values of the slot stores, in order. -/
def svals (l : List (Nat × Nat)) : List Nat := (l.filter (isS q)).map (·.2)
/-- The slot of push `x`. -/
def slot (x : Nat) : Nat := q + 8 + 4 * (x % 2)

theorem svals_length (l : List (Nat × Nat)) : (svals q l).length = cntS q l := by
  simp [svals, cntS]

theorem cnt_snoc (p : Nat × Nat → Bool) (l : List (Nat × Nat)) (e : Nat × Nat) :
    ((l ++ [e]).filter p).length = (l.filter p).length + (if p e then 1 else 0) := by
  simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  split <;> simp

theorem svals_snoc (l : List (Nat × Nat)) (e : Nat × Nat) :
    svals q (l ++ [e]) = svals q l ++ (if isS q e then [e.2] else []) := by
  simp only [svals, List.filter_append, List.map_append, List.filter_cons, List.filter_nil]
  split <;> simp

theorem cntT_snoc (l : List (Nat × Nat)) (e : Nat × Nat) :
    cntT q (l ++ [e]) = cntT q l + (if isT q e then 1 else 0) := cnt_snoc _ _ _

theorem cntS_snoc (l : List (Nat × Nat)) (e : Nat × Nat) :
    cntS q (l ++ [e]) = cntS q l + (if isS q e then 1 else 0) := cnt_snoc _ _ _

theorem cntH_snoc (l : List (Nat × Nat)) (e : Nat × Nat) :
    cntH q (l ++ [e]) = cntH q l + (if isH q e then 1 else 0) := cnt_snoc _ _ _

theorem cnt_prefix (p : Nat × Nat → Bool) {l l' : List (Nat × Nat)} (h : l <+: l') :
    (l.filter p).length ≤ (l'.filter p).length :=
  (h.filter p).length_le

theorem take_prefix_mono {l l' : List (Nat × Nat)} (h : l <+: l') {f f' : Nat} (hf : f ≤ f')
    (hl : f ≤ l.length) : l.take f <+: l'.take f' := by
  obtain ⟨u, rfl⟩ := h
  rw [← List.take_append_of_le_length (l₂ := u) hl]
  exact List.take_prefix_take_left hf

theorem take_of_prefix {l l' : List (Nat × Nat)} (h : l <+: l') {f : Nat} (hf : f ≤ l.length) :
    l'.take f = l.take f := by
  obtain ⟨u, rfl⟩ := h
  exact List.take_append_of_le_length hf

variable {q}

/-- **A state of the ring's producer side** (a prefix of the producer's log). -/
def Pfx (init : Heap) (l : List (Nat × Nat)) : Prop :=
  cellAfter init l (q + 4) = some (cntT q l % 2 ^ 32) ∧ cntT q l ≤ cntS q l ∧
  (∀ H, H < cntT q l → cntS q l ≤ H + 2 → cellAfter init l (slot q H) = (svals q l)[H]?) ∧
  (∀ x ∈ svals q l, 0 < x ∧ x < 2 ^ 32)

/-- Every prefix of the producer's log is a `Pfx` state. -/
def InvP (init : Heap) (l : List (Nat × Nat)) : Prop := ∀ f, Pfx (q := q) init (l.take f)

/-- Every prefix of the consumer's log has `head` = its number of `head` stores. -/
def InvC (init : Heap) (l : List (Nat × Nat)) : Prop :=
  ∀ f, cellAfter init (l.take f) q = some (cntH q (l.take f) % 2 ^ 32)

theorem invP_full {init : Heap} {l : List (Nat × Nat)} (h : InvP (q := q) init l) :
    Pfx (q := q) init l := by
  simpa using h l.length

theorem invP_snoc {init : Heap} {l : List (Nat × Nat)} {e : Nat × Nat} (h : InvP (q := q) init l)
    (he : Pfx (q := q) init (l ++ [e])) : InvP (q := q) init (l ++ [e]) := by
  intro f
  by_cases hf : f ≤ l.length
  · rw [List.take_append_of_le_length hf]; exact h f
  · rw [List.take_of_length_le (by simp; omega)]; exact he

theorem invC_snoc {init : Heap} {l : List (Nat × Nat)} {e : Nat × Nat} (h : InvC (q := q) init l)
    (he : cellAfter init (l ++ [e]) q = some (cntH q (l ++ [e]) % 2 ^ 32)) :
    InvC (q := q) init (l ++ [e]) := by
  intro f
  by_cases hf : f ≤ l.length
  · rw [List.take_append_of_le_length hf]; exact h f
  · rw [List.take_of_length_le (by simp; omega)]; exact he

theorem invC_full {init : Heap} {l : List (Nat × Nat)} (h : InvC (q := q) init l) :
    cellAfter init l q = some (cntH q l % 2 ^ 32) := by
  simpa using h l.length

theorem slot_cases (x : Nat) : slot q x = q + 8 ∨ slot q x = q + 12 := by
  simp only [slot]; omega

theorem slot_ne {x y : Nat} (h : x % 2 ≠ y % 2) : slot q x ≠ slot q y := by
  simp only [slot]; omega

theorem cntS_ne {l : List (Nat × Nat)} {a x : Nat} (h1 : a ≠ q + 8) (h2 : a ≠ q + 12) :
    cntS q (l ++ [(a, x)]) = cntS q l := by
  rw [cntS_snoc]; simp [isS, h1, h2]

theorem cntS_slot (l : List (Nat × Nat)) (P v : Nat) :
    cntS q (l ++ [(slot q P, v)]) = cntS q l + 1 := by
  rw [cntS_snoc]
  have : isS q (slot q P, v) = true := by
    simp only [isS, Bool.or_eq_true, beq_iff_eq]; exact slot_cases _
  simp [this]

theorem cntT_ne {l : List (Nat × Nat)} {a x : Nat} (h : a ≠ q + 4) :
    cntT q (l ++ [(a, x)]) = cntT q l := by
  rw [cntT_snoc]; simp [isT, h]

theorem cntT_tail (l : List (Nat × Nat)) (x : Nat) : cntT q (l ++ [(q + 4, x)]) = cntT q l + 1 := by
  rw [cntT_snoc]; simp [isT]

theorem cntT_slot (l : List (Nat × Nat)) (P v : Nat) : cntT q (l ++ [(slot q P, v)]) = cntT q l :=
  cntT_ne (by rcases slot_cases (q := q) P with h | h <;> omega)

theorem cntH_ne {l : List (Nat × Nat)} {a x : Nat} (h : a ≠ q) :
    cntH q (l ++ [(a, x)]) = cntH q l := by
  rw [cntH_snoc]; simp [isH, h]

theorem cntH_head (l : List (Nat × Nat)) (x : Nat) : cntH q (l ++ [(q, x)]) = cntH q l + 1 := by
  rw [cntH_snoc]; simp [isH]

theorem svals_ne {l : List (Nat × Nat)} {a x : Nat} (h1 : a ≠ q + 8) (h2 : a ≠ q + 12) :
    svals q (l ++ [(a, x)]) = svals q l := by
  rw [svals_snoc]; simp [isS, h1, h2]

theorem svals_slot (l : List (Nat × Nat)) (P v : Nat) :
    svals q (l ++ [(slot q P, v)]) = svals q l ++ [v] := by
  rw [svals_snoc]
  have : isS q (slot q P, v) = true := by
    simp only [isS, Bool.or_eq_true, beq_iff_eq]; exact slot_cases _
  simp [this]

/-- A store to a cell outside the ring keeps `Pfx`. -/
theorem pfx_other {init : Heap} {l : List (Nat × Nat)} {e : Nat × Nat}
    (he : e.1 ≠ q + 4 ∧ e.1 ≠ q + 8 ∧ e.1 ≠ q + 12) (h : Pfx (q := q) init l) :
    Pfx (q := q) init (l ++ [e]) := by
  have hT : isT q e = false := by simp [isT, he.1]
  have hS : isS q e = false := by simp [isS, he.2.1, he.2.2]
  have hc : cntT q (l ++ [e]) = cntT q l := by simp only [cntT_snoc, hT]; rfl
  have hs : cntS q (l ++ [e]) = cntS q l := by simp only [cntS_snoc, hS]; rfl
  have hv : svals q (l ++ [e]) = svals q l := by simp [svals_snoc, hS]
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, by rw [hc, hs]; exact h2, fun H hH hS' => ?_, by rw [hv]; exact h4⟩
  · rw [cellAfter_snoc, ite_f he.1, hc, h1]
  · rw [hc] at hH; rw [hs] at hS'
    rw [cellAfter_snoc, hv, ite_f (by rcases slot_cases (q := q) H with h | h <;> omega)]
    exact h3 H hH hS'

/-- The slot store of push `P` (all earlier pushes published) keeps `Pfx`. -/
theorem pfx_slot {init : Heap} {l : List (Nat × Nat)} {v : Nat} (hP : cntS q l = cntT q l)
    (hv : 0 < v ∧ v < 2 ^ 32) (h : Pfx (q := q) init l) :
    Pfx (q := q) init (l ++ [(slot q (cntS q l), v)]) := by
  have hT : isT q (slot q (cntS q l), v) = false := by
    simp only [isT]; rcases slot_cases (q := q) (cntS q l) with h | h <;> simp [h]
  have hS : isS q (slot q (cntS q l), v) = true := by
    simp only [isS, Bool.or_eq_true, beq_iff_eq]; exact slot_cases _
  have hc : cntT q (l ++ [(slot q (cntS q l), v)]) = cntT q l := by simp only [cntT_snoc, hT]; rfl
  have hs : cntS q (l ++ [(slot q (cntS q l), v)]) = cntS q l + 1 := by
    simp only [cntS_snoc, hS]; rfl
  have hvs : svals q (l ++ [(slot q (cntS q l), v)]) = svals q l ++ [v] := by
    simp [svals_snoc, hS]
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, by rw [hc, hs]; omega, fun H hH hS' => ?_, ?_⟩
  · rw [cellAfter_snoc, ite_f (by rcases slot_cases (q := q) (cntS q l) with h | h <;> omega), hc,
      h1]
  · rw [hc] at hH; rw [hs] at hS'
    have hH' : H + 1 = cntS q l := by omega
    rw [cellAfter_snoc, ite_f (slot_ne (by omega)), hvs,
      List.getElem?_append_left (by rw [svals_length]; omega)]
    exact h3 H hH (by omega)
  · rw [hvs]; intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h4 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hv

/-- The slot store of push `P` followed by the `tail` store publishing it keeps `Pfx`. -/
theorem pfx_tail {init : Heap} {l : List (Nat × Nat)} {v : Nat} (hP : cntS q l = cntT q l)
    (hv : 0 < v ∧ v < 2 ^ 32) (h : Pfx (q := q) init l) :
    Pfx (q := q) init (l ++ [(slot q (cntS q l), v)] ++ [(q + 4, (cntS q l + 1) % 2 ^ 32)]) := by
  have h' := pfx_slot hP hv h
  have hS : isS q (slot q (cntS q l), v) = true := by
    simp only [isS, Bool.or_eq_true, beq_iff_eq]; exact slot_cases _
  have hT : isT q (slot q (cntS q l), v) = false := by
    simp only [isT]; rcases slot_cases (q := q) (cntS q l) with h | h <;> simp [h]
  have hT' : isT q (q + 4, (cntS q l + 1) % 2 ^ 32) = true := by simp [isT]
  have hS' : isS q (q + 4, (cntS q l + 1) % 2 ^ 32) = false := by simp [isS]
  set l1 := l ++ [(slot q (cntS q l), v)] with hl1
  have hc1 : cntT q l1 = cntT q l := by simp only [hl1, cntT_snoc, hT]; rfl
  have hs1 : cntS q l1 = cntS q l + 1 := by simp only [hl1, cntS_snoc, hS]; rfl
  have hv1 : svals q l1 = svals q l ++ [v] := by simp [hl1, svals_snoc, hS]
  have hc : cntT q (l1 ++ [(q + 4, (cntS q l + 1) % 2 ^ 32)]) = cntS q l + 1 := by
    rw [cntT_snoc, hT', hc1, ← hP]; rfl
  have hs : cntS q (l1 ++ [(q + 4, (cntS q l + 1) % 2 ^ 32)]) = cntS q l + 1 := by
    rw [cntS_snoc, hS', hs1]; rfl
  have hvs : svals q (l1 ++ [(q + 4, (cntS q l + 1) % 2 ^ 32)]) = svals q l ++ [v] := by
    rw [svals_snoc, hS', hv1]; simp
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, by rw [hc, hs], fun H hH hS'' => ?_, ?_⟩
  · rw [cellAfter_snoc, ite_t rfl, hc]
  · rw [hc] at hH; rw [hs] at hS''
    rw [cellAfter_snoc, ite_f (by rcases slot_cases (q := q) H with h | h <;> omega), hvs, hl1,
      cellAfter_snoc]
    by_cases hHP : H = cntS q l
    · subst hHP
      rw [ite_t rfl, List.getElem?_append_right (by rw [svals_length]), svals_length]; simp
    · have hHl : H + 1 = cntS q l := by omega
      rw [ite_f (slot_ne (by omega)), List.getElem?_append_left (by rw [svals_length]; omega)]
      exact h3 H (by omega) (by omega)
  · rw [hvs]; intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h4 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hv

end Pure

/-! ## Register arithmetic -/

section Regs

theorem set_apply (rs : Regs) (r q : Reg) (v : Word) :
    (rs.set r v) q = if q = r then v else rs q := rfl

theorem ev_r32 {rs : Regs} {r : Reg} {x : Nat} (h : rs r = BitVec.ofNat 64 x) (hx : x < 2 ^ 32) :
    (r32 r).eval rs = BitVec.ofNat 64 x := by
  apply bv_eq_ofNat (by omega)
  rw [r32, toNat_mask32]
  simp only [Expr.eval, h, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt hx]

theorem ev_add1 {rs : Regs} {r : Reg} {x : Nat} (h : rs r = BitVec.ofNat 64 x) (hx : x < 2 ^ 32) :
    (op32 .add r (.lit 1)).eval rs = BitVec.ofNat 64 ((x + 1) % 2 ^ 32) := by
  apply bv_eq_ofNat (by omega)
  rw [op32, toNat_mask32]
  simp only [Expr.eval, BinOp.eval, h, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : x + 1 < 2 ^ 64)]

theorem ev_and1 {rs : Regs} {r : Reg} {x : Nat} (h : rs r = BitVec.ofNat 64 x) (hx : x < 2 ^ 64) :
    (op32 .and r (.lit 1)).eval rs = BitVec.ofNat 64 (x % 2) := by
  apply bv_eq_ofNat (by omega)
  rw [op32, toNat_mask32]
  simp only [Expr.eval, BinOp.eval, h, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hx, show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod]
  omega

theorem ev_xor (rs : Regs) (r : Reg) : (op32 .xor r (.reg r)).eval rs = BitVec.ofNat 64 0 := by
  apply bv_eq_ofNat (by decide)
  rw [op32, toNat_mask32]
  simp [Expr.eval, BinOp.eval]

theorem ev_sub {rs : Regs} {r r' : Reg} {x y : Nat} (h : rs r = BitVec.ofNat 64 x)
    (h' : rs r' = BitVec.ofNat 64 y) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (op32 .sub r (.reg r')).eval rs = BitVec.ofNat 64 ((x + 2 ^ 32 - y) % 2 ^ 32) := by
  apply bv_eq_ofNat (by omega)
  rw [op32, toNat_mask32]
  simp only [Expr.eval, BinOp.eval, h, h', BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega : y < 2 ^ 64)]
  omega

theorem ev_lit (rs : Regs) {a : Nat} (h : a < 2 ^ 64) : ((Expr.lit a).eval rs).toNat = a := by
  simp only [Expr.eval]; exact toNat_ofNat_lt h

theorem ev_atIdx {rs : Regs} {a x : Nat} (ha : rs .rdi = BitVec.ofNat 64 a)
    (hx : rs .rdx = BitVec.ofNat 64 x) (h : a + 4 * x + 8 < 2 ^ 64) :
    ((atIdx .rdi .rdx 8).eval rs).toNat = a + 4 * x + 8 := by
  simp only [atIdx, idxE, Expr.eval, BinOp.eval, ha, hx, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : x < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 < 2 ^ 64)]
  omega

theorem truthy_full {rs : Regs} {x : Nat} (h : rs .rcx = BitVec.ofNat 64 x) (hx : x < 2 ^ 32) :
    truthy (SpscPush.zFull.eval rs) = decide (x = 2) := by
  rw [SpscPush.zFull, zCmpI, truthy_eq, ev_r32 h hx]
  by_cases hx2 : x = 2
  · subst hx2; simp [Expr.eval]
  · rw [decide_eq_false hx2]
    refine decide_eq_false (fun e => hx2 ?_)
    have := congrArg BitVec.toNat e
    simp only [Expr.eval, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)] at this
    exact this

theorem truthy_cmp {rs : Regs} {a b : Reg} {x y : Nat} (ha : rs a = BitVec.ofNat 64 x)
    (hb : rs b = BitVec.ofNat 64 y) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    truthy ((zCmp a b).eval rs) = decide (x = y) := by
  rw [zCmp, truthy_eq, ev_r32 ha hx, ev_r32 hb hy]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [decide_eq_false hxy]
    refine decide_eq_false (fun e => hxy ?_)
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : y < 2 ^ 64)] at this
    exact this

end Regs

/-! ## The protocol -/

section Proto

variable (q out res k n : Nat) (vs : List Nat) (init : Heap)

/-- **Ownership**: the producer owns `tail`, the slots and its result cells; the consumer owns
`head` and its output cells. -/
def ownS (t c : Nat) : Prop :=
  (t = 0 ∧ (c = q + 4 ∨ c = q + 8 ∨ c = q + 12 ∨ ∃ j, j < n ∧ c = res + 4 * j)) ∨
  (t = 1 ∧ (c = q ∨ ∃ i, i < k ∧ c = out + 4 * i))

/-- **The protocol invariant.** -/
def gpS (g : W) : Prop :=
  InvP (q := q) init (g.log 0) ∧ InvC (q := q) init (g.log 1) ∧
  cntS q (g.log 0) ≤ cntH q ((g.log 1).take (g.fl 1)) + 2 ∧
  cntH q (g.log 1) ≤ cntT q ((g.log 0).take (g.fl 0))

/-- The values of the calls whose push succeeded. -/
def pushedOf (bs : List Bool) : List Nat :=
  ((List.range bs.length).filter fun j => bs.getD j false).map fun j => vs.getD j 0

/-- A push result as a number. -/
def b2n (b : Bool) : Nat := if b then 1 else 0

/-- The producer before call `j`. -/
def PS (j : Nat) (rs : Regs) (g : W) : Prop :=
  rs .rdi = BitVec.ofNat 64 q ∧ ∃ bs : List Bool, bs.length = j ∧
    cntS q (g.log 0) = cntT q (g.log 0) ∧ svals q (g.log 0) = pushedOf vs bs ∧
    ∀ j' < j, lastV (g.log 0) (res + 4 * j') = some (b2n (bs.getD j' false))

/-- The consumer before pop `i`. -/
def CS (i : Nat) (rs : Regs) (g : W) : Prop :=
  rs .rdi = BitVec.ofNat 64 q ∧ ∃ sel : List (Option Nat), sel.length = i ∧
    cntH q (g.log 1) = (sel.filterMap id).length ∧
    (∀ i' < i, lastV (g.log 1) (out + 4 * i') = sel.getD i' none) ∧
    (∀ i', i ≤ i' → i' < k → lastV (g.log 1) (out + 4 * i') = none) ∧
    sel.filterMap id <+: svals q (g.log 0)

/-- The postconditions. -/
def postS (t : Nat) (rs : Regs) (g : W) : Prop :=
  (t = 0 → PS q res vs n rs g) ∧ (t = 1 → CS q out k k rs g)

/-- The producer's statement. -/
def prodS (L : Nat) : Stmt := Tv.chain ((List.range vs.length).map fun j =>
  Tv.chain [.assign .rsi (.lit (vs.getD j 0)), SpscPush.cert.body L,
    .store .na 4 .wb (.lit (res + 4 * j)) (.reg .rax)])

/-- The consumer's statement. -/
def consS (L : Nat) : Stmt := Tv.chain ((List.range k).map fun i =>
  Tv.chain [.assign .rsi (.lit (out + 4 * i)), SpscPop.cert.body L])

end Proto

theorem pushedOf_snoc (vs : List Nat) (bs : List Bool) (b : Bool) :
    pushedOf vs (bs ++ [b]) = pushedOf vs bs ++ (if b then [vs.getD bs.length 0] else []) := by
  simp only [pushedOf, List.length_append, List.length_singleton, List.range_succ,
    List.filter_append, List.map_append]
  congr 1
  · congr 1
    apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  · cases b <;> simp [List.getD_eq_getElem?_getD]

theorem stab_PS {q res : Nat} {vs : List Nat} {Gp : W → Prop} (j : Nat) (rs : Regs) :
    Stab Gp 0 (PS q res vs j rs) := by
  intro g g' h r _
  unfold PS at *
  rw [r.1]; exact h

theorem svals_prefix {q : Nat} {l l' : List (Nat × Nat)} (h : l <+: l') :
    svals q l <+: svals q l' :=
  (h.filter _).map _

theorem stab_CS {q out k : Nat} {Gp : W → Prop} (i : Nat) (rs : Regs) :
    Stab Gp 1 (CS q out k i rs) := by
  intro g g' h r _
  unfold CS at *
  rw [r.1]
  obtain ⟨h1, sel, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, sel, h2, h3, h4, h5, h6.trans (svals_prefix (r.2.1 0))⟩

theorem gpS_flush {q : Nat} {init : Heap} (g : W) (t : Nat) (h : gpS q init g) (_ : WF g)
    (_ : g.fl t < (g.log t).length) : gpS q init (g.flush t) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hf : ∀ u, g.fl u ≤ (g.flush t).fl u := fun u => by
    simp only [W.flush, upd]; by_cases h : u = t <;> simp [h]
  refine ⟨h1, h2, h3.trans ?_, h4.trans ?_⟩
  · exact Nat.add_le_add_right (cnt_prefix _ (List.take_prefix_take_left (hf 1))) 2
  · exact cnt_prefix _ (List.take_prefix_take_left (hf 0))

/-- The `head` count the producer read stays below memory's `head`. -/
theorem stab_hv {q : Nat} {Gp : W → Prop} (Xl : List (Nat × Nat)) (hv : Nat) :
    Stab Gp 0 (fun g => g.log 0 = Xl ∧ WF g ∧ hv ≤ cntH q ((g.log 1).take (g.fl 1))) := by
  intro g g' ⟨h1, h2, h3⟩ r _
  exact ⟨r.1.trans h1, r.2.2.2, h3.trans (cnt_prefix _ (take_prefix_mono (r.2.1 1) (r.2.2.1 1)
    (h2 1)))⟩

/-- The `tail` count the consumer read stays below memory's `tail`. -/
theorem stab_tv {q : Nat} {Gp : W → Prop} (P : W → Prop) (hP : Stab Gp 1 P) (tv : Nat) :
    Stab Gp 1 (fun g => P g ∧ WF g ∧ tv ≤ cntT q ((g.log 0).take (g.fl 0))) := by
  intro g g' ⟨h1, h2, h3⟩ r hg
  exact ⟨hP g g' h1 r hg, r.2.2.2, h3.trans (cnt_prefix _ (take_prefix_mono (r.2.1 0)
    (r.2.2.1 0) (h2 0)))⟩

/-! ## The producer -/

/-- The context of the proofs. -/
structure SCtx (q out res k n : Nat) (vs : List Nat) : Prop where
  hU : ∀ t u c, ownS q out res k n t c → ownS q out res k n u c → t = u
  hq : q + 16 < 2 ^ 64
  hres : res + 4 * n < 2 ^ 64
  hout : out + 4 * k < 2 ^ 64
  hdr : res + 4 * n ≤ q ∨ q + 16 ≤ res
  hdo : out + 4 * k ≤ q ∨ q + 16 ≤ out
  hvs : ∀ v ∈ vs, 0 < v ∧ v < 2 ^ 32
  hn : vs.length = n

section Producer

variable {q out res k n : Nat} {vs : List Nat} {init : Heap}

theorem pushBody (L : Nat) : SpscPush.cert.body L = Tv.chain [SpscPush.ldT, SpscPush.ldH,
    SpscPush.a1, SpscPush.a2, SpscPush.a3, .ite SpscPush.zFull .skip
      (.seq SpscPush.b1 (.seq SpscPush.b2 (.seq SpscPush.b3 (.seq SpscPush.b4
        (.seq SpscPush.b5 SpscPush.b6))))), SpscPush.ret] := rfl

theorem own0 {c : Nat} (h : c = q + 4 ∨ c = q + 8 ∨ c = q + 12 ∨ ∃ j, j < n ∧ c = res + 4 * j) :
    ownS q out res k n 0 c := Or.inl ⟨rfl, h⟩

theorem own1 {c : Nat} (h : c = q ∨ ∃ i, i < k ∧ c = out + 4 * i) :
    ownS q out res k n 1 c := Or.inr ⟨rfl, h⟩

/-- The slot and `tail` stores of a push that found room. -/
theorem push_commit (X : SCtx q out res k n vs) {Q : Regs → W → Prop} {rs : Regs} {g : W}
    {Xl : List (Nat × Nat)} {P hv v : Nat}
    (hrdi : rs .rdi = BitVec.ofNat 64 q) (hrsi : rs .rsi = BitVec.ofNat 64 v)
    (hrax : rs .rax = BitVec.ofNat 64 ((P + 1) % 2 ^ 32)) (hrdx : rs .rdx = BitVec.ofNat 64 (P % 2))
    (hvv : 0 < v ∧ v < 2 ^ 32) (hP : cntS q Xl = P) (hPT : cntT q Xl = P) (h2 : P ≤ hv + 1)
    (hg : g.log 0 = Xl ∧ WF g ∧ hv ≤ cntH q ((g.log 1).take (g.fl 1)))
    (kk : ∀ g', g'.log 0 = Xl ++ [(slot q P, v), (q + 4, (P + 1) % 2 ^ 32)] →
      TSafe (ownS q out res k n) init (gpS q init) 0 Q .skip (rs.set .rdx (Expr.eval rs (.lit 1)))
        g') :
    TSafe (ownS q out res k n) init (gpS q init) 0 Q
      (.seq SpscPush.b4 (.seq SpscPush.b5 SpscPush.b6)) rs g := by
  have hq := X.hq
  have ha : ((atIdx .rdi .rdx 8).eval rs).toNat = slot q P := by
    rw [ev_atIdx hrdi hrdx (by omega)]; simp only [slot]; omega
  refine tsafe_seq_store _ (stab_hv Xl hv) ?_ ?_ hg
  · rw [ha]; exact own0 (by rcases slot_cases (q := q) P with h | h <;> simp [h])
  rintro g ⟨hl, hw, hhv⟩ ⟨i1, i2, i3, i4⟩ _
  rw [ha, eval_reg_mod hrsi hvv.2]
  have hS1 : cntS q (Xl ++ [(slot q P, v)]) = P + 1 := by
    rw [cntS_snoc, hP]; simp only [isS, Bool.or_eq_true, beq_iff_eq, slot_cases, ite_true]
  have hT1 : cntT q (Xl ++ [(slot q P, v)]) = P := by
    rw [cntT_snoc, hPT]
    simp only [isT, beq_iff_eq]
    rw [ite_f (by rcases slot_cases (q := q) P with h | h <;> omega)]; rfl
  have hpx : Pfx (q := q) init Xl := by rw [← hl]; exact invP_full i1
  refine ⟨⟨by rw [push_log, hl]; exact invP_snoc (hl ▸ i1) (hP ▸ pfx_slot (by omega) hvv hpx),
    by rw [push_log_ne _ (by decide)]; exact i2, ?_, ?_⟩, ?_⟩
  · rw [push_log, hl, hS1, push_log_ne _ (by decide), push_fl]; omega
  · rw [push_log_ne _ (by decide), push_log, push_fl, List.take_append_of_le_length (hl ▸ hw 0)]
    exact i4
  apply tsafe_seq_assign
  have hrdi' : (rs.set .rdx (Expr.eval rs (.lit 1))) .rdi = BitVec.ofNat 64 q := by
    simp [set_apply, hrdi]
  have hrax' : (rs.set .rdx (Expr.eval rs (.lit 1))) .rax = BitVec.ofNat 64 ((P + 1) % 2 ^ 32) := by
    simp [set_apply, hrax]
  refine tsafe_store (fun g' => g'.log 0 = Xl ++ [(slot q P, v)] ∧ WF g' ∧
    hv ≤ cntH q ((g'.log 1).take (g'.fl 1))) (stab_hv _ hv) ?_ ?_
    ⟨by rw [push_log, hl], wf_push hw 0 _, by rw [push_log_ne _ (by decide), push_fl]; exact hhv⟩
  · rw [eval_at 4 hrdi' (by omega)]; exact own0 (Or.inl rfl)
  rintro g ⟨hl, hw, hhv⟩ ⟨i1, i2, i3, i4⟩ _
  rw [eval_at 4 hrdi' (by omega), eval_reg_mod hrax' (Nat.mod_lt _ (by decide))]
  have hlog : (g.push 0 (q + 4, (P + 1) % 2 ^ 32)).log 0 =
      Xl ++ [(slot q P, v)] ++ [(q + 4, (cntS q Xl + 1) % 2 ^ 32)] := by
    rw [push_log, hl, hP]
  refine ⟨⟨?_, by rw [push_log_ne _ (by decide)]; exact i2, ?_, ?_⟩, ?_⟩
  · rw [hlog]
    exact invP_snoc (by rw [hl] at i1; exact i1) (hP ▸ pfx_tail (by omega) hvv hpx)
  · rw [hlog, cntS_ne (by omega) (by omega), hS1, push_log_ne _ (by decide), push_fl]
    rw [hl] at i3; rw [hS1] at i3; omega
  · rw [push_log_ne _ (by decide), push_log, push_fl, List.take_append_of_le_length (hw 0)]
    exact i4
  · refine kk _ ?_
    rw [hlog, hP]; simp

/-- The fullness test and the rest of `spsc_push`. -/
theorem push_br (X : SCtx q out res k n vs) {Q : Regs → W → Prop} {rs : Regs} {g : W}
    {Xl : List (Nat × Nat)} {P hv v : Nat}
    (hrdi : rs .rdi = BitVec.ofNat 64 q) (hrsi : rs .rsi = BitVec.ofNat 64 v)
    (hrax : rs .rax = BitVec.ofNat 64 (P % 2 ^ 32)) (hrcx : rs .rcx = BitVec.ofNat 64 (P - hv))
    (hrdx : rs .rdx = BitVec.ofNat 64 0)
    (hvv : 0 < v ∧ v < 2 ^ 32) (hP : cntS q Xl = P) (hPT : cntT q Xl = P) (h1 : hv ≤ P)
    (h2 : P ≤ hv + 2)
    (hg : g.log 0 = Xl ∧ WF g ∧ hv ≤ cntH q ((g.log 1).take (g.fl 1)))
    (kk : ∀ rs' g' (b : Bool), rs' .rdi = BitVec.ofNat 64 q → rs' .rax = BitVec.ofNat 64 (b2n b) →
      g'.log 0 = Xl ++ (if b then [(slot q P, v), (q + 4, (P + 1) % 2 ^ 32)] else []) →
      TSafe (ownS q out res k n) init (gpS q init) 0 Q .skip rs' g') :
    TSafe (ownS q out res k n) init (gpS q init) 0 Q
      (Tv.chain [.ite SpscPush.zFull .skip
        (.seq SpscPush.b1 (.seq SpscPush.b2 (.seq SpscPush.b3 (.seq SpscPush.b4
          (.seq SpscPush.b5 SpscPush.b6))))), SpscPush.ret]) rs g := by
  simp only [Tv.chain]
  apply tsafe_seq_ite
  rw [truthy_full hrcx (by omega)]
  by_cases hfull : P - hv = 2
  · simp only [hfull, decide_true, ite_true]
    apply tsafe_skip_of
    apply tsafe_seq_assign
    refine kk _ g false (by simp [set_apply, hrdi]) ?_ (by simp [hg.1])
    simp only [set_apply, ite_true]
    exact ev_r32 hrdx (by decide)
  · simp only [hfull, decide_false, Bool.false_eq_true, ite_false]
    apply tsafe_seq_assign
    apply tsafe_seq_assign
    apply tsafe_seq_assign
    refine push_commit X (P := P) (hv := hv) (v := v) ?_ ?_ ?_ ?_ hvv hP hPT (by omega) hg
      (fun g' hl => tsafe_skip_of (tsafe_seq_assign (kk _ g' true ?_ ?_ (by simpa using hl))))
    · simp [set_apply, hrdi]
    · simp [set_apply, hrsi]
    · simp only [set_apply, reduceCtorEq, ite_true, ite_false]
      have := ev_add1 (rs := rs.set .rdx ((r32 .rax).eval rs)) (r := .rax) (x := P % 2 ^ 32)
        (by simp [set_apply, hrax]) (Nat.mod_lt _ (by decide))
      rw [this]; congr 1; omega
    · simp only [set_apply, reduceCtorEq, ite_true, ite_false]
      have := ev_and1 (rs := (rs.set .rdx ((r32 .rax).eval rs)).set .rax
        ((op32 .add .rax (.lit 1)).eval (rs.set .rdx ((r32 .rax).eval rs)))) (r := .rdx)
        (x := P % 2 ^ 32) (by simp [set_apply]; exact ev_r32 hrax (Nat.mod_lt _ (by decide)))
        (by omega)
      rw [this]; congr 1; omega
    · simp [set_apply, hrdi]
    · simp only [set_apply, ite_true]
      rw [ev_r32 (x := 1) (by simp [set_apply, Expr.eval]) (by decide)]; rfl

/-- `spsc_push` after its two loads. -/
theorem push_mid (X : SCtx q out res k n vs) {Q : Regs → W → Prop} {rs : Regs} {g : W}
    {Xl : List (Nat × Nat)} {P hv v : Nat}
    (hrdi : rs .rdi = BitVec.ofNat 64 q) (hrsi : rs .rsi = BitVec.ofNat 64 v)
    (hrax : rs .rax = BitVec.ofNat 64 (P % 2 ^ 32)) (hrdx : rs .rdx = BitVec.ofNat 64 (hv % 2 ^ 32))
    (hvv : 0 < v ∧ v < 2 ^ 32) (hP : cntS q Xl = P) (hPT : cntT q Xl = P) (h1 : hv ≤ P)
    (h2 : P ≤ hv + 2)
    (hg : g.log 0 = Xl ∧ WF g ∧ hv ≤ cntH q ((g.log 1).take (g.fl 1)))
    (kk : ∀ rs' g' (b : Bool), rs' .rdi = BitVec.ofNat 64 q → rs' .rax = BitVec.ofNat 64 (b2n b) →
      g'.log 0 = Xl ++ (if b then [(slot q P, v), (q + 4, (P + 1) % 2 ^ 32)] else []) →
      TSafe (ownS q out res k n) init (gpS q init) 0 Q .skip rs' g') :
    TSafe (ownS q out res k n) init (gpS q init) 0 Q
      (Tv.chain [SpscPush.a1, SpscPush.a2, SpscPush.a3, .ite SpscPush.zFull .skip
        (.seq SpscPush.b1 (.seq SpscPush.b2 (.seq SpscPush.b3 (.seq SpscPush.b4
          (.seq SpscPush.b5 SpscPush.b6))))), SpscPush.ret]) rs g := by
  simp only [Tv.chain]
  apply tsafe_seq_assign
  apply tsafe_seq_assign
  apply tsafe_seq_assign
  have hrcx1 : (rs.set .rcx ((r32 .rax).eval rs)) .rcx = BitVec.ofNat 64 (P % 2 ^ 32) := by
    simp only [set_apply, ite_true]; exact ev_r32 hrax (Nat.mod_lt _ (by decide))
  have hrdx1 : (rs.set .rcx ((r32 .rax).eval rs)) .rdx = BitVec.ofNat 64 (hv % 2 ^ 32) := by
    simp [set_apply, hrdx]
  refine push_br X (P := P) (hv := hv) (v := v) ?_ ?_ ?_ ?_ ?_ hvv hP hPT h1 h2 hg kk
  · simp [set_apply, hrdi]
  · simp [set_apply, hrsi]
  · simp [set_apply, hrax]
  · simp only [set_apply, reduceCtorEq, ite_true, ite_false]
    rw [ev_sub hrcx1 hrdx1 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
    congr 1; omega
  · simp only [set_apply, ite_true]; exact ev_xor _ _

theorem lastV_append_ne {l l' : List (Nat × Nat)} {c : Nat} (h : ∀ e ∈ l', e.1 ≠ c) :
    lastV (l ++ l') c = lastV l c := by
  rw [lastV_append, lastV_eq_none h, Option.none_or]

theorem stab_wf {Gp : W → Prop} {t : Nat} : Stab Gp t WF := fun _ _ _ r _ => r.2.2.2

/-- A producer store outside the ring keeps the protocol invariant. -/
theorem gp_push0_other {g : W} (h : gpS q init g) (hw : WF g) {a x : Nat}
    (ha : a ≠ q + 4 ∧ a ≠ q + 8 ∧ a ≠ q + 12) : gpS q init (g.push 0 (a, x)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨?_, by rw [push_log_ne _ (by decide)]; exact i2, ?_, ?_⟩
  · rw [push_log]; exact invP_snoc i1 (pfx_other ha (invP_full i1))
  · rw [push_log, cntS_ne ha.2.1 ha.2.2, push_log_ne _ (by decide), push_fl]; exact i3
  · rw [push_log_ne _ (by decide), push_log, push_fl, List.take_append_of_le_length (hw 0)]
    exact i4

/-- A consumer store outside `head` keeps the protocol invariant. -/
theorem gp_push1_other {g : W} (h : gpS q init g) (hw : WF g) {a x : Nat} (ha : a ≠ q) :
    gpS q init (g.push 1 (a, x)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨by rw [push_log_ne _ (by decide)]; exact i1, ?_, ?_, ?_⟩
  · rw [push_log]
    refine invC_snoc i2 ?_
    rw [cellAfter_snoc, ite_f ha, cntH_ne ha]; exact invC_full i2
  · rw [push_log_ne _ (by decide), push_log, push_fl, List.take_append_of_le_length (hw 1)]
    exact i3
  · rw [push_log, cntH_ne ha, push_log_ne _ (by decide), push_fl]; exact i4

/-- **One producer call**: `push(vs[j])` and the result store. -/
theorem push_item (X : SCtx q out res k n vs) (L j : Nat) (hj : j < n) {Q : Regs → W → Prop}
    {rs : Regs} {g : W} (hps : PS q res vs j rs g)
    (kk : ∀ rs' g', PS q res vs (j + 1) rs' g' →
      TSafe (ownS q out res k n) init (gpS q init) 0 Q .skip rs' g') :
    TSafe (ownS q out res k n) init (gpS q init) 0 Q
      (Tv.chain [.assign .rsi (.lit (vs.getD j 0)), SpscPush.cert.body L,
        .store .na 4 .wb (.lit (res + 4 * j)) (.reg .rax)]) rs g := by
  obtain ⟨hrdi, bs, hbl, hc, hsv, hres⟩ := hps
  have hq := X.hq
  have hrs := X.hres
  have hvj : 0 < vs.getD j 0 ∧ vs.getD j 0 < 2 ^ 32 := by
    apply X.hvs
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [X.hn]; exact hj)]
    exact List.getElem_mem _
  have hrv : ∀ j', j' < n → res + 4 * j' ≠ q + 4 ∧ res + 4 * j' ≠ q + 8 ∧
      res + 4 * j' ≠ q + 12 := fun j' hj' => by have := X.hdr; omega
  rw [pushBody]
  simp only [Tv.chain]
  apply tsafe_seq_assign
  apply tsafe_seq
  have hrdi1 : (rs.set .rsi (Expr.eval rs (.lit (vs.getD j 0)))) .rdi = BitVec.ofNat 64 q := by
    simp [set_apply, hrdi]
  -- `mov eax, [rdi+4]`: the producer's own `tail`
  refine tsafe_seq_load (fun g' => g'.log 0 = g.log 0) (stab_log _)
    (fun g1 a h1 hgp1 hw1 _ hrd => ?_) rfl
  rw [eval_at 4 hrdi1 (by omega)] at hrd
  have ha := rdOk_own X.hU (own0 (Or.inl rfl)) hrd
  rw [(invP_full hgp1.1).1, h1, ← hc, Option.some.injEq] at ha
  -- `mov edx, [rdi]`: the consumer's `head`
  have hrdi2 : ((rs.set .rsi (Expr.eval rs (.lit (vs.getD j 0)))).set .rax
      (BitVec.ofNat 64 a)) .rdi = BitVec.ofNat 64 q := by simp [set_apply, hrdi]
  refine tsafe_seq_load (fun g' => g'.log 0 = g.log 0 ∧ WF g') (stab_and (stab_log _) stab_wf)
    (fun g2 b h2 hgp2 hw2 _ hrd => ?_) ⟨h1, hw1⟩
  rw [eval_at 0 hrdi2 (by omega), Nat.add_zero] at hrd
  have hb := rdOk_other X.hU (own1 (Or.inl rfl)) (by decide) hrd
  rw [hgp2.2.1 (g2.fl 1), Option.some.injEq] at hb
  have hG1 := hgp2.2.2.1
  have hG2 := hgp2.2.2.2
  rw [h2.1] at hG1 hG2
  have hle : cntH q ((g2.log 1).take (g2.fl 1)) ≤ cntH q (g2.log 1) :=
    cnt_prefix _ (List.take_prefix _ _)
  have hle2 : cntT q ((g.log 0).take (g2.fl 0)) ≤ cntT q (g.log 0) :=
    cnt_prefix _ (List.take_prefix _ _)
  refine push_mid X (P := cntS q (g.log 0)) (hv := cntH q ((g2.log 1).take (g2.fl 1)))
    (v := vs.getD j 0) ?_ ?_ ?_ ?_ hvj rfl hc.symm (by omega) (by omega)
    ⟨h2.1, hw2, Nat.le_refl _⟩ (fun rs' g' bb hrdi' hrax' hlog => ?_)
  · simp [set_apply, hrdi]
  · simp [set_apply, Expr.eval]
  · simp [set_apply, ← ha]
  · simp [set_apply, ← hb]
  -- the result store
  apply tsafe_skip_of
  have hx : res + 4 * j < 2 ^ 64 := by omega
  have hrv' := hrv j hj
  have hpair : ∀ (l : List (Nat × Nat)) (a b : Nat × Nat), l ++ [a, b] = l ++ [a] ++ [b] := by
    simp
  refine tsafe_seq_store (fun g'' => g''.log 0 = g'.log 0) (stab_log _) ?_ ?_ rfl
  · rw [ev_lit _ hx]; exact own0 (Or.inr (Or.inr (Or.inr ⟨j, hj, rfl⟩)))
  intro g3 h3 hgp3 hw3
  rw [ev_lit _ hx, eval_reg_mod hrax' (by cases bb <;> decide)]
  refine ⟨gp_push0_other hgp3 hw3 hrv', kk _ _ ⟨hrdi', bs ++ [bb], by simp [hbl], ?_, ?_, ?_⟩⟩
  · rw [push_log, h3, hlog]
    cases bb
    · simp only [Bool.false_eq_true, ite_false, List.append_nil]
      rw [cntS_ne hrv'.2.1 hrv'.2.2, cntT_ne hrv'.1]; exact hc
    · simp only [ite_true]
      rw [hpair, cntS_ne hrv'.2.1 hrv'.2.2, cntS_ne (by omega) (by omega), cntS_slot,
        cntT_ne hrv'.1, cntT_tail, cntT_slot, hc]
  · rw [push_log, h3, hlog, pushedOf_snoc, hbl]
    cases bb
    · simp only [Bool.false_eq_true, ite_false, List.append_nil]
      rw [svals_ne hrv'.2.1 hrv'.2.2, hsv]
    · simp only [ite_true]
      rw [hpair, svals_ne hrv'.2.1 hrv'.2.2, svals_ne (by omega) (by omega), svals_slot, hsv]
  · intro j' hj'
    rw [push_log, h3, lastV_snoc]
    by_cases hjj : j' = j
    · subst hjj
      rw [ite_t rfl]
      simp [List.getD_eq_getElem?_getD, ← hbl]
    · rw [ite_f (by omega), hlog, lastV_append_ne, hres j' (by omega)]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      · intro e he
        cases bb
        · simp at he
        · have := X.hdr
          simp only [ite_true, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl
          · rcases slot_cases (q := q) (cntS q (g.log 0)) with h | h <;> simp only [h] <;> omega
          · simp only; omega

theorem stab_post {q out res k n : Nat} {vs : List Nat} {Gp : W → Prop} (t : Nat) (rs : Regs) :
    Stab Gp t (postS q out res k n vs t rs) := by
  intro g g' h r hg
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · subst ht; exact stab_PS n rs g g' (h.1 rfl) r hg
  · subst ht; exact stab_CS k rs g g' (h.2 rfl) r hg

/-- **The producer is safe**, for every loop bound. -/
theorem prod_safe (X : SCtx q out res k n vs) (L : Nat) {rs : Regs}
    (hrdi : rs .rdi = BitVec.ofNat 64 q) :
    TSafe (ownS q out res k n) init (gpS q init) 0 (postS q out res k n vs 0)
      (prodS res vs L) rs W.zero := by
  refine tsafe_chain (fun j rs g => PS q res vs j rs g) _ 0 (fun i hi rs g h => ?_)
    (fun rs g h => tsafe_skip (fun rs => stab_post 0 rs)
      ⟨fun _ => ?_, fun h => absurd h (by decide)⟩)
    rs W.zero ⟨hrdi, [], rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [List.length_map, List.length_range] at hi
    simp only [Nat.zero_add, List.getElem_map, List.getElem_range] at h ⊢
    exact push_item X L i (X.hn ▸ hi) h (fun rs' g' h' => tsafe_skip (fun rs => stab_PS _ rs) h')
  · simpa [X.hn] using h

end Producer

/-! ## The consumer -/

theorem prefix_getElem? {α : Type} {l m : List α} (h : l <+: m) {i : Nat} (hi : i < l.length) :
    m[i]? = l[i]? := by
  obtain ⟨u, rfl⟩ := h; exact List.getElem?_append_left hi

theorem prefix_snoc {α : Type} {l m : List α} {v : α} (h : l <+: m) (hv : m[l.length]? = some v) :
    l ++ [v] <+: m := by
  obtain ⟨u, rfl⟩ := h
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hv
  cases u with
  | nil => simp at hv
  | cons x u =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
    subst hv
    exact ⟨u, by simp⟩

section Consumer

variable {q out res k n : Nat} {vs : List Nat} {init : Heap}

theorem popBody (L : Nat) : SpscPop.cert.body L = Tv.chain [SpscPop.ldH, SpscPop.ldT, SpscPop.a1,
    .ite SpscPop.zEmpty .skip (.seq SpscPop.b1 (.seq SpscPop.b2 (.seq SpscPop.b3 (.seq SpscPop.b4
      (.seq SpscPop.b5 (.seq SpscPop.b6 SpscPop.b7)))))), SpscPop.ret] := rfl

/-- The consumer's `head` store keeps the protocol invariant, given that it read a `tail` past
its `head`. -/
theorem gp_push1_head {g : W} (h : gpS q init g) (hw : WF g)
    (hT : cntH q (g.log 1) + 1 ≤ cntT q ((g.log 0).take (g.fl 0))) :
    gpS q init (g.push 1 (q, (cntH q (g.log 1) + 1) % 2 ^ 32)) := by
  obtain ⟨i1, i2, i3, i4⟩ := h
  refine ⟨by rw [push_log_ne _ (by decide)]; exact i1, ?_, ?_, ?_⟩
  · rw [push_log]
    refine invC_snoc i2 ?_
    rw [cellAfter_snoc, ite_t rfl, cntH_head]
  · rw [push_log_ne _ (by decide), push_log, push_fl, List.take_append_of_le_length (hw 1)]
    exact i3
  · rw [push_log, cntH_head, push_log_ne _ (by decide), push_fl]; exact hT

theorem stab_sv {Gp : W → Prop} {t : Nat} (H v : Nat) :
    Stab Gp t (fun g => (svals q (g.log 0))[H]? = some v) := by
  intro g g' h r _
  have hl : H < (svals q (g.log 0)).length := by
    rcases Nat.lt_or_ge H (svals q (g.log 0)).length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [prefix_getElem? (svals_prefix (r.2.1 0)) hl]; exact h

/-- The slot load, the output store and the `head` store of a pop that found data. -/
theorem pop_commit (X : SCtx q out res k n vs) {Q : Regs → W → Prop} {rs : Regs} {g : W}
    {Y : List (Nat × Nat)} {H T i : Nat} (hi : i < k) (R : W → Prop) (hR : Stab (gpS q init) 1 R)
    (hRp : ∀ g e, R g → R (g.push 1 e))
    (hrdi : rs .rdi = BitVec.ofNat 64 q) (hrsi : rs .rsi = BitVec.ofNat 64 (out + 4 * i))
    (hrax : rs .rax = BitVec.ofNat 64 ((H + 1) % 2 ^ 32)) (hrdx : rs .rdx = BitVec.ofNat 64 (H % 2))
    (hH : cntH q Y = H) (hT : H + 1 ≤ T)
    (hg : (g.log 1 = Y ∧ R g) ∧ WF g ∧ T ≤ cntT q ((g.log 0).take (g.fl 0)))
    (kk : ∀ v g', (svals q (g'.log 0))[H]? = some v → 0 < v ∧ v < 2 ^ 32 →
      g'.log 1 = Y ++ [(out + 4 * i, v), (q, (H + 1) % 2 ^ 32)] → R g' →
      TSafe (ownS q out res k n) init (gpS q init) 1 Q .skip
        ((rs.set .rdx (BitVec.ofNat 64 v)).set .rdx (Expr.eval (rs.set .rdx (BitVec.ofNat 64 v))
          (.lit 1))) g') :
    TSafe (ownS q out res k n) init (gpS q init) 1 Q
      (.seq SpscPop.b4 (.seq SpscPop.b5 (.seq SpscPop.b6 SpscPop.b7))) rs g := by
  have hq := X.hq
  have ho := X.hout
  have hdo := X.hdo
  have ha : ((atIdx .rdi .rdx 8).eval rs).toNat = slot q H := by
    rw [ev_atIdx hrdi hrdx (by omega)]; simp only [slot]; omega
  -- `mov edx, [rdi+4*rdx+8]`: the slot
  refine tsafe_seq_load _ (stab_tv _ (stab_and (stab_log _) hR) T) (fun g1 v h1 hgp1 _ _ hrd => ?_)
    hg
  rw [ha] at hrd
  have hc := rdOk_other X.hU (own0 (by rcases slot_cases (q := q) H with h | h <;> simp [h]))
    (by decide) hrd
  obtain ⟨⟨hY, hR1⟩, hw1, hT1⟩ := h1
  have hpx := hgp1.1 (g1.fl 0)
  have hHc : cntH q ((g1.log 1).take (g1.fl 1)) ≤ H := by
    rw [← hH, ← hY]; exact cnt_prefix _ (List.take_prefix _ _)
  have hS : cntS q ((g1.log 0).take (g1.fl 0)) ≤ H + 2 := by
    have := hgp1.2.2.1
    have := cnt_prefix (isS q) (List.take_prefix (g1.fl 0) (g1.log 0))
    simp only [cntS] at *; omega
  rw [hpx.2.2.1 H (by omega) hS] at hc
  have hlen : H < (svals q ((g1.log 0).take (g1.fl 0))).length := by
    rcases Nat.lt_or_ge H (svals q ((g1.log 0).take (g1.fl 0))).length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hc; cases hc
  have hsv : (svals q (g1.log 0))[H]? = some v := by
    rw [prefix_getElem? (svals_prefix (List.take_prefix _ _)) hlen]; exact hc
  have hvb : 0 < v ∧ v < 2 ^ 32 := hpx.2.2.2 v (List.mem_of_getElem? hc)
  -- `mov [rsi], edx`: the output
  have hrsi' : (rs.set .rdx (BitVec.ofNat 64 v)) .rsi = BitVec.ofNat 64 (out + 4 * i) := by
    simp [set_apply, hrsi]
  have hrdx' : (rs.set .rdx (BitVec.ofNat 64 v)) .rdx = BitVec.ofNat 64 v := by simp [set_apply]
  have hoi : out + 4 * i ≠ q := by omega
  refine tsafe_seq_store (fun g => ((g.log 1 = Y ∧ R g) ∧ WF g ∧
      T ≤ cntT q ((g.log 0).take (g.fl 0))) ∧ (svals q (g.log 0))[H]? = some v)
    (stab_and (stab_tv _ (stab_and (stab_log _) hR) T) (stab_sv H v)) ?_ ?_
    ⟨⟨⟨hY, hR1⟩, hw1, hT1⟩, hsv⟩
  · rw [eval_at 0 hrsi' (by omega), Nat.add_zero]; exact own1 (Or.inr ⟨i, hi, rfl⟩)
  rintro g2 ⟨⟨⟨hY2, hR2⟩, hw2, hT2⟩, hsv2⟩ hgp2 _
  rw [eval_at 0 hrsi' (by omega), Nat.add_zero, eval_reg_mod hrdx' hvb.2]
  refine ⟨gp_push1_other hgp2 hw2 hoi, ?_⟩
  apply tsafe_seq_assign
  -- `mov [rdi], eax`: publish `head`
  have hrdi'' : ((rs.set .rdx (BitVec.ofNat 64 v)).set .rdx (Expr.eval (rs.set .rdx
      (BitVec.ofNat 64 v)) (.lit 1))) .rdi = BitVec.ofNat 64 q := by simp [set_apply, hrdi]
  have hrax'' : ((rs.set .rdx (BitVec.ofNat 64 v)).set .rdx (Expr.eval (rs.set .rdx
      (BitVec.ofNat 64 v)) (.lit 1))) .rax = BitVec.ofNat 64 ((H + 1) % 2 ^ 32) := by
    simp [set_apply, hrax]
  refine tsafe_store (fun g => ((g.log 1 = Y ++ [(out + 4 * i, v)] ∧ R g) ∧ WF g ∧
      T ≤ cntT q ((g.log 0).take (g.fl 0))) ∧ (svals q (g.log 0))[H]? = some v)
    (stab_and (stab_tv _ (stab_and (stab_log _) hR) T) (stab_sv H v)) ?_ ?_
    ⟨⟨⟨by rw [push_log, hY2], hRp _ _ hR2⟩, wf_push hw2 _ _,
      by rw [push_log_ne _ (by decide), push_fl]; exact hT2⟩,
      by rw [push_log_ne _ (by decide)]; exact hsv2⟩
  · rw [eval_at 0 hrdi'' (by omega), Nat.add_zero]; exact own1 (Or.inl rfl)
  rintro g3 ⟨⟨⟨hY3, hR3⟩, hw3, hT3⟩, hsv3⟩ hgp3 _
  rw [eval_at 0 hrdi'' (by omega), Nat.add_zero, eval_reg_mod hrax'' (Nat.mod_lt _ (by decide))]
  have hH3 : cntH q (g3.log 1) = H := by rw [hY3, cntH_ne hoi, hH]
  refine ⟨hH3 ▸ gp_push1_head hgp3 hw3 (by rw [hH3]; omega), kk v _ ?_ hvb ?_ ?_⟩
  · rw [push_log_ne _ (by decide)]; exact hsv3
  · rw [push_log, hY3]; simp
  · exact hRp _ _ hR3

/-- `spsc_pop` after its two loads. -/
theorem pop_mid (X : SCtx q out res k n vs) {Q : Regs → W → Prop} {rs : Regs} {g : W}
    {Y : List (Nat × Nat)} {H T i : Nat} (hi : i < k) (R : W → Prop) (hR : Stab (gpS q init) 1 R)
    (hRp : ∀ g e, R g → R (g.push 1 e))
    (hrdi : rs .rdi = BitVec.ofNat 64 q) (hrsi : rs .rsi = BitVec.ofNat 64 (out + 4 * i))
    (hrax : rs .rax = BitVec.ofNat 64 (H % 2 ^ 32)) (hrcx : rs .rcx = BitVec.ofNat 64 (T % 2 ^ 32))
    (hH : cntH q Y = H) (h1 : H ≤ T) (h2 : T ≤ H + 2)
    (hg : (g.log 1 = Y ∧ R g) ∧ WF g ∧ T ≤ cntT q ((g.log 0).take (g.fl 0)))
    (kk : ∀ rs' g' (o : Option Nat), rs' .rdi = BitVec.ofNat 64 q → R g' →
      (o = none → g'.log 1 = Y) →
      (∀ v, o = some v → (svals q (g'.log 0))[H]? = some v ∧ 0 < v ∧ v < 2 ^ 32 ∧
        g'.log 1 = Y ++ [(out + 4 * i, v), (q, (H + 1) % 2 ^ 32)]) →
      TSafe (ownS q out res k n) init (gpS q init) 1 Q .skip rs' g') :
    TSafe (ownS q out res k n) init (gpS q init) 1 Q
      (Tv.chain [SpscPop.a1, .ite SpscPop.zEmpty .skip (.seq SpscPop.b1 (.seq SpscPop.b2
        (.seq SpscPop.b3 (.seq SpscPop.b4 (.seq SpscPop.b5 (.seq SpscPop.b6 SpscPop.b7)))))),
        SpscPop.ret]) rs g := by
  simp only [Tv.chain]
  apply tsafe_seq_assign
  apply tsafe_seq_ite
  have hm : ∀ x : Nat, x % 2 ^ 32 < 2 ^ 32 := fun x => Nat.mod_lt _ (by decide)
  rw [show SpscPop.zEmpty = zCmp .rax .rcx from rfl, truthy_cmp (x := H % 2 ^ 32)
    (y := T % 2 ^ 32) (by simp [set_apply, hrax]) (by simp [set_apply, hrcx]) (hm _) (hm _)]
  by_cases he : H % 2 ^ 32 = T % 2 ^ 32
  · simp only [he, decide_true, ite_true]
    apply tsafe_skip_of
    apply tsafe_seq_assign
    exact kk _ g none (by simp [set_apply, hrdi]) hg.1.2 (fun _ => hg.1.1)
      (fun v h => by cases h)
  · simp only [he, decide_false, Bool.false_eq_true, ite_false]
    have hT : H + 1 ≤ T := by omega
    apply tsafe_seq_assign
    apply tsafe_seq_assign
    apply tsafe_seq_assign
    refine pop_commit X hi R hR hRp ?_ ?_ ?_ ?_ hH hT hg (fun v g' hsv hvb hlog hR' =>
      tsafe_skip_of (tsafe_seq_assign (kk _ g' (some v) ?_ hR' (fun h => by cases h)
        (fun v' e => ?_))))
    · simp [set_apply, hrdi]
    · simp [set_apply, hrsi]
    · simp only [set_apply, reduceCtorEq, ite_true, ite_false]
      have := ev_add1 (rs := (rs.set .rdx ((op32 .xor .rdx (.reg .rdx)).eval rs)).set .rdx
        ((r32 .rax).eval (rs.set .rdx ((op32 .xor .rdx (.reg .rdx)).eval rs)))) (r := .rax)
        (x := H % 2 ^ 32) (by simp [set_apply, hrax]) (hm _)
      rw [this]; congr 1; omega
    · simp only [set_apply, reduceCtorEq, ite_true, ite_false]
      have := ev_and1 (rs := ((rs.set .rdx ((op32 .xor .rdx (.reg .rdx)).eval rs)).set .rdx
        ((r32 .rax).eval (rs.set .rdx ((op32 .xor .rdx (.reg .rdx)).eval rs)))).set .rax
        ((op32 .add .rax (.lit 1)).eval ((rs.set .rdx ((op32 .xor .rdx (.reg .rdx)).eval rs)).set
          .rdx ((r32 .rax).eval (rs.set .rdx ((op32 .xor .rdx (.reg .rdx)).eval rs))))))
        (r := .rdx) (x := H % 2 ^ 32)
        (by simp only [set_apply, reduceCtorEq, ite_true, ite_false]
            exact ev_r32 (by simp [set_apply, hrax]) (hm _)) (by omega)
      rw [this]; congr 1; omega
    · simp [set_apply, hrdi]
    · cases e; exact ⟨hsv, hvb.1, hvb.2, hlog⟩

/-- **One pop.** -/
theorem pop_item (X : SCtx q out res k n vs) (L i : Nat) (hi : i < k) {Q : Regs → W → Prop}
    {rs : Regs} {g : W} (hcs : CS q out k i rs g)
    (kk : ∀ rs' g', CS q out k (i + 1) rs' g' →
      TSafe (ownS q out res k n) init (gpS q init) 1 Q .skip rs' g') :
    TSafe (ownS q out res k n) init (gpS q init) 1 Q
      (Tv.chain [.assign .rsi (.lit (out + 4 * i)), SpscPop.cert.body L]) rs g := by
  obtain ⟨hrdi, sel, hsl, hcH, hpast, hfut, hpre⟩ := hcs
  have hq := X.hq
  have ho := X.hout
  have hdo := X.hdo
  let R : W → Prop := fun g' => sel.filterMap id <+: svals q (g'.log 0)
  have hR : Stab (gpS q init) 1 R := fun g g' h r _ => h.trans (svals_prefix (r.2.1 0))
  have hRp : ∀ g e, R g → R (g.push 1 e) := fun g e h => by
    show _ <+: _; rw [push_log_ne _ (by decide)]; exact h
  rw [popBody]
  simp only [Tv.chain]
  apply tsafe_seq_assign
  apply tsafe_seq
  have hrdi1 : (rs.set .rsi (Expr.eval rs (.lit (out + 4 * i)))) .rdi = BitVec.ofNat 64 q := by
    simp [set_apply, hrdi]
  -- `mov eax, [rdi]`: own `head`
  refine tsafe_seq_load (fun g' => g'.log 1 = g.log 1 ∧ R g') (stab_and (stab_log _) hR)
    (fun g1 a h1 hgp1 hw1 _ hrd => ?_) ⟨rfl, hpre⟩
  rw [eval_at 0 hrdi1 (by omega), Nat.add_zero] at hrd
  have ha := rdOk_own X.hU (own1 (Or.inl rfl)) hrd
  rw [invC_full hgp1.2.1, h1.1, Option.some.injEq] at ha
  -- `mov ecx, [rdi+4]`: the producer's `tail`
  have hrdi2 : ((rs.set .rsi (Expr.eval rs (.lit (out + 4 * i)))).set .rax
      (BitVec.ofNat 64 a)) .rdi = BitVec.ofNat 64 q := by simp [set_apply, hrdi]
  refine tsafe_seq_load (fun g' => (g'.log 1 = g.log 1 ∧ R g') ∧ WF g')
    (stab_and (stab_and (stab_log _) hR) stab_wf) (fun g2 b h2 hgp2 hw2 _ hrd => ?_) ⟨h1, hw1⟩
  rw [eval_at 4 hrdi2 (by omega)] at hrd
  have hb := rdOk_other X.hU (own0 (Or.inl rfl)) (by decide) hrd
  rw [(hgp2.1 (g2.fl 0)).1, Option.some.injEq] at hb
  have hG2 := hgp2.2.2.2
  have hG1 := hgp2.2.2.1
  rw [h2.1.1] at hG2
  have hle1 : cntT q ((g2.log 0).take (g2.fl 0)) ≤ cntT q (g2.log 0) :=
    cnt_prefix _ (List.take_prefix _ _)
  have hle2 := (invP_full hgp2.1).2.1
  have hle3 : cntH q ((g2.log 1).take (g2.fl 1)) ≤ cntH q (g.log 1) := by
    rw [← h2.1.1]; exact cnt_prefix _ (List.take_prefix _ _)
  refine pop_mid X hi R hR hRp ?_ ?_ ?_ ?_ (Y := g.log 1) rfl hG2 (by omega)
    ⟨h2.1, hw2, Nat.le_refl _⟩ (fun rs' g' o hrdi' hR' hnone hsome =>
      tsafe_skip_of (kk rs' g' ⟨hrdi', sel ++ [o], by simp [hsl], ?_, ?_, ?_, ?_⟩))
  · simp [set_apply, hrdi]
  · simp [set_apply, Expr.eval]
  · simp [set_apply, ← ha]
  · simp [set_apply, ← hb]
  all_goals have hpair : ∀ (l : List (Nat × Nat)) (a b : Nat × Nat),
    l ++ [a, b] = l ++ [a] ++ [b] := by simp
  all_goals have hoq : ∀ i', i' < k → out + 4 * i' ≠ q := fun i' hi' => by omega
  all_goals cases o with
  | none =>
    have hl := hnone rfl
    first
    | (rw [hl, hcH]; simp)
    | (intro i' hi'
       rw [hl]
       by_cases hii : i' = i
       · subst hii
         rw [hfut i' (Nat.le_refl _) hi]
         simp [List.getD_eq_getElem?_getD, ← hsl]
       · rw [hpast i' (by omega)]
         simp only [List.getD_eq_getElem?_getD]
         rw [List.getElem?_append_left (by omega)])
    | (intro i' hi' hk; rw [hl]; exact hfut i' (by omega) hk)
    | (have e : (sel ++ [none]).filterMap id = sel.filterMap id := by simp
       rw [e]; exact hR')
  | some v =>
    obtain ⟨hsv, _, _, hl⟩ := hsome v rfl
    first
    | (rw [hl, hpair, cntH_head, cntH_ne (hoq i hi), hcH]; simp)
    | (intro i' hi'
       rw [hl, hpair, lastV_snoc, lastV_snoc, ite_f (Ne.symm (hoq i' (by omega)))]
       by_cases hii : i' = i
       · subst hii
         rw [ite_t rfl]
         simp [List.getD_eq_getElem?_getD, ← hsl]
       · rw [ite_f (by omega), hpast i' (by omega)]
         simp only [List.getD_eq_getElem?_getD]
         rw [List.getElem?_append_left (by omega)])
    | (intro i' hi' hk
       rw [hl, hpair, lastV_snoc, lastV_snoc, ite_f (Ne.symm (hoq i' hk)), ite_f (by omega)]
       exact hfut i' (by omega) hk)
    | (have e : (sel ++ [some v]).filterMap id = sel.filterMap id ++ [v] := by simp
       rw [e]; exact prefix_snoc hR' (by rw [← hcH]; exact hsv))

/-- **The consumer is safe**, for every loop bound. -/
theorem cons_safe (X : SCtx q out res k n vs) (L : Nat) {rs : Regs}
    (hrdi : rs .rdi = BitVec.ofNat 64 q) :
    TSafe (ownS q out res k n) init (gpS q init) 1 (postS q out res k n vs 1)
      (consS out k L) rs W.zero := by
  refine tsafe_chain (fun i rs g => CS q out k i rs g) _ 0 (fun i hi rs g h => ?_)
    (fun rs g h => tsafe_skip (fun rs => stab_post 1 rs)
      ⟨fun h => absurd h (by decide), fun _ => by simpa using h⟩)
    rs W.zero ⟨hrdi, [], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ => rfl, List.nil_prefix⟩
  simp only [List.length_map, List.length_range] at hi
  simp only [Nat.zero_add, List.getElem_map, List.getElem_range] at h ⊢
  exact pop_item X L i hi h (fun rs' g' h' => tsafe_skip (fun rs => stab_CS _ rs) h')

end Consumer

/-! ## `Task.spscFifoTso` -/

theorem map_getD_range {sel : List (Option Nat)} (f : Option Nat → Nat) :
    (List.range sel.length).map (fun i => f (sel.getD i none)) = sel.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using h1)]; rfl

theorem filter_getD (sel : List (Option Nat)) (h : ∀ v, some v ∈ sel → v ≠ 0) :
    (sel.map (·.getD 0)).filter (· != 0) = sel.filterMap id := by
  induction sel with
  | nil => rfl
  | cons o sel ih =>
    have ih' := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    cases o with
    | none => simp [ih']
    | some v =>
      have := h v List.mem_cons_self
      simp [ih', this]

theorem drop_range {m : List Nat} {P H : Nat} (hm : m.length = P) (hH : H ≤ P) :
    (List.range (P - H)).map (fun j => (m[H + j]?).getD 0) = m.drop H := by
  apply List.ext_getElem (by simp [hm])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem?_eq_getElem (by omega)]; rfl

theorem own_uniqueS {q out res k n : Nat} (hdo : out + 4 * k ≤ q ∨ q + 16 ≤ out)
    (hdr : res + 4 * n ≤ q ∨ q + 16 ≤ res) (hro : res + 4 * n ≤ out ∨ out + 4 * k ≤ res) :
    ∀ t u c, ownS q out res k n t c → ownS q out res k n u c → t = u := by
  rintro t u c (⟨rfl, hc⟩ | ⟨rfl, hc⟩) (⟨rfl, hc'⟩ | ⟨rfl, hc'⟩)
  · rfl
  · exfalso
    rcases hc' with rfl | ⟨i, hi, rfl⟩ <;>
      rcases hc with h | h | h | ⟨j, hj, h⟩ <;> omega
  · exfalso
    rcases hc with rfl | ⟨i, hi, rfl⟩ <;>
      rcases hc' with h | h | h | ⟨j, hj, h⟩ <;> omega
  · rfl

/-- **`Task.spscFifoTso` is proved.** -/
theorem spscFifoTso_holds : Task.spscFifoTso := by
  intro L q out res k vs hq hout hres hdo hdr hro hvs prod cons C0 C hr hd hfin got pushed hh nn rem
  have hU := own_uniqueS (n := vs.length) hdo hdr hro
  have X : SCtx q out res k vs.length vs := ⟨hU, hq, hres, hout, hdr, hdo, hvs, rfl⟩
  have hmem0 : ∀ a, (a = q ∨ a = q + 4 ∨ a = q + 8 ∨ a = q + 12 ∨ ∃ i, i < k ∧ a = out + 4 * i) →
      C0.mem a = some 0 := by
    intro a ha
    refine heapOf_find ?_ (fun p hp _ => ?_) _
    · rcases ha with rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩
      · simp
      · simp
      · simp
      · simp
      · simp [hi]
    · simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
        List.not_mem_nil, or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl) | ⟨i, _, rfl⟩) | ⟨j, _, rfl⟩ <;> rfl
  have hT0 : ∀ t < 2, TSafe (ownS q out res k vs.length) C0.mem (gpS q C0.mem) t
      (postS q out res k vs.length vs t) (C0.ts t).1 (C0.ts t).2 W.zero := by
    intro t ht
    rcases t with _ | _ | t
    · exact prod_safe X L (by simp [C0, regs])
    · exact cons_safe X L (by simp [C0, regs])
    · omega
  have hG0 : gpS q C0.mem W.zero := by
    refine ⟨fun f => ?_, fun f => ?_, by simp [W.zero, cntS, cntH], by simp [W.zero, cntT, cntH]⟩
    · simp only [W.zero, List.take_nil]
      refine ⟨?_, by simp [cntT, cntS], fun H hH => by simp [cntT] at hH, fun x hx => by
        simp [svals] at hx⟩
      simp [cellAfter, lastV, cntT, hmem0 (q + 4) (Or.inr (Or.inl rfl))]
    · simp [W.zero, cellAfter, lastV, cntH, hmem0 q (Or.inl rfl)]
  obtain ⟨g, hgp, hpost, hcell, hfl⟩ := sw_final hU (fun g t h hw hl => gpS_flush g t h hw hl)
    hG0 hT0 hr hd hfin
  obtain ⟨_, bs, hbl, hcST, hsv, hresv⟩ := (hpost 0 (by decide)).1 rfl
  obtain ⟨_, sel, hsl, hcH, hpast, _, hpre⟩ := (hpost 1 (by decide)).2 rfl
  obtain ⟨i1, i2, i3, i4⟩ := hgp
  rw [List.take_of_length_le (Nat.le_of_eq (hfl 1).symm)] at i3
  rw [List.take_of_length_le (Nat.le_of_eq (hfl 0).symm)] at i4
  have hPf := invP_full i1
  have hlenS := svals_length q (g.log 0)
  -- the counts: `H` pops, `P` pushes, `H ≤ P ≤ H + 2`
  have hHP : cntH q (g.log 1) ≤ cntS q (g.log 0) := by omega
  -- memory
  have hq0 : C.mem q = some (cntH q (g.log 1) % 2 ^ 32) := by
    rw [hcell 1 q (own1 (Or.inl rfl))]; exact invC_full i2
  have ht0 : C.mem (q + 4) = some (cntS q (g.log 0) % 2 ^ 32) := by
    rw [hcell 0 _ (own0 (Or.inl rfl)), hPf.1, hcST]
  have hhh : hh = cntH q (g.log 1) % 2 ^ 32 := by simp only [hh, hq0, Option.getD_some]
  have hnn : nn = cntS q (g.log 0) - cntH q (g.log 1) := by
    simp only [nn, hhh, ht0, Option.getD_some]; omega
  -- `got`: the successful pops, a prefix of the slot values
  have hfm : sel.filterMap id = (svals q (g.log 0)).take (cntH q (g.log 1)) := by
    rw [hcH]; exact List.prefix_iff_eq_take.mp hpre
  have hnz : ∀ v, some v ∈ sel → v ≠ 0 := by
    intro v hv
    have hv' : v ∈ sel.filterMap id := List.mem_filterMap.mpr ⟨_, hv, rfl⟩
    exact Nat.pos_iff_ne_zero.mp (hPf.2.2.2 v (hpre.subset hv')).1
  have hgot : got = (svals q (g.log 0)).take (cntH q (g.log 1)) := by
    have hm : ((List.range k).map fun i => (C.mem (out + 4 * i)).getD 0) =
        sel.map (·.getD 0) := by
      rw [← hsl, ← map_getD_range]
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [hcell 1 _ (own1 (Or.inr ⟨i, by omega, rfl⟩)), cellAfter, hpast i (by omega),
        hmem0 _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, by omega, rfl⟩))))]
      cases sel.getD i none <;> rfl
    simp only [got, hm]
    rw [filter_getD sel hnz, hfm]
  -- `pushed`: the successful pushes
  have hpushed : pushed = pushedOf vs bs := by
    simp only [pushed, pushedOf, hbl]
    congr 1
    apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    rw [hcell 0 _ (own0 (Or.inr (Or.inr (Or.inr ⟨j, hj, rfl⟩)))), cellAfter, hresv j hj]
    cases bs.getD j false <;> rfl
  -- `rem`: the values still in the ring
  have hrem : rem = (svals q (g.log 0)).drop (cntH q (g.log 1)) := by
    simp only [rem, hnn, hhh]
    rw [← drop_range hlenS hHP]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hs : q + 8 + 4 * ((cntH q (g.log 1) % 2 ^ 32 + j) % 2) =
        slot q (cntH q (g.log 1) + j) := by
      simp only [slot]; omega
    rw [hs, hcell 0 _ (own0 (by rcases slot_cases (q := q) (cntH q (g.log 1) + j) with h | h <;>
      simp [h])), hPf.2.2.1 _ (by omega) (by omega)]
  rw [hgot, hrem, hpushed, List.take_append_drop, hsv]

end Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Spsc
