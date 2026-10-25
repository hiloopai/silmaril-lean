module

public import Silmaril.Logic.Metamath.Peano.Arithmetic
public import Silmaril.Logic.Metamath.Peano.ZFC
public import Silmaril.Logic.SetTheory.Nat

@[expose] public section

/-!
# Interpreting Peano arithmetic in set theory

The translation `Peano.ToZF.tr` of arithmetic formulas of `peano.mm` into
formulas of set.mm's primitive language of set theory (`Peano.ZF.grammar`:
`-.`, `->`, `<->`, `/\`, `\/`, `A.`, `E.`, `=`, `e.` between set variables):

* the object variable `a` becomes the set variable `pv a`, and quantifiers are
  relativized to the natural numbers: `forall x phi` becomes
  `A. x ( Nat x -> phi' )`, where `Nat x` says that `x` lies in every
  inductive set (every set containing the empty set and closed under the
  successor `suc y = y u. { y }`);
* numbers are von Neumann numerals: a term `t` is replaced by a formula
  `Val t r` saying that `r` is its value (`Peano.ToZF.val`): `0` is the empty
  set, `S t` the successor;
* addition and multiplication are defined by their recursion equations through
  graphs of Kuratowski triples `<< a , b > , c >`: `a + b = r` says that
  `<< a , b > , r >` lies in every set containing `<< a , 0 > , a >` and closed
  under `<< a , n > , k > ↦ << a , suc n > , suc k >`, and similarly for
  multiplication, whose recursion step uses addition;
* `s = t` becomes `E. v ( Val s v /\ Val t v )`, and `s < t` membership of the
  values.

Every auxiliary variable is bound; the `k`-th fresh variable is `hv k`, chosen
above every variable in scope. Truth in the environment model over `ZFSet` of
the translation of `φ`, with the object variables at von Neumann numerals, is
truth of `φ` in ℕ (`Peano.ToZF.S_tr`).
-/

namespace Silmaril.Logic.Metamath.Peano.ToZF

open Silmaril.Logic.Metamath Grammar Silmaril.Logic.SetTheory Function ZF.T

/-- The set variable interpreting the object variable `a`. -/
def pv (a : V) : ZF.V := .var (2 * a.code)

/-- The `k`-th auxiliary bound variable. -/
def hv (k : ℕ) : ZF.V := .var (2 * k + 1)

@[simp] theorem hv_inj {j k : ℕ} : hv j = hv k ↔ j = k := by
  simp only [hv, ZF.V.var.injEq]
  omega

@[simp] theorem pv_inj {a b : V} : pv a = pv b ↔ a = b := by
  simp only [pv, ZF.V.var.injEq]
  exact ⟨fun h => V.code_injective (by omega), fun h => h ▸ rfl⟩

@[simp] theorem hv_ne_pv (k : ℕ) (a : V) : hv k ≠ pv a := by
  simp only [hv, pv, ne_eq, ZF.V.var.injEq]
  omega

@[simp] theorem pv_ne_hv (a : V) (k : ℕ) : pv a ≠ hv k := (hv_ne_pv k a).symm

/-- The variable `r` is not an auxiliary variable of index at least `d`. -/
def Above (d : ℕ) (r : ZF.V) : Prop := ∀ k, d ≤ k → r ≠ hv k

theorem above_pv (d : ℕ) (a : V) : Above d (pv a) := fun k _ => pv_ne_hv a k

theorem above_hv {d j : ℕ} (h : j < d) : Above d (hv j) := fun k hk => by
  simp only [ne_eq, hv_inj]; omega

theorem Above.mono {d d' : ℕ} {r : ZF.V} (h : Above d r) (hd : d ≤ d') : Above d' r :=
  fun k hk => h k (hd.trans hk)

/-! ## Building blocks -/

/-- `r` is empty. -/
def empty (r : ZF.V) (d : ℕ) : Tree ZF.L ZF.V := wal (hv d) (wn (wel (hv d) r))

/-- `r` is the successor of `a`: `A. z ( z e. r <-> ( z e. a \/ z = a ) )`. -/
def suc (a r : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wal (hv d) (wb (wel (hv d) r) (wo (wel (hv d) a) (weq (hv d) a)))

/-- `s` is the singleton of `a`. -/
def sing (s a : ZF.V) (d : ℕ) : Tree ZF.L ZF.V := wal (hv d) (wb (wel (hv d) s) (weq (hv d) a))

/-- `s` is the unordered pair of `a` and `b`. -/
def dbl (s a b : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wal (hv d) (wb (wel (hv d) s) (wo (weq (hv d) a) (weq (hv d) b)))

/-- `p` is the Kuratowski pair `< a , b > = { { a } , { a , b } }`. -/
def isPair (p a b : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wal (hv d) (wb (wel (hv d) p) (wo (sing (hv d) a (d + 1)) (dbl (hv d) a b (d + 1))))

/-- The triple `<< a , b > , c >` is a member of `g`. -/
def tripIn (a b c g : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wex (hv d) (wa (isPair (hv d) a b (d + 1))
    (wex (hv (d + 1)) (wa (isPair (hv (d + 1)) (hv d) c (d + 2)) (wel (hv (d + 1)) g))))

/-- `y` is inductive: it contains the empty set and is closed under successor. -/
def ind (c : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wa (wex (hv d) (wa (empty (hv d) (d + 1)) (wel (hv d) c)))
    (wal (hv d) (wi (wel (hv d) c)
      (wex (hv (d + 1)) (wa (suc (hv d) (hv (d + 1)) (d + 2)) (wel (hv (d + 1)) c)))))

/-- `a` is a natural number: it lies in every inductive set. -/
def nat (a : ZF.V) (d : ℕ) : Tree ZF.L ZF.V := wal (hv d) (wi (ind (hv d) (d + 1)) (wel a (hv d)))

/-- `g` contains `<< a , 0 > , a >` and is closed under
`<< a , n > , k > ↦ << a , suc n > , suc k >`. -/
def addClosed (a g : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wa (wex (hv d) (wa (empty (hv d) (d + 1)) (tripIn a (hv d) a g (d + 1))))
    (wal (hv d) (wal (hv (d + 1)) (wi (tripIn a (hv d) (hv (d + 1)) g (d + 2))
      (wal (hv (d + 2)) (wi (suc (hv d) (hv (d + 2)) (d + 3))
        (wal (hv (d + 3)) (wi (suc (hv (d + 1)) (hv (d + 3)) (d + 4))
          (tripIn a (hv (d + 2)) (hv (d + 3)) g (d + 4)))))))))

/-- `a + b = r`: `<< a , b > , r >` lies in every set closed as in `addClosed`. -/
def addRel (a b r : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wal (hv d) (wi (addClosed a (hv d) (d + 1)) (tripIn a b r (hv d) (d + 1)))

/-- `g` contains `<< a , 0 > , 0 >` and is closed under
`<< a , n > , k > ↦ << a , suc n > , k + a >`. -/
def mulClosed (a g : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wa (wex (hv d) (wa (empty (hv d) (d + 1)) (tripIn a (hv d) (hv d) g (d + 1))))
    (wal (hv d) (wal (hv (d + 1)) (wi (tripIn a (hv d) (hv (d + 1)) g (d + 2))
      (wal (hv (d + 2)) (wi (suc (hv d) (hv (d + 2)) (d + 3))
        (wal (hv (d + 3)) (wi (addRel (hv (d + 1)) a (hv (d + 3)) (d + 4))
          (tripIn a (hv (d + 2)) (hv (d + 3)) g (d + 4)))))))))

/-- `a * b = r`: `<< a , b > , r >` lies in every set closed as in `mulClosed`. -/
def mulRel (a b r : ZF.V) (d : ℕ) : Tree ZF.L ZF.V :=
  wal (hv d) (wi (mulClosed a (hv d) (d + 1)) (tripIn a b r (hv d) (d + 1)))

/-! ## The translation -/

/-- `Val t r`: `r` is the value of the arithmetic term `t`. -/
def val : Tree L V → ZF.V → ℕ → Tree ZF.L ZF.V
  | .node .tvar [.var a], r, _ => weq r (pv a)
  | .node .tzero [], r, d => empty r d
  | .node .tsucc [s], r, d => wex (hv d) (wa (val s (hv d) (d + 1)) (suc (hv d) r (d + 1)))
  | .node .tbinop [s, t, .node .binopPlus []], r, d =>
    wex (hv d) (wex (hv (d + 1)) (wa (val s (hv d) (d + 2))
      (wa (val t (hv (d + 1)) (d + 2)) (addRel (hv d) (hv (d + 1)) r (d + 2)))))
  | .node .tbinop [s, t, .node .binopTimes []], r, d =>
    wex (hv d) (wex (hv (d + 1)) (wa (val s (hv d) (d + 2))
      (wa (val t (hv (d + 1)) (d + 2)) (mulRel (hv d) (hv (d + 1)) r (d + 2)))))
  | _, r, _ => wn (weq r r)

/-- The translation of an arithmetic formula, with auxiliary variables from
index `d` on. -/
def tr : Tree L V → ℕ → Tree ZF.L ZF.V
  | .node .wffAtom [s, t, .node .binpredEquals []], d =>
    wex (hv d) (wa (val s (hv d) (d + 1)) (val t (hv d) (d + 1)))
  | .node .wffAtom [s, t, .node .binpredLessThan []], d =>
    wex (hv d) (wex (hv (d + 1)) (wa (val s (hv d) (d + 2))
      (wa (val t (hv (d + 1)) (d + 2)) (wel (hv d) (hv (d + 1))))))
  | .node .wffNot [a], d => wn (tr a d)
  | .node .wffLogbinop [.node .logbinopImplies [], b, a], d => wi (tr a d) (tr b d)
  | .node .wffLogbinop [.node .logbinopOr [], b, a], d => wo (tr a d) (tr b d)
  | .node .wffLogbinop [.node .logbinopAnd [], b, a], d => wa (tr a d) (tr b d)
  | .node .wffLogbinop [.node .logbinopIff [], b, a], d => wb (tr a d) (tr b d)
  | .node .wffQuant [.var w, .node .quantAll [], a], d =>
    wal (pv w) (wi (nat (pv w) d) (tr a d))
  | .node .wffQuant [.var w, .node .quantEx [], a], d =>
    wex (pv w) (wa (nat (pv w) d) (tr a d))
  | _, d => wn (weq (hv d) (hv d))

/-! ## Semantics of the building blocks -/

/-- The Tarski semantics of a formula of set theory under an assignment of
sets to variables. -/
abbrev S (t : Tree ZF.L ZF.V) (F : ZF.V → ZFSet.{0}) : Prop := ZF.sem id t F

section Blocks

open ZFSet

variable {d : ℕ}

theorem S_empty {r : ZF.V} (hr : Above d r) (F : ZF.V → ZFSet.{0}) :
    S (empty r d) F ↔ F r = ∅ := by
  simp only [empty, ZF.sem_wal, ZF.sem_wn, ZF.sem_wel, id, update_self,
    update_of_ne (hr d le_rfl)]
  exact (eq_empty _).symm

theorem S_suc {a r : ZF.V} (ha : Above d a) (hr : Above d r) (F : ZF.V → ZFSet.{0}) :
    S (suc a r d) F ↔ F r = succ (F a) := by
  simp only [suc, ZF.sem_wal, ZF.sem_wb, ZF.sem_wo, ZF.sem_wel, ZF.sem_weq, id, update_self,
    update_of_ne (hr d le_rfl), update_of_ne (ha d le_rfl)]
  constructor
  · intro h
    exact ZFSet.ext fun m => (h m).trans (by rw [mem_succ, or_comm])
  · intro h m
    rw [h, mem_succ, or_comm]

theorem S_sing {s a : ZF.V} (hs : Above d s) (ha : Above d a) (F : ZF.V → ZFSet.{0}) :
    S (sing s a d) F ↔ F s = {F a} := by
  simp only [sing, ZF.sem_wal, ZF.sem_wb, ZF.sem_wel, ZF.sem_weq, id, update_self,
    update_of_ne (hs d le_rfl), update_of_ne (ha d le_rfl)]
  exact ⟨fun h => ZFSet.ext fun m => (h m).trans mem_singleton.symm,
    fun h m => by rw [h, mem_singleton]⟩

theorem S_dbl {s a b : ZF.V} (hs : Above d s) (ha : Above d a) (hb : Above d b)
    (F : ZF.V → ZFSet.{0}) : S (dbl s a b d) F ↔ F s = {F a, F b} := by
  simp only [dbl, ZF.sem_wal, ZF.sem_wb, ZF.sem_wo, ZF.sem_wel, ZF.sem_weq, id, update_self,
    update_of_ne (hs d le_rfl), update_of_ne (ha d le_rfl), update_of_ne (hb d le_rfl)]
  exact ⟨fun h => ZFSet.ext fun m => (h m).trans mem_pair.symm, fun h m => by rw [h, mem_pair]⟩

theorem S_isPair {p a b : ZF.V} (hp : Above d p) (ha : Above d a) (hb : Above d b)
    (F : ZF.V → ZFSet.{0}) : S (isPair p a b d) F ↔ F p = pair (F a) (F b) := by
  simp only [isPair, ZF.sem_wal, ZF.sem_wb, ZF.sem_wo, ZF.sem_wel, id, update_self,
    update_of_ne (hp d le_rfl),
    S_sing (above_hv (Nat.lt_succ_self d)) (ha.mono (Nat.le_succ d)),
    S_dbl (above_hv (Nat.lt_succ_self d)) (ha.mono (Nat.le_succ d)) (hb.mono (Nat.le_succ d)),
    update_of_ne (ha d le_rfl), update_of_ne (hb d le_rfl)]
  exact ⟨fun h => ZFSet.ext fun m => (h m).trans mem_pair.symm, fun h m => by
    rw [h, pair, mem_pair]⟩

theorem S_tripIn {a b c g : ZF.V} (ha : Above d a) (hb : Above d b) (hc : Above d c)
    (hg : Above d g) (F : ZF.V → ZFSet.{0}) :
    S (tripIn a b c g d) F ↔ pair (pair (F a) (F b)) (F c) ∈ F g := by
  have h1 : d ≤ d + 1 := Nat.le_succ d
  have h2 : d + 1 ≤ d + 2 := Nat.le_succ _
  simp only [tripIn, ZF.sem_wex, ZF.sem_wa, ZF.sem_wel, id,
    S_isPair (above_hv (Nat.lt_succ_self d)) (ha.mono h1) (hb.mono h1),
    S_isPair (above_hv (Nat.lt_succ_self (d + 1))) (above_hv (by omega : d < d + 2))
      (hc.mono (h1.trans h2)),
    update_apply, hv_inj, ha d le_rfl, hb d le_rfl, hc d le_rfl, hc (d + 1) h1, hg d le_rfl,
    hg (d + 1) h1, ↓reduceIte, (Nat.succ_ne_self d).symm]
  simp

theorem S_ind {c : ZF.V} (hc : Above d c) (F : ZF.V → ZFSet.{0}) :
    S (ind c d) F ↔ ∅ ∈ F c ∧ ∀ z ∈ F c, succ z ∈ F c := by
  have h1 : d ≤ d + 1 := Nat.le_succ d
  simp only [ind, ZF.sem_wex, ZF.sem_wa, ZF.sem_wal, ZF.sem_wi, ZF.sem_wel, id,
    S_empty (above_hv (Nat.lt_succ_self d)),
    S_suc (above_hv (by omega : d < d + 2)) (above_hv (by omega : d + 1 < d + 2)),
    update_apply, hv_inj, hc d le_rfl, hc (d + 1) h1, ↓reduceIte, (Nat.succ_ne_self d).symm]
  simp

theorem S_nat {a : ZF.V} (ha : Above d a) (F : ZF.V → ZFSet.{0}) :
    S (nat a d) F ↔ F a ∈ omega := by
  simp only [nat, ZF.sem_wal, ZF.sem_wi, ZF.sem_wel, id, S_ind (above_hv (Nat.lt_succ_self d)),
    update_apply, ha d le_rfl, ↓reduceIte]
  constructor
  · intro h
    exact h omega ⟨omega_zero, fun z hz => omega_succ hz⟩
  · rintro h y ⟨h0, hs⟩
    exact omega_subset_of_inductive h0 hs h

end Blocks

/-! ## Addition and multiplication graphs -/

section Graphs

open ZFSet

/-- `g` contains `<< a , 0 > , a >` and is closed under
`<< a , n > , k > ↦ << a , suc n > , suc k >`. -/
def AddClosed (a g : ZFSet.{0}) : Prop :=
  pair (pair a ∅) a ∈ g ∧ ∀ n k, pair (pair a n) k ∈ g → pair (pair a (succ n)) (succ k) ∈ g

/-- `a + b = r` as membership in every `AddClosed` set. -/
def AddRel (a b r : ZFSet.{0}) : Prop := ∀ g, AddClosed a g → pair (pair a b) r ∈ g

/-- `g` contains `<< a , 0 > , 0 >` and is closed under
`<< a , n > , k > ↦ << a , suc n > , k + a >`. -/
def MulClosed (a g : ZFSet.{0}) : Prop :=
  pair (pair a ∅) ∅ ∈ g ∧
    ∀ n k, pair (pair a n) k ∈ g → ∀ l, AddRel k a l → pair (pair a (succ n)) l ∈ g

/-- `a * b = r` as membership in every `MulClosed` set. -/
def MulRel (a b r : ZFSet.{0}) : Prop := ∀ g, MulClosed a g → pair (pair a b) r ∈ g

/-- The graph `{<< a , n > , f n >}` over the numerals `n`. -/
noncomputable def graphAt (a : ZFSet.{0}) (f : ℕ → ℕ) : ZFSet.{0} :=
  range fun n : ℕ => pair (pair a (numeral n)) (numeral (f n))

theorem mem_graphAt {a z : ZFSet.{0}} {f : ℕ → ℕ} :
    z ∈ graphAt a f ↔ ∃ n, pair (pair a (numeral n)) (numeral (f n)) = z := mem_range

theorem pair_mem_graphAt {a b r : ZFSet.{0}} {f : ℕ → ℕ} :
    pair (pair a b) r ∈ graphAt a f ↔ ∃ n, b = numeral n ∧ r = numeral (f n) := by
  rw [mem_graphAt]
  constructor
  · rintro ⟨n, h⟩
    simp only [pair_inj] at h
    exact ⟨n, h.1.2.symm, h.2.symm⟩
  · rintro ⟨n, rfl, rfl⟩
    exact ⟨n, rfl⟩

/-- On numerals, `AddRel` is the graph of addition. -/
theorem addRel_numeral (m n : ℕ) (r : ZFSet.{0}) :
    AddRel (numeral m) (numeral n) r ↔ r = numeral (m + n) := by
  constructor
  · intro h
    have hc : AddClosed (numeral m) (graphAt (numeral m) (m + ·)) := by
      refine ⟨pair_mem_graphAt.2 ⟨0, rfl, rfl⟩, fun b k hb => ?_⟩
      obtain ⟨j, rfl, rfl⟩ := pair_mem_graphAt.1 hb
      exact pair_mem_graphAt.2 ⟨j + 1, rfl, rfl⟩
    obtain ⟨j, hj, rfl⟩ := pair_mem_graphAt.1 (h _ hc)
    rw [numeral_inj.1 hj]
  · rintro rfl g ⟨h0, hs⟩
    induction n with
    | zero => exact h0
    | succ n ih => exact hs _ _ ih

/-- On numerals, `MulRel` is the graph of multiplication. -/
theorem mulRel_numeral (m n : ℕ) (r : ZFSet.{0}) :
    MulRel (numeral m) (numeral n) r ↔ r = numeral (m * n) := by
  constructor
  · intro h
    have hc : MulClosed (numeral m) (graphAt (numeral m) (m * ·)) := by
      refine ⟨pair_mem_graphAt.2 ⟨0, rfl, by simp⟩, fun b k hb l hl => ?_⟩
      obtain ⟨j, rfl, rfl⟩ := pair_mem_graphAt.1 hb
      rw [addRel_numeral] at hl
      exact pair_mem_graphAt.2 ⟨j + 1, rfl, by rw [hl, Nat.mul_succ]⟩
    obtain ⟨j, hj, rfl⟩ := pair_mem_graphAt.1 (h _ hc)
    rw [numeral_inj.1 hj]
  · rintro rfl g ⟨h0, hs⟩
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      exact hs _ _ ih _ ((addRel_numeral _ _ _).2 (by rw [Nat.mul_succ]))

theorem S_addClosed {d : ℕ} {a g : ZF.V} (ha : Above d a) (hg : Above d g)
    (F : ZF.V → ZFSet.{0}) : S (addClosed a g d) F ↔ AddClosed (F a) (F g) := by
  have hd : ∀ k, d ≤ d + k := fun k => Nat.le_add_right d k
  simp only [addClosed, ZF.sem_wex, ZF.sem_wa, ZF.sem_wal, ZF.sem_wi, id,
    S_empty (above_hv (by omega : d < d + 1)),
    S_tripIn (ha.mono (hd 1)) (above_hv (by omega : d < d + 1)) (ha.mono (hd 1)) (hg.mono (hd 1)),
    S_tripIn (ha.mono (hd 2)) (above_hv (by omega : d < d + 2))
      (above_hv (by omega : d + 1 < d + 2))
      (hg.mono (hd 2)),
    S_suc (above_hv (by omega : d < d + 3)) (above_hv (by omega : d + 2 < d + 3)),
    S_suc (above_hv (by omega : d + 1 < d + 4)) (above_hv (by omega : d + 3 < d + 4)),
    S_tripIn (ha.mono (hd 4)) (above_hv (by omega : d + 2 < d + 4))
      (above_hv (by omega : d + 3 < d + 4)) (hg.mono (hd 4)),
    update_apply, hv_inj, ha d (hd 0), ha (d + 1) (hd 1), ha (d + 2) (hd 2), ha (d + 3) (hd 3),
    hg d (hd 0), hg (d + 1) (hd 1), hg (d + 2) (hd 2), hg (d + 3) (hd 3), ↓reduceIte]
  simp [AddClosed]

theorem S_addRel {d : ℕ} {a b r : ZF.V} (ha : Above d a) (hb : Above d b) (hr : Above d r)
    (F : ZF.V → ZFSet.{0}) : S (addRel a b r d) F ↔ AddRel (F a) (F b) (F r) := by
  have hd : ∀ k, d ≤ d + k := fun k => Nat.le_add_right d k
  simp only [addRel, ZF.sem_wal, ZF.sem_wi, id,
    S_addClosed (ha.mono (hd 1)) (above_hv (by omega : d < d + 1)),
    S_tripIn (ha.mono (hd 1)) (hb.mono (hd 1)) (hr.mono (hd 1)) (above_hv (by omega : d < d + 1)),
    update_apply, ha d (hd 0), hb d (hd 0), hr d (hd 0), ↓reduceIte]
  rfl

theorem S_mulClosed {d : ℕ} {a g : ZF.V} (ha : Above d a) (hg : Above d g)
    (F : ZF.V → ZFSet.{0}) : S (mulClosed a g d) F ↔ MulClosed (F a) (F g) := by
  have hd : ∀ k, d ≤ d + k := fun k => Nat.le_add_right d k
  simp only [mulClosed, ZF.sem_wex, ZF.sem_wa, ZF.sem_wal, ZF.sem_wi, id,
    S_empty (above_hv (by omega : d < d + 1)),
    S_tripIn (ha.mono (hd 1)) (above_hv (by omega : d < d + 1)) (above_hv (by omega : d < d + 1))
      (hg.mono (hd 1)),
    S_tripIn (ha.mono (hd 2)) (above_hv (by omega : d < d + 2))
      (above_hv (by omega : d + 1 < d + 2))
      (hg.mono (hd 2)),
    S_suc (above_hv (by omega : d < d + 3)) (above_hv (by omega : d + 2 < d + 3)),
    S_addRel (above_hv (by omega : d + 1 < d + 4)) (ha.mono (hd 4))
      (above_hv (by omega : d + 3 < d + 4)),
    S_tripIn (ha.mono (hd 4)) (above_hv (by omega : d + 2 < d + 4))
      (above_hv (by omega : d + 3 < d + 4)) (hg.mono (hd 4)),
    update_apply, hv_inj, ha d (hd 0), ha (d + 1) (hd 1), ha (d + 2) (hd 2), ha (d + 3) (hd 3),
    hg d (hd 0), hg (d + 1) (hd 1), hg (d + 2) (hd 2), hg (d + 3) (hd 3), ↓reduceIte]
  simp [MulClosed]

theorem S_mulRel {d : ℕ} {a b r : ZF.V} (ha : Above d a) (hb : Above d b) (hr : Above d r)
    (F : ZF.V → ZFSet.{0}) : S (mulRel a b r d) F ↔ MulRel (F a) (F b) (F r) := by
  have hd : ∀ k, d ≤ d + k := fun k => Nat.le_add_right d k
  simp only [mulRel, ZF.sem_wal, ZF.sem_wi, id,
    S_mulClosed (ha.mono (hd 1)) (above_hv (by omega : d < d + 1)),
    S_tripIn (ha.mono (hd 1)) (hb.mono (hd 1)) (hr.mono (hd 1)) (above_hv (by omega : d < d + 1)),
    update_apply, ha d (hd 0), hb d (hd 0), hr d (hd 0), ↓reduceIte]
  rfl

end Graphs

/-! ## Correctness of the translation -/

section Correctness

open ZFSet

theorem update_pv_of_hv {F : ZF.V → ZFSet.{0}} {k : ℕ} {m : ZFSet.{0}} (a : V) :
    update F (hv k) m (pv a) = F (pv a) := update_of_ne (pv_ne_hv a k) _ _

/-- The value formula of an arithmetic term defines its value, with the object
variables at numerals. -/
theorem S_val : ∀ (t : Tree L V), IsArithTerm t → ∀ (e : V → ℕ) {r : ZF.V} {d : ℕ}, Above d r →
    ∀ (F : ZF.V → ZFSet.{0}), (∀ a ∈ t.vars, F (pv a) = numeral (e a)) →
      (S (val t r d) F ↔ F r = numeral (evalTerm e t)) := by
  intro t
  induction t using Tree.induction with
  | var a => intro ht; cases ht with | var hv => cases hv
  | node l args ih =>
    intro ht e r d hr F hF
    rcases ht.cases with ⟨a, h⟩ | h | ⟨a, h, ha⟩ | ⟨a, b, h, ha, hb⟩ | ⟨a, b, h, ha, hb⟩ <;>
      cases h
    · simp only [val, ZF.sem_weq, id, evalTerm_tv]
      rw [hF a (by simp)]
    · simp only [val, S_empty hr, evalTerm_zero, numeral_zero]
    · have ih' : ∀ m, S (val a (hv d) (d + 1)) (update F (hv d) m) ↔
          m = numeral (evalTerm e a) := fun m => by
        rw [ih a (by simp) ha e (above_hv (Nat.lt_succ_self d)) _
          (fun c hc => by rw [update_pv_of_hv]; exact hF c (by simpa using hc)), update_self]
      simp only [val, ZF.sem_wex, ZF.sem_wa, id, ih',
        S_suc (above_hv (Nat.lt_succ_self d)) (hr.mono (Nat.le_succ d)), update_self,
        update_of_ne (hr d le_rfl), exists_eq_left, evalTerm_succ, numeral_succ]
    · have h2 : d ≤ d + 2 := Nat.le_add_right d 2
      have iha : ∀ m m', S (val a (hv d) (d + 2)) (update (update F (hv d) m) (hv (d + 1)) m') ↔
          m = numeral (evalTerm e a) := fun m m' => by
        rw [ih a (by simp) ha e (above_hv (by omega : d < d + 2)) _
          (fun c hc => by
            rw [update_pv_of_hv, update_pv_of_hv]; exact hF c (by simp [hc]))]
        simp
      have ihb : ∀ m m', S (val b (hv (d + 1)) (d + 2))
          (update (update F (hv d) m) (hv (d + 1)) m') ↔ m' = numeral (evalTerm e b) :=
        fun m m' => by
          rw [ih b (by simp) hb e (above_hv (by omega : d + 1 < d + 2)) _
            (fun c hc => by
              rw [update_pv_of_hv, update_pv_of_hv]; exact hF c (by simp [hc]))]
          simp
      simp only [val, ZF.sem_wex, ZF.sem_wa, id, iha, ihb,
        S_addRel (above_hv (by omega : d < d + 2)) (above_hv (by omega : d + 1 < d + 2))
          (hr.mono h2), update_apply, hv_inj, hr d le_rfl, hr (d + 1) (Nat.le_succ d),
        ↓reduceIte, (Nat.succ_ne_self d).symm, evalTerm_plus, exists_and_left, exists_eq_left]
      exact addRel_numeral _ _ _
    · have h2 : d ≤ d + 2 := Nat.le_add_right d 2
      have iha : ∀ m m', S (val a (hv d) (d + 2)) (update (update F (hv d) m) (hv (d + 1)) m') ↔
          m = numeral (evalTerm e a) := fun m m' => by
        rw [ih a (by simp) ha e (above_hv (by omega : d < d + 2)) _
          (fun c hc => by
            rw [update_pv_of_hv, update_pv_of_hv]; exact hF c (by simp [hc]))]
        simp
      have ihb : ∀ m m', S (val b (hv (d + 1)) (d + 2))
          (update (update F (hv d) m) (hv (d + 1)) m') ↔ m' = numeral (evalTerm e b) :=
        fun m m' => by
          rw [ih b (by simp) hb e (above_hv (by omega : d + 1 < d + 2)) _
            (fun c hc => by
              rw [update_pv_of_hv, update_pv_of_hv]; exact hF c (by simp [hc]))]
          simp
      simp only [val, ZF.sem_wex, ZF.sem_wa, id, iha, ihb,
        S_mulRel (above_hv (by omega : d < d + 2)) (above_hv (by omega : d + 1 < d + 2))
          (hr.mono h2), update_apply, hv_inj, hr d le_rfl, hr (d + 1) (Nat.le_succ d),
        ↓reduceIte, (Nat.succ_ne_self d).symm, evalTerm_times, exists_and_left, exists_eq_left]
      exact mulRel_numeral _ _ _

/-- Correctness of the translation: with the object variables at the
numerals of their values, the translation of an arithmetic formula holds in
`ZFSet` exactly when the formula is true in ℕ. -/
theorem S_tr : ∀ (φ : Tree L V), IsArith φ → ∀ (d : ℕ) (e : V → ℕ) (F : ZF.V → ZFSet.{0}),
    (∀ a ∈ φ.vars, F (pv a) = numeral (e a)) → (S (tr φ d) F ↔ evalWff e φ) := by
  intro φ
  induction φ using Tree.induction with
  | var a => intro ht; cases ht with | var hv => cases hv
  | node l args ih =>
    intro ht d e F hF
    have sub : ∀ {a}, a ∈ args → ∀ c ∈ a.vars, F (pv c) = numeral (e c) :=
      fun ha c hc => hF c (by simpa using ⟨_, ha, hc⟩)
    rcases ht.cases with ⟨a, b, h, ha, hb⟩ | ⟨a, b, h, ha, hb⟩ | ⟨a, h, ha⟩ |
      ⟨l', a, b, h, hl, ha, hb⟩ | ⟨q, w, a, h, hq, ha⟩ <;> cases h
    · have hsub : ∀ t ∈ [a, b], ∀ m, ∀ c ∈ t.vars,
          update F (hv d) m (pv c) = numeral (e c) := fun t ht m c hc => by
        rw [update_pv_of_hv]; exact sub (by simp at ht ⊢; tauto) c hc
      simp only [tr, ZF.sem_wex, ZF.sem_wa, id,
        S_val a ha e (above_hv (Nat.lt_succ_self d)) _ (hsub a (by simp) _),
        S_val b hb e (above_hv (Nat.lt_succ_self d)) _ (hsub b (by simp) _), update_self,
        evalWff_eq]
      constructor
      · rintro ⟨m, rfl, h⟩; exact numeral_injective h
      · intro h; exact ⟨_, rfl, by rw [h]⟩
    · have hsub : ∀ t ∈ [a, b], ∀ m m', ∀ c ∈ t.vars,
          update (update F (hv d) m) (hv (d + 1)) m' (pv c) = numeral (e c) :=
        fun t ht m m' c hc => by
          rw [update_pv_of_hv, update_pv_of_hv]; exact sub (by simp at ht ⊢; tauto) c hc
      simp only [tr, ZF.sem_wex, ZF.sem_wa, ZF.sem_wel, id,
        S_val a ha e (above_hv (by omega : d < d + 2)) _ (hsub a (by simp) _ _),
        S_val b hb e (above_hv (by omega : d + 1 < d + 2)) _ (hsub b (by simp) _ _),
        update_apply, hv_inj, ↓reduceIte, (Nat.succ_ne_self d).symm, evalWff_lt,
        exists_and_left, exists_eq_left]
      exact numeral_mem_numeral
    · simp only [tr, ZF.sem_wn, evalWff_not]
      exact not_congr (ih a (by simp) ha d e F (sub (by simp)))
    · have iha := ih a (by simp) ha d e F (sub (by simp))
      have ihb := ih b (by simp) hb d e F (sub (by simp))
      rcases hl with rfl | rfl | rfl | rfl <;>
        simp only [tr, ZF.sem_wi, ZF.sem_wo, ZF.sem_wa, ZF.sem_wb, evalWff_imp, evalWff_or,
          evalWff_and, evalWff_iff, iha, ihb]
    · have key : ∀ n, S (tr a d) (update F (pv w) (numeral n)) ↔ evalWff (update e w n) a := by
        intro n
        refine ih a (by simp) ha d _ _ fun c hc => ?_
        by_cases hcw : c = w
        · subst hcw; simp
        · rw [update_of_ne (by simpa using hcw), update_of_ne hcw]
          exact sub (by simp) c hc
      have hnat : ∀ m, S (nat (pv w) d) (update F (pv w) m) ↔ m ∈ omega := fun m => by
        rw [S_nat (above_pv d w), update_self]
      rcases hq with rfl | rfl
      · simp only [tr, ZF.sem_wal, ZF.sem_wi, id, hnat, evalWff_all]
        constructor
        · intro h n; exact (key n).1 (h _ (numeral_mem_omega n))
        · intro h m hm
          obtain ⟨n, rfl⟩ := mem_omega_iff.1 hm
          exact (key n).2 (h n)
      · simp only [tr, ZF.sem_wex, ZF.sem_wa, id, hnat, evalWff_ex]
        constructor
        · rintro ⟨m, hm, h⟩
          obtain ⟨n, rfl⟩ := mem_omega_iff.1 hm
          exact ⟨n, (key n).1 h⟩
        · rintro ⟨n, h⟩; exact ⟨_, numeral_mem_omega n, (key n).2 h⟩

end Correctness

end Silmaril.Logic.Metamath.Peano.ToZF
