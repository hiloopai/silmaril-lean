module

public import Silmaril.Compiler.Core.Verified.Cfg.Defs
/-! # Bounds on the output of a control-flow graph with print nodes

Lir's output buffer and Core's allocation room are finite, so a CFG with print nodes compiles
only with a bound on the output it can write. Each label gets a potential (`Pot`): `a` bytes per
unit of a counter slot `x` below a bound `b`, plus `e` (a constant `e` without a counter).
`Code.cost` is the output a tree writes before its next jump plus the potential of the label it
jumps to, following the slots' values.

`check` proves, without running anything, that a tree costs at most a given potential of the
slots at its root (`check_sound`). It walks every path of the tree symbolically: each slot's value
relative to the root's (`SVal`: a root slot shifted by a constant, a constant, or unknown), an
upper bound on the counter's root value from the tests passed (`refine`), and the room of the
prints passed. At a jump the target's potential must be paid for (`endOk`): a constant one by the
root's constant part, one over the same counter by a shift that does not lower the counter's
distance to its bound, or, past a test that keeps the counter below its bound, by one unit of it.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Cfg

open Silmaril.Cerberus Silmaril.Cerberus.Core
open StateExpr (Key Term)

/-- A test takes its `no` arm: Cerberus's statement test when its value is `1`, a `do` test when
it is `0`. -/
def takesNo (direct : Bool) (v : Int) : Bool := if direct then v == 0 else v == 1

/-- The output a tree writes before it jumps to a label, plus that label's bound `Φ`, following
the slots' values: a print pays its room. -/
noncomputable def Code.cost (Φ : Key → (Key → Int) → Nat) : Code → (Key → Int) → Nat
  | .atom (.set q t) c, σ => c.cost Φ (Function.update σ q (t.val σ))
  | .atom (.clear q) c, σ => c.cost Φ (Function.update σ q 0)
  | .print pre suf _ c, σ => CfgPrintStmt.room pre suf + c.cost Φ σ
  | .test direct t y n, σ => if takesNo direct (t.val σ) then n.cost Φ σ else y.cost Φ σ
  | .goto l, σ => Φ l σ
  | .ret _, _ => 0
  | .abort, _ => 0

/-! ## Potentials -/

/-- `a` bytes per unit of the counter `x` below `b`, plus `e`. -/
structure Pot where
  x : Option Key
  a : Nat
  b : Int
  e : Nat

/-- The potential at the slots `σ`. -/
def Pot.eval (π : Pot) (σ : Key → Int) : Nat :=
  match π.x with
  | none => π.e
  | some x => π.a * (π.b - σ x).toNat + π.e

/-- The least value of a potential at a root whose counter is at most `hi`. -/
def Pot.lower (π : Pot) (hi : Option Int) : Nat :=
  match π.x, hi with
  | some _, some h => π.a * (π.b - h).toNat + π.e
  | _, _ => π.e

/-- The root's counter is at most `hi`. -/
def HiOk (π : Pot) (hi : Option Int) (σ₀ : Key → Int) : Prop :=
  ∀ x h, π.x = some x → hi = some h → σ₀ x ≤ h

theorem Pot.lower_le (π : Pot) {hi : Option Int} {σ₀ : Key → Int} (h : HiOk π hi σ₀) :
    π.lower hi ≤ π.eval σ₀ := by
  unfold Pot.lower Pot.eval
  rcases hx : π.x with _ | x
  · simp
  · rcases hh : hi with _ | u
    · simp
    · have := h x u hx hh
      simp only
      have : (π.b - u).toNat ≤ (π.b - σ₀ x).toNat := by omega
      have := Nat.mul_le_mul_left π.a this
      omega

/-! ## Symbolic values -/

/-- A slot's value on a path: the root value of slot `q` shifted by `δ`, a constant, or
unknown. -/
inductive SVal where
  | rel (q : Key) (δ : Int)
  | const (c : Int)
  | top

def SVal.shift : SVal → Int → SVal
  | .rel q δ, k => .rel q (δ + k)
  | .const c, k => .const (c + k)
  | .top, _ => .top

/-- `x + k` and `x - k` of a literal `k`. -/
def binS (op : IntOp) (s : SVal) : Term → SVal
  | .lit k => match op with
    | .add => s.shift k
    | .sub => s.shift (-k)
    | _ => .top
  | _ => .top

/-- The symbolic value of a term. -/
def sval (st : Key → SVal) : Term → SVal
  | .lit c => .const c
  | .var q => st q
  | .bin op a b => binS op (sval st a) b
  | _ => .top

/-- The value `v` is what the symbolic value says, from the root's slots `σ₀`. -/
def SVal.Holds (σ₀ : Key → Int) (v : Int) : SVal → Prop
  | .rel q δ => v = σ₀ q + δ
  | .const c => v = c
  | .top => True

/-- Every slot holds its symbolic value. -/
def Agrees (st : Key → SVal) (σ₀ σ : Key → Int) : Prop := ∀ q, (st q).Holds σ₀ (σ q)

theorem SVal.shift_holds {σ₀ : Key → Int} {v : Int} {s : SVal} (h : s.Holds σ₀ v) (k : Int) :
    (s.shift k).Holds σ₀ (v + k) := by
  cases s <;> simp_all [SVal.shift, SVal.Holds]; omega

theorem sval_holds {st : Key → SVal} {σ₀ σ : Key → Int} (h : Agrees st σ₀ σ) :
    (t : Term) → (sval st t).Holds σ₀ (t.val σ)
  | .lit _ => rfl
  | .var q => h q
  | .bin op a b => by
    have ha := sval_holds h a
    show SVal.Holds σ₀ (Guard.apply op (a.val σ) (b.val σ)) (binS op (sval st a) b)
    cases b with
    | lit k =>
      cases op
      · exact SVal.shift_holds ha k
      · have := SVal.shift_holds ha (-k)
        rwa [← Int.sub_eq_add_neg] at this
      all_goals trivial
    | _ => trivial
  | .cmp .. => by simp [sval, SVal.Holds]
  | .cond .. => by simp [sval, SVal.Holds]
  | .un .. => by simp [sval, SVal.Holds]
  | .bit .. => by simp [sval, SVal.Holds]
  | .divpos .. => by simp [sval, SVal.Holds]

theorem Agrees.set {st : Key → SVal} {σ₀ σ : Key → Int} (h : Agrees st σ₀ σ) (q : Key) (t : Term) :
    Agrees (Function.update st q (sval st t)) σ₀ (Function.update σ q (t.val σ)) := by
  intro q'
  by_cases e : q' = q
  · subst e; simpa using sval_holds h t
  · simpa [Function.update, e] using h q'

theorem Agrees.clear {st : Key → SVal} {σ₀ σ : Key → Int} (h : Agrees st σ₀ σ) (q : Key) :
    Agrees (Function.update st q (.const 0)) σ₀ (Function.update σ q 0) := by
  intro q'
  by_cases e : q' = q
  · subst e; simp [SVal.Holds]
  · simpa [Function.update, e] using h q'

/-! ## Tests -/

/-- An upper bound on `v` when `holds r v k` is `b`. -/
def ub (r : BinOp) (b : Bool) (k : Int) : Option Int :=
  match r, b with
  | .lt, true => some (k - 1)
  | .le, true => some k
  | .gt, false => some k
  | .ge, false => some (k - 1)
  | _, _ => none

theorem ub_sound {r : BinOp} {b : Bool} {k u v : Int} (hu : ub r b k = some u)
    (hv : Guard.holds r v k = b) : v ≤ u := by
  cases r <;> cases b <;> simp_all [ub, Guard.holds] <;> omega

/-- A comparison of `a` with a literal `k` as a test: `cmp r 1 0 a k`, or its negation
`(cmp r 1 0 a k) == 0` (Cerberus's statement test of a condition). -/
def testFact : Term → Option (BinOp × Term × Int × Bool)
  | .cmp r c₁ c₂ a (.lit k) =>
    if c₁ = 1 ∧ c₂ = 0 then
      match r, a with
      | .eq, .cmp r' d₁ d₂ a' (.lit k') =>
        if d₁ = 1 ∧ d₂ = 0 ∧ k = 0 then some (r', a', k', true) else some (r, a, k, false)
      | _, _ => some (r, a, k, false)
    else none
  | _ => none

theorem testFact_val {t : Term} {r : BinOp} {a : Term} {k : Int} {neg : Bool}
    (h : testFact t = some (r, a, k, neg)) (σ : Key → Int) :
    t.val σ = if (Guard.holds r (a.val σ) k != neg) = true then 1 else 0 := by
  unfold testFact at h
  split at h
  · rename_i r₀ c₁ c₂ a₀ k₀
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      split at h
      · rename_i r' d₁ d₂ a' k'
        split at h
        · rename_i hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          simp only [Term.val, Guard.compare]
          split_ifs <;> simp_all [Guard.holds]
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          simp only [Term.val, Guard.compare]
          split_ifs <;> simp_all
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        simp only [Term.val, Guard.compare]
        split_ifs <;> simp_all
    · cases h
  · cases h

/-- The counter's bound after a test on the arm `no`. -/
def refine (π : Pot) (st : Key → SVal) (hi : Option Int) (direct no : Bool) (t : Term) :
    Option Int :=
  match testFact t with
  | some (r, a, k, neg) =>
    match π.x, sval st a, ub r ((no != direct) != neg) k with
    | some x, .rel q δ, some u =>
      if q = x then some (match hi with | some h => min h (u - δ) | none => u - δ) else hi
    | _, _, _ => hi
  | none => hi

theorem refine_sound {π : Pot} {st : Key → SVal} {σ₀ σ : Key → Int} {hi : Option Int}
    (ag : Agrees st σ₀ σ) (hh : HiOk π hi σ₀) {direct no : Bool} {t : Term}
    (taken : takesNo direct (t.val σ) = no) : HiOk π (refine π st hi direct no t) σ₀ := by
  unfold refine
  split
  · rename_i r a k neg hf
    split
    · rename_i x q δ u hx hs hu
      split
      · rename_i hq
        subst hq
        have hv : Guard.holds r (a.val σ) k = ((no != direct) != neg) := by
          rw [testFact_val hf] at taken
          cases hr : Guard.holds r (a.val σ) k <;> cases neg <;>
            cases direct <;> cases no <;> simp_all [takesNo]
        have hle := ub_sound hu hv
        have hrel : a.val σ = σ₀ q + δ := by
          have := sval_holds ag a; rw [hs] at this; exact this
        intro x' h' hx' hh'
        rw [hx] at hx'
        cases hx'
        rcases hhi : hi with _ | h0
        · simp [hhi] at hh'; omega
        · simp [hhi] at hh'
          have := hh q h0 hx hhi
          omega
      · exact hh
    · exact hh
  · exact hh

/-! ## The check -/

/-- A jump to `l` with the prints `P` passed is paid for by the root's potential `π`. -/
def endOk (Φ : Key → Pot) (π : Pot) (st : Key → SVal) (hi : Option Int) (P : Nat) (l : Key) :
    Bool :=
  let π' := Φ l
  let lo := π.lower hi
  match π'.x with
  | none => decide (P + π'.e ≤ lo)
  | some x' => match st x' with
    | .const c => decide (P + (π'.a * (π'.b - c).toNat + π'.e) ≤ lo)
    | .rel q δ =>
      (π'.a == 0 && decide (P + π'.e ≤ lo)) ||
        (π.x == some q && decide (π'.a ≤ π.a) &&
          ((decide (0 ≤ π.b - π'.b + δ) && decide (P + π'.e ≤ π.e)) ||
            (decide (1 ≤ π.b - π'.b + δ) &&
              (match hi with | some h => decide (h ≤ π.b - 1) | none => false) &&
              decide (P + π'.e ≤ π.a + π.e))))
    | .top => π'.a == 0 && decide (P + π'.e ≤ lo)

/-- Every path of the tree, with the prints `P` passed, is paid for by the root's potential. -/
def check (Φ : Key → Pot) (π : Pot) : (Key → SVal) → Option Int → Nat → Code → Bool
  | st, hi, P, .atom (.set q t) c => check Φ π (Function.update st q (sval st t)) hi P c
  | st, hi, P, .atom (.clear q) c => check Φ π (Function.update st q (.const 0)) hi P c
  | st, hi, P, .print pre suf _ c => check Φ π st hi (P + CfgPrintStmt.room pre suf) c
  | st, hi, P, .test direct t y n =>
    check Φ π st (refine π st hi direct true t) P n && check Φ π st (refine π st hi direct false t) P y
  | st, hi, P, .goto l => endOk Φ π st hi P l
  | _, hi, P, .ret _ => decide (P ≤ π.lower hi)
  | _, hi, P, .abort => decide (P ≤ π.lower hi)

/-- The semantic bound of the potentials. -/
def Pot.bound (Φ : Key → Pot) : Key → (Key → Int) → Nat := fun l σ => (Φ l).eval σ

theorem endOk_sound {Φ : Key → Pot} {π : Pot} {st : Key → SVal} {hi : Option Int} {P : Nat}
    {l : Key} (h : endOk Φ π st hi P l = true) {σ₀ σ : Key → Int} (ag : Agrees st σ₀ σ)
    (hh : HiOk π hi σ₀) : P + (Φ l).eval σ ≤ π.eval σ₀ := by
  have low := π.lower_le hh
  unfold endOk at h
  simp only at h
  unfold Pot.eval at low ⊢
  rcases hx' : (Φ l).x with _ | x'
  · simp only [hx', decide_eq_true_eq] at h
    simp only
    omega
  · simp only [hx'] at h ⊢
    have hv := ag x'
    rcases hs : st x' with ⟨q, δ⟩ | c | _
    · rw [hs] at h hv
      simp only [SVal.Holds] at hv
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      rcases h with ⟨ha, hp⟩ | ⟨⟨hq, ha⟩, h⟩
      · rw [ha, Nat.zero_mul]; omega
      · rw [hq]
        simp only
        have hmul : ∀ n : Nat, (Φ l).a * n ≤ π.a * n := fun n => Nat.mul_le_mul_right n ha
        rcases h with ⟨hs0, hp⟩ | ⟨⟨hs1, hhi⟩, hp⟩
        · have h1 : ((Φ l).b - σ x').toNat ≤ (π.b - σ₀ q).toNat := by omega
          have := Nat.mul_le_mul_left π.a h1
          have := hmul ((Φ l).b - σ x').toNat
          omega
        · rcases hhi' : hi with _ | u
          · simp [hhi'] at hhi
          · simp only [hhi', decide_eq_true_eq] at hhi
            have hu := hh q u hq hhi'
            have h1 : ((Φ l).b - σ x').toNat + 1 ≤ (π.b - σ₀ q).toNat := by omega
            have h2 := Nat.mul_le_mul_left π.a h1
            have h3 := hmul ((Φ l).b - σ x').toNat
            rw [Nat.mul_add, Nat.mul_one] at h2
            omega
    · rw [hs] at h hv
      simp only [SVal.Holds] at hv
      simp only [decide_eq_true_eq] at h
      rw [hv]
      omega
    · rw [hs] at h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      rw [h.1, Nat.zero_mul]
      omega

theorem check_sound (Φ : Key → Pot) (π : Pot) :
    (c : Code) → ∀ (st : Key → SVal) (hi : Option Int) (P : Nat) (σ₀ σ : Key → Int),
    check Φ π st hi P c = true → Agrees st σ₀ σ → HiOk π hi σ₀ →
    P + c.cost (Pot.bound Φ) σ ≤ π.eval σ₀
  | .atom (.set q t) c, st, hi, P, σ₀, σ, h, ag, hh => by
    simpa [Code.cost] using check_sound Φ π c _ hi P σ₀ _ h (ag.set q t) hh
  | .atom (.clear q) c, st, hi, P, σ₀, σ, h, ag, hh => by
    simpa [Code.cost] using check_sound Φ π c _ hi P σ₀ _ h (ag.clear q) hh
  | .print pre suf _ c, st, hi, P, σ₀, σ, h, ag, hh => by
    have := check_sound Φ π c st hi _ σ₀ σ h ag hh
    simp only [Code.cost]
    omega
  | .test direct t y n, st, hi, P, σ₀, σ, h, ag, hh => by
    simp only [check, Bool.and_eq_true] at h
    simp only [Code.cost]
    cases hn : takesNo direct (t.val σ)
    · simpa using check_sound Φ π y st _ P σ₀ σ h.2 ag (refine_sound ag hh hn)
    · simpa using check_sound Φ π n st _ P σ₀ σ h.1 ag (refine_sound ag hh hn)
  | .goto l, st, hi, P, σ₀, σ, h, ag, hh => by
    simpa [Code.cost, Pot.bound] using endOk_sound h ag hh
  | .ret _, st, hi, P, σ₀, σ, h, ag, hh => by
    simp only [check, decide_eq_true_eq] at h
    simp only [Code.cost]
    have := π.lower_le hh
    omega
  | .abort, st, hi, P, σ₀, σ, h, ag, hh => by
    simp only [check, decide_eq_true_eq] at h
    simp only [Code.cost]
    have := π.lower_le hh
    omega

/-- The root store of a label: every slot is its own root value. -/
def rootStore : Key → SVal := fun q => .rel q 0

theorem agrees_root (σ : Key → Int) : Agrees rootStore σ σ := fun q => by
  simp [rootStore, SVal.Holds]

/-- **A label's tree** costs at most its potential when `check` accepts it from the root. -/
theorem label_bound {Φ : Key → Pot} {l : Key} {c : Code}
    (h : check Φ (Φ l) rootStore none 0 c = true) (σ : Key → Int) :
    c.cost (Pot.bound Φ) σ ≤ Pot.bound Φ l σ := by
  have := check_sound Φ (Φ l) c rootStore none 0 σ σ h (agrees_root σ)
    (fun _ _ _ hh => by cases hh)
  simpa [Pot.bound] using this

/-- **The entry tree**, from slots all `0`, costs at most `n` when `check` accepts it. -/
theorem entry_bound {Φ : Key → Pot} {c : Code} {n : Nat}
    (h : check Φ ⟨none, 0, 0, n⟩ (fun _ => .const 0) none 0 c = true) :
    c.cost (Pot.bound Φ) (fun _ => 0) ≤ n := by
  have := check_sound Φ ⟨none, 0, 0, n⟩ c (fun _ => .const 0) none 0 (fun _ => 0) (fun _ => 0) h
    (fun q => by simp [SVal.Holds]) (fun _ _ hx _ => by cases hx)
  simpa [Pot.eval] using this

end Silmaril.Compile.Core.Verified.Cfg
