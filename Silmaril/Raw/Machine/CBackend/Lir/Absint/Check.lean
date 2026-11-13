module

public import Silmaril.Machine.CBackend.Lir.Semantics.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-!
# Certified abstract interpretation for Lir: a post-fixpoint checker

An untrusted analyser (`scripts/absint/absint.py`) computes, for every block of
a leaf Lir function, an abstract state at the block's entry. This file checks
such a certificate and proves that an accepted one is an inductive invariant of
the concrete semantics. From the invariant it derives memory safety relative to
caller-declared buffers: every load and store a reachable state performs lies
inside one of the regions named by the certificate.

Only the checker is trusted. The analyser may use any widening, ordering or
heuristic; a wrong certificate is rejected, never turned into a theorem. This
is the "check `F(a) ⊑ a`, not the solver" design
applied to dataflow facts.

## The domain

Registers hold one of

* `top`: no information;
* `num lo hi`: an unsigned value in `[lo, hi]`;
* `off s lo hi`: a pointer into the buffer of symbol `s`, at a byte offset in
  `[lo, hi]`. A symbol is a parameter index; its value `ρ s` is the parameter's
  value on entry. The offset is computed without wrap-around, which the checker
  guarantees by bounding offsets by the region length and the precondition
  `(ρ s).toNat + len < 2^64`.

Besides values, a state carries *comparison facts* `d = cond(a, b)`: register
`d` holds the result of comparing the current values of `a` and `b`. A branch
on `d` refines the interval of `a` on each edge (an infeasible edge is not
checked). Facts are dropped when any of their registers is written.

## What is checked

`check p f cert` accepts when

* the function has no `call` (leaf functions only; the invariant is about the
  activation that started the run);
* the entry state of the entry block is implied by the parameter state;
* for every block, every load and store address is in a region under the block's
  running abstract state, and the abstract state at every jump and branch edge
  is below the entry state of its target.

`check_sound` turns acceptance into the theorem: along every run from the
function's entry, every memory access is in bounds.
-/

@[expose] public section

namespace Silmaril.Machine.Lir.Absint

/-! ## Abstract values -/

/-- Abstract values of a register. -/
inductive AVal where
  | top
  | num (lo hi : Nat)
  | off (sym lo hi : Nat)
  deriving DecidableEq, Repr

/-- The concretisation of an abstract value under symbol values `ρ`. -/
def AVal.Holds (ρ : Nat → Word) : AVal → Word → Prop
  | .top, _ => True
  | .num lo hi, x => lo ≤ x.toNat ∧ x.toNat ≤ hi
  | .off s lo hi, x => (ρ s).toNat + lo ≤ x.toNat ∧ x.toNat ≤ (ρ s).toNat + hi

/-- The order of the domain (sound, not complete: different constructors are
incomparable except under `top`). -/
def AVal.le : AVal → AVal → Bool
  | _, .top => true
  | .num l h, .num l' h' => decide (l' ≤ l) && decide (h ≤ h')
  | .off s l h, .off s' l' h' => decide (s = s') && decide (l' ≤ l) && decide (h ≤ h')
  | _, _ => false

theorem AVal.le_sound {ρ : Nat → Word} {a b : AVal} {x : Word} (hle : a.le b = true)
    (h : a.Holds ρ x) : b.Holds ρ x := by
  cases a <;> cases b <;> simp_all [AVal.le, AVal.Holds] <;> omega

/-- Region lengths by symbol. The first entry for a symbol wins. -/
def regionLen (s : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (s', n) :: rest => if s' = s then some n else regionLen s rest

theorem regionLen_mem {s n : Nat} {rs : List (Nat × Nat)} (h : regionLen s rs = some n) :
    (s, n) ∈ rs := by
  induction rs with
  | nil => simp [regionLen] at h
  | cons e rest ih =>
    obtain ⟨s', n'⟩ := e
    simp only [regionLen] at h
    split at h
    · cases h; subst_vars; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- The precondition on symbol values: every region fits below `2^64`. -/
def Pre (ρ : Nat → Word) (regions : List (Nat × Nat)) : Prop :=
  ∀ s n, (s, n) ∈ regions → (ρ s).toNat + n < 2 ^ 64

/-- Abstract addition of a byte offset to a pointer into the region of `s`:
the result stays a pointer when its offset is at most the region length. -/
def addOff (regions : List (Nat × Nat)) (s l h l' h' : Nat) : AVal :=
  match regionLen s regions with
  | some n => if h + h' ≤ n then .off s (l + l') (h + h') else .top
  | none => .top

/-- Abstract addition. -/
def addV (regions : List (Nat × Nat)) : AVal → AVal → AVal
  | .num l h, .num l' h' => if h + h' < 2 ^ 64 then .num (l + l') (h + h') else .top
  | .off s l h, .num l' h' => addOff regions s l h l' h'
  | .num l' h', .off s l h => addOff regions s l h l' h'
  | _, _ => .top

theorem addOff_sound {ρ : Nat → Word} {regions : List (Nat × Nat)} (hpre : Pre ρ regions)
    {s l h l' h' : Nat} {x y : Word}
    (ha : (ρ s).toNat + l ≤ x.toNat ∧ x.toNat ≤ (ρ s).toNat + h)
    (hb : l' ≤ y.toNat ∧ y.toNat ≤ h') : (addOff regions s l h l' h').Holds ρ (x + y) := by
  unfold addOff
  cases hn : regionLen s regions with
  | none => trivial
  | some n =>
    have := hpre s n (regionLen_mem hn)
    by_cases hc : h + h' ≤ n
    · simp only [hc, ↓reduceIte, AVal.Holds, BitVec.toNat_add]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [hc, ↓reduceIte]; trivial

theorem addV_sound {ρ : Nat → Word} {regions : List (Nat × Nat)} (hpre : Pre ρ regions)
    {a b : AVal} {x y : Word} (ha : a.Holds ρ x) (hb : b.Holds ρ y) :
    (addV regions a b).Holds ρ (x + y) := by
  have hx := x.isLt
  have hy := y.isLt
  cases a with
  | top => cases b <;> trivial
  | num l h =>
    cases b with
    | top => trivial
    | num l' h' =>
      simp only [addV]
      by_cases hc : h + h' < 2 ^ 64
      · simp only [hc, ↓reduceIte, AVal.Holds, BitVec.toNat_add] at ha hb ⊢
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [hc, ↓reduceIte]; trivial
    | off s l' h' =>
      simp only [addV]
      rw [BitVec.add_comm]
      exact addOff_sound hpre hb ha
  | off s l h =>
    cases b with
    | num l' h' => exact addOff_sound hpre ha hb
    | _ => trivial

/-- Abstract bitwise and: bounded by a `num` operand. -/
def andV : AVal → AVal → AVal
  | _, .num _ h => .num 0 h
  | .num _ h, _ => .num 0 h
  | _, _ => .top

theorem andV_sound {ρ : Nat → Word} {a b : AVal} {x y : Word} (ha : a.Holds ρ x)
    (hb : b.Holds ρ y) : (andV a b).Holds ρ (x &&& y) := by
  have h1 : (x &&& y).toNat ≤ y.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_right
  have h2 : (x &&& y).toNat ≤ x.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_left
  cases a <;> cases b <;> simp only [andV, AVal.Holds] at ha hb ⊢ <;> omega

/-- Abstract binary operators. Comparisons give `0` or `1`. -/
def binaryV (regions : List (Nat × Nat)) : Binop → AVal → AVal → AVal
  | .add, a, b => addV regions a b
  | .and, a, b => andV a b
  | .cmp _, _, _ => .num 0 1
  | .cmp32 _, _, _ => .num 0 1
  | _, _, _ => .top

theorem ofBool_holds {ρ : Nat → Word} (b : Bool) : (AVal.num 0 1).Holds ρ (ofBool b) := by
  cases b <;> simp [AVal.Holds, ofBool]

theorem binaryV_sound {ρ : Nat → Word} {regions : List (Nat × Nat)} (hpre : Pre ρ regions)
    {op : Binop} {a b : AVal} {x y z : Word} (ha : a.Holds ρ x) (hb : b.Holds ρ y)
    (hz : op.eval x y = some z) : (binaryV regions op a b).Holds ρ z := by
  cases op <;> simp only [Binop.eval, Option.some.injEq] at hz <;> subst_vars <;>
    simp only [binaryV] <;> first
      | trivial
      | exact addV_sound hpre ha hb
      | exact andV_sound ha hb
      | exact ofBool_holds _

/-- Zero-extension from `bits` bits: a `num` operand already below `2^bits`
keeps its interval; anything else is bounded by `2^bits - 1`. -/
def zextV (bits : Nat) : AVal → AVal
  | .num l h => if h < 2 ^ bits then .num l h else .num 0 (2 ^ bits - 1)
  | _ => .num 0 (2 ^ bits - 1)

theorem zextV_sound {ρ : Nat → Word} {bits : Nat} {a : AVal} {x y : Word} (ha : a.Holds ρ x)
    (hy : y.toNat = x.toNat % 2 ^ bits) : (zextV bits a).Holds ρ y := by
  have hlt : y.toNat < 2 ^ bits := hy ▸ Nat.mod_lt _ (Nat.two_pow_pos bits)
  cases a with
  | num l h =>
    simp only [zextV]
    by_cases hc : h < 2 ^ bits
    · simp only [hc, ↓reduceIte]
      simp only [AVal.Holds] at ha ⊢
      rw [hy, Nat.mod_eq_of_lt (by omega)]
      exact ha
    · simp only [hc, ↓reduceIte, AVal.Holds]; omega
  | _ => simp only [zextV, AVal.Holds]; omega

/-- Abstract unary operators: the zero-extensions and `eqz` bound their result. -/
def unaryV : Unop → AVal → AVal
  | .zext8, a => zextV 8 a
  | .zext16, a => zextV 16 a
  | .zext32, a => zextV 32 a
  | .eqz, _ => .num 0 1
  | _, _ => .top

theorem unaryV_sound {ρ : Nat → Word} (op : Unop) {a : AVal} {x : Word} (ha : a.Holds ρ x) :
    (unaryV op a).Holds ρ (op.eval x) := by
  cases op <;> simp only [unaryV, Unop.eval] <;> try trivial
  · exact zextV_sound ha (by simp only [BitVec.toNat_setWidth]; omega)
  · exact zextV_sound ha (by simp only [BitVec.toNat_setWidth]; omega)
  · exact zextV_sound ha (by simp only [of32, lo32, BitVec.toNat_setWidth]; omega)
  · exact ofBool_holds _

/-! ## Branch refinement -/

/-- An unsigned order relation between two values. -/
inductive Rel where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- The relation a branch edge establishes between the operands of its
comparison, if it is unsigned. -/
def Rel.ofCond : Cond → Bool → Option Rel
  | .eq, true => some .eq
  | .eq, false => some .ne
  | .ne, true => some .ne
  | .ne, false => some .eq
  | .ltu, true => some .lt
  | .ltu, false => some .ge
  | .leu, true => some .le
  | .leu, false => some .gt
  | .gtu, true => some .gt
  | .gtu, false => some .le
  | .geu, true => some .ge
  | .geu, false => some .lt
  | _, _ => none

def Rel.Holds : Rel → Nat → Nat → Prop
  | .eq, x, y => x = y
  | .ne, x, y => x ≠ y
  | .lt, x, y => x < y
  | .le, x, y => x ≤ y
  | .gt, x, y => x > y
  | .ge, x, y => x ≥ y

theorem Rel.ofCond_holds {c : Cond} {t : Bool} {r : Rel} (h : Rel.ofCond c t = some r)
    {x y : Word} (he : c.eval x y = t) : r.Holds x.toNat y.toNat := by
  cases c <;> cases t <;> simp only [Rel.ofCond, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    simp only [Cond.eval, Rel.Holds, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
      decide_eq_false_iff_not, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at he ⊢ <;>
    first | omega | (subst he; rfl) | exact fun h' => he (BitVec.eq_of_toNat_eq h')

/-- A nonempty interval. -/
def mkBounds (lo hi : Nat) : Option (Nat × Nat) := if lo ≤ hi then some (lo, hi) else none

/-- Narrow the bounds `[l, h]` of `x` with `rel x y` and `y ∈ [l', h']`. `none`
when no value remains. -/
def refineBounds : Rel → Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | .eq, l, h, l', h' => mkBounds (max l l') (min h h')
  | .ne, l, h, l', h' =>
    if l' = h' ∧ l' = l then mkBounds (l + 1) h
    else if l' = h' ∧ l' = h ∧ 0 < h then mkBounds l (h - 1)
    else some (l, h)
  | .lt, l, h, _, h' => if 0 < h' then mkBounds l (min h (h' - 1)) else none
  | .le, l, h, _, h' => mkBounds l (min h h')
  | .gt, l, h, l', _ => mkBounds (max l (l' + 1)) h
  | .ge, l, h, l', _ => mkBounds (max l l') h

theorem mkBounds_sound {lo hi base X : Nat} (h1 : base + lo ≤ X) (h2 : X ≤ base + hi) :
    ∃ lo' hi', mkBounds lo hi = some (lo', hi') ∧ base + lo' ≤ X ∧ X ≤ base + hi' := by
  have : lo ≤ hi := by omega
  exact ⟨lo, hi, by simp [mkBounds, this], h1, h2⟩

theorem refineBounds_sound {r : Rel} {l h l' h' base X Y : Nat}
    (hx : base + l ≤ X ∧ X ≤ base + h) (hy : base + l' ≤ Y ∧ Y ≤ base + h')
    (hr : r.Holds X Y) :
    ∃ lo hi, refineBounds r l h l' h' = some (lo, hi) ∧ base + lo ≤ X ∧ X ≤ base + hi := by
  cases r <;> simp only [Rel.Holds] at hr <;> simp only [refineBounds]
  · exact mkBounds_sound (by omega) (by omega)
  · split
    · exact mkBounds_sound (by omega) (by omega)
    · split
      · exact mkBounds_sound (by omega) (by omega)
      · exact ⟨l, h, rfl, hx⟩
  · simp only [show 0 < h' by omega, ↓reduceIte]; exact mkBounds_sound (by omega) (by omega)
  · exact mkBounds_sound (by omega) (by omega)
  · exact mkBounds_sound (by omega) (by omega)
  · exact mkBounds_sound (by omega) (by omega)

/-- Refine the abstract value of the left operand of a comparison on one edge of
a branch. `none` marks the edge infeasible. -/
def refineV (c : Cond) (t : Bool) (a b : AVal) : Option AVal :=
  match Rel.ofCond c t with
  | none => some a
  | some r =>
    match a, b with
    | .num l h, .num l' h' => (refineBounds r l h l' h').map fun p => .num p.1 p.2
    | .off s l h, .off s' l' h' =>
      if s = s' then (refineBounds r l h l' h').map fun p => .off s p.1 p.2 else some a
    | _, _ => some a

theorem refineV_sound {ρ : Nat → Word} {c : Cond} {t : Bool} {a b : AVal} {x y : Word}
    (ha : a.Holds ρ x) (hb : b.Holds ρ y) (he : c.eval x y = t) :
    ∃ a', refineV c t a b = some a' ∧ a'.Holds ρ x := by
  unfold refineV
  cases hr : Rel.ofCond c t with
  | none => exact ⟨a, rfl, ha⟩
  | some r =>
    have hrel := Rel.ofCond_holds hr he
    simp only
    cases a with
    | num l h =>
      cases b with
      | num l' h' =>
        simp only [AVal.Holds] at ha hb
        obtain ⟨lo, hi, heq, h1, h2⟩ :=
          refineBounds_sound (l := l) (h := h) (l' := l') (h' := h') (base := 0)
            (X := x.toNat) (Y := y.toNat) (by omega) (by omega) hrel
        exact ⟨.num lo hi, by simp [heq], by simp only [AVal.Holds]; omega⟩
      | _ => exact ⟨_, rfl, ha⟩
    | off s l h =>
      cases b with
      | off s' l' h' =>
        simp only
        split
        · rename_i hs
          subst hs
          simp only [AVal.Holds] at ha hb
          obtain ⟨lo, hi, heq, h1, h2⟩ := refineBounds_sound ha hb hrel
          exact ⟨.off s lo hi, by simp [heq], by simp only [AVal.Holds]; omega⟩
        · exact ⟨_, rfl, ha⟩
      | _ => exact ⟨_, rfl, ha⟩
    | top => exact ⟨_, rfl, ha⟩

/-! ## Abstract states -/

/-- A comparison fact: register `dest` holds `cond(lhs, rhs)` of the current
values of `lhs` and `rhs`. -/
structure Fact (R : Type) where
  dest : R
  cond : Cond
  lhs : R
  rhs : R
  deriving DecidableEq, Repr

/-- An abstract state: values of registers (absent means `top`; the first entry
wins) and comparison facts. -/
structure AState (R : Type) where
  vals : List (R × AVal)
  facts : List (Fact R)
  deriving DecidableEq, Repr

variable {R : Type} [DecidableEq R]

def lookup (r : R) : List (R × AVal) → AVal
  | [] => .top
  | (r', v) :: rest => if r' = r then v else lookup r rest

def AState.get (A : AState R) (r : R) : AVal := lookup r A.vals

def Fact.Holds (φ : Fact R) (fr : Frame R) : Prop :=
  ∃ x y, fr.get φ.lhs = some x ∧ fr.get φ.rhs = some y ∧
    fr.get φ.dest = some (ofBool (φ.cond.eval x y))

/-- The concretisation of an abstract state: a property of a frame. Abstract
values constrain only the registers the frame defines. -/
def AState.Holds (ρ : Nat → Word) (A : AState R) (fr : Frame R) : Prop :=
  (∀ r x, fr.get r = some x → (A.get r).Holds ρ x) ∧ ∀ φ ∈ A.facts, φ.Holds fr

/-- The order on abstract states: pointwise on the values `B` mentions, and
inclusion of facts. -/
def AState.le (A B : AState R) : Bool :=
  B.vals.all (fun e => (A.get e.1).le e.2) && B.facts.all (fun φ => A.facts.contains φ)

theorem lookup_cases (r : R) (l : List (R × AVal)) :
    lookup r l = .top ∨ (r, lookup r l) ∈ l := by
  induction l with
  | nil => simp [lookup]
  | cons e rest ih =>
    obtain ⟨r', v⟩ := e
    simp only [lookup]
    split
    · subst_vars; simp
    · rcases ih with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

theorem AState.le_sound {ρ : Nat → Word} {A B : AState R} {fr : Frame R} (hle : A.le B = true)
    (h : A.Holds ρ fr) : B.Holds ρ fr := by
  simp only [AState.le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hle
  refine ⟨fun r x hx => ?_, fun φ hφ => h.2 φ (hle.2 φ hφ)⟩
  rcases lookup_cases r B.vals with h0 | h0
  · simp only [AState.get, h0, AVal.Holds]
  · exact AVal.le_sound (hle.1 _ h0) (h.1 r x hx)

/-- Write `v` to `d`, dropping every fact that mentions `d`. -/
def AState.set (A : AState R) (d : R) (v : AVal) : AState R :=
  ⟨(d, v) :: A.vals.filter (fun e => decide (e.1 ≠ d)),
   A.facts.filter (fun φ => decide (φ.dest ≠ d ∧ φ.lhs ≠ d ∧ φ.rhs ≠ d))⟩

theorem lookup_filter {r d : R} (hrd : r ≠ d) (l : List (R × AVal)) :
    lookup r (l.filter (fun e => decide (e.1 ≠ d))) = lookup r l := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨r', v⟩ := e
    by_cases h : r' = d
    · subst h
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte, ih, lookup]
      simp [Ne.symm hrd]
    · simp only [List.filter_cons, ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte, lookup,
        ih]

theorem AState.get_set (A : AState R) (d r : R) (v : AVal) :
    (A.set d v).get r = if r = d then v else A.get r := by
  simp only [AState.get, AState.set, lookup]
  by_cases h : r = d
  · simp [h]
  · simp only [Ne.symm h, ↓reduceIte, h]; exact lookup_filter h _

theorem AState.holds_set {ρ : Nat → Word} {A : AState R} {fr : Frame R} (h : A.Holds ρ fr)
    (d : R) {v : AVal} {x : Word} (hv : v.Holds ρ x) : (A.set d v).Holds ρ (fr.set d x) := by
  refine ⟨fun r y hy => ?_, fun φ hφ => ?_⟩
  · rw [AState.get_set]
    simp only [Frame.get, Frame.regs_set] at hy
    split at hy
    · cases hy; simp_all
    · simp_all only [↓reduceIte]; exact h.1 r y hy
  · simp only [AState.set, List.mem_filter, decide_eq_true_eq] at hφ
    obtain ⟨hφ, h1, h2, h3⟩ := hφ
    obtain ⟨a, b, ha, hb, hd⟩ := h.2 φ hφ
    exact ⟨a, b, by simpa [Frame.get, h2] using ha, by simpa [Frame.get, h3] using hb,
      by simpa [Frame.get, h1] using hd⟩

/-- Overwrite the value of `r` without touching facts: used for refinement,
where the concrete value is unchanged. -/
def AState.refineReg (A : AState R) (r : R) (v : AVal) : AState R :=
  ⟨(r, v) :: A.vals, A.facts⟩

theorem AState.holds_refineReg {ρ : Nat → Word} {A : AState R} {fr : Frame R}
    (h : A.Holds ρ fr) {r : R} {v : AVal} (hv : ∀ x, fr.get r = some x → v.Holds ρ x) :
    (A.refineReg r v).Holds ρ fr := by
  refine ⟨fun r' y hy => ?_, h.2⟩
  simp only [AState.refineReg, AState.get, lookup]
  split
  · subst_vars; exact hv y hy
  · exact h.1 r' y hy

/-! ## Transfer functions -/

/-- Abstract execution of a straight-line operation. -/
def transferOp (regions : List (Nat × Nat)) (A : AState R) : Op R → AState R
  | .const d v => A.set d (.num v.toNat v.toNat)
  | .move d s => A.set d (A.get s)
  | .unary op d s => A.set d (unaryV op (A.get s))
  | .binary op d a b =>
    let A' := A.set d (binaryV regions op (A.get a) (A.get b))
    match op with
    | .cmp c => if d ≠ a ∧ d ≠ b then { A' with facts := ⟨d, c, a, b⟩ :: A'.facts } else A'
    | _ => A'
  | .load _ _ d _ _ => A.set d .top
  | .store .. => A
  | .slotGet d _ => A.set d .top
  | .slotSet .. => A

/-- Abstract execution of an instruction. Calls are rejected by `safeInstr`. -/
def transferInstr (regions : List (Nat × Nat)) (A : AState R) : Instr R → AState R
  | .op o => transferOp regions A o
  | .fop _ d _ _ => A.set d .top
  | .call .. => A

/-- An access through `base + off` of `w` bytes stays inside a region. -/
def accessOk (regions : List (Nat × Nat)) (A : AState R) (base : R) (off : Nat) (w : Width) :
    Bool :=
  match A.get base with
  | .off s _ h =>
    match regionLen s regions with
    | some n => decide (h + off + w.bytes ≤ n)
    | none => false
  | _ => false

/-- The per-instruction obligation: accesses in bounds, and no calls. -/
def safeInstr (regions : List (Nat × Nat)) (A : AState R) : Instr R → Bool
  | .op (.load w _ _ base off) => accessOk regions A base off w
  | .op (.store w base off _) => accessOk regions A base off w
  | .op _ => true
  | .fop .. => true
  | .call .. => false

def run (regions : List (Nat × Nat)) (A : AState R) (is : List (Instr R)) : AState R :=
  is.foldl (transferInstr regions) A

def instrsOk (regions : List (Nat × Nat)) : AState R → List (Instr R) → Bool
  | _, [] => true
  | A, i :: is => safeInstr regions A i && instrsOk regions (transferInstr regions A i) is

/-- Refine a state on one edge of a branch on `c`, using the first fact about
`c`. `none` marks the edge infeasible. -/
def refineBranch (A : AState R) (c : R) (t : Bool) : Option (AState R) :=
  match A.facts.find? (fun φ => decide (φ.dest = c)) with
  | none => some A
  | some φ => (refineV φ.cond t (A.get φ.lhs) (A.get φ.rhs)).map (A.refineReg φ.lhs)

/-- The obligation of one control-flow edge. -/
def edgeOk (entry : List (AState R)) : Option (AState R) → Label → Bool
  | none, _ => true
  | some A, l =>
    match entry[l]? with
    | some B => A.le B
    | none => false

def termOk (entry : List (AState R)) (A : AState R) : Term R → Bool
  | .jump l => edgeOk entry (some A) l
  | .branch c l₁ l₂ => edgeOk entry (refineBranch A c true) l₁ &&
      edgeOk entry (refineBranch A c false) l₂
  | .ret _ => true
  | .trap => true

/-- The abstract state of the parameters: parameter `i`, when it is a
register, points at offset `0` of symbol `i`. -/
def initVals : Nat → List (Loc R) → List (R × AVal)
  | _, [] => []
  | i, .reg r :: ls => (r, .off i 0 0) :: initVals (i + 1) ls
  | i, .slot _ :: ls => initVals (i + 1) ls

def initState (params : List (Loc R)) : AState R := ⟨initVals 0 params, []⟩

/-- A certificate: the regions (symbol, length in bytes) and an abstract state at
the entry of every block. -/
structure Cert (R : Type) where
  regions : List (Nat × Nat)
  entry : List (AState R)
  deriving Repr

def blockOk (regions : List (Nat × Nat)) (entry : List (AState R)) (A : AState R)
    (b : Block R) : Bool :=
  instrsOk regions A b.instrs && termOk entry (run regions A b.instrs) b.term

/-- The checker. -/
def check (p : Prog R) (f : FuncId) (c : Cert R) : Bool :=
  match p.func? f with
  | none => false
  | some fn =>
    decide (c.entry.length = fn.blocks.length) &&
    (match c.entry[fn.entry]? with
     | some E => (initState fn.params).le E
     | none => false) &&
    (List.range fn.blocks.length).all fun l =>
      match fn.blocks[l]?, c.entry[l]? with
      | some b, some A => blockOk c.regions c.entry A b
      | _, _ => false

/-! ## Soundness -/

/-- The address and width of the memory access a state is about to perform. -/
def access? (p : Prog R) (s : State R) : Option (Nat × Width) :=
  match p.fetch s.point with
  | some (.instr (.op (.load w _ _ base off))) => (s.frame.get base).map fun a => (a.toNat + off, w)
  | some (.instr (.op (.store w base off _))) => (s.frame.get base).map fun a => (a.toNat + off, w)
  | _ => none

/-- Symbol values of a run: parameter `i`'s value in the initial frame. -/
def symbols (params : List (Loc R)) (fr : Frame R) (i : Nat) : Word :=
  match params[i]? with
  | some (.reg r) => (fr.get r).getD 0
  | _ => 0

theorem lookup_initVals (params : List (Loc R)) (i : Nat) (r : R) :
    lookup r (initVals i params) = .top ∨
      ∃ j, params[j]? = some (.reg r) ∧ lookup r (initVals i params) = .off (i + j) 0 0 := by
  induction params generalizing i with
  | nil => simp [initVals, lookup]
  | cons l ls ih =>
    cases l with
    | reg r' =>
      simp only [initVals, lookup]
      split
      · subst_vars; exact .inr ⟨0, by simp, by simp⟩
      · rcases ih (i + 1) with h | ⟨j, hj, h⟩
        · exact .inl h
        · exact .inr ⟨j + 1, by simpa using hj, by rw [h]; congr 1; omega⟩
    | slot n =>
      simp only [initVals]
      rcases ih (i + 1) with h | ⟨j, hj, h⟩
      · exact .inl h
      · exact .inr ⟨j + 1, by simpa using hj, by rw [h]; congr 1; omega⟩

theorem initState_holds (params : List (Loc R)) (fr : Frame R) :
    (initState params).Holds (symbols params fr) fr := by
  refine ⟨fun r x hx => ?_, by simp [initState]⟩
  simp only [initState, AState.get]
  rcases lookup_initVals params 0 r with h | ⟨j, hj, h⟩
  · rw [h]; trivial
  · rw [h]; simp only [AVal.Holds, Nat.zero_add, symbols, hj, hx, Option.getD_some]; omega

section
variable {regions : List (Nat × Nat)} {ρ : Nat → Word}

theorem accessOk_sound (_hpre : Pre ρ regions) {A : AState R} {fr : Frame R} (h : A.Holds ρ fr)
    {base : R} {off : Nat} {w : Width} (hok : accessOk regions A base off w = true)
    {a : Word} (ha : fr.get base = some a) :
    ∃ s n, (s, n) ∈ regions ∧ (ρ s).toNat ≤ a.toNat + off ∧
      a.toNat + off + w.bytes ≤ (ρ s).toNat + n := by
  have hv := h.1 base a ha
  unfold accessOk at hok
  split at hok
  · rename_i s l hi hget
    split at hok
    · rename_i n hn
      rw [hget] at hv
      simp only [AVal.Holds, decide_eq_true_eq] at hv hok
      exact ⟨s, n, regionLen_mem hn, by omega, by omega⟩
    · simp at hok
  · simp at hok

theorem transferOp_sound (hpre : Pre ρ regions) {A : AState R} {fr fr' : Frame R}
    {m m' : Memory} {o : Op R} (h : A.Holds ρ fr) (he : o.exec fr m = some (fr', m')) :
    (transferOp regions A o).Holds ρ fr' := by
  cases o with
  | const d v =>
    simp only [Op.exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact AState.holds_set h d (by simp [AVal.Holds])
  | move d s =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨x, hx, rfl, rfl⟩ := he
    exact AState.holds_set h d (h.1 s x hx)
  | unary op d s =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨x, hx, rfl, rfl⟩ := he
    exact AState.holds_set h d (unaryV_sound op (h.1 s x hx))
  | binary op d a b =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨x, hx, y, hy, z, hz, rfl, rfl⟩ := he
    have hset := AState.holds_set h d (binaryV_sound hpre (h.1 a x hx) (h.1 b y hy) hz)
    simp only [transferOp]
    split
    · rename_i c
      split
      · rename_i hne
        refine ⟨hset.1, fun φ hφ => ?_⟩
        simp only [List.mem_cons] at hφ
        rcases hφ with rfl | hφ
        · simp only [Binop.eval, Option.some.injEq] at hz
          subst hz
          refine ⟨x, y, ?_, ?_, ?_⟩ <;> simp [Frame.get, Ne.symm hne.1, Ne.symm hne.2] <;>
            simp_all [Frame.get]
        · exact hset.2 φ hφ
      · exact hset
    · exact hset
  | load w e d base off =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, z, hz, rfl, rfl⟩ := he
    exact AState.holds_set h d (v := .top) trivial
  | store w base off src =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨a, ha, x, hx, m'', hm, he⟩ := he
    cases he; exact h
  | slotGet d n =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨x, hx, rfl, rfl⟩ := he
    exact AState.holds_set h d (v := .top) trivial
  | slotSet n s =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨x, hx, rfl, rfl⟩ := he
    exact ⟨fun r y hy => h.1 r y (by simpa [Frame.get, Frame.setSlot] using hy), fun φ hφ => by
      obtain ⟨a, b, ha, hb, hd⟩ := h.2 φ hφ
      exact ⟨a, b, by simpa [Frame.get, Frame.setSlot] using ha,
        by simpa [Frame.get, Frame.setSlot] using hb, by simpa [Frame.get, Frame.setSlot] using hd⟩⟩

theorem refineBranch_sound {A : AState R} {fr : Frame R} (h : A.Holds ρ fr) {c : R}
    {x : Word} (hc : fr.get c = some x) (t : Bool) (ht : (x ≠ 0) = (t = true)) :
    ∃ A', refineBranch A c t = some A' ∧ A'.Holds ρ fr := by
  unfold refineBranch
  split
  · exact ⟨A, rfl, h⟩
  · rename_i φ hφ
    have hmem := List.mem_of_find?_eq_some hφ
    have hdest : φ.dest = c := by simpa using List.find?_some hφ
    obtain ⟨a, b, ha, hb, hd⟩ := h.2 φ hmem
    rw [hdest, hc, Option.some.injEq] at hd
    have heval : φ.cond.eval a b = t := by
      subst hd
      cases hev : φ.cond.eval a b <;> cases t <;> simp_all [ofBool]
    obtain ⟨a', ha', hh⟩ := refineV_sound (h.1 _ a ha) (h.1 _ b hb) heval
    refine ⟨_, by rw [ha']; rfl, AState.holds_refineReg h fun z hz => ?_⟩
    rw [ha] at hz; cases hz; exact hh

end

theorem run_take_succ (regions : List (Nat × Nat)) (A : AState R) (is : List (Instr R)) (n : Nat)
    {i : Instr R} (hi : is[n]? = some i) :
    run regions A (is.take (n + 1)) = transferInstr regions (run regions A (is.take n)) i := by
  simp only [run]
  rw [List.take_add_one, hi, List.foldl_append]
  rfl

theorem instrsOk_get {regions : List (Nat × Nat)} {A : AState R} {is : List (Instr R)}
    (hok : instrsOk regions A is = true) {n : Nat} {i : Instr R} (hi : is[n]? = some i) :
    safeInstr regions (run regions A (is.take n)) i = true := by
  induction is generalizing A n with
  | nil => simp at hi
  | cons j js ih =>
    simp only [instrsOk, Bool.and_eq_true] at hok
    cases n with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
              simpa [run] using hok.1
    | succ n =>
      simp only [List.getElem?_cons_succ] at hi
      have := ih hok.2 hi
      simpa [run] using this

/-- The invariant of an accepted certificate. -/
def Inv (p : Prog R) (f : FuncId) (c : Cert R) (ρ : Nat → Word) (s : State R) : Prop :=
  s.stack = [] ∧ s.point.func = f ∧
    ∃ b A, p.block? f s.point.label = some b ∧ c.entry[s.point.label]? = some A ∧
      s.point.index ≤ b.instrs.length ∧
      (run c.regions A (b.instrs.take s.point.index)).Holds ρ s.frame

theorem check_blocks {p : Prog R} {f : FuncId} {c : Cert R} {fn : Func R}
    (hf : p.func? f = some fn) (hc : check p f c = true) :
    c.entry.length = fn.blocks.length ∧
      ∀ (l : Nat) b A, fn.blocks[l]? = some b → c.entry[l]? = some A →
        blockOk c.regions c.entry A b = true := by
  simp only [check, hf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  refine ⟨hc.1.1, fun l b A hb hA => ?_⟩
  have hl : l < fn.blocks.length := by
    exact (List.getElem?_eq_some_iff.mp hb).1
  have := hc.2 l hl
  simpa [hb, hA] using this

theorem edgeOk_sound {p : Prog R} {f : FuncId} {c : Cert R} {fn : Func R} {ρ : Nat → Word}
    (hf : p.func? f = some fn) (hlen : c.entry.length = fn.blocks.length)
    {A : AState R} {l : Label} (hok : edgeOk c.entry (some A) l = true) {s : State R}
    (hs : s.stack = []) (hpt : s.point = ⟨f, l, 0⟩) (h : A.Holds ρ s.frame) : Inv p f c ρ s := by
  simp only [edgeOk] at hok
  split at hok
  · rename_i B hB
    have hl : l < fn.blocks.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hB).1
    refine ⟨hs, by simp [hpt], fn.blocks[l], B, ?_, by simp [hpt, hB], by simp [hpt], ?_⟩
    · simp [hpt, Prog.block?, hf, hl]
    · simpa [hpt, run] using AState.le_sound hok h
  · simp at hok

theorem inv_step {p : Prog R} {f : FuncId} {c : Cert R} {ρ : Nat → Word} (hpre : Pre ρ c.regions)
    (hc : check p f c = true) {s s' : State R} (hinv : Inv p f c ρ s)
    (hstep : step p s = .running s') : Inv p f c ρ s' := by
  obtain ⟨hstack, hfunc, b, A, hb, hA, hidx, hholds⟩ := hinv
  obtain ⟨fn, hf⟩ : ∃ fn, p.func? f = some fn := by
    cases h : p.func? f with
    | none => simp [check, h] at hc
    | some fn => exact ⟨fn, rfl⟩
  obtain ⟨hlen, hblocks⟩ := check_blocks hf hc
  have hb' : fn.blocks[s.point.label]? = some b := by simpa [Prog.block?, hf] using hb
  have hbok := hblocks _ _ _ hb' hA
  simp only [blockOk, Bool.and_eq_true] at hbok
  have hpt : p.block? s.point.func s.point.label = some b := by rw [hfunc]; exact hb
  by_cases hlt : s.point.index < b.instrs.length
  · -- an instruction
    have hi : b.instrs[s.point.index]? = some b.instrs[s.point.index] := by simp [hlt]
    have hfetch : p.fetch s.point = some (.instr b.instrs[s.point.index]) := by
      simp [Prog.fetch, hpt, hi]
    have hsafe := instrsOk_get hbok.1 hi
    have hrun := run_take_succ c.regions A b.instrs s.point.index hi
    generalize hins : b.instrs[s.point.index] = ins at hfetch hsafe hrun
    simp only [step, hfetch] at hstep
    cases ins with
    | op o =>
      simp only at hstep
      split at hstep
      · rename_i fr m he
        cases hstep
        refine ⟨hstack, by simp [hfunc], b, A, hb, hA, by simp; omega, ?_⟩
        simp only [Point.next_index]
        rw [hrun]
        exact transferOp_sound hpre hholds he
      · cases hstep
    | call g args results => simp [safeInstr] at hsafe
    | fop op d a b' =>
      simp only at hstep
      split at hstep
      · rename_i fr he
        cases hstep
        refine ⟨hstack, by simp [hfunc], b, A, hb, hA, by simp; omega, ?_⟩
        simp only [Point.next_index]
        rw [hrun]
        simp only [FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
        obtain ⟨x, hx, y, hy, rfl⟩ := he
        exact AState.holds_set hholds d (v := .top) trivial
      · cases hstep
  · -- the terminator
    have heq : s.point.index = b.instrs.length := by omega
    have hfetch : p.fetch s.point = some (.term b.term) := by
      simp [Prog.fetch, hpt, heq]
    have htake : b.instrs.take s.point.index = b.instrs := by rw [heq]; simp
    rw [htake] at hholds
    have hterm := hbok.2
    generalize hT : b.term = T at hfetch hterm
    simp only [step, hfetch] at hstep
    cases T with
    | jump l =>
      simp only at hstep
      cases hstep
      exact edgeOk_sound hf hlen hterm hstack (by simp [hfunc]) hholds
    | branch cr l₁ l₂ =>
      simp only [termOk, Bool.and_eq_true] at hterm
      simp only at hstep
      split at hstep
      · cases hstep
      · rename_i x hx
        cases hstep
        by_cases hx0 : x = 0
        · have hif : (if x = 0 then l₂ else l₁) = l₂ := by simp only [hx0, ↓reduceIte]
          obtain ⟨A', hA', hh⟩ := refineBranch_sound hholds hx false
            (by simp only [hx0, ne_eq, not_true_eq_false, Bool.false_eq_true])
          rw [hA'] at hterm
          exact edgeOk_sound hf hlen hterm.2 hstack (by simp only [hif, hfunc]) hh
        · have hif : (if x = 0 then l₂ else l₁) = l₁ := by simp only [hx0, ↓reduceIte]
          obtain ⟨A', hA', hh⟩ := refineBranch_sound hholds hx true
            (by simp only [hx0, ne_eq, not_false_eq_true])
          rw [hA'] at hterm
          exact edgeOk_sound hf hlen hterm.1 hstack (by simp only [hif, hfunc]) hh
    | ret locs =>
      simp only [hstack] at hstep
      split at hstep <;> cases hstep
    | trap => simp only at hstep; cases hstep

/-- **Soundness.** If `check` accepts a certificate for function `f`, then
along every run that starts at `f`'s entry with an empty stack, whose parameters
satisfy the region precondition, every load and store accesses bytes inside a
declared region of a parameter buffer. -/
theorem check_sound {p : Prog R} {f : FuncId} {c : Cert R} (hc : check p f c = true)
    {fn : Func R} (hf : p.func? f = some fn) {s₀ : State R}
    (h₀ : s₀.point = ⟨f, fn.entry, 0⟩) (hs₀ : s₀.stack = [])
    (hpre : Pre (symbols fn.params s₀.frame) c.regions) {s : State R} (hreach : Steps p s₀ s)
    {addr : Nat} {w : Width} (hacc : access? p s = some (addr, w)) :
    ∃ sym n, (sym, n) ∈ c.regions ∧ (symbols fn.params s₀.frame sym).toNat ≤ addr ∧
      addr + w.bytes ≤ (symbols fn.params s₀.frame sym).toNat + n := by
  set ρ := symbols fn.params s₀.frame
  have hinv : Inv p f c ρ s := by
    clear hacc
    induction hreach with
    | refl =>
      simp only [check, hf, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hE := hc.1.2
      split at hE
      · rename_i E hE'
        exact edgeOk_sound hf hc.1.1 (A := initState fn.params) (by simp [edgeOk, hE', hE])
          hs₀ h₀ (initState_holds fn.params s₀.frame)
      · simp at hE
    | tail _ hst ih => exact inv_step hpre hc ih hst
  obtain ⟨hstack, hfunc, b, A, hb, hA, hidx, hholds⟩ := hinv
  obtain ⟨hlen, hblocks⟩ := check_blocks hf hc
  have hb' : fn.blocks[s.point.label]? = some b := by simpa [Prog.block?, hf] using hb
  have hbok := hblocks _ _ _ hb' hA
  simp only [blockOk, Bool.and_eq_true] at hbok
  have hpt : p.block? s.point.func s.point.label = some b := by rw [hfunc]; exact hb
  simp only [access?] at hacc
  split at hacc <;> try simp only [Option.map_eq_some_iff, Prod.mk.injEq, reduceCtorEq] at hacc
  all_goals
    rename_i hfetch
    simp only [Prog.fetch, hpt, Option.bind_some] at hfetch
    split at hfetch
    · rename_i i hi
      simp only [Option.some.injEq, Code.instr.injEq] at hfetch
      subst hfetch
      have hsafe := instrsOk_get hbok.1 hi
      obtain ⟨a, ha, rfl, rfl⟩ := hacc
      exact accessOk_sound hpre hholds hsafe ha
    · split at hfetch <;> cases hfetch

end Silmaril.Machine.Lir.Absint
