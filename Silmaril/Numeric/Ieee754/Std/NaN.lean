module

public import Silmaril.Numeric.Ieee754.Std.Encoding
public import Mathlib.Order.Basic

/-!
# NaN policies as a lattice, and bit-level operation specifications

IEEE 754-2019 fixes every result except which NaN encoding an operation
delivers (§6.2.3 only says a propagated NaN *should* carry an input payload).
A `NaNSpec` is a relation between the operand encodings and an admissible
result encoding. `NaNSpec` is `List Fields → Fields → Prop`, so it carries
Mathlib's complete lattice of predicates, ordered by implication: a smaller
policy is more exact.

The policies, from most exact to least, with proved inclusions:

```
x86SSE (first NaN operand, quieted;     ⊆ propagating ⊆ quietNaN ⊆ anyNaN ⊆ anything
        else the negative default NaN)
x87    (larger significand, pairwise; quieted) ⊆ propagating
riscv  (canonical NaN)                  ⊆ quietNaN,   but riscv ⊄ propagating
```

`OpSpec E P tin mode ins e out flags` is the bit-level specification of an
operation with operands `ins` and exact outcome `e`: the delivered datum and
flags are the specified ones (`Deliver`), non-NaN data are encoded canonically,
and a NaN result is any encoding admitted by `P`. It is monotone in `P`
(`OpSpec.mono`), so a statement proved for an ISA's exact policy holds for every
coarser one, and a statement may assume only the chaotic `anyNaN` (or even
`anything`, which also leaves the NaN-ness of the encoding unconstrained).

`runOp` is the executable bit-level operation for a NaN *function*; it meets
`OpSpec` for that function's singleton policy and, by uniqueness of delivery,
is the only result that does (`runOp_spec_iff`).
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-- Admissible NaN result encodings, given the operand encodings. -/
abbrev NaNSpec := List Fields → Fields → Prop

namespace NaNSpec

variable (E : Encoding)

/-- Top: any encoding at all. -/
def anything : NaNSpec := fun _ _ => True

/-- Any NaN encoding (the chaotic NaN policy). -/
def anyNaN : NaNSpec := fun _ out => E.isNaN out = true

/-- Any quiet NaN (IEEE 754-2019 §6.2: operations deliver quiet NaNs). -/
def quietNaN : NaNSpec := fun _ out => E.isNaN out = true ∧ E.isQuiet out = true

/-- A quiet NaN which, when some operand is a NaN, is one of them quieted
(IEEE 754-2019 §6.2.3 recommendation). -/
def propagating : NaNSpec := fun ins out =>
  quietNaN E ins out ∧ ((∃ i ∈ ins, E.isNaN i = true) → ∃ i ∈ ins, E.isNaN i = true ∧ out = E.quiet i)

/-- The singleton policy of a NaN function. -/
def ofFun (f : List Fields → Fields) : NaNSpec := fun ins out => out = f ins

theorem quietNaN_le_anyNaN : quietNaN E ≤ anyNaN E := fun _ _ h => h.1
theorem propagating_le_quietNaN : propagating E ≤ quietNaN E := fun _ _ h => h.1
theorem anyNaN_le_anything : anyNaN E ≤ anything := fun _ _ _ => trivial

end NaNSpec

/-! ## Per-ISA NaN functions -/

namespace NaNFun

/-- x86 SSE/AVX (Intel SDM Vol. 1 §4.8.3.5, Table 4-7): the first NaN operand,
quieted; with no NaN operand, the default "QNaN floating-point indefinite". -/
def x86SSE (E : Encoding) (dflt : Fields) (ins : List Fields) : Fields :=
  match ins.find? (fun i => E.isNaN i) with
  | some i => E.quiet i
  | none => dflt

/-- RISC-V F/D/Q/Zfh (Unprivileged ISA §"NaN Generation and Propagation"):
always the canonical NaN. -/
def riscv (canonical : Fields) (_ : List Fields) : Fields := canonical

/-- The x87 choice between two NaN operands (Intel SDM Vol. 1 Table 4-7;
SoftFloat `8086` `softfloat_propagateNaNExtF80UI`): a quiet NaN wins over a
signaling one, otherwise the larger significand, then the larger exponent field,
then the positive sign. -/
def x87Better (E : Encoding) (a b : Fields) : Fields :=
  let qa := E.isQuiet a
  let qb := E.isQuiet b
  if qa && !qb then a else if qb && !qa then b else
  if a.exp < b.exp then b else if b.exp < a.exp then a else
  if a.frac < b.frac then b else if b.frac < a.frac then a else
  if !a.sign then a else b

/-- The NaN among two operand encodings chosen by `x87Better`, if any. -/
def x87Pair (E : Encoding) (a b : Fields) : Option Fields :=
  if E.isNaN a then (if E.isNaN b then some (x87Better E a b) else some a)
  else if E.isNaN b then some b else none

/-- One more operand after a (possibly) NaN intermediate result: the intermediate
NaN has already been quieted, so it is compared quieted (SoftFloat `8086`
`softfloat_mulAddF*`: `propagateNaN(propagateNaN(a, b), c)`). The chosen
encoding is kept unquieted; `x87` quiets it at the end. -/
def x87Step (E : Encoding) (acc : Option Fields) (c : Fields) : Option Fields :=
  match acc with
  | none => if E.isNaN c then some c else none
  | some z => if E.isNaN c && decide (x87Better E (E.quiet z) c = c) then some c else some z

/-- x87: the NaN operand chosen pairwise from left to right, the first two
operands by `x87Better` and each further operand against the quieted choice so
far, quieted; with no NaN operand, the default NaN. For one or two operands this
is the x87 rule; three operands only occur in `fma`, which x87 lacks, and follow
SoftFloat's `8086` specialization. -/
def x87 (E : Encoding) (dflt : Fields) (ins : List Fields) : Fields :=
  let r := match ins with
    | a :: b :: rest => rest.foldl (x87Step E) (x87Pair E a b)
    | l => l.foldl (x87Step E) none
  match r with
  | none => dflt
  | some z => E.quiet z

end NaNFun

/-! ## Inclusions -/

namespace NaNSpec

theorem x86SSE_le_propagating (E : Encoding) (dflt : Fields)
    (hd : E.isNaN dflt = true ∧ E.isQuiet dflt = true) :
    ofFun (NaNFun.x86SSE E dflt) ≤ propagating E := by
  intro ins out h
  simp only [ofFun] at h
  subst h
  unfold NaNFun.x86SSE
  split
  next i hi =>
    have hmem := List.mem_of_find?_eq_some hi
    have hnan : E.isNaN i = true := by simpa using List.find?_some hi
    exact ⟨E.isQuiet_quiet i hnan, fun _ => ⟨i, hmem, hnan, rfl⟩⟩
  next hnone =>
    refine ⟨hd, fun ⟨i, hi, hnan⟩ => ?_⟩
    have := List.find?_eq_none.mp hnone i hi
    simp [hnan] at this

theorem riscv_le_quietNaN (E : Encoding) (canonical : Fields)
    (hc : E.isNaN canonical = true ∧ E.isQuiet canonical = true) :
    ofFun (NaNFun.riscv canonical) ≤ quietNaN E := by
  intro ins out h
  simp only [ofFun, NaNFun.riscv] at h
  subst h
  exact hc

theorem foldl_mem {α : Type*} (f : α → α → α) (hf : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ (rest : List α) (n : α), rest.foldl f n ∈ n :: rest
  | [], n => by simp
  | x :: rest, n => by
    simp only [List.foldl_cons]
    have ih := foldl_mem f hf rest (f n x)
    rcases hf n x with h | h <;> rw [h] <;> rw [h] at ih <;> simp only [List.mem_cons] at ih ⊢ <;>
      tauto

theorem x87Better_cases (E : Encoding) (a b : Fields) :
    NaNFun.x87Better E a b = a ∨ NaNFun.x87Better E a b = b := by
  unfold NaNFun.x87Better
  dsimp only
  split_ifs <;> simp

theorem x87Step_foldl_some (E : Encoding) (S : List Fields) :
    ∀ (rest : List Fields) (acc : Option Fields), (∀ c ∈ rest, c ∈ S) →
      (∀ z, acc = some z → z ∈ S ∧ E.isNaN z = true) →
      ∀ z, rest.foldl (NaNFun.x87Step E) acc = some z → z ∈ S ∧ E.isNaN z = true
  | [], _, _, hacc => by simpa using hacc
  | c :: rest, acc, hsub, hacc => by
    simp only [List.foldl_cons]
    refine x87Step_foldl_some E S rest _ (fun d hd => hsub d (by simp [hd])) ?_
    intro z hz
    have hc : c ∈ S := hsub c (by simp)
    unfold NaNFun.x87Step at hz
    split at hz
    · split_ifs at hz with h
      · cases hz; exact ⟨hc, h⟩
    · split_ifs at hz with h
      · cases hz; simp only [Bool.and_eq_true] at h; exact ⟨hc, h.1⟩
      · cases hz; exact hacc _ rfl

theorem x87Step_foldl_none (E : Encoding) :
    ∀ (rest : List Fields) (acc : Option Fields),
      rest.foldl (NaNFun.x87Step E) acc = none → acc = none ∧ ∀ c ∈ rest, E.isNaN c = false
  | [], acc, h => by simpa using h
  | c :: rest, acc, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := x87Step_foldl_none E rest _ h
    unfold NaNFun.x87Step at h1
    split at h1
    · split_ifs at h1 with hc
      refine ⟨rfl, ?_⟩
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · simpa using hc
      · exact h2 d hd
    · split_ifs at h1

theorem x87Pair_spec (E : Encoding) (a b : Fields) :
    (∀ z, NaNFun.x87Pair E a b = some z → (z = a ∨ z = b) ∧ E.isNaN z = true) ∧
      (NaNFun.x87Pair E a b = none → E.isNaN a = false ∧ E.isNaN b = false) := by
  unfold NaNFun.x87Pair
  by_cases ha : E.isNaN a = true <;> by_cases hb : E.isNaN b = true
  · simp only [ha, hb, ite_true, Option.some.injEq, forall_eq', reduceCtorEq, IsEmpty.forall_iff,
      and_true]
    rcases x87Better_cases E a b with h | h <;> rw [h] <;> simp [ha, hb]
  · simp only [Bool.not_eq_true] at hb
    simp [ha, hb]
  · simp only [Bool.not_eq_true] at ha
    simp [ha, hb]
  · simp only [Bool.not_eq_true] at ha hb
    simp [ha, hb]

theorem x87_le_propagating (E : Encoding) (dflt : Fields)
    (hd : E.isNaN dflt = true ∧ E.isQuiet dflt = true) :
    ofFun (NaNFun.x87 E dflt) ≤ propagating E := by
  intro ins out h
  simp only [ofFun] at h
  subst h
  -- The choice is `none` exactly when no operand is a NaN, else a NaN operand.
  have key : ∀ r : Option Fields, (∀ z, r = some z → z ∈ ins ∧ E.isNaN z = true) →
      (r = none → ∀ i ∈ ins, E.isNaN i = false) →
      propagating E ins (match r with | none => dflt | some z => E.quiet z) := by
    intro r hs hn
    cases r with
    | none =>
      refine ⟨hd, fun ⟨i, hi, hnan⟩ => ?_⟩
      simp [hn rfl i hi] at hnan
    | some z =>
      obtain ⟨hz, hnan⟩ := hs z rfl
      exact ⟨E.isQuiet_quiet _ hnan, fun _ => ⟨z, hz, hnan, rfl⟩⟩
  unfold NaNFun.x87
  split
  next a b rest =>
    obtain ⟨ps, pn⟩ := x87Pair_spec E a b
    apply key
    · refine x87Step_foldl_some E _ rest _ (fun c hc => by simp [hc]) ?_
      intro z hz
      obtain ⟨h1, h2⟩ := ps z hz
      rcases h1 with rfl | rfl <;> simp [h2]
    · intro hnone i hi
      obtain ⟨h1, h2⟩ := x87Step_foldl_none E rest _ hnone
      obtain ⟨ha, hb⟩ := pn h1
      simp only [List.mem_cons] at hi
      rcases hi with rfl | rfl | hi
      · exact ha
      · exact hb
      · exact h2 i hi
  next l _ =>
    apply key
    · exact x87Step_foldl_some E ins ins none (fun c hc => hc) (by simp)
    · intro hnone
      exact (x87Step_foldl_none E ins none hnone).2

/-- The canonical-NaN policy is not propagating: a signaling NaN with a nonzero
payload is not delivered quieted. -/
theorem riscv_not_le_propagating :
    ¬ ofFun (NaNFun.riscv (Interchange.binary32.encoding.defaultNaN false)) ≤
      propagating Interchange.binary32.encoding := by
  intro h
  have := h [⟨false, 255, 1⟩] _ rfl
  obtain ⟨i, hi, -, heq⟩ := this.2 ⟨⟨false, 255, 1⟩, by simp, by decide⟩
  simp only [List.mem_singleton] at hi
  subst hi
  revert heq
  decide

end NaNSpec

/-! ## Bit-level operations -/

section Op

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- Bit-level specification of an operation with operand encodings `ins` and
exact outcome `e`, for the NaN policy `P`. -/
def OpSpec (E : Encoding) (P : NaNSpec) (tin : TininessDetection) (mode : RoundingMode)
    (ins : List Fields) (e : Exact K) (out : Fields) (fl : Flags) : Prop :=
  ∃ res, Deliver E.fmt tin mode e res fl ∧ (res.isNaN = true → P ins out) ∧
    (res.isNaN = false → out = E.encode res)

theorem OpSpec.mono {E : Encoding} {P Q : NaNSpec} (hPQ : P ≤ Q) {tin : TininessDetection}
    {mode : RoundingMode} {ins : List Fields} {e : Exact K} {out : Fields} {fl : Flags}
    (h : OpSpec E P tin mode ins e out fl) : OpSpec E Q tin mode ins e out fl := by
  obtain ⟨res, hd, hn, he⟩ := h
  exact ⟨res, hd, fun h => hPQ _ _ (hn h), he⟩

end Op

/-- Executable bit-level operation for a NaN function. -/
def runOp (E : Encoding) (nan : List Fields → Fields) (tin : TininessDetection)
    (mode : RoundingMode) (ins : List Fields) (e : Exact ℚ) : Fields × Flags :=
  let p := deliverQ E.fmt tin mode e
  (if p.1.isNaN then nan ins else E.encode p.1, p.2)

theorem runOp_spec (E : Encoding) (nan : List Fields → Fields) (tin : TininessDetection)
    (mode : RoundingMode) (ins : List Fields) (e : Exact ℚ) :
    OpSpec E (NaNSpec.ofFun nan) tin mode ins e (runOp E nan tin mode ins e).1
      (runOp E nan tin mode ins e).2 := by
  refine ⟨_, deliverQ_spec E.fmt tin mode e, fun h => ?_, fun h => ?_⟩
  · simp [runOp, h, NaNSpec.ofFun]
  · simp [runOp, h]

/-- For an exact (singleton) policy the specification determines the result. -/
theorem runOp_spec_iff (E : Encoding) (nan : List Fields → Fields) (tin : TininessDetection)
    (mode : RoundingMode) (ins : List Fields) (e : Exact ℚ) (out : Fields) (fl : Flags) :
    OpSpec E (NaNSpec.ofFun nan) tin mode ins e out fl ↔ runOp E nan tin mode ins e = (out, fl) := by
  constructor
  · rintro ⟨res, hd, hn, he⟩
    obtain ⟨h1, h2⟩ := (deliverQ_spec E.fmt tin mode e).unique hd
    simp only [runOp, Prod.mk.injEq]
    refine ⟨?_, h2⟩
    rw [h1]
    cases hres : res.isNaN
    · simp [he hres]
    · simp only [ite_true]; exact (hn hres : out = nan ins).symm
  · intro h
    have := runOp_spec E nan tin mode ins e
    rw [h] at this
    exact this

/-- Executable bit-level square root for a NaN function. -/
def runSqrt (E : Encoding) (nan : List Fields → Fields) (tin : TininessDetection)
    (mode : RoundingMode) (x : Fields) : Fields × Flags :=
  let p := sqrtQ E.fmt tin mode (E.decode x)
  (if p.1.isNaN then nan [x] else E.encode p.1, p.2)

theorem runSqrt_spec (E : Encoding) (nan : List Fields → Fields) (tin : TininessDetection)
    (mode : RoundingMode) (x : Fields) :
    OpSpec E (NaNSpec.ofFun nan) tin mode [x] (exactSqrt (E.decode x))
      (runSqrt E nan tin mode x).1 (runSqrt E nan tin mode x).2 := by
  refine ⟨_, sqrtQ_spec E.fmt tin mode (E.decode x) (fun a m h => E.decode_nonneg x a m h),
    fun h => ?_, fun h => ?_⟩
  · simp [runSqrt, h, NaNSpec.ofFun]
  · simp [runSqrt, h]

end Silmaril.Numeric.Ieee754.Std
