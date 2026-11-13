module

public import Silmaril.Wasm.Logic.V1.Examples.Defs

/-!
# Folding and unfolding the array predicates

Separation-logic proofs about arrays spend most of their steps unfolding a
predicate to expose one cell, framing the rest off, doing the load or store, and
folding back — the paper's Figure 12 does exactly this twice. The lemmas here
are that bookkeeping, done once.

Everything is an equality of `HAssert`, which is `Sto → AHeap → Prop`, so
`funext` twice and `propext` reduce each to an iff between two existential
splittings of the same heap.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1.Examples

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Logic.V1

/-! ## `HAssert` as a separation algebra -/

theorem HAssert.ext {H H' : HAssert} (h : ∀ ρ a, H ρ a ↔ H' ρ a) : H = H' :=
  funext fun ρ => funext fun a => propext (h ρ a)

theorem HAssert.star_comm (H H' : HAssert) : HAssert.star H H' = HAssert.star H' H := by
  refine HAssert.ext fun ρ a => ⟨?_, ?_⟩ <;>
    rintro ⟨h₁, h₂, d, rfl, hH, hH'⟩ <;>
    exact ⟨h₂, h₁, d.symm, AHeap.union_comm d, hH', hH⟩

theorem HAssert.star_assoc (H₁ H₂ H₃ : HAssert) :
    HAssert.star (HAssert.star H₁ H₂) H₃ = HAssert.star H₁ (HAssert.star H₂ H₃) := by
  refine HAssert.ext fun ρ a => ⟨?_, ?_⟩
  · rintro ⟨-, h₃, d, rfl, ⟨h₁, h₂, d₁₂, rfl, hH₁, hH₂⟩, hH₃⟩
    exact ⟨h₁, h₂ ∪ h₃,
      (AHeap.disj_union d₁₂.symm (AHeap.disj_union_left d).symm).symm,
      AHeap.union_assoc h₁ h₂ h₃, hH₁,
      h₂, h₃, AHeap.disj_union_right d, rfl, hH₂, hH₃⟩
  · rintro ⟨h₁, -, d, rfl, hH₁, ⟨h₂, h₃, d₂₃, rfl, hH₂, hH₃⟩⟩
    refine ⟨h₁ ∪ h₂, h₃, ?_, (AHeap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, ?_, rfl, hH₁, hH₂⟩, hH₃⟩
    · exact AHeap.disj_union (AHeap.disj_union_right (AHeap.Disj.symm d)).symm d₂₃
    · exact (AHeap.disj_union_left (AHeap.Disj.symm d)).symm

instance : Std.Associative HAssert.star := ⟨HAssert.star_assoc⟩

instance : Std.Commutative HAssert.star := ⟨HAssert.star_comm⟩

theorem HAssert.star_left_comm (H₁ H₂ H₃ : HAssert) :
    HAssert.star H₁ (HAssert.star H₂ H₃) = HAssert.star H₂ (HAssert.star H₁ H₃) := by
  rw [← HAssert.star_assoc, HAssert.star_comm H₁ H₂, HAssert.star_assoc]

/-- A vacuous pure conjunct can always be dropped. -/
@[simp] theorem HAssert.and_pure_true (H : HAssert) :
    HAssert.and H (HAssert.pure fun _ => True) = H :=
  HAssert.ext fun _ _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-! ## Iterated separating conjunction -/

/-- The body of `HAssert.iterRange`, as a fold over an explicit list. -/
private theorem foldr_star_append (l₁ l₂ : List Nat) (f : Nat → HAssert) :
    (l₁ ++ l₂).foldr (fun i acc => HAssert.star (f i) acc) HAssert.emp =
      HAssert.star (l₁.foldr (fun i acc => HAssert.star (f i) acc) HAssert.emp)
        (l₂.foldr (fun i acc => HAssert.star (f i) acc) HAssert.emp) := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, List.foldr_cons, ih, HAssert.star_assoc]

private theorem foldr_star_congr (l : List Nat) (f g : Nat → HAssert)
    (h : ∀ i ∈ l, f i = g i) :
    l.foldr (fun i acc => HAssert.star (f i) acc) HAssert.emp =
      l.foldr (fun i acc => HAssert.star (g i) acc) HAssert.emp := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, h a (by simp), ih fun i hi => h i (by simp [hi])]

private theorem foldr_star_shift (f : Nat → HAssert) (k n : Nat) : ∀ s : Nat,
    (List.range' (s + k) n).foldr (fun i acc => HAssert.star (f i) acc) HAssert.emp =
      (List.range' s n).foldr (fun i acc => HAssert.star (f (i + k)) acc) HAssert.emp := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [List.range'_succ, List.range'_succ, List.foldr_cons, List.foldr_cons,
      show s + k + 1 = s + 1 + k by omega, ih (s + 1)]

theorem HAssert.iterRange_self (lo : Nat) (f : Nat → HAssert) :
    HAssert.iterRange lo lo f = HAssert.emp := by
  simp [HAssert.iterRange]

theorem HAssert.iterRange_shift (lo hi k : Nat) (f : Nat → HAssert) :
    HAssert.iterRange (lo + k) (hi + k) f = HAssert.iterRange lo hi (fun i => f (i + k)) := by
  simp only [HAssert.iterRange, show hi + k - (lo + k) = hi - lo by omega]
  exact foldr_star_shift f k (hi - lo) lo

theorem HAssert.iterRange_succ_right (lo hi : Nat) (f : Nat → HAssert) (le : lo ≤ hi) :
    HAssert.iterRange lo (hi + 1) f = HAssert.star (HAssert.iterRange lo hi f) (f hi) := by
  simp only [HAssert.iterRange, show hi + 1 - lo = (hi - lo) + 1 by omega, List.range'_concat,
    foldr_star_append, show lo + 1 * (hi - lo) = hi by omega, List.foldr_cons, List.foldr_nil,
    HAssert.star_emp]

theorem HAssert.iterRange_one (lo : Nat) (f : Nat → HAssert) :
    HAssert.iterRange lo (lo + 1) f = f lo := by
  rw [HAssert.iterRange_succ_right lo lo f Nat.le.refl, HAssert.iterRange_self,
    HAssert.emp_star]

theorem HAssert.iterRange_succ_left (lo hi : Nat) (f : Nat → HAssert) (lt : lo < hi) :
    HAssert.iterRange lo hi f = HAssert.star (f lo) (HAssert.iterRange (lo + 1) hi f) := by
  simp only [HAssert.iterRange, show hi - lo = (hi - (lo + 1)) + 1 by omega, List.range'_succ,
    List.foldr_cons]

theorem HAssert.iterRange_split (lo mid hi : Nat) (f : Nat → HAssert)
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    HAssert.iterRange lo hi f =
      HAssert.star (HAssert.iterRange lo mid f) (HAssert.iterRange mid hi f) := by
  simp only [HAssert.iterRange, show hi - lo = (mid - lo) + (hi - mid) by omega,
    ← List.range'_append, show lo + 1 * (mid - lo) = mid by omega, foldr_star_append]

theorem HAssert.iterRange_congr (lo hi : Nat) (f g : Nat → HAssert)
    (h : ∀ i, lo ≤ i → i < hi → f i = g i) :
    HAssert.iterRange lo hi f = HAssert.iterRange lo hi g := by
  refine foldr_star_congr _ f g fun i hi' => ?_
  rw [List.mem_range'_1] at hi'
  exact h i hi'.1 (by omega)

/-! ## Array segments -/

private theorem getElem!_append_left {β : Type _} [Inhabited β] {l₁ l₂ : List β} {i : Nat}
    (h : i < l₁.length) : (l₁ ++ l₂)[i]! = l₁[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getElem!_append_right {β : Type _} [Inhabited β] {l₁ l₂ : List β} {i : Nat} :
    (l₁ ++ l₂)[l₁.length + i]! = l₂[i]! := by
  simp only [List.getElem!_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

private theorem getElem!_append_right' {β : Type _} [Inhabited β] {l₁ l₂ : List β} {k : Nat}
    (h : l₁.length ≤ k) : (l₁ ++ l₂)[k]! = l₂[k - l₁.length]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right h]

private theorem getElem!_take {β : Type _} [Inhabited β] {l : List β} {i j : Nat} (h : j < i) :
    (l.take i)[j]! = l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

private theorem getElem!_drop {β : Type _} [Inhabited β] {l : List β} {i j : Nat} :
    (l.drop i)[j]! = l[i + j]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

/-- `Aseg` at a constant list, as an `iterRange`: the form every proof below starts from. -/
theorem Aseg_const (x : Term Nat) (α : List (BitVec 32)) :
    Aseg x (fun _ => α) =
      HAssert.iterRange 0 α.length
        (fun i => cell32 (fun ρ' => x ρ' + 4 * i) (fun _ => α[i]!)) := rfl

@[simp] theorem Aseg_nil (x : Term Nat) : Aseg x (fun _ => []) = HAssert.emp := by
  rw [Aseg_const]
  exact HAssert.iterRange_self 0 _

theorem Aseg_single (x : Term Nat) (a : BitVec 32) :
    Aseg x (fun _ => [a]) = cell32 x (fun _ => a) := by
  rw [Aseg_const]
  exact HAssert.iterRange_one 0 _

/-- `Aseg` is a function of the values its arguments take, so a pointwise
equality of terms is enough. -/
theorem Aseg_congr {x y : Term Nat} {α β : Term (List (BitVec 32))}
    (hx : ∀ ρ, x ρ = y ρ) (hα : ∀ ρ, α ρ = β ρ) : Aseg x α = Aseg y β := by
  rw [funext hx, funext hα]

theorem Aseg_append (x : Term Nat) (α β : List (BitVec 32)) :
    Aseg x (fun _ => α ++ β) =
      HAssert.star (Aseg x fun _ => α) (Aseg (fun ρ => x ρ + 4 * α.length) fun _ => β) := by
  rw [Aseg_const, Aseg_const, Aseg_const, List.length_append,
    HAssert.iterRange_split 0 α.length (α.length + β.length) _ (Nat.zero_le _)
      (Nat.le_add_right _ _)]
  have hs := HAssert.iterRange_shift 0 β.length α.length
    (fun i => cell32 (fun ρ' => x ρ' + 4 * i) (fun _ : Sto => (α ++ β)[i]!))
  rw [Nat.zero_add] at hs
  rw [show α.length + β.length = β.length + α.length from Nat.add_comm _ _, hs]
  congr 1
  · exact HAssert.iterRange_congr _ _ _ _ fun i _ h => by rw [getElem!_append_left h]
  · refine HAssert.iterRange_congr _ _ _ _ fun i _ _ => ?_
    rw [show (fun ρ' => x ρ' + 4 * (i + α.length)) =
        (fun ρ' : Sto => x ρ' + 4 * α.length + 4 * i) from funext fun ρ' => by omega,
      Nat.add_comm i α.length, getElem!_append_right]

theorem Aseg_cons (x : Term Nat) (a : BitVec 32) (α : List (BitVec 32)) :
    Aseg x (fun _ => a :: α) =
      HAssert.star (cell32 x fun _ => a) (Aseg (fun ρ => x ρ + 4) fun _ => α) := by
  have h : Aseg x (fun _ => a :: α) = Aseg x (fun _ => [a] ++ α) := rfl
  rw [h, Aseg_append, Aseg_single]
  rfl

/-- Expose the `i`-th cell of an array segment, as Figure 12 does. -/
theorem Aseg_at (x : Term Nat) (α : List (BitVec 32)) (i : Nat) (lt : i < α.length) :
    Aseg x (fun _ => α) =
      HAssert.star (Aseg x fun _ => α.take i)
        (HAssert.star (cell32 (fun ρ => x ρ + 4 * i) fun _ => α[i]!)
          (Aseg (fun ρ => x ρ + 4 * (i + 1)) fun _ => α.drop (i + 1))) := by
  have hd : α.drop i = α[i]! :: α.drop (i + 1) := by
    rw [getElem!_pos α i lt]
    exact (List.getElem_cons_drop lt).symm
  have hsplit : α = α.take i ++ (α[i]! :: α.drop (i + 1)) := by
    rw [← hd, List.take_append_drop]
  have hlen : (α.take i).length = i := by
    rw [List.length_take]; omega
  conv_lhs => rw [hsplit]
  rw [Aseg_append, hlen, Aseg_cons,
    show (fun ρ => x ρ + 4 * i + 4) = (fun ρ : Sto => x ρ + 4 * (i + 1)) from
      funext fun ρ => by omega]

/-- Writing one cell of an array segment. -/
theorem Aseg_set (x : Term Nat) (α : List (BitVec 32)) (i : Nat) (v : BitVec 32)
    (lt : i < α.length) :
    HAssert.star (Aseg x fun _ => α.take i)
        (HAssert.star (cell32 (fun ρ => x ρ + 4 * i) fun _ => v)
          (Aseg (fun ρ => x ρ + 4 * (i + 1)) fun _ => α.drop (i + 1))) =
      Aseg x (fun _ => α.set i v) := by
  have e₁ : (α.set i v).take i = α.take i := by
    rw [List.take_set]
    exact List.set_eq_of_length_le (by rw [List.length_take]; omega)
  have e₂ : (α.set i v).drop (i + 1) = α.drop (i + 1) := by
    rw [List.drop_set]
    simp
  have e₃ : (α.set i v)[i]! = v := by
    simp [lt]
  have h := Aseg_at x (α.set i v) i (by rw [List.length_set]; exact lt)
  rw [e₁, e₂, e₃] at h
  exact h.symm

/-! ## Bounded arrays -/

/-- `BA` unfolded: the length cell, the contents, and the spare capacity. -/
theorem BA_unfold (x : Term Nat) (n : Nat) (α : List (BitVec 32)) :
    BA x (fun _ => n) (fun _ => α) =
      HAssert.and
        (HAssert.star (cell32 x fun _ => BitVec.ofNat 32 α.length)
          (HAssert.star (Aseg (fun ρ => x ρ + 4) fun _ => α) (Aspare x (fun _ => n) fun _ => α)))
        (HAssert.pure fun ρ => α.length ≤ n ∧ x ρ + 4 * (n + 1) ≤ INT32_MAX) :=
  rfl

/-- `Aspare` at a constant capacity and list, as an `iterRange`. -/
theorem Aspare_const (x : Term Nat) (n : Nat) (α : List (BitVec 32)) :
    Aspare x (fun _ => n) (fun _ => α) =
      HAssert.iterRange (α.length + 1) (n + 1)
        (fun i => cell32Any (fun ρ' => x ρ' + 4 * i)) := rfl

/-- `Aspare` only sees the *length* of the array it leaves room for. -/
theorem Aspare_congr_length (x : Term Nat) (n : Nat) (α β : List (BitVec 32))
    (h : α.length = β.length) :
    Aspare x (fun _ => n) (fun _ => α) = Aspare x (fun _ => n) (fun _ => β) := by
  rw [Aspare_const, Aspare_const, h]

/-- The spare capacity of a bounded array with one more element. -/
theorem Aspare_succ (x : Term Nat) (n : Nat) (α : List (BitVec 32)) (lt : α.length < n) :
    Aspare x (fun _ => n) (fun _ => α) =
      HAssert.star (cell32Any fun ρ => x ρ + 4 * (α.length + 1))
        (Aspare x (fun _ => n) fun _ => α ++ [0]) := by
  rw [Aspare_const, Aspare_const, List.length_append, List.length_singleton,
    HAssert.iterRange_succ_left (α.length + 1) (n + 1) _ (by omega)]

/-- Appending to a bounded array consumes one slot of spare capacity.

Note that the length cell on the left already holds the *new* length: this lemma
folds the state the program is in *after* both the store of `v` and the update
of the length cell. -/
theorem BA_push (x : Term Nat) (n : Nat) (α : List (BitVec 32)) (v : BitVec 32)
    (lt : α.length < n) :
    HAssert.and
        (HAssert.star (cell32 x fun _ => BitVec.ofNat 32 (α.length + 1))
          (HAssert.star (Aseg (fun ρ => x ρ + 4) fun _ => α)
            (HAssert.star (cell32 (fun ρ => x ρ + 4 * (α.length + 1)) fun _ => v)
              (Aspare x (fun _ => n) fun _ => α ++ [0]))))
        (HAssert.pure fun ρ => α.length ≤ n ∧ x ρ + 4 * (n + 1) ≤ INT32_MAX) =
      HAssert.and (BA x (fun _ => n) fun _ => α ++ [v])
        (HAssert.pure fun _ => True) := by
  rw [HAssert.and_pure_true, BA_unfold, List.length_append, List.length_singleton,
    Aseg_append, Aseg_single,
    Aspare_congr_length x n (α ++ [0]) (α ++ [v]) (by simp),
    show (fun ρ => x ρ + 4 + 4 * α.length) = (fun ρ : Sto => x ρ + 4 * (α.length + 1)) from
      funext fun ρ => by omega,
    show (HAssert.pure fun ρ => α.length ≤ n ∧ x ρ + 4 * (n + 1) ≤ INT32_MAX) =
        (HAssert.pure fun ρ => α.length + 1 ≤ n ∧ x ρ + 4 * (n + 1) ≤ INT32_MAX) from
      HAssert.ext fun ρ _ => by
        constructor <;> (rintro ⟨-, h₂⟩; exact ⟨by omega, h₂⟩)]
  congr 1
  ac_rfl

/-- Expose the `i`-th element of a bounded array, with the length cell and the
rest framed off — the shape `OBAGet` and `BASet` both need. -/
theorem BA_at (x : Term Nat) (n : Nat) (α : List (BitVec 32)) (i : Nat) (lt : i < α.length) :
    BA x (fun _ => n) (fun _ => α) =
      HAssert.and
        (HAssert.star (cell32 (fun ρ => x ρ + 4 + 4 * i) fun _ => α[i]!)
          (HAssert.star (cell32 x fun _ => BitVec.ofNat 32 α.length)
            (HAssert.star (Aseg (fun ρ => x ρ + 4) fun _ => α.take i)
              (HAssert.star (Aseg (fun ρ => x ρ + 4 + 4 * (i + 1)) fun _ => α.drop (i + 1))
                (Aspare x (fun _ => n) fun _ => α)))))
        (HAssert.pure fun ρ => α.length ≤ n ∧ x ρ + 4 * (n + 1) ≤ INT32_MAX) := by
  rw [BA_unfold, Aseg_at (fun ρ => x ρ + 4) α i lt]
  congr 1
  ac_rfl

/-- Writing one element of a bounded array: the `BA` form of `Aseg_set`. -/
theorem BA_set (x : Term Nat) (n : Nat) (α : List (BitVec 32)) (i : Nat) (v : BitVec 32)
    (lt : i < α.length) :
    HAssert.and
        (HAssert.star (cell32 (fun ρ => x ρ + 4 + 4 * i) fun _ => v)
          (HAssert.star (cell32 x fun _ => BitVec.ofNat 32 α.length)
            (HAssert.star (Aseg (fun ρ => x ρ + 4) fun _ => α.take i)
              (HAssert.star (Aseg (fun ρ => x ρ + 4 + 4 * (i + 1)) fun _ => α.drop (i + 1))
                (Aspare x (fun _ => n) fun _ => α)))))
        (HAssert.pure fun ρ => α.length ≤ n ∧ x ρ + 4 * (n + 1) ≤ INT32_MAX) =
      BA x (fun _ => n) (fun _ => α.set i v) := by
  have hlen : (α.set i v).length = α.length := List.length_set ..
  have e₁ : (α.set i v).take i = α.take i := by
    rw [List.take_set]
    exact List.set_eq_of_length_le (by rw [List.length_take]; omega)
  have e₂ : (α.set i v).drop (i + 1) = α.drop (i + 1) := by
    rw [List.drop_set]
    simp
  have e₃ : (α.set i v)[i]! = v := by simp [lt]
  have h := BA_at x n (α.set i v) i (by rw [hlen]; exact lt)
  rw [hlen, e₁, e₂, e₃, Aspare_congr_length x n (α.set i v) α hlen] at h
  exact h.symm

/-! ## Ordered bounded arrays -/

theorem OBA_unfold (x : Term Nat) (n : Nat) (α : List (BitVec 32)) :
    OBA x (fun _ => n) (fun _ => α) =
      HAssert.and (BA x (fun _ => n) fun _ => α) (HAssert.pure fun _ => Ordered α) :=
  rfl

theorem OBAnd_unfold (x : Term Nat) (n : Nat) (α : List (BitVec 32)) :
    OBAnd x (fun _ => n) (fun _ => α) =
      HAssert.and (OBA x (fun _ => n) fun _ => α) (HAssert.pure fun _ => α.Nodup) :=
  rfl

/-- Once orderedness is known, `OBA` collapses to `BA`. -/
theorem OBA_fold (x : Term Nat) (n : Nat) (α : List (BitVec 32)) (ord : Ordered α) :
    OBA x (fun _ => n) (fun _ => α) = BA x (fun _ => n) (fun _ => α) :=
  HAssert.ext fun _ _ => ⟨fun h => h.1, fun h => ⟨h, ord⟩⟩

/-- Once orderedness and absence of duplicates are known, `OBAnd` collapses to
`BA`: this is how `OBAInsert` and `OBADelete` discharge their postconditions. -/
theorem OBAnd_fold (x : Term Nat) (n : Nat) (α : List (BitVec 32)) (ord : Ordered α)
    (nd : α.Nodup) : OBAnd x (fun _ => n) (fun _ => α) = BA x (fun _ => n) (fun _ => α) :=
  HAssert.ext fun _ _ => ⟨fun h => h.1.1, fun h => ⟨⟨h, ord⟩, nd⟩⟩

private theorem nodup_iff_getElem! {β : Type _} [Inhabited β] {l : List β} :
    l.Nodup ↔ ∀ p q, p < q → q < l.length → l[p]! ≠ l[q]! := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  constructor
  · intro h p q hpq hq hv
    refine h p q hpq hq ?_
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hq,
      ← getElem!_pos l p (by omega), ← getElem!_pos l q hq, hv]
  · intro h p q hpq hq hv
    refine h p q hpq hq ?_
    rw [getElem!_pos l p (by omega), getElem!_pos l q hq]
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hq] at hv
    exact Option.some.inj hv

/-! ### Indexing an insertion and a deletion -/

private theorem take_length_eq (α : List (BitVec 32)) (i : Nat) (hi : i ≤ α.length) :
    (α.take i).length = i := by
  rw [List.length_take]; omega

private theorem insert_length (α : List (BitVec 32)) (i : Nat) (v : BitVec 32)
    (hi : i ≤ α.length) : (α.take i ++ [v] ++ α.drop i).length = α.length + 1 := by
  rw [List.length_append, List.length_append, List.length_take, List.length_drop,
    List.length_singleton]
  omega

private theorem erase_length (α : List (BitVec 32)) (i : Nat) (hi : i ≤ α.length) :
    (α.take i ++ α.drop (i + 1)).length = i + (α.length - (i + 1)) := by
  rw [List.length_append, List.length_take, List.length_drop]
  omega

private theorem getElem!_insert_lt (α : List (BitVec 32)) (i : Nat) (v : BitVec 32) (k : Nat)
    (hi : i ≤ α.length) (hk : k < i) : (α.take i ++ [v] ++ α.drop i)[k]! = α[k]! := by
  have hlen := take_length_eq α i hi
  have h₁ : k < (α.take i ++ [v]).length := by
    rw [List.length_append, hlen, List.length_singleton]; omega
  have h₂ : k < (α.take i).length := by rw [hlen]; exact hk
  rw [getElem!_append_left h₁, getElem!_append_left h₂, getElem!_take hk]

private theorem getElem!_insert_eq (α : List (BitVec 32)) (i : Nat) (v : BitVec 32)
    (hi : i ≤ α.length) : (α.take i ++ [v] ++ α.drop i)[i]! = v := by
  have hlen := take_length_eq α i hi
  have h₁ : i < (α.take i ++ [v]).length := by
    rw [List.length_append, hlen, List.length_singleton]; omega
  have h₂ : (α.take i).length ≤ i := by rw [hlen]
  rw [getElem!_append_left h₁, getElem!_append_right' h₂, hlen, Nat.sub_self]
  rfl

private theorem getElem!_insert_gt (α : List (BitVec 32)) (i : Nat) (v : BitVec 32) (k : Nat)
    (hi : i ≤ α.length) (hk : i < k) : (α.take i ++ [v] ++ α.drop i)[k]! = α[k - 1]! := by
  have hlen := take_length_eq α i hi
  have h₁ : (α.take i ++ [v]).length ≤ k := by
    rw [List.length_append, hlen, List.length_singleton]; omega
  rw [getElem!_append_right' h₁, List.length_append, hlen, List.length_singleton,
    getElem!_drop, show i + (k - (i + 1)) = k - 1 from by omega]

private theorem getElem!_erase_lt (α : List (BitVec 32)) (i k : Nat)
    (hi : i ≤ α.length) (hk : k < i) : (α.take i ++ α.drop (i + 1))[k]! = α[k]! := by
  have hlen := take_length_eq α i hi
  rw [getElem!_append_left (by rw [hlen]; exact hk), getElem!_take hk]

private theorem getElem!_erase_ge (α : List (BitVec 32)) (i k : Nat)
    (hi : i ≤ α.length) (hk : i ≤ k) : (α.take i ++ α.drop (i + 1))[k]! = α[k + 1]! := by
  have hlen := take_length_eq α i hi
  rw [getElem!_append_right' (by rw [hlen]; exact hk), hlen, getElem!_drop,
    show i + 1 + (k - i) = k + 1 from by omega]

/-- Past the end of `α`, `take`/`drop` saturate, so an insertion at `i > |α|` is
the insertion at `|α|`. -/
private theorem insert_clamp (α : List (BitVec 32)) (i : Nat) (v : BitVec 32)
    (hi : α.length ≤ i) :
    α.take i ++ [v] ++ α.drop i = α.take α.length ++ [v] ++ α.drop α.length := by
  rw [List.take_of_length_le hi, List.drop_eq_nil_of_le hi,
    List.take_of_length_le (Nat.le_refl _), List.drop_eq_nil_of_le (Nat.le_refl _)]

/-! ### Ordering -/

private theorem Ordered_insert_le (α : List (BitVec 32)) (i : Nat) (v : BitVec 32)
    (hi : i ≤ α.length) (ord : Ordered α)
    (lower : ∀ j, j < i → ((α[j]!).toNat < v.toNat))
    (upper : ∀ j, i ≤ j → j < α.length → v.toNat ≤ (α[j]!).toNat) :
    Ordered (α.take i ++ [v] ++ α.drop i) := by
  intro p q hq hpq
  rw [insert_length α i v hi] at hq
  rcases Nat.lt_trichotomy p i with hp | hp | hp
  · rw [getElem!_insert_lt α i v p hi hp]
    rcases Nat.lt_trichotomy q i with hq' | hq' | hq'
    · rw [getElem!_insert_lt α i v q hi hq']
      exact ord p q (by omega) hpq
    · rw [hq', getElem!_insert_eq α i v hi]
      exact Nat.le_of_lt (lower p hp)
    · rw [getElem!_insert_gt α i v q hi hq']
      rcases Nat.lt_or_ge p (q - 1) with h | h
      · exact ord p (q - 1) (by omega) h
      · rw [show q - 1 = p from by omega]
  · rw [hp, getElem!_insert_eq α i v hi, getElem!_insert_gt α i v q hi (by omega)]
    exact upper (q - 1) (by omega) (by omega)
  · rw [getElem!_insert_gt α i v p hi hp, getElem!_insert_gt α i v q hi (by omega)]
    exact ord (p - 1) (q - 1) (by omega) (by omega)

/-- Ordered insertion keeps the array ordered. -/
theorem Ordered_insert (α : List (BitVec 32)) (i : Nat) (v : BitVec 32)
    (ord : Ordered α) (lower : ∀ j, j < i → ((α[j]!).toNat < v.toNat))
    (upper : ∀ j, i ≤ j → j < α.length → v.toNat ≤ (α[j]!).toNat) :
    Ordered (α.take i ++ [v] ++ α.drop i) := by
  rcases Nat.lt_or_ge α.length i with hi | hi
  · rw [insert_clamp α i v (by omega)]
    exact Ordered_insert_le α α.length v (Nat.le_refl _) ord
      (fun j hj => lower j (by omega)) (fun _ hj hj' => absurd hj' (by omega))
  · exact Ordered_insert_le α i v hi ord lower upper

/-- Deleting an element keeps the array ordered. -/
theorem Ordered_erase (α : List (BitVec 32)) (i : Nat) (ord : Ordered α) :
    Ordered (α.take i ++ α.drop (i + 1)) := by
  rcases Nat.lt_or_ge α.length i with hi | hi
  · rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]
    exact ord
  · intro p q hq hpq
    rw [erase_length α i hi] at hq
    rcases Nat.lt_or_ge p i with hp | hp
    · rw [getElem!_erase_lt α i p hi hp]
      rcases Nat.lt_or_ge q i with hq' | hq'
      · rw [getElem!_erase_lt α i q hi hq']
        exact ord p q (by omega) hpq
      · rw [getElem!_erase_ge α i q hi hq']
        exact ord p (q + 1) (by omega) (by omega)
    · rw [getElem!_erase_ge α i p hi hp, getElem!_erase_ge α i q hi (by omega)]
      exact ord (p + 1) (q + 1) (by omega) (by omega)

/-! ### Absence of duplicates -/

/-- Deleting an element keeps the array duplicate-free. -/
theorem Nodup_erase (α : List (BitVec 32)) (i : Nat) (nd : α.Nodup) :
    (α.take i ++ α.drop (i + 1)).Nodup := by
  rw [← List.eraseIdx_eq_take_drop_succ]
  exact nd.eraseIdx i

private theorem Nodup_insert_le (α : List (BitVec 32)) (i : Nat) (v : BitVec 32)
    (hi : i ≤ α.length) (nd : α.Nodup)
    (lower : ∀ j, j < i → ((α[j]!).toNat < v.toNat))
    (upper : ∀ j, i ≤ j → j < α.length → v.toNat < (α[j]!).toNat) :
    (α.take i ++ [v] ++ α.drop i).Nodup := by
  have nd' : ∀ p q, p < q → q < α.length → α[p]! ≠ α[q]! := nodup_iff_getElem!.mp nd
  rw [nodup_iff_getElem!]
  intro p q hpq hq₀
  have hq : q < α.length + 1 := by rwa [insert_length α i v hi] at hq₀
  rcases Nat.lt_trichotomy p i with hp | hp | hp
  · show (α.take i ++ [v] ++ α.drop i)[p]! ≠ (α.take i ++ [v] ++ α.drop i)[q]!
    rw [getElem!_insert_lt α i v p hi hp]
    rcases Nat.lt_trichotomy q i with hq' | hq' | hq'
    · rw [getElem!_insert_lt α i v q hi hq']
      exact nd' p q hpq (by omega)
    · rw [hq', getElem!_insert_eq α i v hi]
      exact fun h => Nat.ne_of_lt (lower p hp) (congrArg BitVec.toNat h)
    · rw [getElem!_insert_gt α i v q hi hq']
      rcases Nat.lt_or_ge p (q - 1) with h | h
      · exact nd' p (q - 1) h (by omega)
      · rw [show q - 1 = p from by omega]
        exact fun h' => Nat.ne_of_lt (lower p hp)
          (by rw [h', (upper p (by omega) (by omega)).le.antisymm (lower p hp).le])
  · rw [hp, getElem!_insert_eq α i v hi, getElem!_insert_gt α i v q hi (by omega)]
    exact fun h => Nat.ne_of_lt (upper (q - 1) (by omega) (by omega)) (congrArg BitVec.toNat h)
  · rw [getElem!_insert_gt α i v p hi hp, getElem!_insert_gt α i v q hi (by omega)]
    exact nd' (p - 1) (q - 1) (by omega) (by omega)

/-- Ordered insertion of a strictly new key keeps the array duplicate-free. -/
theorem Nodup_insert (α : List (BitVec 32)) (i : Nat) (v : BitVec 32) (nd : α.Nodup)
    (lower : ∀ j, j < i → ((α[j]!).toNat < v.toNat))
    (upper : ∀ j, i ≤ j → j < α.length → v.toNat < (α[j]!).toNat) :
    (α.take i ++ [v] ++ α.drop i).Nodup := by
  rcases Nat.lt_or_ge α.length i with hi | hi
  · rw [insert_clamp α i v (by omega)]
    exact Nodup_insert_le α α.length v (Nat.le_refl _) nd
      (fun j hj => lower j (by omega)) (fun _ hj hj' => absurd hj' (by omega))
  · exact Nodup_insert_le α i v hi nd lower upper

end Silmaril.Wasm.Logic.V1.Examples
