module

public import Silmaril.X86.Cfg.Defs

/-! Proofs for `Silmaril.X86.Cfg`: one step of the block decoder (`walk_cases`) and the address
arithmetic of targets (`ofNat_wrap`). -/

@[expose] public section

namespace Silmaril.Proofs.X86.Cfg

open Silmaril.X86 (Byte)
open Silmaril.X86.Flow (FlowDec Kind)
open Silmaril.X86.Cfg

variable {ε : Type}

/-- **One step of `walk`**: the instruction at `o` decodes, and it is either the last one (it
agrees with the terminator) or an interior `seq`/`rep` followed by the rest of the block. -/
theorem walk_cases {D : FlowDec} {t : Term ε} {start fuel o : Nat} {v : Option Nat} {s : List Byte}
    (h : walk D t start fuel o v s = true) :
    ∃ i l, D.decode s = some (i, l) ∧ 0 < l ∧ l ≤ s.length ∧
      (D.kind i = .rep → D.rax i = .keep) ∧
      ((l = s.length ∧ termOk t (D.kind i) (start + o + l) v = true) ∨
       (l < s.length ∧ (D.kind i = .seq ∨ D.kind i = .rep) ∧
         ∃ fuel', walk D t start fuel' (o + l) (raxStep D v i) (s.drop l) = true)) := by
  cases fuel with
  | zero => simp [walk] at h
  | succ fuel =>
    unfold walk at h
    split at h
    · simp at h
    · rename_i i l hd
      refine ⟨i, l, hd, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
        Bool.or_eq_true] at h
      obtain ⟨⟨⟨h0, hl⟩, hrep⟩, hrest⟩ := h
      refine ⟨h0, hl, fun hk => by rcases hrep with h1 | h1 <;> simp_all, ?_⟩
      by_cases he : l = s.length
      · simp only [he, ↓reduceIte] at hrest; exact Or.inl ⟨he, by simpa [he] using hrest⟩
      · simp only [he, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrest
        exact Or.inr ⟨by omega, hrest.1, fuel, hrest.2⟩

/-- **A wrapped target is the machine's sum.** -/
theorem ofNat_wrap (n : Nat) (r : Int) :
    BitVec.ofNat 64 (wrap ((n : Int) + r)) = BitVec.ofNat 64 n + BitVec.ofInt 64 r := by
  have h : BitVec.ofNat 64 (wrap ((n : Int) + r)) = BitVec.ofInt 64 ((n : Int) + r) := by
    apply BitVec.eq_of_toNat_eq
    simp only [wrap, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  rw [h, BitVec.ofInt_add, BitVec.ofInt_natCast]

end Silmaril.Proofs.X86.Cfg
