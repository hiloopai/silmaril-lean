module

public import Silmaril.Logic.Metamath.Verify.Machine

@[expose] public section

/-!
# Compressed proofs

The compressed proof format (Megill and Wheeler, *Metamath*, Appendix B).
The letter block encodes a sequence of positive integers: `U`-`Y` are leading
base-5 digits and `A`-`T` a final base-20 digit, all counting from one. `Z`
tags the step just completed for later reuse. If the statement has `m`
mandatory hypotheses and the parenthesized list has `n` labels, then `1..m`
push the mandatory hypotheses in order, `m+1..m+n` are the listed labels, and
`m+n+k` pushes the `k`-th saved step.

Decoding produces machine instructions. Its soundness (`decode_valid`) is that
it only emits mandatory hypotheses, listed instructions, `save` and `load`, so
the result is valid whenever its inputs are.
-/

namespace Silmaril.Logic.Metamath.Verify

universe u

variable {C V : Type u}

/-- The instruction for the zero-based compressed number `k`. -/
def numInstr (mand : Array (Expr C V)) (list : Array (Instr C V)) (k : Nat) : Instr C V :=
  if h : k < mand.size then .hyp mand[k]
  else if h' : k - mand.size < list.size then list[k - mand.size]
  else .load (k - mand.size - list.size)

/-- Decode a letter block. `acc` holds the leading digits read so far, and
`prev` records whether the last letter completed a step, which `Z` requires. -/
def decodeAux (mand : Array (Expr C V)) (list : Array (Instr C V)) :
    List Char → Nat → Bool → Array (Instr C V) → Except ProofError (Array (Instr C V))
  | [], acc, _, out => if acc = 0 then .ok out else .error .unfinishedNumber
  | c :: cs, acc, prev, out =>
    if 'A' ≤ c ∧ c ≤ 'T' then
      decodeAux mand list cs 0 true (out.push (numInstr mand list (acc * 20 + (c.toNat - 65))))
    else if 'U' ≤ c ∧ c ≤ 'Y' then
      decodeAux mand list cs (acc * 5 + (c.toNat - 84)) false out
    else if c = 'Z' then
      if prev then decodeAux mand list cs 0 false (out.push .save) else .error .badSave
    else if c = '?' then .error .incomplete
    else .error (.badLetter c)

/-- Decode the letter block of a compressed proof into instructions, given the
mandatory hypotheses and the instructions of the parenthesized labels. -/
def decode (mand : Array (Expr C V)) (list : Array (Instr C V)) (letters : String) :
    Except ProofError (List (Instr C V)) :=
  match decodeAux mand list letters.toList 0 false #[] with
  | .ok out => .ok out.toList
  | .error e => .error e

theorem numInstr_valid {Γ : Set (Assertion C V)} {F : Assertion C V}
    {mand : Array (Expr C V)} {list : Array (Instr C V)}
    (hmand : ∀ e ∈ mand.toList, e ∈ F.hypExprs) (hlist : ∀ i ∈ list.toList, i.Valid Γ F)
    (k : Nat) : (numInstr mand list k).Valid Γ F := by
  unfold numInstr
  split
  · exact hmand _ (Array.mem_toList_iff.2 (Array.getElem_mem _))
  · split
    · exact hlist _ (Array.mem_toList_iff.2 (Array.getElem_mem _))
    · trivial

theorem decodeAux_valid {Γ : Set (Assertion C V)} {F : Assertion C V}
    {mand : Array (Expr C V)} {list : Array (Instr C V)}
    (hmand : ∀ e ∈ mand.toList, e ∈ F.hypExprs) (hlist : ∀ i ∈ list.toList, i.Valid Γ F) :
    ∀ {cs : List Char} {acc : Nat} {prev : Bool} {out res : Array (Instr C V)},
      (∀ i ∈ out.toList, i.Valid Γ F) → decodeAux mand list cs acc prev out = .ok res →
      ∀ i ∈ res.toList, i.Valid Γ F
  | [], acc, prev, out, res, hout, h => by
    simp only [decodeAux] at h
    split at h
    · cases h; exact hout
    · cases h
  | c :: cs, acc, prev, out, res, hout, h => by
    have push : ∀ j : Instr C V, j.Valid Γ F → ∀ i ∈ (out.push j).toList, i.Valid Γ F := by
      intro j hj i hi
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · exact hout i hi
      · exact hj
    simp only [decodeAux] at h
    split at h
    · exact decodeAux_valid hmand hlist (push _ (numInstr_valid hmand hlist _)) h
    · split at h
      · exact decodeAux_valid hmand hlist hout h
      · split at h
        · split at h
          · exact decodeAux_valid hmand hlist (push .save trivial) h
          · cases h
        · split at h <;> cases h

/-- **Soundness of compressed decoding**: decoding only emits valid
instructions when the mandatory hypotheses and the listed labels are valid. -/
theorem decode_valid {Γ : Set (Assertion C V)} {F : Assertion C V}
    {mand : Array (Expr C V)} {list : Array (Instr C V)} {letters : String}
    {is : List (Instr C V)}
    (hmand : ∀ e ∈ mand.toList, e ∈ F.hypExprs) (hlist : ∀ i ∈ list.toList, i.Valid Γ F)
    (h : decode mand list letters = .ok is) : ∀ i ∈ is, i.Valid Γ F := by
  simp only [decode] at h
  split at h
  · rename_i out hout
    cases h
    exact decodeAux_valid hmand hlist (by simp) hout
  · cases h

end Silmaril.Logic.Metamath.Verify
