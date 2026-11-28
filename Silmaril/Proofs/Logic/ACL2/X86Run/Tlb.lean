module

public import Silmaril.Logic.ACL2.X86Run.Status.TlbDefs
public import Silmaril.Logic.ACL2.Standard.Quotient.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.X86Run.Tlb

open Silmaril.Logic.ACL2.Standard
open Silmaril.Logic.ACL2.X86Run.Status
open Silmaril.Logic.ACL2.X86Run.Status.Tlb

theorem keyP_rank_lt (l : Layout) (x : Object) (hx : keyP l x = true) :
    x.natRank < 2 ^ l.keyWidth := by
  cases h : x.integerValue? with
  | none => simp [keyP, unsignedByteP, h] at hx
  | some n =>
    have range : 0 ≤ n ∧ n < (2 : Int) ^ l.keyWidth := by
      simpa [keyP, unsignedByteP, h] using hx
    have limit : (n.toNat : Int) < (↑(2 ^ l.keyWidth : Nat) : Int) := by
      simpa [Int.toNat_of_nonneg range.1] using range.2
    simpa [Object.natRank, h] using Int.ofNat_lt.mp limit

theorem selectedBits_native (l : Layout) (key : Nat) (valid : key < 2 ^ l.keyWidth) :
    (selectedBits l.modeWidth l.modeOffset key : Int) =
      Quotient.modInteger
        (Quotient.floorInteger (Quotient.modInteger key (2 ^ l.keyWidth)) (2 ^ l.modeOffset))
        (2 ^ l.modeWidth) := by
  simp only [selectedBits, Quotient.modInteger_eq_mod, Quotient.floorInteger_eq_div]
  rw [Int.ofNat_mod_ofNat, Nat.mod_eq_of_lt valid, Int.ofNat_ediv_ofNat, Int.ofNat_mod_ofNat]

theorem goodKeyP_native (l : Layout) (x : Object) : goodKeyP l x =
    (if keyP l x then
      decide (Quotient.modInteger
        (Quotient.floorInteger (Quotient.modInteger x.natRank (2 ^ l.keyWidth)) (2 ^ l.modeOffset))
        (2 ^ l.modeWidth) ≤ (l.maxMode : Int))
    else false) := by
  cases h : keyP l x with
  | false => simp [goodKeyP, h]
  | true =>
    rw [← selectedBits_native l x.natRank (keyP_rank_lt l x h)]
    simp [goodKeyP, h]

end Silmaril.Proofs.Logic.ACL2.X86Run.Tlb
