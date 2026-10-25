module

-- Kernel computation uses the body of the upstream derived instance.
import all Batteries.Data.Except

public import Silmaril.Logic.Metamath.Verify.Machine

@[expose] public section

/-!
# Checking a proof in the kernel

The proof machine is generic in constants and variables and uses no hashing,
so the kernel can run it by reduction. Here `demo0.mm` is coded with natural
numbers and the proof of its theorem `th1 : |- t = t` is checked with
`decide +kernel`. The result is checked by Lean's kernel.
Soundness of the machine (`verify_sound`) then gives a derivation from the
seven axioms of `demo0.mm`.

The full checker `Silmaril.Logic.Metamath.Verify.check` on a `Text.Source`
does not reduce by the same method with the pinned toolchain: its hash maps hash strings with `String.hash`, which is
opaque to the kernel, so reduction gets stuck. Replacing the hash by a
reducible one is not enough: the operations of `Std.HashSet` and `Std.HashMap`
themselves (already `(∅.insert "a").contains "a"`) and `String.all` do not
reduce in the kernel.
-/

namespace Silmaril.Logic.Metamath.Verify.Kernel

/-- A constant of the coded `demo0.mm`: `0 + = -> ( ) term wff |-` are `0`-`8`. -/
abbrev c (n : Nat) : Sym Nat Nat := .const n

/-- A variable of the coded `demo0.mm`: `t r s P Q` are `0`-`4`. -/
abbrev v (n : Nat) : Sym Nat Nat := .var n

/-- `tze $a term 0 $.` -/
def tze : Assertion Nat Nat := ⟨[], [], ⟨6, [c 0]⟩⟩
/-- `tpl $a term ( t + r ) $.` -/
def tpl : Assertion Nat Nat := ⟨[], [.float 6 0, .float 6 1], ⟨6, [c 4, v 0, c 1, v 1, c 5]⟩⟩
/-- `weq $a wff t = r $.` -/
def weq : Assertion Nat Nat := ⟨[], [.float 6 0, .float 6 1], ⟨7, [v 0, c 2, v 1]⟩⟩
/-- `wim $a wff ( P -> Q ) $.` -/
def wim : Assertion Nat Nat := ⟨[], [.float 7 3, .float 7 4], ⟨7, [c 4, v 3, c 3, v 4, c 5]⟩⟩
/-- `a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.` -/
def a1 : Assertion Nat Nat := ⟨[], [.float 6 0, .float 6 1, .float 6 2],
  ⟨8, [c 4, v 0, c 2, v 1, c 3, c 4, v 0, c 2, v 2, c 3, v 1, c 2, v 2, c 5, c 5]⟩⟩
/-- `a2 $a |- ( t + 0 ) = t $.` -/
def a2 : Assertion Nat Nat := ⟨[], [.float 6 0], ⟨8, [c 4, v 0, c 1, c 0, c 5, c 2, v 0]⟩⟩
/-- `mp $a |- Q $.` with hypotheses `|- P` and `|- ( P -> Q )`. -/
def mp : Assertion Nat Nat := ⟨[], [.float 7 3, .float 7 4, .ess ⟨8, [v 3]⟩,
  .ess ⟨8, [c 4, v 3, c 3, v 4, c 5]⟩], ⟨8, [v 4]⟩⟩

/-- The axioms of `demo0.mm`. -/
def axioms : Set (Assertion Nat Nat) := {B | B ∈ [tze, tpl, weq, wim, a1, a2, mp]}

instance : DecidablePred (· ∈ axioms) := fun B =>
  inferInstanceAs (Decidable (B ∈ [tze, tpl, weq, wim, a1, a2, mp]))

/-- `th1 $p |- t = t $.` -/
def th1 : Assertion Nat Nat := ⟨[], [.float 6 0], ⟨8, [v 0, c 2, v 0]⟩⟩

/-- The normal proof of `th1`. -/
def th1Proof : List (Instr Nat Nat) :=
  let tt : Instr Nat Nat := .hyp ⟨6, [v 0]⟩
  [tt, .app "tze" tze, .app "tpl" tpl, tt, .app "weq" weq, tt, tt, .app "weq" weq, tt,
    .app "a2" a2, tt, .app "tze" tze, .app "tpl" tpl, tt, .app "weq" weq, tt, .app "tze" tze,
    .app "tpl" tpl, tt, .app "weq" weq, tt, tt, .app "weq" weq, .app "wim" wim, tt,
    .app "a2" a2, tt, .app "tze" tze, .app "tpl" tpl, tt, tt, .app "a1" a1, .app "mp" mp,
    .app "mp" mp]

theorem th1Proof_valid : ∀ i ∈ th1Proof, i.Valid axioms th1 := by decide +kernel

theorem th1Proof_verify : verify (fun _ _ => false) th1Proof th1.concl = .ok () := by
  decide +kernel

/-- `th1` is derivable from the axioms of `demo0.mm`, by running its proof in
the kernel. -/
theorem th1_derivable : Derivable axioms th1 := by
  refine derivable_iff.2 ⟨Dummies.none th1, ?_⟩
  rw [Assertion.extend_none]
  exact verify_sound (fun _ _ h => Bool.noConfusion h) th1Proof_valid th1Proof_verify

end Silmaril.Logic.Metamath.Verify.Kernel
