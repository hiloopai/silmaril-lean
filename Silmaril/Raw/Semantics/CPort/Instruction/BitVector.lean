module

public import Silmaril.Semantics.CPort.Isotope.Morphism.SeqCase.Monadic.Defs
public import Silmaril.Semantics.CPort.Isotope.Morphism.CaseIter.Monadic.Defs
public import Mathlib.Data.BitVec

/-!
# Fixed-width bitvector instructions

Widths are part of the signature. Arithmetic is modular; shifts use the unsigned
value of their second operand without masking. Resizing truncates when the
target is smaller. Comparisons return `unit + unit` (true on the left), so case
analysis needs no additional Boolean eliminator.
-/

@[expose] public section

namespace Silmaril.Instruction.BitVector

inductive Binary where
  | add | sub | mul | and | or | xor | shl | lshr | ashr
  deriving DecidableEq, Repr

inductive Unary where
  | neg | not
  deriving DecidableEq, Repr

inductive Comparison where
  | eq | ult | ule | slt | sle
  deriving DecidableEq, Repr

inductive Instr where
  | const {w : Nat} (value : BitVec w)
  | binary (w : Nat) (op : Binary)
  | unary (w : Nat) (op : Unary)
  | compare (w : Nat) (op : Comparison)
  | resize (source target : Nat) (signed : Bool)
  | extract (source start length : Nat)
  | concat (high low : Nat)
  deriving DecidableEq, Repr

instance : HasTy Instr (Ty Nat) where
  src
    | .const _ => .unit
    | .binary w _ | .compare w _ => .product (.base w) (.base w)
    | .unary w _ | .resize w _ _ | .extract w _ _ => .base w
    | .concat hi lo => .product (.base hi) (.base lo)
  trg
    | .const (w := w) _ | .binary w _ | .unary w _ => .base w
    | .compare _ _ => .coprod .unit .unit
    | .resize _ w _ | .extract _ _ w => .base w
    | .concat hi lo => .base (hi + lo)

instance : HasEff Instr Bool where
  eff _ := false

abbrev Denote := Ty.denote BitVec

def Binary.eval {w : Nat} : Binary → BitVec w × BitVec w → BitVec w
  | .add, (x, y) => x + y
  | .sub, (x, y) => x - y
  | .mul, (x, y) => x * y
  | .and, (x, y) => x &&& y
  | .or, (x, y) => x ||| y
  | .xor, (x, y) => x ^^^ y
  | .shl, (x, y) => x <<< y.toNat
  | .lshr, (x, y) => x >>> y.toNat
  | .ashr, (x, y) => x.sshiftRight y.toNat

def Unary.eval {w : Nat} : Unary → BitVec w → BitVec w
  | .neg, x => -x
  | .not, x => ~~~x

def Comparison.eval {w : Nat} : Comparison → BitVec w × BitVec w → Bool
  | .eq, (x, y) => x == y
  | .ult, (x, y) => x.ult y
  | .ule, (x, y) => x.ule y
  | .slt, (x, y) => x.slt y
  | .sle, (x, y) => x.sle y

/-- Total mathematical interpretation of each typed primitive. -/
def Instr.eval : (f : Instr) → Denote (instrSrc f) → Denote (instrTrg f)
  | .const x, _ => x
  | .binary _ op, p => op.eval p
  | .unary _ op, x => op.eval x
  | .compare _ op, p => if op.eval p then .inl PUnit.unit else .inr PUnit.unit
  | .resize _ w signed, x => if signed then x.signExtend w else x.setWidth w
  | .extract _ start len, x => x.extractLsb' start len
  | .concat _ _, (x, y) => BitVec.append x y

open Isotope.Semantics

/-- Use the same pure instructions in any of the monadic calculus models. -/
def model (m : Type → Type) [Monad m] : InstructionModel Denote Instr m :=
  .ofPure Denote Instr m Instr.eval

theorem model_respectsPure (m : Type → Type) [Monad m] :
    (model m).RespectsPure (ε := Bool) := fun f _ => ⟨f.eval, fun _ => rfl⟩

@[simp] theorem add_zero {w : Nat} (x : BitVec w) :
    Instr.eval (.binary w .add) (x, 0#w) = x := BitVec.add_zero x

@[simp] theorem xor_self {w : Nat} (x : BitVec w) :
    Instr.eval (.binary w .xor) (x, x) = 0#w := BitVec.xor_self

theorem compare_self {w : Nat} (x : BitVec w) :
    Instr.eval (.compare w .eq) (x, x) = Sum.inl PUnit.unit := by
  simp [Instr.eval, Comparison.eval]
  rfl

namespace Examples

open Isotope LetSeq.LocallyNameless

def addZero {w : Nat} (x : BitVec w) : Tm Empty Instr 0 :=
  .op (.binary w .add) (.pair (.op (.const x) .unit) (.op (.const (0#w)) .unit))

def addZeroTyped {w : Nat} (x : BitVec w) :
    Derivation Instr (.nil : Ctx Empty (Ty Nat)) .nil (addZero x) (.base w) :=
  .op (.pair (.op .unit) (.op .unit))

theorem denote_addZero {w : Nat} (x : BitVec w) (m : Type → Type)
    [Monad m] [LawfulMonad m] :
    (addZeroTyped x).denoteClosed Denote (model m) = pure x := by
  change (((pure PUnit.unit >>= fun _ => pure x) >>= fun a =>
    (pure PUnit.unit >>= fun _ => pure (0#w)) >>= fun b => pure (a, b)) >>=
    fun p => pure (p.1 + p.2)) = pure x
  simp

theorem denote_addZero_case {w : Nat} (x : BitVec w) (m : Type → Type)
    [Monad m] [LawfulMonad m] :
    (Morphism.SeqCase.derivation (addZeroTyped x)).denoteClosed Denote (model m) = pure x := by
  simp only [LetCase.LocallyNameless.Derivation.denoteClosed,
    Morphism.SeqCase.denote_derivation]
  have h := denote_addZero x m
  unfold Derivation.denoteClosed at h
  convert h using 2

theorem denote_addZero_iter {w : Nat} (x : BitVec w) (m : Type → Type)
    [Monad m] [LawfulMonad m] [Elgot.Iterate m] :
    (Morphism.CaseIter.derivation (Morphism.SeqCase.derivation (addZeroTyped x))).denoteClosed
      Denote (model m) = pure x := by
  simp only [LetIter.LocallyNameless.Derivation.denoteClosed,
    Morphism.CaseIter.denote_derivation, Morphism.SeqCase.denote_derivation]
  have h := denote_addZero x m
  unfold Derivation.denoteClosed at h
  convert h using 2

end Examples
end Silmaril.Instruction.BitVector
