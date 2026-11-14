module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Control.Monad.Basic
public import Silmaril.Semantics.Elgot.Thms

/-!
# TraceModels

Source: the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126`, Concrete Models, §Trace Models
(mapped by content). `PartialWriter` is the case where the output monoid acts on itself.

-/

@[expose] public section

section

/-!
## Ordered accumulation of logs

Logs compose in order, their empty value is least, and multiplication preserves
nonempty suprema on either side. Empty suprema are deliberately excluded: making
the identity absorbing would collapse the log algebra.
-/

namespace Silmaril.Elgot

universe u v

/-- A log monoid supporting limits of growing finite observations. -/
class ContinuousLog (W : Type u) [Monoid W] [CompleteLattice W] : Prop where
  one_eq_bot : (1 : W) = ⊥
  mul_mono {a b c d : W} : a ≤ b → c ≤ d → a * c ≤ b * d
  mul_sSup (w : W) (s : Set W) (hs : s.Nonempty) :
    w * sSup s = sSup ((w * ·) '' s)
  sSup_mul (s : Set W) (hs : s.Nonempty) (w : W) :
    sSup s * w = sSup ((· * w) '' s)

namespace ContinuousLog

variable {W : Type u} [Monoid W] [CompleteLattice W] [ContinuousLog W]

end ContinuousLog

namespace ContinuousLog

variable {W : Type u} [Monoid W]

/-- Multiply the first `n` logs in chronological order. -/
def prefixProd (ws : ℕ → W) : ℕ → W
  | 0 => 1
  | n + 1 => prefixProd ws n * ws n

/-- Group a stream into consecutive finite blocks; empty blocks are permitted. -/
def blocks (ws : ℕ → W) (cuts : ℕ → ℕ) (i : ℕ) : W :=
  prefixProd (fun j => ws (cuts i + j)) (cuts (i + 1) - cuts i)

variable [CompleteLattice W]

/-- The total observation of a stream is the supremum of its finite prefixes. -/
noncomputable def omegaProduct (ws : ℕ → W) : W := ⨆ n, prefixProd ws n

variable [ContinuousLog W]

end ContinuousLog

end Silmaril.Elgot

end

section

/-!
## Extended natural durations

Duration logs add elapsed time, using multiplicative notation to fit the log
interface. They distinguish repeated observations: two unit durations take twice
as long. Infinitely many unit durations accumulate to infinity.
-/

namespace Silmaril.Elgot

abbrev Duration := Multiplicative ℕ∞

namespace Duration

noncomputable instance : CompleteLattice Duration := inferInstanceAs (CompleteLattice ℕ∞)

def toENat : Duration ≃o ℕ∞ where
  toEquiv := Multiplicative.toAdd
  map_rel_iff' := Iff.rfl

/-- One elapsed time unit, distinct from the log identity (zero elapsed time). -/
def tick : Duration := Multiplicative.ofAdd 1

end Duration

end Silmaril.Elgot

end

section

/-!
## Partial computations with persistent output

The output survives even when a computation has no returned value. Sequencing
appends the next output only when the preceding computation returns. This is
the generalized writer with the output monoid acting on itself on the left.
-/

namespace Silmaril.Elgot

universe u

/-- A possibly absent result together with output that is always observable. -/
structure PartialWriter (W A : Type u) where
  value : _root_.Part A
  output : W

namespace PartialWriter

variable {W A B C : Type u}

def done (a : A) (w : W) : PartialWriter W A := ⟨.some a, w⟩

def diverge (w : W) : PartialWriter W A := ⟨.none, w⟩

variable [Monoid W]

noncomputable def bind (x : PartialWriter W A) (f : A → PartialWriter W B) : PartialWriter W B := by
  classical
  exact ⟨x.value >>= fun a => (f a).value,
    if h : x.value.Dom then x.output * (f (x.value.get h)).output else x.output⟩

noncomputable instance : Monad (PartialWriter W) where
  pure a := done a 1
  bind := bind

end PartialWriter

end Silmaril.Elgot

end

section

/-! ## Finite observations of partial writer loops -/

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B : Type u} [Monoid W]

/-- A finite prefix of recursive calls, with the output preceding its last state. -/
inductive Prefix (f : A → PartialWriter W (B ⊕ A)) : A → W → A → Prop
  | start (a : A) : Prefix f a 1 a
  | step {a a' z : A} {w : W} :
      Sum.inr a' ∈ (f a).value → Prefix f a' w z → Prefix f a ((f a).output * w) z

/-- A finite successful run and its complete output. -/
inductive Runs (f : A → PartialWriter W (B ⊕ A)) : A → W → B → Prop
  | done {a : A} {b : B} : Sum.inl b ∈ (f a).value → Runs f a (f a).output b
  | step {a a' : A} {b : B} {w : W} :
      Sum.inr a' ∈ (f a).value → Runs f a' w b → Runs f a ((f a).output * w) b

namespace Prefix

end Prefix

namespace Runs

end Runs

end Silmaril.Elgot.PartialWriter

end

section

/-!
## Iteration with persistent finite and infinite output

The result is determined by a finite successful run. Output is the supremum
of every finite observation, including observations along divergent executions.
The ordered monoid need not be commutative or idempotent.
-/

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B : Type u} [Monoid W]

def observations (f : A → PartialWriter W (B ⊕ A)) (a : A) : Set W :=
  {v | ∃ w z, Prefix f a w z ∧ v = w * (f z).output}

variable [CompleteLattice W]

noncomputable def iterOutput (f : A → PartialWriter W (B ⊕ A)) (a : A) : W :=
  sSup (observations f a)

variable [ContinuousLog W]

noncomputable instance : Iterate (PartialWriter W) where
  iter f a := ⟨iter (fun a => (f a).value) a, iterOutput f a⟩

end Silmaril.Elgot.PartialWriter

end

section

/-!
## Infinite output streams

A loop that emits the next stream element at each step has no returned value,
and its observable output is exactly the ordered infinite product. This connects
the operational prefix definition of iteration to the algebraic limit operator.
-/

namespace Silmaril.Elgot.PartialWriter

open ContinuousLog

variable {W : Type} [Monoid W]

/-- Emit one stream element and advance, with no terminating branch. -/
def stream (ws : ℕ → W) (n : ℕ) : PartialWriter W (PUnit ⊕ ℕ) :=
  done (.inr (n + 1)) (ws n)

variable [CompleteLattice W] [ContinuousLog W]

end Silmaril.Elgot.PartialWriter

end
