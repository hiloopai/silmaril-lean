module

public import Silmaril.X86.Sep.Alloc.Defs

/-!
# The availability layer: allocators that promise to succeed

`Sep/Alloc`'s `Iface` is loose: `mallocSpec` may return `NULL` for every request, so a client
can never rely on an allocation succeeding. `IfaceS` refines it with an **abstract state**
`St` and an **availability predicate** `avail : St → Nat → Prop`, in the style of the
resource-bounded allocator specifications of Appel and Naumann ("Verified sequential malloc/free",
ISMM 2020):

* `mmS s`: the allocator's state, described at the abstract state `s`;
* `avail s n`: a request of `n` bytes in state `s` **must** succeed.

`mallocSpecS B` takes the abstract state as a logical argument. Its postcondition is
`mallocSpec`'s, plus `⌜B.avail s n → v ≠ 0⌝`. The allocator's state after the call is again
`B.toIface.mm` (some state), so the guarantee is about one call; chaining it needs a
description of the next state, which this layer does not give.

`IfaceS.toIface` forgets the state (`mm := ∃ s, mmS s`). The refinement `mallocSpecS B ⊑
mallocSpec B.toIface` does **not** fit `FnSpec.Sub`: `Sub` picks the stronger spec's logical
argument from the weaker one's alone, while here it is the state `s` hidden in the
precondition's fragment. `FnSpec.SubH` is the variant whose choice may depend on that
fragment; it still transfers satisfaction (`FnSpec.SubH.satWith`, in `Thms`).

`Iface.toS` goes the other way: every loose allocator is a strong one that promises nothing
(`avail := False`).
-/

@[expose] public section

namespace Silmaril.X86.Sep

/-- `S ⊑ₕ T`: like `FnSpec.Sub`, but `S`'s logical argument and the frame may be chosen
from the fragment satisfying `T`'s precondition (e.g. an abstract state hidden under an
existential). -/
structure FnSpec.SubH (S T : FnSpec) : Prop where
  stack : S.stack ≤ T.stack
  arg : ∀ (y : T.Arg) (h : Frag), T.pre y h → ∃ x : S.Arg, S.args x = T.args y ∧
    ∃ R : SProp, (S.pre x ∗ R) h ∧ ∀ v, (S.post x v ∗ R) ⊢ₛ T.post y v

end Silmaril.X86.Sep

namespace Silmaril.X86.Sep.Alloc

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-- **An allocator with an availability guarantee.** -/
structure IfaceS where
  /-- The allocator's abstract state. -/
  St : Type
  /-- The allocator's state at the abstract state `s`. -/
  mmS : St → SProp
  /-- `tok p n`, as in `Iface`. -/
  tok : Word → Nat → SProp
  /-- Every non-null result is a multiple of `align`. -/
  align : Nat
  /-- Stack budget of every entry point. -/
  stack : Nat
  /-- `avail s n`: in state `s`, a request of `n` bytes succeeds. -/
  avail : St → Nat → Prop

/-- Forget the abstract state and the availability guarantee. -/
def IfaceS.toIface (B : IfaceS) : Iface where
  mm := sexists B.mmS
  tok := B.tok
  align := B.align
  stack := B.stack

/-- **`malloc` with availability.** The logical arguments are the abstract state and the
request; failure is allowed only when the request is not available. -/
def mallocSpecS (B : IfaceS) : FnSpec where
  Arg := B.St × Word
  args x := [x.2]
  stack := B.stack
  pre x := B.mmS x.1
  post x v := B.toIface.mm ∗ ⌜B.avail x.1 x.2.toNat → v ≠ 0⌝ ∗
    sor ⌜v = 0⌝ (B.toIface.Fresh v x.2.toNat)

/-- A loose allocator as a strong one that promises nothing. -/
def Iface.toS (A : Iface) : IfaceS where
  St := Unit
  mmS _ := A.mm
  tok := A.tok
  align := A.align
  stack := A.stack
  avail _ _ := False

end Silmaril.X86.Sep.Alloc
