module

public import Silmaril.X86.Sep.Defs
public import Silmaril.X86.Sse9.Defs
public import Silmaril.X86.Safe.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Extends.Defs
/-!
# Separation logic with XMM registers: an additive product on fragments

`Sep.Loc` has no XMM location, and adding one would break
every exhaustive match on `Loc`. Instead the XMM file is a **second component** of a
fragment:

* `PMap α β := α → Option β`: partial maps, with `empty`, `single`, `Disjoint`, `union`,
  `Le`, `reval` defined as `Sep.Frag`'s (`Frag.union h₁ h₂ = PMap.union h₁ h₂`, … are proved
  in `Proofs/.../Xmm/Algebra.lean` and re-exported by `Thms.lean`), so one set of lemmas serves both components.
* `XMap := PMap XReg Xmm`, and `XFrag := Frag × XMap`; `XFrag.Disjoint`/`union`/`Le`/`reval`
  are the `PMap` operations, componentwise.
* `XSProp := XFrag → Prop`, with `xsep` (`P ∗ₓ Q`), `xemp`, `xspure` (`⌜φ⌝ₓ`), `xsexists`,
  `xsand`, `XEntails` (`P ⊢ₓ Q`) and `xtrue` (the XMM-level "garbage"; `Sep.strue` of
  `Sep/Extra` stays the `SProp` one).
* `lift P` (`↑ₓP`): an `SProp` owning no XMM register.
* XMM atoms: `xmmPt r v`, `xmmAny r`, `xmmLowPt r bytes` (the low `bytes.length` bytes of
  `r`, little-endian, are `bytes`; the rest is unknown).
* `toXFrag x`: the total fragment of an `Sse9.XState` (it reads `Sse9.XState.xmm`).
* `XSafeN M Q n x` is the public `Safe.SafeN M Q n x` on an XMM machine `M : SegVC.Isa XState`
  (`Sse9.isa`); `XSTriple M n P Q` has the shape of `Safe.STriple` over `XSProp`.
* `ExtendsOpen9X M`: every `Open9` step is an `M` step with the XMM file unchanged; it follows
  from `Open9.isa.Extends M` along the lens `x ↦ x.m` (`ExtendsOpen9X.of_extends`).

Laws and the bridge from `Open9` triples are in `Sep/Xmm/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Xmm

open Silmaril.X86 (MState XReg Byte)
open Silmaril.X86.Sse9 (Xmm XFile XState le128)
open Silmaril.X86.Sep

/-! ## Partial maps -/

/-- A partial map. `Sep.Frag` is `PMap Loc Val`. -/
abbrev PMap (α : Type) (β : Type) := α → Option β

namespace PMap

variable {α β : Type}

/-- The empty map. -/
def empty : PMap α β := fun _ => none

/-- The map with one key. -/
def single [DecidableEq α] (a : α) (v : β) : PMap α β := fun a' => if a' = a then some v else none

/-- Disjoint domains. -/
def Disjoint (f g : PMap α β) : Prop := ∀ a, f a = none ∨ g a = none

/-- Left-biased union. -/
def union (f g : PMap α β) : PMap α β := fun a =>
  match f a with
  | some v => some v
  | none => g a

/-- Containment. -/
def Le (f s : PMap α β) : Prop := ∀ a v, f a = some v → s a = some v

/-- The domain of `f` with the values of `s`. -/
def reval (f s : PMap α β) : PMap α β := fun a => if (f a).isSome then s a else none

end PMap

/-! ## Fragments with XMM registers -/

/-- A partial XMM file. -/
abbrev XMap := PMap XReg Sse9.Xmm

/-- The total partial map of an XMM file. -/
def XMap.all (x : XFile) : XMap := fun r => some (x r)

/-- A partial machine state with XMM registers. -/
abbrev XFrag := Frag × XMap

namespace XFrag

/-- The empty fragment. -/
def empty : XFrag := (PMap.empty, PMap.empty)

/-- Componentwise disjoint domains. -/
def Disjoint (h₁ h₂ : XFrag) : Prop := PMap.Disjoint h₁.1 h₂.1 ∧ PMap.Disjoint h₁.2 h₂.2

/-- Componentwise union. -/
def union (h₁ h₂ : XFrag) : XFrag := (PMap.union h₁.1 h₂.1, PMap.union h₁.2 h₂.2)

/-- Componentwise containment. -/
def Le (h s : XFrag) : Prop := PMap.Le h.1 s.1 ∧ PMap.Le h.2 s.2

/-- Componentwise re-valuation. -/
def reval (h s : XFrag) : XFrag := (PMap.reval h.1 s.1, PMap.reval h.2 s.2)

end XFrag

/-- Assertions on fragments with XMM registers. -/
abbrev XSProp := XFrag → Prop

/-- Separating conjunction. -/
def xsep (P Q : XSProp) : XSProp := fun h =>
  ∃ h₁ h₂, XFrag.Disjoint h₁ h₂ ∧ h = XFrag.union h₁ h₂ ∧ P h₁ ∧ Q h₂

/-- The empty fragment. -/
def xemp : XSProp := fun h => h = XFrag.empty

/-- A pure fact, owning nothing. -/
def xspure (φ : Prop) : XSProp := fun h => h = XFrag.empty ∧ φ

/-- Existential quantification. -/
def xsexists {α : Sort _} (P : α → XSProp) : XSProp := fun h => ∃ a, P a h

/-- Non-separating conjunction. -/
def xsand (P Q : XSProp) : XSProp := fun h => P h ∧ Q h

/-- Every fragment ("garbage"). -/
def xtrue : XSProp := fun _ => True

/-- Entailment. -/
def XEntails (P Q : XSProp) : Prop := ∀ h, P h → Q h

@[inherit_doc] scoped infixr:35 " ∗ₓ " => xsep
@[inherit_doc] scoped infix:25 " ⊢ₓ " => XEntails
@[inherit_doc] scoped notation "⌜" φ "⌝ₓ" => xspure φ

/-- An `SProp` that owns no XMM register. -/
def lift (P : SProp) : XSProp := fun h => P h.1 ∧ h.2 = PMap.empty

@[inherit_doc] scoped prefix:max "↑ₓ" => lift

/-! ## XMM atoms -/

/-- XMM register `r` holds `v` (and nothing else is owned). -/
def xmmPt (r : XReg) (v : Sse9.Xmm) : XSProp := fun h => h.1 = Frag.empty ∧ h.2 = PMap.single r v

/-- XMM register `r` is owned, with an unknown value. -/
def xmmAny (r : XReg) : XSProp := xsexists (xmmPt r)

/-- XMM register `r` is owned and its low `bytes.length` bytes (little-endian) are `bytes`;
the upper bytes are unknown. -/
def xmmLowPt (r : XReg) (bytes : List Byte) : XSProp :=
  xsexists fun v => xmmPt r v ∗ₓ ⌜(le128 v).take bytes.length = bytes⌝ₓ

/-! ## Machine states as fragments -/

/-- The total fragment of an XMM machine state (everything but `fsBase`). -/
def toXFrag (x : XState) : XFrag := (toFrag x.m, XMap.all x.xmm)

/-- An assertion holds of a part of the machine state. -/
def XHolds (P : XSProp) (x : XState) : Prop := ∃ h, P h ∧ XFrag.Le h (toXFrag x)

/-! ## Safety and triples over XMM machines -/

variable (M : Silmaril.X86.SegVC.Isa XState)

/-- **Step-indexed partial correctness** on an XMM machine: the public `Safe.SafeN` on `M`. -/
abbrev XSafeN (Q : XState → Prop) : Nat → XState → Prop := Silmaril.X86.Safe.SafeN M Q

/-- **A step-indexed triple** on an XMM machine, frame built in (the shape of
`Safe.STriple`, over `XSProp`, so that assertions may own XMM registers). -/
def XSTriple (n : Nat) (P Q : XSProp) : Prop :=
  ∀ (F : XSProp) (x : XState), (P ∗ₓ F) (toXFrag x) →
    XSafeN M (fun x' => (Q ∗ₓ F) (toXFrag x')) n x

/-- **The machine extends `Open9` with the XMM file as the frame**: every `Open9` step of
`x.m` is an `M` step that keeps `x.xmm`. This is `Open9.isa.Extends M` along the lens
`x ↦ x.m` (`ExtendsOpen9X.of_extends`); `Sse9.isa` is an instance. -/
class ExtendsOpen9X : Prop where
  ext : ∀ {x : XState} {m' : MState}, Silmaril.X86.Open9.step x.m = some m' →
    M.step x = some ⟨m', x.xmm⟩

/-- An extension of `Open9` along the lens `x ↦ x.m` (with `put x m = ⟨m, x.xmm⟩`) gives
`ExtendsOpen9X`. -/
theorem ExtendsOpen9X.of_extends {M : Silmaril.X86.SegVC.Isa XState}
    (E : Silmaril.X86.Open9.isa.Extends M) (hv : ∀ x, E.view x = x.m)
    (hp : ∀ x m, E.put x m = ⟨m, x.xmm⟩) : ExtendsOpen9X M :=
  ⟨fun {x m'} h => by rw [← hp]; exact E.step (by rw [hv]; exact h)⟩

end Silmaril.X86.Sep.Xmm
