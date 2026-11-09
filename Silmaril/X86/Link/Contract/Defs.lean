module

public import Silmaril.X86.Link.Unit.Defs

/-! # Contracts of translation units and their composition (spec-agnostic)

The spec-agnostic core of the TU-contract layer. A program logic is abstract
(`Logic Spec`); a TU contract (`TU.Sat`) is relocation-parametric and
step-indexed; `link_compose` (`Silmaril.X86.Link.Contract.Thms`) composes the
contracts of all units of one successful link.

* `Image`, `Extends small big`: images are lists of placed sections; `big`
  extends `small` when it holds every byte `small` holds, at the same address and with the
  same section flags (`ContainsF`).
* `Logic Spec`: the interface a program logic provides.
  - `Safe n a s ctx`: the code at address `a` meets `s` for `n` steps on every
    machine whose memory contains `ctx` (a step-indexed, SafeN-style relation);
  - `zero`: everything is safe for 0 steps; `mono`: safety is downward closed;
  - `frame`: safety is preserved when the image grows (`Extends`), which is the
    locality property "adding disjoint units preserves satisfaction";
  - `Sub se si` with `sub`: an export with spec `se` may serve an import that
    assumes `si`.
  The other locality property, "relocation under a valuation that agrees on the
  unit's imports", is a theorem about `image` (`image_congr_valuation`), not an
  assumption on the logic.
* `allocatedIndices`, `WellPlaced object p`: `p` places each allocated section
  of `object` exactly once (closes the gap `Unit.image_not_wellPlaced`).
* `TU.Sat L relocate u`: for every slot, well-formed placement `p`, valuation
  `σ`, image `img` of `u` under them, step index `n` and context `ctx ⊇ img`: if
  every import `i` is safe for `n` steps at `σ i.name` in `ctx`, then every
  export `e` is safe for `n + 1` steps at its own address `u.exportAddr p e.name`.
  The `n + 1` is the "later" step that makes mutual recursion across units sound.
* `ImportsClosed L units ext`: every import is served (up to `Sub`) by an export
  of some unit, or by an assumed external entry in `ext`.
* `AbiCompatible policy units`: the ABI-tag check (`Abi.checkAbi`) accepts the
  units; it also fixes that each unit's export list names exactly its defined
  globals, which ties `TU.exports` to the symbols the linker resolves.
* `OwnershipDisjoint units out`: sections owned by a unit are disjoint from all
  sections of other units. A successful link implies it
  (`ownershipDisjoint_of_link`), so it is a consequence, not a hypothesis, of
  `link_compose`. Whether other units *write* into owned memory is a semantic
  question for the instantiated logic (the invariant `I_u` of a separation-logic
  spec), not for this layer.

The `FnSpec` instance is `Silmaril.X86.Link.FnSpec.logic`
(`Silmaril.X86.Link.FnSpec.Thms`): `Safe n a S ctx` is a frame-quantified,
step-indexed triple on the open x86 machine from `Code ∗ SysVPre S x a sp ret` to
`Code ∗ SysVPost S x sp ret`, for every code region `Code` covering `ctx`, and
`Sub := FnSpec.Sub`. `Logic`, `Entry` and `TU` are universe-polymorphic in `Spec` because
`FnSpec` lives in `Type 1`.
-/

@[expose] public section

namespace Silmaril.X86.Link.Contract

universe u

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (Layout AbsoluteSymbols Relocator LinkedSection allocated)
open Silmaril.X86.Link.Unit

/-- A placed image: a list of placed sections. -/
abbrev Image := List LinkedSection

/-- `img` holds byte `b` at address `a`, in a section with flags `f` (`SHF_WRITE` = 1,
`SHF_ALLOC` = 2, `SHF_EXECINSTR` = 4). -/
def ContainsF (img : Image) (a : Nat) (b : BitVec 8) (f : Nat) : Prop :=
  ∃ s ∈ img, s.flags = f ∧ s.address ≤ a ∧ s.data[a - s.address]? = some b

/-- `big` holds every byte that `small` holds, at the same address and in a section with
the same flags. -/
def Extends (small big : Image) : Prop :=
  ∀ a b f, ContainsF small a b f → ContainsF big a b f

/-- Flag-aware inclusion gives byte-level inclusion. -/
theorem Extends.contains {small big : Image} (h : Extends small big) {a : Nat} {b : BitVec 8}
    (hc : Contains small a b) : Contains big a b := by
  obtain ⟨s, hs, hle, hb⟩ := hc
  obtain ⟨t, ht, -, hle', hb'⟩ := h a b s.flags ⟨s, hs, rfl, hle, hb⟩
  exact ⟨t, ht, hle', hb'⟩

/-- The interface of an abstract, step-indexed program logic over images. -/
structure Logic (Spec : Type u) where
  /-- The code at address `a` meets `s` for `n` steps in every machine whose
  memory contains the image. -/
  Safe : Nat → Nat → Spec → Image → Prop
  zero : ∀ a s img, Safe 0 a s img
  mono : ∀ {n a s img}, Safe (n + 1) a s img → Safe n a s img
  frame : ∀ {n a s img big}, Extends img big → Safe n a s img → Safe n a s big
  /-- `Sub se si`: an export specified by `se` may serve an import assuming `si`. -/
  Sub : Spec → Spec → Prop
  sub : ∀ {n a se si img}, Sub se si → Safe n a se img → Safe n a si img

/-- Indices of the allocated sections of an object. -/
def allocatedIndices (object : ObjectFile) : List Nat :=
  object.sections.zipIdx.filterMap fun (part, index) =>
    if allocated part then some index else none

/-- `p` places every allocated section of `object` exactly once, and nothing else. -/
def WellPlaced (object : ObjectFile) (p : Placement) : Prop :=
  (p.map Prod.fst).Nodup ∧ (p.map Prod.fst).Perm (allocatedIndices object)

variable {Tag : Type} {Spec : Type u}

/-- **Relocation-parametric, step-indexed TU contract.** -/
def _root_.Silmaril.X86.Link.Unit.TU.Sat (L : Logic Spec) (relocate : Relocator) (u : TU Tag Spec) : Prop :=
  ∀ (slot : Nat) (p : Placement) (σ : Valuation) (img : Image),
    WellPlaced u.object p → u.image slot p σ relocate = some img →
    ∀ (n : Nat) (ctx : Image), Extends img ctx →
      (∀ i ∈ u.imports, ∀ a, σ i.name = some a → L.Safe n a i.spec ctx) →
      ∀ e ∈ u.exports, ∀ a, u.exportAddr p e.name = some a → L.Safe (n + 1) a e.spec ctx

/-- Every import is served by an export of some unit, or by an assumed external. -/
def ImportsClosed (L : Logic Spec) (units : List (TU Tag Spec)) (ext : List (Entry Tag Spec)) :
    Prop :=
  ∀ u ∈ units, ∀ i ∈ u.imports,
    (∃ (slot : Nat) (v : TU Tag Spec), units[slot]? = some v ∧ ∃ e ∈ v.exports, e.name = i.name ∧ L.Sub e.spec i.spec) ∨
    (∃ x ∈ ext, x.name = i.name ∧ L.Sub x.spec i.spec)

/-- The link-time ABI check accepts the units. -/
def AbiCompatible [DecidableEq Tag] (policy : Abi.Policy Tag) (units : List (TU Tag Spec)) :
    Prop :=
  Abi.checkAbi policy (units.map TU.object) (units.map TU.iface) = true

/-- Sections a unit owns are disjoint from every section of every other unit. -/
def OwnershipDisjoint (units : List (TU Tag Spec)) (out : Image) : Prop :=
  ∀ (slot : Nat) (u : TU Tag Spec), units[slot]? = some u →
    ∀ s ∈ out, s.key.object = slot → s.key.index ∈ u.owned →
      ∀ t ∈ out, t.key.object ≠ slot → s.Disjoint t

end Silmaril.X86.Link.Contract
