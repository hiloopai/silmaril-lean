module

public import Silmaril.Wasm.Component.Algebra.Term.Defs

/-!
# The component algebra: composition operators

Operators on components of the component IR (`Comp M`). Each places its arguments as
nested instances (`Node.inst`), so each is the evaluation of a term
(`Silmaril.Wasm.Component.Algebra.Term`); renaming acts on labels only.

* `ident I`: the **identity** component of the interface `I`: it re-exports its imports;
* `seq c₁ c₂`: **plugging** (sequential composition): an instance of `c₁` on the
  imports, and an instance of `c₂` whose `j`-th import is the `j`-th export of `c₁`
  (positionally; `wac plug` plugs by name, see `Silmaril.Wasm.Wac.Seq`); it exports the
  exports of `c₂`;
* `par c₁ c₂`: **independent instantiation** (tensor): the imports of `c₁` then those of
  `c₂`, one instance of each on its own imports, the exports of `c₁` then those of `c₂`;
* `wrap I args c`: **instantiation with arguments**: one instance of `c` whose imports
  are wired by `args` over the imports `I`, re-exporting all exports of `c`;
  `reimport I ρ c` is `wrap` with forwarding arguments: the `i`-th import of `c` is the
  `ρ[i]`-th import of `I`. A non-injective `ρ` **merges** imports; wrapping a
  component whose own import list is a sublist of `I` **promotes** them;
* `select keep c`: **hiding** of exports: keep the exports of indices `keep`, in that
  order (indices out of range are dropped);
* `renameExports f c`, `renameImports f c`: **renaming** of exports and imports.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

variable {M : Type}

/-- The handler forwarding function `i` to function `b + i` (used to describe wiring). -/
def shiftH (b : Nat) : Handler sigU sigU := fun q => .call (b + q.1, q.2) fun r => .pure r

/-- Forwarding wiring: `n` functions `b, b+1, …` of the environment. -/
def fwds (b n : Nat) : List Impl := (List.range n).map fun j => Impl.fwd (b + j)

/-- Re-export the exports `xs` by forwarding to the functions `b, b+1, …`. -/
def reexport : Nat → List Export → List Export
  | _, [] => []
  | b, x :: xs => { x with impl := .fwd b } :: reexport (b + 1) xs

/-- The interface offered by a component. -/
def exportIface (c : Comp M) : Iface := c.exports.map fun x => (x.name, x.ty)

/-- Exports with the names and types of an interface (their implementations are set by
`reexport`). -/
def ifaceExports (I : Iface) : List Export := I.map fun p => ⟨p.1, p.2, Impl.trap⟩

/-- **The identity component** of an interface. -/
def ident (I : Iface) : Comp M := .mk I [] (reexport 0 (ifaceExports I))

/-- **Plugging**: the exports of `c₁` satisfy the imports of `c₂`, positionally. -/
def seq (c₁ c₂ : Comp M) : Comp M :=
  .mk c₁.imports
    [.inst c₁ (fwds 0 c₁.imports.length),
     .inst c₂ (fwds c₁.imports.length c₂.imports.length)]
    (reexport (c₁.imports.length + c₁.exports.length) c₂.exports)

/-- **Independent instantiation**. -/
def par (c₁ c₂ : Comp M) : Comp M :=
  .mk (c₁.imports ++ c₂.imports)
    [.inst c₁ (fwds 0 c₁.imports.length),
     .inst c₂ (fwds c₁.imports.length c₂.imports.length)]
    (reexport (c₁.imports.length + c₂.imports.length) (c₁.exports ++ c₂.exports))

/-- **Instantiation with arguments** `args` over the imports `I`. -/
def wrap (I : Iface) (args : List Impl) (c : Comp M) : Comp M :=
  .mk I [.inst c args] (reexport I.length c.exports)

/-- **Promotion and merging of imports**: the `i`-th import of `c` is the `ρ[i]`-th
import of `I`. -/
def reimport (I : Iface) (ρ : List Nat) (c : Comp M) : Comp M :=
  wrap I (ρ.map Impl.fwd) c

/-- The exports of `c` of indices `keep`, forwarding from `b`. -/
def keptExports (b : Nat) (xs : List Export) (keep : List Nat) : List Export :=
  keep.filterMap fun j => xs[j]?.map fun x => { x with impl := .fwd (b + j) }

/-- **Hiding**: keep the exports of indices `keep`. -/
def select (keep : List Nat) (c : Comp M) : Comp M :=
  .mk c.imports [.inst c (fwds 0 c.imports.length)]
    (keptExports c.imports.length c.exports keep)

/-- **Renaming of exports.** -/
def renameExports (f : String → String) : Comp M → Comp M
  | .mk I ns xs => .mk I ns (xs.map fun x => { x with name := f x.name })

/-- **Renaming of imports.** -/
def renameImports (f : String → String) : Comp M → Comp M
  | .mk I ns xs => .mk (I.map fun p => (f p.1, p.2)) ns xs

end Silmaril.Wasm.Component.Algebra
