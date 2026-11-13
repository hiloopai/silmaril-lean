module

public import Silmaril.Wasm.Wac.NestOrder.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Thms

/-!
# WAC: nesting and inlining list imports in different orders

An instance of `NestOk` (`ok`) where the nested and the inlined composition, built by
`Graph.toComp` (first-occurrence import order), have their imports in different orders:
`g₁` declares `b` before `a` but instantiates package `0` (importing `a`) before package
`1` (importing `b`); `g₂` is one instance of `g₁`. The nested side imports `g₁`'s
interface, `b` then `a`; the inlined side meets `a` first.

* `imports_ne` (kernel): the flat components' imports differ;
* `flatten_toComp_ne`: so the equality of the flat components with first-occurrence
  import order, under `NestOk`, is false in general (`not_flatten_toComp_eq`);
* `importPerm_eq` (kernel): the renumbering of `nest_inline_toComp` swaps the two
  imports.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestOrderExample

open Silmaril.Wasm.Component

instance : CoreModule Unit := ⟨fun _ => [], fun _ => []⟩

def ft : FuncTy := anyTy

/-- Package 0 imports `a`, package 1 imports `b`; both export `f`. -/
def pkgs : Nat → Comp Unit
  | 0 => .mk [("a", ft)] [] [⟨"f", ft, Impl.fwd 0⟩]
  | 1 => .mk [("b", ft)] [] [⟨"f", ft, Impl.fwd 0⟩]
  | _ => .mk [] [] []

def g₁ : Graph where
  imports := [("b", ft), ("a", ft)]
  nodes := [⟨0, []⟩, ⟨1, []⟩]
  exports := [("f", .out 0 "f")]

def g₂ : Graph where
  nodes := [⟨2, []⟩]
  exports := [("f", .out 0 "f")]

/-- The interface of the nested package: `g₁`'s declared imports, `b` then `a`. -/
theorem imports_nested : (sigOf (nestPkgs pkgs 2 g₁ 2)).imports = [("b", ft), ("a", ft)] := by
  decide +kernel

theorem wf₁ : g₁.WF fun k => sigOf (pkgs k) := by
  refine ⟨fun k n h => ?_, fun p hp => ?_⟩
  · rcases k with _ | _ | k <;> simp [g₁] at h <;> subst h <;> intro p hp <;>
      simp [pkgs, sigOf] at hp <;> subst hp <;>
      simp only [Inst.src, List.lookup, Option.getD, Graph.Resolves] <;> decide +kernel
  · have e : p = ("f", .out 0 "f") := by simpa [g₁] using hp
    rw [e]
    exact ⟨⟨0, []⟩, rfl, by decide, by decide +kernel⟩

theorem wf₂ : g₂.WF fun k => sigOf (nestPkgs pkgs 2 g₁ k) := by
  refine ⟨fun k n h => ?_, fun p hp => ?_⟩
  · have e : k = 0 ∧ n = ⟨2, []⟩ := by rcases k with _ | k <;> simp [g₂] at h ⊢; exact h.symm
    obtain ⟨rfl, rfl⟩ := e
    intro p hp
    have hp' : p = ("b", ft) ∨ p = ("a", ft) := by simpa [imports_nested] using hp
    rcases hp' with rfl | rfl <;>
      simp only [Inst.src, List.lookup, Option.getD, Graph.Resolves] <;> decide +kernel
  · have e : p = ("f", .out 0 "f") := by simpa [g₂] using hp
    rw [e]
    exact ⟨⟨2, []⟩, rfl, by decide, by decide +kernel⟩

theorem typed₁ : g₁.TypedImports fun k => sigOf (pkgs k) := by
  intro n hn p hp x hx
  have hn' : n = ⟨0, []⟩ ∨ n = ⟨1, []⟩ := by simpa [g₁] using hn
  rcases hn' with rfl | rfl <;> simp [pkgs, sigOf] at hp <;> subst hp <;>
    simp [Inst.src] at hx <;> subst hx <;> decide +kernel

theorem typed₂ : g₂.TypedImports fun k => sigOf (nestPkgs pkgs 2 g₁ k) := by
  intro n hn p hp x hx
  have hn' : n = ⟨2, []⟩ := by simpa [g₂] using hn
  subst hn'
  have hp' : p = ("b", ft) ∨ p = ("a", ft) := by simpa [imports_nested] using hp
  rcases hp' with rfl | rfl <;> simp [Inst.src] at hx <;> subst hx <;> decide +kernel

theorem out₁ : g₁.ExportsOut := fun p hp =>
  ⟨0, "f", by rw [show p = ("f", .out 0 "f") by simpa [g₁] using hp]⟩

theorem out₂ : g₂.ExportsOut := fun p hp =>
  ⟨0, "f", by rw [show p = ("f", .out 0 "f") by simpa [g₂] using hp]⟩

/-- The instance satisfies the conditions of nesting = inlining. -/
theorem ok : NestOk pkgs 2 g₁ g₂ :=
  ⟨wf₁, wf₂, by decide, by decide +kernel, by decide +kernel, out₁, out₂, typed₁, typed₂⟩

theorem imports_ne :
    (flatten (g₂.toComp (nestPkgs pkgs 2 g₁))).imports ≠
      (flatten ((Graph.inline (fun k => sigOf (pkgs k)) 2 g₁ g₂).toComp pkgs)).imports := by
  decide +kernel

theorem flatten_toComp_ne :
    flatten (g₂.toComp (nestPkgs pkgs 2 g₁)) ≠
      flatten ((Graph.inline (fun k => sigOf (pkgs k)) 2 g₁ g₂).toComp pkgs) :=
  fun h => imports_ne (congrArg Linked.imports h)

/-- **The unsorted form of `flatten_nest_inline` is false.** -/
theorem not_flatten_toComp_eq :
    ¬ ∀ (P : Nat → Comp Unit) (k0 : Nat) (g₁ g₂ : Graph), NestOk P k0 g₁ g₂ →
      flatten (g₂.toComp (nestPkgs P k0 g₁)) =
        flatten ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).toComp P) :=
  fun h => flatten_toComp_ne (h pkgs 2 g₁ g₂ ok)

/-- The renumbering of `nest_inline_toComp` on this instance: a swap. -/
theorem importPerm_eq :
    importPerm (g₂.iface fun k => sigOf (nestPkgs pkgs 2 g₁ k))
        ((Graph.inline (fun k => sigOf (pkgs k)) 2 g₁ g₂).iface fun k => sigOf (pkgs k)) =
      [Impl.fwd 1, Impl.fwd 0] := by
  rfl

end Silmaril.Wasm.Wac.NestOrderExample
