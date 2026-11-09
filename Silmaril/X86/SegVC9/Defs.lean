module

public import Silmaril.X86.SegVC
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# Segment VCs on the open machine over `Ext9`: simp sets and segment stops

* `segStops exits Q`: a segment's exit offsets as the stops of its segment VC, each with
  the postcondition `Q`.
* The simp sets of `seg_vc9_var` (`Silmaril.X86.SegVC9.Thms`), declared here because Lean
  cannot use an attribute in the module that declares it:
  * `seg_vc9_var`: the normalising lemmas of one `seg_vc9_var` pass (filled in `Thms`). It
    is `seg_vc9`'s lemma set with the `rfl` unfoldings of `wpN`/`wpI`/`after` replaced by
    equation lemmas with propositional proofs;
  * `seg_vc9_listing`: a listing's per-offset lookups (`List.lookup o L = some (i, l)`) and
    `nextAt` equations. A proof file adds its listing's lemmas locally
    (`attribute [local seg_vc9_listing] …`), once.

A simp set is indexed once, when the attribute is applied; `simp only [l₁, …, lₙ]`
re-elaborates and re-indexes its `n` lemmas on every call. For a long listing whose lookup
lemmas are passed to every pass, that indexing dominates the cost of the tactic.
-/

public meta section

/-- The normalising lemmas of one `seg_vc9_var` pass. -/
register_simp_attr seg_vc9_var

/-- A listing's lookup and `nextAt` equations for `seg_vc9_var` (add them locally). -/
register_simp_attr seg_vc9_listing

end

@[expose] public section

namespace Silmaril.X86.SegVC9

/-- The exits of a segment as the stops of its segment VC, each with the postcondition
`Q`. -/
abbrev segStops {σ : Type} (exits : List Nat) (Q : σ → Prop) : List (Nat × (σ → Prop)) :=
  exits.map fun e => (e, Q)

end Silmaril.X86.SegVC9
