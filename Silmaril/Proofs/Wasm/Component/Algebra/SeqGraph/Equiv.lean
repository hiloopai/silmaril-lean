module

public import Silmaril.Proofs.Wasm.Component.Algebra.SeqGraph.Main

/-!
# `wac plug` of arbitrary graphs is positional plugging: the agreement

`inv_start`: before the socket's instances run, the positional side's valuation `V₂` and the
plug's run `r₁` are related by `Inv` (an import `x` of the socket reads, through `byName`, the
plug's export `x`, which `Graph.plugSrc` substitutes; no instance export exists yet).
`seq_graph_equiv`: with `gRun_sim`, the two flattened sides have the same nodes and export
wiring, so the components are equivalent.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra.SeqGraphProof

open Silmaril.Wasm.Component Silmaril.Wasm.Wac

variable {M : Type} [CoreModule M]

/-- An import of the socket, on the positional side. -/
theorem V₂_imp {P : Nat → Comp M} {g₁ g₂ : Graph} (ho : g₁.ExportsOut)
    (hc : Covers (fun k => sigOf (P k)) g₁ g₂) (hw : g₁.WF fun k => sigOf (P k)) {x : String}
    (hx : x ∈ names (g₂.iface fun k => sigOf (P k))) :
    V₂ P (fun k => sigOf (P k)) g₁ g₂ (.imp x) =
      (run₁ P (fun k => sigOf (P k)) g₁).1 (g₁.plugSrc (.imp x)) := by
  obtain ⟨t, q, hl, -, ha⟩ := plug_out ho hc hw hx
  obtain ⟨v, -, -, hi⟩ := lookup_of_mem x (g₂.iface fun k => sigOf (P k)) hx
  have hil : (names (g₂.iface fun k => sigOf (P k))).idxOf x <
      (g₂.iface fun k => sigOf (P k)).length := (List.getElem?_eq_some_iff.1 hi).1
  have hal : (g₁.exports.map Prod.fst).idxOf x < g₁.exports.length :=
    (List.getElem?_eq_some_iff.1 ha).1
  have hρ : (ρ₁ (fun k => sigOf (P k)) g₁ g₂)[(names (g₂.iface fun k => sigOf (P k))).idxOf x]? =
      some ((g₁.exports.map Prod.fst).idxOf x) := by
    simp only [ρ₁, List.getElem?_map, names] at hi ⊢
    rw [hi]
    rfl
  have h₂ : (σ₂ P (fun k => sigOf (P k)) g₁ g₂)[(names (g₂.iface fun k => sigOf (P k))).idxOf x]? =
      some ((Impl.fwd ((g₁.exports.map Prod.fst).idxOf x)).subst (σW P (fun k => sigOf (P k)) g₁)) := by
    simp only [σ₂, List.getElem?_map, List.getElem?_range hil, hρ, Option.map_some,
      Option.getD_some]
  have hW : (σW P (fun k => sigOf (P k)) g₁)[(g₁.exports.map Prod.fst).idxOf x]? =
      some ((Impl.fwd ((g₁.iface fun k => sigOf (P k)).length +
        (g₁.exports.map Prod.fst).idxOf x)).subst (σ₁ P (fun k => sigOf (P k)) g₁)) := by
    simp only [σW, List.getElem?_map, List.getElem?_range hal, Option.map_some]
  have h₁ : (Impl.fwd ((g₁.iface fun k => sigOf (P k)).length +
      (g₁.exports.map Prod.fst).idxOf x)).subst (σ₁ P (fun k => sigOf (P k)) g₁) =
      (run₁ P (fun k => sigOf (P k)) g₁).1 (.out t q) := by
    rw [σ₁, subst_fwd_append_right (by simp)]
    exact subst_fwd (by simp only [List.getElem?_map, ha, Option.map_some])
  have hr : g₂.resolve (fun k => sigOf (P k)) (g₂.iface fun k => sigOf (P k)) 0 (.imp x) =
      Impl.fwd ((names (g₂.iface fun k => sigOf (P k))).idxOf x) := by
    simp only [Graph.resolve, hx, ↓reduceIte]
  rw [V₂, hr, subst_fwd h₂, subst_fwd hW, h₁]
  simp only [Graph.plugSrc, hl, Option.getD_some]

/-- An export of an instance of the socket, on the positional side, before any instance. -/
theorem V₂_out (P : Nat → Comp M) (g₁ g₂ : Graph) (j : Nat) (q : String) :
    V₂ P (fun k => sigOf (P k)) g₁ g₂ (.out j q) = .trap := by
  simp only [V₂, Graph.resolve, Nat.not_lt_zero, false_and, ↓reduceIte]
  split <;> rfl

theorem inv_start {P : Nat → Comp M} {g₁ g₂ : Graph} (ho : g₁.ExportsOut)
    (hc : Covers (fun k => sigOf (P k)) g₁ g₂) (hw : g₁.WF fun k => sigOf (P k)) :
    Inv (names (g₂.iface fun k => sigOf (P k))) g₁.nodes.length g₁.plugSrc
      (V₂ P (fun k => sigOf (P k)) g₁ g₂) (run₁ P (fun k => sigOf (P k)) g₁).1 := by
  refine ⟨fun x hx => V₂_imp ho hc hw hx, fun j q => ?_⟩
  rw [V₂_out, run₁, gRun_above P g₁.nodes _ _ 0 (j + g₁.nodes.length) q (by omega)]
  rfl

/-- The two runs of the socket's instances. -/
theorem runs_sim {P : Nat → Comp M} {g₁ g₂ : Graph} (ho : g₁.ExportsOut)
    (hc : Covers (fun k => sigOf (P k)) g₁ g₂) (hw : g₁.WF fun k => sigOf (P k)) :
    (run₂' P (fun k => sigOf (P k)) g₁ g₂).2 = (run₂ P (fun k => sigOf (P k)) g₁ g₂).2 ∧
      Inv (names (g₂.iface fun k => sigOf (P k))) g₁.nodes.length g₁.plugSrc
        (run₂' P (fun k => sigOf (P k)) g₁ g₂).1 (run₂ P (fun k => sigOf (P k)) g₁ g₂).1 :=
  gRun_sim P g₁.plugSrc (fun _ _ => rfl) (fun _ hx => plugSrc_imp_out ho hc hw hx) g₂.nodes 0
    _ _ _ (fun _ hn _ hp _ hs => mem_iface_of_src (fun k => sigOf (P k)) g₂ hn hp hs)
    (inv_start ho hc hw)

/-- **`wac plug` of arbitrary graphs is positional plugging after re-reading the socket's
imports by name.** No hypothesis on the socket's well-formedness or on export names is
needed. -/
theorem seq_graph_equiv (C : CoreSem M) (P : Nat → Comp M) (g₁ g₂ : Graph)
    (ho : g₁.ExportsOut) (hc : Covers (fun k => sigOf (P k)) g₁ g₂)
    (hw : g₁.WF fun k => sigOf (P k)) :
    CompEquiv C (select (List.range g₂.exports.length) ((g₁.seq (fun k => sigOf (P k)) g₂).toComp P))
      (seq (g₁.toComp P)
        (reimport (exportIface (g₁.toComp P))
          (byName (exportIface (g₁.toComp P)) (g₂.toComp P).imports) (g₂.toComp P))) := by
  obtain ⟨li, ln, lx⟩ := flat_lhs P g₁ g₂ (iface_seq ho hc hw)
  obtain ⟨ri, rn, rx⟩ := flat_rhs P g₁ g₂
  obtain ⟨hn, hI⟩ := runs_sim ho hc hw
  have hx : g₂.exports.map (fun e => (run₂ P (fun k => sigOf (P k)) g₁ g₂).1 (g₁.plugSrc e.2)) =
      g₂.exports.map fun e => (run₂' P (fun k => sigOf (P k)) g₁ g₂).1 e.2 := by
    refine List.map_congr_left fun e he => ?_
    cases hs : e.2 with
    | imp x => exact (hI.1 x (mem_iface_of_export _ g₂ he hs)).symm
    | out j q => exact (hI.2 j q).symm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← imports_flatten, li, ← imports_flatten, ri]
  · have h₁ := congrArg List.length lx
    have h₂ := congrArg List.length rx
    simp only [List.length_map] at h₁ h₂
    rw [← exports_length_flatten, ← exports_length_flatten, h₁, h₂]
  · rw [← denU_flatten' C, ← denU_flatten' C]
    refine linked_denU_congr C (by rw [li, ri]) (by rw [ln, rn, congrArg Prod.snd hn]) (by rw [lx, rx, hx])

end Silmaril.Wasm.Component.Algebra.SeqGraphProof
