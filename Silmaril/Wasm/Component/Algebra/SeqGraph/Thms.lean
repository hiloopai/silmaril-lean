module

public import Silmaril.Wasm.Component.Algebra.SeqGraph.Defs
public import Silmaril.Proofs.Wasm.Component.Algebra.SeqGraph.Equiv

/-!
# Plugging arbitrary composition graphs: `SeqGraphLaw` is proved

* **`seq_graph`**: `wac plug` (`Graph.seq`) of an arbitrary plug graph `g₁` into an arbitrary
  socket graph `g₂`, keeping the socket's exports, is equivalent (for every core semantics `C`)
  to the positional plug `seq` of the two compositions after re-reading the socket's imports by
  name (`reimport … (byName …)`). Hypotheses: the plug's exports are exports of its instances
  (`ExportsOut`), every import of the socket is exported by the plug (`Covers`), and the plug is
  well formed. The socket's well-formedness and distinct export names, which the frozen
  statement also assumes, are not needed.
* **`task_seq_graph : SeqGraphLaw`**: the frozen open target , proved.

The proof (`Silmaril.Proofs.Wasm.Component.Algebra.SeqGraph`) does not go through nesting, as the
sketch in `SeqGraph.Defs` proposed. Both sides are flattened (`Passes.Flatten`, which keeps
the meaning, `denU_flatten'`); flattening a graph is a run over valuations
(`Wac.flatten_mkNodes_run`). The plug's instances give the same run on both sides; the socket's
instances, nested inside `reimport` on the right and plugged by `Graph.plugSrc` on the left,
give runs related by a simulation (`SeqGraphProof.gRun_sim`: an import `x` of the socket on the
right is the plug's export `x` on the left, the export `q` of socket instance `j` is the export
`q` of instance `j + m`); and the kept exports are the socket's on both sides. So the two flat
components have equal imports, nodes and export wiring.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Wasm.Component Silmaril.Wasm.Wac

variable {M : Type} [CoreModule M]

/-- **`wac plug` of arbitrary graphs is positional plugging after re-reading the socket's
imports by name.** -/
theorem seq_graph (C : CoreSem M) (P : Nat → Comp M) (g₁ g₂ : Graph)
    (ho : g₁.ExportsOut) (hc : Covers (fun k => sigOf (P k)) g₁ g₂)
    (hw : g₁.WF fun k => sigOf (P k)) :
    CompEquiv C (select (List.range g₂.exports.length) ((g₁.seq (fun k => sigOf (P k)) g₂).toComp P))
      (seq (g₁.toComp P)
        (reimport (exportIface (g₁.toComp P))
          (byName (exportIface (g₁.toComp P)) (g₂.toComp P).imports) (g₂.toComp P))) :=
  SeqGraphProof.seq_graph_equiv C P g₁ g₂ ho hc hw

/-- **The frozen target `SeqGraphLaw` holds.** -/
theorem task_seq_graph : SeqGraphLaw := by
  intro M _ C P g₁ g₂ S ho hc hw _ _ _
  exact seq_graph C P g₁ g₂ ho hc hw

end Silmaril.Wasm.Component.Algebra
