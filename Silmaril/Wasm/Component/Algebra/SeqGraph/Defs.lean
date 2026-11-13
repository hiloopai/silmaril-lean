module

public import Silmaril.Wasm.Component.Algebra.Plug.Defs
public import Silmaril.Wasm.Component.Algebra.Equiv.Defs
public import Silmaril.Wasm.Wac.Seq.Defs
public import Silmaril.Wasm.Wac.Nest.Defs

/-!
# Plugging arbitrary composition graphs: the statement

`Algebra.plug_equiv_seq` proves that `wac plug` (`Wac.Graph.seq`) of **two package graphs**
agrees with the positional `seq` after re-reading the socket's imports by name. This module
states the same agreement for **arbitrary** graphs `g₁` (the plug) and `g₂` (the socket):
`SeqGraphLaw`. It is **proved**: `Algebra.task_seq_graph`, from `Algebra.seq_graph`
(`Silmaril.Wasm.Component.Algebra.SeqGraph.Thms`), which needs weaker hypotheses (the socket
need not be well formed, and neither graph needs distinct export names).

The hypotheses of the statement are those under which the two sides have the same imports
(`g₁.iface`):

* `g₁.ExportsOut`: the plug's exports are exports of its instances (no import is re-exported,
  so `Graph.seq` introduces no new uses of imports);
* `Covers`: every import of the socket is exported by the plug;
* both graphs are well formed (`Graph.WF`: every reference resolves), and the export names of
  each graph are distinct (`List.lookup` takes the first export of a name).

The proof does not go through nesting (the route once sketched here, by `NestOk` and
`Wac.nest_inline_toComp`). Both sides are flattened (`Passes.Flatten`), flattening a graph is a
run over valuations (`Wac.flatten_mkNodes_run`), and the socket's run nested in `reimport` is
simulated by its run as instances plugged after the plug's (`gRun_sim` in
`Silmaril.Proofs.Wasm.Component.Algebra.SeqGraph`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Wasm.Component Silmaril.Wasm.Wac

/-- Every import of the socket `g₂` is exported by the plug `g₁`. -/
def Covers (S : Nat → PkgSig) (g₁ g₂ : Graph) : Prop :=
  ∀ p ∈ g₂.iface S, p.1 ∈ g₁.exports.map Prod.fst

/-- **`wac plug` of arbitrary graphs is positional plugging after re-reading the socket's
imports by name** (proved: `Algebra.task_seq_graph`). -/
def SeqGraphLaw : Prop :=
  ∀ {M : Type} [CoreModule M] (C : CoreSem M) (P : Nat → Comp M) (g₁ g₂ : Graph),
    let S := fun k => sigOf (P k)
    g₁.ExportsOut → Covers S g₁ g₂ → g₁.WF S → g₂.WF S →
      (g₁.exports.map Prod.fst).Nodup → (g₂.exports.map Prod.fst).Nodup →
      CompEquiv C (select (List.range g₂.exports.length) ((g₁.seq S g₂).toComp P))
        (seq (g₁.toComp P)
          (reimport (exportIface (g₁.toComp P))
            (byName (exportIface (g₁.toComp P)) (g₂.toComp P).imports) (g₂.toComp P)))

end Silmaril.Wasm.Component.Algebra
