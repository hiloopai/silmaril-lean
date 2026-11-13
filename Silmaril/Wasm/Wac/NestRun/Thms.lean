module

public import Silmaril.Wasm.Wac.NestRun.Defs
public import Silmaril.Proofs.Wasm.Wac.Nest.Run

/-!
# WAC: flattening a composition graph, node by node (theorems)

The interface of the run lemmas of `Silmaril.Proofs.Wasm.Wac.Nest.Run`, for use outside the
nesting proof (the proof of `Algebra.task_seq_graph` uses them):

* `flattenNodes_inst_run`: flattening a nested instance node;
* `flatten_mkNodes_run`: flattening the instances of a graph, below any wiring `σ`, is the
  run `gRun` from any valuation `V` that agrees with `σ` on the graph's references;
* `gRun_append_run`, `gRun_stable_run`: runs compose, and leave the valuation unchanged
  at the imports and below their first instance;
* `resolve_zero_subst_run`, `offset_zero_run`: the start of a run over the identity wiring.

The statements are those of `NestProof`; this module only restates them.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

theorem flattenNodes_inst_run (σ : List Impl) (eB : Nat) (c : Comp M) (args : List Impl)
    (ns : List (Node M)) :
    flattenNodes σ eB (.inst c args :: ns) =
      let rc := flattenNodes ((List.range c.imports.length).map fun i =>
        (args[i]?.getD .trap).subst σ) eB c.nodes
      let r := flattenNodes (σ ++ c.exports.map fun x => x.impl.subst rc.1) rc.2.1 ns
      (r.1, r.2.1, rc.2.2 ++ r.2.2) :=
  NestProof.flattenNodes_inst σ eB c args ns

/-- **Flattening the instances of a graph is a run over valuations.** -/
theorem flatten_mkNodes_run (P : Nat → Comp M) (g : Graph) (I : Iface)
    (ns : List Inst) (k : Nat) (σ : List Impl) (eB : Nat) (V : Src → Impl)
    (hd : g.nodes.drop k = ns) (hlen : σ.length = I.length + g.offset (fun k => sigOf (P k)) k)
    (hV : ∀ s, (g.resolve (fun k => sigOf (P k)) I k s).subst σ = V s) :
    (flattenNodes σ eB (g.mkNodes (fun k => sigOf (P k)) P I k ns)).2.1 =
        (gRun P V eB k ns).2.1 ∧
      (flattenNodes σ eB (g.mkNodes (fun k => sigOf (P k)) P I k ns)).2.2 =
        (gRun P V eB k ns).2.2 ∧
      ∀ s, (g.resolve (fun k => sigOf (P k)) I (k + ns.length) s).subst
        (flattenNodes σ eB (g.mkNodes (fun k => sigOf (P k)) P I k ns)).1 =
          (gRun P V eB k ns).1 s :=
  NestProof.flatten_mkNodes P g I ns k σ eB V hd hlen hV

theorem gRun_append_run (P : Nat → Comp M) (l₁ l₂ : List Inst) (V : Src → Impl) (eB k : Nat) :
    gRun P V eB k (l₁ ++ l₂) =
      let r₁ := gRun P V eB k l₁
      let r₂ := gRun P r₁.1 r₁.2.1 (k + l₁.length) l₂
      (r₂.1, r₂.2.1, r₁.2.2 ++ r₂.2.2) :=
  NestProof.gRun_append P l₁ l₂ V eB k

theorem gRun_stable_run (P : Nat → Comp M) (ns : List Inst) (V : Src → Impl) (eB k : Nat)
    (s : Src) (hs : ∀ t q, s = .out t q → t < k) : (gRun P V eB k ns).1 s = V s :=
  NestProof.gRun_stable P ns V eB k s hs

theorem resolve_zero_subst_run (S : Nat → PkgSig) (g : Graph) (I : Iface) (s : Src) :
    (g.resolve S I 0 s).subst ((List.range I.length).map Impl.fwd) = baseV I s :=
  NestProof.resolve_zero_subst S g I s

theorem offset_zero_run (S : Nat → PkgSig) (g : Graph) : g.offset S 0 = 0 :=
  NestProof.offset_zero S g

end Silmaril.Wasm.Wac
