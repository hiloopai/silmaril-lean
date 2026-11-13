module

public import Silmaril.Wasm.Component.IR.Defs

/-!
# Flattening nested components: the transformation

`flatten : Comp M → Linked M` inlines every nested component instance into its
parent, recursively, producing the flat IR. It walks the nodes keeping

* `σ : List Impl`: for each function of the *source* environment (the imports
  and the exports of the nodes so far, at the current nesting level), its
  implementation over the *flat* environment;
* `eB`: the size of the flat environment.

A core instance is kept, with its wiring substituted by `σ`; its exports are
appended to both environments. A nested instance `inst c args` is replaced by
the flattened nodes of `c`, where the imports of `c` are implemented by its
`args` substituted by `σ`; its exports become the exports of `c`, substituted
by the final environment of `c`. Substitution concatenates adapter chains
(`Impl.subst`): the `canon lower` of a consumer component and the `canon lift`
of a provider become adjacent, ready for adapter fusion. Known constant
answers supplied by a parent (`Target.const`) are propagated into the child:
cross-component specialisation.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- Flatten a list of nodes: returns the final `σ`, the final flat environment
size and the new flat nodes. -/
def flattenNodes : List Impl → Nat → List (Node M) → List Impl × Nat × List (M × List Impl)
  | σ, eB, [] => (σ, eB, [])
  | σ, eB, .core m args :: ns =>
    let w := (CoreModule.exports m).length
    let r := flattenNodes (σ ++ (List.range w).map fun i => Impl.fwd (eB + i)) (eB + w) ns
    (r.1, r.2.1, (m, args.map (Impl.subst σ)) :: r.2.2)
  | σ, eB, .inst (.mk I ns' xs') args :: ns =>
    let σc := (List.range I.length).map fun i => (args[i]?.getD Impl.trap).subst σ
    let rc := flattenNodes σc eB ns'
    let r := flattenNodes (σ ++ xs'.map fun x => x.impl.subst rc.1) rc.2.1 ns
    (r.1, r.2.1, rc.2.2 ++ r.2.2)

/-- Flatten a component. -/
def flatten (c : Comp M) : Linked M :=
  match c with
  | .mk I ns xs =>
    let r := flattenNodes ((List.range I.length).map Impl.fwd) I.length ns
    ⟨I, r.2.2, xs.map fun x => { x with impl := x.impl.subst r.1 }⟩

/-- **Specialisation by a known handler**: the imports of `c` are implemented by
the wiring programs `σ₀` over new imports `J` (for example `Target.const`
answers, or adapters and renamings of host functions); `specialise J σ₀ c`
composes them in statically, substituting them into every wiring program
(and flattening `c`). -/
def specialise (J : Iface) (σ₀ : List Impl) (c : Comp M) : Linked M :=
  match c with
  | .mk _ ns xs =>
    let r := flattenNodes σ₀ J.length ns
    ⟨J, r.2.2, xs.map fun x => { x with impl := x.impl.subst r.1 }⟩

end Silmaril.Wasm.Component
