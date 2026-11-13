module

public import Silmaril.Wasi.Versions.Net.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# Forwarding with translated answers, for gated theories

`Silmaril.Wasi.Versions.WitImport.Fwd` forwards each call to the function of the other version
with the same name and returns its answer unchanged; it is correct for the WIT typing when the
two signatures name no type. Most WASI functions name an `error-code`, a `descriptor-type` or
another enum whose cases differ between 0.2 and 0.3 (`WitImport.FwdNamed`), so their answers have
to be **translated**, and their behaviour is stated by gated theories (`Net.gated`), not by the
typing.

`fwdT X I tgt hto tr` is the stateless component that exports `X`, imports `I`, forwards each call
of `f` to `tgt f` with the same arguments and returns `tr f r` for the answer `r`.
`Silmaril.Wasi.Versions.FwdT.Thms.fwdT_model`: if a relation `R` between the states of the import
theory `gated iT nT okT` and the export theory `gated iG nG okG` holds initially and every
checked import answer gives a checked translated export answer, with the next states related,
then over every host of the import theory the forwarder is a model of the export theory.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-- **The translating forwarder.** -/
def fwdT (X I : Set FnName) (tgt : FnName → FnName) (hto : ∀ f ∈ X, tgt f ∈ I)
    (tr : FnName → Option (List Val) → Option (List Val)) : SBody Unit I X := fun _ q =>
  .call (⟨tgt q.1.1, hto q.1.1 q.1.2⟩, q.2) fun r => .pure ((), tr q.1.1 r)

/-- **A simulation for the translating forwarder** between two gated theories. -/
structure FwdSim {ST SG : Type} (X : Set FnName) (tgt : FnName → FnName)
    (tr : FnName → Option (List Val) → Option (List Val))
    (iT : ST) (nT : ST → WEv → ST) (okT : ST → WEv → Bool)
    (iG : SG) (nG : SG → WEv → SG) (okG : SG → WEv → Bool) (R : ST → SG → Prop) : Prop where
  init : R iT iG
  step : ∀ qT qG f a r, f ∈ X → R qT qG → okT qT (.imp (tgt f) a r) = true →
    okG qG (.imp f a (tr f r)) = true ∧ R (nT qT (.imp (tgt f) a r)) (nG qG (.imp f a (tr f r)))

end Silmaril.Wasi.Versions
