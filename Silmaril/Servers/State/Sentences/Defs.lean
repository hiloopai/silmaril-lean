module

public import Silmaril.Servers.Core.Defs

/-!
# The state models' results as sentences of the server core

The state models (`Silmaril.Servers.State.{Component, OwnedFs, SharedFs}`) and the
file-backed `wasi:http` store (`Silmaril.Servers.WasiFs`) were proved with the state models'
own vocabulary: histories of `Ev.call` and `Ev.ret`, `Server.Sat`, `Server.Refines`,
Herlihy and Wing linearizability. `Silmaril.Servers.State.Sentences.Thms` restates each of
those results one by one in the server core (`Silmaril.Servers.Core`): about the core model
`Server.model M` (the histories read as core traces, one connection per request), as a
refinement of a core atomic-handler server (`Machine.server`), as satisfaction of a core
linearizability sentence (`Sen.lin`), or as satisfaction of a core atomic sentence
(`Sen.atomic`, `Sen.ofFun`).

The only new sentence is `Sen.distinct`: different requests are never answered the same (the
counter's property, which is not an atomic or a linearizability sentence).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers

/-- **Distinct answers**: responses to different requests are different. -/
def Sen.distinct {A : Sig} : Sen A :=
  fun t => ∀ i j a b, Event.send i a ∈ t → Event.send j b ∈ t → i ≠ j → a ≠ b

end Silmaril.Servers
