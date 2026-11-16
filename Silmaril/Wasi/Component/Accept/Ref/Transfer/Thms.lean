module

public import Silmaril.Wasi.Component.Accept.Ref.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Transfer.Defs
import Silmaril.Proofs.Wasi.Component.Accept.RefTransfer

/-! # Acceptance across engines with the same static part

`accepted_of_withStore`: for a store simulation `S : E.StoreSim I`, a byte string accepted on
REF over `E.withStore I` is accepted on REF over `E`, **provided** that

* the acceptor's dispatchers over the two engines are related (`DispatchRel S`), and
* the linked instantiation programs `acceptLinkedProg c` over the two engines are related
  (`ProgRel S`).

The proof is the machine simulation `Machine.Transfer.steps_sim`, applied to the instantiation
run and to the environment's run. Neither hypothesis is proved here for any engine, so no
unconditional acceptance over `E` follows yet from a run over `E.withStore I` (for example
`Ref.KMem.Examples.acceptedK_hi`, over `core3K neverFail`). Discharging them means relating
every REF program that `acceptLinkedProg` and `Canon.dispatch` can reach
(`docs/projects/wasm-memrep.md`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Machine.Transfer

variable {E : CoreEngine} {I : E.StoreImpl}

/-- **Acceptance over `E.withStore I` is acceptance over `E`**, given related dispatchers and
related instantiation programs. -/
theorem accepted_of_withStore [∀ a b, Decidable (E.ExternSub a b)] (S : E.StoreSim I)
    {prof : ProfileKind} {c : Syntax.Component E.Module} {w : List UInt8}
    (hd : DispatchRel S (dispatch (E := E.withStore I)) (dispatch (E := E)))
    (hp : ProgRel S (acceptLinkedProg (E := E.withStore I) c) (acceptLinkedProg (E := E) c))
    (h : Accepted (E := E.withStore I) prof c w) : Accepted (E := E) prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.RefTransfer.accepted_of_withStore S hd hp h

end Silmaril.Wasi.Accept.Ref
