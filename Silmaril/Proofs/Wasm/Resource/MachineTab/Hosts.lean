module

public import Silmaril.Proofs.Wasm.Resource.MachineTab.Dispatch
public import Silmaril.Wasm.Component.Reference.Sound.Defs

/-!
# Silmaril.Wasm.Component.Runtime.Table-moving hosts with host functions

`tabHost_none` covers the host without functions. This file covers the answering hosts of the
component soundness theorems (`Silmaril.Wasm.Component.Reference.answerImplS`,
`answerImpl`): a host function reads its arguments (`on_start`), reads and writes the host
state, and resolves (`on_resolve`) or traps. Its own program issues no store update; the
`on_start`/`on_resolve` calls are dispatcher calls, covered by `tabDispatch_canon`.

* `tabHost_ofFns`: a host given by host function programs is table-moving when they are;
* `tabHost_answerImplS`, `tabHost_answerImpl`: the answering hosts are table-moving, for every
  answering function and every handle table.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type} {j : InstId}

/-- A host given by host function programs is table-moving when they are. -/
theorem tabHost_ofFns {fns : HostFuncId → CallerId → P E σ (Ret E)}
    (h : ∀ fn c, TabProg j (fns fn c)) : TabHost j (HostImpl.ofFns fns) where
  funcs := h
  embedder _ _ _ _ := P.Inv.trap _
  threadBody _ _ _ := P.Inv.internal _
  buffer _ _ := P.Inv.internal _
  cancel _ _ := P.Inv.pure _

/-- **The stateful answering host is table-moving.** -/
theorem tabHost_answerImplS (g : σ → HostFuncId → List Val → Option (List Val × σ)) :
    TabHost j (Silmaril.Wasm.Component.Reference.answerImplS g : HostImpl E σ) :=
  tabHost_ofFns fun fn _ _ =>
    P.Inv.bind (P.Inv.callVals _) fun args =>
      P.Inv.bind P.Inv.hostGet fun s =>
        match g s fn args with
        | some (_, s') =>
          P.Inv.bind (P.Inv.hostSet s') fun _ =>
            P.Inv.bind (P.Inv.callUnit _) fun _ => P.Inv.pure _
        | none => P.Inv.trap _

/-- **The stateless answering host is table-moving.** -/
theorem tabHost_answerImpl (g : HostFuncId → List Val → Option (List Val)) :
    TabHost j (Silmaril.Wasm.Component.Reference.answerImpl g : HostImpl E σ) :=
  tabHost_answerImplS _

end Silmaril.Wasm.Resource
