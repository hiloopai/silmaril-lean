module

public import Silmaril.Proofs.Wasm.LimeCompile.Select.Module

/-!
# Erasing `select` annotations: Core 3.0 behaviour is unchanged

Core 3.0's two `select` rules ignore the annotation, and this is proved to lift to whole runs,
for every profile `P` and every host that respects erasure (`HostResp`):

* `behavioursOf_eq`: configurations equal after erasure (`selC`) have the same behaviours,
  finite results and divergence (one simulation, `step_sim`, of a symmetric relation, by cases on
  every rule of `Step`);
* `behaviours_eq`: so do invocations in stores equal after erasure;
* `exportEquiv_selM`: a valid module and its erasure `selM m`, if also valid, are export
  equivalent under `Eq` (silmaril-lean's `ExportEquiv`: the instantiation run, then any session
  of export invocations sharing the store);
* `hostResp_closed`: the closed host respects erasure.

New statements over the proofs in `Silmaril.Proofs.Wasm.LimeCompile.Select`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Select

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (ExportEquiv closedHost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Configurations equal after erasure have the same behaviours.** -/
theorem behavioursOf_eq (hh : HostResp host) {c d : Config H} (hd : selC c = selC d) :
    behavioursOf P host c = behavioursOf P host d :=
  Silmaril.Proofs.Wasm.LimeCompile.Select.behavioursOf_eq hh hd

/-- **Stores equal after erasure have the same behaviours at every call.** -/
theorem behaviours_eq (hh : HostResp host) {s t : Store H} (h : selS s = selS t) (a : Nat)
    (vs : List Val) : behaviours P host s a vs = behaviours P host t a vs :=
  Silmaril.Proofs.Wasm.LimeCompile.Select.behaviours_eq hh h a vs

/-- **A module and its erasure are export equivalent** (both valid). -/
theorem exportEquiv_selM (hh : HostResp host) {m : Module} (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk (selM m) mt) : ExportEquiv (· = ·) P host m (selM m) :=
  Silmaril.Proofs.Wasm.LimeCompile.Select.exportEquiv_selM hh hm hm'

/-- The closed host (no host call returns or diverges) respects erasure. -/
theorem hostResp_closed : HostResp (closedHost (H := H)) :=
  fun _ _ _ _ _ _ h => h.elim

end Silmaril.Wasm.LimeCompile.Select
