module

public import Silmaril.Servers.WasiBinaries.Defs
public import Silmaril.Servers.WasiExamples.Defs
public import Silmaril.Servers.WasiCore.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# The core module of `hello` runs the body `hello`

`hello_sim`: for every call `handle(r, o)`, the denotation of `helloCore` makes the import calls
of the body `hello`, with the same arguments, and after every typed answer continues as the body
does, up to the same result. Each step computes the next import call of the denotation in the
kernel (`kernel_rfl`), with the host's answers as variables; the proof splits the answers only
where the module reads them (the results of `outgoing-response.body` and `outgoing-body.write`,
read back by `$ok_handle`), so it has four paths.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiBinaries

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiCore
open Silmaril.Servers.WasiExamples Silmaril.Servers.WasiBinaries
open Silmaril.Wasm.Component (Val)

/-- The typed answers of `outgoing-response.body` and `outgoing-body.write`. -/
theorem ansTy_handleR {f : FnName} (hf : f = respBody ∨ f = bodyWrite) {n : Option (List Val)}
    (h : AnsTy f n) : (∃ x, n = some [okV (some (.u32 x))]) ∨ n = some [errV none] := by
  rcases hf with rfl | rfl <;>
    simpa [AnsTy, respBody, bodyWrite, newFields, newResp, reqHeaders, fieldsAppend, setStatus,
      reqConsume, inStream] using h

/-- **The core module of `hello` simulates the body `hello`** on typed answers. -/
theorem hello_sim (q : (nsig proxyWorld.exports).Op) :
    Sim AnsTy (coreBody helloCore binFuel q) (hello q) := by
  refine sim_step ?_ rfl fun n1 _ => ?_
  · kernel_rfl
  refine sim_step ?_ rfl fun n2 _ => ?_
  · kernel_rfl
  refine sim_step ?_ rfl fun n3 _ => ?_
  · kernel_rfl
  refine sim_step ?_ rfl fun n4 _ => ?_
  · kernel_rfl
  refine sim_step ?_ rfl fun n5 h5 => ?_
  · kernel_rfl
  rcases ansTy_handleR (.inl rfl) h5 with ⟨x5, rfl⟩ | rfl <;>
  · refine sim_step ?_ rfl fun n6 _ => ?_
    · kernel_rfl
    refine sim_step ?_ rfl fun n7 h7 => ?_
    · kernel_rfl
    rcases ansTy_handleR (.inr rfl) h7 with ⟨x7, rfl⟩ | rfl <;>
    · refine sim_step ?_ rfl fun n8 _ => ?_
      · kernel_rfl
      refine sim_step ?_ rfl fun n9 _ => ?_
      · kernel_rfl
      refine sim_step ?_ rfl fun n10 _ => ?_
      · kernel_rfl
      exact sim_pure (by kernel_rfl) rfl

end Silmaril.Proofs.Servers.WasiBinaries
