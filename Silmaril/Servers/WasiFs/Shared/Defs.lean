module

public import Silmaril.Servers.WasiFs.Kv.Defs
public import Silmaril.Servers.State.SharedFs.Defs

@[expose] public section

/-!
# The file-backed `wasi:http` store over files that others change: state model (c)

See `docs/projects/http-servers.md` (section "State models"). The store component of
`Silmaril.Servers.WasiFs` run over a preopened directory that other writers may change
between handler runs (state model (c), `Silmaril.Servers.State.SharedFs`), as the
conformance harness does to the component served by `wasmtime serve`:

* `wasiShared root fs₀ E`: the component, on short requests, with the environment `E`;
* `safeNF root`: the safety specification: each response is `specStep`'s answer from some
  short files;
* `keyOn root K`: the files of the keys of `K` (targets in origin form);
* `kvOnNF K`: the key-value store on the keys of `K` (`SharedFs.kvOn`), on short requests, read
  on targets in origin form and without header fields.

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiFs

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.SharedFs
open Silmaril.Net.Http (Request Response Target Store storeStep)
open Silmaril.Cli (Fs FPath)

/-- **The store component over shared files**, on short requests. -/
def wasiShared (root : String) (fs₀ : Fs) (E : Fs → Fs → Prop) : Server Request Response :=
  ⟨Fs, (storeHandler root).guard smallReq, E, fs₀⟩

/-- The safety specification: the answer of `specStep` from some short files. -/
def safeNF (root : String) : Atomic Unit Request Response :=
  Atomic.ofRel fun r resp => ∃ fs, Small fs ∧ resp = (specStep root fs r).1

/-- The files of the keys of `K`. -/
def keyOn (root : String) (K : Target → Prop) (p : FPath) : Prop :=
  ∃ t, K t ∧ originForm t = t ∧ keyFile root t = p

/-- **The key-value store on the keys of `K`**, read as `kvNF` reads `kv`. -/
def kvOnNF (K : Target → Prop) : Atomic Store Request Response :=
  ((kvOn K).guard smallReq).comap normReq noFields

end Silmaril.Servers.WasiFs
