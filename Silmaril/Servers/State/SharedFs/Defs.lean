module

public import Silmaril.Servers.State.OwnedFs.Defs

@[expose] public section

/-!
# State model (c): WASI over a file system that others may change

See `docs/projects/http-servers.md` (section "State models"). The servers of
`Silmaril.Servers.State.OwnedFs`, but the files are shared: between handler runs, the
environment `E : Fs → Fs → Prop` may change them (another process, an operator, a deploy).
The handler runs stay atomic with respect to the environment: a run reads and writes the files
as one step, as when each request reads or writes whole files that are replaced atomically
(`rename`). Interleaving the environment inside a handler run is not modelled.

* `sharedStatic loc fs₀ E`, `sharedStore enc fs₀ E`: the static file server and the
  file-backed store with environment `E`;
* `Untouched E P`: the environment never changes a file whose path satisfies `P`;
* `Keeps E I`: the environment preserves the file-system-state invariant `I`.

What is claimed (`SharedFs/Thms.lean`):

* **safety, whatever the environment**: each response of the static server is its answer
  with **some** files satisfying any invariant the environment keeps; each response of the
  store is a `storeStep` answer from some store;
* **functional correctness for untouched files**: a request whose file the environment never
  touches is answered as with the initial files; a store whose key files the environment never
  touches refines the component-state store, as in state model (b).

A Silmaril addition.
-/

namespace Silmaril.Servers.State.SharedFs

open Silmaril.Net.Http Silmaril.Cli Silmaril.Servers.State.OwnedFs

/-- **The static file server over shared files**. -/
def sharedStatic (loc : Target → Option FPath) (fs₀ : Fs) (E : Fs → Fs → Prop) :
    Server Request Response :=
  ⟨Fs, Atomic.ofFun (staticStep loc), E, fs₀⟩

/-- **The file-backed store over shared files**. -/
def sharedStore (enc : Target → FPath) (fs₀ : Fs) (E : Fs → Fs → Prop) :
    Server Request Response :=
  ⟨Fs, Atomic.ofFun (fileStoreStep enc), E, fs₀⟩

/-- The environment never changes the files whose paths satisfy `P`. -/
def Untouched (E : Fs → Fs → Prop) (P : FPath → Prop) : Prop :=
  ∀ s s', E s s' → ∀ p, P p → s' p = s p

/-- The environment preserves the invariant `I`. -/
def Keeps (E : Fs → Fs → Prop) (I : Fs → Prop) : Prop := ∀ s s', I s → E s s' → I s'

/-- The safety specification of the static server under the invariant `I`: some files
satisfying `I` give the answer. -/
def staticSafe (loc : Target → Option FPath) (I : Fs → Prop) : Atomic Unit Request Response :=
  Atomic.ofRel fun r resp => ∃ fs, I fs ∧ resp = staticAnswer loc fs r

/-- The safety specification of the store: some store gives the answer. -/
def storeSafe : Atomic Unit Request Response :=
  Atomic.ofRel fun r resp => ∃ S S', storeStep S r = (resp, S')

end Silmaril.Servers.State.SharedFs
