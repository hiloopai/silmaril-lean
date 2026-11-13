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
  touches refines the component-state store, as in state model (b);
* **linearizability on the untouched keys**: when the environment may change the files of some
  keys (those outside `K`), the store is still linearizable with respect to `kvOn K`, the
  key-value store on the keys of `K` (`restrictKeys K`): requests on keys of `K` are atomic
  `storeStep`s of one store, and requests on other keys are answered as `storeStep` answers from
  some store and leave the keys of `K` alone.

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

/-- The store on the keys `K`: the other keys hold nothing. -/
def restrictKeys (K : Target → Prop) [DecidablePred K] (S : Store) : Store :=
  fun t => if K t then S t else none

/-- **The key-value store on the keys `K`**: a request on a key of `K` is a `storeStep`; a
request on another key is answered as `storeStep` answers it from some store, and leaves the
state alone. -/
def kvOn (K : Target → Prop) : Atomic Store Request Response := fun S r resp S' =>
  (K r.target → storeStep S r = (resp, S')) ∧
    (¬ K r.target → (∃ S₁ S₁', storeStep S₁ r = (resp, S₁')) ∧ S' = S)

end Silmaril.Servers.State.SharedFs
