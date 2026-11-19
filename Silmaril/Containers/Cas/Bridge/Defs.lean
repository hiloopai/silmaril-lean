module

public import Silmaril.Containers.Oci.Defs
public import Silmaril.Containers.Runtime.Defs

/-! # Experimental abstract, byte and checked OCI stores

`Oci.loadFrom` uses the existing OCI parser and size checks with a supplied fetch operation.
`loadBytes` avoids hashing. `load_checked_eq_bytes` requires a Lean integrity certificate;
an external verifier report alone is not such a certificate. Parsed abstract `Stores D C`
remain the cheapest route when byte-level OCI facts are irrelevant to an example. -/

@[expose] public section
namespace Silmaril.Containers.Oci

/-- Fetch byte contents without recomputing their digest. -/
def fetchBytes (store : Cas.Store Digest (List UInt8)) (d : Digest) :
    Except Refusal (List UInt8) :=
  match store d with
  | none => .error .missingBlob
  | some bs => .ok bs

/-- Same reader and size checks, with digest integrity left as a separate obligation. -/
def loadBytes (store : Cas.Store Digest (List UInt8)) (manifest : Digest) :
    Except Refusal (Flat (List UInt8)) := loadFrom (fetchBytes store) manifest

/-- A byte-store image runtime, with the program/machine semantics kept unchanged. -/
def runtimeBytes {P E : Type} (store : Cas.Store Digest (List UInt8))
    (runtime : Runtime (Flat (List UInt8)) P E) : Runtime Digest P E where
  load d := (loadBytes store d).bind runtime.load
  sem := runtime.sem
  obs := runtime.obs

end Silmaril.Containers.Oci
