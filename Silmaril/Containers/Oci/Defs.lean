module

public import Silmaril.Containers.Image.Defs
public import Silmaril.Containers.Behaviour.Defs
public import Silmaril.Crypto.SHA256.Defs
public import Silmaril.Formats.Tar.Defs
public import Silmaril.Formats.Json.RfcParser

/-!
# A restricted OCI image reader, with checked digests

**Experimental API** (`docs/projects/containers.md`): definitions and statements may change.

`Oci.load L d` reads an image from an OCI image layout's blobs (`Layout`) starting at the digest
`d` of its manifest, into a flat image (`Silmaril.Containers.Flat`) whose files hold octets. It
accepts **one profile** and refuses everything else (`Refusal.other` for an unsupported format,
`missingBlob`, `badDigest`); it is not a general OCI implementation.

**Integrity.** Every blob is fetched by its SHA-256 digest and checked (`Layout.fetch`): a blob
whose hash is not its digest is refused (`badDigest`), never used. `Thms.fetch_eq_checked` relates
this to the checked content store of `Silmaril.Containers.Cas` (`Store.checked Crypto.sha256`). A
descriptor's `size` must equal the blob's length. Collision resistance of SHA-256 is not assumed
by the reader; it is what makes the digest of the manifest name one image (`Cas.Store.InjOn`).

**The profile.**

* JSON documents: ASCII only, read by the existing RFC 8259 reader `Silmaril.Formats.RfcJson.value?`
  with no trailing input and no duplicate member names at any depth (checked by `fold`, which also
  turns the reader's syntax into the plain tree `J`); anything else is refused.
* Manifest: `schemaVersion` 2, `mediaType` `application/vnd.oci.image.manifest.v1+json`, a config
  descriptor of media type `application/vnd.oci.image.config.v1+json`, and layers of media type
  `application/vnd.oci.image.layer.v1.tar` only (uncompressed). Compressed layers (gzip, zstd),
  foreign layers and image indexes are refused.
* Configuration: `architecture` `amd64`, `os` `linux`, a non-empty `config.Entrypoint`, an optional
  `config.Cmd` and `config.Env` (`KEY=VALUE` strings), and optional `config.ExposedPorts`
  (members `N/tcp` or `N/udp` with value `{}`, read as the configuration's declared ports).
  Other configuration fields are not read; claims over images read this way quantify over every
  launch the process semantics admits (`Silmaril.Containers.Lps`), so they do not depend on them.
* Layers: decoded by `Silmaril.Formats.Tar.decode`; only regular files and directories are
  accepted; links, devices, FIFOs, PAX headers and whiteouts (`.wh.` names) are refused. Layers
  apply lowest first (`Tree.applyAll`).

The image index (`index.json`) and `oci-layout` files are not read: the reader starts from a
manifest digest, as a runtime does after resolving a reference.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Oci

open Silmaril.Containers Silmaril.Formats

/-- A SHA-256 digest, as its 32 octets. -/
abbrev Digest : Type := List UInt8

/-- **An OCI image layout's blobs**, by the digest they are stored under (their file names). -/
structure Layout where
  blobs : List (Digest × List UInt8)

/-- The raw store: the blob stored under a digest, unchecked. -/
def Layout.raw (L : Layout) : Cas.Store Digest (List UInt8) :=
  fun d => (L.blobs.find? (·.1 == d)).map (·.2)

/-- **Fetch a blob and check its digest.** -/
def Layout.fetch (L : Layout) (d : Digest) : Except Refusal (List UInt8) :=
  match L.raw d with
  | none => .error .missingBlob
  | some bs => if Silmaril.Crypto.sha256 bs = d then .ok bs else .error .badDigest

/-- Refusal of an unsupported format. -/
abbrev unsupported {α : Type} : Except Refusal α := .error .other

/-- Lift an option, refusing `none` as unsupported. -/
def req {α : Type} : Option α → Except Refusal α
  | some a => .ok a
  | none => unsupported

/-! ## JSON -/

/-- **A JSON value**, as a plain tree: scalars as the RFC reader decodes them, arrays, and
objects with their members in order. -/
inductive J where
  | scalar (s : Silmaril.Formats.RfcJsonScalar)
  | arr (xs : List J)
  | obj (es : List (String × J))

/-- What the fold returns at each sort of the reader's syntax, with whether member names are
distinct so far. -/
abbrev Fold : Silmaril.Formats.JsonIx → Type
  | .val => J × Bool
  | .arr => List J × Bool
  | .obj => List (String × J) × Bool

/-- The fold, compiled (used for evaluation only). -/
def foldC : {i : Silmaril.Formats.JsonIx} →
    Silmaril.Formats.RawSyn String Silmaril.Formats.RfcJsonScalar i → Fold i
  | _, .scalar s => (.scalar s, true)
  | _, .list xs => let r := foldC xs; (.arr r.1, r.2)
  | _, .map es => let r := foldC es; (.obj r.1, r.2)
  | _, .nil => ([], true)
  | _, .cons v vs => let a := foldC v; let b := foldC vs; (a.1 :: b.1, a.2 && b.2)
  | _, .objNil => ([], true)
  | _, .objCons k v vs =>
    let a := foldC v; let b := foldC vs
    ((k, a.1) :: b.1, !(b.1.any (·.1 == k)) && a.2 && b.2)

/-- **The fold of the reader's syntax into `J`**, checking that member names are distinct at
every depth. Defined with the recursor so that the kernel evaluates it (a `match` over the indexed
syntax would not reduce); `foldC` is the same function for compiled evaluation. -/
@[implemented_by foldC]
def fold {i : Silmaril.Formats.JsonIx}
    (t : Silmaril.Formats.RawSyn String Silmaril.Formats.RfcJsonScalar i) : Fold i :=
  Silmaril.Formats.RawSyn.rec (motive := fun i _ => Fold i)
    (fun s => (.scalar s, true))
    (fun _ ih => (.arr ih.1, ih.2))
    (fun _ ih => (.obj ih.1, ih.2))
    ([], true)
    (fun _ _ ihv ihs => (ihv.1 :: ihs.1, ihv.2 && ihs.2))
    ([], true)
    (fun k _ _ ihv ihs => ((k, ihv.1) :: ihs.1, !(ihs.1.any (·.1 == k)) && ihv.2 && ihs.2))
    t

/-- **A JSON document of the profile**: ASCII, accepted by the RFC reader, nothing after it, no
duplicate member names. -/
def jsonOf (bs : List UInt8) : Except Refusal J :=
  if bs.all (· < 128) then
    let cs := bs.map fun b => Char.ofNat b.toNat
    match Silmaril.Formats.RfcJson.value? (cs.length + 1) cs with
    | some (j, rest) =>
      let r := fold j
      if (Silmaril.Formats.RfcJson.ws rest).isEmpty && r.2 then .ok r.1 else unsupported
    | none => unsupported
  else unsupported

/-- A member of an object. -/
def J.member? (j : J) (k : String) : Option J :=
  match j with
  | .obj es => (es.find? (·.1 == k)).map (·.2)
  | _ => none

def J.str? : J → Option String
  | .scalar (some (.string s)) => some s
  | _ => none

/-- A non-negative integer literal (decimal digits only). -/
def natOf? (s : String) : Option Nat :=
  let cs := s.toList
  if !cs.isEmpty && cs.all Char.isDigit then
    some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

def J.nat? : J → Option Nat
  | .scalar (some (.number s)) => natOf? s
  | _ => none

def J.arr? : J → Option (List J)
  | .arr xs => some xs
  | _ => none

def J.strs? (j : J) : Option (List String) := j.arr? >>= (·.mapM J.str?)

/-- An optional list of strings: absent is empty. -/
def J.optStrs? (j : J) (k : String) : Option (List String) :=
  match j.member? k with
  | none => some []
  | some v => v.strs?

/-! ## Digests and descriptors -/

/-- A lowercase hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

/-- Hex pairs to octets. -/
def hexBytes? : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigit? a
    let y ← hexDigit? b
    let tail ← hexBytes? rest
    pure ((x * 16 + y).toUInt8 :: tail)
  | [_] => none

/-- `sha256:` followed by 64 lowercase hexadecimal digits. -/
def digestOf? (s : String) : Option Digest :=
  match s.toList with
  | 's' :: 'h' :: 'a' :: '2' :: '5' :: '6' :: ':' :: hex =>
    if hex.length = 64 then hexBytes? hex else none
  | _ => none

/-- A descriptor of the given media type: its digest and size. -/
def descriptor (mediaType : String) (j : J) : Except Refusal (Digest × Nat) := do
  let mt ← req (j.member? "mediaType" >>= J.str?)
  if mt ≠ mediaType then unsupported else
  let d ← req (j.member? "digest" >>= J.str? >>= digestOf?)
  let n ← req (j.member? "size" >>= J.nat?)
  pure (d, n)

/-- Fetch the blob of a descriptor, checking digest and size. -/
def Layout.fetchSized (L : Layout) (d : Digest × Nat) : Except Refusal (List UInt8) := do
  let bs ← L.fetch d.1
  if bs.length = d.2 then pure bs else .error .badDigest

def manifestMediaType : String := "application/vnd.oci.image.manifest.v1+json"
def configMediaType : String := "application/vnd.oci.image.config.v1+json"
def layerTarMediaType : String := "application/vnd.oci.image.layer.v1.tar"

/-- **A manifest of the profile**: the config descriptor and the layer descriptors. -/
def manifestOf (j : J) : Except Refusal ((Digest × Nat) × List (Digest × Nat)) := do
  if (j.member? "schemaVersion" >>= J.nat?) ≠ some 2 then unsupported else
  if (j.member? "mediaType" >>= J.str?) ≠ some manifestMediaType then unsupported else
  let cfg ← descriptor configMediaType (← req (j.member? "config"))
  let layers ← (← req (j.member? "layers" >>= J.arr?)).mapM (descriptor layerTarMediaType)
  pure (cfg, layers)

/-- `KEY=VALUE`. -/
def envPair? (s : String) : Option (String × String) :=
  match s.toList.span (· ≠ '=') with
  | (k, '=' :: v) => if k.isEmpty then none else some (String.ofList k, String.ofList v)
  | _ => none

/-- A declared port, `N/tcp` or `N/udp` with `N` a decimal below 65536 (the key of an
`ExposedPorts` member). The form without a protocol is outside the profile. -/
def portSpecOf? (s : String) : Option PortSpec :=
  match s.toList.span (· ≠ '/') with
  | (n, '/' :: p) =>
    match natOf? (String.ofList n) with
    | some v =>
      if v < 65536 then
        if p = ['t', 'c', 'p'] then some ⟨.tcp, v.toUInt16⟩
        else if p = ['u', 'd', 'p'] then some ⟨.udp, v.toUInt16⟩ else none
      else none
    | none => none
  | _ => none

/-- `config.ExposedPorts`: an object whose members are declared ports with the empty object as
value; absent is none. -/
def J.exposed? (c : J) : Option (List PortSpec) :=
  match c.member? "ExposedPorts" with
  | none => some []
  | some (.obj es) => es.mapM fun e => match e.2 with
    | .obj [] => portSpecOf? e.1
    | _ => none
  | some _ => none

/-- **A configuration of the profile.** -/
def configOf (j : J) : Except Refusal Config := do
  if (j.member? "architecture" >>= J.str?) ≠ some "amd64" then unsupported else
  if (j.member? "os" >>= J.str?) ≠ some "linux" then unsupported else
  let c ← req (j.member? "config")
  let entry ← req (c.member? "Entrypoint" >>= J.strs?)
  if entry.isEmpty then unsupported else
  let cmd ← req (c.optStrs? "Cmd")
  let env ← req ((c.optStrs? "Env").bind (·.mapM envPair?))
  let exposed ← req c.exposed?
  pure { entrypoint := entry, cmd, env, exposed }

/-! ## Layers -/

/-- A path component that is a whiteout. -/
def isWhiteout (c : String) : Bool := c.toList.take 4 == ['.', 'w', 'h', '.']

/-- **One tar entry of the profile**: a regular file or a directory, not a whiteout. -/
def entryOf (e : Tar.Entry) : Except Refusal (Path × Option (Entry (List UInt8))) :=
  let p := Path.ofString e.name
  if p.isEmpty || p.any isWhiteout then unsupported else
  match e.typeflag with
  | .regular => .ok (p, some (.file e.data (e.mode % 512 / 64 % 2 == 1)))
  | .directory => .ok (p, some .dir)
  | _ => unsupported

/-- **A layer of the profile**: an uncompressed tar archive. -/
def layerOf (bs : List UInt8) : Except Refusal (Layer (List UInt8)) := do
  let es ← req (Tar.decode bs)
  es.mapM entryOf

/-! ## Images -/

/-- **Read an image** from a layout, starting at the digest of its manifest. -/
def loadFrom (fetch : Digest → Except Refusal (List UInt8)) (manifest : Digest) :
    Except Refusal (Flat (List UInt8)) := do
  let fetchSizedFrom := fun d : Digest × Nat => do
    let bs ← fetch d.1
    if bs.length = d.2 then pure bs else .error .badDigest
  let m ← jsonOf (← fetch manifest)
  let (cfgD, layerDs) ← manifestOf m
  let cfg ← configOf (← jsonOf (← fetchSizedFrom cfgD))
  let layers ← layerDs.mapM fun d => do layerOf (← fetchSizedFrom d)
  pure ⟨cfg, Tree.empty.applyAll layers⟩

/-- The original checked reader, using exactly the original parser and size checks. -/
def load (L : Layout) (manifest : Digest) : Except Refusal (Flat (List UInt8)) :=
  loadFrom L.fetch manifest

end Silmaril.Containers.Oci
