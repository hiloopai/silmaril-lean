module

public import Silmaril.Wasm.Tools.Meta.Fast.Defs
public import Silmaril.Wasm.Tools.Meta.FastErr.Defs
public import Silmaril.Wasm.Tools.Meta.Metadata.Defs
public import Silmaril.Wasm.Tools.Meta.Demangle.Defs

/-!
# `demangle`, `metadata show` and `metadata add` over a `ByteArray`

The commands run these functions; the list functions of `Demangle.Defs` and `Metadata.Defs` are
their specifications. Each walks the binary with `parseBinaryB` (no copy of the input), turns
into lists only the custom sections the command reads (`name`, `component-name`, `producers`,
the OCI fields, `.dep-v0`), and copies every other section from the input array into the output
array (`pushRawSec`).

`Silmaril.Wasm.Tools.Meta.FastCmd.Thms` proves the walk they share equal to the list walk
(`parseBinaryB_spec`), `demangleB` equal to `demangle` (`demangleB_spec`), and so are `payloadOfB` and `addMetadataB` to
`payloadOf` and `addMetadata` (`payloadOfB_spec`, `addMetadataB_spec`); error messages are tested
(`tools/wasm-tools/tests/meta-differential.sh`, `meta-malformed.sh`). Framing errors are
rendered with wasmparser's offset (`FErr.render`), and the first error in stream order is found
with the commands' hooks (`firstErr`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

open Silmaril.Wasm.Tools.Meta.Metadata Silmaril.Wasm.Tools.Meta.Demangle

/-- The custom sections whose contents `readCustom` looks at. -/
def metaNames : List String :=
  ["name", "component-name", "producers", "authors", "description", "revision", "version",
   "licenses", "source", "homepage", ".dep-v0"]

/-- The error to report when the walk fails with `e`: the first error in stream order of the
walk with the consumer's checks `hk` (upstream consumes each payload before reading the next). -/
def firstErr (ba : ByteArray) (hk : Hook) (e : FErr) : String :=
  match parseBinaryHB ba hk with
  | .error e' => e'.render
  | .ok _ => e.render

namespace Metadata

/-- `readCustom` on a custom section `[a, b)` of `ba` (its name already read: `[ns, ne)`); only
the data of a section `readCustom` looks at is copied into a list. -/
def readCustomB (ba : ByteArray) (m : Meta) (ns ne b : Nat) : Except String Meta :=
  let nm := sl ba ns ne
  if strOf nm ∈ metaNames then readCustom m nm (sl ba ne b) else .ok m

/-- The first error of `readCustom` on a section, with wasmparser's offset where it has one
(`Chk`); `ok` when it reads. -/
def customErrB (ba : ByteArray) (ns ne b : Nat) : Except FErr Unit :=
  let nm := sl ba ns ne
  let n := strOf nm
  if n == "name" then Chk.scanNames ba ne b
  else if n == "component-name" then Chk.scanCompNames ba ne b
  else if n == "producers" then
    if (rdU32 ba b ne).toBool then Chk.producers ba ne b else .ok ()
  else if n ∈ metaNames then
    match readCustom {} nm (sl ba ne b) with
    | .error e => .error (FErr.plain e)
    | .ok _ => .ok ()
  else .ok ()

/-- The message of an error of `readCustomB`: the offset-aware one if the checker finds it. -/
def customMsg (ba : ByteArray) (ns ne b : Nat) (e : String) : String :=
  match customErrB ba ns ne b with
  | .error e' => e'.render
  | .ok () => e

/-- The hook of `metadata show`: `readCustom`'s errors in stream order. -/
def showHook (ba : ByteArray) : Hook := fun _ a b => do
  let (ns, ne) ← customOfB ba a b
  customErrB ba ns ne b

mutual
/-- `walkItems` over the input array. -/
def walkItemsB (ba : ByteArray) (m : Meta) : List ItemB → Except String (Meta × List Payload)
  | [] => .ok (m, [])
  | .sec s :: is => do
    let m ← if s.id == 0 then
        match customOfB ba s.bodyAt s.bodyEnd with
        | .ok (ns, ne) =>
          match readCustomB ba m ns ne s.bodyEnd with
          | .ok m => pure m
          | .error e => throw (customMsg ba ns ne s.bodyEnd e)
        | .error e => throw e.render
      else pure m
    walkItemsB ba m is
  | .nest _ _ a b enc items :: is => do
    let p ← walkUnitB ba a b enc items
    let (m, cs) ← walkItemsB ba m is
    pure (m, p :: cs)
/-- `walkUnit` over the input array. -/
def walkUnitB (ba : ByteArray) (a b : Nat) (enc : Enc) (items : List ItemB) : Except String Payload := do
  let (m, cs) ← walkItemsB ba { range := (a, b) } items
  match enc with
  | .module => pure (.module m)
  | .component => pure (.component m cs)
end

/-- **`Payload::from_binary`** over a `ByteArray`. -/
def payloadOfB (ba : ByteArray) : Except String Payload :=
  match parseBinaryB ba with
  | .error e => .error (firstErr ba (showHook ba) e)
  | .ok (enc, items) => walkUnitB ba 0 ba.size enc items

/-- `rawItems` of a nested unit, appended to `out`. -/
def pushRawItems (ba : ByteArray) (out : ByteArray) : List ItemB → ByteArray
  | [] => out
  | .sec s :: is => pushRawItems ba (pushRawSec out s.id ba s.bodyAt s.bodyEnd) is
  | .nest id _ _ _ enc items :: is =>
    let inner := pushRawItems ba (appendList ByteArray.empty enc.header) items
    let out := appendList (out.push id) (encU32 inner.size) ++ inner
    pushRawItems ba out is

/-- The state of the fast `rewrite_wasm` walk. -/
structure AddStB where
  out : ByteArray
  producersFound : Bool := false
  namesFound : Bool := false

/-- The custom sections `addSec` rewrites (or drops). -/
def addNames : List String :=
  ["producers", "name", "component-name", "authors", "description", "licenses", "source",
   "homepage", "revision", "version"]

/-- The first error of `addSec` on a custom section, with wasmparser's offset where it has
one; `ok` when it reads. -/
def addErrB (ba : ByteArray) (ns ne b : Nat) : Except FErr Unit :=
  let n := strOf (sl ba ns ne)
  if n == "name" then do Chk.scanNames ba ne b; Chk.decodeNames ba ne b
  else if n == "component-name" then do Chk.scanCompNames ba ne b; Chk.decodeCompNames ba ne b
  else if n == "producers" then
    if (rdU32 ba b ne).toBool then Chk.producers ba ne b else .ok ()
  else .ok ()

/-- The message of an error of `addSec`. -/
def addMsg (ba : ByteArray) (ns ne b : Nat) (e : String) : String :=
  match addErrB ba ns ne b with
  | .error e' => e'.render
  | .ok () => e

/-- One outer section of `rewrite_wasm` over the input array. -/
def addSecB (a : Add) (comp : Bool) (ba : ByteArray) (st : AddStB) (s : SecB) : Except String AddStB := do
  if s.id != 0 then return { st with out := pushRawSec st.out s.id ba s.bodyAt s.bodyEnd }
  let (ns, ne) ← match customOfB ba s.bodyAt s.bodyEnd with
    | .ok r => pure r
    | .error e => throw e.render
  if strOf (sl ba ns ne) ∉ addNames then
    return { st with out := pushRawSec st.out s.id ba s.bodyAt s.bodyEnd }
  let r ← match addSec a comp {} (s.toSec ba) with
    | .ok r => pure r
    | .error e => throw (addMsg ba ns ne s.bodyEnd e)
  pure { out := appendList st.out r.out.reverse.flatten,
         producersFound := st.producersFound || r.producersFound,
         namesFound := st.namesFound || r.namesFound }

/-- The hook of `metadata add`: `addSec`'s errors on the outer unit's custom sections, in stream
order (the nested units are copied, not read). -/
def addHook (a : Add) (ba : ByteArray) : Hook := fun outer x y => do
  if !outer then return ()
  let (ns, ne) ← customOfB ba x y
  if strOf (sl ba ns ne) ∉ addNames then return ()
  match addSec a false {} ⟨0, [], sl ba x y⟩ with
  | .ok _ => pure ()
  | .error e => match addErrB ba ns ne y with
    | .error e' => throw e'
    | .ok () => throw (FErr.plain e)

/-- `addOci` over an output array. -/
def addOciB (a : Add) (out : ByteArray) : Except String ByteArray := do
  let mut out := out
  for (k, f) in ociFields a do
    if let .set v := f then
      out := appendList out (strSec k (← ociValue k v))
  pure out

/-- **`AddMetadata::to_wasm`** over a `ByteArray`. -/
def addMetadataB (a : Add) (ba : ByteArray) : Except String ByteArray := do
  let (enc, items) ← match parseBinaryB ba with
    | .ok r => pure r
    | .error e => throw (firstErr ba (addHook a ba) e)
  let comp := enc == .component
  let st ← items.foldlM (fun st it =>
    match it with
    | .sec s => addSecB a comp ba st s
    | .nest id _ _ _ enc' items' =>
      let inner := pushRawItems ba (appendList ByteArray.empty enc'.header) items'
      pure { st with out := appendList (st.out.push id) (encU32 inner.size) ++ inner })
    ({ out := appendList (ByteArray.emptyWithCapacity (ba.size + 256)) enc.header } : AddStB)
  let mut out := st.out
  if !st.namesFound then
    if let .set v := a.name then
      out := appendList out (customSec (if comp then compNameName else nameName) (encNames [.name (sBytes v)]))
  if !st.producersFound && !a.producers.isEmpty then
    out := appendList out (encProducers (Producers.merge [] a.producers))
  addOciB a out

end Metadata

namespace Demangle

/-- The output of one section over the input array: a `name` section is demangled
(`demangleSecBody`), every other section copied. -/
def pushDemangleSec (ba : ByteArray) (out : ByteArray) (s : SecB) : ByteArray :=
  let raw := pushRawSec out s.id ba s.bodyAt s.bodyEnd
  if s.id != 0 then raw else
  match customOfB ba s.bodyAt s.bodyEnd with
  | .error _ => raw
  | .ok (ns, ne) =>
    if sl ba ns ne != nameName then raw
    else appendList out (demangleSecBody 0 (sl ba s.bodyAt s.bodyEnd))

/-- **`wasm-tools demangle`** over a `ByteArray`. -/
def demangleB (ba : ByteArray) : Except String ByteArray :=
  match readHeaderB ba none ba.size 0 with
  | .ok (.component, _) => .error "demangling components is not supported"
  | _ =>
    match parseBinaryB ba with
    | .error e => .error e.render
    | .ok (_, items) =>
      .ok (items.foldl (fun out it =>
        match it with
        | .sec s => pushDemangleSec ba out s
        | .nest id _ _ _ _ _ => appendList out (rawSec id []))
        (appendList (ByteArray.emptyWithCapacity (ba.size + 256)) Enc.module.header))

end Demangle

end Silmaril.Wasm.Tools.Meta

end
