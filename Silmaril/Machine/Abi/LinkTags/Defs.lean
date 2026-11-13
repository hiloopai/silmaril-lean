module

public import Silmaril.X86.Link.Abi.Defs
public import Silmaril.Machine.Abi.LinkSim.Defs
/-! # One meaning for two ABI tag vocabularies

Track B's linker (`Silmaril.X86.Link.Abi`) guards the imported static linker with
`checkAbi policy objects ifaces`, over an arbitrary tag type: a binding of an import tagged
`ti` to an export tagged `te` is accepted when `policy.compatible ti te` or a thunk
`⟨name, ti, te⟩` is declared. Track C's link layer (`Silmaril.Machine.Abi.Link`) gives tags a
meaning: an `Endpoint` (C prototype and `AbiTag`), the decidable `check` with verdicts
`direct`/`thunk`/`reject`, an `Interp`retation of tags as conventions, and `link_sound`.

This module joins them:

* `PolicySound ep policy`: the B policy is *sound* for C's check under a tag meaning
  `ep : NameBytes → T → Option Endpoint` (a tag on a name denotes an endpoint, or nothing for
  data and private conventions): `compatible` implies C's `Compatible`, and a declared thunk
  is never a C `reject`;
* `Edge ep policy name ti te`: the C verdict of an accepted binding is `direct`, or `thunk`
  with a declared thunk;
* `Bridges I ep policy`: a simulating adapter (`Link.SimThunk`) for every declared thunk on a
  `thunk` edge;
* `Transfers I ep name ti te`: the binding carries ABI correctness: a bridge for its C verdict
  exists, and through it every exporter that satisfies its convention's translation of a
  strict C contract satisfies the importer's translation (`Link.link_sound_sim`);
* `abiTagOf`, `convEndpoint`: the obvious map from B's default vocabulary `Conv` (`sysv64`
  to LP64 System V with default options, `ms64` to `ms64`, `data` and `custom` to nothing),
  given each name's prototype.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.LinkTags

open Silmaril.Formats.ELF (NameBytes)
open Silmaril.Logic.Institution.Bridges
open Silmaril.X86.Link.Abi (Policy Interface Conv)
open Silmaril.Machine.Abi.Link (Endpoint Verdict check Compatible Interp SimBridge SimThunk AbiTag)
open Silmaril.Machine.Abi.SystemV (Proto vocab CallSite)
open Silmaril.Machine.SystemV.Abi (Ffi.State)
open Silmaril.Machine.Abi.Convention (Strict Guarantees)

/-- B's declared thunk (a link-time permission). -/
abbrev DeclThunk := Silmaril.X86.Link.Abi.Thunk

variable {T : Type}

/-- B's policy is sound for C's link check under the tag meaning `ep`. -/
structure PolicySound (ep : NameBytes → T → Option Endpoint) (policy : Policy T) : Prop where
  compatible : ∀ name ti te i e, policy.compatible ti te = true → ep name ti = some i →
    ep name te = some e → Compatible i e
  thunks : ∀ th ∈ policy.thunks, ∀ i e, ep th.name th.importTag = some i →
    ep th.name th.exportTag = some e → check i e ≠ .reject

/-- The C verdict of a binding is `direct`, or `thunk` with a declared thunk. -/
def Edge (ep : NameBytes → T → Option Endpoint) (policy : Policy T) (name : NameBytes)
    (ti te : T) : Prop :=
  ∀ i e, ep name ti = some i → ep name te = some e →
    check i e = .direct ∨ (check i e = .thunk ∧ (⟨name, ti, te⟩ : DeclThunk T) ∈ policy.thunks)

/-- A simulating adapter for every declared thunk whose C verdict is `thunk`. -/
def Bridges (I : Interp) (ep : NameBytes → T → Option Endpoint) (policy : Policy T) : Type :=
  ∀ th : DeclThunk T, th ∈ policy.thunks → ∀ i e A B, ep th.name th.importTag = some i →
    ep th.name th.exportTag = some e → I.conv i.abi = some A → I.conv e.abi = some B →
    check i e = .thunk → SimThunk A B i.proto

/-- A binding carries ABI correctness: for its C verdict there is a bridge, and through it
the exporter's translated contract gives the importer's (on the bridge's room). -/
def Transfers (I : Interp) (ep : NameBytes → T → Option Endpoint) (name : NameBytes)
    (ti te : T) : Prop :=
  ∀ i e A B, ep name ti = some i → ep name te = some e → I.conv i.abi = some A →
    I.conv e.abi = some B → ∃ v, check i e = v ∧ ∃ bridge : SimBridge A B i.proto v,
      ∀ (model : Contracts.Model Ffi.State Ffi.State)
        (c : Contracts.Contract (vocab.Args i.proto) (Option (vocab.Ret i.proto))),
        Strict c → Contracts.Sat model (B.translate i.proto c) →
        Guarantees B i.proto c model (SimBridge.guar v bridge) →
        Contracts.Sat (SimBridge.wrap v bridge model)
          (within (A.translate i.proto c) (SimBridge.room v bridge))

/-- The link-layer meaning of B's default tags. -/
def abiTagOf : Conv → Option AbiTag
  | .sysv64 => some (.sysv64 {})
  | .ms64 => some .ms64
  | .data => none
  | .custom _ => none

/-- A `Conv` tag on `name` denotes the endpoint of `name`'s prototype under that tag. -/
def convEndpoint (protoOf : NameBytes → Option Proto) (name : NameBytes) (t : Conv) :
    Option Endpoint :=
  match protoOf name, abiTagOf t with
  | some p, some a => some ⟨p, a⟩
  | _, _ => none

/-- B's `Policy.exact` on `Conv` with a list of declared thunks. -/
def convPolicy (thunks : List (DeclThunk Conv)) : Policy Conv :=
  { (Policy.exact : Policy Conv) with thunks := thunks }

end Silmaril.Machine.Abi.LinkTags
