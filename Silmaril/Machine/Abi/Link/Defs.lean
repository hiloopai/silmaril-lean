module

public import Silmaril.Machine.Abi.SystemV.Thms
public import Silmaril.Machine.Abi.Infer.Defs
/-! # ABI tags, link compatibility and thunk obligations

This is the link-facing interface of the ABI comorphisms. A linker tags every
import and export with an `Endpoint` (a C prototype of the INTEGER/pointer
fragment and an `AbiTag`) and asks `check importer exporter`:

* `.direct` — the importer may call the exporter directly; `Thms.check_direct_agree`
  proves the two conventions `Agree`, so the exporter's verified machine contract
  *is* the importer's (`Thms.compatible_translate_eq`);
* `.thunk` — same prototype, different conventions; linking needs an adapter
  with a `Convention.Thunk.Correct` proof (`Bridge`), and then
  `Thms.link_sound` transfers the exporter's contract through it;
* `.reject` — the prototypes differ; no thunk is offered.

`Compatible` is the decidable predicate `check imp exp = .direct`.

The meaning of a tag is supplied by an `Interp`, which may leave tags
uninterpreted (`none`) but must send every LP64 System V tag to C1's `sysv`
convention. `Interp.standard` interprets exactly those tags. Soundness is proved
for *every* `Interp`, so a later Win64 or x32 convention plugs in without
re-proving `check`.

Rules of `checkTags`, and why each is sound or conservative:
* identical tags are direct (`Agree` is reflexive);
* LP64 System V tags differing only in vector level are direct on the INTEGER
  fragment (`SystemV.sysv_agree`; vector arguments are outside the fragment);
* red zone: a red-zone callee under a no-red-zone caller needs a thunk (one that
  moves RSP down by 128 bytes, say). The red zone is semantically inert in C1's
  value-level contracts, so this rule is stricter than the semantics requires;
  it anticipates footprint contracts;
* x32, Win64 and inferred tags are direct only when identical: different
  options of these may be interpreted by non-agreeing conventions;
* everything else with the same prototype needs a thunk.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.Link

open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options CallSite)
open Silmaril.Machine.SystemV.Abi (VectorLevel Ffi.State)
open Silmaril.X86 (Reg)
open Silmaril.Logic.Institution.Bridges

/-- System V AMD64 options: vector level, red zone, and the x32 (ILP32) model. -/
structure SysvOptions where
  vectors : VectorLevel := .sse
  redZone : Bool := true
  x32 : Bool := false
  deriving DecidableEq, Repr

/-- The C1 options of an LP64 System V tag. -/
def SysvOptions.options (o : SysvOptions) : Options :=
  { profile := { vectors := o.vectors }, redZone := o.redZone }

/-- A link-level ABI tag. `inferred` carries the register-usage evidence a lifter
produced for a local function (`*.isra`, `*.constprop`) with no declared ABI. -/
inductive AbiTag where
  | sysv64 (o : SysvOptions)
  | ms64
  | inferred (evidence : Infer.Usage Reg)
  deriving DecidableEq, Repr

/-- C1's coarser `Tag`. -/
def AbiTag.toTag : AbiTag → Tag
  | .sysv64 o => if o.x32 then .sysvX32 else (o.options).tag
  | .ms64 => .win64
  | .inferred _ => .other "inferred"

/-- An import or export: a C prototype under an ABI. -/
structure Endpoint where
  proto : Proto
  abi : AbiTag

/-- Outcome of the link check. -/
inductive Verdict where
  | direct
  | thunk
  | reject
  deriving DecidableEq, Repr

/-- Tag compatibility for one prototype (the prototype is unused on the
INTEGER fragment; vector arguments will make it matter). -/
def checkTags (_p : Proto) (imp exp : AbiTag) : Verdict :=
  if imp = exp then .direct else
  match imp, exp with
  | .sysv64 i, .sysv64 e =>
    if !i.x32 && !e.x32 && (!e.redZone || i.redZone) then .direct else .thunk
  | _, _ => .thunk

/-- The link check between an importer and an exporter. -/
def check (imp exp : Endpoint) : Verdict :=
  if imp.proto.signature = exp.proto.signature then checkTags imp.proto imp.abi exp.abi
  else .reject

/-- Direct link compatibility; decidable. -/
def Compatible (imp exp : Endpoint) : Prop := check imp exp = .direct

instance (imp exp : Endpoint) : Decidable (Compatible imp exp) :=
  inferInstanceAs (Decidable (check imp exp = .direct))

/-- A semantics for tags: the convention each tag denotes, if any. LP64 System V
tags must denote C1's `sysv`. -/
structure Interp where
  conv : AbiTag → Option (Convention vocab Ffi.State CallSite)
  sysv : ∀ o : SysvOptions, o.x32 = false → conv (.sysv64 o) = some (sysv o.options)

/-- Only LP64 System V tags are interpreted. -/
def Interp.standard : Interp where
  conv
    | .sysv64 o => if o.x32 then none else some (SystemV.sysv o.options)
    | _ => none
  sysv o h := by simp [h]

/-- What a link edge with a given verdict must supply: nothing for `direct`, a
correct thunk for `thunk`, and nothing can be supplied for `reject`. -/
def Bridge (A B : Convention vocab Ffi.State CallSite) (p : Proto) : Verdict → Type
  | .direct => PUnit
  | .thunk => { t : Convention.Thunk A B p // t.Correct }
  | .reject => Empty

/-- The machine relation the importer actually calls through the bridge. -/
def Bridge.wrap {A B : Convention vocab Ffi.State CallSite} {p : Proto} :
    (v : Verdict) → Bridge A B p v → Contracts.Model Ffi.State Ffi.State →
      Contracts.Model Ffi.State Ffi.State
  | .direct, _, model => model
  | .thunk, t, model => t.1.wrap model
  | .reject, e, _ => nomatch e

/-- The inference candidate of a prototype under a family. -/
def candidate (fam : Infer.Family) (p : Proto) : Infer.Candidate :=
  ⟨fam, p.signature.arguments.length, p.signature.result.isSome⟩

/-- Diagnostic for an `inferred` exporter: its register evidence is consistent with
the prototype under `fam` (`Infer.consistent_iff_respects`). This is only the
register discipline; it does not discharge the `thunk` obligation. -/
def evidenceFits (fam : Infer.Family) (p : Proto) : AbiTag → Bool
  | .inferred u => Infer.consistent u (candidate fam p)
  | _ => true

end Silmaril.Machine.Abi.Link
