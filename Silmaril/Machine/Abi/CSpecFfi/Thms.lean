module

public import Silmaril.Machine.Abi.CSpecFfi.Defs
public import Silmaril.X86.Sep.CSpec.Thms
public import Silmaril.Machine.Abi.CtypeBridge.Thms
import Silmaril.Proofs.Machine.Abi.CSpecFfi
/-!
# `CSpec` → FFI export: what is proved (CP-12)

PROVED with the standard axioms (proofs in `Silmaril/Proofs/Machine/Abi/CSpecFfi.lean`).

**Total satisfaction.** `CSpec.SatT.sat` (total implies CP-10b's partial `Sat`);
`CSpec.XTriple.frame`, `CSpec.XTriple.conseq`; `CSpec.xtriple_of_triple` (track A's total
`Sep.Triple`s are total triples of every XMM machine extending `Open9`); and
**`CSpec.satT_toC_of_sat`**: `S.Sat Open.isa C entry → S.toC.SatT M ↑ₓC entry`.

**C types, through CPA.**
* `CSpec.ofCtypes_plan_ok`: the plan of `ofCtypes` is `Abi.plan` on the classified objects.
* **`CSpec.ofCtypes_proto`**: on a fragment prototype `p` (`Proto.ctypes p`,
  `Proto.resultCtype p`), the plan is `(sigOf profile p).callPlan`, the typed FFI signature
  of `Abi.SystemV.convention`; **`CSpec.ofCtypes_desc`**: `(sysv options).desc p` is that plan.
* **`CSpec.ofCtypes_scalar`**: for an integer `FnSpec` `S` with a prototype `ks → r` of
  64-bit scalars (`uint64`, `int64`, pointer; at most six arguments; `S.args` of length
  `ks.length`), `ofScalarFn tags S ks r` has `S.toC`'s shape, and the two specs refine each
  other (`Sub` both ways). Equality of the two `CSpec` structures does not hold literally
  (`ofCtypes` adds pure facts to the precondition); mutual refinement is the statement.
  The agreement with the native call-convention correspondence is CPA's gated corollary (`native_call_plan_is_convention`), which
  is **not** built here.

**The export.**
* `CSpec.ffiXState_withX`: `ffiXState (withX s x) = x`.
* `CSpec.resultAt_of_retPt`: the result placement `retPt` with `ResultBytes` gives the ABI model's
  `Ffi.ResultAt` (direct chunks through CP-10a's `chunksPt_iff_chunksAt`; `sret` through the
  call's `SretAt`), when `ResultShaped sig`.
* **`CSpec.realizes_of_satT`**: from `S.SatT M C entry`, for any signature, result,
  aliasing predicate and domain, if every admitted call has an `EntrySplit` and the
  postcondition gives `ResultAt`, then
  `FfiRealizesCall sig result (entryWrites S C entry) unaliased domain (xExecute M)`.
  `Return` (exit address, `rsp + 8`, callee-saved registers), the write frame and the
  mapping list come from the frame rule: the complement of the entry split is the frame.
* **`CSpec.ofSignature_realizes`**: for `ofSignature sig …` the result obligation is
  discharged, and the domain is `SigDomain` (the spec's entry condition at the call).
* **`CSpec.pairId_realizes`** (acceptance): a total proof of the `{uint64_t, uint64_t}`
  identity spec `pairIdSpec` yields the export for `pairSig`.

Not proved here: that `SigDomain` follows from `Ffi.Entry` plus a code/stack layout condition
(the domain is the spec's entry condition, as for libmini's `memcpyDomain`); a `SatT` proof of
concrete pair-identity code (CP-13's `pair_swap_sat`); the native-correspondence corollary.
-/

@[expose] public section

namespace Silmaril.X86.Sep.CSpec

open Silmaril.X86 (Word Byte XReg)
open Silmaril.C.Api (Scalar)
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.X86.Sse9 (XState)
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.Machine.SystemV.Abi (Object Profile CallPlan)
open Silmaril.Machine.SystemV.Abi (Ffi.State Ffi.Call Ffi.Signature Ffi.Values Ffi.ResultValue)
open Silmaril.Machine.Abi.CtypeBridge (Scalar.toCtype Proto.ctypes Proto.resultCtype sigOf)
open Silmaril.Machine.Abi.CSpecFfi (withX xExecute)
open Silmaril.Machine.Abi.CallFootprint (FfiRealizesCall)

/-! ## Total satisfaction -/

section Total

variable {M : Silmaril.X86.SegVC.Isa XState}

/-- **Total satisfaction gives CP-10b's partial satisfaction.** -/
theorem SatT.sat {C : XSProp} {entry : Word} {S : CSpec} (h : S.SatT M C entry) :
    S.Sat M C entry :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.SatT.sat h

theorem XTriple.frame {P Q : XSProp} (h : XTriple M P Q) (R : XSProp) :
    XTriple M (P ∗ₓ R) (Q ∗ₓ R) :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.XTriple.frame h R

theorem XTriple.conseq {P P' Q Q' : XSProp} (hp : P' ⊢ₓ P) (h : XTriple M P Q)
    (hq : Q ⊢ₓ Q') : XTriple M P' Q' :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.XTriple.conseq hp h hq

/-- Track A's total triples are total triples of every XMM machine extending `Open9`. -/
theorem xtriple_of_triple [ExtendsOpen9X M] {P Q : SProp}
    (h : Triple Silmaril.X86.Open.isa P Q) :
    XTriple M (lift P) (lift Q) :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.xtriple_of_triple h

/-- **Every `FnSpec` proof is a total `CSpec` proof** on every XMM machine extending
`Open9`. -/
theorem satT_toC_of_sat [ExtendsOpen9X M] {S : FnSpec} {C : SProp} {entry : Word}
    (hS : S.Sat Silmaril.X86.Open.isa C entry) : S.toC.SatT M ↑ₓC entry :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.satT_toC_of_sat hS

end Total

/-! ## C types -/

theorem ofCtypes_plan_ok {profile : Profile} {tags : Tags} {Arg : Type} {args res named
    variadic bytes sret stack pre post} (x : Arg) {os : List Object} {ro : Option Object}
    (hos : (args x).mapM (Silmaril.Machine.SystemV.Abi.objectOfCtype tags) = .ok os)
    (hro : (res x).mapM (Silmaril.Machine.SystemV.Abi.objectOfCtype tags) = .ok ro) :
    ((ofCtypes profile tags Arg args res named variadic bytes sret stack pre post).shape x).plan =
      planOr (Silmaril.Machine.SystemV.Abi.plan profile os ro named variadic) :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.ofCtypes_plan_ok x hos hro

/-- **`ofCtypes` on a fragment prototype has the convention's plan.** -/
theorem ofCtypes_proto (profile : Profile) (tags : Tags) (p : Silmaril.Machine.Abi.SystemV.Proto)
    {Arg : Type} {bytes sret stack pre post} (x : Arg) :
    ((ofCtypes profile tags Arg (fun _ => Proto.ctypes p) (fun _ => Proto.resultCtype p)
      (Proto.ctypes p).length false bytes sret stack pre post).shape x).plan =
      (sigOf profile p).callPlan :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.ofCtypes_proto profile tags p x

/-- **`Abi.SystemV.convention`'s descriptor is `ofCtypes`'s plan**, for every tag table. -/
theorem ofCtypes_desc (options : Silmaril.Machine.Abi.SystemV.Options) (tags : Tags)
    (p : Silmaril.Machine.Abi.SystemV.Proto) {Arg : Type} {bytes sret stack pre post} (x : Arg) :
    (Silmaril.Machine.Abi.SystemV.sysv options).desc p =
      ⟨options.tag, .ok ((ofCtypes options.profile tags Arg (fun _ => Proto.ctypes p)
        (fun _ => Proto.resultCtype p) (Proto.ctypes p).length false bytes sret stack pre
        post).shape x).plan⟩ := by
  rw [ofCtypes_proto, Silmaril.Machine.Abi.CtypeBridge.sysv_desc_of_ctypes options tags p,
    Silmaril.Machine.Abi.CtypeBridge.ctypePlan_eq_callPlan]

/-- **`ofCtypes_scalar`**: on a prototype of 64-bit scalars, the C-type spec of an integer
`FnSpec` has `FnSpec.toC`'s shape, and the two refine each other. -/
theorem ofCtypes_scalar (tags : Tags) (S : FnSpec) (ks : List Scalar) (r : Scalar)
    (h64 : ∀ k ∈ ks, Silmaril.Machine.Abi.SystemV.Kind.object k = int64Object)
    (hr : Silmaril.Machine.Abi.SystemV.Kind.object r = int64Object) (hks : ks.length ≤ 6)
    (hlen : ∀ x, (S.args x).length = ks.length) :
    (∀ x, (ofScalarFn tags S ks r).shape x = intShape (S.args x)) ∧
      (ofScalarFn tags S ks r).Sub S.toC ∧ S.toC.Sub (ofScalarFn tags S ks r) :=
  ⟨Silmaril.Proofs.Machine.Abi.CSpecFfi.ofScalarFn_shape tags S ks r h64 hr hks hlen,
    Silmaril.Proofs.Machine.Abi.CSpecFfi.ofScalarFn_sub_toC tags S ks r h64 hr hks hlen,
    Silmaril.Proofs.Machine.Abi.CSpecFfi.toC_sub_ofScalarFn tags S ks r h64 hr hks hlen⟩

/-- The 64-bit scalars have the `int64Object` layout. -/
example : Silmaril.Machine.Abi.SystemV.Kind.object .uint64 = int64Object := by decide
example : Silmaril.Machine.Abi.SystemV.Kind.object .int64 = int64Object := by decide
example : Silmaril.Machine.Abi.SystemV.Kind.object .pointer = int64Object := by decide

/-! ## The export -/

theorem ffiXState_withX (s : Ffi.State) (x : XState) : ffiXState (withX s x) = x :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.ffiXState_withX s x

/-- The result placement gives the ABI model's `ResultAt`. -/
theorem resultAt_of_retPt {sig : Ffi.Signature} {call : Ffi.Call} {final : Ffi.State}
    {u : Nat → Nat → Prop} (hshape : ResultShaped sig)
    (hsret : Silmaril.Machine.SystemV.Abi.Ffi.SretAt sig call u)
    (v : Ffi.ResultValue sig.result) (rb : List Byte) (hrb : ResultBytes sig.result v rb)
    (hret : XHolds (retPt sig.callPlan.result (call.resultStorage.map (BitVec.ofNat 64)) rb)
      (ffiXState final)) :
    Silmaril.Machine.SystemV.Abi.Ffi.ResultAt sig call final v :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.resultAt_of_retPt hshape hsret v rb hrb hret

section Export

variable {M : Silmaril.X86.SegVC.Isa XState}

/-- **The export from total satisfaction**, for any `CSpec`. -/
theorem realizes_of_satT {S : CSpec} {C : XSProp} {entry : Word} (hS : S.SatT M C entry)
    (sig : Ffi.Signature) (result : Ffi.Values sig.arguments → Ffi.Call → Ffi.ResultValue sig.result)
    (unaliased : Ffi.Values sig.arguments → Nat → Nat → Prop)
    (domain : Ffi.Values sig.arguments → Ffi.Call → Prop)
    (hentry : ∀ a call, Silmaril.Machine.SystemV.Abi.Ffi.Entry sig a call (unaliased a) →
      domain a call → ∃ x hP, EntrySplit S C entry call x hP ∧
        ∀ x', XHolds (S.Post x (callFrame call)) x' →
          Silmaril.Machine.SystemV.Abi.Ffi.ResultAt sig call (withX call.initial x') (result a call)) :
    FfiRealizesCall sig result (fun _ call => entryWrites S C entry call) unaliased domain
      (xExecute M) :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.realizes_of_satT hS sig result unaliased domain hentry

/-- **`ofSignature_realizes`**: a total proof of `ofSignature sig …` exports as
`FfiRealizesCall` for `sig` (angelic, as `FfiRealizesCall`), with the spec's entry condition
`SigDomain` as domain and its owned bytes `entryWrites` as footprint, on `xExecute M`. -/
theorem ofSignature_realizes {sig : Ffi.Signature} {stack : Nat}
    {result : Ffi.Values sig.arguments → Ffi.Call → Ffi.ResultValue sig.result}
    {pre : SigArg sig → Frame → XSProp} {post : SigArg sig → Frame → List Byte → XSProp}
    {C : XSProp} {entry : Word} (hS : (ofSignature sig stack result pre post).SatT M C entry)
    (hshape : ResultShaped sig) (unaliased : Ffi.Values sig.arguments → Nat → Nat → Prop) :
    FfiRealizesCall sig result
      (fun _ call => entryWrites (ofSignature sig stack result pre post) C entry call) unaliased
      (SigDomain sig stack result pre post C entry) (xExecute M) :=
  Silmaril.Proofs.Machine.Abi.CSpecFfi.ofSignature_realizes hS hshape unaliased

/-! ## Acceptance: the `{uint64_t, uint64_t}` identity -/

/-- `pairSig`'s plan is the ABI model's `plan` on the pair object (`rdi:rsi` in, `rax:rdx` out). -/
example : (Silmaril.Machine.SystemV.Abi.plan {} [pairObject] (some pairObject) 1 false).toOption =
    some pairPlan := by decide

theorem pairSig_shaped : ResultShaped pairSig := trivial

/-- **Acceptance (CP-12)**: a total proof of the `{uint64_t, uint64_t}` identity spec yields
the typed FFI export of `struct pair id(struct pair)`: the result is the argument pair, the
footprint is the spec's owned bytes. -/
theorem pairId_realizes {C : XSProp} {entry : Word} (hS : pairIdSpec.SatT M C entry)
    (unaliased : Ffi.Values pairSig.arguments → Nat → Nat → Prop) :
    FfiRealizesCall pairSig (fun v _ => v.1)
      (fun _ call => entryWrites pairIdSpec C entry call) unaliased
      (SigDomain pairSig 0 (fun v _ => v.1) (fun _ _ => xemp) (fun _ _ _ => xemp) C entry)
      (xExecute M) :=
  ofSignature_realizes hS pairSig_shaped unaliased

end Export

end Silmaril.X86.Sep.CSpec
