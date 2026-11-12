module

public import Silmaril.X86.Sep.CSpec.Defs
public import Silmaril.X86.Sep.SysV.Defs
public import Silmaril.Machine.Abi.CtypeBridge.Defs
public import Silmaril.Machine.Abi.CallFootprint.Defs
/-!
# `CSpec` → FFI export: `ofCtypes`, `ofSignature`, total satisfaction and the FFI run

This header connects the author spec
`CSpec` (CP-10b) to the exported certificate `CallFootprint.FfiRealizesCall` (the ABI model's typed
FFI signature) and to Cerberus `Ctype` prototypes through CPA (`Abi/CtypeBridge`). There is
**no classification of our own**: object layouts come from the ABI model's `objectOfCtype`, plans from
the ABI model's `plan`.

**Specs from C types and signatures** (namespace `Silmaril.X86.Sep.CSpec`):
* `CSpec.ofCtypes`: `CSpec.ofPlan` applied to the `objectOfCtype` classification of the
  argument and result `Ctype`s; the precondition adds that classification succeeded
  (`Classified`). `CSpec.ofScalarFn tags S ks r` is the instance for an integer `FnSpec`
  `S` with the fragment prototype `ks → r` (CPA's `Scalar.toCtype`).
* `CSpec.ofSignature sig stack result pre post`: the spec of a System V ABI `Ffi.Signature`. Its
  logical argument `SigArg sig` is the typed argument values, the FFI call and the object
  bytes of each argument. The plan is `sig.callPlan`; the hidden result pointer is the call's
  `resultStorage`; the precondition adds that the frame is the call's (`callFrame`) and that
  the bytes encode the values (`ArgBytes`); the postcondition adds that the result bytes
  encode `result values call` (`ResultBytes`).

**Total satisfaction.** `CSpec.Sat` (CP-10b) is step-indexed partial correctness, and
`FfiRealizesCall` is angelic (some run returns). The bridge therefore needs a total notion:
`CSpec.XTriple M P Q` (from `P` and any frame, some run reaches `Q` with the frame) and
`CSpec.SatT M C entry S` (the `SatN` shape with `XTriple`). `SatT` implies `Sat`
(`Thms.SatT.sat`), and `FnSpec.toC` of every `FnSpec` proof is `SatT` (`Thms.satT_toC_of_sat`),
so this is the total reading of the same spec, not a new spec notion.

**The FFI run of an XMM machine** (namespace `Silmaril.Machine.Abi.CSpecFfi`):
* `withX s x`: the `Ffi.State` `s` with its integer machine replaced by `x.m` and the low 128
  bits of vector registers 0-15 by `x.xmm`. Everything `Sse9.XState` does not model (upper
  vector bits, vector registers 16-31, x87, direction flag field, MXCSR, x87 control word,
  `fsBase`) is **carried unchanged**, the same modelling choice as track A's
  `Open.ffiExecute`; it is sound only for code that does not touch that state.
* `xExecute M call final`: `step` reaches some `x` from `ffiXState call.initial`, and
  `final = withX call.initial x`.

**The entry condition of the export.** `EntrySplit S C e call x hP`: the fragment `hP` of the
call's initial state satisfies the code and the `CSpec` precondition at `callFrame call`, owns
no callee-saved register and not the mapping list (`Sep.Avoids`), and the frame is aligned
with room for the budget. `entryWrites S C e call` is the set of byte addresses owned by such
a fragment (the footprint of the export, as in `FnSpec.contractSpec`). `ResultShaped sig`:
the plan's result kind matches the signature (decidable for a concrete signature).

**Example** (`pairSig`, `pairIdSpec`): the `{uint64_t, uint64_t}` identity, a 16-byte INTEGER
struct passed in `rdi:rsi` and returned in `rax:rdx`.

Name hygiene: no declaration here is named after the ABI convention type, and
no `open` of the compiler's category namespace.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.CSpecFfi

open Silmaril.X86 (XReg)
open Silmaril.X86.Sse9 (XState)
open Silmaril.X86.Sep.Plan (ffiXState xregOfIdx)
open Silmaril.Machine.SystemV.Abi (Ffi.State Ffi.Call)

/-- An XMM register value written into the low 128 bits of a 512-bit vector register, upper
bits kept. -/
def setLow128 (old : BitVec 512) (v : BitVec 128) : BitVec 512 :=
  (old.extractLsb' 128 384 ++ v : BitVec (384 + 128))

/-- **An `Ffi.State` updated by an XMM machine state**: integer machine and the low 128 bits
of vector registers 0-15 from `x`; everything else carried from `s`. -/
def withX (s : Ffi.State) (x : XState) : Ffi.State :=
  { s with
    machine := x.m
    vectors := fun i => if i < 16 then setLow128 (s.vectors i) (x.xmm (xregOfIdx i))
      else s.vectors i }

/-- **The FFI execution relation of an XMM machine `M`**: some run from the projection of
the initial state, written back into the initial `Ffi.State`. -/
def xExecute (M : Silmaril.X86.SegVC.Isa XState) (call : Ffi.Call) (final : Ffi.State) : Prop :=
  ∃ x, Silmaril.Machine.Execution.Reaches M.step (ffiXState call.initial) x ∧
    final = withX call.initial x

end Silmaril.Machine.Abi.CSpecFfi

namespace Silmaril.X86.Sep

open Silmaril.X86 (Reg XReg Word Byte)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.C.Api (Scalar)
open Silmaril.Cerberus (Ctype)
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.X86.Sse9 (XState)
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.Machine.SystemV.Abi (Object Profile CallPlan objectOfCtype)
open Silmaril.Machine.Abi.CtypeBridge (Scalar.toCtype)

namespace CSpec

/-! ## Total satisfaction -/

/-- **A total triple on an XMM machine**, frame built in: from `P` with any frame, some run
reaches `Q` with the same frame. -/
def XTriple (M : Silmaril.X86.SegVC.Isa XState) (P Q : XSProp) : Prop :=
  ∀ (F : XSProp) (x : XState), (P ∗ₓ F) (toXFrag x) →
    ∃ x', Reaches M.step x x' ∧ (Q ∗ₓ F) (toXFrag x')

/-- **The code `C` at `entry` meets `S` totally**: from every aligned frame with room for the
budget, some run returns with the postcondition. -/
def SatT (M : Silmaril.X86.SegVC.Isa XState) (C : XSProp) (entry : Word) (S : CSpec) : Prop :=
  ∀ (x : S.Arg) (fr : Frame), FnSpec.EntryAligned fr.sp → S.stack x ≤ fr.sp.toNat →
    XTriple M (C ∗ₓ S.Pre x entry fr) (C ∗ₓ S.Post x fr)

/-! ## Specs from C types (through CPA) -/

/-- The classified objects, or `[]` when classification fails (then `Classified` is false). -/
def objectsOr : Except String (List Object) → List Object
  | .ok os => os
  | .error _ => []

/-- The classified result object, or `none` when classification fails. -/
def resultOr : Except String (Option Object) → Option Object
  | .ok o => o
  | .error _ => none

/-- the ABI model's `objectOfCtype` classifies every argument and the result. -/
def Classified (tags : Tags) (args : List Ctype) (res : Option Ctype) : Prop :=
  (args.mapM (objectOfCtype tags)).toOption.isSome = true ∧
    (res.mapM (objectOfCtype tags)).toOption.isSome = true

/-- **A `CSpec` from C types**: `ofPlan` applied to `objectOfCtype`'s results. The
precondition adds that classification succeeded. -/
def ofCtypes (profile : Profile) (tags : Tags) (Arg : Type) (args : Arg → List Ctype)
    (res : Arg → Option Ctype) (named : Nat) (variadic : Bool)
    (bytes : Arg → List (List Byte)) (sret : Arg → Option Word) (stack : Arg → Nat)
    (pre : Arg → Frame → XSProp) (post : Arg → Frame → List Byte → XSProp) : CSpec :=
  ofPlan profile Arg (fun x => objectsOr ((args x).mapM (objectOfCtype tags)))
    (fun x => resultOr ((res x).mapM (objectOfCtype tags))) named variadic bytes sret stack
    (fun x fr => ⌜Classified tags (args x) (res x)⌝ₓ ∗ₓ pre x fr) post

/-- **An integer `FnSpec` with the fragment prototype `ks → r`, through C types.** Word
arguments as eight-byte objects, a word result, the budget and assertions of `S`. -/
def ofScalarFn (tags : Tags) (S : FnSpec) (ks : List Scalar) (r : Scalar) : CSpec :=
  ofCtypes {} tags S.Arg (fun _ => ks.map Scalar.toCtype) (fun _ => some (Scalar.toCtype r))
    ks.length false (fun x => (S.args x).map wordBytes) (fun _ => none) (fun _ => S.stack)
    (fun x _ => ↑ₓ(S.pre x)) (fun x _ rb => xsexists fun v => ⌜rb = wordBytes v⌝ₓ ∗ₓ ↑ₓ(S.post x v))

/-! ## Specs from the ABI model signatures -/

open Silmaril.Machine.SystemV.Abi (Ffi.Signature Ffi.Values Ffi.ResultValue Ffi.ObjectSpec Ffi.Call)

/-- The logical argument of `ofSignature`: typed argument values, the FFI call, and the object
bytes of each argument. -/
structure SigArg (sig : Ffi.Signature) where
  values : Ffi.Values sig.arguments
  call : Ffi.Call
  bytes : List (List Byte)

/-- The callee-entry frame of an FFI call: the initial `rsp`, and the call's exit address. -/
def callFrame (call : Ffi.Call) : Frame := ⟨call.initial.machine.core.read .rsp, call.exit⟩

/-- Each argument's bytes encode its value (the ABI model's `representation.encodes`). -/
def ArgBytes : (specs : List Ffi.ObjectSpec) → Ffi.Values specs → List (List Byte) → Prop
  | [], _, [] => True
  | spec :: rest, (value, values), b :: bs =>
      (∃ e, spec.representation.encodes value e ∧ b = toSepBytes e) ∧ ArgBytes rest values bs
  | _, _, _ => False

/-- The result bytes encode the result value (`[]` for `void`). -/
def ResultBytes : (spec : Option Ffi.ObjectSpec) → Ffi.ResultValue spec → List Byte → Prop
  | none, _, rb => rb = []
  | some spec, value, rb => ∃ e, spec.representation.encodes value e ∧ rb = toSepBytes e

/-- **The `CSpec` of a System V ABI signature**, with a call-dependent result `result`. -/
def ofSignature (sig : Ffi.Signature) (stack : Nat)
    (result : Ffi.Values sig.arguments → Ffi.Call → Ffi.ResultValue sig.result)
    (pre : SigArg sig → Frame → XSProp) (post : SigArg sig → Frame → List Byte → XSProp) :
    CSpec where
  Arg := SigArg sig
  shape x := ⟨sig.callPlan, x.bytes, x.call.resultStorage.map (BitVec.ofNat 64)⟩
  stack _ := stack
  pre x fr := ⌜fr = callFrame x.call ∧ ArgBytes sig.arguments x.values x.bytes⌝ₓ ∗ₓ pre x fr
  post x fr rb := ⌜ResultBytes sig.result (result x.values x.call) rb⌝ₓ ∗ₓ post x fr rb

/-- The plan's result kind matches the signature: `void` exactly for no result, and a
non-empty indirect result. -/
def ResultShaped (sig : Ffi.Signature) : Prop :=
  match sig.result, sig.callPlan.result with
  | none, .void => True
  | none, _ => False
  | some _, .void => False
  | some _, .direct _ => True
  | some _, .indirect size _ => 0 < size

/-! ## The entry condition and footprint of the export -/

/-- **The `CSpec` entry condition at an FFI call**: `hP`, a part of the call's initial state,
satisfies the code and the precondition at `callFrame call`; it owns no callee-saved register
and not the mapping list; the frame is aligned and leaves room for the budget. -/
def EntrySplit (S : CSpec) (C : XSProp) (entry : Word) (call : Ffi.Call) (x : S.Arg)
    (hP : XFrag) : Prop :=
  (C ∗ₓ S.Pre x entry (callFrame call)) hP ∧
    XFrag.Le hP (toXFrag (ffiXState call.initial)) ∧ Avoids hP.1 ∧
    S.stack x ≤ (callFrame call).sp.toNat ∧ FnSpec.EntryAligned (callFrame call).sp

/-- The byte addresses owned by some entry split: the footprint of the export. -/
def entryWrites (S : CSpec) (C : XSProp) (entry : Word) (call : Ffi.Call) :
    Silmaril.Machine.SystemV.Abi.Ffi.Footprint := fun a =>
  ∃ x hP, EntrySplit S C entry call x hP ∧ (hP.1 (.mem a)).isSome

/-- **The domain of `ofSignature`'s export**: some entry split whose logical argument carries
the call's values and the call. -/
def SigDomain (sig : Ffi.Signature) (stack : Nat)
    (result : Ffi.Values sig.arguments → Ffi.Call → Ffi.ResultValue sig.result)
    (pre : SigArg sig → Frame → XSProp) (post : SigArg sig → Frame → List Byte → XSProp)
    (C : XSProp) (entry : Word) (a : Ffi.Values sig.arguments) (call : Ffi.Call) : Prop :=
  ∃ (x : SigArg sig) (hP : XFrag), x.values = a ∧ x.call = call ∧
    EntrySplit (ofSignature sig stack result pre post) C entry call x hP

/-! ## Example: the `{uint64_t, uint64_t}` identity -/

open Silmaril.Cerberus.NativeTypes (CType Representation Bytes)

/-- The layout of `struct { uint64_t a, b; }`: sixteen bytes, two INTEGER eightbytes. -/
def pairObject : Object := ⟨16, 8, [.integer, .integer]⟩

/-- Its representation: two words, little-endian. -/
def pairRepr : Representation (.record .struct 0) where
  layout := ⟨16, 8, 128⟩
  Value := Word × Word
  encodes v bytes := bytes = Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat v.1.toNat 0 8 ++
    Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat v.2.toNat 0 8
  exactSize := by
    rintro v bytes rfl
    simp [Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat]

/-- The the ABI model object specification of the pair. -/
def pairSpec : Ffi.ObjectSpec where
  type := .record .struct 0
  object := pairObject
  representation := pairRepr
  size := rfl
  alignment := rfl
  valid := by decide

/-- The plan of `struct pair id(struct pair)`: `rdi:rsi` in, `rax:rdx` out. -/
def pairPlan : CallPlan :=
  ⟨[⟨pairObject, [⟨0, 8, .gp .rdi⟩, ⟨8, 8, .gp .rsi⟩], none⟩],
    .direct [⟨0, 8, .gp .rax⟩, ⟨8, 8, .gp .rdx⟩], 0, 16, 2, 0, none⟩

/-- **The signature of `struct pair id(struct pair)`.** -/
def pairSig : Ffi.Signature where
  profile := {}
  arguments := [pairSpec]
  result := some pairSpec
  namedCount := 1
  variadic := false
  callPlan := pairPlan
  planned := by rfl

/-- **The `{uint64_t, uint64_t}` identity as a `CSpec`**: no stack, no user assertions; the
result is the argument. -/
def pairIdSpec : CSpec :=
  ofSignature pairSig 0 (fun v _ => v.1) (fun _ _ => xemp) (fun _ _ _ => xemp)

end CSpec

end Silmaril.X86.Sep
