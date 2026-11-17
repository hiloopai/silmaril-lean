module

public import Silmaril.Machine.Abi.SystemV.Thms
public import Silmaril.X86.FnContract.Defs
public import Silmaril.Data.Layout.Header.Defs

/-!
# ABI conformance of a function: the statement

**`Conforms A M mode hdr f p code frame S`** says that the machine code `code`, run on the
machine model `M`, conforms to the ABI `A` as the function `f` of the C header `hdr`. The code
is called as `A` requires for the prototype `p` that `hdr` declares for `f`. Then:

* it never reaches a state `M` cannot step (it may diverge in `.safe` mode);
* every return is by `A`'s discipline;
* the result is one `A` reads back and the C-level spec `S` allows;
* it writes only memory that `S` or `A` gives it;
* it keeps the thread pointer;
* in `.total` mode, it returns.

Every ingredient is a definition the statement names. Nothing is an uninterpreted "conforms"
predicate, and no signature is attached to a symbol by hand:

| ingredient | what fixes it |
| --- | --- |
| the ABI | `A : AbiDef`: a versioned identity and source, a data model, the C → ABI lowering (`lower`, which refuses what it does not support), and a `Convention`. The convention gives `Entry` (argument placement, stack alignment, return address, direction flag, x87 mode, `%al` for varargs), `Return` (return address, `rsp + 8`, callee-saved registers, control state, FFI thread pointer) and `ResultAt` (result read-back) |
| the prototype | `declared`: the header files parse (`Data.Layout.Header.read`, which refuses incompatible redeclarations) to a header declaring `f` with a C prototype that `A.lower` maps to `p`. The prototype is a function of the header (`HeaderSrc.proto?`): the exact parsed one, with signedness and widths; its qualifiers are `HeaderSrc.quals?` (they do not change the lowering) |
| the code | `code : Code`: the bytes, where they are loaded, the entry offset, the function's extent, the read-only data it reads and the image's address ranges |
| admissible calls | `Admit`: a live machine state; `A.conv.Entry p a s`; the code and data placed, with the return address outside the code; the stack `A` gives the callee (`frame` bytes below `rsp`, the return address, the argument area); the FFI thread pointer equal to the machine's (`fsCoherent`). The stack must be readable, writable, and apart from the code, the data, the image and the call's caller-visible objects (`S.objects`). Also `S.pre a mem`: the C precondition, on the arguments and memory only |
| execution | `callModelOf M`: the **first return** of `M` (`FnContract.FirstReturn`) |
| no stuck state | `safe`: from every admitted call, every state before the return takes a step on `M` (`NoStuck`). Code using an instruction `M` does not model is stuck, so it does not conform in either mode (`Proofs….Negative`) |
| return | `Good`: `Return`; a result with `ResultAt` and `S.post`; memory written only inside `S.writes` or `Owned`: bounded memory that `Stack` admits (the row's `frame` bytes `[rsp − frame, rsp)`, which contain the red zone when `frame ≥ 128`; the argument area; `A.owned`). Nothing else below `rsp` is owned; the machine's FS base unchanged |
| non-vacuity | `nonvacuous`: some admitted call exists; `enterable`: for every argument tuple and caller memory the precondition admits (objects outside the code and its data), an admitted call with those arguments, the same objects and the same bytes on them; the rest of its memory is the ABI's. The precondition, shown with every row, is what restricts the claim |
| mode | `.total`: every admitted call returns. `.safe`: partial correctness, divergence allowed, stuck states not |

**The machine is a restricted model, and `sysvInt` a restricted fragment.** `M : Mach` is any
x86-64 segment machine on the integer state, and the standard ones (`Open`, `Open9`) decode an
integer subset of x86-64. A row is a statement about `M`. `sysvInt` is the INTEGER fragment of
the System V psABI (fixed-arity 4- and 8-byte integers and pointers), not the whole psABI.

**FP, vector and control state are preserved by construction, not proved.** `Ffi.State`'s
vector, x87, direction-flag, MXCSR and x87-control state is carried unchanged by `callModelOf`
(`Thms.callModelOf_carried`), so `Return`'s obligations about it hold *by the model*: a row
proves nothing about them for real x86. Those obligations are about real x86 only through `Faithful R M`: on a
reference machine `R`, each step `M` takes is the same step and leaves that state unchanged.
`Thms.Conforms.onRef` transfers a row to `R` under that assumption; nothing here proves it of
hardware. Because stuck states are excluded, an instruction outside `M` (SSE, x87, `std`,
`ldmxcsr`, `fldcw`, `bsr` on `Open`) makes a row unprovable, never vacuous.

**External calls and the runtime.** The machine is the only place behaviour comes from. On the
open machines there are no external calls: a call to code that is not loaded is stuck. A machine
whose steps include trusted callee contracts (`Silmaril.Elf.Link.Dyn.Proc`) makes those
contracts the explicit assumptions of every row stated on it.

**Header satisfaction.**
- `HeaderSatPartial`: a nonempty claimed part, every other declaration excluded for a checked
  reason (`unsupported`: the lowering refuses it; `absent`/`unclaimed`: checked against the
  file by the ELF form).
- `HeaderSatAvailable`: no `unclaimed` declaration, every claimed function total; `absent`
  declarations (compatible version gaps) allowed.
- `HeaderSatComplete`: available, with nothing absent: the whole header.

See `docs/projects/abi-conformance.md`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState Word Byte)
open Silmaril.Data.Layout (CTy DataModel)
open Silmaril.Data.Layout.Header (CProto Header)

/-! ## ABI definitions -/

/-- **An ABI definition**: what a conformance statement is judged against. -/
structure AbiDef where
  /-- Versioned identity, e.g. `x86_64-sysv-psabi@e1ce0983/lp64/integer`. -/
  id : String
  /-- The cited document, with its version. -/
  source : String
  /-- Sizes and alignments of C types. -/
  dm : DataModel
  V : Vocab
  D : Type
  /-- Argument placement, return discipline, result read-back. -/
  conv : Convention V Ffi.State D
  /-- The ABI's prototype for a C prototype, or the reason it is outside the ABI fragment. -/
  lower : CProto → Except String V.Proto
  /-- Bytes of the caller's frame the callee receives above its return address (incoming stack
  arguments, a shadow area), which it may read and write. -/
  argArea : V.Proto → Nat
  /-- Other memory the ABI gives the callee at entry `s` (sret storage). -/
  owned : V.Proto → Ffi.State → Nat → Prop

/-! ## The System V AMD64 INTEGER fragment -/

open Silmaril.C.Api (Scalar Signature)

/-- The `C.Api` scalar of a C type under a data model, or why it has none: the fragment has
4- and 8-byte integers and pointers. -/
def scalarOf (dm : DataModel) : CTy → Except String Scalar
  | .typedef _ t => scalarOf dm t
  | .ptr _ => .ok .pointer
  | .int k s => match dm.intShape k with
    | some ⟨4, _⟩ => .ok (if dm.isSigned k s then .int32 else .uint32)
    | some ⟨8, _⟩ => .ok (if dm.isSigned k s then .int64 else .uint64)
    | some ⟨n, _⟩ => .error s!"{n}-byte integer: outside the INTEGER fragment (4- and 8-byte integers and pointers)"
    | none => .error "integer kind without a size in the data model"
  | .bool => .error "_Bool: outside the INTEGER fragment (4- and 8-byte integers and pointers)"
  | .float _ => .error "floating type: SSE/x87 classes are outside the INTEGER fragment"
  | .struct t => .error s!"struct {t} by value: aggregates are outside the INTEGER fragment"
  | .union t => .error s!"union {t} by value: aggregates are outside the INTEGER fragment"
  | .enum t _ => .error s!"enum {t}: enumerations are outside the INTEGER fragment"
  | .array .. => .error "array object type"
  | .void => .error "void object type"

/-- The INTEGER-fragment prototype of a C prototype. -/
def lowerInt (dm : DataModel) (cp : CProto) : Except String Silmaril.Machine.Abi.SystemV.Proto :=
  if cp.variadic then .error "variadic: the %al count and va_list are outside the INTEGER fragment"
  else
    match Silmaril.Data.Layout.traverse (scalarOf dm) cp.params,
        (match cp.ret with
          | .void => (Except.ok none : Except String (Option Scalar))
          | t => some <$> scalarOf dm t) with
    | .error e, _ => .error e
    | _, .error e => .error s!"result: {e}"
    | .ok ps, .ok r =>
      if h : ps.length ≤ Silmaril.Machine.Abi.SystemV.maxArity then .ok ⟨⟨ps, r⟩, h⟩
      else .error "more than 127 parameters"

/-- **System V AMD64, INTEGER fragment**: fixed-arity prototypes of 4- and 8-byte integers and
pointers, planned by the psABI planner (`Machine.SystemV.Abi.plan`, which on this fragment is
`intPlan`), with the full `Ffi.Entry`/`Ffi.Return` discipline (`Machine.Abi.SystemV.sysv`).
Arguments past the sixth are 8-byte stack slots above the return address; the callee owns
that area. -/
def sysvInt : AbiDef where
  id := "x86_64-sysv-psabi@e1ce0983/lp64/integer"
  source := "System V Application Binary Interface, AMD64 Architecture Processor Supplement, \
    x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236, §3.2 (Function Calling \
    Sequence): register save and red zone (§3.2.1–3.2.2), parameter passing (§3.2.3)"
  dm := Silmaril.Data.Layout.sysvX86_64
  V := Silmaril.Machine.Abi.SystemV.vocab
  D := Silmaril.Machine.Abi.SystemV.CallSite
  conv := Silmaril.Machine.Abi.SystemV.sysv {}
  lower := lowerInt Silmaril.Data.Layout.sysvX86_64
  argArea p := 8 * (p.signature.arguments.length - 6)
  owned _ _ _ := False

/-! ## Code, machines, specs -/

/-- **The code of a function**: `bytes` loaded at `base`, entered at offset `off`; the function
itself is the `len` bytes from `off` (its symbol's extent). The other bytes are code it may
reach (a tail call, a shared epilogue). `data` are read-only data of the same image the code
reads at fixed addresses (a constant table); an admitted call has them loaded too. `image` is
every address range of the loaded image (code, read-only data, writable data, `.bss`), as
(start, length): the stack the ABI gives the callee must be apart from all of it. -/
structure Code where
  base : Word
  bytes : List Byte
  off : Nat
  len : Nat
  data : List (Word × List Byte) := []
  image : List (Word × Nat) := []

/-- The entry address. -/
def Code.entry (c : Code) : Word := c.base + BitVec.ofNat 64 c.off

/-- The code loaded `b` bytes above its link-time addresses (a load base). The bytes do not
change: a statement about the rebased code is about position-independent code whose bytes no
relocation patches (`Elf.Abi.Untouched`). -/
def Code.rebase (c : Code) (b : Nat) : Code where
  base := c.base + BitVec.ofNat 64 b
  bytes := c.bytes
  off := c.off
  len := c.len
  data := c.data.map fun d => (d.1 + BitVec.ofNat 64 b, d.2)
  image := c.image.map fun r => (r.1 + BitVec.ofNat 64 b, r.2)

/-- The machines conformance is stated on (`Mach`): x86-64 segment machines on the integer
open state. These are **restricted models**: the standard ones (`Open`, `Open9`, `Str9`) decode
an integer subset of x86-64 and have no SSE, x87, MXCSR or direction-flag instruction. A row on
`M` is a statement about `M`; reading it about real x86 needs `Faithful` (below). -/
abbrev Mach := Silmaril.X86.SegVC.Isa MState

/-- **The call relation of `M`**: the first return of the run from the entry state, with the
state the machine does not model (vectors, x87, control state, FFI thread pointer) carried. -/
def callModelOf (M : Mach) : Contracts.Model Ffi.State Ffi.State := fun s =>
  {t | Silmaril.X86.FnContract.FirstReturn M s.machine t.machine ∧ t = { s with machine := t.machine }}

/-- **No stuck state**: every state the machine reaches from `s` before the function returns,
and that is not the return, takes a step. A run may diverge; it may not get stuck (an
instruction outside the model, a fault, a fetch outside the code). -/
def NoStuck (M : Mach) (s : Ffi.State) : Prop :=
  ∀ m, Silmaril.X86.FnContract.RunsIn M (fun x => ¬ Silmaril.X86.FnContract.Returned M s.machine x)
      s.machine m → ¬ Silmaril.X86.FnContract.Returned M s.machine m → (M.step m).isSome

/-- **A C-level call spec** for prototype `p`.

* `objects a mem`: the caller-visible memory the call may access through its arguments
  (buffers, strings); the stack the ABI gives the callee is apart from it.
* `pre a mem`: the C precondition, on the arguments and memory only (validity of what pointers
  point to, absence of undefined behaviour). It cannot constrain registers, the stack pointer or
  the entry address: those are the ABI's (`Admit`).
* `writes a mem`: the caller-visible memory the call may write.
* `post a s r t`: the result `r` and the final state. -/
structure CallSpec (V : Vocab) (p : V.Proto) where
  objects : V.Args p → Silmaril.Process.Memory → Nat → Prop := fun _ _ _ => False
  pre : V.Args p → Silmaril.Process.Memory → Prop
  writes : V.Args p → Silmaril.Process.Memory → Nat → Prop := fun _ _ _ => False
  post : V.Args p → Ffi.State → V.Ret p → Ffi.State → Prop

/-- The spec of ABI conformance of a **pure** function: every call admitted, any result, no
caller-visible memory written. (A function with effects, `memset`, needs its `writes`.) -/
def CallSpec.abiPure (V : Vocab) (p : V.Proto) : CallSpec V p where
  pre _ _ := True
  post _ _ _ _ := True

/-- A value-level C contract (`Contracts.Contract`, as `Convention.translate` takes) as a spec
that writes nothing. -/
def CallSpec.ofContract {V : Vocab} {p : V.Proto}
    (c : Contracts.Contract (V.Args p) (Option (V.Ret p))) : CallSpec V p where
  pre a _ := c.pre a
  post a _ r _ := c.post a (some r)

/-- `.total`: every admitted call returns. `.safe`: partial correctness without getting stuck:
an admitted call may diverge, but never reaches a state the machine cannot step. -/
inductive Mode where
  | total
  | safe
  deriving DecidableEq, Repr

/-! ## The statement -/

/-- The stack pointer of an FFI state. -/
def sp (s : Ffi.State) : Nat := (s.machine.core.read .rsp).toNat

/-- `[lo, lo + n)` and `[lo', lo' + n')` are disjoint. -/
def Apart (lo n lo' n' : Nat) : Prop := lo + n ≤ lo' ∨ lo' + n' ≤ lo

/-- The code is placed: loaded, `rip` at the entry, the data loaded, the return address outside
the bytes. -/
structure Placed (c : Code) (s : Ffi.State) : Prop where
  loaded : Silmaril.X86.Ext.Loaded s.machine.memory c.base c.bytes
  pc : s.machine.core.rip = c.entry
  data : ∀ d ∈ c.data, Silmaril.X86.Ext.Loaded s.machine.memory d.1 d.2
  retOutside : ∀ o, o < c.bytes.length →
    Silmaril.X86.FnContract.retOf s.machine.core s.machine.memory ≠ c.base + BitVec.ofNat 64 o

/-- The stack the ABI gives the callee, `[sp − frame, sp + 8 + argArea)` (its frame, the return
address, its incoming arguments): in the address space, readable and writable, and apart from
the code, its data, the image and the caller-visible objects of the call. -/
structure Stack (A : AbiDef) (p : A.V.Proto) (c : Code) (frame : Nat) (objects : Nat → Prop)
    (s : Ffi.State) : Prop where
  room : frame ≤ sp s
  fits : sp s + 8 + A.argArea p ≤ 2 ^ 64
  read : s.machine.memory.Permitted .read (sp s - frame) (frame + 8 + A.argArea p)
  write : s.machine.memory.Permitted .write (sp s - frame) (frame + 8 + A.argArea p)
  apartCode : Apart c.base.toNat c.bytes.length (sp s - frame) (frame + 8 + A.argArea p)
  apartData : ∀ d ∈ c.data, Apart d.1.toNat d.2.length (sp s - frame) (frame + 8 + A.argArea p)
  apartImage : ∀ r ∈ c.image, Apart r.1.toNat r.2 (sp s - frame) (frame + 8 + A.argArea p)
  apartObjects : ∀ x, objects x → ¬ (sp s - frame ≤ x ∧ x < sp s + 8 + A.argArea p)

/-- **An admitted call** of the code with arguments `a` and spec `S`: a live machine state,
`A`'s entry obligations, the code placed, the stack, and the FFI thread pointer is the machine's
(`FsBase.FsCoherent`). -/
structure Admit (A : AbiDef) (M : Mach) (p : A.V.Proto) (c : Code) (frame : Nat)
    (S : CallSpec A.V p) (a : A.V.Args p) (s : Ffi.State) : Prop where
  live : M.live s.machine
  entry : A.conv.Entry p a s
  placed : Placed c s
  stack : Stack A p c frame (S.objects a s.machine.memory) s
  fsCoherent : s.fsBase = s.machine.core.fsBase

/-- The memory `A` gives a callee entered at `s`: the `frame` bytes below `rsp` (its frame,
including the red zone), its argument area above the return address, and `A.owned`. -/
def Owned (A : AbiDef) (p : A.V.Proto) (frame : Nat) (s : Ffi.State) (x : Nat) : Prop :=
  (sp s - frame ≤ x ∧ x < sp s) ∨ (sp s + 8 ≤ x ∧ x < sp s + 8 + A.argArea p) ∨ A.owned p s x

/-- **A conforming return** from `s` to `t` for arguments `a`: `A`'s return discipline, a
result `A` reads back that the spec allows, memory written only inside the spec's writes or the
owned memory, and the machine's FS base (the thread pointer `%fs:` reads) unchanged. -/
structure Good (A : AbiDef) (p : A.V.Proto) (frame : Nat) (S : CallSpec A.V p)
    (a : A.V.Args p) (s t : Ffi.State) : Prop where
  ret : A.conv.Return p s t
  result : ∃ r, A.conv.ResultAt p s t r ∧ S.post a s r t
  frame : s.machine.memory.WritesWithin t.machine.memory
    (fun x => S.writes a s.machine.memory x ∨ Owned A p frame s x)
  fsBase : t.machine.core.fsBase = s.machine.core.fsBase

/-- Header source files (name, text) and the file to read. -/
structure HeaderSrc where
  files : List (String × String)
  root : String

/-- The C prototype the header declares for `f`, if the header reads. -/
def HeaderSrc.proto? (hdr : HeaderSrc) (f : String) : Option CProto :=
  (Silmaril.Data.Layout.Header.read hdr.files hdr.root).toOption.bind (·.proto? f)

/-- The qualifiers the header writes in its prototype for `f`, if the header reads. -/
def HeaderSrc.quals? (hdr : HeaderSrc) (f : String) : Option Silmaril.Data.Layout.Header.ProtoQuals :=
  (Silmaril.Data.Layout.Header.read hdr.files hdr.root).toOption.bind (·.quals? f)

/-- `x` is outside the code's bytes and its read-only data: the addresses where an admitted
state's memory is fixed by the placement (`Placed`). -/
def Code.Outside (c : Code) (x : Nat) : Prop :=
  ¬ (c.base.toNat ≤ x ∧ x < c.base.toNat + c.bytes.length) ∧
    ∀ d ∈ c.data, ¬ (d.1.toNat ≤ x ∧ x < d.1.toNat + d.2.length)

/-- **The header declares `f` with a C prototype that `A` lowers to `p`.** The prototype `cp` is
the one `hdr.proto? f` gives (a function of the header), so it is unique. -/
def Declares (A : AbiDef) (hdr : HeaderSrc) (f : String) (p : A.V.Proto) : Prop :=
  ∃ cp, hdr.proto? f = some cp ∧ A.lower cp = .ok p

/-- **The code conforms to `A` on the machine `M`** as the function `f` of the header `hdr`,
with prototype `p`, `frame` bytes of stack and C-level spec `S`. Every admitted call has no
stuck state, and every first return is a conforming return; in `.total` mode every admitted
call returns. -/
structure Conforms (A : AbiDef) (M : Mach) (mode : Mode) (hdr : HeaderSrc) (f : String)
    (p : A.V.Proto) (c : Code) (frame : Nat) (S : CallSpec A.V p) : Prop where
  declared : Declares A hdr f p
  extent : c.off + c.len ≤ c.bytes.length
  nonvacuous : ∃ a s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory
  /-- **Every caller state the precondition admits is callable**: for every argument tuple `a`
  and caller memory `mem` meeting the precondition, whose caller-visible objects avoid the code
  and its read-only data (`Code.Outside`: there an admitted state's bytes are the code's), some
  admitted call has the arguments `a`, meets the precondition, has the same objects, and has
  `mem`'s bytes on them (for example, every buffer content). The rest of its memory (code,
  stack, permissions) is the ABI's. A row cannot be non-vacuous through one hand-picked call
  while its precondition admits others. -/
  enterable : ∀ a mem, S.pre a mem → (∀ x, S.objects a mem x → c.Outside x) →
    ∃ s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory ∧
      (∀ x, S.objects a s.machine.memory x ↔ S.objects a mem x) ∧
      ∀ x, S.objects a mem x → s.machine.memory.bytes[x]? = mem.bytes[x]?
  safe : ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory → NoStuck M s
  progress : mode = .total → ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory →
    (callModelOf M s).Nonempty
  sound : ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory →
    ∀ t ∈ callModelOf M s, Good A p frame S a s t

/-! ## Real x86: faithfulness of the machine -/

/-- **A reference machine** on the whole FFI state (vectors, x87, control state, thread pointer
included): a finer model of x86-64, or hardware observed by a differential-testing oracle. -/
structure Ref where
  step : Ffi.State → Option Ffi.State

/-- **`M` is faithful to the reference `R`**: wherever `M` takes a step, `R` takes the same step
on the integer state and leaves the state `M` does not model unchanged. For the standard
integer machines this is the claim that each instruction they decode is executed by real x86 as
they say and touches no vector, x87 or control state; it is an **assumption** of every
real-x86 reading of a row, not proved here. -/
def Faithful (R : Ref) (M : Mach) : Prop :=
  ∀ s m', M.step s.machine = some m' → R.step s = some { s with machine := m' }

/-- Runs of the reference machine taking every step from a state satisfying `P`. -/
inductive Ref.RunsIn (R : Ref) (P : Ffi.State → Prop) : Ffi.State → Ffi.State → Prop
  | refl (s : Ffi.State) : R.RunsIn P s s
  | step {s s' t : Ffi.State} : P s → R.step s = some s' → R.RunsIn P s' t → R.RunsIn P s t

/-- The first returns of the reference machine (returned as for `M`). -/
def Ref.callModel (R : Ref) (M : Mach) : Contracts.Model Ffi.State Ffi.State := fun s =>
  {t | R.RunsIn (fun x => ¬ Silmaril.X86.FnContract.Returned M s.machine x.machine) s t ∧
    Silmaril.X86.FnContract.Returned M s.machine t.machine}

/-! ## Header satisfaction -/

/-- Why a declaration of a header is not claimed for a binary. -/
inductive Exclusion where
  /-- The ABI's lowering refuses the prototype (checked; `why` summarizes `A.lower`'s message). -/
  | unsupported (why : String)
  /-- The binary does not define the function (an API version gap; checked against the file
  by the ELF form). -/
  | absent (why : String)
  /-- Defined and in the fragment, but not claimed (for instance: the machine model lacks an
  instruction the code uses). The ELF form checks that the function is present. -/
  | unclaimed (why : String)
  deriving DecidableEq, Repr

/-- **A coverage declaration** for a header and a binary: the claimed functions, and every
other declared function with its exclusion. -/
structure Coverage where
  claimed : List String
  excluded : List (String × Exclusion)
  deriving DecidableEq, Repr

/-- The coverage accounts for the header: every declared name is claimed or excluded, not both,
and nothing else is listed. -/
def Coverage.Complete (cov : Coverage) (H : Header) : Prop :=
  (∀ f ∈ H.names, f ∈ cov.claimed ∨ f ∈ cov.excluded.map (·.1)) ∧
  (∀ f ∈ cov.claimed, f ∈ H.names ∧ f ∉ cov.excluded.map (·.1)) ∧
  (∀ f ∈ cov.excluded.map (·.1), f ∈ H.names)

instance (cov : Coverage) (H : Header) : Decidable (cov.Complete H) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Every `unsupported` exclusion is refused by the lowering. -/
def Coverage.refusalsOk (A : AbiDef) (cov : Coverage) (H : Header) : Bool :=
  cov.excluded.all fun (f, e) => match e with
    | .unsupported _ => match H.proto? f with
      | some cp => (match A.lower cp with | .error _ => true | .ok _ => false)
      | none => false
    | _ => true

/-- **The coverage is checked against the header** (a computation): the header reads, the
coverage is complete, and the `unsupported` exclusions are refused by the lowering. -/
def Coverage.check (A : AbiDef) (hdr : HeaderSrc) (cov : Coverage) : Bool :=
  match Silmaril.Data.Layout.Header.read hdr.files hdr.root with
  | .ok H => decide (cov.Complete H) && cov.refusalsOk A H
  | .error _ => false

/-- No declaration is left `unclaimed`: every one is claimed, refused by the ABI, or absent (a
compatible version gap). -/
def Coverage.available (cov : Coverage) : Bool :=
  cov.excluded.all fun (_, e) => match e with | .unclaimed _ => false | _ => true

/-- Every declaration is claimed or refused by the ABI: none is absent, none unclaimed (the whole
API surface the ABI can express is provided and claimed). -/
def Coverage.complete (cov : Coverage) : Bool :=
  cov.excluded.all fun (_, e) => match e with | .unsupported _ => true | _ => false

/-- **A binary's functions for a header**: for each claimed name, its code, frame, spec and
mode (the prototype is the header's). -/
structure Impl (A : AbiDef) where
  proto : A.V.Proto
  code : Code
  frame : Nat
  spec : CallSpec A.V proto
  mode : Mode

/-- **The binary satisfies a part of the header** (partial header satisfaction): at least one
function is claimed, the coverage is checked against the header, and every claimed function
has an implementation that conforms. The claimed and excluded lists are the statement's
content: this says nothing about the excluded functions. -/
def HeaderSatPartial (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage)
    (impl : String → Option (Impl A)) : Prop :=
  cov.claimed ≠ [] ∧ cov.check A hdr = true ∧
  ∀ f ∈ cov.claimed, ∃ i, impl f = some i ∧
    Conforms A M i.mode hdr f i.proto i.code i.frame i.spec

/-- **The binary satisfies every function of the header it provides** (available header
satisfaction): partial satisfaction with no `unclaimed` declaration and every claimed function
total. Declarations the binary does not define (`absent`: a compatible version gap, checked
against the file by the ELF form) are allowed and are part of the statement. -/
def HeaderSatAvailable (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage)
    (impl : String → Option (Impl A)) : Prop :=
  HeaderSatPartial A M hdr cov impl ∧ cov.available = true ∧
  ∀ f ∈ cov.claimed, ∃ i, impl f = some i ∧ i.mode = .total

/-- **The binary satisfies the whole header** (complete header satisfaction): available header
satisfaction with nothing absent: every declaration is claimed (total) or refused by the ABI's
lowering. -/
def HeaderSatComplete (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage)
    (impl : String → Option (Impl A)) : Prop :=
  HeaderSatAvailable A M hdr cov impl ∧ cov.complete = true

end Silmaril.Machine.Abi.Conformance

end
