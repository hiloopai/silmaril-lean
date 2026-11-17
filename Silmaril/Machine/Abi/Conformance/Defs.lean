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
| the ABI | `A : AbiDef`: a versioned identity and source, a data model, the C → ABI lowering (`lower`, which refuses what it does not support; it reads struct and union definitions from the tag definitions of the header, `Header.env`), a `Convention` and an entry environment. The convention gives `Entry` (argument placement, stack alignment, return address, direction flag, x87 mode, `%al` for varargs), `Return` (return address, `rsp + 8`, callee-saved registers, the MXCSR control bits and x87 control word preserved, the MXCSR status flags free, direction flag clear, x87 mode, FFI thread pointer) and `ResultAt` (result read-back). `EntryEnv` constrains the MXCSR and x87 control word at entry, and nothing else: `True` for `sysvInt`, `sysvScalar`, `win64Int` (their conventions let a caller enter with any control bits); an ABI requiring the default MXCSR control bits (`MXCSR &&& 0xffc0 = 0x1F80`; the sticky status flags free) is a **default-environment subset** (`AbiDef.defaultEnv`) |
| the prototype | `declared`: the header files parse (`Data.Layout.Header.read`, which refuses incompatible redeclarations) to a header declaring `f` with a C prototype that `A.lower` maps to `p`, with the tag definitions of **that** header (`HeaderSrc.env`: a by-value `struct T` is the `T` the same header defines). The prototype is a function of the header (`HeaderSrc.proto?`): the exact parsed one, with signedness and widths; its qualifiers are `HeaderSrc.quals?` (they do not change the lowering) |
| the code | `code : Code`: the bytes, where they are loaded, the entry offset, the function's extent, the read-only data it reads and the image's address ranges |
| admissible calls | `Admit`: every admissible completion of the entry state live; `A.conv.Entry p a s`; the entry environment `A.EntryEnv`; the code and data placed, with the return address outside the code; the memory `A` gives the callee (`Stack`: `frame` bytes below `rsp`, the return address, the argument area, and `A.owned`, the storage of a MEMORY result); the FFI thread pointer equal to the machine's (`fsCoherent`). The stack window must be readable, writable, and apart from the code, the data, the image and the call's caller-visible objects (`S.objects`); every byte of `A.owned` readable, writable, and apart from the stack window, the code, the data, the image and `S.objects`. Also `S.pre a mem`: the C precondition, on the arguments and memory only |
| the machine | `M : Mach`: a segment machine `M.isa` on its own state `M.σ`; the FFI fields it **models** (`M.models`, always including `.machine`), the rest carried; what a machine state says about them (`M.view`); and its **admissible completions** of an FFI state (`M.Fills s x`: `x` agrees with `s` on the modelled fields, so its core and memory are `s.machine`'s, and holds anything else hardware may present; every FFI state has one). A machine state is written back by `M.store s y = overwrite M.models s (M.view y)`, a definition: the modelled fields from `y`, the others from `s`. An integer machine on `MState` is `Mach.ofInt I`: it models `.machine` only, and its one completion of `s` is `s.machine` |
| execution | `callModelOf M`: the **first returns** of `M.isa` (`FnContract.FirstReturn`) from **every** completion of `s`, stored back into `s` (`Mach.store`; `callFrom` for one completion) |
| no stuck state | `safe`: from every completion of every admitted call, every state before the return takes a step on `M` (`NoStuck`). Code using an instruction `M` does not model is stuck, so it does not conform in either mode (`Proofs….Negative`) |
| return | `Good`: `Return`; a result with `ResultAt` and `S.post`; memory written only inside `S.writes` or `Owned`: the memory `Stack` admits (the row's `frame` bytes `[rsp − frame, rsp)`, which contain the red zone when `frame ≥ 128`; the argument area; `A.owned`, each byte of which `Stack` requires readable, writable and apart from the rest). Nothing else below `rsp` is owned; the machine's FS base unchanged |
| non-vacuity | `nonvacuous`: some admitted call exists; `enterable`: for every argument tuple and caller memory the precondition admits (objects outside the code and its data), an admitted call with those arguments, the same objects and the same bytes on them; the rest of its memory is the ABI's. The precondition, shown with every row, is what restricts the claim |
| mode | `.total`: every admitted call returns, from every completion. `.safe`: partial correctness, divergence allowed, stuck states not |

**The machine is a restricted model, and `sysvInt` a restricted fragment.** `M : Mach` is any
x86-64 segment machine with a modelled/carried split of the FFI state; the standard ones
(`Mach.ofInt` of `Open.isa`, `Open9.isa`) are integer machines on `MState` and decode an
integer subset of x86-64. A row is a statement about `M`. `sysvInt` is the INTEGER fragment of
the System V psABI (fixed-arity 4- and 8-byte integers and pointers), not the whole psABI.

**FP, vector and control state are preserved by construction, not proved.** On an integer
machine (`Mach.ofInt`), `Ffi.State`'s vector, x87, direction-flag, MXCSR and x87-control state
is carried unchanged by `callModelOf` (`Thms.callModelOf_carried`), so `Return`'s obligations
about it hold *by the model*: a row proves nothing about them for real x86. Those obligations
are about real x86 only through `Faithful R M`: on a reference machine `R`, each step `M` takes
is the same step and leaves that state unchanged.
`Thms.Conforms.onRef` transfers a row to `R` under that assumption; nothing here proves it of
hardware. Because stuck states are excluded, an instruction outside `M` (SSE, x87, `std`,
`ldmxcsr`, `fldcw`, `bsr` on `Open`) makes a row unprovable, never vacuous. A machine that
models more of the state (SSE registers, MXCSR) lists those fields in `models`, and its rows
prove `Return`'s obligations about them rather than carrying them; a field it does not list is
carried by the definition of `store` (`Thms.Mach.store_carried`), so no machine can make an
obligation hold by its write-back alone (`Lens.Thms.launder_not_store`). State the FFI state
does not determine (a time-stamp oracle) is quantified over: every row covers every admissible
completion (`Mach.Fills`). Which MXCSR and x87 control modes an admitted call may start in is
the ABI's entry environment (`AbiDef.EntryEnv`), shown with every row and never part of a
machine. The psABI lets callers enter with any control bits, so the full conventions here
admit every mode; a row that requires the default MXCSR control bits
(`MXCSR &&& 0xffc0 = 0x1F80`, any status flags) is about a
**default-environment subset** (`AbiDef.defaultEnv`), not full System V. `Return` follows the
psABI (§3.2.1, "Registers and the Stack Frame"): the MXCSR control bits (6–15) and the x87
control word are preserved, the MXCSR status flags (0–5) are not constrained, the direction
flag is clear and the CPU is in x87 mode.

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
  /-- The ABI's prototype for a C prototype whose struct and union tags are defined in `env`
  (the header's tag definitions, `Header.env`), or the reason it is outside the ABI
  fragment. -/
  lower : Silmaril.Data.Layout.Env → CProto → Except String V.Proto
  /-- Bytes of the caller's frame the callee receives above its return address (incoming stack
  arguments, a shadow area), which it may read and write. -/
  argArea : V.Proto → Nat
  /-- Other memory the ABI gives the callee at entry `s` (sret storage). -/
  owned : V.Proto → Ffi.State → Nat → Prop
  /-- **The entry environment**: what an admitted call's floating-point control state may be at
  entry, as a predicate on exactly the **MXCSR** (rounding mode, exception masks, DAZ, FTZ,
  and its status flags) and the **x87 control word**. Its type is its scope: it cannot
  constrain arguments, registers, memory or the other FFI fields (those are `conv.Entry`'s,
  which already fixes the direction flag and x87 mode at entry). `True` for an ABI that, like
  the System V psABI and Microsoft x64, lets a caller enter with any control bits. An ABI
  definition that requires the default environment (MXCSR control bits `0x1F80`) is a
  **default-environment subset**, not the full convention (`AbiDef.defaultEnv`). -/
  EntryEnv : BitVec 32 → BitVec 16 → Prop

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
that area. Every entry environment is admitted (`EntryEnv` is `True`): the psABI lets a caller
enter with any MXCSR and x87 control bits. -/
def sysvInt : AbiDef where
  id := "x86_64-sysv-psabi@e1ce0983/lp64/integer"
  source := "System V Application Binary Interface, AMD64 Architecture Processor Supplement, \
    x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236, §3.2 (Function Calling \
    Sequence): register save and red zone (§3.2.1–3.2.2), parameter passing (§3.2.3)"
  dm := Silmaril.Data.Layout.sysvX86_64
  V := Silmaril.Machine.Abi.SystemV.vocab
  D := Silmaril.Machine.Abi.SystemV.CallSite
  conv := Silmaril.Machine.Abi.SystemV.sysv {}
  lower _ := lowerInt Silmaril.Data.Layout.sysvX86_64
  argArea p := 8 * (p.signature.arguments.length - 6)
  owned _ _ _ := False
  EntryEnv _ _ := True

/-- **The default-environment subset of `A`**: `A` with calls admitted only when they enter
with the default MXCSR **control bits** (bits 6–15 of `0x1F80`: round to nearest, every
exception masked, DAZ and FTZ off), labelled as such in its identity. The status flags (bits
0–5) are free: they are sticky, so an ordinary caller's MXCSR is `0x1F80` only until its first
inexact operation (`0x1FA0` after `1.0/3.0`), and `Return` leaves them free too. The reserved
bits 16–31 are not constrained (hardware keeps them zero). A row stated on it covers only callers in the default floating-point
control environment; the full System V and Microsoft conventions let a caller enter with other
control bits. -/
def AbiDef.defaultEnv (A : AbiDef) : AbiDef :=
  { A with
    id := A.id ++ "/default-env-subset"
    EntryEnv := fun mxcsr x87Control =>
      A.EntryEnv mxcsr x87Control ∧ mxcsr &&& 0xffc0 = 0x1F80 }

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

/-- **The fields of the FFI state** (`Ffi.State`), named so that a machine can list the ones it
models (`Mach.models`). -/
inductive FfiField where
  | machine
  | vectors
  | x87
  | direction
  | x87Mode
  | mxcsr
  | x87Control
  | fsBase
  deriving DecidableEq, Repr

/-- `s` and `t` agree on the field `f`. -/
def FfiField.Agree : FfiField → Ffi.State → Ffi.State → Prop
  | .machine, s, t => s.machine = t.machine
  | .vectors, s, t => s.vectors = t.vectors
  | .x87, s, t => s.x87 = t.x87
  | .direction, s, t => s.direction = t.direction
  | .x87Mode, s, t => s.x87Mode = t.x87Mode
  | .mxcsr, s, t => s.mxcsr = t.mxcsr
  | .x87Control, s, t => s.x87Control = t.x87Control
  | .fsBase, s, t => s.fsBase = t.fsBase

/-- **`overwrite F s u`**: the fields `F` selects taken from `u`, every other field from `s`. For
a fixed `F` this is the `merge` of a very well-behaved lens on `Ffi.State` whose part is the
`F` fields: `overwrite F s s = s`, the `F` fields of `overwrite F s u` are `u`'s, and
`overwrite F (overwrite F s u) w = overwrite F s w` (`Thms.overwrite_self`,
`Thms.overwrite_agree`, `Thms.overwrite_overwrite`). The fields outside `F` are `s`'s
(`Thms.overwrite_carried`): nothing else can write them. -/
def overwrite (F : FfiField → Bool) (s u : Ffi.State) : Ffi.State where
  machine := bif F .machine then u.machine else s.machine
  vectors := bif F .vectors then u.vectors else s.vectors
  x87 := bif F .x87 then u.x87 else s.x87
  direction := bif F .direction then u.direction else s.direction
  x87Mode := bif F .x87Mode then u.x87Mode else s.x87Mode
  mxcsr := bif F .mxcsr then u.mxcsr else s.mxcsr
  x87Control := bif F .x87Control then u.x87Control else s.x87Control
  fsBase := bif F .fsBase then u.fsBase else s.fsBase

/-- **The machines conformance is stated on** (`Mach`): an x86-64 segment machine `isa` on a
state `σ`, the FFI fields it **models** (`models`, which always include `.machine`: the core
and memory every other ingredient reads), what a machine state says about them (`view`), and
its **admissible completions** (`Fills`).

* **What a return writes (no laundering).** A machine state `y` is written back into the entry's
  FFI state `s` by `Mach.store s y := overwrite models s (view y)`: the modelled fields come
  from `y`, every other field is `s`'s. `store` is a definition, not a field, so it cannot
  supply a value the machine never computed: a field outside `models` is **carried**
  (`Thms.Mach.store_carried`), and a modelled field of `store s y` is a function of `y` alone.
  `models` is the per-machine list of what a row proves rather than carries; for
  `Mach.ofInt` it is `.machine` alone (`Thms.ofInt_models`). A machine whose state is fixed by
  its core and memory models nothing else (`Lens.Thms.models_eq_machine`), so its store keeps
  the direction flag, x87 mode, MXCSR and the rest; the laundering lens of the #994 review is
  the store of no `Mach` (`Lens.Thms.launder_not_store`).
* **Every admissible completion.** `Fills s x` says that `x` is a machine state hardware may
  present for the FFI state `s`: it agrees with `s` on every modelled field (`fills_agree`,
  so its core and memory are `s.machine`'s) and may hold anything the FFI state does not
  determine (a time-stamp oracle, a hidden profile). Every FFI state has one (`fills_total`):
  a machine is required to represent every FFI state, so no admitted call has its claims
  emptied by the absence of a completion. `Admit.live`, `NoStuck`, `callModelOf` and
  `Conforms.progress` quantify over **every** `x` with `Fills s x`: a row holds for each
  completion, not for one chosen by the machine. `Fills` is part of the machine, shown with
  every row; for `Mach.ofInt` it is `x = s.machine` (`Thms.ofInt_fills`). It is trusted like
  `isa`: a `Fills` narrower than "agrees with `s` on the modelled fields" (a fixed oracle, one
  profile) narrows every row on the machine, and the machine's documentation must say so.
* **Faithfulness over reachable completions.** `Faithful` constrains the reference machine only
  at states reached from a completion, and the reference machine is a relation, so a step that
  reads hidden state (an `rdtsc` oracle) does not make it unsatisfiable
  (`Lens.Thms.tsc_faithful`).

These are **restricted models**: the standard ones (`Mach.ofInt Open.isa`, `Mach.ofInt
Open9.isa`, `Mach.ofInt Str9.isa`) decode an integer subset of x86-64 and have no SSE, x87,
MXCSR or direction-flag instruction. A row on `M` is a statement about `M`; reading it about
real x86 needs `Faithful` (below).

`view x` is read only on the modelled fields (`store` takes the others from `s`). Within a
call, runs stay in `σ` and `store` is applied once, against the entry state; composing two
calls (`Fills (store s y)`) admits every completion again, so hidden state is not carried
from one call to the next unless a theorem chaining calls says so. -/
structure Mach where
  /-- The machine's state. -/
  σ : Type
  /-- The machine. -/
  isa : Silmaril.X86.SegVC.Isa σ
  /-- The FFI fields the machine models. The others are carried by `store`. -/
  models : FfiField → Bool
  models_machine : models .machine = true
  /-- The FFI state a machine state stands for, read on the modelled fields only. -/
  view : σ → Ffi.State
  machine_view : ∀ x, (view x).machine = ⟨isa.core x, isa.mem x⟩
  /-- The admissible completions of an FFI state: the machine states hardware may present
  for it. -/
  Fills : Ffi.State → σ → Prop
  fills_agree : ∀ {s x}, Fills s x → ∀ f, models f = true → f.Agree (view x) s
  fills_total : ∀ s, ∃ x, Fills s x

/-- **Write a machine state back** into an FFI state: the modelled fields from `x`, the others
from `s` (`overwrite`). -/
def Mach.store (M : Mach) (s : Ffi.State) (x : M.σ) : Ffi.State :=
  overwrite M.models s (M.view x)

/-- **`M`'s completions are all the states that fit**: every machine state agreeing with `s` on
the modelled fields completes `s`. `Fills` is trusted like `isa`, and nothing in `Mach` forces
this: a narrower `Fills` (a fixed oracle value, a single profile) narrows every row on `M`
silently. A row on a machine that does not satisfy `FillsAll` must say what its `Fills` fixes.
It holds for the integer machines (`Thms.ofInt_fillsAll`) and for `Lens.tsc`
(`Lens.tsc_fillsAll`).

Hidden state must also be as fine-grained as the hardware's nondeterminism. A time-stamp
oracle that is one constant per run, read twice (`rdtsc; rdtsc`), is not faithful to a
reference that returns a fresh value each time: `Faithful.bwd` asks for a single run. `onRef`
then never applies, which is vacuous, not unsound; a per-step stream oracle avoids it. (`Lens.tsc`
reads once; the two-read case is argued here, not yet a kernel-checked example.) -/
def Mach.FillsAll (M : Mach) : Prop :=
  ∀ s x, (∀ f, M.models f = true → f.Agree (M.view x) s) → M.Fills s x

/-- **An integer machine** (on `MState`, whose core and memory are the state's) as a `Mach`:
it models `.machine` only, and its one completion of `s` is `s.machine`, so the rest of the
FFI state (vectors, x87, control state, thread pointer) is carried unchanged by `callModelOf`
(`Thms.callModelOf_carried`). The side conditions hold by `rfl` for the standard machines. -/
def Mach.ofInt (I : Silmaril.X86.SegVC.Isa MState)
    (hc : ∀ m, I.core m = m.core := by intro _; rfl)
    (hm : ∀ m, I.mem m = m.memory := by intro _; rfl) : Mach where
  σ := MState
  isa := I
  models
    | .machine => true
    | _ => false
  models_machine := rfl
  view m := ⟨m, fun _ => 0, fun _ => 0, false, true, 0, 0, 0⟩
  machine_view x := by rw [hc, hm]
  Fills s m := m = s.machine
  fills_agree {s _} h f hf := by
    subst h
    cases f <;> first | rfl | cases hf
  fills_total s := ⟨s.machine, rfl⟩

/-- **The first returns of `M` from the completion `x`** of the FFI state `s`, stored back
into `s` (`Mach.store`). -/
def callFrom (M : Mach) (s : Ffi.State) (x : M.σ) : Set Ffi.State :=
  {t | ∃ y, Silmaril.X86.FnContract.FirstReturn M.isa x y ∧ t = M.store s y}

/-- **The call relation of `M`**: the first returns from **every** admissible completion of
the entry state (`Mach.Fills`), stored back into it. For an integer machine (`Mach.ofInt`),
the state the machine does not model (vectors, x87, control state, FFI thread pointer) is
carried. -/
def callModelOf (M : Mach) : Contracts.Model Ffi.State Ffi.State := fun s =>
  {t | ∃ x, M.Fills s x ∧ t ∈ callFrom M s x}

/-- **No stuck state**: from every admissible completion of `s`, every state the machine
reaches before the function returns, and that is not the return, takes a step. A run may
diverge; it may not get stuck (an instruction outside the model, a fault, a fetch outside the
code). -/
def NoStuck (M : Mach) (s : Ffi.State) : Prop :=
  ∀ x, M.Fills s x → ∀ y, Silmaril.X86.FnContract.RunsIn M.isa
      (fun z => ¬ Silmaril.X86.FnContract.Returned M.isa x z) x y →
    ¬ Silmaril.X86.FnContract.Returned M.isa x y → (M.isa.step y).isSome

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

/-- **The memory the ABI gives the callee** at entry `s`:
* the stack window `[sp − frame, sp + 8 + argArea)` (its frame, the return address, its
  incoming arguments): in the address space, readable and writable, and apart from the code,
  its data, the image and the caller-visible objects of the call;
* every byte of `A.owned` (the storage of a MEMORY result at the hidden pointer, under
  `sysvScalar`): readable and writable, and apart from the stack window, the code, its data,
  the image and the caller-visible objects. This is the psABI's guarantee that the caller
  provides the result storage (§3.2.3: "the caller provides space for the return value"),
  which the callee writes; that the storage does not alias anything else the call sees is a
  requirement on admitted calls, not something the callee could check.

Apartness from the image also excludes result storage inside the loaded image's own ranges: in
a statically linked program a caller may pass the address of a file-local static as the hidden
pointer. Rows do not cover such calls; the claim is narrower, not unsound. -/
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
  ownedRead : ∀ x, A.owned p s x → s.machine.memory.Permitted .read x 1
  ownedWrite : ∀ x, A.owned p s x → s.machine.memory.Permitted .write x 1
  ownedApartStack : ∀ x, A.owned p s x → ¬ (sp s - frame ≤ x ∧ x < sp s + 8 + A.argArea p)
  ownedApartCode : ∀ x, A.owned p s x → ¬ (c.base.toNat ≤ x ∧ x < c.base.toNat + c.bytes.length)
  ownedApartData : ∀ x, A.owned p s x → ∀ d ∈ c.data, ¬ (d.1.toNat ≤ x ∧ x < d.1.toNat + d.2.length)
  ownedApartImage : ∀ x, A.owned p s x → ∀ r ∈ c.image, ¬ (r.1.toNat ≤ x ∧ x < r.1.toNat + r.2)
  ownedApartObjects : ∀ x, A.owned p s x → ¬ objects x

/-- **An admitted call** of the code with arguments `a` and spec `S`: every admissible
completion of the entry state is live, `A`'s entry obligations and entry environment, the code
placed, the stack, and the FFI thread pointer is the machine's (`FsBase.FsCoherent`). -/
structure Admit (A : AbiDef) (M : Mach) (p : A.V.Proto) (c : Code) (frame : Nat)
    (S : CallSpec A.V p) (a : A.V.Args p) (s : Ffi.State) : Prop where
  live : ∀ x, M.Fills s x → M.isa.live x
  entry : A.conv.Entry p a s
  /-- The entry environment (`AbiDef.EntryEnv`): `True` for the full conventions. -/
  env : A.EntryEnv s.mxcsr s.x87Control
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

/-- The tag definitions of the header (`Header.env`), if the header reads; none otherwise. The
lowering reads by-value structs and unions there (`Declares`, `Coverage.refusalsOk`). -/
def HeaderSrc.env (hdr : HeaderSrc) : Silmaril.Data.Layout.Env :=
  match Silmaril.Data.Layout.Header.read hdr.files hdr.root with
  | .ok H => H.env
  | .error _ => []

/-- The qualifiers the header writes in its prototype for `f`, if the header reads. -/
def HeaderSrc.quals? (hdr : HeaderSrc) (f : String) : Option Silmaril.Data.Layout.Header.ProtoQuals :=
  (Silmaril.Data.Layout.Header.read hdr.files hdr.root).toOption.bind (·.quals? f)

/-- `x` is outside the code's bytes and its read-only data: the addresses where an admitted
state's memory is fixed by the placement (`Placed`). -/
def Code.Outside (c : Code) (x : Nat) : Prop :=
  ¬ (c.base.toNat ≤ x ∧ x < c.base.toNat + c.bytes.length) ∧
    ∀ d ∈ c.data, ¬ (d.1.toNat ≤ x ∧ x < d.1.toNat + d.2.length)

/-- **The header declares `f` with a C prototype that `A` lowers to `p`.** The prototype `cp` is
the one `hdr.proto? f` gives (a function of the header), so it is unique, and it is lowered with
the tag definitions of the same header (`hdr.env`), so a by-value `struct T` is laid out as that
header defines `T`. -/
def Declares (A : AbiDef) (hdr : HeaderSrc) (f : String) (p : A.V.Proto) : Prop :=
  ∃ cp, hdr.proto? f = some cp ∧ A.lower hdr.env cp = .ok p

/-- **The code conforms to `A` on the machine `M`** as the function `f` of the header `hdr`,
with prototype `p`, `frame` bytes of stack and C-level spec `S`. Every admitted call has no
stuck state from any admissible completion of its entry state (`Mach.Fills`), and every first
return from any completion is a conforming return; in `.total` mode every admitted call returns
from every completion. -/
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
    ∀ x, M.Fills s x → (callFrom M s x).Nonempty
  sound : ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory →
    ∀ t ∈ callModelOf M s, Good A p frame S a s t

/-! ## Real x86: faithfulness of the machine -/

/-- **A reference machine** on the whole FFI state (vectors, x87, control state, thread pointer
included): a finer model of x86-64, or hardware observed by a differential-testing oracle. It is
a relation: a step that reads state outside `Ffi.State` (a time-stamp counter) may have several
outcomes. A deterministic one is `Ref.ofFun`. -/
structure Ref where
  Step : Ffi.State → Ffi.State → Prop

/-- A deterministic reference machine. -/
def Ref.ofFun (step : Ffi.State → Option Ffi.State) : Ref := ⟨fun s t => step s = some t⟩

/-- `t` has returned from the call entered at `s`: `rip` at `s`'s return address and `rsp`
popped past it (`FnContract.Returned`, read on the FFI states). -/
def ReturnedAt (s t : Ffi.State) : Prop :=
  t.machine.core.rip = Silmaril.X86.FnContract.retOf s.machine.core s.machine.memory ∧
    t.machine.core.read .rsp = s.machine.core.read .rsp + 8#64

/-- **`M` is faithful to the reference `R`**, at the states `M` reaches from an admissible
completion `x` of an FFI state `s` (states `M` never reaches from a completion are not
constrained):
* `fwd`: where `M` steps from `y` to `y'`, `R` can step from `M.store s y` to `M.store s y'`;
* `bwd`: where `M` steps from `y`, every step of `R` from `M.store s y` is a step `M` takes
  from a state `y'` with the same FFI state, reached from some completion of `s` along a run
  with the same guard (`Q`, a predicate on the FFI states of the run). The completion may
  differ from `x`: a step that reads hidden state (`rdtsc`) is matched by the completion that
  holds the value `R` produced.

For the standard integer machines this is the claim that each instruction they decode is
executed by real x86 as they say and touches no vector, x87 or control state
(`Thms.faithful_ofInt_iff`); it is an **assumption** of every real-x86 reading of a row, not
proved here. -/
structure Faithful (R : Ref) (M : Mach) : Prop where
  fwd : ∀ s x, M.Fills s x → ∀ y y',
    Silmaril.X86.FnContract.RunsIn M.isa (fun _ => True) x y →
    M.isa.step y = some y' → R.Step (M.store s y) (M.store s y')
  bwd : ∀ (Q : Ffi.State → Prop) s x y, M.Fills s x →
    Silmaril.X86.FnContract.RunsIn M.isa (fun z => Q (M.store s z)) x y →
    (M.isa.step y).isSome → ∀ t, R.Step (M.store s y) t →
    ∃ x' y' y'', M.Fills s x' ∧
      Silmaril.X86.FnContract.RunsIn M.isa (fun z => Q (M.store s z)) x' y' ∧
      M.store s y' = M.store s y ∧ M.isa.step y' = some y'' ∧ t = M.store s y''

/-- Runs of the reference machine taking every step from a state satisfying `P`. -/
inductive Ref.RunsIn (R : Ref) (P : Ffi.State → Prop) : Ffi.State → Ffi.State → Prop
  | refl (s : Ffi.State) : R.RunsIn P s s
  | step {s s' t : Ffi.State} : P s → R.Step s s' → R.RunsIn P s' t → R.RunsIn P s t

/-- The first returns of the reference machine (`ReturnedAt`). -/
def Ref.callModel (R : Ref) : Contracts.Model Ffi.State Ffi.State := fun s =>
  {t | R.RunsIn (fun u => ¬ ReturnedAt s u) s t ∧ ReturnedAt s t}

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

/-- Every `unsupported` exclusion is refused by the lowering (with the header's tag
definitions). -/
def Coverage.refusalsOk (A : AbiDef) (cov : Coverage) (H : Header) : Bool :=
  cov.excluded.all fun (f, e) => match e with
    | .unsupported _ => match H.proto? f with
      | some cp => (match A.lower H.env cp with | .error _ => true | .ok _ => false)
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
