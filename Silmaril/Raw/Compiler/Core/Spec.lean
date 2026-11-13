module

public import Silmaril.Cerberus.Core.Dynamics.Defs
public import Silmaril.Machine.X86.Lir.Image.Defs
public import Silmaril.X86.Ext.Behaviour

/-! # The verified Core compiler: the frozen specification

This file is the **fixed statement** of the `core-comp` campaign (an honest verified C
compiler through Cerberus Core, `docs/projects/cerberus.md`). It defines what a compiled
program may do, and nothing else; the compiler and its proof are in
`Silmaril/Compile/Core/Verified.lean`:

```
def compile : Codec.Document → Option Artifact
theorem compile_sound : SoundSpec compile
```

The campaign's evaluator checks that this file is byte-identical to its frozen copy and
that `compile_sound` has exactly the type `SoundSpec compile`, uses no `sorry` and only
the standard axioms. Changing this file is a change of the specification and needs the
human's approval.

## Statement

For a decoded Core document `doc` (Cerberus's elaboration of a C file, linked with
std.core and the implementation), `compile doc = some a` gives an `Artifact`: x86-64
machine code, the address it is linked at, its entry, its stack-check sites, the
initial image of the linear memory and the area for the program's arguments. `SoundSpec compile` says: for every machine on which
the trusted loader has placed the artifact (`Loaded`), every behaviour of the machine
(`MachineBeh`: `X86.Ext.sem`, the fetch/decode/execute model, from the loaded state), as
observed by the trusted startup code (`observe`), run with any arguments `args` (`ArgsOk`: the
loader writes them as `argBlock`, and the source's `main(argc, argv)` receives the same
strings), is allowed by the source run with `args` (`Allowed`):

* the run exhausted a resource (a stack-limit check failed), which implements every
  source behaviour, as in CompCert and in `X86.Backend.compile_refines`; or
* Core can reach undefined behaviour from `doc`'s initial state (then every behaviour is
  allowed); or
* the observation is a Core behaviour (`CoreBeh`): `main` returned a value `v`, or the
  program called `exit(v)`, with output `out`, and the process exits with status `v mod 256`
  after writing `out`; or the program called `abort()` with output `out` and the process
  dies by SIGABRT after writing `out`; or both diverge.

`CoreBeh` is defined from the Core dynamics `Silmaril.Cerberus.Core.Dynamics.lts`
(every transition, every scheduler, every nondeterministic choice), not from the bounded
runner `Core.Run`. Core outcomes `error` and `unsupported` (a construct the Lean dynamics does not implement) have **no** behaviour: a
compiler cannot be proved sound on a program whose Core run reaches one.

## Observation (what the trusted startup code `tools/ccomp/runtime/crt0-x86_64.S` does)

* a return of the entry function: write the output buffer, exit with `rax mod 256`;
* a trap (UD2) that is not exhaustion: write the output buffer; after the runtime's
  `exit` (control word 5 = 1), exit with control word 4; after `abort` (word 5 = 2),
  die by SIGABRT; otherwise die by the trap's signal;
* a machine fault: write the output buffer, die by its signal.

The output buffer is control words 6 (address) and 3 (length); the control block is at
linear address `ctlAddr` (`Target.dataBase`).

## Trusted base

Cerberus's C→Core elaboration and Core passes (later its Lean port, `Silmaril.Cerberus.Elab`), the Core
exporter and the checked reader (`Codec.WellFormed.parseDocument`, proved
`print ∘ parse = id`), this specification (including the observation), the ELF writer,
`as`/`ld` (placing `.text` at `Artifact.codeBase`), the Linux loader and `crt0`
(mapping the linear memory with the image, the stack, the registers of `loadImage`), and
the x86-64 model `X86.Ext`. Everything from the Core document to the machine code is
proved.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Spec

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Machine
open Silmaril.X86 (MState Word Reg)
open Silmaril.X86.Backend (Space loadImage)
open Relation

/-- Core states and outcomes (`Silmaril.Cerberus.Core.Dynamics`). -/
abbrev CState := Silmaril.Cerberus.Core.Dynamics.State
abbrev COutcome := Silmaril.Cerberus.Core.Dynamics.Outcome

/-! ## Observations -/

/-- What a process shows: its exit status and output, death by a signal with its output,
divergence, or resource exhaustion. -/
inductive Obs where
  | exit (status : Nat) (stdout : List UInt8)
  | abort (stdout : List UInt8)
  | trap (stdout : List UInt8)
  | fault (stdout : List UInt8)
  | diverges
  | exhausted
  deriving DecidableEq, Repr

/-! ## The compiled artifact -/

/-- What the verified compiler produces; the trusted ELF writer, linker and loader turn it
into a process. -/
structure Artifact where
  /-- The address at which the linker places the code (`ld --section-start=.text=…`). -/
  codeBase : Nat
  /-- The machine code. -/
  code : List X86.Byte
  /-- The absolute address of the entry function (`__ccomp_start`), called with `argc` and the
  linear address of `argv` (`argBlock`) in the first two argument registers. -/
  entry : Nat
  /-- Stack-limit check sites `(address, bytes needed)`; a UD2 there with less stack is
  exhaustion. `observe` caps each requirement at `maxStackNeed`. -/
  stackSites : List (Nat × Nat)
  /-- Size of the linear memory. -/
  memSize : Nat
  /-- The initial linear memory: `image` at `imageBase`, zero elsewhere. -/
  imageBase : Nat
  image : ByteArray
  /-- The linear-memory area where the loader writes the program's arguments (`argBlock`), of
  `argSize ≥ minArgSize` bytes. -/
  argBase : Nat
  argSize : Nat

/-- The address of the runtime control block in the linear memory. -/
def ctlAddr : Nat := 0x1000

/-- A stack-check site may claim at most this many bytes: exhaustion is a real shortage. -/
def maxStackNeed : Nat := 2 ^ 16

/-- The argument area holds at least this many bytes (`SoundSpec` requires it). -/
def minArgSize : Nat := 4096

/-- The little-endian bytes of an 8-byte word. -/
def le8 (n : Nat) : List UInt8 := (List.range 8).map fun i => ((n >>> (8 * i)) % 256).toUInt8

/-- The program's arguments as the loader writes them at linear address `base` (crt0): the
`argc + 1` pointers of `argv` (8 bytes each, the last null), then the strings, each
null-terminated, in order. -/
def argBlock (base : Nat) (args : List String) : List UInt8 :=
  let start := base + 8 * (args.length + 1)
  let offsets := args.foldl (fun (acc : List Nat × Nat) s => (acc.1 ++ [acc.2], acc.2 + s.utf8ByteSize + 1))
    ([], start)
  (offsets.1.flatMap le8) ++ le8 0 ++ args.flatMap fun s => s.toUTF8.toList ++ [0]

/-- Arguments the startup of the Core dynamics and the specification accept: at least the
program name, printable ASCII without backslash (`Core.Startup.stringValue`), and a block that
fits in `minArgSize` bytes. -/
def ArgsOk (args : List String) : Prop :=
  args ≠ [] ∧ (∀ s ∈ args, ∀ c ∈ s.toList, 0x20 ≤ c.toNat ∧ c.toNat ≤ 0x7e ∧ c ≠ '\\') ∧
    (argBlock 0 args).length ≤ minArgSize

/-- The initial linear memory of an artifact run with `args`: the image, then the argument block
over it. -/
def Artifact.lmem (a : Artifact) (args : List String) : Lir.Memory where
  size := a.memSize
  bytes i :=
    let block := argBlock a.argBase args
    if a.argBase ≤ i ∧ i < a.argBase + block.length then
      BitVec.ofNat 8 (block[i - a.argBase]!).toNat
    else if a.imageBase ≤ i ∧ i < a.imageBase + a.image.size then
      BitVec.ofNat 8 (a.image.get! (i - a.imageBase)).toNat
    else 0

/-- The stack-check sites with their requirements capped. -/
def Artifact.sites (a : Artifact) : List (Nat × Nat) :=
  a.stackSites.map fun (x, n) => (x, min n maxStackNeed)

/-! ## The machine -/

/-- What the trusted loader and startup code establish (the premises of
`X86.Backend.compile_refines` for the entry function). -/
structure Loaded (a : Artifact) (S : Space) (exit : Word) (E0 : Nat) : Prop where
  codeBase : S.codeBase = a.codeBase
  valid : S.Valid a.code.length
  memSize : S.memSize = a.memSize
  e0_hi : E0 + 8 ≤ S.stackHi
  e0_lo : S.stackLo ≤ E0
  /-- At least `maxStackNeed` bytes of stack are available at entry. -/
  e0_room : S.stackLo + maxStackNeed ≤ E0
  align : E0 % 16 = 8
  exit_out : exit.toNat < S.codeBase ∨ S.codeBase + a.code.length ≤ exit.toNat

/-- The little-endian number of `n` bytes. -/
def leNat : List X86.Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- An 8-byte word of the linear memory at linear address `addr` (0 if unreadable). -/
def lword (S : Space) (m : Process.Memory) (addr : Nat) : Nat :=
  ((m.readBytes (S.memBase + addr) 8).map leNat).getD 0

/-- The output buffer (control words 6 and 3), as the startup code writes it. -/
def stdoutOf (S : Space) (m : Process.Memory) : List UInt8 :=
  let addr := lword S m (ctlAddr + 48)
  let len := lword S m (ctlAddr + 24)
  ((m.readBytes (S.memBase + addr) len).getD []).map fun b => b.toNat.toUInt8

/-- The process's observation of a machine outcome (`crt0-x86_64.S`). -/
def observe (S : Space) : Behaviour.Outcome MState MState X86.Ext.Fault → Obs
  | .returned final => .exit ((final.core.read .rax).toNat % 256) (stdoutOf S final.memory)
  | .trapped t =>
    let kind := lword S t.memory (ctlAddr + 40)
    if kind = 1 then .exit (lword S t.memory (ctlAddr + 32) % 256) (stdoutOf S t.memory)
    else if kind = 2 then .abort (stdoutOf S t.memory)
    else .trap (stdoutOf S t.memory)
  | .faulted _ => .fault []
  | .undefined => .fault []
  | .exhausted => .exhausted
  | .diverges => .diverges

/-- The observations of the loaded artifact run with `args` on the machine model: the entry is
called with `argc` and the linear address of `argv`. -/
def MachineBeh (a : Artifact) (S : Space) (exit : Word) (E0 : Nat) (saved : Reg → Word)
    (init : X86.State) (args : List String) (o : Obs) : Prop :=
  ∃ out, (X86.Ext.sem (X86.Ext.StackCheck.Exhausted S.stackLo a.sites)).Beh
      (exit, loadImage S a.code a.entry exit E0 saved
        [BitVec.ofNat 64 args.length, BitVec.ofNat 64 a.argBase] (a.lmem args) init) out ∧
    observe S out = o

/-! ## The source -/

/-- One transition of the Core dynamics, whatever its label. -/
def coreStep (file : Program) (labels : Labels) (s t : CState) : Prop :=
  ∃ l, (lts file labels).Tr s l t

/-- The initial Core state of a document run with the arguments `args` (`argv`, the program
name first; `main(argc, argv)` receives them, driver.lem:1628-1703). -/
def coreStart (doc : Codec.Document) (args : List String) : Except COutcome (CState × Labels) :=
  initial doc.file (Map.ofList (doc.enumBindings.getD [])) args

/-- A state reachable from the initial state, with the file's labels. -/
def CoreReach (doc : Codec.Document) (args : List String) (t : CState) : Prop :=
  ∃ s labels, coreStart doc args = .ok (s, labels) ∧ ReflTransGen (coreStep doc.file labels) s t

/-- Core can reach undefined behaviour. -/
def CoreUB (doc : Codec.Document) (args : List String) : Prop :=
  (∃ loc ub, coreStart doc args = .error (.ub loc ub)) ∨
    ∃ t loc ub, CoreReach doc args t ∧ t.control = .halt (.ub loc ub)

/-- The exit statuses of `main`'s result: an integer `n` gives `n mod 256`; an
unspecified one any status. -/
def exitStatuses : Val → Nat → Prop
  | .loaded (.specified (.integer n)), k | .object (.integer n), k => k = (n % 256).toNat
  | .loaded (.unspecified _), k => k < 256
  | _, _ => False

/-- The driver's output string, one byte per character. -/
def coreBytes (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- The defined behaviours of a Core document. `exit(v)` ends the dynamics like a return of `v`
from `main` (Cerberus's `Step_done`); `abort()` ends it with `aborted`
(`Silmaril.Cerberus.Core.Dynamics.libraryCall`). -/
inductive CoreBeh (doc : Codec.Document) (args : List String) : Obs → Prop where
  | exit {t : CState} {v : Val} {k : Nat} (reach : CoreReach doc args t)
      (halt : t.control = .halt (.defined v)) (status : exitStatuses v k) :
      CoreBeh doc args (.exit k (coreBytes t.memory.stdout))
  | abort {t : CState} (reach : CoreReach doc args t) (halt : t.control = .halt .aborted) :
      CoreBeh doc args (.abort (coreBytes t.memory.stdout))
  | diverges {s : CState} {labels : Labels} (start : coreStart doc args = .ok (s, labels))
      (inf : InfiniteTrace (coreStep doc.file labels) s) :
      CoreBeh doc args .diverges

/-- What the source run with `args` allows the compiled program to show. -/
def Allowed (doc : Codec.Document) (args : List String) (o : Obs) : Prop :=
  o = .exhausted ∨ CoreUB doc args ∨ CoreBeh doc args o

/-- **The specification.** Every artifact that `compile` produces reserves an argument area of
at least `minArgSize` bytes, and every observation of it, loaded and run with any arguments the
specification accepts, is allowed by its source run with the same arguments. -/
def SoundSpec (compile : Codec.Document → Option Artifact) : Prop :=
  ∀ (doc : Codec.Document) (a : Artifact), compile doc = some a →
    minArgSize ≤ a.argSize ∧
    ∀ (S : Space) (exit : Word) (E0 : Nat), Loaded a S exit E0 →
      ∀ (args : List String), ArgsOk args →
      ∀ (saved : Reg → Word) (init : X86.State) (o : Obs), MachineBeh a S exit E0 saved init args o →
        Allowed doc args o

end Silmaril.Compile.Core.Spec
