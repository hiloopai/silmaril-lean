module

public import Silmaril.Elf.Effects.Defs
public import Silmaril.Elf.Shapes.Defs

/-!
# Problem shapes: CFGs, call graphs and effects of x86 code in an ELF file

| name | statement |
|---|---|
| `silmaril.shapes.elf.cfg_is` | `CfgIs X D loc C`: `C` is the CFG of the function at `loc` |
| `silmaril.shapes.elf.cfg_sub` | `CfgSub X D loc C`: `C` is a closed over-approximation |
| `silmaril.shapes.effects.callgraph_sub` | every call from the function stays in `G` |
| `silmaril.shapes.effects.no_spawn` | no process or thread creation |
| `silmaril.shapes.effects.syscall_set` | every system call is in `S` |
| `silmaril.shapes.effects.foreign_calls` | every import called is in `I` |
| `silmaril.shapes.effects.no_network` | no socket or `io_uring` system call |
| `silmaril.shapes.effects.no_exec` | no `execve`/`execveat` |
| `….prog_*` | the same for a whole program (from `_start`, or from `main`) |

The effect shapes are stated over **every admissible world** (`Admissible`): any kernel and any
library within their frames, any placement, the code stable, indirect branches and returns within
the certificate `P`. They are relative to `P` because the frame conditions name its return sites
and listed targets; the call-graph claim itself is checked (`Thms`). Imports count as their summaries
(`summ`), which are rows of their own over the library (`import_syscalls`).
-/

@[expose] public section

namespace Silmaril.Elf.Effects.Shapes

open Silmaril.Project (Value)
open Silmaril.X86 (Word)
open Silmaril.X86.Flow (FlowDec UMach FlowLaw)
open Silmaril.X86.Cfg (Graph)
open Silmaril.Elf.Shapes (file)

/-- **`C` is the control-flow graph of the function at `loc` in `X`**, decoded by `D`: every
block's bytes are code of `X` at its start (`CodeAt`), the entry is `loc`'s address, and `C` is
exact (`Graph.exact`: closed, sorted, disjoint, maximal, reachable). The last conjunct is a
closed `decide` goal over the bytes. -/
@[problem "silmaril.shapes.elf.cfg_is" (title := "The control-flow graph of a function")]
def CfgIs {V : Type} (X : Value V) (D : FlowDec) (loc : Loc) (C : Graph Ref) : Prop :=
  (∀ b ∈ C.blocks, CodeAt (file X) b.start b.bytes) ∧ Func.At ⟨file X, loc⟩ C.entry ∧
    C.exact D = true

/-- **`C` over-approximates the control-flow graph of the function at `loc`**: closed under
intraprocedural successors, possibly with extra or split blocks (`Graph.sub`). -/
@[problem "silmaril.shapes.elf.cfg_sub" (title := "A closed control-flow graph of a function")]
def CfgSub {V : Type} (X : Value V) (D : FlowDec) (loc : Loc) (C : Graph Ref) : Prop :=
  (∀ b ∈ C.blocks, CodeAt (file X) b.start b.bytes) ∧ Func.At ⟨file X, loc⟩ C.entry ∧
    C.sub D = true

variable {σ : Type}

/-- **An admissible world for file `F` at `base`** on the machine `J` with decoder `D`, entered
at `s₀` with `rip = base + v`: the flow law, the placement, the read-only segments stable along
the run, no import bound inside certified code, and the kernel, library, indirect-branch and
return frames relative to the certificate `P` and its nodes reachable from `v` and `esc`. -/
structure Admissible (J : UMach σ) (D : FlowDec) (F : Silmaril.X86.Link.Blob) (P : Cert)
    (esc : List Nat) (W : World σ) (base : Word) (v : Nat) (keep : σ → Prop) (s₀ : σ) : Prop where
  mach : W.J = J
  law : FlowLaw J D
  placement : Link.ElfBind.Placement F base
  start : W.rip s₀ = base + BitVec.ofNat 64 v
  stable : CodeStable W D F base keep s₀
  image : ImageOk W base P
  kernel : KOk W D
  lib : LibOk W D base P (P.reach v esc) esc keep s₀
  ind : IndOk W D base P keep s₀
  ret : RetOk W D base P (P.reach v esc) esc keep s₀

/-- A statement `Φ` of every run of the function at `loc` (its activation) in every admissible
world. -/
def ForFunc {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (P : Cert)
    (esc : List Nat) (Φ : World σ → Word → (σ → Prop) → σ → Nat → Prop) : Prop :=
  ∀ v, Func.At ⟨file X, loc⟩ v → ∀ W base s₀,
    Admissible J D (file X) P esc W base v (Within W s₀) s₀ → Φ W base (Within W s₀) s₀ v

/-- **Every call of the function at `loc` stays in `P`'s call graph**: every executed call
target, import entered, system call and unknown step is covered by a node reachable from the
function and the escapes. -/
@[problem "silmaril.shapes.effects.callgraph_sub" (title := "The calls of a function stay in a call graph")]
def CallGraphSub {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (P : Cert)
    (esc : List Nat) : Prop :=
  ForFunc J D X loc P esc fun W base keep s₀ v => ReachIn W D base keep s₀ (P.reach v esc)

/-- **Every system call of the function is in `S`** (an import counts as its summary). -/
@[problem "silmaril.shapes.effects.syscall_set" (title := "The system calls of a function")]
def SyscallSet {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (P : Cert)
    (esc : List Nat) (summ : Summ) (S : List Nat) : Prop :=
  ForFunc J D X loc P esc fun W base keep s₀ _ => SyscallsOk W D base keep s₀ summ (· ∈ S)

/-- **The function creates no process or thread.** -/
@[problem "silmaril.shapes.effects.no_spawn" (title := "A function creates no process or thread")]
def NoSpawn {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (P : Cert)
    (esc : List Nat) (summ : Summ) : Prop :=
  ForFunc J D X loc P esc fun W base keep s₀ _ => SyscallsOk W D base keep s₀ summ (notIn spawnNrs)

/-- **The function makes no network system call.** -/
@[problem "silmaril.shapes.effects.no_network" (title := "A function uses no network")]
def NoNetwork {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (P : Cert)
    (esc : List Nat) (summ : Summ) : Prop :=
  ForFunc J D X loc P esc fun W base keep s₀ _ => SyscallsOk W D base keep s₀ summ (notIn netNrs)

/-- **The function executes no program.** -/
@[problem "silmaril.shapes.effects.no_exec" (title := "A function executes no program")]
def NoExec {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (P : Cert)
    (esc : List Nat) (summ : Summ) : Prop :=
  ForFunc J D X loc P esc fun W base keep s₀ _ => SyscallsOk W D base keep s₀ summ (notIn execNrs)

/-- **Every import the function enters is in `I`.** -/
@[problem "silmaril.shapes.effects.foreign_calls" (title := "The imports a function calls")]
def ForeignCalls {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (P : Cert)
    (esc : List Nat) (I : List Ref) : Prop :=
  ForFunc J D X loc P esc fun W base keep s₀ _ => ForeignIn W D base keep s₀ (· ∈ I)

/-- A statement of every run of the program `X` from `_start` (`e_entry`, the whole run). -/
def ForProg {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (P : Cert) (esc : List Nat)
    (Φ : World σ → Word → (σ → Prop) → σ → Nat → Prop) : Prop :=
  ∀ v, EntryIs (file X) v → ∀ W base s₀,
    Admissible J D (file X) P esc W base v (fun _ => True) s₀ → Φ W base (fun _ => True) s₀ v

/-- **The program creates no process or thread** (the route to the single-threaded model). -/
@[problem "silmaril.shapes.effects.prog_no_spawn" (title := "A program creates no process or thread")]
def ProgNoSpawn {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (P : Cert) (esc : List Nat)
    (summ : Summ) : Prop :=
  ForProg J D X P esc fun W base keep s₀ _ => SyscallsOk W D base keep s₀ summ (notIn spawnNrs)

/-- **Every system call of the program is in `S`.** -/
@[problem "silmaril.shapes.effects.prog_syscall_set" (title := "The system calls of a program")]
def ProgSyscallSet {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (P : Cert)
    (esc : List Nat) (summ : Summ) (S : List Nat) : Prop :=
  ForProg J D X P esc fun W base keep s₀ _ => SyscallsOk W D base keep s₀ summ (· ∈ S)

/-- **The certificate facts a row proves** (by `decide`, and a `CodeAt` row per block): the
decoder is stable, `loc` is at `v`, `P` is checked with `v` and the escapes as roots, and `L` is
a listed node set closed under `P`'s edges, holding the roots and not `unresolved`. -/
structure CertOk {V : Type} (D : FlowDec) (X : Value V) (loc : Loc) (P : Cert) (esc : List Nat) (v : Nat)
    (L : List Node) : Prop where
  stable : D.Stable
  at_ : ∀ w, Func.At ⟨file X, loc⟩ w → w = v
  check : P.check D (v :: esc) = true
  code : ∀ f C, (f, C) ∈ P.fns → ∀ b ∈ C.blocks, Link.ElfBind.CodeAt (file X) b.start b.bytes
  closed : P.graph.closedB L = true
  roots : (Node.fn v :: esc.map .fn).all L.contains = true
  noUnres : L.contains .unresolved = false

/-- The imports of a listed node set. -/
def importsOf (L : List Node) : List Ref := L.filterMap fun | .ext r => some r | _ => none

/-- A node's own system calls are in `S`: a known number in `S`; never `sysAny` or `unresolved`
(imports are judged by their summaries). -/
def directOk (S : List Nat) : Node → Bool
  | .sys k => S.contains k
  | .sysAny | .unresolved => false
  | _ => true

end Silmaril.Elf.Effects.Shapes
