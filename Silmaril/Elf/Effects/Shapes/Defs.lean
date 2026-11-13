module

public import Silmaril.Elf.Effects.Defs
public import Silmaril.Elf.Shapes.Defs

/-!
# Problem shapes: CFGs, call graphs and effects of x86 code in an ELF file

DESIGN SKELETON (effects design, `/tmp/elfwork/effects/DESIGN.md`).

| name | statement |
|---|---|
| `silmaril.shapes.elf.cfg_is` | `CfgIs X D loc img C`: `C` is the CFG of the function at `loc` |
| `silmaril.shapes.elf.cfg_sub` | `CfgSub X D loc img C`: `C` is a closed over-approximation |
| `silmaril.shapes.effects.callgraph_sub` | every call from the function stays in `G` |
| `silmaril.shapes.effects.no_spawn` | no process or thread creation |
| `silmaril.shapes.effects.syscall_set` | every system call is in `S` |
| `silmaril.shapes.effects.foreign_calls` | every import called is in `I` |
| `silmaril.shapes.effects.no_network` | no socket or `io_uring` system call |
| `silmaril.shapes.effects.no_exec` | no `execve`/`execveat` |
| `….prog_*` | the same for a whole program (from `_start`, or from `main`) |

The effect shapes are stated over **every admissible world** (`Admissible`): any kernel and any
library within their frames, any placement, the code stable. Imports count as their summaries
(`summ`), which are rows of their own over the library (`import_syscalls`).
-/

@[expose] public section

namespace Silmaril.Elf.Effects.Shapes

open Silmaril.Project (Value)
open Silmaril.X86 (Word)
open Silmaril.X86.Flow (FlowDec UMach FlowLaw)
open Silmaril.X86.Cfg (Image Graph)
open Silmaril.Elf.Shapes (file)

/-- **`C` is the control-flow graph of the function at `loc` in `X`**, decoded by `D` from code
windows of `X`. Decidable: a row is proved by `decide` over the bytes (`CodeAt` rows give `img`). -/
@[problem "silmaril.shapes.elf.cfg_is" (title := "The control-flow graph of a function")]
def CfgIs {V : Type} (X : Value V) (D : FlowDec) (loc : Loc) (img : Image) (C : Graph D Ref) : Prop :=
  (∀ w ∈ img, CodeAt (file X) w.1 w.2) ∧ Func.At ⟨file X, loc⟩ C.entry ∧ C.exact img = true

/-- **`C` over-approximates the control-flow graph of the function at `loc`**: closed under
successors, possibly with extra or split blocks. -/
@[problem "silmaril.shapes.elf.cfg_sub" (title := "A closed control-flow graph of a function")]
def CfgSub {V : Type} (X : Value V) (D : FlowDec) (loc : Loc) (img : Image) (C : Graph D Ref) : Prop :=
  (∀ w ∈ img, CodeAt (file X) w.1 w.2) ∧ Func.At ⟨file X, loc⟩ C.entry ∧ C.sub img = true

variable {σ : Type}

/-- **An admissible world for file `F` at `base`** on the machine `J` with decoder `D`, the
library calling back only into `esc`, entered at `s₀` with `rip = base + v`. -/
structure Admissible (J : UMach σ) (D : FlowDec) (F : Silmaril.X86.Link.Blob) (esc : List Nat)
    (W : World σ) (base : Word) (v : Nat) (keep : σ → Prop) (s₀ : σ) : Prop where
  mach : W.J = J
  dec : W.D = D
  law : FlowLaw J D
  placement : Placement F base.toNat
  lib : LibOk W F base esc
  kernel : KOk W F base
  entry : (W.J.core s₀).rip = base + BitVec.ofNat 64 v
  loaded : Link.ElfBind.RoLoaded F base (W.J.mem s₀)
  stable : CodeStable W F base keep s₀

/-- A statement `Φ` of every run of the function at `loc` (its activation) in every admissible
world. -/
def ForFunc {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (esc : List Nat)
    (Φ : World σ → Word → (σ → Prop) → σ → Nat → Prop) : Prop :=
  ∀ v, Func.At ⟨file X, loc⟩ v → ∀ W base s₀,
    Admissible J D (file X) esc W base v (Within W s₀) s₀ → Φ W base (Within W s₀) s₀ v

/-- **Every call from the function at `loc` stays in `G`**: every executed call, system call,
import and callback is a node of `G` reachable from the function and the escapes. -/
@[problem "silmaril.shapes.effects.callgraph_sub" (title := "The calls of a function stay in a call graph")]
def CallGraphSub {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (esc : List Nat)
    (G : CallGraph) : Prop :=
  ForFunc J D X loc esc fun W base keep s₀ v =>
    ReachIn W base keep s₀ (G.reach (.fn v :: esc.map .fn))

/-- **Every system call of the function is in `S`** (an import counts as its summary). -/
@[problem "silmaril.shapes.effects.syscall_set" (title := "The system calls of a function")]
def SyscallSet {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (esc : List Nat)
    (summ : Summ) (S : List Nat) : Prop :=
  ForFunc J D X loc esc fun W base keep s₀ _ => SyscallsOk W base keep s₀ summ (· ∈ S)

/-- **The function creates no process or thread.** -/
@[problem "silmaril.shapes.effects.no_spawn" (title := "A function creates no process or thread")]
def NoSpawn {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (esc : List Nat)
    (summ : Summ) : Prop :=
  ForFunc J D X loc esc fun W base keep s₀ _ => SyscallsOk W base keep s₀ summ (notIn spawnNrs)

/-- **The function makes no network system call.** -/
@[problem "silmaril.shapes.effects.no_network" (title := "A function uses no network")]
def NoNetwork {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (esc : List Nat)
    (summ : Summ) : Prop :=
  ForFunc J D X loc esc fun W base keep s₀ _ => SyscallsOk W base keep s₀ summ (notIn netNrs)

/-- **The function executes no program.** -/
@[problem "silmaril.shapes.effects.no_exec" (title := "A function executes no program")]
def NoExec {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (esc : List Nat)
    (summ : Summ) : Prop :=
  ForFunc J D X loc esc fun W base keep s₀ _ => SyscallsOk W base keep s₀ summ (notIn execNrs)

/-- **Every import the function calls is in `I`.** -/
@[problem "silmaril.shapes.effects.foreign_calls" (title := "The imports a function calls")]
def ForeignCalls {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) (esc : List Nat)
    (I : List Ref) : Prop :=
  ForFunc J D X loc esc fun W base keep s₀ _ => ForeignIn W base keep s₀ (· ∈ I)

/-- A statement of every run of the program `X` from `_start` (`e_entry`, the whole run). The
`main` entry adds `at_main`'s state and `main`'s return address bound to the C runtime
(`Effects.StdExe`). -/
def ForProg {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (esc : List Nat)
    (Φ : World σ → Word → (σ → Prop) → σ → Nat → Prop) : Prop :=
  ∀ v, EntryIs (file X) v → ∀ W base s₀,
    Admissible J D (file X) esc W base v (fun _ => True) s₀ → Φ W base (fun _ => True) s₀ v

/-- **The program creates no process or thread** (the route to the single-threaded model). -/
@[problem "silmaril.shapes.effects.prog_no_spawn" (title := "A program creates no process or thread")]
def ProgNoSpawn {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (esc : List Nat)
    (summ : Summ) : Prop :=
  ForProg J D X esc fun W base keep s₀ _ => SyscallsOk W base keep s₀ summ (notIn spawnNrs)

/-- **Every system call of the program is in `S`.** -/
@[problem "silmaril.shapes.effects.prog_syscall_set" (title := "The system calls of a program")]
def ProgSyscallSet {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (esc : List Nat)
    (summ : Summ) (S : List Nat) : Prop :=
  ForProg J D X esc fun W base keep s₀ _ => SyscallsOk W base keep s₀ summ (· ∈ S)

/-- **The open, edge-respecting form**: every run of the function at `loc` respects `G`, the
frames of the frontier `H` opaque (their calls unchecked until they return). -/
def CallGraphSubOpen {V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc)
    (esc : List Nat) (G : CallGraph) (H : List Node) : Prop :=
  ForFunc J D X loc esc fun W base keep s₀ v => CallSubIn W base keep s₀ G H (.fn v)

/-- **Composition**: `F` respects `G₁` with its callees `H` opaque, and each callee respects `G₂`;
then `F` respects `G₁ ∪ G₂`. -/
def Task.compose : Prop :=
  ∀ {σ V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) esc (G₁ G₂ : CallGraph)
    (H : List Nat),
    CallGraphSubOpen J D X loc esc G₁ (H.map .fn) →
    (∀ b ∈ H, CallGraphSubOpen J D X (.addr b) esc G₂ []) →
    CallGraphSubOpen J D X loc esc (G₁.union G₂) []

/-- **Monotone in the graph.** -/
def Task.mono : Prop :=
  ∀ {σ V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) esc (G G' : CallGraph),
    G.Le G' → CallGraphSub J D X loc esc G → CallGraphSub J D X loc esc G'

/-- **`no_spawn` from a call graph** whose reachable nodes do not spawn. -/
def Task.noSpawn_of_callGraph : Prop :=
  ∀ {σ V : Type} (J : UMach σ) (D : FlowDec) (X : Value V) (loc : Loc) esc (G : CallGraph)
    (summ : Summ),
    CallGraphSub J D X loc esc G →
    (∀ v, Func.At ⟨file X, loc⟩ v → ∀ n ∈ G.reach (.fn v :: esc.map .fn), n.SysOk summ (notIn spawnNrs)) →
    NoSpawn J D X loc esc summ

end Silmaril.Elf.Effects.Shapes
