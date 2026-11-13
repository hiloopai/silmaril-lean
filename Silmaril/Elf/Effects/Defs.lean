module

public import Silmaril.X86.Cfg.Defs
public import Silmaril.X86.Flow.Str9.Defs
public import Silmaril.Elf.Defs
public import Silmaril.Elf.Link.ElfBind.Defs

/-!
# Effects of x86 code: call graphs, the most general process, and effect predicates

Layers: a flow decoder and its flow law (`Silmaril.X86.Flow`), CFG certificates
(`Silmaril.X86.Cfg`), then here **call graphs**, a **most general process** around the image (any
kernel, any library), and **effect predicates** read off the reachable call-graph nodes.

* A `Cert` is one CFG per internal function and a call graph. `Cert.check` (by `decide`) checks
  each CFG (`Graph.sub`) and that every call, tail jump, import and system-call edge of each CFG
  is an edge of the graph.
* The process (`World`, `Step`, `Run`) runs the image's machine `J` on image code, any kernel `K`
  at a `syscall` (`int 0x80`/`sysenter`: an unknown system call), and any library `L` on foreign
  code. A step from image bytes the decoder does not read is an `unknown` event.
* `ReachIn N`: every executed call target, import entered, system call and unknown step is a node
  of `N` (a known system call is also covered by `sysAny ∈ N`).
* **Soundness** (`Thms.sound`): under the `Setting` (the flow law, the certificate checked, `N`
  closed under the graph's edges and without `unresolved`, the code loaded, and the world's frame
  conditions `KOk`, `LibOk`, `IndOk`, `RetOk`, `ImageOk`), `ReachIn N` holds for every run from
  the entry.
-/

@[expose] public section

namespace Silmaril.Elf.Effects

open Silmaril.X86 (Word Byte State)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)
open Silmaril.X86.Flow (FlowDec UMach FlowLaw)
open Silmaril.X86.Cfg (Graph Target Term Why Block walk)
open Silmaril.X86.Ext (loadN)
open Silmaril.Formats.ELF (NameBytes)

/-! ## Entities -/

/-- Where a function is: an address (ELF virtual address) or a bound symbol. -/
inductive Loc where
  | addr (v : Nat)
  | sym (sel : Sel)
  deriving DecidableEq, Repr

/-- **A function**: a file and a location in it. -/
structure Func where
  file : Blob
  loc : Loc

/-- The entry of `f` is `v`: the address, or a plain (non-IFUNC, non-absolute) definition. -/
def Func.At (f : Func) (v : Nat) : Prop :=
  match f.loc with
  | .addr w => v = w
  | .sym sel => ∃ d, Lookup f.file sel (some d) ∧ d.value = v ∧ d.ifunc = false ∧ d.abs = false

/-- **A program**: from `_start` (`e_entry`, the loader's initial state), or from `main` with the
C runtime set up (`StdExe`'s `at_main`; the bridge is `Effects.StdExe`). -/
inductive Prog where
  | start (file : Blob)
  | main (file : Blob)

/-! ## Call graphs -/

/-- **A call-graph node.** -/
inductive Node where
  /-- An internal function, by its entry (ELF virtual address). -/
  | fn (a : Nat)
  /-- An import, by versioned name (the library abstracted away). -/
  | ext (r : Ref)
  /-- A direct `syscall` with a known number. -/
  | sys (nr : Nat)
  /-- A system call whose number is not determined (or `int 0x80`/`sysenter`). -/
  | sysAny
  /-- A transfer whose target is not resolved, or an instruction the decoder does not read. -/
  | unresolved
  deriving DecidableEq, Repr

/-- **A call graph**: directed edges, cycles allowed. -/
structure CallGraph where
  edges : List (Node × Node)
  deriving DecidableEq, Repr

namespace CallGraph

/-- **`N` is closed under the edges** (decidable form, for a listed `N`). -/
def closedB (G : CallGraph) (N : List Node) : Bool :=
  G.edges.all fun e => !N.contains e.1 || N.contains e.2

/-- **Reachability** from `roots`. -/
inductive Reaches (G : CallGraph) (roots : List Node) : Node → Prop
  | root {n} : n ∈ roots → Reaches G roots n
  | edge {m n} : Reaches G roots m → (m, n) ∈ G.edges → Reaches G roots n

/-- `G` is a subgraph of `H`. -/
def Le (G H : CallGraph) : Prop := ∀ e ∈ G.edges, e ∈ H.edges

/-- The union. -/
def union (G H : CallGraph) : CallGraph := ⟨G.edges ++ H.edges⟩

end CallGraph

/-- The call-graph targets of a transfer. -/
def tgtNode : Target Ref → List Node
  | .fn a => [.fn a]
  | .ext r => [.ext r]
  | .blk _ => []

/-- The call-graph targets of a terminator: calls, tail jumps, imports, system calls, and
`unresolved` for an indirect transfer without listed targets. -/
def termNodes : Term Ref → List Node
  | .jmp t | .call t _ => tgtNode t
  | .jmpInd (some ts) _ | .callInd (some ts) _ _ => ts.flatMap tgtNode
  | .jmpInd none _ | .callInd none _ _ => [.unresolved]
  | .sys (some n) _ => [.sys n]
  | .sys none _ | .sysOther _ => [.sysAny]
  | _ => []

/-- The call-graph edges of one function's CFG. -/
def edgesOf (f : Nat) (C : Graph Ref) : List (Node × Node) :=
  C.blocks.flatMap fun b => (termNodes b.term).map fun n => (.fn f, n)

/-! ## Program certificates -/

/-- **A certificate**: one CFG per internal function (keyed by its entry), and a call graph. -/
structure Cert where
  fns : List (Nat × Graph Ref)
  graph : CallGraph
  deriving DecidableEq, Repr

/-- `a` has a CFG. -/
def Cert.has (P : Cert) (a : Nat) : Bool := P.fns.any (·.1 == a)

/-- **One function's part of the check**: its CFG is closed (`Graph.sub`) with its key as entry,
and each of its edges is in the graph, a function target having a CFG. -/
def Cert.fnOk (D : FlowDec) (P : Cert) (a : Nat) (C : Graph Ref) : Bool :=
  C.entry == a && decide (a < 2 ^ 64) && C.sub D &&
    (edgesOf a C).all fun e => P.graph.edges.contains e && (match e.2 with
      | .fn b => P.has b
      | _ => true)

/-- **The kernel check** (by `decide`): every function's part, and the roots have CFGs. -/
def Cert.check (D : FlowDec) (P : Cert) (roots : List Nat) : Bool :=
  P.fns.all (fun x => P.fnOk D x.1 x.2) && roots.all P.has

/-- The nodes of `P`'s graph reachable from the entry `v` and the escapes. -/
def Cert.reach (P : Cert) (v : Nat) (esc : List Nat) : Node → Prop :=
  P.graph.Reaches (.fn v :: esc.map .fn)

/-- **The union of two certificates** (composition: the functions and edges of both). -/
def Cert.union (P Q : Cert) : Cert := ⟨P.fns ++ Q.fns, P.graph.union Q.graph⟩

/-! ## The most general process -/

/-- Where an address is: image code, the bound entry of an import, or other foreign code
(library code, the vDSO, unmapped). -/
inductive Cls where
  | image
  | entry (r : Ref)
  | foreign
  deriving DecidableEq, Repr

/-- **A world**: the image machine, where the loader put things (`cls`), any kernel (`K nr s t`;
`t = none`: the process ended) and any library (`L s t`, one step of foreign code). -/
structure World (σ : Type) where
  J : UMach σ
  cls : Word → Cls
  K : Nat → σ → Option σ → Prop
  L : σ → Option σ → Prop

/-- An observable event of a step. -/
inductive Ev where
  /-- Any other step. -/
  | step
  /-- A `call` retired to `dst`, pushing `ret`. -/
  | call (dst ret : Word)
  /-- A `jmp`/`jcc` retired to `dst`. -/
  | jump (dst : Word)
  | ret (dst : Word)
  /-- A `syscall` with `rax = nr`. -/
  | sys (nr : Nat)
  /-- `int n`/`sysenter`. -/
  | sysAny
  /-- A library step, to `dst`. -/
  | lib (dst : Option Word)
  /-- A step from image bytes the decoder does not read. -/
  | unknown
  deriving DecidableEq

variable {σ : Type}

/-- The event of a user step of kind `k`. -/
def evOf (k : Silmaril.X86.Flow.Kind) (s : State) (l : Nat) (t : State) : Ev :=
  match k with
  | .call _ | .callInd _ => .call t.rip (Silmaril.X86.Flow.next s l)
  | .jmp _ | .jmpInd _ | .jcc _ => .jump t.rip
  | .ret => .ret t.rip
  | _ => .step

/-- `rip` of a state. -/
abbrev World.rip (W : World σ) (s : σ) : Word := (W.J.core s).rip

/-- **One step of the most general process** with its event. -/
inductive Step (W : World σ) (D : FlowDec) : Option σ → Ev → Option σ → Prop
  | user {s t i l} : W.cls (W.rip s) = .image → Silmaril.X86.Flow.At W.J D s i l → D.kind i ≠ .syscall →
      D.kind i ≠ .sysOther → W.J.step s t →
      Step W D (some s) (evOf (D.kind i) (W.J.core s) l (W.J.core t)) (some t)
  | unknown {s t} : W.cls (W.rip s) = .image → (∀ i l, ¬ Silmaril.X86.Flow.At W.J D s i l) → W.J.step s t →
      Step W D (some s) .unknown (some t)
  | sys {s t i l} : W.cls (W.rip s) = .image → Silmaril.X86.Flow.At W.J D s i l → D.kind i = .syscall →
      W.K ((W.J.core s).read .rax).toNat s t → Step W D (some s) (.sys ((W.J.core s).read .rax).toNat) t
  | sysOther {s t i l n} : W.cls (W.rip s) = .image → Silmaril.X86.Flow.At W.J D s i l → D.kind i = .sysOther →
      W.K n s t → Step W D (some s) .sysAny t
  | lib {s t} : W.cls (W.rip s) ≠ .image → W.L s t → Step W D (some s) (.lib (t.map W.rip)) t

/-- **Runs with their events**, while every state stepped from satisfies `keep` (a function's
activation: `rsp ≤ rsp₀`; a program: `True`). -/
inductive Run (W : World σ) (D : FlowDec) (keep : σ → Prop) : Option σ → List Ev → Option σ → Prop
  | refl (x) : Run W D keep x [] x
  | step {s e y es z} : keep s → Step W D (some s) e y → Run W D keep y es z →
      Run W D keep (some s) (e :: es) z

/-- The activation of a function entered at `s₀`. -/
def Within (W : World σ) (s₀ s : σ) : Prop :=
  ((W.J.core s).read .rsp).toNat ≤ ((W.J.core s₀).read .rsp).toNat

/-- **The node of an event**, for the events a call graph constrains: a call into the image is
its target function; entering an import (by a call or a jump) is the import; entering other
foreign code, or an unknown step, is `unresolved`. -/
def Ev.node (W : World σ) (base : Word) : Ev → Option Node
  | .call a _ => some (match W.cls a with
    | .image => .fn (a - base).toNat
    | .entry r => .ext r
    | .foreign => .unresolved)
  | .jump a => match W.cls a with
    | .image => none
    | .entry r => some (.ext r)
    | .foreign => some .unresolved
  | .sys n => some (.sys n)
  | .sysAny => some .sysAny
  | .unknown => some .unresolved
  | _ => none

/-- `n` is in `N`, a known system call also through `sysAny`. -/
def Covered (N : Node → Prop) (n : Node) : Prop :=
  N n ∨ (∃ k, n = .sys k) ∧ N .sysAny

/-- **Every executed call, import, system call and unknown step from `s₀` is covered by `N`.** -/
def ReachIn (W : World σ) (D : FlowDec) (base : Word) (keep : σ → Prop) (s₀ : σ)
    (N : Node → Prop) : Prop :=
  ∀ es y, Run W D keep (some s₀) es y → ∀ e ∈ es, ∀ n, e.node W base = some n → Covered N n

/-! ## The frame conditions of a world -/

/-- `a` is the return-to address of a call of a function of `N`. -/
def RetSite (P : Cert) (N : Node → Prop) (a : Nat) : Prop :=
  ∃ f C b, (f, C) ∈ P.fns ∧ N (.fn f) ∧ b ∈ C.blocks ∧ b.term.retTo = some a

/-- **Where control may come back into the image**: foreign code, a return site of a function of
`N`, or an escaped entry (`esc`: the entries a library may call back). -/
def Landing (W : World σ) (base : Word) (P : Cert) (N : Node → Prop) (esc : List Nat) (t : σ) :
    Prop :=
  W.cls (W.rip t) ≠ .image ∨ (∃ a, RetSite P N a ∧ W.rip t = base + BitVec.ofNat 64 a) ∨
    ∃ e ∈ esc, W.rip t = base + BitVec.ofNat 64 e

/-- **The code stays loaded** at every state of a run: each block's bytes are fetchable at
`base + start`. Derived from `CodeStable` (the read-only segments stay loaded), `CodeAt` rows and
the placement (`Thms.codeLoaded_of`). -/
def CodeLoaded (W : World σ) (D : FlowDec) (base : Word) (P : Cert) (keep : σ → Prop) (s₀ : σ) :
    Prop :=
  ∀ es u, Run W D keep (some s₀) es (some u) → ∀ f C, (f, C) ∈ P.fns → ∀ b ∈ C.blocks,
    Silmaril.X86.Ext.Loaded (W.J.mem u) (base + BitVec.ofNat 64 b.start) b.bytes

/-- **Code stability** (W^X along the run): the read-only segments of `F` stay loaded at `base`.
A hypothesis until derived from the machine's write discipline, `LibOk` and the kernel. -/
def CodeStable (W : World σ) (D : FlowDec) (F : Blob) (base : Word) (keep : σ → Prop) (s₀ : σ) :
    Prop :=
  ∀ es u, Run W D keep (some s₀) es (some u) → Link.ElfBind.RoLoaded F base (W.J.mem u)

/-- **The certified code is image code**: no import is bound inside a block. -/
def ImageOk (W : World σ) (base : Word) (P : Cert) : Prop :=
  ∀ f C, (f, C) ∈ P.fns → ∀ b ∈ C.blocks, ∀ o < b.bytes.length,
    W.cls (base + BitVec.ofNat 64 (b.start + o)) = .image

/-- **The kernel resumes after the system-call instruction** (or ends the process). -/
def KOk (W : World σ) (D : FlowDec) : Prop :=
  ∀ n s t i l, Silmaril.X86.Flow.At W.J D s i l → (D.kind i = .syscall ∨ D.kind i = .sysOther) →
    W.K n s (some t) → W.rip t = Silmaril.X86.Flow.next (W.J.core s) l

/-- **The library frame**: a library step either stays in foreign code, returns to a return site
of a function of `N`, calls back an escaped entry, or leaves `keep`. -/
def LibOk (W : World σ) (D : FlowDec) (base : Word) (P : Cert) (N : Node → Prop) (esc : List Nat)
    (keep : σ → Prop) (s₀ : σ) : Prop :=
  ∀ es u t, Run W D keep (some s₀) es (some u) → keep u → W.cls (W.rip u) ≠ .image →
    W.L u (some t) → keep t → Landing W base P N esc t

/-- Where a listed target sends `t`. -/
def Lands (W : World σ) (base : Word) (t : σ) : Target Ref → Prop
  | .blk c | .fn c => W.rip t = base + BitVec.ofNat 64 c
  | .ext r => W.cls (W.rip t) = .entry r

/-- **Indirect transfers stay in their listed sets**: a step from the last instruction of a block
whose terminator lists targets lands on one of them. Discharged for `got` from RELRO and
`BIND_NOW`, for `table` from read-only data (later); for `assumed` it stays a hypothesis. -/
def IndOk (W : World σ) (D : FlowDec) (base : Word) (P : Cert) (keep : σ → Prop) (s₀ : σ) :
    Prop :=
  ∀ es u t i l, Run W D keep (some s₀) es (some u) → keep u → Silmaril.X86.Flow.At W.J D u i l → W.J.step u t →
    ∀ f C, (f, C) ∈ P.fns → ∀ b ∈ C.blocks, ∀ o, W.rip u = base + BitVec.ofNat 64 (b.start + o) →
      o + l = b.bytes.length → ∀ ts, b.term.listed = some ts → ∃ x ∈ ts, Lands W base t x

/-- **Returns land on return sites**: a `ret` in the image lands where control may come back
(`Landing`), or leaves `keep`. The tolerant form of return discipline: from the stack safety of
the code, or a function contract. -/
def RetOk (W : World σ) (D : FlowDec) (base : Word) (P : Cert) (N : Node → Prop) (esc : List Nat)
    (keep : σ → Prop) (s₀ : σ) : Prop :=
  ∀ es u t i l, Run W D keep (some s₀) es (some u) → keep u → W.cls (W.rip u) = .image →
    Silmaril.X86.Flow.At W.J D u i l → D.kind i = .ret → W.J.step u t → keep t → Landing W base P N esc t

/-- **The setting of the soundness theorem**: the flow law and a stable decoder; the certificate
checked with the entry and the escapes as roots; `N` holding the roots, closed under the graph's
edges and without `unresolved`; the state at `entry`; and the world's frame conditions. -/
structure Setting (W : World σ) (D : FlowDec) (base : Word) (P : Cert) (esc : List Nat)
    (entry : Nat) (keep : σ → Prop) (s₀ : σ) (N : Node → Prop) : Prop where
  law : FlowLaw W.J D
  stable : D.Stable
  check : P.check D (entry :: esc) = true
  root : N (.fn entry)
  escapes : ∀ e ∈ esc, N (.fn e)
  closed : ∀ e ∈ P.graph.edges, N e.1 → N e.2
  noUnres : ¬ N .unresolved
  start : W.rip s₀ = base + BitVec.ofNat 64 entry
  code : CodeLoaded W D base P keep s₀
  image : ImageOk W base P
  kernel : KOk W D
  lib : LibOk W D base P N esc keep s₀
  ind : IndOk W D base P keep s₀
  ret : RetOk W D base P N esc keep s₀

/-! ## Effects -/

/-- **Syscall summaries of imports**: `(r, ns)` says the import `r` makes at most the system calls
`ns`; an import without an entry is unknown. Proved per import (`Libc.SysWrap`, a followed call
graph of the library), or assumed. -/
abbrev Summ := List (Ref × List Nat)

/-- A node makes only system calls satisfying `ok`. -/
def Node.SysOk (summ : Summ) (ok : Nat → Prop) : Node → Prop
  | .fn _ => True
  | .ext r => ∃ ns, summ.lookup r = some ns ∧ ∀ n ∈ ns, ok n
  | .sys n => ok n
  | .sysAny | .unresolved => False

/-- **Every system call of every run satisfies `ok`** (an import counts as its summary). -/
def SyscallsOk (W : World σ) (D : FlowDec) (base : Word) (keep : σ → Prop) (s₀ : σ) (summ : Summ)
    (ok : Nat → Prop) : Prop :=
  ∀ es y, Run W D keep (some s₀) es y → ∀ e ∈ es, ∀ n, e.node W base = some n → n.SysOk summ ok

/-- **Every import entered is in `I`.** -/
def ForeignIn (W : World σ) (D : FlowDec) (base : Word) (keep : σ → Prop) (s₀ : σ)
    (I : Ref → Prop) : Prop :=
  ∀ es y, Run W D keep (some s₀) es y → ∀ e ∈ es, ∀ r, e.node W base = some (.ext r) → I r

/-- Process creation: `clone`, `fork`, `vfork`, `clone3`. -/
def spawnNrs : List Nat := [56, 57, 58, 435]

/-- `execve`, `execveat`. -/
def execNrs : List Nat := [59, 322]

/-- Sockets and `io_uring` (which can do network operations without them). -/
def netNrs : List Nat := (List.range 15).map (· + 41) ++ [288, 299, 307, 425, 426, 427]

/-- The imports the name-level shapes treat as spawning (glibc and musl). -/
def spawnNames : List String :=
  ["fork", "vfork", "_Fork", "clone", "clone3", "pthread_create", "posix_spawn", "posix_spawnp",
    "system", "popen", "daemon", "forkpty", "wordexp", "thrd_create", "timer_create"]

/-- `n` is not in `ns`. -/
def notIn (ns : List Nat) (n : Nat) : Prop := n ∉ ns

/-- The system calls of a set of nodes: the numbers, and every summary of an import. -/
def sysOf (summ : Summ) : List Node → List Nat
  | [] => []
  | .sys n :: ns => n :: sysOf summ ns
  | .ext r :: ns => (summ.lookup r).getD [] ++ sysOf summ ns
  | _ :: ns => sysOf summ ns

/-- Every node of `N` has a known system-call set (no `sysAny`, `unresolved`, unsummarised
import). -/
def known (summ : Summ) (N : List Node) : Bool :=
  N.all fun
    | .ext r => (summ.lookup r).isSome
    | .sysAny | .unresolved => false
    | _ => true

/-- Decidable form of `Node.SysOk` for a decidable `ok`. -/
def Node.okB (summ : Summ) (ok : Nat → Bool) : Node → Bool
  | .fn _ => true
  | .ext r => match summ.lookup r with
    | some ns => ns.all ok
    | none => false
  | .sys n => ok n
  | .sysAny | .unresolved => false

/-! ## Open goals -/

/-- **Soundness** (proved: `Thms.sound`). -/
def Task.sound : Prop :=
  ∀ {σ : Type} (W : World σ) (D : FlowDec) base (P : Cert) esc entry keep (s₀ : σ) N,
    Setting W D base P esc entry keep s₀ N → ReachIn W D base keep s₀ N

end Silmaril.Elf.Effects
