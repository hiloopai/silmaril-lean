module

public import Silmaril.X86.Cfg.Defs
public import Silmaril.Elf.Defs
public import Silmaril.Elf.Link.ElfBind.Defs

/-!
# Effects of x86 code: call graphs, the most general process, and effect predicates

DESIGN SKELETON (effects design, `/tmp/elfwork/effects/DESIGN.md`). The open theorems are the
`Task.*` propositions at the end.
-/

@[expose] public section

namespace Silmaril.Elf.Effects

open Silmaril.X86 (Word Byte State)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)
open Silmaril.X86.Flow (FlowDec UMach FlowLaw)
open Silmaril.X86.Cfg (Image Graph Target Term Why)
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
  /-- An indirect transfer whose targets are not resolved. -/
  | unresolved
  deriving DecidableEq, Repr

/-- **A call graph**: nodes and directed edges, cycles allowed. -/
structure CallGraph where
  nodes : List Node
  edges : List (Node × Node)
  deriving DecidableEq, Repr

namespace CallGraph

/-- The nodes reachable from `roots` (`k` rounds). -/
def reachK (G : CallGraph) (roots : List Node) : Nat → List Node
  | 0 => roots
  | k + 1 =>
    let r := G.reachK roots k
    r ++ (G.edges.filter fun e => r.contains e.1 && !r.contains e.2).map (·.2)

/-- The nodes reachable from `roots`. -/
def reach (G : CallGraph) (roots : List Node) : List Node := G.reachK roots G.nodes.length

/-- `G` is a subgraph of `H`. -/
def Le (G H : CallGraph) : Prop := (∀ n ∈ G.nodes, n ∈ H.nodes) ∧ (∀ e ∈ G.edges, e ∈ H.edges)

/-- The union. -/
def union (G H : CallGraph) : CallGraph := ⟨G.nodes ++ H.nodes, G.edges ++ H.edges⟩

end CallGraph

/-- The call-graph edges of one function's CFG: calls, tail jumps, imports, system calls. -/
def edgesOf {D : FlowDec} (f : Nat) (C : Graph D Ref) : List (Node × Node) :=
  let tgt : Target Ref → List Node
    | .fn a => [.fn a]
    | .ext r => [.ext r]
    | .blk _ => []
  let tgts : Option (List (Target Ref)) → List Node
    | some ts => ts.flatMap tgt
    | none => [.unresolved]
  C.blocks.flatMap fun b => (match b.term with
    | .jmp t | .call t _ => tgt t
    | .jmpInd ts _ | .callInd ts _ _ => tgts ts
    | .sys (some n) _ => [.sys n]
    | .sys none _ | .sysOther _ => [.sysAny]
    | _ => []).map fun n => (.fn f, n)

/-! ## Program certificates -/

/-- **A certificate** for the code of one file reached from `roots`: code windows, one CFG per
internal function, the address-taken entries (callbacks), and the call graph. -/
structure Cert (D : FlowDec) where
  img : Image
  fns : List (Nat × Graph D Ref)
  /-- Entries a library may call back (`main`, `DT_INIT_ARRAY`/`DT_FINI_ARRAY`, address-taken
  functions, exports). -/
  escapes : List Nat
  graph : CallGraph

/-- **The kernel check** (by `decide`): each CFG is closed (`cfg_sub`) with its key as entry;
every function target has a CFG; the escapes have CFGs; every derived edge is in the graph; every
import calls back to every escape. -/
def Cert.check {D : FlowDec} (P : Cert D) : Bool :=
  let has (a : Nat) := P.fns.any (·.1 = a)
  P.fns.all (fun (a, C) => C.entry = a && C.sub P.img &&
    (edgesOf a C).all fun e => P.graph.edges.contains e && (match e.2 with
      | .fn b => has b
      | _ => true)) &&
  P.escapes.all has &&
  P.graph.nodes.all fun n => match n with
    | .ext _ => P.escapes.all fun a => P.graph.edges.contains (n, .fn a)
    | _ => true

/-- The windows are code of `F`, and every address `F` exposes is listed in `escapes`
(`Escapes`: `e_entry`, `DT_INIT_ARRAY`/`DT_FINI_ARRAY` entries, `R_X86_64_RELATIVE` targets in
code, exported functions, `lea`/`mov` immediates into code; decidable from the parse and the
CFGs, design §5). -/
structure Cert.Faithful {D : FlowDec} (P : Cert D) (F : Blob) (Escapes : Nat → Prop) : Prop where
  code : ∀ w ∈ P.img, CodeAt F w.1 w.2
  escapes : ∀ a, Escapes a → a ∈ P.escapes

/-! ## The most general process -/

/-- An observable event of a step. -/
inductive Ev where
  /-- Any other step. -/
  | step
  /-- A `call`/`callInd` retired to `dst`, pushing the return address `ret`. -/
  | call (dst ret : Word)
  /-- A `jmp`/`jmpInd`/`jcc` retired to `dst`. -/
  | jump (dst : Word)
  | ret (dst : Word)
  /-- A direct system call with `rax = nr`. -/
  | sys (nr : Nat)
  /-- A library step of import `r`: returned (`none`) or called back to `dst`. -/
  | lib (r : Ref) (dst : Option Word)
  /-- A step from bytes the decoder does not read. -/
  | unknown
  deriving DecidableEq

/-- **A world**: the image machine and its decoder, where imports are bound (`lib`, from the
loader), the kernel (`K nr s t`, `t = none`: the process ended), and the library (`L r s t`,
from the bound address of `r` to a return or a callback, `t = none`: the process ended). -/
structure World (σ : Type) where
  J : UMach σ
  D : FlowDec
  lib : Word → Option Ref
  K : Nat → σ → Option σ → Prop
  L : Ref → σ → Option σ → Prop

variable {σ : Type}

/-- The bytes at `rip` that `D` reads as `i` of length `l`. -/
def World.At (W : World σ) (s : σ) (i : W.D.Instr) (l : Nat) : Prop :=
  ∃ w, (W.J.mem s).fetchBytes (W.J.core s).rip.toNat l = some w ∧ W.D.decode w = some (i, l)

/-- The event of a user step of kind `k`. -/
def evOf (k : Silmaril.X86.Flow.Kind) (s : State) (l : Nat) (t : State) : Ev :=
  match k with
  | .call _ | .callInd _ => .call t.rip (Silmaril.X86.Flow.next s l)
  | .jmp _ | .jmpInd _ | .jcc _ => .jump t.rip
  | .ret => .ret t.rip
  | _ => .step

/-- **One step of the most general process** with its event. -/
inductive Step (W : World σ) : Option σ → Ev → Option σ → Prop
  | user {s t i l} : W.lib (W.J.core s).rip = none → W.At s i l → W.D.kind i ≠ .syscall →
      W.J.step s t → Step W (some s) (evOf (W.D.kind i) (W.J.core s) l (W.J.core t)) (some t)
  | unknown {s t} : W.lib (W.J.core s).rip = none → (∀ i l, ¬ W.At s i l) → W.J.step s t →
      Step W (some s) .unknown (some t)
  | sys {s t i l} : W.lib (W.J.core s).rip = none → W.At s i l → W.D.kind i = .syscall →
      W.K ((W.J.core s).read .rax).toNat s t → Step W (some s) (.sys ((W.J.core s).read .rax).toNat) t
  | lib {s t r} : W.lib (W.J.core s).rip = some r → W.L r s t →
      Step W (some s) (.lib r (t.map fun u => (W.J.core u).rip)) t

/-- **Runs with their events**, while every state satisfies `keep` (a function's activation:
`rsp ≤ rsp₀`; a program: `True`). -/
inductive Run (W : World σ) (keep : σ → Prop) : Option σ → List Ev → Option σ → Prop
  | refl (x) : Run W keep x [] x
  | step {s e y es z} : keep s → Step W (some s) e y → Run W keep y es z →
      Run W keep (some s) (e :: es) z

/-- The activation of a function entered at `s₀`. -/
def Within (W : World σ) (s₀ s : σ) : Prop :=
  ((W.J.core s).read .rsp).toNat ≤ ((W.J.core s₀).read .rsp).toNat

/-- The call-graph node of a runtime address (an import's bound address, or an image function). -/
def nodeAt (W : World σ) (base a : Word) : Node :=
  match W.lib a with
  | some r => .ext r
  | none => .fn (a - base).toNat

/-- **The node of an event**, for the events a call graph constrains. -/
def Ev.node (W : World σ) (base : Word) : Ev → Option Node
  | .call a _ => some (nodeAt W base a)
  | .sys n => some (.sys n)
  | .lib _ (some a) => some (.fn (a - base).toNat)
  | .unknown => some .unresolved
  | _ => none

/-! ## The edge-respecting reading: a shadow stack of frames -/

/-- A frame: the node running, whether it is opaque (a frontier node of an open graph, or called
from one), and the return address its caller pushed. -/
abbrev Frame := Node × Bool × Option Word

/-- **One event on the shadow stack**; `none` when the event leaves `G` (an edge not in `G`, a
return to another address than the pushed one, an unknown instruction). Inside an opaque frame
nothing is checked but the nesting. A `jump` to the entry of a function node of `G` is a tail
call; any other jump is intraprocedural. -/
def walk (W : World σ) (base : Word) (G : CallGraph) (H : List Node) :
    List Frame → Ev → Option (List Frame)
  | [], _ => some []
  | f :: fs, e =>
    let edge (n : Node) : Bool := f.2.1 || G.edges.contains (f.1, n)
    let push (n : Node) (r : Option Word) : Option (List Frame) :=
      if edge n then some ((n, f.2.1 || H.contains n, r) :: f :: fs) else none
    match e with
    | .call a r => push (nodeAt W base a) (some r)
    | .jump a =>
      let n := nodeAt W base a
      if (G.nodes.contains n || (match n with | .ext _ => true | _ => false)) && n != f.1 then
        (if edge n then some ((n, f.2.1 || H.contains n, f.2.2) :: fs) else none)
      else some (f :: fs)
    | .ret a => if f.2.2 == some a || f.2.2 == none then some fs else none
    | .lib _ none => some fs
    | .lib _ (some a) => push (.fn (a - base).toNat) none
    | .sys n => if edge (.sys n) || edge .sysAny then some (f :: fs) else none
    | .unknown => if f.2.1 then some (f :: fs) else none
    | .step => some (f :: fs)

/-- **Every run from `s₀`, entered as `root`, respects `G`** (the open form: frames of `H` are
opaque). -/
def CallSubIn (W : World σ) (base : Word) (keep : σ → Prop) (s₀ : σ) (G : CallGraph)
    (H : List Node) (root : Node) : Prop :=
  ∀ es y, Run W keep (some s₀) es y → (es.foldlM (walk W base G H) [(root, H.contains root, none)]).isSome

/-! ## Admissible worlds: the side conditions -/

/-- **The kernel frame.** A system call resumes after the `syscall` (`rcx = rip`) and, unless it
is one of `codeNrs` (`mmap`, `mprotect`, `munmap`, `mremap`, `pkey_mprotect`, `shmat`,
`remap_file_pages`), keeps the image's read-only segments. -/
def codeNrs : List Nat := [9, 10, 11, 25, 31, 216, 329]

/-- **The library frame** (the most general library): from the bound address, it returns to the
popped return address, calls back to an escaped entry, or ends the process; it keeps the image's
read-only segments. -/
structure LibOk (W : World σ) (F : Blob) (base : Word) (escapes : List Nat) : Prop where
  ro : ∀ r s t, W.L r s (some t) → Link.ElfBind.RoLoaded F base (W.J.mem s) →
    Link.ElfBind.RoLoaded F base (W.J.mem t)
  dest : ∀ r s t, W.L r s (some t) →
    loadN (W.J.mem s) ((W.J.core s).read .rsp) 8 = some (W.J.core t).rip ∨
      ((W.J.core t).rip - base).toNat ∈ escapes

/-- The kernel keeps the read-only segments outside `codeNrs`. -/
def KOk (W : World σ) (F : Blob) (base : Word) : Prop :=
  ∀ n s t, W.K n s (some t) → n ∉ codeNrs → Link.ElfBind.RoLoaded F base (W.J.mem s) →
    Link.ElfBind.RoLoaded F base (W.J.mem t)

/-- **Code stability** along a run (W^X): the read-only segments stay loaded. Derived
(`Task.codeStable`) from the machine's write-permission discipline, the segments' flags, `LibOk`,
`KOk` and no `codeNrs` call touching them; a hypothesis until then. -/
def CodeStable (W : World σ) (F : Blob) (base : Word) (keep : σ → Prop) (s₀ : σ) : Prop :=
  ∀ es u, Run W keep (some s₀) es (some u) → Link.ElfBind.RoLoaded F base (W.J.mem u)

/-- **Indirect transfers stay in their resolved sets**: for every block whose terminator lists
targets (`got`, `table`, `assumed`), every step from it lands on a listed target; for `got`, the
slot holds the bound address of the import. `got` and `table` are discharged from RELRO and
read-only data (`Task.indirect_got`, `Task.indirect_table`); `assumed` stays a hypothesis. -/
def IndOk {D : FlowDec} (W : World σ) (base : Word) (P : Cert D) (keep : σ → Prop) (s₀ : σ) : Prop :=
  ∀ es u t, Run W keep (some s₀) es (some u) → W.J.step u t →
    ∀ a C, (a, C) ∈ P.fns → ∀ b ∈ C.blocks, ∀ ts why ret,
      (b.term = .jmpInd (some ts) why ∨ b.term = .callInd (some ts) why ret) →
      (W.J.core u).rip = base + BitVec.ofNat 64 (b.stop - (b.body.getLast?.map (·.2)).getD 0) →
      ∃ x ∈ ts, match x with
        | .blk c | .fn c => (W.J.core t).rip = base + BitVec.ofNat 64 c
        | .ext r => W.lib (W.J.core t).rip = some r

/-- **Returns go to a return site**: every `ret` lands on the return address of a call site of
the certificate, or leaves the activation. (The strong form, `RetDiscipline`, is the matching
call's address; it is what `CallSub` needs.) -/
def RetOk {D : FlowDec} (W : World σ) (base : Word) (P : Cert D) (keep : σ → Prop) (s₀ : σ) : Prop :=
  ∀ es a y, Run W keep (some s₀) (es ++ [.ret a]) y → (∀ u, y = some u → keep u) →
    ∃ f C, (f, C) ∈ P.fns ∧ ∃ b ∈ C.blocks, ∃ r,
      (b.term.succs.contains (r, false)) ∧ a = base + BitVec.ofNat 64 r

/-! ## Semantic statements -/

/-- **Every executed call, system call, import and callback from `s₀` is a node of `N`.** -/
def ReachIn (W : World σ) (base : Word) (keep : σ → Prop) (s₀ : σ) (N : List Node) : Prop :=
  ∀ es y, Run W keep (some s₀) es y → ∀ e ∈ es, ∀ n, e.node W base = some n → n ∈ N

/-- **Syscall summaries of imports**: `(r, ns)` says the import `r` makes at most the system
calls `ns` (and calls back only to escapes); an import without an entry is unknown. Proved per import from `SysWrap` or a
followed call graph of the library (`Effects.Libc`), or assumed. -/
abbrev Summ := List (Ref × List Nat)

/-- A node makes only system calls satisfying `ok`. -/
def Node.SysOk (summ : Summ) (ok : Nat → Prop) : Node → Prop
  | .fn _ => True
  | .ext r => ∃ ns, summ.lookup r = some ns ∧ ∀ n ∈ ns, ok n
  | .sys n => ok n
  | .sysAny | .unresolved => False

/-- **Every system call of every run satisfies `ok`** (an import counts as its summary). -/
def SyscallsOk (W : World σ) (base : Word) (keep : σ → Prop) (s₀ : σ) (summ : Summ)
    (ok : Nat → Prop) : Prop :=
  ∀ es y, Run W keep (some s₀) es y → ∀ e ∈ es, ∀ n, e.node W base = some n → n.SysOk summ ok

/-- **Every import called is in `I`.** -/
def ForeignIn (W : World σ) (base : Word) (keep : σ → Prop) (s₀ : σ) (I : Ref → Prop) : Prop :=
  ∀ es y, Run W keep (some s₀) es y → ∀ e ∈ es, ∀ r, e.node W base = some (.ext r) → I r

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

/-! ## The open theorems -/

/-- The setting of a statement: an admissible world, a placement, the certificate checked and
faithful, an entry state at `entry` with the image loaded, and the side conditions. -/
structure Setting {D : FlowDec} (W : World σ) (F : Blob) (base : Word) (P : Cert D)
    (Escapes : Nat → Prop) (entry : Nat) (keep : σ → Prop) (s₀ : σ) : Prop where
  law : FlowLaw W.J W.D
  dec : W.D = D
  check : P.check = true
  faithful : P.Faithful F Escapes
  placement : Placement F base.toNat
  lib : LibOk W F base P.escapes
  kernel : KOk W F base
  entry : (W.J.core s₀).rip = base + BitVec.ofNat 64 entry
  loaded : Link.ElfBind.RoLoaded F base (W.J.mem s₀)
  stable : CodeStable W F base keep s₀
  ind : IndOk W base P keep s₀
  ret : RetOk W base P keep s₀

/-- **Soundness of a certificate.** In every admissible world, every run from the entry of
`P`'s function `entry` (or from a callback) executes only calls, system calls, imports and
callbacks that are nodes reachable in `P.graph` from `entry` and the escapes. -/
def Task.sound : Prop :=
  ∀ {σ : Type} {D : FlowDec} (W : World σ) (F : Blob) (base : Word) (P : Cert D) Escapes entry keep s₀,
    Setting W F base P Escapes entry keep s₀ →
    ReachIn W base keep s₀ (P.graph.reach (.fn entry :: P.escapes.map .fn))

/-- **`no_spawn` from a call graph**: no reachable node spawns. -/
def Task.noSpawn_of_reach : Prop :=
  ∀ {σ : Type} (W : World σ) base keep s₀ (N : List Node) (summ : Summ),
    ReachIn W base keep s₀ N → (∀ n ∈ N, n.SysOk summ (notIn spawnNrs)) →
    SyscallsOk W base keep s₀ summ (notIn spawnNrs)

/-- **Monotone in the graph.** -/
def Task.reach_mono : Prop :=
  ∀ {σ : Type} (W : World σ) base keep s₀ (N N' : List Node),
    ReachIn W base keep s₀ N → (∀ n ∈ N, n ∈ N') → ReachIn W base keep s₀ N'

/-- **The strong reading implies the node reading.** -/
def Task.reach_of_callSub : Prop :=
  ∀ {σ : Type} (W : World σ) base keep s₀ G root,
    CallSubIn W base keep s₀ G [] root → ReachIn W base keep s₀ (G.reach [root])

end Silmaril.Elf.Effects
