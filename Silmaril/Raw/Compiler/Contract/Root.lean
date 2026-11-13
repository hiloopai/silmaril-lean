module

public import Silmaril.Machine.CBackend.Lir.Behaviour.Defs
public import Silmaril.Machine.X86.Lir.Behaviour.Defs
public import Silmaril.Compiler.Target.X86Layout.Defs
public import Silmaril.Compiler.Target.Runtime.Defs
public import Silmaril.Formats.ELF.Object
public import Silmaril.Foundations.InfiniteTrace

/-! # Correctness contracts of the stages of `ccomp`

The statement a stage of `ccomp` must prove to count as **validated** in the stage
registry (`Silmaril/Compile/Registry.lean`). Changing a contract, or adding one for a stage that has none,
is a reviewed change of its own.

The contract of registry row `key` is `Silmaril.Compile.Contract.key`. It is either

* a **predicate on the stage function** `Silmaril.Compile.Registry.Stage.key`, and the
  row's theorem must have the type `Contract.key Registry.Stage.key`, or
* a **proposition**, and the row's theorem must have the type `Contract.key`.

The evaluator checks the type up to definitional unfolding (`isDefEq`), and that the
theorem is sorry-free and uses only `propext`, `Classical.choice` and `Quot.sound`.
A stage whose key has no contract here cannot be validated: it stays in the trusted
base until its contract is written.

| key | contract | stage function |
|---|---|---|
| `asm` | none (see below) | `Stage.asm`: `C.Asm.lower`, GNU `asm` made droppable or rejected |
| `frontend` | none yet (needs a Lean semantics of typed Ail; csem) | `Stage.frontend`: Cabs parser, desugaring, typing |
| `lower` | none yet (needs a semantics of C or typed Ail; csem) | `Stage.lower`: typed Ail to Mir units |
| `link` | `link`: refines the independent Mir semantics `MirSem` (names, function values) | `Stage.link`: `Mir.link` |
| `mirOpt` | `mirPass`: refinement on `MirSem` at the identity convention | `Stage.mirOpt`: the registered Mir-to-Mir passes, in order |
| `renumber` | `lirPass`: refinement at the identity convention | `Stage.renumber`: `RegAlloc.renumber 7` |
| `spill` | `lirPass` | `Stage.spill`: `Lir.Alloc.spill (firstK 7)` |
| `codegen` | the statement of `X86.Backend.compile_refines`, for the stage function | `Stage.codegen`: `X86.Backend.compile` |
| `layout` | `X86.Backend.compile = compileX86Fast` (the `@[csimp]` replacement the executable runs) | none (a proposition) |
| `object` | `object`: the ELF round trip through `Formats.ELF.readObject` | `Stage.object`: ELF relocatable object |
| `rv64` | none (not on the evaluated x86-64 path; not counted) | `Stage.rv64`: the RISC-V backend |

**No contract for `asm`.** `C.Asm.lower` is not the identity on accepted texts: it
rewrites an empty-template `asm` with operands into a C comma expression (and drops
the others), so its correctness is a statement about the meaning of C, which needs the
C semantics (csem). A syntactic contract (text outside `asm` unchanged, no unsafe
`asm` left) would leave the rewritten expressions unconstrained and so would validate
the stage without verifying what it does.

**Rejection.** Every contract allows the stage to fail (`.error`): rejecting a program is
always correct. What a stage accepts is measured by the conformance and coverage tracks,
which a verify keep must hold.

A validator counts like a proof: a stage that runs an unverified transformation and a
checker, and falls back (or fails) when the checker rejects, proves the same contract
for the checked stage function.
-/

@[expose] public section

namespace Silmaril.Compile.Contract

open Silmaril.Machine
open Silmaril.Machine.Behaviour (Refines Mode Obs)
open Silmaril.X86 (Word Reg)
open Silmaril.X86.Backend

/-- **A Lir-to-Lir pass is a refinement at the identity convention**: for every
program, from start states of the same function, arguments and memory whose source
state is safe, every behaviour of the transformed program is a behaviour of the
original one (`Lir.Alloc.spill_refines` has this form). -/
def lirPass {V P : Type} [DecidableEq V] [DecidableEq P] (f : Lir.Prog V → Lir.Prog P) : Prop :=
  ∀ p : Lir.Prog V,
    Refines Mode.strict (Lir.sem (f p)) (Lir.sem p)
      (fun t s => ∃ fn args mem, p.start fn args mem = some s ∧ (f p).start fn args mem = some t)
      (fun _ _ => Obs.id)

/-- Register renumbering refines the program it renumbers. -/
def renumber (f : Lir.Prog Nat → Lir.Prog Nat) : Prop := lirPass f

/-- Spilling refines the program it spills. -/
def spill {P : Type} [DecidableEq P] (f : Lir.Prog Nat → Lir.Prog P) : Prop := lirPass f

/-- **The x86-64 code generator**: the statement of `X86.Backend.compile_refines`, for
the code generator `c` in place of `X86.Backend.compile`. -/
def codegen (c : ∀ {P : Type}, Assign P → Lir.Prog P → Nat → Except (List Error) Image) :
    Prop :=
  ∀ {P : Type} [DecidableEq P] (A : Assign P) (p : Lir.Prog P) (S : Space)
    {img : Image} (_hc : c A p S.codeBase = .ok img) (_hvalid : S.Valid img.code.length)
    (exit : Word) (E0 : Nat) (saved : Reg → Word) (_hhi : E0 + 8 ≤ S.stackHi)
    (_hlo : S.stackLo ≤ E0) (_halign : E0 % 16 = 8)
    (_hexit : exit.toNat < S.codeBase ∨ S.codeBase + img.code.length ≤ exit.toNat),
    let E : Env P := ⟨A, p, S, exit, E0, saved⟩
    Behaviour.Refines ⟨.strict, .allowed⟩ (Silmaril.X86.Ext.sem (Silmaril.X86.Ext.StackCheck.Exhausted S.stackLo E.stackSites))
      (Lir.sem p)
      (fun t s => ∃ lm main args init, lm.size = S.memSize ∧ p.start main args lm = some s ∧
        t = (exit, E.load lm main args init))
      (fun _ _ => ⟨fun final (vs, lm) => E.Final vs lm final, fun t lm => MemRel S lm t.memory,
        fun _ e => e.elim⟩)

/-- **The executed x86-64 layout is the verified one**: the executable runs
`compileX86Fast` in place of `X86.Backend.compile` (a `@[csimp]` lemma of this
statement). -/
def layout : Prop := @X86.Backend.compile = @Silmaril.Compile.Target.compileX86Fast

/-! ## `object`: the ELF writer round-trips

`Stage.object l q x` is the ELF relocatable object of the linked program `l`, spilled
to `q` and compiled to `x`: either the verified backend's image (`.inl img`) or the
native emitter's bytes and function offsets (`.inr (bytes, entries)`). `objectCode`
reads both as the code's bytes and function offsets: for `.inl img`, `img.code` and
`img.layout.func i` for each function `i` of `q`. Read back with the frozen reader
`Formats.ELF.readObject`, the object must be an x86-64 relocatable object with no
relocations, whose `.text` holds exactly those bytes (allocated, executable), whose
`.rodata.ccomp` holds exactly the initial memory image `l.image` (allocated, read-only),
with one global `FUNC` symbol in `.text` at offset `i` of the code for each named
function `i` of the link, the image symbols the startup code reads (`crt0`), and no two
symbols of the same name. The hypotheses bound the input (sizes that fit the ELF64
fields, names without NUL bytes and not clashing with the reserved `__ccomp_*` names);
none mentions the output. -/

/-- The bytes of a name as the reader returns them. -/
def nameBytes (s : String) : List (BitVec 8) := s.toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- A `ByteArray` as the reader's byte array. -/
def elfBytes (b : ByteArray) : Formats.ELF.Bytes := (b.toList.map fun x => BitVec.ofNat 8 x.toNat).toArray

/-- The section of `file` that a symbol lies in, by its section index. -/
def symSection (file : Formats.ELF.ObjectFile) (sym : Formats.ELF.ObjectSymbol) :
    Option Formats.ELF.ObjectSection :=
  file.sections[sym.raw.sectionIndex]?

/-- A global symbol `name` of kind `kind` with value `value`, in the section named `sec`
(`none`: absolute, `SHN_ABS`). -/
def HasSymbol (file : Formats.ELF.ObjectFile) (name : String) (kind : Nat) (sec : Option String)
    (value : Nat) : Prop :=
  ∃ sym ∈ file.symbols, sym.name = nameBytes name ∧ sym.kind = kind ∧ sym.binding = 1 ∧
    sym.raw.value = value ∧
    match sec with
    | some s => ∃ part, symSection file sym = some part ∧ part.name = nameBytes s
    | none => sym.raw.sectionIndex = 0xfff1

/-- An allocated `PROGBITS` section `name` with flags `flags` and contents `data`. -/
def HasSection (file : Formats.ELF.ObjectFile) (name : String) (flags : Nat)
    (data : Formats.ELF.Bytes) : Prop :=
  ∃ part ∈ file.sections, part.name = nameBytes name ∧ part.header.kind = 1 ∧
    part.header.flags = flags ∧ part.data = data

/-- The names the object reserves for the startup code and the dispatchers. -/
def reservedName (n : String) : Prop :=
  n ∈ ["__ccomp_image", "__ccomp_image_base", "__ccomp_image_size", "__ccomp_lmem_size",
    "__ccomp_ctl"] ∨ n.startsWith "__ccomp_dispatch."

/-- The code an object wraps, as the reader returns it: its bytes and the offset of each
function. The verified backend gives an image (bytes `img.code`, offsets
`img.layout.func i` for the functions of `q`); the native emitter gives both directly. -/
def objectCode (q : Lir.Prog (Fin 9)) : Image ⊕ (ByteArray × Array Nat) →
    Formats.ELF.Bytes × Array Nat
  | .inl img => (img.code.toArray, ((List.range q.funcs.length).map img.layout.func).toArray)
  | .inr (bytes, entries) => (elfBytes bytes, entries)

/-- **The object stage**: the bytes it writes read back as the object of the input. -/
def object (f : Mir.Linked → Lir.Prog (Fin 9) → Image ⊕ (ByteArray × Array Nat) → ByteArray) :
    Prop :=
  ∀ (l : Mir.Linked) (q : Lir.Prog (Fin 9)) (x : Image ⊕ (ByteArray × Array Nat)),
    -- names: no NUL byte, one name per function index, none reserved
    (∀ (n : String) (i : Nat), l.funcs[n]? = some i → '\x00' ∉ n.toList ∧ ¬ reservedName n) →
    (∀ (n m : String) (i : Nat), l.funcs[n]? = some i → l.funcs[m]? = some i → n = m) →
    -- sizes that fit the ELF64 fields
    (objectCode q x).1.size < 2 ^ 30 → l.image.size < 2 ^ 30 → (objectCode q x).2.size < 2 ^ 20 →
    (l.funcs.toList.map fun (n, _) => n.utf8ByteSize).sum < 2 ^ 28 →
    (∀ (i : Nat) (h : i < (objectCode q x).2.size), (objectCode q x).2[i] < 2 ^ 64) →
    l.dataBase < 2 ^ 64 →
    (∀ a : Nat, l.data[Target.ctlSymbol]? = some a → a < 2 ^ 64) →
    ∃ file, Formats.ELF.readObject (elfBytes (f l q x)) = some file ∧
      file.header.machine = 62 ∧ file.header.fileType = 1 ∧ file.relocations = [] ∧
      HasSection file ".text" 6 (objectCode q x).1 ∧
      HasSection file ".rodata.ccomp" 2 (elfBytes l.image) ∧
      (∀ (n : String) (i : Nat), l.funcs[n]? = some i → (h : i < (objectCode q x).2.size) →
        HasSymbol file n 2 (some ".text") (objectCode q x).2[i]) ∧
      HasSymbol file "__ccomp_image" 1 (some ".rodata.ccomp") 0 ∧
      HasSymbol file "__ccomp_image_base" 0 none l.dataBase ∧
      HasSymbol file "__ccomp_image_size" 0 none l.image.size ∧
      HasSymbol file "__ccomp_lmem_size" 0 none Target.memSize ∧
      (∀ a : Nat, l.data[Target.ctlSymbol]? = some a → HasSymbol file "__ccomp_ctl" 0 none a) ∧
      ((file.symbols.drop 1).map (·.name)).Nodup

/-! ## `link`: an independent semantics of Mir, refined by the link

Mir (`Silmaril/Compile/Mir/Syntax.lean`) has no semantics of its own in the compiler:
it is *defined* as the Lir semantics of its link, so a contract stated that way would
hold by definition. The contract below gives Mir a small-step semantics of its own,
`MirSem`, that resolves symbols **by name**:

* a direct `call f` runs the definition named `f` (a weak definition yields to a
  non-weak one of the same name);
* `callIndirect t` runs the function whose pointer value is the value of `t`, if its
  address is taken somewhere (`addr` or a relocation) and its parameter and result
  counts match the call; otherwise the call is undefined (stuck);
* `addr d s k` and relocations give the address of the data object `s` plus `k`, or the
  pointer of function `s`, or (`__mir_data_end`) the start of the free memory;
* data objects are placed in memory by a **placement** (`MirSem.Placement`): every
  object reachable from the entry has an address, nonzero, aligned, inside the memory,
  below the free memory and disjoint from the others; every reachable function has a
  distinct nonzero pointer below `2 ^ 64`. The initial memory holds each placed object's
  bytes (its `init`, zeros, then its relocations) and zeros elsewhere;
* straight-line operations and terminators are Lir's (`Lir.Op.exec`, `Lir.Term`), on one
  frame of virtual registers per activation.

The stage must then prove: when the link succeeds and the data fits the memory, there is
a valid placement such that every non-stuck behaviour (return with values and memory,
trap with memory, divergence) of the Mir program from its entry is a behaviour of the
linked Lir program from function 0 with the link's image loaded at `dataBase`. This is
what the link implements and could get wrong: name resolution and weak definitions,
function indices, dead-code elimination, the dispatchers of indirect calls, data layout,
the image and its relocations. A link that produces nothing (no start state) fails it on
every program with a behaviour; rejecting a program (`.error`) is allowed, as for every
stage, and is what the conformance track measures. -/

namespace MirSem

/-- The symbol whose address is the start of the free memory. -/
def heapSymbol : String := "__mir_data_end"

/-- Names with a non-weak definition (function or data). -/
def strongNames (us : Array Mir.Unit) : List String :=
  us.toList.flatMap fun u => (u.funcs.toList.filter (!·.weak)).map (·.name) ++
    (u.data.toList.filter (!·.weak)).map (·.name)

/-- The function definitions in force: a weak one yields to a non-weak one. -/
def funcDefs (us : Array Mir.Unit) : List Mir.Func :=
  (us.toList.flatMap (·.funcs.toList)).filter fun f => !f.weak || !(strongNames us).contains f.name

/-- The data definitions in force. -/
def dataDefs (us : Array Mir.Unit) : List Mir.Data :=
  (us.toList.flatMap (·.data.toList)).filter fun d => !d.weak || !(strongNames us).contains d.name

def funcOf (us : Array Mir.Unit) (n : String) : Option Mir.Func := (funcDefs us).find? (·.name == n)
def dataOf (us : Array Mir.Unit) (n : String) : Option Mir.Data := (dataDefs us).find? (·.name == n)

/-- The symbols an instruction refers to by name. -/
def instrRefs : Mir.Instr → List String
  | .addr _ s _ => [s]
  | .call s _ _ => [s]
  | _ => []

/-- Whether the address of `n` is taken somewhere (`addr` or a relocation). -/
def taken (us : Array Mir.Unit) (n : String) : Bool :=
  us.any fun u => u.funcs.any (fun f => f.blocks.any fun b => b.instrs.any fun
      | .addr _ s _ => s == n
      | _ => false) ||
    u.data.any fun d => d.relocs.any (·.sym == n)

/-- The symbols reachable from the entry (the first function in force) through calls,
`addr` and relocations. -/
inductive Reach (us : Array Mir.Unit) : String → Prop
  | entry {f : Mir.Func} : (funcDefs us).head? = some f → Reach us f.name
  | func {n s : String} {f : Mir.Func} {b : Mir.Block} {i : Mir.Instr} : Reach us n →
      funcOf us n = some f → b ∈ f.blocks.toList → i ∈ b.instrs.toList → s ∈ instrRefs i →
      Reach us s
  | data {n : String} {d : Mir.Data} {r : Mir.Reloc} : Reach us n → dataOf us n = some d →
      r ∈ d.relocs → Reach us r.sym

/-- Where data objects go and what function pointers are. -/
structure Placement where
  data : String → Option Nat
  func : String → Option Nat
  heap : Nat

/-- A valid placement for a memory of `memSize` bytes. -/
def Placement.Valid (us : Array Mir.Unit) (memSize : Nat) (P : Placement) : Prop :=
  (∀ s, Reach us s → (dataOf us s).isSome → (P.data s).isSome) ∧
  (∀ s, Reach us s → (dataOf us s).isNone → (funcOf us s).isSome → (P.func s).isSome) ∧
  (∀ d ∈ dataDefs us, ∀ a, P.data d.name = some a →
    0 < a ∧ a + d.size ≤ P.heap ∧ (d.align ≤ 1 ∨ a % d.align = 0)) ∧
  (∀ d ∈ dataDefs us, ∀ d' ∈ dataDefs us, d.name ≠ d'.name → ∀ a a',
    P.data d.name = some a → P.data d'.name = some a' → a + d.size ≤ a' ∨ a' + d'.size ≤ a) ∧
  P.heap ≤ memSize ∧
  (∀ s a, P.func s = some a → 0 < a ∧ a < 2 ^ 64) ∧
  (∀ s s' a, P.func s = some a → P.func s' = some a → s = s')

/-- The value of a symbol: a data address, the start of the free memory, or a function
pointer. -/
def symValue (us : Array Mir.Unit) (P : Placement) (s : String) : Option Nat :=
  if s = heapSymbol then some P.heap else
  match dataOf us s with
  | some _ => P.data s
  | none => if (funcOf us s).isSome then P.func s else none

/-- Byte `k` of the initial contents of object `d`: its `init`, zeros, then its
relocations in order (each the 8-byte little-endian value of its symbol plus addend). -/
def objectByte (us : Array Mir.Unit) (P : Placement) (d : Mir.Data) (k : Nat) : BitVec 8 :=
  d.relocs.foldl (fun acc r j =>
      if r.offset ≤ j ∧ j < r.offset + 8 then
        LittleEndian.wordByte
          (BitVec.ofNat 64 (Int.toNat (((symValue us P r.sym).getD 0 : Int) + r.addend)))
          (j - r.offset)
      else acc j)
    (fun j => if h : j < d.init.size then BitVec.ofNat 8 d.init[j].toNat else 0) k

/-- The initial memory: each placed object's bytes, zeros elsewhere. -/
def initMem (us : Array Mir.Unit) (P : Placement) (memSize : Nat) : Lir.Memory :=
  ⟨memSize, fun a =>
    match (dataDefs us).find? (fun d => match P.data d.name with
      | some b => decide (b ≤ a ∧ a < b + d.size)
      | none => false) with
    | some d => objectByte us P d (a - (P.data d.name).getD 0)
    | none => 0⟩

/-- A suspended caller: where it resumes and the registers that receive the results. -/
structure Act where
  func : Mir.Func
  label : Nat
  index : Nat
  frame : Lir.Frame Nat
  results : List Nat

structure State where
  func : Mir.Func
  label : Nat
  index : Nat
  frame : Lir.Frame Nat
  stack : List Act
  mem : Lir.Memory

inductive Result where
  | running (s : State)
  | returned (values : List Lir.Word) (mem : Lir.Memory)
  | trapped (mem : Lir.Memory)
  | stuck

/-- The fresh frame of a call of `fn` on `vals`. -/
def enter (fn : Mir.Func) (vals : List Lir.Word) : Option (Lir.Frame Nat) :=
  Lir.Frame.empty.writeAll (fn.params.map .reg) vals

/-- Call `fn` from `s`, the results going to `res`. -/
def call (s : State) (fn : Mir.Func) (vals : List Lir.Word) (res : List Nat) : Result :=
  match enter fn vals with
  | some fr => .running ⟨fn, 0, 0, fr, ⟨s.func, s.label, s.index, s.frame, res⟩ :: s.stack, s.mem⟩
  | none => .stuck

/-- The function an indirect call with value `v`, `n` arguments and `r` results runs. -/
def target (us : Array Mir.Unit) (P : Placement) (v : Lir.Word) (n r : Nat) : Option Mir.Func :=
  (funcDefs us).find? fun g => taken us g.name &&
    (match P.func g.name with
      | some a => BitVec.ofNat 64 a == v
      | none => false) &&
    g.params.length == n && g.results == r

def step (us : Array Mir.Unit) (P : Placement) (s : State) : Result :=
  match s.func.blocks[s.label]? with
  | none => .stuck
  | some b =>
    match b.instrs[s.index]? with
    | some (.op o) =>
      match o.exec s.frame s.mem with
      | some (fr, m) => .running { s with index := s.index + 1, frame := fr, mem := m }
      | none => .stuck
    | some (.fop op d x y) =>
      -- as Lir's `fop` (`Lir.FOp.exec`: `FOp.eval` under `Lir.floatProfile`)
      match Lir.FOp.exec op d x y s.frame with
      | some fr => .running { s with index := s.index + 1, frame := fr }
      | none => .stuck
    | some (.addr d sym off) =>
      match symValue us P sym with
      | some v =>
        let fr := s.frame.set d (BitVec.ofNat 64 (v + off))
        .running { s with index := s.index + 1, frame := fr }
      | none => .stuck
    | some (.call callee args res) =>
      match funcOf us callee, s.frame.readAll (args.map .reg) with
      | some fn, some vals => call s fn vals res
      | _, _ => .stuck
    | some (.callIndirect t args res) =>
      match s.frame.get t, s.frame.readAll (args.map .reg) with
      | some v, some vals =>
        match target us P v args.length res.length with
        | some fn => call s fn vals res
        | none => .stuck
      | _, _ => .stuck
    | none =>
      if s.index ≠ b.instrs.size then .stuck else
      match b.term with
      | .jump l => .running { s with label := l, index := 0 }
      | .branch c l₁ l₂ =>
        match s.frame.get c with
        | some x => .running { s with label := if x = 0 then l₂ else l₁, index := 0 }
        | none => .stuck
      | .ret locs =>
        match s.frame.readAll locs with
        | none => .stuck
        | some vals =>
          match s.stack with
          | [] => .returned vals s.mem
          | a :: rest =>
            match a.frame.writeAll (a.results.map .reg) vals with
            | some fr => .running ⟨a.func, a.label, a.index + 1, fr, rest, s.mem⟩
            | none => .stuck
      | .trap => .trapped s.mem

def Step (us : Array Mir.Unit) (P : Placement) (s s' : State) : Prop := step us P s = .running s'

/-- The start state: the entry (the first function in force) on no arguments. -/
def start (us : Array Mir.Unit) (P : Placement) (memSize : Nat) : Option State :=
  (funcDefs us).head?.bind fun fn =>
    (enter fn []).map fun fr => ⟨fn, 0, 0, fr, [], initMem us P memSize⟩

/-- The behaviours of a Mir state, in Lir's vocabulary. -/
def Behaves (us : Array Mir.Unit) (P : Placement) (s : State) : Lir.Behavior → Prop
  | .returned vs m => ∃ t, Relation.ReflTransGen (Step us P) s t ∧ step us P t = .returned vs m
  | .trapped m => ∃ t, Relation.ReflTransGen (Step us P) s t ∧ step us P t = .trapped m
  | .stuck => ∃ t, Relation.ReflTransGen (Step us P) s t ∧ step us P t = .stuck
  | .diverges => Silmaril.InfiniteTrace (Step us P) s

/-- The bytes the data of `us` needs from `base`, at most (sizes, alignments and the
final page). -/
def need (us : Array Mir.Unit) (base : Nat) : Nat :=
  base + ((us.toList.flatMap (·.data.toList)).map fun d => d.size + d.align).sum + 4096

end MirSem

/-- The memory a linked program starts with: its image at `dataBase`, zeros elsewhere. -/
def linkedMem (l : Mir.Linked) (memSize : Nat) : Lir.Memory :=
  ⟨memSize, fun a =>
    if h : l.dataBase ≤ a ∧ a < l.dataBase + l.image.size then
      BitVec.ofNat 8 (l.image[a - l.dataBase]'(by omega)).toNat
    else 0⟩

/-- **The link stage**: refines the independent Mir semantics `MirSem` (see above). -/
def link (f : Array Mir.Unit → Except String Mir.Linked) : Prop :=
  ∀ (us : Array Mir.Unit) (l : Mir.Linked), f us = .ok l →
    ∀ memSize, MirSem.need us Target.layout.dataBase ≤ memSize → memSize ≤ 2 ^ 64 →
    ∃ P : MirSem.Placement, P.Valid us memSize ∧
      ∀ s, MirSem.start us P memSize = some s → ∀ b, MirSem.Behaves us P s b → b ≠ .stuck →
        ∃ t, l.prog.start 0 [] (linkedMem l memSize) = some t ∧ Lir.Behaves l.prog t b

/-! ## `mirPass`: a Mir-to-Mir pass refines the independent Mir semantics

A Mir-to-Mir pass (an optimization between `lower` and `link`: constant folding, copy
propagation, dead-code elimination, inlining) maps units to units. It is correct when the
program it produces refines the one it is given on `MirSem`, at the identity convention
(the same values and the same memory observed):

* **data size**: it needs no more data memory than its input (`MirSem.need`), so the link
  contract's hypothesis on the output follows from the one on the input;
* **placements**: for every valid placement `P'` of the output (the link chooses one) there
  is a valid placement `P` of the input, over the same memory, such that, whenever the input
  has an entry state `s` under `P`:
  * **entry**: the output has an entry state under `P'`;
  * **refinement** (backward, as `lirPass`'s `Refines Mode.strict`): every behaviour `b` of
    the output from its entry is matched by a behaviour `b'` of the input from `s` that is
    `b` itself or `.stuck`. Once the input gets stuck (undefined), anything is allowed.

The direction is the one of refinement: the output adds no behaviour that the input does
not have, whether or not `MirSem` is deterministic. The entry clause excludes the vacuous
pass that produces a program with no entry, which refines everything backward. Because
`MirSem.step` is a function, each state has exactly one behaviour, so the backward clause
and the entry clause give the forward direction that `link` uses: every non-stuck behaviour
of the input is a behaviour of the output. Hence, if `L` proves `link` and `f` proves
`mirPass`, then `L ∘ f` proves `link` (`Mir.Pass.link_comp`); the identity and the
composite of two passes prove `mirPass`.

The statement is about `MirSem` only, not about the syntax of Mir, so a pass proved in
another dialect (an SSA or λSSA embedding of Mir functions with a semantics-preservation
lemma) discharges it through that embedding. A pass that makes a placed data
object unreachable changes the initial memory, which the identity convention observes; it
does not prove this contract. Dead-global removal will have a contract key of its own,
with a convention that forgets the removed objects. -/

/-- **A Mir-to-Mir pass refines its input on `MirSem`** (see above). -/
def mirPass (f : Array Mir.Unit → Array Mir.Unit) : Prop :=
  ∀ us : Array Mir.Unit,
    (∀ base, MirSem.need (f us) base ≤ MirSem.need us base) ∧
    ∀ memSize, memSize ≤ 2 ^ 64 → ∀ P' : MirSem.Placement, P'.Valid (f us) memSize →
      ∃ P : MirSem.Placement, P.Valid us memSize ∧
        ∀ s, MirSem.start us P memSize = some s →
          (∃ t, MirSem.start (f us) P' memSize = some t) ∧
          ∀ t, MirSem.start (f us) P' memSize = some t → ∀ b, MirSem.Behaves (f us) P' t b →
            ∃ b', MirSem.Behaves us P s b' ∧ (b' = .stuck ∨ b' = b)

/-- **The Mir optimizer**: the registered Mir-to-Mir passes, run in order, refine their
input (`mirPass`). -/
def mirOpt (f : Array Mir.Unit → Array Mir.Unit) : Prop := mirPass f

end Silmaril.Compile.Contract
