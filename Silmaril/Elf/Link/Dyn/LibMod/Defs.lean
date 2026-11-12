module

public import Silmaril.Elf.Link.Dyn.Libc.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Extends.Defs

/-!
# Library modules: libraries with global state, and the C-runtime machine

A C library keeps **global state**: stdio's `FILE` objects and buffers, the allocator's arenas,
`errno`, the `atexit` list. A client cannot see that state except through the library's
functions. This module gives the standard pattern for such libraries:

* **A library module** (`LibModule`) is a pair
  - an **invariant** `Inv` over the memory the library **owns** (`own`) and the process ghost,
    local to them (`local_`: a state that agrees on the owned memory, the thread pointer and the
    ghost fields the module reads (`gEq`) keeps `Inv`);
  - its **functions** (`fns`), atomic process steps by name, each preserving `Inv`
    (`PreservesInv`) within the **frame convention** (`Framed`).
* **The frame convention** (`ModRet`): a call returns System V (`AbiReturn`, `fsBase` kept) and
  changes only (1) the memory its library owns, before or after the call, and (2) its own stack:
  the `budget` bytes below the entry `rsp` (the red zone is part of it), outside the process's
  kept memory (`World.Kept`). Permissions change only in owned memory. Dually, client code may
  not change owned memory at all: the C-runtime machine stops when it does (`crtStep`), so a
  client proof never owns library memory.
* **Relaxation** (`relax`): an existing contract of the process model (`Proc`, `Program.lib`)
  keeps the whole stack below `rsp`; real code writes its frame there, so no real function meets
  it. `relax W k` allows every outcome of `k` followed by any change of the scratch
  stack (`Havoc`). It is looser than `k` (`Thms.refines_relax`): every client proof against `relax
  W k` holds against `k`.
* **The C-runtime machine** (`crt M W`): the process model `Proc.proc W` (the executable's image
  run by `Open9`, every library call one atomic step) with (a) every library step relaxed and (b)
  the client steps that change `M`'s owned memory or the thread pointer stopped. `Thms.must_proc`:
  a `Must` on `crt` is a `Must` on `proc` (the converse is per program: `Task`s).
* **Composition** (`LibModule.sep`, `Thms.sep_frame`): two modules with disjoint ownership are a
  module (separating conjunction of their invariants); a call of one keeps the other's invariant.
* **Subsets** (`LibModule.Map`): `N` provides `M` when it owns the same memory, its invariant
  implies `M`'s and its functions refine `M`'s (`Thms.Map.spec_le`: then `M.spec ≤ N.spec` in the
  `LibcSpec` lattice).
* **Soundness** (`Real`, `Rel`, `Sim`, `Realises`): a deterministic machine `X.J` (Str9K with an
  I/O kernel, for glibc) whose states show an `MState` (an `Open9` lens) and what the kernel
  observed (`obs`). `Rel X M c a`: the real state `c` shows the machine state of `a`, satisfies
  `M`'s invariant and the kernel observed `a`'s ghost. `Sim`: every abstract step that makes a
  claim is matched by a real run segment. `Thms.must_real`: a `Must` on the abstract machine is a
  real run reaching the goal. `Thms.sim_crt`: `Sim (crt M W)` follows from one `Realises`
  obligation per library entry point (the gate of callbacks, each bound function, the lazy
  resolver): the client steps are proved once.

Nothing here is trusted: the realisation obligations are the open `Task`s of an instance
(`LibMod.Hello`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.LibMod

open Silmaril.X86 (Word Byte MState State)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Elf.Link.Dyn.Proc (PState Ghost World Keeps Contract)
open Silmaril.Elf.Link.Dyn.Libc (Step Refines LibcSpec)

/-! ## 1. The frame convention -/

/-- The stack a call may use below its entry `rsp` (it contains the 128-byte red zone). -/
def budget : Nat := 0x10000

/-- The entry stack pointer of a call. -/
abbrev rspOf (s : PState) : Word := s.m.core.read .rsp

/-- `a` is in the scratch stack of a call entered with stack pointer `sp`: `[sp - budget, sp)`. -/
def Scratch (sp : Word) (a : Nat) : Prop := sp.toNat - budget ≤ a ∧ a < sp.toNat

/-- **The bytes a call may write** from entry `s` to return `t`: the memory its library owns
before or after, and its scratch stack outside the process's kept memory. -/
def MayWrite (W : World) (own : PState → Nat → Prop) (s t : PState) (a : Nat) : Prop :=
  own s a ∨ own t a ∨ (Scratch (rspOf s) a ∧ ¬ W.Kept a)

/-- **The memory frame of a call**: every other mapped byte keeps its value, and permissions
change only in owned memory (so the unmapped memory a library maps becomes its own). -/
def Frame (W : World) (own : PState → Nat → Prop) (s t : PState) : Prop :=
  (∀ a, s.m.memory.permits .read a = true → ¬ MayWrite W own s t a →
    t.m.memory.bytes.get? a = s.m.memory.bytes.get? a) ∧
  (∀ a, ¬ own s a → ¬ own t a → ∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a)

/-- **The frame convention**: a System V return, the thread pointer kept, within the frame. -/
def ModRet (W : World) (own : PState → Nat → Prop) (s t : PState) : Prop :=
  AbiReturn s.m.core s.m.memory t.m.core ∧ t.m.core.fsBase = s.m.core.fsBase ∧ Frame W own s t

/-- The mapped bytes and the permissions of `P` are unchanged (the frame of the invariants: an
unreadable byte has no value a reader could see). -/
def KeepsR (P : Nat → Prop) (m m' : Memory) : Prop :=
  ∀ a, P a → (m.permits .read a = true → m'.bytes.get? a = m.bytes.get? a) ∧
    ∀ acc, m'.permits acc a = m.permits acc a

/-! ## 2. Relaxing a contract by the scratch stack -/

/-- `t` is `t0` with the scratch stack of the call entered at `s` changed: same core, ghost and
permissions, the same bytes outside the scratch stack. -/
def Havoc (W : World) (s t0 t : PState) : Prop :=
  t.m.core = t0.m.core ∧ t.g = t0.g ∧
  (∀ a, ¬ (Scratch (rspOf s) a ∧ ¬ W.Kept a) → t.m.memory.bytes.get? a = t0.m.memory.bytes.get? a) ∧
  ∀ a acc, t.m.memory.permits acc a = t0.m.memory.permits acc a

/-- **The relaxed step**: an outcome of `k`, then any change of the scratch stack. It claims
exactly where `k` does (`relax W k s .stop ↔ k s .stop`). -/
def relax (W : World) (k : Step) : Step := fun s r =>
  match r with
  | .stop => k s .stop
  | .ok t => ∃ t0, k s (.ok t0) ∧ Havoc W s t0 t

/-- A libc specification relaxed at every name. -/
def relaxSpec (L : LibcSpec) : LibcSpec :=
  ⟨L.syms.map fun e => (e.1, fun c => relax c.W (e.2 c))⟩

/-! ## 3. Library modules -/

/-- **A library module** (module doc): owned memory, an invariant local to it, functions. -/
structure LibModule where
  /-- The memory the library owns in a process state (its data, heap metadata, TLS, buffers). -/
  own : PState → Nat → Prop
  /-- The invariant: the owned memory represents a consistent library state, shown by the
  ghost. -/
  Inv : PState → Prop
  /-- The ghost fields the invariant reads: `gEq g g'` when they agree on them. -/
  gEq : Ghost → Ghost → Prop := Eq
  gEq_refl : ∀ g, gEq g g := by intro g; rfl
  /-- **Locality**: a state agreeing on the owned memory, the thread pointer and the ghost
  fields keeps the invariant, and owns the same memory. -/
  local_ : ∀ s t, KeepsR (own s) s.m.memory t.m.memory → t.m.core.fsBase = s.m.core.fsBase →
    gEq s.g t.g → Inv s → Inv t ∧ own t = own s
  /-- The functions, by name, as atomic steps in a process world. -/
  fns : List (Name × (World → Step))

namespace LibModule

variable (M : LibModule)

/-- The contract of the name `n` in world `W`; a stop off the module. -/
def named (W : World) (n : Name) : Step :=
  match M.fns.lookup n with
  | some k => k W
  | none => Libc.stopStep

/-- The module as a libc specification (each contract in the context's world). -/
def spec : LibcSpec := ⟨M.fns.map fun e => (e.1, fun c => e.2 c.W)⟩

/-- **The function preserves the invariant** where it makes a claim. -/
def PreservesInv (k : Step) : Prop :=
  ∀ s t, M.Inv s → ¬ k s .stop → k s (.ok t) → M.Inv t

/-- **The function keeps the frame convention** where it makes a claim. -/
def Framed (W : World) (k : Step) : Prop :=
  ∀ s t, M.Inv s → ¬ k s .stop → k s (.ok t) → ModRet W M.own s t

/-- **A well-formed module**: every function preserves the invariant within the frame. -/
def WF : Prop := ∀ W n k, M.fns.lookup n = some k → M.PreservesInv (k W) ∧ M.Framed W (k W)

/-- **A module contract** (the standard shape): from a System V entry in the invariant with
`pre`, a return within the frame convention, in the invariant, with `post`. -/
def contract (W : World) (pre : PState → Prop) (post : PState → PState → Prop) : Step :=
  fun s => Contract (AbiEntry s.m.core s.m.memory ∧ M.Inv s ∧ pre s)
    fun t => ModRet W M.own s t ∧ M.Inv t ∧ post s t

/-- Disjoint ownership. -/
def Disjoint (N : LibModule) : Prop := ∀ s a, M.own s a → N.own s a → False

/-- **The separating conjunction** of two modules: the union of their memory, both invariants,
the ghost fields of both, both function tables (`M`'s first). -/
def sep (N : LibModule) : LibModule where
  own s a := M.own s a ∨ N.own s a
  Inv s := M.Inv s ∧ N.Inv s
  gEq g g' := M.gEq g g' ∧ N.gEq g g'
  gEq_refl g := ⟨M.gEq_refl g, N.gEq_refl g⟩
  local_ s t hk hfs hg hi := by
    have h1 := M.local_ s t (fun a ha => hk a (Or.inl ha)) hfs hg.1 hi.1
    have h2 := N.local_ s t (fun a ha => hk a (Or.inr ha)) hfs hg.2 hi.2
    refine ⟨⟨h1.1, h2.1⟩, ?_⟩
    rw [h1.2, h2.2]
  fns := M.fns ++ N.fns

/-- **`N` provides the subset `M`** of a library: it owns the same memory, its invariant
implies `M`'s, and each function of `M` is a function of `N` refining it. -/
structure Map (N : LibModule) : Prop where
  own : N.own = M.own
  inv : ∀ s, N.Inv s → M.Inv s
  fns : ∀ n k, M.fns.lookup n = some k → ∃ k', N.fns.lookup n = some k' ∧ ∀ W, Refines (k' W) (k W)

end LibModule

/-! ## 4. The C-runtime machine -/

/-- A client step to `m'` keeps the owned memory of `M` and the thread pointer. -/
def OwnKept (M : LibModule) (s : PState) (m' : MState) : Prop :=
  KeepsR (M.own s) s.m.memory m'.memory ∧ m'.core.fsBase = s.m.core.fsBase

/-- **One step of the C-runtime machine** (module doc): an ended process stops; in the image,
`Open9`, stopping when the step would change owned memory or the thread pointer; elsewhere, the
library's step of `Proc`, relaxed by the scratch stack. -/
def crtStep (M : LibModule) (W : World) (s : PState) (r : Res PState) : Prop :=
  match s.g.done with
  | some _ => r = .stop
  | none =>
    if W.InImage s.m.core.rip.toNat then
      match Silmaril.X86.Open9.step s.m with
      | some m' => (OwnKept M s m' ∧ r = .ok ⟨m', s.g⟩) ∨ (¬ OwnKept M s m' ∧ r = .stop)
      | none => r = .stop
    else relax W (Proc.extStep W) s r

/-- **The C-runtime machine**: x86 user code, atomic library steps on opaque state. -/
def crt (M : LibModule) (W : World) : Silmaril.X86.RelIsa PState where
  core s := s.m.core
  mem s := s.m.memory
  upd s c m := { s with m := ⟨c, m⟩ }
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  live _ := True
  step := crtStep M W
  live_step _ _ := trivial

/-- The C-runtime machine must reach `Q`. -/
abbrev MustC (M : LibModule) (W : World) (Q : PState → Prop) (s : PState) : Prop :=
  Silmaril.X86.RelIsa.Must (crt M W) (fun _ => True) Q s

/-! ## 5. Soundness against a real machine -/

/-- **A real process machine**: a deterministic machine whose states show an `MState` (every
`Open9` step of the view is a step), and what its kernel has observed of the process, as a
ghost (the bytes written to file descriptors 1 and 2, the exit status), which the view does not
change. -/
structure Real where
  τ : Type
  J : Isa τ
  L : Silmaril.X86.Open9.isa.Extends J
  obs : τ → Ghost → Prop
  obs_put : ∀ c m g, obs (L.put c m) g ↔ obs c g

/-- **The abstraction**: the real state shows the machine state of `a`, satisfies the module's
invariant there, and its kernel observed `a`'s ghost. -/
def Rel (X : Real) (M : LibModule) (c : X.τ) (a : PState) : Prop :=
  X.L.view c = a.m ∧ M.Inv a ∧ X.obs c a.g

/-- **Stuttering simulation**: every abstract step that makes a claim (cannot stop) is matched
by a real run segment (possibly empty) to a related state after one of its outcomes. -/
def Sim {σ τ : Type} (A : Silmaril.X86.RelIsa σ) (step : τ → Option τ) (R : τ → σ → Prop) : Prop :=
  ∀ c a, R c a → ¬ A.step a .stop → ∃ a', A.step a (.ok a') ∧ ∃ c', Reaches step c c' ∧ R c' a'

/-- **The library's code at `e` realises the atomic step `k`**: from every related state at
`e` where `k` makes a claim, the real machine runs to a related state after an outcome of `k`. -/
def Realises (X : Real) (M : LibModule) (k : Step) (e : Word) : Prop :=
  ∀ c a, Rel X M c a → a.m.core.rip = e → a.g.done = none → ¬ k a .stop →
    ∃ a', k a (.ok a') ∧ ∃ c', Reaches X.J.step c c' ∧ Rel X M c' a'

/-- **The library realises the process world `W`**: the callback gate, every bound function and
the lazy resolver realise their relaxed `Proc` steps. -/
structure RealisesWorld (X : Real) (M : LibModule) (W : World) : Prop where
  gate : Realises X M (relax W (Proc.gateStep W)) W.gate
  fns : ∀ e f, (e, f) ∈ W.fns → e ≠ W.gate → Realises X M (relax W (Proc.fnStep W f)) e
  lazy : ∀ res slots, W.lazy = some (res, slots) → res ≠ W.gate →
    Realises X M (relax W (Proc.resolveStep W slots)) res

end Silmaril.Elf.Link.Dyn.LibMod
