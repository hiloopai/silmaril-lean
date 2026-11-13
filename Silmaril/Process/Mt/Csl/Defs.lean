module


/-!
# Thread-modular decomposition of multi-threaded verification problems

A multi-threaded program is verified by verifying **each thread on its own**: its code runs on a
single-threaded machine, calls of trusted *primitives* (mutex, recursive lock, atomics, lock-free
lists, futex) are single atomic steps given by abstract specifications, and the thread owns a part
of memory. Shared state lives in a **resource invariant** `I`, and a primitive call may move
ownership between the thread and `I` (concurrent separation logic, with atomic primitives as the
only places where ownership moves). `Mt/Csl/Thms` proves that the per-thread problems compose:
the multi-threaded system (sequentially consistent interleaving, atomic primitives) never faults,
has no data race, keeps `I`, and every finished thread meets its postcondition.

## The pieces

* `Heap A V`: partial maps from addresses to values (owned memory, or the invariant's memory),
  with `Disjoint`, `union`, `Sub` (containment) and `DomLe` (domain inclusion).
* `Store M A V`: how a memory `M` is read cell by cell (`get : M → A → Option V`). `Agrees h m`
  (the heap is a fragment of `m`), `Keeps h m m'` (cells outside `h` unchanged), `cut h m'` (the
  values of `m'` on the domain of `h`). The x86 instance reads the bytes of
  `Silmaril.Process.Memory`; abstract primitive state (lock owners) and ghost state are further
  cells of a sum of address types, so they can be owned and put in invariants like bytes.
* `TIsa S`: **one thread's machine** over memories of the store `S`, with three kinds of steps:
  *plain* steps (`step`, `fault`, footprint `fp`), *atomic* steps (`atom`, `afault`: a trusted
  primitive, a system call, a library-contract step) and `clone` (`spawn`); `done` marks finished
  states. `TIsa.ofRel` builds one from any single-threaded step relation on `(state, memory)`
  pairs (such as a `Silmaril.X86.RelIsa` machine whose memory view is the shared memory) and
  primitive call sites.
* `PrimSpec`: a trusted primitive's **abstract, logically atomic specification**: when a call
  faults, and its one atomic step (memory before, result, memory after: the linearization
  point). `Prims σ M`: primitive call sites (`call s = some (p, args)`, resumed by `resume s r`)
  and their specs; `Prims.atom` and `Prims.afault` are the atomic steps they contribute.
* `Cfg U`, `Step U`, `Reach U`: the **multi-threaded system**: a thread table and one memory;
  a step is a plain or atomic step of one thread, or a `clone` to a fresh thread id. This is
  sequentially consistent interleaving with atomic primitives.
* `Fault`, `Race`: some thread can fault (plainly or atomically); two threads' next plain steps
  access a common address.

## The single-threaded problem

`Safe I Q t s h` (thread `t` in state `s` owning `h` is safe, ending in `Q`): the greatest
post-fixed point of `SafeF`, given by a witness relation `R` (the thread's invariant). Every
obligation of `SafeF` speaks about **one thread only**, quantifying over every memory that agrees
with what it owns (whatever the other threads did):

* finished: `done s → Q t s h`;
* plain step (`LocOk`): from every memory `m ⊇ h`, no fault, the footprint is owned, the step
  changes nothing outside `h`, and the successor is safe on `cut h m'`;
* atomic step (`AtomOk`, an instance of `AtomicOk`; `PrimOk` for one primitive spec): for every
  invariant heap `hI ⊨ I` disjoint from `h` and every memory `m ⊇ h ∪ hI`, no fault, the step
  changes nothing outside `h ∪ hI`, and the result re-splits into a new owned heap and a new
  invariant heap (within the old domain) with `I` holding again and the successor safe
  (**lock acquire moves the protected region in, release moves it out**);
* `clone` (`SpawnOk`): as an atomic step, whose new owned heap splits into the parent's part and
  the child's part, both safe (the child under its new id).

`GInv I Q C hs hI`: the **compatibility conditions**: pairwise disjoint owned heaps, disjoint from
the invariant heap `hI ⊨ I`, all fragments of memory, no heap for an absent thread, and every
thread safe on its heap. `Good I Q C` is the global property delivered by the adequacy theorem.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Csl

/-! ## Heaps -/

/-- A partial heap: address to value. -/
abbrev Heap (A V : Type) := A → Option V

namespace Heap

variable {A V : Type}

/-- The empty heap. -/
def empty : Heap A V := fun _ => none

/-- Disjoint domains. -/
def Disjoint (h₁ h₂ : Heap A V) : Prop := ∀ a, h₁ a = none ∨ h₂ a = none

/-- Left-biased union (a disjoint union when the domains are disjoint). -/
def union (h₁ h₂ : Heap A V) : Heap A V := fun a => (h₁ a).or (h₂ a)

/-- Containment: `h` is a fragment of `g`. -/
def Sub (h g : Heap A V) : Prop := ∀ a v, h a = some v → g a = some v

/-- Domain inclusion. -/
def DomLe (h g : Heap A V) : Prop := ∀ a, (h a).isSome → (g a).isSome

/-- Update one entry of a family. -/
def upd {α : Type} (f : Nat → α) (t : Nat) (x : α) : Nat → α := fun u => if u = t then x else f u

end Heap

/-- A heap assertion. -/
abbrev HProp (A V : Type) := Heap A V → Prop

/-! ## Memories read cell by cell -/

/-- **How a memory is read cell by cell.** -/
structure Store (M A V : Type) where
  get : M → A → Option V

namespace Store

variable {M A V : Type} (S : Store M A V)

/-- The heap is a fragment of the memory. -/
def Agrees (h : Heap A V) (m : M) : Prop := ∀ a v, h a = some v → S.get m a = some v

/-- From `m` to `m'`, no cell outside the domain of `h` changed. -/
def Keeps (h : Heap A V) (m m' : M) : Prop := ∀ a, h a = none → S.get m' a = S.get m a

/-- The values of `m` on the domain of `h`. -/
def cut (h : Heap A V) (m : M) : Heap A V := fun a => (h a).bind fun _ => S.get m a

end Store

/-! ## One thread's machine -/

/-- **One thread's machine** over the memories of a store, as the multi-threaded system sees it.
Thread ids are `Nat`. A thread takes three kinds of steps:

* **plain** steps (`step`, faulting per `fault`): ordinary instructions, which must touch only
  what the thread owns; `fp` is the set of addresses the next one accesses;
* **atomic** steps (`atom`, faulting per `afault`): one indivisible action on the shared state,
  such as a trusted primitive (`Prims.atom`), a system call or a library-contract step; they may
  touch the invariant's state;
* `clone` (`spawn t u s m s₁ s₂ m'`): thread `t` creates thread `u`; the parent continues as
  `s₁`, the child starts as `s₂`, the memory becomes `m'` (as an atomic step).

`done s`: the thread has finished (its postcondition is checked there). -/
structure TIsa {M A V : Type} (S : Store M A V) where
  /-- Thread states (registers, `rip`, thread-local ghost state; not the shared memory). -/
  St : Type
  /-- A plain step of thread `t`: `(s, m)` to `(s', m')`. -/
  step : Nat → St → M → St → M → Prop
  /-- A plain step of thread `t` from `(s, m)` faults (undefined behaviour, unmodelled). -/
  fault : Nat → St → M → Prop
  /-- The addresses the next plain step of thread `t` from `(s, m)` accesses. -/
  fp : Nat → St → M → A → Prop
  /-- An atomic step of thread `t`: `(s, m)` to `(s', m')`. -/
  atom : Nat → St → M → St → M → Prop
  /-- An atomic step of thread `t` from `(s, m)` faults (a primitive's precondition fails). -/
  afault : Nat → St → M → Prop
  /-- `clone` by thread `t` creating thread `u`. -/
  spawn : Nat → Nat → St → M → St → St → M → Prop
  /-- A finished thread. -/
  done : St → Prop

/-- **A trusted primitive's abstract, logically atomic specification.** `step t args m r m'`:
one atomic step by thread `t` from memory `m` returning `r` with memory `m'` (its linearization
point); no step means the call blocks. `fault t args m`: calling it here is an error. -/
structure PrimSpec (M : Type) where
  fault : Nat → List Nat → M → Prop
  step : Nat → List Nat → M → Nat → M → Prop

/-- **Primitive call sites** of thread states `σ`: `call s = some (p, args)` when `s` is at a
call of primitive `p`, resumed with result `r` as `resume s r`; `spec p` is its specification. -/
structure Prims (σ M : Type) where
  Prim : Type
  call : σ → Option (Prim × List Nat)
  resume : σ → Nat → σ
  spec : Prim → PrimSpec M

namespace Prims

variable {σ M : Type} (P : Prims σ M)

/-- The atomic steps of the primitive calls. -/
def atom (t : Nat) (s : σ) (m : M) (s' : σ) (m' : M) : Prop :=
  ∃ p args r, P.call s = some (p, args) ∧ (P.spec p).step t args m r m' ∧ s' = P.resume s r

/-- A primitive call that faults. -/
def afault (t : Nat) (s : σ) (m : M) : Prop :=
  ∃ p args, P.call s = some (p, args) ∧ (P.spec p).fault t args m

end Prims

namespace TIsa

variable {M A V : Type} {S : Store M A V}

/-- **A thread machine from a single-threaded step relation** on `(state, memory)` pairs and
primitive call sites: `step t (s, m) (some (s', m'))` is a plain step and
`step t (s, m) none` a fault (the `Silmaril.X86.RelIsa.Res.stop` outcome); the atomic steps are
the primitive calls of `P`. -/
def ofRel {σ : Type} (step : Nat → σ × M → Option (σ × M) → Prop)
    (fp : Nat → σ → M → A → Prop) (P : Prims σ M)
    (spawn : Nat → Nat → σ → M → σ → σ → M → Prop) (done : σ → Prop) : TIsa S where
  St := σ
  step t s m s' m' := step t (s, m) (some (s', m'))
  fault t s m := step t (s, m) none
  fp := fp
  atom := P.atom
  afault := P.afault
  spawn := spawn
  done := done

end TIsa

/-! ## The multi-threaded system (SC interleaving, atomic steps) -/

/-- A configuration: the thread table (`none`: no thread with that id) and the memory. -/
structure Cfg {M A V : Type} {S : Store M A V} (U : TIsa S) where
  th : Nat → Option U.St
  mem : M

/-- **One step of the multi-threaded system**: a plain or atomic step of one thread, or a
`clone` to a fresh thread id. -/
inductive Step {M A V : Type} {S : Store M A V} (U : TIsa S) : Cfg U → Cfg U → Prop
  | loc {C : Cfg U} {t : Nat} {s s' : U.St} {m' : M} (hs : C.th t = some s)
      (h : U.step t s C.mem s' m') : Step U C ⟨Heap.upd C.th t (some s'), m'⟩
  | atom {C : Cfg U} {t : Nat} {s s' : U.St} {m' : M} (hs : C.th t = some s)
      (h : U.atom t s C.mem s' m') : Step U C ⟨Heap.upd C.th t (some s'), m'⟩
  | spawn {C : Cfg U} {t u : Nat} {s s₁ s₂ : U.St} {m' : M} (hs : C.th t = some s)
      (hu : C.th u = none) (h : U.spawn t u s C.mem s₁ s₂ m') :
      Step U C ⟨Heap.upd (Heap.upd C.th t (some s₁)) u (some s₂), m'⟩

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl {a : α} : Star r a a
  | step {a b c : α} (h : r a b) (h' : Star r b c) : Star r a c

/-- Reachability of the multi-threaded system. -/
abbrev Reach {M A V : Type} {S : Store M A V} (U : TIsa S) : Cfg U → Cfg U → Prop :=
  Star (Step U)

/-- **Some thread can fault**: a plain step, or an atomic one (a primitive's precondition). -/
def Fault {M A V : Type} {S : Store M A V} (U : TIsa S) (C : Cfg U) : Prop :=
  ∃ t s, C.th t = some s ∧ (U.fault t s C.mem ∨ U.afault t s C.mem)

/-- **A data race**: two different threads whose next plain steps access a common address.
(Atomic steps never race.) -/
def Race {M A V : Type} {S : Store M A V} (U : TIsa S) (C : Cfg U) : Prop :=
  ∃ t u s s' a, t ≠ u ∧ C.th t = some s ∧ C.th u = some s' ∧ U.fp t s C.mem a ∧
    U.fp u s' C.mem a

/-! ## The single-threaded problem -/

section Safe

variable {M A V : Type} {S : Store M A V} (U : TIsa S)

/-- **The obligations of a plain step** of thread `t` in state `s` owning `h`, whose successors
must satisfy `K`: from every memory agreeing with `h`, no fault, the footprint is owned, nothing
outside `h` changes, and `K` holds of the successor and the new values of the owned cells. -/
def LocOk (K : U.St → Heap A V → Prop) (t : Nat) (s : U.St) (h : Heap A V) : Prop :=
  ∀ m, S.Agrees h m →
    ¬ U.fault t s m ∧ (∀ a, U.fp t s m a → (h a).isSome) ∧
    ∀ s' m', U.step t s m s' m' → S.Keeps h m m' ∧ K s' (S.cut h m')

/-- **The obligations of an atomic action** `act` (with fault predicate `bad`) of a thread
owning `h`, whose outcomes `o` must satisfy `K o h'` (`h'` the new owned heap): for every
invariant heap `hI ⊨ I` disjoint from `h` and every memory agreeing with both, no fault; every
outcome keeps the cells outside `h ∪ hI` and re-splits (part of) `h ∪ hI` into a new owned heap
and a new invariant heap, with `I` holding again. -/
def AtomicOk {O : Type} (I : HProp A V) (bad : M → Prop) (act : M → O → M → Prop)
    (K : O → Heap A V → Prop) (h : Heap A V) : Prop :=
  ∀ hI, I hI → Heap.Disjoint h hI → ∀ m, S.Agrees (Heap.union h hI) m →
    ¬ bad m ∧
    ∀ o m', act m o m' → S.Keeps (Heap.union h hI) m m' ∧
      ∃ h' hI', Heap.Disjoint h' hI' ∧ Heap.DomLe (Heap.union h' hI') (Heap.union h hI) ∧
        S.Agrees (Heap.union h' hI') m' ∧ I hI' ∧ K o h'

/-- **The obligations of an atomic step** of thread `t` in state `s` owning `h`. -/
def AtomOk (I : HProp A V) (K : U.St → Heap A V → Prop) (t : Nat) (s : U.St) (h : Heap A V) :
    Prop :=
  AtomicOk (S := S) I (U.afault t s) (fun m s' m' => U.atom t s m s' m') K h

/-- **The obligations of a primitive call** `p args` by thread `t` owning `h` (the atomic
obligations of one primitive step, outcome the result `r`). -/
def PrimOk (I : HProp A V) (sp : PrimSpec M) (K : Nat → Heap A V → Prop) (t : Nat)
    (args : List Nat) (h : Heap A V) : Prop :=
  AtomicOk (S := S) I (sp.fault t args) (sp.step t args) K h

/-- **The obligations of a `clone`** by thread `t` in state `s` owning `h`: as an atomic step,
whose new owned heap splits into the parent's part (satisfying `R t s₁`) and the child's
(satisfying `R u s₂`). -/
def SpawnOk (I : HProp A V) (R : Nat → U.St → Heap A V → Prop) (t : Nat) (s : U.St)
    (h : Heap A V) : Prop :=
  ∀ u, AtomicOk (S := S) I (fun _ => False)
    (fun m (o : U.St × U.St) m' => U.spawn t u s m o.1 o.2 m')
    (fun o h' => ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ Heap.union h₁ h₂ = h' ∧ R t o.1 h₁ ∧ R u o.2 h₂) h

/-- **The safety functional** (see the module documentation); successors must satisfy `R`. -/
def SafeF (I : HProp A V) (Q : Nat → U.St → Heap A V → Prop)
    (R : Nat → U.St → Heap A V → Prop) (t : Nat) (s : U.St) (h : Heap A V) : Prop :=
  (U.done s → Q t s h) ∧ LocOk U (R t) t s h ∧ AtomOk U I (R t) t s h ∧ SpawnOk U I R t s h

/-- **Thread `t` in state `s` owning `h` is safe** under the invariant `I`, ending in `Q`: some
relation `R` (the thread's invariant) contains it and is post-fixed for `SafeF`. -/
def Safe (I : HProp A V) (Q : Nat → U.St → Heap A V → Prop) (t : Nat) (s : U.St)
    (h : Heap A V) : Prop :=
  ∃ R : Nat → U.St → Heap A V → Prop, R t s h ∧ ∀ t s h, R t s h → SafeF U I Q R t s h

/-- **The compatibility conditions** of a configuration with owned heaps `hs` and invariant heap
`hI`: pairwise disjoint owned heaps, disjoint from `hI ⊨ I`, all fragments of memory, no heap for
an absent thread, and every thread safe on its heap. -/
def GInv (I : HProp A V) (Q : Nat → U.St → Heap A V → Prop) (C : Cfg U) (hs : Nat → Heap A V)
    (hI : Heap A V) : Prop :=
  (∀ t u, t ≠ u → Heap.Disjoint (hs t) (hs u)) ∧ (∀ t, Heap.Disjoint (hs t) hI) ∧
  (∀ t, S.Agrees (hs t) C.mem) ∧ S.Agrees hI C.mem ∧ I hI ∧
  (∀ t, C.th t = none → hs t = Heap.empty) ∧
  ∀ t s, C.th t = some s → Safe U I Q t s (hs t)

/-- **The global property**: no thread can fault, no data race, and for some owned heaps and
invariant heap (fragments of memory, pairwise disjoint), `I` holds and every finished thread
meets its postcondition. -/
def Good (I : HProp A V) (Q : Nat → U.St → Heap A V → Prop) (C : Cfg U) : Prop :=
  ¬ Fault U C ∧ ¬ Race U C ∧
  ∃ (hs : Nat → Heap A V) (hI : Heap A V), I hI ∧ S.Agrees hI C.mem ∧
    (∀ t, S.Agrees (hs t) C.mem) ∧ (∀ t u, t ≠ u → Heap.Disjoint (hs t) (hs u)) ∧
    (∀ t, Heap.Disjoint (hs t) hI) ∧ ∀ t s, C.th t = some s → U.done s → Q t s (hs t)

end Safe

/-- The configuration of one thread `t₀` in state `s₀` with memory `m₀`. -/
def Cfg.single {M A V : Type} {S : Store M A V} (U : TIsa S) (t₀ : Nat) (s₀ : U.St) (m₀ : M) :
    Cfg U :=
  ⟨fun t => if t = t₀ then some s₀ else none, m₀⟩

end Silmaril.Process.Mt.Csl
