module

public import Silmaril.Wasm.Component.FXRes.ContEngine.Defs
public import Silmaril.Wasm.Resource.Table.Defs

/-!
# Continuations in the table or in a store, never both: definitions

The engine `fxCE P` (`Silmaril.Wasm.Component.FXRes.ContEngine`) keeps continuations in two kinds
of places: the store `K` of each FX thread, and the continuation table of the engine store,
shared by all threads. The built-in `new` moves a continuation from a thread's store into the
table, `take` moves one from the table into the store of the calling thread, which may be
another thread than the one that put it there (a later export call, say).

This module tracks **continuation identities** along runs of a pool of threads over one engine
store, an abstraction of how the component machine drives engine threads through the engine
interface:

* `Loc`: a location: entry `j` of the store of thread `i`, or entry `n` of the table;
  `Live p l`: location `l` holds a continuation in pool `p`.
* `Pool H`: an engine store and a list of thread slots (`none`: a finished thread).
* `PStep P`: one step of the pool: an internal step `InternalC P` of a thread, starting a thread
  (`invoke`), resuming a parked thread (`resumeV`), changing the engine store without changing
  the table (instantiation, host-function allocation and memory writes are such changes:
  `ContEngine.prepareC_tab`, `allocHostC_tab`, `memWriteC_tab`), and discarding a thread.
* `Ghost`: identities of locations (`id`) and the next fresh identity (`next`).
* **`GStep P`**: the pool step with its identity update. A continuation created by `cont.new`,
  `suspend`, `cont.bind` or `switch` (an `alloc` store event) gets the fresh identity `next`
  (`Ghost.allocs`); `new` **moves** the identity of store entry `k` to table entry `n`, and
  `take` moves the identity of table entry `n` to the new store entry (`Ghost.move`); every other
  step keeps all identities.
* `GInv p g`: the table's representation invariant (`FreeOK`), every live identity is below
  `next`, and **distinct live locations have distinct identities**.

Theorems: `Silmaril.Wasm.Component.FXRes.ContPool.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContPool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (ContFX AdminFX)
open Silmaril.Wasm.Models.FXV (CtxV)
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXRes Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

/-- A location of a continuation. -/
inductive Loc where
  /-- Entry `j` of the store of thread `i`. -/
  | store (i j : ℕ)
  /-- Entry `n` of the continuation table. -/
  | tab (n : ℕ)
  deriving DecidableEq

/-- A pool of threads over one engine store. -/
structure Pool (H : Type) where
  s : EStore H
  ts : List (Option (ThreadV (CH H)))

variable {H : Type}

/-- The initial pool: an engine store with an empty table, no threads. -/
def Pool.init (c : Store (FXCode (CH H))) : Pool H := ⟨⟨c, Table.empty⟩, []⟩

/-- Location `l` holds a continuation. -/
def Live (p : Pool H) : Loc → Prop
  | .store i j => ∃ t, p.ts[i]? = some (some t) ∧ ∃ C, (threadConts t)[j]? = some (some C)
  | .tab n => ∃ C, p.s.tab.get? n = some C

/-- **One step of the pool.** -/
inductive PStep (P : Profile) : Pool H → Pool H → Prop where
  | internal {p : Pool H} {i : ℕ} {t t' : ThreadV (CH H)} {s' : EStore H}
      (hi : p.ts[i]? = some (some t)) (h : InternalC P (p.s, t) (s', t')) :
      PStep P p ⟨s', p.ts.set i (some t')⟩
  | spawn {p : Pool H} (a : ℕ) (args : List Silmaril.Wasm.Component.Engine.FlatValue) :
      PStep P p ⟨p.s, p.ts ++ [some (.core (SingleThreaded.Thread.invokeFlat a args))]⟩
  | resume {p : Pool H} {i : ℕ} {t : ThreadV (CH H)}
      (res : Silmaril.Wasm.Component.Engine.CallResult) (hi : p.ts[i]? = some (some t)) :
      PStep P p ⟨p.s, p.ts.set i (some (resumeV p.s.core t res))⟩
  | env {p : Pool H} {s' : EStore H} (hs : s'.tab = p.s.tab) : PStep P p ⟨s', p.ts⟩
  | finish {p : Pool H} (i : ℕ) : PStep P p ⟨p.s, p.ts.set i none⟩

/-- Runs of the pool. -/
abbrev PSteps (P : Profile) : Pool H → Pool H → Prop := Relation.ReflTransGen (PStep P)

/-- Identities of locations, and the next fresh identity. -/
structure Ghost where
  id : Loc → ℕ
  next : ℕ

/-- The initial identities. -/
def Ghost.init : Ghost := ⟨fun _ => 0, 0⟩

/-- Location `l` gets the fresh identity. -/
def Ghost.fresh (g : Ghost) (l : Loc) : Ghost := ⟨Function.update g.id l g.next, g.next + 1⟩

/-- The identity at `src` moves to `dst`. -/
def Ghost.move (g : Ghost) (src dst : Loc) : Ghost := ⟨Function.update g.id dst (g.id src), g.next⟩

/-- The identity update of the store events of thread `i`: each allocation is fresh. -/
def Ghost.allocs (i : ℕ) : Ghost → List (HEv ℕ) → Ghost
  | g, [] => g
  | g, .alloc m :: evs => (g.fresh (.store i m)).allocs i evs
  | g, _ :: evs => g.allocs i evs

/-- **One step of the pool with its identity update.** -/
inductive GStep (P : Profile) : Pool H × Ghost → Pool H × Ghost → Prop where
  /-- An FX step or a Core step of thread `i` (no built-in): allocations are fresh. -/
  | fx {p : Pool H} {g : Ghost} {i : ℕ} {t t' : ThreadV (CH H)} {s' : EStore H}
      {evs : List (HEv ℕ)} (hi : p.ts[i]? = some (some t)) (ht : s'.tab = p.s.tab)
      (hv : InternalV P (p.s.core, t) (s'.core, t')) (hn : ¬ ParkedCB t')
      (hk : KStep (threadConts t) (threadConts t') evs) :
      GStep P (p, g) (⟨s', p.ts.set i (some t')⟩, g.allocs i evs)
  /-- `new` in thread `i`: the identity of store entry `k` moves to table entry `n`. -/
  | cbNew {s : Store (FXCode (CH H))} {tb tb' : Silmaril.Wasm.Component.Runtime.Table ContFX} {ts : List (Option (ThreadV (CH H)))}
      {g : Ghost} {i : ℕ} {K : List (Option ContFX)} {f : Frame} {E : CtxV} {a k n : ℕ}
      {c : Admin} {C : ContFX}
      (hi : ts[i]? = some (some (.fx K f (E.plug (.contRef k :: callAt a c)))))
      (hc : c.IsCallRef) (hb : IsCB s a .new) (hk : K[k]? = some (some C))
      (ht : tb.add? C = some (n, tb')) :
      GStep P (⟨⟨s, tb⟩, ts⟩, g)
        (⟨⟨s, tb'⟩, ts.set i (some (.fx (K.set k none) f (E.plug [handleVal n])))⟩,
          g.move (.store i k) (.tab n))
  /-- `take` in thread `i`: the identity of table entry `b` moves to the new store entry. -/
  | cbTake {s : Store (FXCode (CH H))} {tb tb' : Silmaril.Wasm.Component.Runtime.Table ContFX}
      {ts : List (Option (ThreadV (CH H)))} {g : Ghost} {i : ℕ} {K : List (Option ContFX)}
      {f : Frame} {E : CtxV} {a : ℕ} {c : Admin} {b : BitVec 32} {C : ContFX}
      (hi : ts[i]? = some (some (.fx K f (E.plug (.core (constI32 b) :: callAt a c)))))
      (hc : c.IsCallRef) (hb : IsCB s a .take) (ht : tb.remove? b.toNat = some (C, tb')) :
      GStep P (⟨⟨s, tb⟩, ts⟩, g)
        (⟨⟨s, tb'⟩, ts.set i (some (.fx (K ++ [some C]) f (E.plug [.contRef K.length])))⟩,
          g.move (.tab b.toNat) (.store i K.length))
  /-- Any other built-in call (`drop`, traps): identities are kept. -/
  | cbOther {p : Pool H} {g : Ghost} {i : ℕ} {t t' : ThreadV (CH H)} {s' : EStore H}
      {ev : Option (Table.Event ContFX)} (hi : p.ts[i]? = some (some t))
      (hb : BStep (p.s, t) (s', t') ev) (hK : threadConts t' = threadConts t) :
      GStep P (p, g) (⟨s', p.ts.set i (some t')⟩, g)
  | spawn {p : Pool H} {g : Ghost} (a : ℕ) (args : List Silmaril.Wasm.Component.Engine.FlatValue) :
      GStep P (p, g) (⟨p.s, p.ts ++ [some (.core (SingleThreaded.Thread.invokeFlat a args))]⟩, g)
  | resume {p : Pool H} {g : Ghost} {i : ℕ} {t : ThreadV (CH H)}
      (res : Silmaril.Wasm.Component.Engine.CallResult) (hi : p.ts[i]? = some (some t)) :
      GStep P (p, g) (⟨p.s, p.ts.set i (some (resumeV p.s.core t res))⟩, g)
  | env {p : Pool H} {g : Ghost} {s' : EStore H} (hs : s'.tab = p.s.tab) :
      GStep P (p, g) (⟨s', p.ts⟩, g)
  | finish {p : Pool H} {g : Ghost} (i : ℕ) : GStep P (p, g) (⟨p.s, p.ts.set i none⟩, g)

/-- Runs of the pool with identities. -/
abbrev GSteps (P : Profile) : Pool H × Ghost → Pool H × Ghost → Prop :=
  Relation.ReflTransGen (GStep P)

/-- **The identity invariant.** -/
structure GInv (p : Pool H) (g : Ghost) : Prop where
  /-- The table's representation invariant. -/
  wf : FreeOK p.s.tab
  /-- Live identities are below `next`. -/
  lt : ∀ l, Live p l → g.id l < g.next
  /-- Distinct live locations have distinct identities. -/
  inj : ∀ l₁ l₂, Live p l₁ → Live p l₂ → g.id l₁ = g.id l₂ → l₁ = l₂

end Silmaril.Wasm.Component.FXRes.ContPool
