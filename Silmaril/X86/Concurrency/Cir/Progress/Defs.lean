module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Defs

/-!
# Progress of CSL-certified CIR programs

On the CIR-native store-buffer machines
(`Csl.OStep .tso`/`.xl`) a thread can be **stuck** for only a few reasons: its next statement is
a loop with no iterations left whose condition holds (`Exh`), it is a `spawn`/`join` (which these
machines do not model), or a memory label cannot fire because a cell it touches is unmapped, the
value in a cell does not fit the access size (a 4-byte load of a value `≥ 2 ^ 32`), or a `local`
block's contract has no output for the current inputs. Nothing ever *blocks*: a lock is a
bounded spin, and the `futex_wait` always returns.

So "every stuck reachable configuration is finished or has run out of a loop bound" is a
**safety** property, proved here once for every CSL-certified program whose code passes a
thread-local check:

* the unmapped-cell case is excluded by the CSL certificate (the `Safe` makes every label touch
  owned or invariant cells, which are in memory);
* the value-size case by a **width map** `w` (`w a = some k`: cell `a` only ever holds values
  below `2 ^ (8 k)`), kept by every write of the code (`LabFits`) and read only by accesses at
  least as wide;
* the block case by requiring total contracts.

## Definitions

* `fits w a v`, `LabFits w l`: the value `v` fits cell `a`; every value label `l` writes fits.
* `lead s`, `Exh p`: the next leaf statement (through `seq`); the thread has run out of a loop.
* `TReach`: thread-local reachability (any labels, any read values).
* `Good w s rs`: every label of `(s, rs)` writes fitting values, and `(s, rs)` is finished, has
  run out of a loop, has a silent step, or has, for every memory whose values fit and in which
  every cell its labels touch is mapped, a label step whose reads agree with that memory.
* `Inv w A s B`: from every register file satisfying `A`, every thread-local state reachable
  from `s` is `Good`, and `B` holds when it finishes (`Progress.Thms` has the rules).
* `MutexLive M`: a mutex whose lock and unlock code is `Good` from `rdi = l`, for a width map of
  its object (`wd`) that its initial cells fit.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Progress

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-- Value `v` **fits** cell `a` under the width map `w` (`w a = some k`: `k` bytes). -/
def fits (w : Nat → Option Nat) (a v : Nat) : Prop := ∀ k, w a = some k → v < 2 ^ (8 * k)

/-- **Every value a label writes fits**: its writes to memory (`wval`) and its buffer entries. -/
def LabFits (w : Nat → Option Nat) (l : Lab) : Prop :=
  (∀ a v, l.wval a = some v → fits w a v) ∧ ∀ e ∈ l.ents, ∀ a v b, e = .st a v b → fits w a v

/-- The next leaf statement (through `seq`). -/
def lead : Stmt → Stmt
  | .seq s _ => lead s
  | s => s

/-- A thread has **run out of a loop bound**: its next statement is a loop with no iterations
left whose condition still holds. -/
def Exh (p : Stmt × Regs) : Prop := ∃ c b, lead p.1 = .loop 0 c b ∧ truthy (c.eval p.2) = true

/-- **Thread-local reachability**: any sequence of thread steps, with any labels (so any read
values). -/
def TReach : Stmt × Regs → Stmt × Regs → Prop :=
  Star fun p q => ∃ l, TStep p.1 p.2 l q.1 q.2

/-- **A thread state that cannot get stuck on its own**: every label of it writes fitting values,
and it is finished, out of a loop bound, has a silent step, or, in every memory `H` whose values
fit and in which every cell its labels touch is mapped, has a label step reading `H`. -/
def Good (w : Nat → Option Nat) (s : Stmt) (rs : Regs) : Prop :=
  (∀ l s' rs', TStep s rs (some l) s' rs' → LabFits w l) ∧
  (s = .skip ∨ Exh (s, rs) ∨ (∃ s' rs', TStep s rs none s' rs') ∨
    ∀ H : Heap, (∀ a v, H a = some v → fits w a v) →
      (∀ l s' rs', TStep s rs (some l) s' rs' → ∀ a, l.Touches a → (H a).isSome) →
      ∃ l s' rs', TStep s rs (some l) s' rs' ∧ l.okH H)

/-- **Thread-local progress of a statement**: from every register file satisfying `A`, every
reachable thread state is `Good`, and `B` holds of the registers when it finishes. -/
def Inv (w : Nat → Option Nat) (A : Regs → Prop) (s : Stmt) (B : Regs → Prop) : Prop :=
  ∀ rs, A rs → ∀ p, TReach (s, rs) p → Good w p.1 p.2 ∧ (p.1 = .skip → B p.2)

/-- A width map **agrees with** `wd` on the addresses `[l, l + n)`. -/
def Agrees (w wd : Nat → Option Nat) (l n : Nat) : Prop := ∀ a, l ≤ a → a < l + n → w a = wd a

/-- **A mutex whose code cannot get stuck**: a width map `wd l` of the object at `l`
(no constraint outside it), which its initial cells fit, and under which the lock and the unlock,
run with `rdi = l` at every loop bound, are thread-locally `Good` in every width map that agrees
with `wd l` on the object. -/
structure MutexLive (M : Mutex.Iface) where
  /-- The widths of the object's cells. -/
  wd : Nat → Nat → Option Nat
  wd_dom : ∀ l a k, wd l a = some k → l ≤ a ∧ a < l + M.size
  init_fits : ∀ l a v, M.init l a = some v → fits (wd l) a v
  lock_inv : ∀ l L w, Agrees w (wd l) l M.size →
    Inv w (fun rs => (rs .rdi).toNat = l) (M.lockCode L) fun _ => True
  unlock_inv : ∀ l L w, Agrees w (wd l) l M.size →
    Inv w (fun rs => (rs .rdi).toNat = l) (M.unlockCode L) fun _ => True

end Silmaril.X86.Concurrency.Cir.Progress
