module

public import Silmaril.X86.Concurrency.Cir.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms

/-!
# RC11 on CIR: definitions

RC11, the repaired C11
model of Lahav, Vafeiadis, Kang, Hur and Dreyer ("Repairing sequential consistency in C/C++11",
PLDI 2017), for the fragment of CIR that compiled C11 litmus tests use: loads, stores and
read-modify-writes with a C11 mode, and sequentially consistent fences.

## Same candidate executions as x86

RC11 is stated over the **same** candidate executions (`Axiomatic.Exec`) as the SC, TSO
and XL models: the access units of the CIR program's lowered traces, with program order `po`,
reads-from `rf`, coherence `co` (RC11's modification order `mo`), from-reads `fr` and the locked
read-modify-write pairs `rmw`. What RC11 adds is a **C11 role** per unit (`Role`): an access
with a mode, an SC fence, or nothing (not a C11 event). So "the compilation is correct" can be
said execution by execution: an execution consistent under XL is consistent under RC11
(`Task.cirXlRc11`), not only outcome by outcome.

The roles of a CIR program are **static** (`Stmt.c11Roles`): a straight-line CIR thread lowers to
the same sequence of units in every run (only the values differ), so the role of the unit at
program position `p` of thread `i` is fixed by the program text (`Prog.sroleAt`). Loads and
stores give one access unit with their mode, read-modify-writes two (the read and the write), and
`mfence` one SC fence (the standard mapping of `atomic_thread_fence(seq_cst)`). A locked
`or` of `0` (`lock or $0, m`, the fence idiom both gcc and clang emit for a seq_cst fence) is an
**SC fence when it touches no location of the program** (a stack slot: no C object lives there)
and an ordinary read-modify-write otherwise (`SRole.idem`, `Prog.roleOfEv`).

## The model (`Consistent`)

With `[E⊒m]` the events of mode at least `m` (SC fences are at least everything):

* `rs ≜ [W] ; po|loc? ; [W⊒rlx] ; (rf ; rmw)*` (release sequence);
* `sw ≜ [E⊒rel] ; ([F] ; po)? ; rs ; rf ; [R⊒rlx] ; (po ; [F])? ; [E⊒acq]`;
* `hb ≜ (po ∪ sw)⁺`, `eco ≜ (rf ∪ mo ∪ fr)⁺`;
* `scb ≜ po ∪ po|≠loc ; hb ; po|≠loc ∪ hb|loc ∪ mo ∪ fr`;
* `psc_base ≜ ([E^sc] ∪ [F^sc] ; hb?) ; scb ; ([E^sc] ∪ hb? ; [F^sc])`,
  `psc_F ≜ [F^sc] ; (hb ∪ hb ; eco ; hb) ; [F^sc]`, `psc ≜ psc_base ∪ psc_F`.

An execution is RC11-consistent when (coherence) `hb ; eco?` is irreflexive, (atomicity)
`rmw ∩ (fre ; moe) = ∅`, (SC) `psc` is acyclic and (no-thin-air) `po ∪ rf` is acyclic. RC11
has no mixed-size accesses: `rf` and `mo` are per location, so on the byte-granular candidates
an RC11 execution must have no read that tears and a modification order that agrees across the
bytes of a location; on uniform candidates both are "`com` has no 2-cycle" (`whole`).

A consistent execution is **racy** if two conflicting accesses (same location, at least one a
write, at least one non-atomic) are unordered by `hb` (`Racy`). A program with a racy consistent
execution has undefined behaviour.

## Decision procedure

`judge` decides consistency and raciness on bitmask relations (below). Closures are computed by
squaring (`c ↦ c ∪ c;c`) to a fixpoint; if no fixpoint is reached within `n + 1` rounds the
procedure gives up (`none`), so it never claims anything it did not compute. It runs in stages
(`judge`, `judgeB`, `judgeC`, `judgeD`, `judgeE`) so that its proof can name each mask. Its
correctness (`judge_spec`) is in `Rc11/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Axiomatic (Exec BRel Ev before)

/-! ## Roles -/

/-- The C11 role of an access unit. -/
inductive Role where
  /-- A C11 access (read, write, or half of a read-modify-write) with its mode. -/
  | acc (m : Mode)
  /-- A sequentially consistent fence. -/
  | fsc
  /-- Not a C11 event. -/
  | none
  deriving DecidableEq, Repr

namespace Role

/-- A C11 access. -/
def isAcc : Role → Bool
  | .acc _ => true
  | _ => false

/-- An SC fence. -/
def isF (r : Role) : Bool := r == .fsc

/-- A non-atomic access. -/
def isNa (r : Role) : Bool := r == .acc .na

/-- At least relaxed (`E⊒rlx`; an SC fence counts). -/
def rlx : Role → Bool
  | .acc .na | .none => false
  | _ => true

/-- At least release. -/
def rel : Role → Bool
  | .acc .rel | .acc .acqRel | .acc .sc | .fsc => true
  | _ => false

/-- At least acquire. -/
def acq : Role → Bool
  | .acc .acq | .acc .acqRel | .acc .sc | .fsc => true
  | _ => false

/-- Sequentially consistent (`E^sc`; SC fences included). -/
def sc : Role → Bool
  | .acc .sc | .fsc => true
  | _ => false

end Role

/-- A static role: a role, or the role of a locked `or 0` (an SC fence on a cell outside every
location, an access of mode `m` otherwise). -/
inductive SRole where
  | role (r : Role)
  | idem (m : Mode)
  deriving DecidableEq, Repr

/-- **The static roles of a statement**, one per access unit in program order. -/
def Stmt.c11Roles : Stmt → List SRole
  | .load _ m .. | .store m .. => [.role (.acc m)]
  | .rmw _ m _ (.op .or) _ (.lit 0) => [.idem m, .idem m]
  | .rmw _ m .. => [.role (.acc m), .role (.acc m)]
  | .fence .mfence => [.role .fsc]
  | .fence _ => [.role .none]
  | .spawn _ | .join _ => [.role (.acc .sc), .role (.acc .sc)]
  | .seq s t => s.c11Roles ++ t.c11Roles
  | _ => []

/-- The statement is in the fragment whose roles are static: straight-line code of skips,
assignments, accesses, read-modify-writes, fences, `spawn` and `join`. -/
def Stmt.c11Frag : Stmt → Bool
  | .skip | .assign .. | .load .. | .store .. | .rmw .. | .fence _ | .spawn _ | .join _ => true
  | .seq s t => s.c11Frag && t.c11Frag
  | _ => false

/-- The static roles of a thread (the start and end events of a spawned thread are SC
read-modify-writes of its control byte). -/
def Thread.c11Roles (th : Thread) : List SRole :=
  let ctl : List SRole := if th.spawned then [.role (.acc .sc), .role (.acc .sc)] else []
  ctl ++ th.body.c11Roles ++ ctl

/-- The static role at program position `p` of thread `i`. -/
def Prog.sroleAt (P : Prog) (i p : Nat) : SRole :=
  match P.threads[i]? with
  | some th => th.c11Roles.getD p (.role .none)
  | none => .role .none

/-- The address lies in a location of the program. -/
def Prog.inLoc (P : Prog) (a : Nat) : Bool := P.locs.any fun l => decide (l.addr ≤ a ∧ a < l.addr + l.size)

/-- **The role of a unit.** -/
def Prog.roleOfEv (P : Prog) (e : Ev) : Role :=
  match P.sroleAt e.tid e.pos with
  | .role r => r
  | .idem m => if P.inLoc e.addr then .acc m else .fsc

/-- The roles of an execution's units, by index. -/
def Prog.roles (P : Prog) (x : Exec) : Nat → Role := fun i => P.roleOfEv (x.evN i)

/-! ## Finite relations as bitmasks

The decision procedure runs in the kernel (`decide +kernel`), which evaluates lazily and shares
nothing: a relation given as a function is recomputed at every use. So relations on the units
`0, ..., n - 1` are **bitmasks** (bit `a * n + b` for the pair `(a, b)`; row `a` is the `n`
bits from `a * n`), whose arithmetic the kernel does on literals, and every intermediate mask is
evaluated once and passed on as a literal (`force`, the identity: `force v k = k v`). Union and
intersection are `|||` and `&&&`; composition works row by row (`seqR`). -/

namespace Rc11

/-- The bits `b < k` with `g b`. -/
def maskK (g : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => maskK g k ||| (if g k then 2 ^ k else 0)

/-- Rows `a < k`: row `a` is `g a` (its low `n` bits) placed at `a * n`. -/
def rowsK (n : Nat) (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rowsK n g k ||| ((g k % 2 ^ n) <<< (k * n))

/-- A relation on `0, ..., n - 1` as an `n²`-bit mask. -/
def rel (n : Nat) (f : Nat → Nat → Bool) : Nat := rowsK n (fun a => maskK (f a) n) n

/-- The pair `(a, b)` of a relation mask. -/
def get (n T a b : Nat) : Bool := T.testBit (a * n + b)

/-- Row `a` of a relation mask. -/
def row (n T a : Nat) : Nat := (T >>> (a * n)) % 2 ^ n

/-- The union of the rows `U c` for the `c < k` with `(a, c) ∈ T`. -/
def joinK (n T U a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => joinK n T U a k ||| (if get n T a k then row n U k else 0)

/-- Composition `T ; U`. -/
def seqR (n T U : Nat) : Nat := rowsK n (fun a => joinK n T U a n) n

/-- Some `c < n` satisfies `p`. -/
def anyLt (n : Nat) (p : Nat → Bool) : Bool := (List.range n).any p

/-- Every `c < n` satisfies `p`. -/
def allLt (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p

/-- Evaluate `v` once and continue with its value (the identity, `force_eq`). -/
def force {α : Sort _} (v : Nat) (k : Nat → α) : α :=
  match v with
  | 0 => k 0
  | m + 1 => k (m + 1)

/-- Iterate `c ↦ c ∪ c ; c` until a fixpoint, at most `k` times. -/
def tcLoop (n : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, c => force (c ||| seqR n c c) fun c' => if c' == c then some c else tcLoop n k c'

/-- **The transitive closure** of `R`, if the iteration (squaring, so about `log₂ n` rounds)
reaches a fixpoint within `n + 1` rounds. -/
def tcN (n R : Nat) : Option Nat := force R fun R => tcLoop n (n + 1) R

/-- A relation mask as a relation on `Fin n`. -/
def ofMask (n T : Nat) : BRel n := fun a b => get n T a.val b.val

/-- Evaluate a list of numbers once (the identity, `forceL_eq`). -/
def forceL {α : Sort _} : List Nat → (List Nat → α) → α
  | [], k => k []
  | a :: l, k => force a fun a => forceL l fun l => k (a :: l)

end Rc11

/-! ## The model -/

namespace Rc11

variable (ro : Nat → Role) (x : Exec)

/-- The role of a unit. -/
def C (a : Fin x.n) : Role := ro a.val

/-- A C11 read. -/
def R (a : Fin x.n) : Bool := (x.ev a).isR && (C ro x a).isAcc

/-- A C11 write. -/
def W (a : Fin x.n) : Bool := (x.ev a).isW && (C ro x a).isAcc

/-- Both units are C11 accesses. -/
def both (a b : Fin x.n) : Bool := (C ro x a).isAcc && (C ro x b).isAcc

/-- Program order. -/
def po : BRel x.n := x.po

/-- Reads-from between C11 accesses. -/
def rf : BRel x.n := fun a b => x.rfR a b && both ro x a b

/-- Modification order between C11 accesses. -/
def mo : BRel x.n := fun a b => x.coR a b && both ro x a b

/-- From-reads between C11 accesses. -/
def fr : BRel x.n := fun a b => x.frR a b && both ro x a b

/-- The read-modify-write pairs of C11 accesses. -/
def rmw : BRel x.n := fun a b => x.rmwR a b && both ro x a b

/-- Same location (two C11 accesses that share a byte). -/
def loc : BRel x.n := fun a b => x.loc a b && both ro x a b

/-- External (different threads). -/
def ext : BRel x.n := x.ext

/-- `(rf ; rmw)*`. -/
def RfRmwStar (a b : Fin x.n) : Prop := Relation.ReflTransGen ((rf ro x).seq (rmw ro x)).Holds a b

/-- The release sequence `[W] ; po|loc? ; [W⊒rlx] ; (rf ; rmw)*`. -/
def Rs (a b : Fin x.n) : Prop :=
  W ro x a = true ∧ ∃ c, (c = a ∨ (po x a c = true ∧ loc ro x a c = true)) ∧ W ro x c = true ∧
    (C ro x c).rlx = true ∧ RfRmwStar ro x c b

/-- Synchronises-with `[E⊒rel] ; ([F] ; po)? ; rs ; rf ; [R⊒rlx] ; (po ; [F])? ; [E⊒acq]`. -/
def Sw (a b : Fin x.n) : Prop :=
  (C ro x a).rel = true ∧ ∃ a' w r, (a' = a ∨ ((C ro x a).isF = true ∧ po x a a' = true)) ∧
    Rs ro x a' w ∧ rf ro x w r = true ∧ R ro x r = true ∧ (C ro x r).rlx = true ∧
    (b = r ∨ (po x r b = true ∧ (C ro x b).isF = true)) ∧ (C ro x b).acq = true

/-- Happens-before `(po ∪ sw)⁺`. -/
def Hb (a b : Fin x.n) : Prop := Relation.TransGen (fun a b => po x a b = true ∨ Sw ro x a b) a b

/-- Extended coherence order `(rf ∪ mo ∪ fr)⁺`. -/
def Eco (a b : Fin x.n) : Prop := Relation.TransGen ((rf ro x).union ((mo ro x).union (fr ro x))).Holds a b

/-- `scb ≜ po ∪ po|≠loc ; hb ; po|≠loc ∪ hb|loc ∪ mo ∪ fr`. -/
def Scb (a b : Fin x.n) : Prop :=
  po x a b = true ∨
    (∃ c d, po x a c = true ∧ loc ro x a c = false ∧ Hb ro x c d ∧ po x d b = true ∧
      loc ro x d b = false) ∨
    (Hb ro x a b ∧ loc ro x a b = true) ∨ mo ro x a b = true ∨ fr ro x a b = true

/-- `psc_base ≜ ([E^sc] ∪ [F^sc] ; hb?) ; scb ; ([E^sc] ∪ hb? ; [F^sc])`. -/
def PscBase (a b : Fin x.n) : Prop :=
  ∃ a' b', ((C ro x a).sc = true ∧ a' = a ∨ (C ro x a).isF = true ∧ (a' = a ∨ Hb ro x a a')) ∧
    Scb ro x a' b' ∧
    ((C ro x b).sc = true ∧ b' = b ∨ (C ro x b).isF = true ∧ (b' = b ∨ Hb ro x b' b))

/-- `psc_F ≜ [F^sc] ; (hb ∪ hb ; eco ; hb) ; [F^sc]`. -/
def PscF (a b : Fin x.n) : Prop :=
  (C ro x a).isF = true ∧ (C ro x b).isF = true ∧
    (Hb ro x a b ∨ ∃ c d, Hb ro x a c ∧ Eco ro x c d ∧ Hb ro x d b)

/-- `psc ≜ psc_base ∪ psc_F`. -/
def Psc (a b : Fin x.n) : Prop := PscBase ro x a b ∨ PscF ro x a b

/-- **RC11 consistency** (Lahav et al., PLDI 2017, Definition 1), with RC11's per-location `rf`
and `mo` on byte-granular candidates (`whole`). -/
structure Consistent : Prop where
  /-- `rf` and `mo` are per location: `com` has no 2-cycle. -/
  whole : ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False
  /-- Coherence: `hb ; eco?` is irreflexive. -/
  coherence : ∀ a b, Hb ro x a b → a ≠ b ∧ ¬ Eco ro x b a
  /-- Atomicity: `rmw ∩ (fre ; moe) = ∅`. -/
  atomicity : x.atomicB = true
  /-- SC: `psc` is acyclic. -/
  sc : ∀ a, ¬ Relation.TransGen (Psc ro x) a a
  /-- No thin air: `po ∪ rf` is acyclic. -/
  noThinAir : ∀ a, ¬ Relation.TransGen (fun a b => po x a b = true ∨ rf ro x a b = true) a a

/-- **A data race**: two conflicting accesses, at least one non-atomic, unordered by `hb`. -/
def Racy : Prop :=
  ∃ a b : Fin x.n, a ≠ b ∧ loc ro x a b = true ∧ (W ro x a = true ∨ W ro x b = true) ∧
    ((C ro x a).isNa = true ∨ (C ro x b).isNa = true) ∧ ¬ Hb ro x a b ∧ ¬ Hb ro x b a

/-! ## The decision procedure -/

/-- The code of a role (`roleOf` is its inverse). -/
def roleCode : Role → Nat
  | .none => 0
  | .acc .na => 1
  | .acc .rlx => 2
  | .acc .acq => 3
  | .acc .rel => 4
  | .acc .sc => 5
  | .acc .acqRel => 6
  | .fsc => 7

/-- The role of a code. -/
def roleOf : Nat → Role
  | 1 => .acc .na
  | 2 => .acc .rlx
  | 3 => .acc .acq
  | 4 => .acc .rel
  | 5 => .acc .sc
  | 6 => .acc .acqRel
  | 7 => .fsc
  | _ => .none

/-- Evaluate a list of pairs (byte, source) once. -/
def forceRf {α : Sort _} : List (Nat × Option Nat) → (List (Nat × Option Nat) → α) → α
  | [], k => k []
  | (y, none) :: l, k => force y fun y => forceRf l fun l => k ((y, none) :: l)
  | (y, some w) :: l, k => force y fun y => force w fun w => forceRf l fun l => k ((y, some w) :: l)

/-- Evaluate a list of pairs (byte, coherence order) once. -/
def forceCo {α : Sort _} : List (Nat × List Nat) → (List (Nat × List Nat) → α) → α
  | [], k => k []
  | (y, o) :: l, k => force y fun y => forceL o fun o => forceCo l fun l => k ((y, o) :: l)

/-- Evaluate a list of lists once. -/
def forceLL {α β : Type} (f : List α → (List α → β) → β) : List (List α) → (List (List α) → β) → β
  | [], k => k []
  | a :: l, k => f a fun a => forceLL f l fun l => k (a :: l)

/-- Per unit, its bytes with the write each one is read from. -/
def rfTab : List (List (Nat × Option Nat)) :=
  (List.range x.n).map fun i => (x.evN i).bytes.map fun y => (y, x.rf i y)

/-- Per unit, its bytes with their coherence orders. -/
def coTab : List (List (Nat × List Nat)) :=
  (List.range x.n).map fun i => (x.evN i).bytes.map fun y => (y, x.co y)

/-- `rfR`, from the tables. -/
def rfF (rfL : List (List (Nat × Option Nat))) (w r : Nat) : Bool :=
  (x.evN w).isW && (x.evN r).isR && (rfL.getD r []).any fun p => p.2 == some w && (x.evN w).covers p.1

/-- `coR`, from the tables. -/
def coF (coL : List (List (Nat × List Nat))) (a b : Nat) : Bool :=
  (x.evN a).isW && (x.evN b).isW && (coL.getD a []).any fun p => (x.evN b).covers p.1 && before p.2 a b

/-- `frR`, from the tables. -/
def frF (rfL : List (List (Nat × Option Nat))) (coL : List (List (Nat × List Nat))) (r w : Nat) : Bool :=
  (x.evN r).isR && (x.evN w).isW &&
    ((rfL.getD r []).zip (coL.getD r [])).any fun p =>
      (x.evN w).covers p.1.1 && match p.1.2 with
        | none => true
        | some v => before p.2.2 v w

/-- `loc`, from the units. -/
def locF (a b : Nat) : Bool := (x.evN a).isM && (x.evN b).isM && (x.evN a).bytes.any (x.evN b).covers

/-- `po`, from the units. -/
def poF (a b : Nat) : Bool := (x.evN a).tid == (x.evN b).tid && decide ((x.evN a).pos < (x.evN b).pos)

/-- `ext`, from the units. -/
def extF (a b : Nat) : Bool := (x.evN a).tid != (x.evN b).tid

/-- The answer of `judge` from a code `2 * consistent + racy`. -/
def decode (k : Nat) : Option (Bool × Bool) :=
  if k = 0 then some (false, false) else if k = 1 then some (false, true)
  else if k = 2 then some (true, false) else if k = 3 then some (true, true) else none

/-- The code of `judge`. -/
def code (cons racy : Bool) : Nat := (if cons then 2 else 0) + (if racy then 1 else 0)

/-- The last stage of `judge`: the checks, given `hb`, `eco` and `psc` (and the base masks). -/
def judgeE (n : Nat) (C : Nat → Role) (isW : Nat → Bool) (poT rfT locT rfAll coAll frAll rmwAll extT
    hb eco psc : Nat) : Option (Bool × Bool) :=
  let com := rfAll ||| coAll ||| frAll
  let whole := allLt n fun a => allLt n fun b => !(get n com a b && get n com b a)
  let atom := allLt n fun a => allLt n fun b =>
    !(get n rmwAll a b && get n (seqR n (frAll &&& extT) (coAll &&& extT)) a b)
  let coh := allLt n fun a => allLt n fun b => !get n hb a b || (a != b && !get n eco b a)
  let racy := anyLt n fun a => anyLt n fun b =>
    a != b && get n locT a b && (isW a || isW b) && ((C a).isNa || (C b).isNa) &&
      !get n hb a b && !get n hb b a
  let cons := whole && coh && atom && (ofMask n psc).acyclicB && (ofMask n (poT ||| rfT)).acyclicB
  force (code cons racy) decode

/-- The third stage of `judge`: `psc`, given `hb` and `eco`. -/
def judgeD (n : Nat) (C : Nat → Role) (isW : Nat → Bool) (poT rfT moT frT locT rfAll coAll frAll
    rmwAll extT eco hb : Nat) : Option (Bool × Bool) :=
  -- `scb = po ∪ po|≠loc ; hb ; po|≠loc ∪ hb|loc ∪ mo ∪ fr`
  force (rel n fun a b => get n poT a b && !get n locT a b) fun pn =>
  force (poT ||| seqR n (seqR n pn hb) pn ||| (hb &&& locT) ||| moT ||| frT) fun scb =>
  -- `psc_base = ([E^sc] ∪ [F^sc] ; hb?) ; scb ; ([E^sc] ∪ hb? ; [F^sc])`
  force (rel n fun a a' => ((C a).sc && a' == a) || ((C a).isF && (a' == a || get n hb a a')))
    fun lft =>
  force (rel n fun b' b => ((C b).sc && b' == b) || ((C b).isF && (b' == b || get n hb b' b)))
    fun rgt =>
  -- `psc_F = [F^sc] ; (hb ∪ hb ; eco ; hb) ; [F^sc]`
  force (rel n fun a b => (C a).isF && (C b).isF) fun ff =>
  force (seqR n (seqR n lft scb) rgt ||| (ff &&& (hb ||| seqR n (seqR n hb eco) hb))) fun psc =>
  judgeE n C isW poT rfT locT rfAll coAll frAll rmwAll extT hb eco psc

/-- The second stage of `judge`: `sw` and `hb`, given `(rf ; rmw)⁺` and `eco`. -/
def judgeC (n : Nat) (C : Nat → Role) (isR isW : Nat → Bool) (poT rfT moT frT locT rfAll coAll frAll
    rmwAll extT rr eco : Nat) : Option (Bool × Bool) :=
  -- `rs = [W] ; po|loc? ; [W⊒rlx] ; (rf ; rmw)*`
  force (rel n fun a c => isW a && (c == a || (get n poT a c && get n locT a c)) && isW c &&
    (C c).rlx) fun rsL =>
  force (rsL ||| seqR n rsL rr) fun rs =>
  -- `sw = [E⊒rel] ; ([F] ; po)? ; rs ; rf ; [R⊒rlx] ; (po ; [F])? ; [E⊒acq]`
  force (rel n fun a a' => a' == a || ((C a).isF && get n poT a a')) fun fpo =>
  force (rel n fun w r => get n rfT w r && isR r && (C r).rlx) fun rfA =>
  force (rel n fun r b => b == r || (get n poT r b && (C b).isF)) fun pf =>
  force (seqR n (seqR n (seqR n fpo rs) rfA) pf) fun s3 =>
  force (rel n fun a b => (C a).rel && (C b).acq && get n s3 a b) fun sw =>
  match tcN n (poT ||| sw) with
  | some hb => judgeD n C isW poT rfT moT frT locT rfAll coAll frAll rmwAll extT eco hb
  | none => none

/-- The first stage of `judge`: `(rf ; rmw)⁺` and `eco`, given the base masks. -/
def judgeB (n : Nat) (C : Nat → Role) (isR isW : Nat → Bool) (poT rfAll coAll frAll locAll rmwAll
    extT accT : Nat) : Option (Bool × Bool) :=
  let rfT := rfAll &&& accT
  let moT := coAll &&& accT
  let frT := frAll &&& accT
  let locT := locAll &&& accT
  match tcN n (seqR n rfT (rmwAll &&& accT)), tcN n (rfT ||| moT ||| frT) with
  | some rr, some eco => judgeC n C isR isW poT rfT moT frT locT rfAll coAll frAll rmwAll extT rr eco
  | _, _ => none

/-- **Decide RC11 consistency and raciness** (`none` if a closure did not converge). -/
def judge : Option (Bool × Bool) :=
  force x.n fun n =>
  forceL ((List.range n).map fun i => roleCode (ro i)) fun roL =>
  forceLL forceRf (rfTab x) fun rfL => forceLL forceCo (coTab x) fun coL =>
  let C (a : Nat) : Role := roleOf (roL.getD a 0)
  force (rel n (poF x)) fun poT =>
  force (rel n (rfF x rfL)) fun rfAll => force (rel n (coF x coL)) fun coAll =>
  force (rel n (frF x rfL coL)) fun frAll => force (rel n (locF x)) fun locAll =>
  force (rel n fun a b => x.rmw.contains (a, b)) fun rmwAll => force (rel n (extF x)) fun extT =>
  force (rel n fun a b => (C a).isAcc && (C b).isAcc) fun accT =>
  judgeB n C (fun a => (x.evN a).isR && (C a).isAcc) (fun a => (x.evN a).isW && (C a).isAcc)
    poT rfAll coAll frAll locAll rmwAll extT accT

end Rc11

/-! ## Programs -/

/-- **RC11 for a CIR program**: consistency with the program's roles. -/
def Prog.Rc11 (P : Prog) (x : Exec) : Prop := Rc11.Consistent (P.roles x) x

/-- RC11-consistent and racy. -/
def Prog.Rc11Racy (P : Prog) (x : Exec) : Prop := Rc11.Consistent (P.roles x) x ∧ Rc11.Racy (P.roles x) x

end Silmaril.X86.Concurrency.Cir
