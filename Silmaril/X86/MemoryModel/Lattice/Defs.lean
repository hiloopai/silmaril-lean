module

public import Silmaril.X86.MemoryModel.Xl.Defs

/-!
# A lattice of x86 memory models: definitions

A **memory model** is the set of candidate executions it allows (`Model := Exec → Prop`), over the
herd-style candidates of `Silmaril.X86.MemoryModel.Axiomatic`. Models are preordered by inclusion:
`M ⊑ N` (`Model.Le`) when every execution `M` allows is allowed by `N`, so every behaviour of a
program under `M` is a behaviour under `N`; a result proved for all `N`-behaviours holds for all
`M`-behaviours. A **separating** execution for `M ⊏ N` is one `N` allows and `M` forbids
(`Model.Sep`).

## The models

* `sc`: sequential consistency (`Exec.Sc`, herd's `sc.cat`);
* `tso`: x86-TSO (`Exec.Tso`, herd's `x86tso.cat`). The operational store-buffer machine
  (`Silmaril.X86.MemoryModel.Tso`) is related to it per litmus test by
  `Litmus.TsoVerdicts.op_eq_ax` (for every test whose `checkTso` passes);
* `xl`: the loose x86 model XL (`Exec.Xl`): x86-TSO on tame accesses, weak non-temporal and
  string stores, per-byte tearing of misaligned, wide and mixed-size accesses;
* `ra`: **release/acquire**, every memory access a release write or an acquire read (the x86
  mapping of C11 `memory_order_release`/`acquire`; fences are ignored, so this is RA of the
  access fragment). `Exec.Ra`: locked-RMW atomicity, per-location coherence (`uniproc`),
  happens-before `hb = (po ∪ rf)⁺` acyclic, and `hb ; com` irreflexive. For accesses with one
  footprint per location, `rf ⊆ hb` makes the last condition RA's `irreflexive (hb ; eco?)`
  (Lahav, Giannarakis, Vafeiadis, "Taming release-acquire consistency", POPL 2016);
* `cf`: **catch-fire with locked synchronisation**: an execution is allowed if it is SC, or if
  it has a race (`Exec.DrfL` fails), or if some access is split into several units (no claim is
  made about split accesses). A race is two conflicting accesses of different threads, not both
  locked, unordered by `hbL = (po ∪ rf ∪ lock)⁺`, where `lock` is the communication between
  locked accesses of different threads (lock words, atomic RMWs: their coherence order is part
  of happens-before). This is "DRF modulo primitives";
* `cfPlain`: catch-fire where only `hb = (po ∪ rf)⁺` synchronises (`Exec.Drf`);
* `top`: every candidate execution.

`cf` and `cfPlain` are the models in which **DRF-SC** is an inclusion: `tso ⊑ cf` says every
data-race-free (unsplit) x86-TSO execution is SC.

## Deciding the transitive relations on concrete executions

`Exec.Hb` and `Exec.HbL` are transitive closures. `BRel.reach r a` computes, by `n` rounds of
successor steps, a set of nodes reachable from `a`; it is always sound (`reach_sound`), and it
is exact as soon as it is closed under `r` (`BRel.closedB`, checked per execution). The Boolean
checks `Exec.raB`, `Exec.drfB`, `Exec.drfLB` use it, together with `Exec.hbClosedB` /
`Exec.hbLClosedB`; their soundness is in `Silmaril.X86.MemoryModel.Lattice.Thms`.

## Names

`Name` lists the models; `Name.model` interprets them and `Name.le` is the order **proved** in
`Thms` (`Name.le_sound`), for clients (process models, problems) that pick a memory model by
name and move results along `⊑`.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Axiomatic

open Relation

/-! ## Reachability on finite Boolean relations -/

namespace BRel
variable {n : Nat}

/-- One round: `S` together with the `r`-successors of `S`. -/
def stepSet (r : BRel n) (S : Fin n → Bool) : Fin n → Bool :=
  fun b => S b || (List.finRange n).any fun c => S c && r c b

/-- `k` rounds from the successors of `a`. -/
def reachK (r : BRel n) (a : Fin n) : Nat → Fin n → Bool
  | 0 => r a
  | k + 1 => stepSet r (reachK r a k)

/-- Nodes reachable from `a` in at most `n` rounds (sound; exact when closed). -/
def reach (r : BRel n) (a : Fin n) : Fin n → Bool := reachK r a n

/-- `S` is closed under `r`. -/
def closedB (r : BRel n) (S : Fin n → Bool) : Bool :=
  (List.finRange n).all fun c => (List.finRange n).all fun d => !(S c && r c d) || S d

/-- Every `reach r a` is closed under `r`. -/
def reachClosedB (r : BRel n) : Bool := (List.finRange n).all fun a => closedB r (reach r a)

end BRel

namespace Exec
variable (x : Exec)

/-! ## Races -/

/-- Each access is one unit: `sm` is the identity. -/
def Unsplit : Prop := ∀ a b, x.sm a b = true → a = b

/-- Conflicting units: different threads, a shared byte, at least one write. -/
def conflict : BRel x.n := fun a b =>
  x.ext a b && x.loc a b && ((x.ev a).isW || (x.ev b).isW)

/-- Communication between locked units of different threads (lock words, atomic RMWs). -/
def lockCom : BRel x.n := fun a b => x.com a b && x.ext a b && (x.ev a).isA && (x.ev b).isA

/-- The edges of `hbL`: `po ∪ rf ∪ lockCom`. -/
def syncL : BRel x.n := x.thinAir.union x.lockCom

/-- Happens-before when every access is release/acquire: `(po ∪ rf)⁺`. -/
def Hb (a b : Fin x.n) : Prop := TransGen x.thinAir.Holds a b

/-- Happens-before where locked accesses also synchronise: `(po ∪ rf ∪ lockCom)⁺`. -/
def HbL (a b : Fin x.n) : Prop := TransGen x.syncL.Holds a b

/-- Data-race freedom: every conflicting pair is ordered by `hb`. -/
def Drf : Prop := ∀ a b, x.conflict a b = true → x.Hb a b ∨ x.Hb b a

/-- Data-race freedom modulo locked synchronisation: every conflicting pair that is not two
locked accesses is ordered by `hbL`. -/
def DrfL : Prop :=
  ∀ a b, x.conflict a b = true → ((x.ev a).isA && (x.ev b).isA) = false → x.HbL a b ∨ x.HbL b a

/-! ## Release/acquire -/

/-- Release/acquire (every access rel/acq; fences ignored): atomicity, per-location coherence,
`hb` acyclic and `hb ; com` irreflexive. -/
def Ra : Prop :=
  x.atomicB = true ∧ BRel.Acyclic x.uniproc ∧ BRel.Acyclic x.thinAir ∧
    ∀ a b, x.Hb a b → x.com b a = false

/-! ## Catch-fire models -/

/-- Catch-fire with locked synchronisation: SC unless racy (`DrfL` fails) or split. -/
def Cf : Prop := x.Unsplit → x.DrfL → x.Sc

/-- Catch-fire with `hb = (po ∪ rf)⁺` only. -/
def CfPlain : Prop := x.Unsplit → x.Drf → x.Sc

/-! ## Boolean checks for concrete executions -/

/-- `hb` as computed by `reach`. -/
def hbB : BRel x.n := fun a b => BRel.reach x.thinAir a b

/-- `hbL` as computed by `reach`. -/
def hbLB : BRel x.n := fun a b => BRel.reach x.syncL a b

/-- The `hb` reach sets are closed (so `hbB` is exact). -/
def hbClosedB : Bool := BRel.reachClosedB x.thinAir

/-- The `hbL` reach sets are closed (so `hbLB` is exact). -/
def hbLClosedB : Bool := BRel.reachClosedB x.syncL

/-- `Unsplit`, as a Boolean. -/
def unsplitB : Bool :=
  (List.finRange x.n).all fun a => (List.finRange x.n).all fun b => !x.sm a b || a == b

/-- `Drf`, as a Boolean (exact when `hbClosedB`). -/
def drfB : Bool :=
  (List.finRange x.n).all fun a => (List.finRange x.n).all fun b =>
    !x.conflict a b || x.hbB a b || x.hbB b a

/-- `DrfL`, as a Boolean (exact when `hbLClosedB`). -/
def drfLB : Bool :=
  (List.finRange x.n).all fun a => (List.finRange x.n).all fun b =>
    !x.conflict a b || ((x.ev a).isA && (x.ev b).isA) || x.hbLB a b || x.hbLB b a

/-- The coherence part of `Ra`, as a Boolean (exact when `hbClosedB`). -/
def raCohB : Bool :=
  (List.finRange x.n).all fun a => (List.finRange x.n).all fun b => !x.hbB a b || !x.com b a

end Exec

end Silmaril.X86.MemoryModel.Axiomatic

namespace Silmaril.X86.MemoryModel.Lattice

open Silmaril.X86.MemoryModel.Axiomatic

/-! ## Models and their order -/

/-- A memory model: the candidate executions it allows. -/
abbrev Model := Exec → Prop

namespace Model

/-- `M ⊑ N`: every execution `M` allows, `N` allows. -/
def Le (M N : Model) : Prop := ∀ x, M x → N x

/-- `x` separates `M` from `N`: `N` allows it and `M` does not (so `N ⋢ M`). -/
def Sep (x : Exec) (M N : Model) : Prop := N x ∧ ¬ M x

/-- `M ⊏ N`: `M ⊑ N` and some execution separates them. -/
def Lt (M N : Model) : Prop := Le M N ∧ ∃ x, Sep x M N

/-- `M` and `N` are incomparable: each allows an execution the other forbids. -/
def Incomparable (M N : Model) : Prop := (∃ x, Sep x M N) ∧ ∃ x, Sep x N M

/-- The meet: both allow it. -/
def inf (M N : Model) : Model := fun x => M x ∧ N x

/-- The join: either allows it. -/
def sup (M N : Model) : Model := fun x => M x ∨ N x

end Model

/-- Sequential consistency. -/
def sc : Model := Exec.Sc
/-- x86-TSO (axiomatic). -/
def tso : Model := Exec.Tso
/-- The loose x86 model XL. -/
def xl : Model := Exec.Xl
/-- Release/acquire on every access. -/
def ra : Model := Exec.Ra
/-- Catch-fire, locked accesses synchronise (DRF modulo primitives). -/
def cf : Model := Exec.Cf
/-- Catch-fire, only `po ∪ rf` synchronises. -/
def cfPlain : Model := Exec.CfPlain
/-- Anything goes. -/
def top : Model := fun _ => True
/-- Executions all of whose memory units are tame (write-back, not tearable). -/
def tame : Model := Exec.Tame

/-! ## Names -/

/-- The named models. -/
inductive Name where
  | sc
  | tso
  | ra
  | xl
  | cf
  | cfPlain
  | top
  deriving DecidableEq, Repr

/-- The model a name stands for. -/
def Name.model : Name → Model
  | .sc => Lattice.sc
  | .tso => Lattice.tso
  | .ra => Lattice.ra
  | .xl => Lattice.xl
  | .cf => Lattice.cf
  | .cfPlain => Lattice.cfPlain
  | .top => Lattice.top

/-- The proved order on names (reflexive-transitive closure of the proved edges
`sc ⊑ tso`, `tso ⊑ ra`, `tso ⊑ xl`, `tso ⊑ cf`, `ra ⊑ cfPlain`, `cf ⊑ cfPlain`, `xl ⊑ top`,
`cfPlain ⊑ top`). -/
def Name.le : Name → Name → Bool
  | _, .top => true
  | .sc, _ => true
  | .tso, .tso | .tso, .ra | .tso, .xl | .tso, .cf | .tso, .cfPlain => true
  | .ra, .ra | .ra, .cfPlain => true
  | .xl, .xl => true
  | .cf, .cf | .cf, .cfPlain => true
  | .cfPlain, .cfPlain => true
  | _, _ => false

/-- A property of executions holds under the named model: every execution it allows has it.
A client (a process model, a problem) that names its model states its results this way, and
`HoldsUnder.mono` moves them down `⊑`. -/
def HoldsUnder (a : Name) (P : Exec → Prop) : Prop := ∀ x, a.model x → P x

end Silmaril.X86.MemoryModel.Lattice
