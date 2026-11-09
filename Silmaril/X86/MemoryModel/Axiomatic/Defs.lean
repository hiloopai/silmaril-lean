module

public import Mathlib.Logic.Relation
public import Silmaril.X86.MemEvent.Defs

/-!
# Axiomatic memory models over candidate executions: definitions

Herd-style
candidate executions over a finite list of events, with program order `po`, reads-from `rf`,
coherence `co`, derived from-reads `fr`, the internal/external splits `rfe`/`rfi`/`coe`/`fre`,
and locked read-modify-write pairs `rmw`, and two consistency predicates:

* `Exec.Sc` — herd's `sc.cat`: `empty rmw & (fre;coe)` and `acyclic po | ((fr|rf|co);sm)`;
* `Exec.Tso` — herd's `x86tso.cat`: `acyclic po-loc | com` (uniproc; `amo` is empty on x86),
  `empty rmw & (fre;coe)` (atomic) and `acyclic mfence | implied | ppo | rfe | fr | co` (tso),
  with communication lifted through `sm` as in `sc.cat` (identity unless an access is split
  into several units).

The loose model `Exec.Xl` is in `Silmaril.X86.MemoryModel.Xl.Defs`.

## Events and units

An `Ev` is one **access unit**: a read, a write or a fence of one thread. `pos` is the
program-order index of the *access* in its thread; units of the same access share `tid` and
`pos` (relation `sm`, herd's "same memory access"), and `po a b` is `tid a = tid b ∧ pos a <
pos b`, so units of one access are unordered and `po` is a strict order by construction. An
unsplit access is one unit (`addr = accAddr`, `size = accSize`); an access may be split into
byte units (`Ev.bytesSplit`) so that the loose model can let it tear. A locked
read-modify-write is two accesses, a read at `pos` and a write at a later `pos` of the same
thread, both `locked`, related by `rmw`.

## Bytes

`rf` and `co` are **per byte**, as in mixed-size models: `rf r y` is the write unit the read
unit `r` takes byte `y` from (`none`: the initial value), and `co y` lists the write units of
byte `y` in coherence order (the initial write is implicitly first). Event-level `rf`/`co`/`fr`
are the unions over bytes. Indices are plain `Nat`s into `evs`, so literal executions are easy
to write; `Exec.Wf` checks that they are sensible. **None of the consistency predicates and
none of the inclusion theorems need `Wf`.**

## Acyclicity

`BRel.Acyclic r` is herd's `acyclic r`: no `TransGen` cycle. `BRel.acyclicB` is a decision
procedure (repeatedly remove a node without predecessors); its correctness
(`BRel.acyclic_iff`) and the `Decidable` instances are in `Silmaril.X86.MemoryModel.Axiomatic.Thms`.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Axiomatic


/-! ## Finite Boolean relations -/

/-- A decidable binary relation on the events `Fin n`. -/
abbrev BRel (n : Nat) := Fin n → Fin n → Bool

namespace BRel
variable {n : Nat}

/-- Union. -/
def union (r s : BRel n) : BRel n := fun a b => r a b || s a b

/-- Intersection. -/
def inter (r s : BRel n) : BRel n := fun a b => r a b && s a b

/-- Sequential composition `r ; s`. -/
def seq (r s : BRel n) : BRel n := fun a b => (List.finRange n).any fun c => r a c && s c b

/-- `r` as a proposition-valued relation. -/
def Holds (r : BRel n) (a b : Fin n) : Prop := r a b = true

/-- herd's `acyclic r`: the transitive closure of `r` is irreflexive. -/
def Acyclic (r : BRel n) : Prop := ∀ a, ¬ Relation.TransGen r.Holds a a

/-- herd's `empty r`. -/
def Empty (r : BRel n) : Prop := ∀ a b, r a b = false

/-- A node of `S` with no `r`-predecessor in `S`. -/
def source? (r : BRel n) (S : List (Fin n)) : List (Fin n) → Option (Fin n)
  | [] => none
  | b :: l => if S.all (fun a => !r a b) then some b else source? r S l

/-- Remove nodes without predecessors, at most `k` times; `true` iff `S` empties. -/
def peel (r : BRel n) : Nat → List (Fin n) → Bool
  | 0, S => S.isEmpty
  | k + 1, S =>
    match source? r S S with
    | none => S.isEmpty
    | some b => peel r k (S.erase b)

/-- Decision procedure for `Acyclic` (Kahn's algorithm). -/
def acyclicB (r : BRel n) : Bool := peel r n (List.finRange n)

/-- Decision procedure for `Empty`. -/
def emptyB (r : BRel n) : Bool :=
  (List.finRange n).all fun a => (List.finRange n).all fun b => !r a b

end BRel

/-! ## Events -/

/-- The direction of an access unit. -/
inductive Act where
  | read
  | write
  | fence (k : X86.Atomic9.FenceKind)
  deriving DecidableEq, Repr

/-- The memory annotation of an access: an ordinary write-back access, a non-temporal store
(`movnti`, `movntdq`, ...), or a store of a string instruction (`rep movs`/`rep stos`). Only
the loose model distinguishes them. -/
inductive Ann where
  | wb
  | nt
  | str
  deriving DecidableEq, Repr

/-- One access unit. `addr`/`size` are the bytes of this unit; `accAddr`/`accSize` those of
the whole access it belongs to. `data` holds the bytes a write unit writes (lowest address
first). `locked` is herd's `X`/`A` set: the unit belongs to a locked instruction (a `lock`ed
RMW or `xchg` with memory). -/
structure Ev where
  tid : Nat
  pos : Nat
  act : Act
  addr : Nat := 0
  size : Nat := 0
  accAddr : Nat := addr
  accSize : Nat := size
  locked : Bool := false
  ann : Ann := .wb
  data : List (BitVec 8) := []
  deriving DecidableEq, Repr

namespace Ev

/-- A read (herd `R`). -/
def isR (e : Ev) : Bool := e.act == .read

/-- A write (herd `W`). -/
def isW (e : Ev) : Bool := e.act == .write

/-- A memory access (herd `M`). -/
def isM (e : Ev) : Bool := e.isR || e.isW

/-- A memory access of a locked instruction (herd `A`, i.e. `X` on x86). -/
def isA (e : Ev) : Bool := e.locked && e.isM

/-- A fence of kind `k` (herd `MFENCE`, `SFENCE`, `LFENCE`). -/
def isFence (k : X86.Atomic9.FenceKind) (e : Ev) : Bool := e.act == .fence k

/-- The unit touches byte `y`. -/
def covers (e : Ev) (y : Nat) : Bool := decide (e.addr ≤ y) && decide (y < e.addr + e.size)

/-- The bytes of the unit. -/
def bytes (e : Ev) : List Nat := List.range' e.addr e.size

/-- The access the unit belongs to is single-copy atomic on x86: naturally aligned and at most
eight bytes (`MemEvent.Event.singleCopy`). -/
def singleCopy (e : Ev) : Bool := decide (e.accSize ≤ 8) && e.accAddr % e.accSize == 0

/-- The byte `y` of a write unit. -/
def byte (e : Ev) (y : Nat) : BitVec 8 := (e.data[y - e.addr]?).getD 0

/-- Split a unit into one unit per byte (same `tid`, `pos` and access footprint). -/
def bytesSplit (e : Ev) : List Ev :=
  e.bytes.map fun y =>
    { e with addr := y, size := 1, data := if e.act == .write then [e.byte y] else [] }

/-- The access units of a `MemEvent.Event` of thread `tid` at program positions `pos` (and
`pos + 1` for the write half of a read-modify-write), unsplit. `data` is what the write (half)
writes. Pairing the halves of a locked RMW in `Exec.rmw` is up to the caller. -/
def ofMemEvent (tid pos : Nat) (ann : Ann) (data : List (BitVec 8)) (e : X86.MemEvent.Event) :
    List Ev :=
  let u (k : Nat) (a : Act) (d : List (BitVec 8)) : Ev :=
    { tid, pos := pos + k, act := a, addr := e.addr, size := e.size, locked := e.locked, ann,
      data := d }
  match e.kind with
  | .load => [u 0 .read []]
  | .store => [u 0 .write data]
  | .rmw => [u 0 .read [], u 1 .write data]
  | .fence k => [{ tid, pos, act := .fence k, locked := e.locked }]

end Ev

/-! ## Candidate executions -/

/-- `a` occurs strictly before `b` in `l` (at its first occurrence). -/
def before : List Nat → Nat → Nat → Bool
  | [], _, _ => false
  | c :: l, a, b => if c == a then l.contains b else before l a b

/-- A candidate execution. `rf r y = some w`: the read unit `r` takes byte `y` from the write
unit `w` (`none`: from the initial state); `co y`: the write units of byte `y` in coherence
order, after the initial write; `rmw`: the (read, write) pairs of locked read-modify-writes. -/
structure Exec where
  evs : List Ev
  rf : Nat → Nat → Option Nat := fun _ _ => none
  co : Nat → List Nat := fun _ => []
  rmw : List (Nat × Nat) := []

namespace Exec
variable (x : Exec)

/-- Number of units. -/
abbrev n : Nat := x.evs.length

/-- The unit at an index. -/
def ev (a : Fin x.n) : Ev := x.evs[a]

/-! ### Base relations -/

/-- Program order: same thread, earlier access. -/
def po : BRel x.n := fun a b => (x.ev a).tid == (x.ev b).tid && decide ((x.ev a).pos < (x.ev b).pos)

/-- herd's `sm`: units of the same access (reflexive). -/
def sm : BRel x.n := fun a b => (x.ev a).tid == (x.ev b).tid && (x.ev a).pos == (x.ev b).pos

/-- herd's `ext`: different threads. -/
def ext : BRel x.n := fun a b => (x.ev a).tid != (x.ev b).tid

/-- herd's `loc`, at byte granularity: two memory units that share a byte. -/
def loc : BRel x.n := fun a b =>
  (x.ev a).isM && (x.ev b).isM && (x.ev a).bytes.any (x.ev b).covers

/-- herd's `po-loc`. -/
def poLoc : BRel x.n := x.po.inter x.loc

/-- Reads-from, lifted to units: `w` writes a byte that `r` takes from it. -/
def rfR : BRel x.n := fun w r =>
  (x.ev w).isW && (x.ev r).isR &&
    (x.ev r).bytes.any fun y => x.rf r y == some w.val && (x.ev w).covers y

/-- Coherence, lifted to units: `a` precedes `b` in the coherence order of a shared byte. -/
def coR : BRel x.n := fun a b =>
  (x.ev a).isW && (x.ev b).isW &&
    (x.ev a).bytes.any fun y => (x.ev b).covers y && before (x.co y) a.val b.val

/-- From-reads, lifted to units (herd `rf^-1;co`, with the initial write before every write):
`r` takes a byte from a write that `w` is coherence-after, or from the initial state. -/
def frR : BRel x.n := fun r w =>
  (x.ev r).isR && (x.ev w).isW &&
    (x.ev r).bytes.any fun y =>
      (x.ev w).covers y &&
        match x.rf r y with
        | none => true
        | some v => before (x.co y) v w.val

/-- herd's `com = rf | co | fr`. -/
def com : BRel x.n := x.rfR.union (x.coR.union x.frR)

/-- herd's `rfe`. -/
def rfe : BRel x.n := x.rfR.inter x.ext
/-- herd's `rfi`. -/
def rfi : BRel x.n := fun a b => x.rfR a b && !x.ext a b
/-- herd's `coe`. -/
def coe : BRel x.n := x.coR.inter x.ext
/-- herd's `fre`. -/
def fre : BRel x.n := x.frR.inter x.ext

/-- The locked read-modify-write pairs. -/
def rmwR : BRel x.n := fun a b => x.rmw.contains (a.val, b.val)

/-- herd's `fencerel(B) = (po & (_ * B)); po` for fences of kind `k`. -/
def fencerel (k : X86.Atomic9.FenceKind) : BRel x.n := fun a b =>
  (List.finRange x.n).any fun f => (x.ev f).isFence k && x.po a f && x.po f b

/-- herd's `mfence` (`x86fences.cat`). -/
def mfence : BRel x.n := x.fencerel .mfence

/-! ### Atomicity -/

/-- herd's `empty rmw & (fre;coe)`, as a Boolean. -/
def atomicB : Bool := BRel.emptyB (x.rmwR.inter (x.fre.seq x.coe))

/-! ### SC (`sc.cat`) -/

/-- `po | ((fr | rf | co); sm)`. -/
def scRel : BRel x.n := x.po.union (x.com.seq x.sm)

/-- Sequential consistency (herd `sc.cat`). -/
def Sc : Prop := x.atomicB = true ∧ BRel.Acyclic x.scRel

/-! ### x86-TSO (`x86tso.cat`) -/

/-- Uniproc: `po-loc | com` (`amo` is empty on x86), communication lifted through `sm`. -/
def uniproc : BRel x.n := x.poLoc.union (x.com.seq x.sm)

/-- herd's `po_ghb = WW(po) | RM(po)`. -/
def ppo : BRel x.n := fun a b =>
  x.po a b && (((x.ev a).isW && (x.ev b).isW) || ((x.ev a).isR && (x.ev b).isM))

/-- herd's `implied = MA(WR(po)) | AM(WR(po))`. -/
def implied : BRel x.n := fun a b =>
  x.po a b && (x.ev a).isW && (x.ev b).isR && ((x.ev a).isA || (x.ev b).isA)

/-- `rfe | fr | co`, lifted through `sm`. -/
def comGhb : BRel x.n := (x.rfe.union (x.frR.union x.coR)).seq x.sm

/-- herd's `ghb = mfence | implied | po_ghb | rfe | fr | co`. -/
def ghb : BRel x.n := x.mfence.union (x.implied.union (x.ppo.union x.comGhb))

/-- x86-TSO (herd `x86tso.cat`): uniproc, atomic and tso. -/
def Tso : Prop := x.atomicB = true ∧ BRel.Acyclic x.uniproc ∧ BRel.Acyclic x.ghb

/-! ### Well-formedness and outcomes -/

/-- Indices in range. -/
def valid (i : Nat) : Bool := decide (i < x.n)

/-- The unit at a `Nat` index (a dummy fence out of range). -/
def evN (i : Nat) : Ev := x.evs.getD i { tid := 0, pos := 0, act := .fence .lfence }

/-- The memory bytes the execution touches. -/
def touched : List Nat := (x.evs.filter Ev.isM).flatMap Ev.bytes

/-- Well-formedness of a candidate (not needed by any theorem; for enumerators):
* every read byte comes from an in-range write unit covering that byte, or from the initial
  state;
* for every touched byte, `co` lists exactly the write units covering it, without repetition;
* `rmw` pairs a read with a later write of the same thread, both locked, on the same access
  footprint;
* units of one access agree on direction, `locked`, annotation and access footprint, and lie
  inside it; memory units are non-empty, write units carry `size` bytes, fences are empty. -/
def Wf : Bool :=
  (List.finRange x.n).all (fun r =>
    !(x.ev r).isR || (x.ev r).bytes.all fun y =>
      match x.rf r.val y with
      | none => true
      | some w => x.valid w && (x.evN w).isW && (x.evN w).covers y) &&
  x.touched.all (fun y =>
    (x.co y).Nodup && (x.co y).all (fun w => x.valid w && (x.evN w).isW && (x.evN w).covers y) &&
    (List.finRange x.n).all fun w => !((x.ev w).isW && (x.ev w).covers y) || (x.co y).contains w.val) &&
  x.rmw.all (fun p =>
    x.valid p.1 && x.valid p.2 && (x.evN p.1).isR && (x.evN p.2).isW &&
    (x.evN p.1).tid == (x.evN p.2).tid && decide ((x.evN p.1).pos < (x.evN p.2).pos) &&
    (x.evN p.1).locked && (x.evN p.2).locked &&
    (x.evN p.1).accAddr == (x.evN p.2).accAddr && (x.evN p.1).accSize == (x.evN p.2).accSize) &&
  (List.finRange x.n).all (fun a => (List.finRange x.n).all fun b =>
    !x.sm a b || ((x.ev a).act == (x.ev b).act && (x.ev a).locked == (x.ev b).locked &&
      (x.ev a).ann == (x.ev b).ann && (x.ev a).accAddr == (x.ev b).accAddr &&
      (x.ev a).accSize == (x.ev b).accSize)) &&
  x.evs.all (fun e =>
    if e.isM then
      decide (0 < e.size) && decide (e.accAddr ≤ e.addr) &&
        decide (e.addr + e.size ≤ e.accAddr + e.accSize) && (!e.isW || e.data.length == e.size)
    else e.size == 0)

/-- The byte `y` that read unit `r` returns, given the initial memory. -/
def readByte (init : Nat → BitVec 8) (r : Nat) (y : Nat) : BitVec 8 :=
  match x.rf r y with
  | none => init y
  | some w => (x.evN w).byte y

/-- The bytes read unit `r` returns, lowest address first. -/
def readBytes (init : Nat → BitVec 8) (r : Nat) : List (BitVec 8) :=
  (x.evN r).bytes.map (x.readByte init r)

/-- The final value of byte `y`: the coherence-last write, else the initial value. -/
def finalByte (init : Nat → BitVec 8) (y : Nat) : BitVec 8 :=
  match (x.co y).getLast? with
  | none => init y
  | some w => (x.evN w).byte y

end Exec

end Silmaril.X86.MemoryModel.Axiomatic
