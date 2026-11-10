module

public import Silmaril.X86.MemoryModel.Axiomatic.Defs

/-!
# The loose x86 concurrency model XL: definitions

XL is stated over
the same candidate executions as `Exec.Sc` and `Exec.Tso` (`Silmaril.X86.MemoryModel.Axiomatic`).

* On **tame** units — write-back, single-copy atomic (aligned, at most eight bytes), not
  overlapping an access of another footprint — XL has exactly the x86-TSO axioms of herd's
  `x86tso.cat` (`Xl.xl_iff_tso_of_tame` in `Silmaril.X86.MemoryModel.Xl.Thms`).
* **Weak stores** (non-temporal or string-instruction stores, `Ann.nt`/`Ann.str`) lose the
  `po_ghb` order with every other access; they are ordered only by `mfence`, by `sfence`
  (against other stores), and by locked instructions (before, after or between).
* **Tearable** units (of a misaligned or larger-than-eight-byte access, or of an access that
  overlaps an access with a different footprint) lose the `sm` lifting of communication: when
  such an access is split into byte units (`Ev.bytesSplit`), each byte is coherent and ordered
  on its own, so the access may tear per byte.
* Always: coherence (`acyclic po-loc | com`), locked-RMW atomicity (`empty rmw & (fre;coe)`)
  and no-thin-air (`acyclic po | rf`).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Axiomatic

namespace Ev

/-- A non-temporal or string-instruction store. -/
def weak (e : Ev) : Bool := e.isW && e.ann != .wb

/-- The access footprints of two units overlap. -/
def accOverlap (e f : Ev) : Bool :=
  decide (e.accAddr < f.accAddr + f.accSize) && decide (f.accAddr < e.accAddr + e.accSize)

end Ev

namespace Exec
variable (x : Exec)

/-- The unit may tear: a memory unit of a misaligned or wide access, or of an access that
overlaps a memory access with a different footprint (mixed size). -/
def tearable (a : Fin x.n) : Bool :=
  (x.ev a).isM &&
    (!(x.ev a).singleCopy ||
      (List.finRange x.n).any fun b =>
        (x.ev b).isM && (x.ev a).accOverlap (x.ev b) &&
          ((x.ev a).accAddr != (x.ev b).accAddr || (x.ev a).accSize != (x.ev b).accSize))

/-- `sm` restricted to non-tearable accesses (reflexive). -/
def smT : BRel x.n := fun a b => decide (a = b) || (x.sm a b && !x.tearable a)

/-- XL coherence: `po-loc | com`, lifted through `smT`. -/
def uniprocXl : BRel x.n := x.poLoc.union (x.com.seq x.smT)

/-- No-thin-air: `po | rf`. -/
def thinAir : BRel x.n := x.po.union x.rfR

/-- `po_ghb` without weak stores. -/
def ppoXl : BRel x.n := fun a b => x.ppo a b && !(x.ev a).weak && !(x.ev b).weak

/-- Locked-instruction order: memory units in program order with a locked unit at either end
or in between (contains herd's `implied`). -/
def lockXl : BRel x.n := fun a b =>
  (x.ev a).isM && (x.ev b).isM && x.po a b &&
    ((x.ev a).isA || (x.ev b).isA ||
      (List.finRange x.n).any fun l => (x.ev l).isA && x.po a l && x.po l b)

/-- `sfence` orders stores with stores. -/
def sfenceXl : BRel x.n := fun a b =>
  (x.ev a).isW && (x.ev b).isW && x.fencerel .sfence a b

/-- `rfe | fr | co`, lifted through `smT`. -/
def comGhbXl : BRel x.n := (x.rfe.union (x.frR.union x.coR)).seq x.smT

/-- XL's global order: `mfence | ppoXl | lockXl | sfenceXl | rfe | fr | co`. -/
def ghbXl : BRel x.n :=
  x.mfence.union (x.ppoXl.union (x.lockXl.union (x.sfenceXl.union x.comGhbXl)))

/-- The loose x86 model XL. -/
def Xl : Prop :=
  x.atomicB = true ∧ BRel.Acyclic x.uniprocXl ∧ BRel.Acyclic x.thinAir ∧ BRel.Acyclic x.ghbXl

/-- Every memory unit is tame: write-back and not tearable. -/
def Tame : Prop := ∀ a, (x.ev a).weak = false ∧ x.tearable a = false

end Exec

end Silmaril.X86.MemoryModel.Axiomatic
