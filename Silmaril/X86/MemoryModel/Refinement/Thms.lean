module

public import Silmaril.X86.MemoryModel.Refinement.Defs
public import Silmaril.Semantics.MemoryRefinement.Thms
public import Silmaril.X86.MemoryModel.Lattice.Thms
public import Silmaril.X86.Concurrency.Lift.Thms
public import Silmaril.X86.Extends.Thms
import Silmaril.Proofs.X86.MemoryModel.Refinement.Basic

/-! # Proof transport for lattice inclusions, DRF, tame XL, and a single thread -/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Refinement

open Silmaril.Semantics.MemoryRefinement
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Concurrency
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (XAct)

theorem guarded_wp (allowed good candidates post : Exec → Prop) :
    (guarded allowed good).wp post candidates ↔
      (∀ exec, candidates exec → good exec) ∧ ∀ exec, candidates exec → allowed exec → post exec := by
  simp [Model.wp, guarded, and_imp]

/-- Keep a weaker guard and read concrete executions back under the stronger one. -/
def guardArrow {src dst good keep : Exec → Prop} (weaken : ∀ x, good x → keep x)
    (back : ∀ x, good x → dst x → src x) : Hom (guarded src good) (guarded dst keep) :=
  ⟨Eq, fun | rfl, safe => let allGood := Classical.not_not.mp safe
    ⟨fun bad => bad fun x hx => weaken x (allGood x hx),
      fun x ⟨hx, allowed⟩ => ⟨hx, back x (allGood x hx) allowed⟩⟩⟩

/-- Proofs go *against* inclusion of allowed executions. Includes RA, cfPlain and top. -/
def ofLe {small big : Lattice.Model} (included : Lattice.Model.Le small big) :
    Hom (guarded big Lattice.top) (guarded small Lattice.top) :=
  guardArrow (fun _ h => h) (fun x _ => included x)

/-- `tso ⊑ cf`: SC with racy or split candidates as UB. Carry any next guard along. -/
def drf (keep : Exec → Prop) : Hom (guarded Lattice.sc (fun x => raceFree x ∧ keep x)) (guarded Lattice.tso keep) :=
  guardArrow (fun _ h => h.2) (fun x h allowed => Lattice.tso_le_cf x allowed h.1.1 h.1.2)

/-- No unconditional TSO-to-XL proof arrow: this one spends the tameness guard. -/
def tameXL : Hom (guarded Lattice.tso Lattice.tame) (guarded Lattice.xl Lattice.top) :=
  guardArrow (fun _ _ => trivial) (fun x tame allowed => Lattice.xl_tame_le_tso x ⟨allowed, tame⟩)

def drfXL := (drf Lattice.tame).comp tameXL

/-- Prove a postcondition only for SC, then use it for all XL executions of this client. -/
theorem xl_of_drf_tame (candidates post : Exec → Prop)
    (safe : ∀ x, candidates x → raceFree x ∧ Lattice.tame x)
    (sc : ∀ x, candidates x → Lattice.sc x → post x) : ∀ x, candidates x → Lattice.xl x → post x :=
  ((guarded_wp _ _ _ _).1 (drfXL.transport ⟨candidates, rfl, rfl⟩ ((guarded_wp _ _ _ _).2 ⟨safe, sc⟩))).2

/-- The existing CIR single-thread result as an arrow at the observable final state. -/
def solo (locs : List Litmus.Loc) (stmt : Cir.Stmt) (free : stmt.threadFree = true) (sizes : stmt.posSizes = true)
    {model : Exec → Prop} (upper : Cir.MLe model Exec.Xl) :
    Hom (⟨Unit, fun _ out => ∃ tr rs mem, Cir.SeqRun stmt Cir.Regs.zero (Litmus.initByte locs) tr rs mem ∧
        out = Cir.Seq.soloFinal rs mem, fun _ => False⟩ : Model Litmus.Final)
      ⟨Unit, fun _ => Cir.Behav (Cir.Seq.solo locs stmt) model, fun _ => False⟩ :=
  ⟨Eq, fun _ safe => ⟨safe, fun _ => Cir.Seq.solo_behav_sound locs stmt free sizes upper⟩⟩

section
variable {State Obs : Type} {step : State → Option State} {mem : State → Cir.Mem}
    {events : State → List XAct → Prop} {model : Exec → Prop} (flat : Lift.FlatStep step mem events)
    (lower : Cir.MLe Exec.Sc model) (upper : Cir.MLe model Exec.Xl) (count : Nat) (see : State → State → Obs)

include flat lower upper in
theorem singleThread_sound (start : State) :
    SoundAt (sequential step count see) (under step mem events model count see) start start :=
  Proofs.X86.MemoryModel.Refinement.singleThread_sound flat lower upper count see start

/-- The `RunUnder` part of `Lift.totalUnder_of`, as a stackable arrow at any finite prefix. -/
def singleThread :
    Hom (sequential step count see) (under step mem events model count see) :=
  ⟨Eq, fun | rfl => singleThread_sound flat lower upper count see _⟩

end

/-- A bounded WP requires an actual endpoint and memory-event trace. Determinism of `run` fixes the endpoint. -/
theorem wp_under_iff {State Obs : Type} {step : State → Option State} {mem : State → Cir.Mem}
    {events : State → List XAct → Prop} {model : Exec → Prop} {count : Nat} {see : State → State → Obs}
    {post : Obs → Prop} {start : State} : (under step mem events model count see).wp post start ↔
    ∃ stop, run step count start = some stop ∧ Lift.RunUnder model step mem events start stop ∧ post (see start stop) :=
  ⟨fun wp => let ⟨stop, done⟩ := Classical.not_not.mp wp.1
             ⟨stop, done.1, done.2, wp.2 _ ⟨stop, done, rfl⟩⟩,
   fun ⟨stop, ran, cert, ok⟩ => ⟨fun bad => bad ⟨stop, ran, cert⟩, fun _ ⟨_, ⟨hit, _⟩, eq⟩ =>
     eq ▸ Option.some.inj (ran.symm.trans hit) ▸ ok⟩⟩

/-- In the existing total contract the prefix length is existential *after* choosing the call entry. -/
theorem totalUnder_iff_wp {State : Type} (isa : SegVC.Isa State) (spec : FnContract.Spec State)
    (events : State → List XAct → Prop) (model : Exec → Prop) : spec.TotalUnder isa events model ↔
    ∀ start, isa.live start → FnContract.AbiEntry (isa.core start) (isa.mem start) → spec.entry start →
      ∃ count, (under isa.step (fun s => Lift.flat (isa.mem s)) events model count (fun _ stop => stop)).wp
        (FnContract.Spec.Result isa spec start) start := by
  simp only [FnContract.Spec.TotalUnder, Machine.Execution.Reaches, wp_under_iff]
  grind

/-- A successful source prefix on the state lens is preserved. No converse at unsupported opcodes. -/
def ofExtends {S T : Type} {small : SegVC.Isa S} {big : SegVC.Isa T} (ext : small.Extends big) (count : Nat) :
    Hom (ofEval (run small.step count)) (ofEval fun start => (run big.step count start).map ext.view) :=
  Hom.ofEval (fun left right => left = ext.view right) fun {_ right _} eq ok => by
    rw [eq] at ok
    simp [ext.run count (x := right) ok, ext.view_put]

end Silmaril.X86.MemoryModel.Refinement
