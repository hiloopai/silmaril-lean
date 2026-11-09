module

public import Silmaril.X86.Concurrency.Cir.Seq.Defs
public import Silmaril.X86.Concurrency.Cir.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Seq.Lab

/-!
# The single-threaded lift: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Seq/{Mem,Exec,Units,Trace,Lab}.lean`).

**One CIR thread** (the IR statement; `solo locs s` is the one-thread program):

* `solo_behav_iff`: for a thread-free statement with positive access sizes, under **every**
  model `M` with `SC ⊑ M ⊑ XL`, the behaviours of `solo locs s` are exactly its sequential runs
  (`SeqRun`: a thread run whose trace replays on one flat memory) from the initial memory;
* `solo_behav_sound` needs only `M ⊑ XL`, `solo_behav_complete` only `SC ⊑ M`;
* `cirSeqSc`: the statement `Task.cirSeqSc` (the case `M = SC`) holds;
* `solo_behav_model`, `solo_behav_model_iff_sc`, `solo_safe_iff`: the same for each of the
  three models, the models agree on one thread, and a safety property of a one-thread program
  holds under XL iff it holds of its sequential runs.

**One litmus trace** (the same statement one level down, for any per-thread trace set):

* `axReach_one_iff`: `AxReach` for a one-thread test whose actions are `ActOk` is exactly
  the final states of the sequential replays (`actsReplay`) of its traces;
* `oneSem_iff`: one thread's action list under `M`, from **any** initial memory (`OneSem`), has
  exactly its sequential replay as behaviour.

**How it is proved.** On the units of one thread (`Proofs/.../Seq/Exec.lean`), XL's coherence
rule alone (`acyclic po-loc | com`) forces every read byte to come from the last earlier write
of that byte and the coherence-last write to be the last write; conversely the candidate that
takes exactly these is SC-consistent and well-formed. Splitting a tearable access into byte
units (`units`) does not change its sequential meaning (`Proofs/.../Seq/Units.lean`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Seq

open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace Test Final AxReach finalOf initByte Loc Model)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-! ## One CIR thread -/

/-- **The single-threaded lift for CIR**: under every `M` with `SC ⊑ M ⊑ XL`, a one-thread,
thread-free CIR program with positive access sizes has exactly its sequential behaviours. -/
theorem solo_behav_iff (locs : List Loc) (s : Stmt) (ht : s.threadFree = true)
    (hp : s.posSizes = true) {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl)
    (f : Final) :
    Behav (solo locs s) M f ↔
      ∃ tr rs m, SeqRun s Regs.zero (initByte locs) tr rs m ∧ f = soloFinal rs m :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.solo_behav_iff locs s ht hp hsc hxl f

/-- The behaviours of a one-thread program under `M ⊑ XL` are sequential. -/
theorem solo_behav_sound (locs : List Loc) (s : Stmt) (ht : s.threadFree = true)
    (hp : s.posSizes = true) {M : Exec → Prop} (hxl : M ⊑ Exec.Xl) {f : Final}
    (h : Behav (solo locs s) M f) :
    ∃ tr rs m, SeqRun s Regs.zero (initByte locs) tr rs m ∧ f = soloFinal rs m :=
  (Silmaril.Proofs.X86.Concurrency.Cir.Seq.solo_behav_iff locs s ht hp (M := fun x => M x ∨ x.Sc)
    (fun _ h => .inr h) (fun x h => h.elim (hxl x) (fun h => Exec.xl_of_sc x h)) f).mp
    (behav_mono (fun _ h => .inl h) h)

/-- The sequential behaviours of a one-thread program are behaviours under every `SC ⊑ M`. -/
theorem solo_behav_complete (locs : List Loc) (s : Stmt) (ht : s.threadFree = true)
    (hp : s.posSizes = true) {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) {tr : List Lab} {rs : Regs}
    {m : Mem} (h : SeqRun s Regs.zero (initByte locs) tr rs m) :
    Behav (solo locs s) M (soloFinal rs m) :=
  behav_mono hsc ((solo_behav_iff locs s ht hp (MLe.refl _) sc_le_xl _).mpr ⟨tr, rs, m, h, rfl⟩)

/-- **`Task.cirSeqSc` holds** (the lift at `M = SC`). -/
theorem cirSeqSc : Task.cirSeqSc := fun locs s ht hp f =>
  solo_behav_iff locs s ht hp (MLe.refl _) sc_le_xl f

theorem model_sc_le (M : Model) : Exec.Sc ⊑ M.Holds := by
  cases M
  · exact MLe.refl _
  · exact sc_le_tso
  · exact sc_le_xl

theorem model_le_xl (M : Model) : M.Holds ⊑ Exec.Xl := by
  cases M
  · exact sc_le_xl
  · exact tso_le_xl
  · exact MLe.refl _

/-- The lift for each of three models. -/
theorem solo_behav_model (locs : List Loc) (s : Stmt) (ht : s.threadFree = true)
    (hp : s.posSizes = true) (M : Model) (f : Final) :
    Behav (solo locs s) M.Holds f ↔
      ∃ tr rs m, SeqRun s Regs.zero (initByte locs) tr rs m ∧ f = soloFinal rs m :=
  solo_behav_iff locs s ht hp (model_sc_le M) (model_le_xl M) f

/-- On one thread, SC, x86-TSO and XL have the same behaviours. -/
theorem solo_behav_model_iff_sc (locs : List Loc) (s : Stmt) (ht : s.threadFree = true)
    (hp : s.posSizes = true) (M : Model) (f : Final) :
    Behav (solo locs s) M.Holds f ↔ Behav (solo locs s) Exec.Sc f :=
  (solo_behav_model locs s ht hp M f).trans (solo_behav_model locs s ht hp .sc f).symm

/-- **Sequential reasoning suffices**: a property of final states holds for every behaviour of a
one-thread program under `M ⊑ XL` iff it holds after every sequential run. -/
theorem solo_safe_iff (locs : List Loc) (s : Stmt) (ht : s.threadFree = true)
    (hp : s.posSizes = true) {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl)
    (Q : Final → Prop) :
    Safe (solo locs s) M Q ↔
      ∀ tr rs m, SeqRun s Regs.zero (initByte locs) tr rs m → Q (soloFinal rs m) := by
  constructor
  · intro h tr rs m hr
    exact h _ ((solo_behav_iff locs s ht hp hsc hxl _).mpr ⟨tr, rs, m, hr, rfl⟩)
  · intro h f hf
    obtain ⟨tr, rs, m, hr, rfl⟩ := (solo_behav_iff locs s ht hp hsc hxl f).mp hf
    exact h tr rs m hr

/-! ## One litmus trace -/

/-- **The single-threaded lift for litmus traces**: for a one-thread test whose actions are `ActOk`,
under every `M` with `SC ⊑ M ⊑ XL`, the axiomatic final states are exactly the final states of
the sequential replays of its traces. -/
theorem axReach_one_iff (t : Test) (T : List XTrace) (hok : ∀ tr ∈ T, ∀ a ∈ tr.acts, ActOk a)
    {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) (f : Final) :
    AxReach t [T] M f ↔ ∃ tr ∈ T, ∃ m, actsReplay t.initMem tr.acts = some m ∧ f = finalOf [tr] m :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.axReach_one_iff t T hok hsc hxl f

/-- **The single-threaded lift from any memory**: one thread's `ActOk` action list under every
`M` with `SC ⊑ M ⊑ XL` has exactly its sequential replay as behaviour. -/
theorem oneSem_iff {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) (m0 : Mem)
    (acts : List XAct) (hok : ∀ a ∈ acts, ActOk a) (m : Mem) :
    OneSem M m0 acts m ↔ actsReplay m0 acts = some m :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.oneSem_iff hsc hxl m0 acts hok m

/-- Sequential replay composes. -/
theorem actsReplay_append (m : Mem) (l l' : List XAct) :
    actsReplay m (l ++ l') = (actsReplay m l).bind fun m' => actsReplay m' l' :=
  Silmaril.Proofs.X86.Concurrency.Cir.Seq.actsReplay_append m l l'

/-- **The one-thread semantics composes**: under `SC ⊑ M ⊑ XL`, a behaviour of `l ++ l'` is a
behaviour of `l` followed by one of `l'`, so a single-threaded run may be read under `M` step by
step. -/
theorem oneSem_append {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) (m0 : Mem)
    (l l' : List XAct) (hl : ∀ a ∈ l, ActOk a) (hl' : ∀ a ∈ l', ActOk a) (m : Mem) :
    OneSem M m0 (l ++ l') m ↔ ∃ m1, OneSem M m0 l m1 ∧ OneSem M m1 l' m := by
  rw [oneSem_iff hsc hxl m0 _ (fun a ha => (List.mem_append.mp ha).elim (hl a) (hl' a)),
    actsReplay_append]
  constructor
  · intro h
    cases h1 : actsReplay m0 l with
    | none => rw [h1] at h; cases h
    | some m1 =>
      rw [h1, Option.bind_some] at h
      exact ⟨m1, (oneSem_iff hsc hxl m0 l hl m1).mpr h1, (oneSem_iff hsc hxl m1 l' hl' m).mpr h⟩
  · rintro ⟨m1, h1, h2⟩
    rw [(oneSem_iff hsc hxl m0 l hl m1).mp h1, Option.bind_some]
    exact (oneSem_iff hsc hxl m1 l' hl' m).mp h2

/-- **Each read is forced**. Under `SC ⊑ M ⊑ XL`, if a one-thread action list
has any behaviour, each of its loads and read-modify-writes returns exactly the bytes the
sequential replay of the actions before it leaves. `OneSem` takes the read bytes as given; this
says no other read bytes are consistent, so a machine that issues its next action from the bytes
it has read follows the sequential run read by read. -/
theorem oneSem_read_forced {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) (m0 : Mem)
    (p : List XAct) (a : XAct) (q : List XAct) (hok : ∀ x ∈ p ++ a :: q, ActOk x) {m : Mem}
    (h : OneSem M m0 (p ++ a :: q) m) (hk : a.ev.kind = .load ∨ a.ev.kind = .rmw) :
    ∃ m1, actsReplay m0 p = some m1 ∧ a.rd = bytesAt m1 a.ev.addr a.ev.size := by
  rw [oneSem_iff hsc hxl m0 _ hok, actsReplay_append] at h
  cases h1 : actsReplay m0 p with
  | none => rw [h1] at h; cases h
  | some m1 =>
    rw [h1, Option.bind_some] at h
    refine ⟨m1, rfl, ?_⟩
    simp only [actsReplay, actStep] at h
    rcases hk with hk | hk <;> rw [hk] at h <;> simp only at h <;>
      (split at h
       · rename_i he; exact he.symm
       · cases h)

end Silmaril.X86.Concurrency.Cir.Seq
