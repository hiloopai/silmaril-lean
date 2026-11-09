module

public import Silmaril.X86.MemEvent.Defs
import Silmaril.Proofs.X86.MemEvent.Ext
import Silmaril.Proofs.X86.MemEvent.Ext8
import Silmaril.Proofs.X86.MemEvent.Ext9
import Silmaril.Proofs.X86.MemEvent.Sse9
import Silmaril.Proofs.X86.MemEvent.Atomic9
import Silmaril.Proofs.X86.MemEvent.Frame

/-!
# Memory events and locality: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/MemEvent/{Ext,Ext8,Ext9,Sse9,Atomic9,Frame}.lean`). No family is
left as a `Task`.

**Locality, per family** (every constructor of every family; `Local` is congruence on the read
set plus an exact, really-written write set):
* `ext_local`: `Ext.exec`, all 49 `Ext.Instr` constructors;
* `ext8_execNew_local`, `ext8_local`: the 10 byte forms of `Ext8.New`, and `Ext8.exec`;
* `ext9_execNew_local`, `ext9_local`: the 20 forms of `Ext9.New`, and `Ext9.exec`;
* `atomic9_execNew_local`, `atomic9_local`: the 12 atomic forms (with the `locked` tags of
  `Atomic9.tag`), and `Atomic9.exec`;
* `sse9_local`: the 10 SSE forms of `Sse9.Instr`, for every XMM file.

**Frame and the SC reading.**
* `Local.frame`: a local executor changes only its write set, keeps the mapping list, and
  wrote every byte of the write set (write-permitted before, backed after).
* `open_step_eq`, `open9_step_eq`, `atomic9_step_eq`: a step is the fetch (`openFetch`,
  `open9Fetch`, `atomic9Fetch`) followed by the executor on the one memory.
* `open_step_sc`, `open9_step_sc`, `atomic9_step_sc`: every step is a fetched instruction
  whose executor is local for its access list, with the memory patched on exactly its write
  set.

**The instruction-level `Sep` frame rule.**
* `triple_of_step`: a one-step `Sep.Triple` from a footprint (`ChangesWithin`).
* `changesWithin_of_patched`: the footprint from the write set and the changed core locations.
* `triple_step_of_local`: a one-step `Sep.Triple P Q` from the fetched instruction, the
  ownership of its access list's **write set** by the `P`-fragment, and the ownership of the
  changed registers, `rip` and flags (`CoreWithin`); the memory frame comes from locality.

**A concrete access list.** `lockOr_rsp_zero_events`: gcc's SEQ_CST fence `f0 48 83 0c 24 00`
has one locked eight-byte `rmw` event at `rsp`.

**Anti-vacuity.** `not_local_spurious_store`: an access list with a store the instruction does
not do is not local (write sets are exact, not just upper bounds). `not_local_spurious_rmw`:
a load claimed as a read-modify-write is not local. `not_local_dropped_load`: an access list
missing a load is not local (read sets are needed).
-/

@[expose] public section

namespace Silmaril.X86.MemEvent

open Silmaril.X86 (State MState Word)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep (Frag SProp toFrag Triple)

/-! ## Agreement and patching -/

theorem Agree.refl (R : Nat → Prop) (m : Memory) : Agree R m m :=
  Silmaril.Proofs.X86.MemEvent.Agree.refl R m

theorem Agree.mono {R R' : Nat → Prop} {m m' : Memory} (h : Agree R m m')
    (hs : ∀ a, R' a → R a) : Agree R' m m' :=
  Silmaril.Proofs.X86.MemEvent.Agree.mono h hs

theorem Patched.none {W : Nat → Prop} {m m' : Memory} (hW : ∀ a, ¬ W a) :
    Patched W m m m' m' :=
  Silmaril.Proofs.X86.MemEvent.Patched.none hW

/-- **Frame and exactness** of a local executor. -/
theorem Local.frame {ρ ε α : Type} {view : ρ → ε ⊕ (α × Memory)} {exec : Memory → ρ}
    {es : List Event} (hl : Local view exec es) {m m₁ : Memory} {a : α}
    (h : view (exec m) = .inr (a, m₁)) : Patched (writeSet es) m m₁ m m₁ :=
  Silmaril.Proofs.X86.MemEvent.Local.frame hl h

/-! ## Locality per family -/

/-- **`Ext.exec` is local** for `extAccesses`. -/
theorem ext_local (i : Silmaril.X86.Ext.Instr) (s : State) (len : Nat) :
    Local extView (fun m => Silmaril.X86.Ext.exec i s m len) (extAccesses i s len) :=
  Silmaril.Proofs.X86.MemEvent.ext_local i s len

theorem ext8_execNew_local (i : Silmaril.X86.Ext8.New) (s : State) (next : Word) :
    Local extView (fun m => Silmaril.X86.Ext8.execNew i s m next) (ext8NewAccesses i s next) :=
  Silmaril.Proofs.X86.MemEvent.ext8_execNew_local i s next

/-- **`Ext8.exec` is local** for `ext8Accesses`. -/
theorem ext8_local (i : Silmaril.X86.Ext8.Instr) (s : State) (len : Nat) :
    Local extView (fun m => Silmaril.X86.Ext8.exec i s m len) (ext8Accesses i s len) :=
  Silmaril.Proofs.X86.MemEvent.ext8_local i s len

theorem ext9_execNew_local (i : Ext9.New) (s : State) (next : Word) :
    Local extView (fun m => Ext9.execNew i s m next) (ext9NewAccesses i s next) :=
  Silmaril.Proofs.X86.MemEvent.ext9_execNew_local i s next

/-- **`Ext9.exec` is local** for `ext9Accesses`. -/
theorem ext9_local (i : Ext9.Instr) (s : State) (len : Nat) :
    Local extView (fun m => Ext9.exec i s m len) (ext9Accesses i s len) :=
  Silmaril.Proofs.X86.MemEvent.ext9_local i s len

theorem atomic9_execNew_local (i : Atomic9.New) (s : State) (next : Word) :
    Local extView (fun m => Atomic9.execNew i s m next) (atomic9NewAccesses i s next) :=
  Silmaril.Proofs.X86.MemEvent.atomic9_execNew_local i s next

/-- **`Atomic9.exec` is local** for `atomic9Accesses`. -/
theorem atomic9_local (i : Atomic9.Instr) (s : State) (len : Nat) :
    Local extView (fun m => Atomic9.exec i s m len) (atomic9Accesses i s len) :=
  Silmaril.Proofs.X86.MemEvent.atomic9_local i s len

/-- **`Sse9.exec` is local** for `sse9Accesses`, for every XMM file. -/
theorem sse9_local (i : Sse9.Instr) (s : State) (x : Sse9.XFile) (next : Word) :
    Local sse9View (fun m => Sse9.exec i s x m next) (sse9Accesses i s next) :=
  Silmaril.Proofs.X86.MemEvent.sse9_local i s x next

/-! ## A step is a fetch followed by an execution -/

theorem open_step_eq (m : MState) :
    Open.step m =
      (openFetch m.memory m.core.rip.toNat).bind fun p =>
        Open.ofResult (Silmaril.X86.Ext8.exec p.1 m.core m.memory p.2) :=
  Silmaril.Proofs.X86.MemEvent.open_step_eq m

theorem open9_step_eq (m : MState) :
    Open9.step m =
      (open9Fetch m.memory m.core.rip.toNat).bind fun p =>
        Open.ofResult (Ext9.exec p.1 m.core m.memory p.2) :=
  Silmaril.Proofs.X86.MemEvent.open9_step_eq m

theorem atomic9_step_eq (m : MState) :
    Atomic9.step m =
      (atomic9Fetch m.memory m.core.rip.toNat).bind fun p =>
        Open.ofResult (Atomic9.exec p.1 m.core m.memory p.2) :=
  Silmaril.Proofs.X86.MemEvent.atomic9_step_eq m

/-! ## The SC reading -/

/-- **The SC reading of `Open.step`.** -/
theorem open_step_sc {m m' : MState} (h : Open.step m = some m') :
    ∃ i n, openFetch m.memory m.core.rip.toNat = some (i, n) ∧
      Silmaril.X86.Ext8.exec i m.core m.memory n = .ok m'.core m'.memory ∧
      Local extView (fun mem => Silmaril.X86.Ext8.exec i m.core mem n) (ext8Accesses i m.core n) ∧
      Patched (writeSet (ext8Accesses i m.core n)) m.memory m'.memory m.memory m'.memory :=
  Silmaril.Proofs.X86.MemEvent.open_step_sc h

/-- **The SC reading of `Open9.step`**: an `Open9` step is the fetched instruction's access
list run against one memory. Its executor is local for the access list, and the new memory is
the old one patched on exactly the write set. -/
theorem open9_step_sc {m m' : MState} (h : Open9.step m = some m') :
    ∃ i n, open9Fetch m.memory m.core.rip.toNat = some (i, n) ∧
      Ext9.exec i m.core m.memory n = .ok m'.core m'.memory ∧
      Local extView (fun mem => Ext9.exec i m.core mem n) (ext9Accesses i m.core n) ∧
      Patched (writeSet (ext9Accesses i m.core n)) m.memory m'.memory m.memory m'.memory :=
  Silmaril.Proofs.X86.MemEvent.open9_step_sc h

/-- **The SC reading of `Atomic9.step`.** -/
theorem atomic9_step_sc {m m' : MState} (h : Atomic9.step m = some m') :
    ∃ i n, atomic9Fetch m.memory m.core.rip.toNat = some (i, n) ∧
      Atomic9.exec i m.core m.memory n = .ok m'.core m'.memory ∧
      Local extView (fun mem => Atomic9.exec i m.core mem n) (atomic9Accesses i m.core n) ∧
      Patched (writeSet (atomic9Accesses i m.core n)) m.memory m'.memory m.memory m'.memory :=
  Silmaril.Proofs.X86.MemEvent.atomic9_step_sc h

/-! ## The one-step `Sep` frame rule -/

theorem changesWithin_of_patched {h : Frag} {m m' : MState} {W : Nat → Prop}
    (hp : Patched W m.memory m'.memory m.memory m'.memory)
    (hw : ∀ a, W a → (h (.mem a)).isSome = true) (hc : CoreWithin h m.core m'.core) :
    ChangesWithin h m m' :=
  Silmaril.Proofs.X86.MemEvent.changesWithin_of_patched hp hw hc

/-- **The one-step triple rule** from a footprint. -/
theorem triple_of_step {P Q : SProp}
    (hstep : ∀ m h, Frag.Le h (toFrag m) → P h →
      ∃ m', Open.step m = some m' ∧ ChangesWithin h m m' ∧ Q (Frag.reval h (toFrag m'))) :
    Triple Silmaril.X86.Open.isa P Q :=
  Silmaril.Proofs.X86.MemEvent.triple_of_step hstep

/-- **The instruction-level frame rule for `Sep.Triple`.** The memory part of the frame
obligation of one `Open.step` is only that the precondition's fragment owns the write set of
the fetched instruction's access list. -/
theorem triple_step_of_local {P Q : SProp}
    (hstep : ∀ m h, Frag.Le h (toFrag m) → P h →
      ∃ i n m', openFetch m.memory m.core.rip.toNat = some (i, n) ∧
        Silmaril.X86.Ext8.exec i m.core m.memory n = .ok m'.core m'.memory ∧
        (∀ a, writeSet (ext8Accesses i m.core n) a → (h (.mem a)).isSome = true) ∧
        CoreWithin h m.core m'.core ∧ Q (Frag.reval h (toFrag m'))) :
    Triple Silmaril.X86.Open.isa P Q :=
  Silmaril.Proofs.X86.MemEvent.triple_step_of_local hstep

/-! ## A concrete access list -/

/-- gcc's SEQ_CST fence `lock or qword ptr [rsp], 0` (`f0 48 83 0c 24 00`) has one locked
eight-byte read-modify-write event at `rsp`. -/
theorem lockOr_rsp_zero_events (s : State) (next : Word) :
    (Atomic9.decodeNew [0xf0, 0x48, 0x83, 0x0c, 0x24, 0x00]).map
        (fun p => (atomic9NewAccesses p.1 s next, p.2)) =
      some ([⟨.rmw, (s.read .rsp).toNat, 8, true⟩], 6) :=
  Silmaril.Proofs.X86.MemEvent.lockOr_rsp_zero_events s next

/-- **`Local` is not vacuous about write sets**: an access list claiming a store that
`endbr64` does not do is not local for it. -/
theorem not_local_spurious_store (s : State) :
    ¬ Local extView (fun m => Silmaril.X86.Ext.exec .endbr64 s m 4) [⟨.store, 0, 1, false⟩] :=
  Silmaril.Proofs.X86.MemEvent.not_local_spurious_store s

/-- **Read sets are not vacuous**: `pop rax` with its load dropped is not local. -/
theorem not_local_dropped_load (s : State) (hs : s.read .rsp = 0) :
    ¬ Local extView (fun m => Silmaril.X86.Ext.exec (.pop .rax) s m 1) [] :=
  Silmaril.Proofs.X86.MemEvent.not_local_dropped_load s hs

/-- **`rmw` write sets are exact**: `test qword ptr [rsp], rax` claimed as a read-modify-write
is not local (it succeeds on read-only memory). -/
theorem not_local_spurious_rmw (s : State) (hs : s.read .rsp = 0) :
    ¬ Local extView
      (fun m => Silmaril.X86.Ext.exec (.test .q (.mem ⟨.reg .rsp, none, 0, by simp⟩) .rax) s m 3)
      [⟨.rmw, 0, 8, false⟩] :=
  Silmaril.Proofs.X86.MemEvent.not_local_spurious_rmw s hs

end Silmaril.X86.MemEvent
