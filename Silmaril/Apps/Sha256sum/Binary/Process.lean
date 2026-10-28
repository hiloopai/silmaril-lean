module

public import Silmaril.Apps.Sha256sum.Binary.CallEntry
public import Silmaril.Apps.Sha256sum.X86Sys.Silent
public import Silmaril.Process.CLI.X86Linux.Silent

/-! # The linked SHA compression contract inside process executions

The checked linked callee is reused without executing its proof again. Each
completed Ext return supplies the exact process endpoint, SHA value, System V
register/stack guarantees and memory frame. The segment includes RET and emits
no events; arbitrary surrounding syscalls retain their original R11 policy.

These are call-site contracts, not a proof of the SHA driver or of its launch,
I/O, padding, output or termination. `CallEntry` separately discharges the
code/K-table entry clauses from loaded bytes preserved by the driver.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary

open Silmaril.X86 (Word MState)
open Silmaril.Crypto.X86.Sha256O2
open Silmaril.Process.CLI
open Silmaril.Apps.Sha256sum.X86Sys

/-- Reuse the linked contract on an actual returning execution, including the
last RET in the internal segment. Heap/fault bookkeeping is retained exactly
by `withExtState`; the supplied R11 policy is unrestricted. -/
theorem compress_returns_silent {r11Of : Core → Word} {exit state block rspEntry : Word}
    {s : XState} {final : MState} (running : s.faulted = false)
    (entry : SysVEntry (layout exit) state block rspEntry frameSize (toExtState s))
    (returned : X86.Ext.Returns exit (toExtState s) final) :
    (∃ n, TauRun r11Of (n + 1) s (withExtState s final)) ∧
      Post (layout exit) state block rspEntry frameSize (toExtState s) final :=
  ⟨ext_returns_tauRun running returned,
    compress_contract exit state block rspEntry _ _ entry returned⟩

/-- The existing callee execution theorem provides a nonempty silent segment.
This is local to a valid compression entry, and imposes no progress requirement
on the driver or continuation. -/
theorem compress_silent {r11Of : Core → Word} {exit state block rspEntry : Word}
    {s : XState} (running : s.faulted = false)
    (entry : SysVEntry (layout exit) state block rspEntry frameSize (toExtState s)) :
    ∃ final, X86.Ext.Returns exit (toExtState s) final ∧
      (∃ n, TauRun r11Of (n + 1) s (withExtState s final)) ∧
      Post (layout exit) state block rspEntry frameSize (toExtState s) final := by
  obtain ⟨final, returned⟩ := sha256_compress_O2_live (layout exit) _ _ _ _ entry
  exact ⟨final, returned, compress_returns_silent running entry returned⟩

/-- A driver may establish the caller-owned entry clauses after arbitrary
writes that avoid the loaded code and K table. This recovers the full entry
and immediately applies the linked callee contract and process adapter. -/
theorem compress_silent_of_loaded {r11Of : Core → Word} {exit state block rspEntry : Word}
    {s : XState} (running : s.faulted = false)
    (site : CallSite exit state block rspEntry (toExtState s))
    {loaded : Silmaril.Process.Memory} {inside : Nat → Prop}
    (mapped : Image.image.Mapped loaded)
    (writes : Silmaril.Process.Memory.WritesWithin loaded s.memory inside)
    (codeOutside : ∀ address, (codeRegion (layout 0)).Contains address → ¬ inside address)
    (kTableOutside : ∀ address, (kTableRegion (layout 0)).Contains address → ¬ inside address) :
    ∃ final, X86.Ext.Returns exit (toExtState s) final ∧
      (∃ n, TauRun r11Of (n + 1) s (withExtState s final)) ∧
      Post (layout exit) state block rspEntry frameSize (toExtState s) final :=
  compress_silent running (site.entry_of_loaded mapped writes codeOutside kTableOutside)

/-- Replacing a completed compression segment by its exact result preserves
all calls/replies and the status in every kernel environment. `Post` includes
compression, RSP after RET, the six callee-saved registers and the memory frame;
it does not assert preservation of scratch R11. -/
theorem compress_exec_iff {r11Of : Core → Word} {exit state block rspEntry : Word}
    {s : XState} {final : MState} (running : s.faulted = false)
    (entry : SysVEntry (layout exit) state block rspEntry frameSize (toExtState s))
    (returned : X86.Ext.Returns exit (toExtState s) final)
    {E : Sys.Env} {k : Sys.KState} {events : List Sys.Event} {status : Nat} :
    Post (layout exit) state block rspEntry frameSize (toExtState s) final ∧
      (Sys.Exec (x86Machine r11Of) E s k events status ↔
        Sys.Exec (x86Machine r11Of) E (withExtState s final) k events status) :=
  ⟨compress_contract exit state block rspEntry _ _ entry returned,
    exec_iff_of_ext_returns running returned⟩

/-- Eliminate the internal callee from a completed process execution. The
continuation starts from the exact certified core/memory with the same kernel,
event trace and exit status. No global liveness assumption is needed. -/
theorem compress_exec_continuation {r11Of : Core → Word} {exit state block rspEntry : Word}
    {s : XState} (running : s.faulted = false)
    (entry : SysVEntry (layout exit) state block rspEntry frameSize (toExtState s))
    {E : Sys.Env} {k : Sys.KState} {events : List Sys.Event} {status : Nat}
    (execution : Sys.Exec (x86Machine r11Of) E s k events status) :
    ∃ final, X86.Ext.Returns exit (toExtState s) final ∧
      Post (layout exit) state block rspEntry frameSize (toExtState s) final ∧
      Sys.Exec (x86Machine r11Of) E (withExtState s final) k events status := by
  obtain ⟨final, returned, _, post⟩ := compress_silent (r11Of := r11Of) running entry
  exact ⟨final, returned, post, (exec_iff_of_ext_returns running returned).mp execution⟩

/-- The same linked compression return is silent in the generic CLI model,
with an exact environment memory update through the chosen lawful lens. -/
theorem compress_cli_returns {E : Silmaril.Process.CLI.Env} (lens : E.MemoryLens)
    {exit state block rspEntry : Word} {core : X86.State} {s : E.State} {final : MState}
    (running : E.exited s = none)
    (entry : SysVEntry (layout exit) state block rspEntry frameSize ⟨core, E.memory s⟩)
    (returned : X86.Ext.Returns exit ⟨core, E.memory s⟩ final) :
    Proc.Runs X86Linux.isa E ⟨core, s⟩ [] ⟨final.core, E.withMemory s final.memory⟩ ∧
      Post (layout exit) state block rspEntry frameSize ⟨core, E.memory s⟩ final :=
  ⟨X86Linux.runs_of_ext_returns lens running rfl returned,
    compress_contract exit state block rspEntry _ _ entry returned⟩

/-- An arbitrary CLI continuation retains its observable trace after the linked
compression call. A RET remains internal even if the continuation later faults. -/
theorem compress_cli_continue {E : Silmaril.Process.CLI.Env} (lens : E.MemoryLens)
    {exit state block rspEntry : Word} {core : X86.State} {s : E.State} {final : MState}
    {target : PState X86Linux.isa E} {events : List Silmaril.Process.Syscall.Event}
    (running : E.exited s = none)
    (entry : SysVEntry (layout exit) state block rspEntry frameSize ⟨core, E.memory s⟩)
    (returned : X86.Ext.Returns exit ⟨core, E.memory s⟩ final)
    (continuation : Proc.Runs X86Linux.isa E
      ⟨final.core, E.withMemory s final.memory⟩ events target) :
    Proc.Runs X86Linux.isa E ⟨core, s⟩ events target ∧
      Post (layout exit) state block rspEntry frameSize ⟨core, E.memory s⟩ final := by
  obtain ⟨segment, post⟩ := compress_cli_returns lens running entry returned
  exact ⟨segment.append continuation, post⟩

end Silmaril.Apps.Sha256sum.Binary
