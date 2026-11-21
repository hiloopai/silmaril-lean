module

public import Silmaril.Machine.SqliteMutex.Defs
public import Silmaril.X86.Decompile.Region
public import Silmaril.X86.Ext.Wire.Machine

/-! The pinned SQLite mutex-leave fragment at its link-time virtual addresses.
The cut is a `ret` to the designated caller or retirement of the indirect jump.
The loader and the callee are not run by this probe. -/

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteMutex

open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.Ext.Wire (Platform Outcome step)
open Silmaril.Machine.SqliteMutex (Obs)

def region : Silmaril.X86.Decompile.Region :=
  ⟨0xff70, [0x48, 0x85, 0xff, 0x74, 0x0b, 0xff, 0x25, 0xd5, 0xf6, 0x0f, 0x00,
    0x0f, 0x1f, 0x44, 0x00, 0x00, 0xc3]⟩

def slot : Word := 0x10f650

/-- The caller's return address is already on the stack; the environment
provides the stable `xMutexLeave` pointer when the argument is nonnull.
Handler typing and meaning at that address are separate linking obligations. -/
structure Entry (initial : MState) (caller target : Word) : Prop where
  rip : initial.core.rip = 0xff70
  code : region.LoadedIn initial.memory
  stack : initial.memory.readBytes (initial.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [caller])
  callback : initial.core.read .rdi ≠ 0#64 → target ≠ 0#64 ∧ loadN initial.memory slot 8 = some target

inductive Cut where
  | callerReturn (final : MState)
  | handlerEntry (entry : MState)
  | stopped (reason : Outcome)
  | rejected

/-- Observe the wire machine, without scripting the source's null test. The
budget is a bound on the fragment, not an encoding of machine divergence. -/
def run (platform : Platform) (caller : Word) : Nat → MState → Cut
  | 0, _ => .rejected
  | fuel + 1, initial =>
    match step platform caller initial with
    | .returned final => .callerReturn final
    | .retired next =>
      if initial.core.rip = 0xff75 then .handlerEntry next else run platform caller fuel next
    | other => .stopped other

def observe : Cut → Obs
  | .callerReturn _ => ⟨[], .returned .callerReturn⟩
  | .handlerEntry entry => ⟨[.leave (entry.core.read .rdi)], .returned .handlerEntry⟩
  | .stopped .trapped => ⟨[], .aborted ()⟩
  | .stopped (.undefinedCondition _) => ⟨[], .faulted .undefinedFlag⟩
  | .stopped .divideFault => ⟨[], .faulted .divide⟩
  | .stopped (.dataFault _) => ⟨[], .faulted .data⟩
  | .stopped .fetchFault => ⟨[], .faulted .fetch⟩
  | .stopped .undecodable => ⟨[], .faulted .unsupported⟩
  | _ => ⟨[], .faulted .validation⟩

end Silmaril.Elf.Corpus.SqliteMutex
