module

public import Silmaril.Process.LPS.Table

/-!
# LPS in Lean: the families' arms at the native x86-64 numbers

Each family module (`Silmaril.Process.LPS.Sys.*`) exports, next to its LPS (asm-generic) arms,
a `…X86Arms` list: the same specifications at the native x86-64 numbers
(`arch/x86/entry/syscalls/syscall_64.tbl`), with the x86-64 form of a specification where a
structure layout, an argument order or `access_ok` differs, plus the x86-64-only legacy entry
points (`open`, `creat`, `access`, `dup2`, `stat`, `lstat`, `getdents`, `unlink`, `rmdir`,
`readlink`, `pipe`, `poll`, `select`, `epoll_create`, `epoll_wait`, `eventfd`, `fork`,
`vfork`).

`familyX86Arms` collects them for the owner of the native x86-64 table
(`Silmaril.Process.LPS.NativeX86`) and its ABI-review gate. This module does not change that
table or its gate.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- Every family's arms at the native x86-64 numbers. -/
def familyX86Arms : List SpecArm :=
  fsIoX86Arms ++ fsMetaX86Arms ++ fsCtlX86Arms ++ fdEventsX86Arms ++ mmX86Arms ++
    exitX86Arms ++ forkX86Arms ++ kernelSysX86Arms ++ signalX86Arms ++ futexX86Arms ++
    socketX86Arms

/-- No x86-64 number is exported by two families (or twice by one). -/
theorem familyX86Arms_nodup : (armNumbers familyX86Arms).Nodup := by decide +kernel

/-- The number of exported x86-64 arms. -/
theorem familyX86Arms_length : familyX86Arms.length = 108 := by decide +kernel

/-- No exported x86-64 arm is a `pendingArm` placeholder. This holds by construction (`arm`
always sets `.translated`); it is not evidence that an arm translates its LPS specification,
which rests on the per-arm definitions, their renumbering lemmas and the family checks. -/
theorem familyX86Arms_all_translated :
    familyX86Arms.all (·.status == .translated) = true := by decide +kernel

end Silmaril.Process.LPS
