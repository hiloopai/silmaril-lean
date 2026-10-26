module

public import Silmaril.Process.LPS.Run

/-!
# LPS in Lean: the memory-management refusal and budget dispatch at x86-64 numbers

`Run.lean` translates LPS `Run.v` over the asm-generic numbering: `refusalB` special-cases
`brk` at 214, `injectedTable` registers the alloc family at 214/216/222/226, and
`allocBudgetRefusedB` (LPS `Run.v:1451`, `alloc_mark_sysnos = [214; 216; 222; 226]`) dispatches
the budget marks there. Under x86-64 numbering (`arch/x86/entry/syscalls/syscall_64.tbl`)
those numbers are not memory-management calls (214 is `epoll_ctl_old`, 216 `remap_file_pages`,
222 `timer_create`, 226 `timer_delete`), while `brk`, `mremap`, `mmap` and `mprotect` are
12, 25, 9 and 10.

This module gives the x86-64 counterparts of the alloc-family parts of that dispatch, keyed on
the native numbers and calling the same marks and the same injected errnos:

* `mmSysnoX86ToLps`: the x86-64 → asm-generic map of the six memory-management calls;
* `allocMarkSysnosX86` and `allocBudgetRefusedBX86`: `alloc_mark_sysnos` and
  `alloc_budget_refused_b` at x86-64 numbers;
* `mmInjectedTableX86`: the alloc-family rows of `injected_table` at x86-64 numbers;
* `mmRefusalBX86`: `refusal_b` restricted to those rows, with `brk`'s old-break refusal at 12.

Each is proved equal to its LPS counterpart under the renumbering (`*_renumber` lemmas), and
the LPS pins `alloc_family_dispatched` and `alloc_budget_refused_b_outside` are restated for
the x86-64 list. `NativeX86.allocBudgetRefusedBX86_eq` (`NativeX86Budget.lean`) proves
`allocBudgetRefusedBX86` equal, on every input, to `NativeX86.allocBudgetRefusedB`, the
classifier that renumbers through the native table and that `NativeX86.BudgetRefusedAt`
threads through the run predicates; so there is one x86-64 budget dispatch, stated twice.
The rows of the other families (fs, fd, net, cred, intr) are not joined into a full x86-64
`injectedTable`, and `spuriousRefusalCfg` has no x86-64 counterpart yet.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- The x86-64 numbers of the memory-management calls, mapped to their asm-generic (LPS)
numbers: `mmap` 9 ↦ 222, `mprotect` 10 ↦ 226, `munmap` 11 ↦ 215, `brk` 12 ↦ 214,
`mremap` 25 ↦ 216, `madvise` 28 ↦ 233 (`arch/x86/entry/syscalls/syscall_64.tbl`,
LPS `Sys/SyscallTable.v:119-125`). -/
def mmSysnoX86ToLps : Nat → Option Nat
  | 9 => some 222
  | 10 => some 226
  | 11 => some 215
  | 12 => some 214
  | 25 => some 216
  | 28 => some 233
  | _ => none

/-- LPS `Run.v:1449` `alloc_mark_sysnos` at x86-64 numbers: `brk` 12, `mremap` 25,
`mmap` 9, `mprotect` 10. -/
def allocMarkSysnosX86 : List Nat := [12, 25, 9, 10]

/-- LPS `Run.v:1451` `alloc_budget_refused_b` at x86-64 numbers: the budget marks of `brk`
(12), `mremap` (25), `mmap` (9) and `mprotect` (10), on the same arguments. -/
def allocBudgetRefusedBX86 (i : SyscallInput) (m : Model) : Bool :=
  let no := i.sysno.toNat
  if no = 12 then brkBudgetRefusedB m (i.arg 0)
  else if no = 25 then mremapBudgetRefusedB (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3) m
  else if no = 9 then
    mmapBudgetRefusedB (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5) m
  else if no = 10 then mprotectBudgetRefusedB (i.arg 0) (i.arg 1) (i.arg 2) m
  else false

/-- The alloc-family rows of LPS `Run.v:1358` `injected_table` at x86-64 numbers
(`Sys/Mm/Mmap.v:645`, `Sys/Mm/Mremap.v:115`, `Sys/Mm/Mprotect.v:78`): `brk` (12, no errno:
its refusal is the old break), `mremap` (25), `mmap` (9), `mprotect` (10). -/
def mmInjectedTableX86 : List InjectedArm :=
  [⟨12, .alloc, []⟩, ⟨25, .alloc, [ENOMEM]⟩, ⟨9, .alloc, mmapErrnos⟩, ⟨10, .alloc, [ENOMEM]⟩]

/-- LPS `Run.v:1394` `injected_arm`, over the x86-64 alloc-family rows. -/
def mmInjectedArmX86 (no : Nat) : Option InjectedArm := mmInjectedTableX86.find? (·.no = no)

/-- LPS `Run.v:1418` `refusal_b` for the x86-64 memory-management calls: `brk` (12) refuses by
answering the old break, the other alloc rows by one of their errnos. -/
def mmRefusalBX86 (i : SyscallInput) (m : Model) (ret : Word) : Bool :=
  let no := i.sysno.toNat
  if no = 12 then brkRefusalB m (i.arg 0) ret
  else match mmInjectedArmX86 no with
    | some a => retInErrnos a.errnos ret
    | none => false

/-! ## Pins (LPS `Run.v` `alloc_family_dispatched`, `alloc_budget_refused_b_outside`) -/

/-- Every alloc-family row of `mmInjectedTableX86` is dispatched by `allocBudgetRefusedBX86`. -/
theorem mmInjectedX86_alloc_dispatched :
    ∀ a ∈ mmInjectedTableX86, a.family = .alloc → a.no ∈ allocMarkSysnosX86 := by
  decide

/-- `allocBudgetRefusedBX86` is `false` off `allocMarkSysnosX86`. -/
theorem allocBudgetRefusedBX86_outside (i : SyscallInput) (m : Model)
    (h : i.sysno.toNat ∉ allocMarkSysnosX86) : allocBudgetRefusedBX86 i m = false := by
  simp only [allocMarkSysnosX86, List.mem_cons, List.not_mem_nil, not_or] at h
  obtain ⟨h12, h25, h9, h10, -⟩ := h
  simp [allocBudgetRefusedBX86, h12, h25, h9, h10]

/-- The alloc marks are exactly at the numbers the renumbering sends to LPS's alloc marks. -/
theorem allocMarkSysnosX86_renumber :
    allocMarkSysnosX86.map mmSysnoX86ToLps = [some 214, some 216, some 222, some 226] := rfl

/-! ## Agreement with the asm-generic dispatch under the renumbering -/

/-- The x86-64 budget dispatch is LPS's at the renumbered call: for every x86-64
memory-management number `x` with LPS number `n`, `allocBudgetRefusedBX86` at `x` is
`allocBudgetRefusedB` at `n` on the same arguments and model. -/
theorem allocBudgetRefusedBX86_renumber (i : SyscallInput) (m : Model) (x n : Nat)
    (hx : mmSysnoX86ToLps x = some n) :
    allocBudgetRefusedBX86 { i with sysno := BitVec.ofNat 64 x } m =
      allocBudgetRefusedB { i with sysno := BitVec.ofNat 64 n } m := by
  unfold mmSysnoX86ToLps at hx
  split at hx <;> cases hx <;> simp [allocBudgetRefusedBX86, allocBudgetRefusedB, SyscallInput.arg]

/-- The x86-64 alloc-family refusal reading is LPS's `refusalB` at the renumbered call. -/
theorem mmRefusalBX86_renumber (i : SyscallInput) (m : Model) (ret : Word) (x n : Nat)
    (hx : mmSysnoX86ToLps x = some n) (ha : n ∈ [214, 216, 222, 226]) :
    mmRefusalBX86 { i with sysno := BitVec.ofNat 64 x } m ret =
      refusalB { i with sysno := BitVec.ofNat 64 n } m ret := by
  unfold mmSysnoX86ToLps at hx
  split at hx <;> cases hx <;> simp at ha <;> rfl

/-- The x86-64 alloc rows carry the family and errnos of the LPS rows they renumber. -/
theorem mmInjectedTableX86_renumber :
    mmInjectedTableX86.map (fun a =>
        ((mmSysnoX86ToLps a.no).bind injectedArm).map fun b => (b.family, b.errnos)) =
      mmInjectedTableX86.map (fun a => some (a.family, a.errnos)) := by
  decide

end Silmaril.Process.LPS
