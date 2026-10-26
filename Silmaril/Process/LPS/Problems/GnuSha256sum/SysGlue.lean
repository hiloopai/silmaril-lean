module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Silent
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Syscalls

/-! # Glue for `sys-total`: system-call steps as `Leads` steps

`sys-total` (`SysTotalOn`) is a `Leads` proof over `GStep`. Its silent parts come from the
segment results of the VC and lift tracks through `Silent.leads_of_run` (any `r11`); this file
supplies the system-call steps between them, for an arbitrary `r11` at each return.

* `leads_call`: at a `syscall` whose request decodes to the call `c` (with its buffer, for a
  `read`), if the kernel can answer and every answer, with every `r11`, continues into `Leads`,
  then `Leads` holds before the call.
* `leads_exit`: at an `exit_group(0)` whose history already satisfies the goal's conditions,
  `Leads` holds (one step to `Done`).
* `leads_seq`: a silent run to a `syscall` followed by such a call step.

Status: everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.X86Sys (XState Core)
open Silmaril.Apps.Sha256sum.Sys (Call Ret KState WorldStep)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

variable {w : Silmaril.Apps.Sha256sum.World} {message : List Byte}

/-- The core after the `syscall` instruction at `g`. -/
abbrev trapped (g : GS) : Core := { g.x.core with rip := g.x.core.rip + 2 }

/-- **A system call as a `Leads` step.** -/
theorem leads_call {Post : GS → List Ev → Prop} {g : GS} {h : List Ev} {c : Call}
    (trap : Trap g.x) (running : g.exited = none) (unfaulted : g.x.faulted = false)
    (ok : Ok message g h)
    (decoded : Silmaril.Apps.Sha256sum.X86Sys.decode (trapped g) g.x.memory = some (.call c))
    (buf : ReadBuf (trapped g) g.x.memory c)
    (answers : ∃ r k', WorldStep w g.k c r k')
    (next : ∀ (r : Ret) (k' : KState) (r11 : Silmaril.X86.Word), WorldStep w g.k c r k' →
      Leads (GStep w) (Ok message) Post
        ⟨Silmaril.Apps.Sha256sum.X86Sys.resume (fun _ => r11) g.x (trapped g) c r, k', none⟩
        (h ++ [.sys c r])) :
    Leads (GStep w) (Ok message) Post g h := by
  have step := step8_trap (core := g.x.core) (memory := g.x.memory) trap
  obtain ⟨r, k', ws⟩ := answers
  refine .step ok ⟨_, _, GStep.call 0 running unfaulted step decoded buf ws⟩ fun e y s => ?_
  cases s with
  | retire _ _ st => rw [step] at st; cases st
  | call r11 _ _ st dec _ ws' =>
    rw [step] at st; cases st
    rw [decoded] at dec; cases dec
    exact next _ _ r11 ws'
  | exit _ _ st dec =>
    rw [step] at st; cases st
    rw [decoded] at dec; cases dec

/-- **`exit_group(0)` as the last step.** At an exit request with status `0` (mod 256), from
a history of allowed calls that read the whole message and wrote exactly the answer, the only
step reaches `Done`. -/
theorem leads_exit {g : GS} {h : List Ev} {n : Nat}
    (trap : Trap g.x) (running : g.exited = none) (unfaulted : g.x.faulted = false)
    (ok : Ok message g h)
    (decoded : Silmaril.Apps.Sha256sum.X86Sys.decode (trapped g) g.x.memory = some (.exit n))
    (zero : n % 256 = 0) (allowed : ∀ e ∈ h, Allowed e) (read : stdinRead h = message)
    (written : out h = expected message) :
    Leads (GStep w) (Ok message) (Done message) g h := by
  have step := step8_trap (core := g.x.core) (memory := g.x.memory) trap
  refine .step ok ⟨_, _, GStep.exit running unfaulted step decoded⟩ fun e y s => ?_
  cases s with
  | retire _ _ st => rw [step] at st; cases st
  | call _ _ _ st dec =>
    rw [step] at st; cases st
    rw [decoded] at dec; cases dec
  | exit _ _ st dec =>
    rw [step] at st; cases st
    rw [decoded] at dec; cases dec
    refine .done ⟨by simp [zero], h, by simp [zero], allowed, read, written⟩

/-- **A silent run, then a step.** A `retStep` run from `g` to a state `t` from which `Leads`
holds gives `Leads` from `g`. -/
theorem leads_seq {Post : GS → List Ev → Prop} {g : GS} {t : XState} {h : List Ev}
    (r : Silmaril.Machine.Execution.Reaches retStep g.x t) (running : g.exited = none)
    (ok : Ok message g h) (then_ : Leads (GStep w) (Ok message) Post { g with x := t } h) :
    Leads (GStep w) (Ok message) Post g h :=
  (leads_of_reaches (Post := fun y hy => Leads (GStep w) (Ok message) Post y hy) r running ok
    then_).trans fun _ _ l => l

end Silmaril.Process.LPS.Problems.GnuSha256sum
