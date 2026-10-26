module

public import Silmaril.Process.LPS.Syscall

/-!
# LPS in Lean: exit, identities, `close` and `getrandom`

Translations from LPS (upstream commit `f1006fe8`):

* `Sys/Kernel/Exit.v`: `exit_spec` (numbers 93 and 94) and `wait4_spec`;
* `Sys/Kernel/Fork.v`: `set_tid_address_spec`, which `getpid` and `gettid` share
  (`Sys/Kernel/Sys.v:112,173`): the thread id is pinned at its first observation;
* `Sys/Kernel/Sys.v`: `getid_spec` (`getuid`, `geteuid`, `getgid`, `getegid`);
* `Sys/Fs/Open.v`: `close_spec`;
* `Sys/Drivers/Char/Random.v`: `getrandom_spec`, whose bytes are a free choice at each call,
  and which may be refused with `EINTR` without cause on requests over 256 bytes.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- LPS `Sys/Kernel/Exit.v:22` `exit_spec`: record the low eight bits of the status. -/
def exitSpec (code : Word) : Sys SyscallEffect := do
  modify (·.withHalted (code &&& 255))
  retOnly 0

/-- LPS `Sys/Kernel/Exit.v:33` `WAIT_ANY32`. -/
def WAIT_ANY32 : Int := 2 ^ 32 - 1
/-- LPS `Sys/Uapi.v:837` `WNOHANG`. -/
def WNOHANG : Int := 1

/-- LPS `Sys/Kernel/Exit.v:244` `wait4_spec`: only `wait4(-1, _, WNOHANG, NULL)` without
children is modelled. -/
def wait4Spec (upid _statAddr options rusage : Word) : Sys SyscallEffect :=
  if uns upid ≠ WAIT_ANY32 then unmodeled
  else if uns options ≠ WNOHANG then unmodeled
  else if !wIs0 rusage then unmodeled
  else do
    let m ← getModel
    if m.hasChildren then unmodeled else errRet ECHILD

/-- LPS `Sys/Kernel/Fork.v:72` `PID_MAX_ENVELOPE`. -/
def PID_MAX_ENVELOPE : Int := 2 ^ 22

/-- LPS `Sys/Kernel/Fork.v:123` `set_tid_address_spec`: the thread id, chosen by the
environment at its first observation and fixed thereafter. -/
def setTidAddressSpec : Sys SyscallEffect := do
  let m ← getModel
  match m.tid with
  | some tid => retOnly tid
  | none => do
    let tid ← Sys.choose fun tid : Word => 0 < uns tid ∧ uns tid < PID_MAX_ENVELOPE
    modify (·.withTid tid)
    retOnly tid

/-- LPS `Sys/Kernel/Sys.v:112` `getpid_spec`. -/
def getpidSpec : Sys SyscallEffect := setTidAddressSpec
/-- LPS `Sys/Kernel/Sys.v:173` `gettid_spec`. -/
def gettidSpec : Sys SyscallEffect := setTidAddressSpec

/-- LPS `Sys/Kernel/Sys.v:730` `getid_spec`. -/
def getidSpec (sel : Creds → Word) : Sys SyscallEffect := do
  let m ← getModel
  retOnly (sel m.creds)

/-- LPS `Sys/Fs/Open.v:1387` `close_spec`. -/
def closeSpec (fd : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some _ => do
    modify (·.withFds (fdRemove m.fds fd))
    retOnly 0

/-- LPS `Sys/Drivers/Char/Random.v:26` `getrandom_errnos`. -/
def getrandomErrnos : List Int := [EINTR]
/-- LPS `Sys/Drivers/Char/Random.v:51` `getrandom_small_max`. -/
def getrandomSmallMax : Int := 256

/-- LPS `Sys/Drivers/Char/Random.v:90` `getrandom_spec`. -/
def getrandomSpec (buf buflen flags : Word) : Sys SyscallEffect :=
  if !(uns flags == 0 || uns flags == GRND_NONBLOCK) then unmodeled
  else if !modeledRwCount buflen then unmodeled
  else do
    let i ← input
    match readBytesMap i.wmem buf buflen with
    | none => unmodeled
    | some _ =>
      let interrupted : Sys SyscallEffect := do
        let e ← errnoFrom getrandomErrnos
        errRet e
      if !wIs0 buflen then
        if uns buflen ≤ getrandomSmallMax then do
          let bs ← Sys.choose fun bs : List Byte => (bs.length : Int) = uns buflen
          Sys.pure (mkEffect (lenWord bs) [(buf, bs)] [])
        else
          Sys.alt interrupted do
            let bs ← Sys.choose fun bs : List Byte =>
              1 ≤ bs.length ∧ (bs.length : Int) ≤ uns buflen
            Sys.pure (mkEffect (lenWord bs) [(buf, bs)] [])
      else if accessOkb buf (uns buflen) then Sys.alt interrupted (retOnly 0)
      else Sys.alt interrupted (errRet EFAULT)

end Silmaril.Process.LPS
