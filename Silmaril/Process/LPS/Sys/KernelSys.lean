module

public import Silmaril.Process.LPS.Sys.Kernel
public import Silmaril.Process.LPS.Sys.Time
public import Silmaril.Process.LPS.Arm
public import Silmaril.Process.LPS.MonadExt

/-!
# LPS in Lean: credentials, `setsid`, `uname`, `prctl`, `prlimit64`, groups and scheduling

Translations from LPS (upstream commit `f1006fe8`):

* `Sys/Kernel/Sys.v` (Linux `kernel/sys.c`):
  - `setsid_spec` (157): `EPERM` once a `setsid` has succeeded; otherwise either `EPERM` (an
    untracked environment condition) or success, returning the tid (pinned at its first
    observation, in the envelope `set_tid_address` uses) and recording the success;
  - the credential setters over `IdTriple`: `setid_spec` (`setuid` 146, `setgid` 144) and
    `setresid_spec` (`setresuid` 147, `setresgid` 149), with `setid_errnos`: `ENOMEM`
    always injectable, `EAGAIN` only on a user-id setter that moves the real uid;
  - `prlimit64_spec` (261): only `pid = 0`, `RLIMIT_CORE` and exactly one of the two
    pointers; the first read pins an environment-chosen `soft ≤ hard` pair, a set must keep
    the hard limit, a set before any read is `unmodeled`;
  - `uname_spec` (160): `access_ok` first, then the walk; the first call pins an
    environment-chosen `struct new_utsname` with `sysname = "Linux"` and the architecture's
    `machine`, the other four members free with a NUL at byte 64;
  - `prctl_spec` (167): `PR_CAPBSET_READ` only, `EINVAL` above `CAP_LAST_CAP`, else 1;
  - `getpid`, `gettid` and `get*id` were already translated (`Sys/Kernel`); audited below.
* `Sys/Kernel/Groups.v` (`kernel/groups.c`): `getgroups_spec` (158), the count and the
  index-ordered `EINVAL`s, the writing path `unmodeled`; `setgroups_spec` (159), `EPERM`
  unprivileged and `unmodeled` privileged.
* `Sys/Kernel/Sched/Syscalls.v` (`kernel/sched/syscalls.c`): `sched_getaffinity_spec` (123),
  `EINVAL` for lengths every `nr_cpu_ids ≥ 1` refuses, else `unmodeled`;
  `sched_setscheduler_spec` (119), the argument-only prefix exactly and `SCHED_IDLE` at
  priority 0 on the caller as 0; `sched_yield_spec` (124), 0.

The clocks (`gettimeofday`, `clock_gettime`, `nanosleep`) are in `Sys/Time`; this module
exports the arms of both.

## Audit of the existing arms

`getpidSpec` and `gettidSpec` are LPS's `set_tid_address_spec` (`Sys/Kernel/Sys.v:112,173`),
`getidSpec` is `getid_spec` (`Sys/Kernel/Sys.v:730`) and `getrandomSpec` is `getrandom_spec`
(`Sys/Drivers/Char/Random.v:90`) clause by clause: the flag test on the whole word, the
`rw_bytes_max` bound, the walk, the full small-request delivery, the `[1, buflen]` choice beside
`EINTR` above 256 bytes, and the zero-length `access_ok` with `EINTR` admissible on both sides.

## x86-64

Numbers (`arch/x86/entry/syscalls/syscall_64.tbl`, all `common`): `sched_yield` 24,
`getpid` 39, `uname` 63 (`sys_newuname`, as LPS's 160), `getuid` 102, `getgid` 104, `setuid`
105, `setgid` 106, `geteuid` 107, `getegid` 108, `setsid` 112, `getgroups` 115, `setgroups`
116, `setresuid` 117, `setresgid` 119, `sched_setscheduler` 144, `prctl` 157, `gettid` 186,
`sched_getaffinity` 204, `prlimit64` 302, `getrandom` 318. The x86-64 `SYSCALL_DEFINEx`
wrappers narrow `int`/`pid_t`/`uid_t` arguments with the same `__SC_CAST`, so `uid32`,
`int32`, `pid32` and `sint32` apply unchanged, and `SYSCALL_DEFINE0` reads no register.

x86-64 also has the legacy `getrlimit` (97) and `setrlimit` (160). They are not in the LPS
table, and they are not given arms here: as on riscv64 (where LPS leaves 163/164 unmodeled,
`Sys/Kernel/Sys.v:330`) they enter `do_prlimit` directly, skipping
`check_prlimit_permission` and the LSM hook, so they would need their own argument. They fall
through the dispatcher to `unmodeled`.

The x86-64 forms (`…X86`) differ from LPS in the following, and nowhere else:

* `uname`: `UTS_MACHINE` is `"x86_64"` (`arch/x86/Makefile`), so `utsnameWfX86` pins that
  `machine`; the other members stay quantified exactly as in LPS. x86-64's
  `COMPAT_UTS_MACHINE` (`"i686"`) is the `PER_LINUX32` rewrite, which does not fire for an
  ordinary 64-bit `execve`, as LPS argues for `"riscv32"`;
* `access_ok` is x86-64's (`Uaccess.accessOkbX86`, `USER_PTR_MAX = 2^47 - 4096`) in `uname`,
  `prlimit64`, `sched_setscheduler` and the zero-length arm of `getrandom`;
* `sched_getaffinity`: LPS answers `EINVAL` for a length whose bit count wraps to 0 because
  `nr_cpu_ids ≥ 1`, and states that this is a riscv64 claim: on x86 `xen_smp_count_cpus`
  (`arch/x86/xen/smp_pv.c`) can set `nr_cpu_ids` to 0 (`Sys/Kernel/Sched/Syscalls.v:113`).
  With `nr_cpu_ids = 0` such a length passes both gates, so `schedGetaffinitySpecX86` answers
  `EINVAL` only for the lengths that are not a multiple of 8 (refused by the alignment gate for
  every `nr_cpu_ids`) and declines the wrapping multiples of 8.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-! ## `setsid` (LPS `Sys/Kernel/Sys.v:277`) -/

/-- LPS `Sys/Kernel/Sys.v:277` `setsid_spec`. -/
def setsidSpec : Sys SyscallEffect := do
  let m ← getModel
  if m.setsidSucceeded then errRet EPERM
  else
    Sys.alt (errRet EPERM) do
      let tid ← Sys.choose fun t : Word =>
        (0 < uns t ∧ uns t < PID_MAX_ENVELOPE) ∧
          (match m.tid with
           | none => True
           | some t0 => t = t0)
      modify (·.withTid tid)
      modify (·.withSetsidSucceeded)
      retOnly tid

/-! ## `prlimit64` (LPS `Sys/Kernel/Sys.v:318-598`) -/

/-- LPS `Sys/Kernel/Sys.v:318` `rlim64_soft`. -/
def rlim64Soft (bs : List Byte) : Word := leBytesToWord (bs.take 8)
/-- LPS `Sys/Kernel/Sys.v:319` `rlim64_hard`. -/
def rlim64Hard (bs : List Byte) : Word := leBytesToWord (bs.drop 8)

/-- LPS `Sys/Kernel/Sys.v:326` `rlim64_wf`: 16 bytes and `soft ≤ hard`. -/
def rlim64Wf (bs : List Byte) : Bool :=
  bs.length == 16 && decide (uns (rlim64Soft bs) ≤ uns (rlim64Hard bs))

/-- LPS `Sys/Kernel/Sys.v:557` `prlimit64_spec`, over the architecture's `access_ok`. As in
LPS, the walk is asked before `access_ok` on both pointers. -/
def prlimit64SpecWith (ok : Word → Int → Bool) (pid resource newRlim oldRlim : Word) :
    Sys SyscallEffect :=
  if !wIs0 pid then unmodeled
  else if !(uns resource == RLIMIT_CORE) then unmodeled
  else if wIs0 newRlim && wIs0 oldRlim then unmodeled
  else if !wIs0 newRlim && !wIs0 oldRlim then unmodeled
  else do
    let i ← input
    let m ← getModel
    if wIs0 newRlim then
      match readBytesMap i.wmem oldRlim 16 with
      | none => if !ok oldRlim 16 then errRet EFAULT else unmodeled
      | some _ =>
        match m.rlimitCore with
        | some bs => Sys.pure (mkEffect 0 [(oldRlim, bs)] [])
        | none => do
          let bs ← Sys.choose fun bs : List Byte => rlim64Wf bs = true
          modify (·.withRlimitCore bs)
          Sys.pure (mkEffect 0 [(oldRlim, bs)] [])
    else
      match m.rlimitCore with
      | none => unmodeled
      | some bs0 =>
        match readBytesMap i.mem newRlim 16 with
        | none => if !ok newRlim 16 then errRet EFAULT else unmodeled
        | some nb =>
          recordCopyins [(newRlim, 16)]
            (if uns (rlim64Hard nb) < uns (rlim64Soft nb) then errRet EINVAL
            else if !(rlim64Hard nb == rlim64Hard bs0) then unmodeled
            else do
              modify (·.withRlimitCore nb)
              retOnly 0)

/-- LPS `Sys/Kernel/Sys.v:557` `prlimit64_spec`. -/
def prlimit64Spec (pid resource newRlim oldRlim : Word) : Sys SyscallEffect :=
  prlimit64SpecWith accessOkb pid resource newRlim oldRlim

/-- x86-64 form of LPS `Sys/Kernel/Sys.v:557` `prlimit64_spec`: x86-64 `access_ok`
(`struct rlimit64` and `RLIM_INFINITY` are the same on x86-64). -/
def prlimit64SpecX86 (pid resource newRlim oldRlim : Word) : Sys SyscallEffect :=
  prlimit64SpecWith accessOkbX86 pid resource newRlim oldRlim

/-! ## Credentials (LPS `Sys/Kernel/Sys.v:600-873`) -/

/-- LPS `Sys/Kernel/Sys.v:671` `IdTriple`: real, effective and saved id. -/
structure IdTriple where
  real : Word
  eff : Word
  saved : Word
  deriving DecidableEq, Repr

/-- LPS `Sys/Kernel/Sys.v:677` `cred_uids`. -/
def credUids (c : Creds) : IdTriple := ⟨c.uid, c.euid, c.suid⟩
/-- LPS `Sys/Kernel/Sys.v:679` `cred_gids`. -/
def credGids (c : Creds) : IdTriple := ⟨c.gid, c.egid, c.sgid⟩

/-- LPS `Sys/Kernel/Sys.v:691` `set_cred_uids`: the group ids and the supplementary list
carry over. -/
def setCredUids (t : IdTriple) (c : Creds) : Creds :=
  ⟨t.real, t.eff, t.saved, c.gid, c.egid, c.sgid, c.groups⟩
/-- LPS `Sys/Kernel/Sys.v:694` `set_cred_gids`. -/
def setCredGids (t : IdTriple) (c : Creds) : Creds :=
  ⟨c.uid, c.euid, c.suid, t.real, t.eff, t.saved, c.groups⟩

/-- LPS `Sys/Kernel/Sys.v:756` `setid_errnos`: `ENOMEM` (`prepare_creds`), and `EAGAIN`
(`set_user`, `set_cred_ucounts`) only when the real uid changes. `Run.setidErrnos` is the same
definition, translated for LPS's injected table; `Run` imports the table, so this module cannot
import it, and `Checks.KernelSys` proves the two equal. -/
def setidInjectedErrnos (realUidChanges : Bool) : List Int :=
  if realUidChanges then [ENOMEM, EAGAIN] else [ENOMEM]

/-- LPS `Sys/Kernel/Sys.v:794` `setid_spec` (`setuid`, `setgid`). -/
def setidSpec (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool)
    (v : Word) : Sys SyscallEffect := do
  let m ← getModel
  let c := m.creds
  let t := get c
  if v == ID_MINUS_ONE then errRet EINVAL
  else if c.privileged then
    Sys.alt (do let e ← errnoFrom (setidInjectedErrnos (user && !(v == t.real))); errRet e)
      (do setCreds (put ⟨v, v, v⟩ c); retOnly 0)
  else if v == t.real || v == t.saved then
    Sys.alt (do let e ← errnoFrom (setidInjectedErrnos false); errRet e)
      (do setCreds (put ⟨t.real, v, t.saved⟩ c); retOnly 0)
  else
    Sys.alt (do let e ← errnoFrom (setidInjectedErrnos false); errRet e) (errRet EPERM)

/-- LPS `Sys/Kernel/Sys.v:852` `setresid_spec` (`setresuid`, `setresgid`). `(uid_t)-1`
leaves an id alone; the no-op is total; the permission test precedes `prepare_creds`. -/
def setresidSpec (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool)
    (r e s : Word) : Sys SyscallEffect := do
  let m ← getModel
  let c := m.creds
  let t := get c
  let pick (a cur : Word) : Word := if a == ID_MINUS_ONE then cur else a
  let nr := pick r t.real
  let ne := pick e t.eff
  let ns := pick s t.saved
  if nr == t.real && ne == t.eff && ns == t.saved then retOnly 0
  else
    let isOld (x : Word) : Bool := x == t.real || x == t.eff || x == t.saved
    if !(isOld nr && isOld ne && isOld ns) && !c.privileged then errRet EPERM
    else
      Sys.alt (do let en ← errnoFrom (setidInjectedErrnos (user && !(nr == t.real))); errRet en)
        (do setCreds (put ⟨nr, ne, ns⟩ c); retOnly 0)

/-! ## `uname` (LPS `Sys/Kernel/Sys.v:875-1063`) -/

/-- LPS `Sys/Kernel/Sys.v:883` `uts_field`: member `k` of `struct new_utsname`, 65 bytes. -/
def utsField (k : Nat) (bs : List Byte) : List Byte := (bs.drop (k * 65)).take 65

/-- LPS `Sys/Kernel/Sys.v:886` `uts_nul`. -/
def utsNul : Byte := 0

/-- LPS `Sys/Kernel/Sys.v:893` `uts_literal`: the characters, then NUL to 65 bytes. -/
def utsLiteral (cs : List Int) : List Byte := cs.map zb ++ List.replicate (65 - cs.length) utsNul

/-- LPS `Sys/Kernel/Sys.v:896` `uts_eqb`. -/
def utsEqb (l1 l2 : List Byte) : Bool :=
  l1.length == l2.length && (l1.zip l2).all fun p => p.1 == p.2

/-- LPS `Sys/Kernel/Sys.v:907` `uts_sysname_chars`: `"Linux"`. -/
def utsSysnameChars : List Int := [76, 105, 110, 117, 120]

/-- LPS `Sys/Kernel/Sys.v:967` `utsname_wf`, for the architecture's `UTS_MACHINE`: 390 bytes,
`sysname` and `machine` pinned, a NUL at byte 64 of the other four members. -/
def utsnameWfWith (machine : List Int) (bs : List Byte) : Bool :=
  bs.length == 390
    && utsEqb (utsField 0 bs) (utsLiteral utsSysnameChars)
    && utsEqb (utsField 4 bs) (utsLiteral machine)
    && (utsField 1 bs).getD 64 utsNul == utsNul
    && (utsField 2 bs).getD 64 utsNul == utsNul
    && (utsField 3 bs).getD 64 utsNul == utsNul
    && (utsField 5 bs).getD 64 utsNul == utsNul

/-- LPS `Sys/Kernel/Sys.v:967` `utsname_wf`: `machine = "riscv64"`. -/
def utsnameWf (bs : List Byte) : Bool := utsnameWfWith utsMachineChars bs

/-- x86-64 form of LPS `Sys/Kernel/Sys.v:967` `utsname_wf`: `machine = "x86_64"`. -/
def utsnameWfX86 (bs : List Byte) : Bool := utsnameWfWith utsMachineCharsX86 bs

/-- LPS `Sys/Kernel/Sys.v:1048` `uname_spec`, over the architecture's `access_ok` and
`utsname_wf`. -/
def unameSpecWith (ok : Word → Int → Bool) (wf : List Byte → Bool) (name : Word) :
    Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  if !ok name NEW_UTSNAME_SIZE then errRet EFAULT
  else
    match readBytesMap i.wmem name (zw NEW_UTSNAME_SIZE) with
    | none => unmodeled
    | some _ =>
      match m.utsname with
      | some bs => Sys.pure (mkEffect 0 [(name, bs)] [])
      | none => do
        let bs ← Sys.choose fun bs : List Byte => wf bs = true
        modify (·.withUtsname bs)
        Sys.pure (mkEffect 0 [(name, bs)] [])

/-- LPS `Sys/Kernel/Sys.v:1048` `uname_spec`. -/
def unameSpec (name : Word) : Sys SyscallEffect := unameSpecWith accessOkb utsnameWf name

/-- x86-64 form of LPS `Sys/Kernel/Sys.v:1048` `uname_spec`: `machine = "x86_64"` and x86-64
`access_ok`. -/
def unameSpecX86 (name : Word) : Sys SyscallEffect :=
  unameSpecWith accessOkbX86 utsnameWfX86 name

/-! ## `prctl` (LPS `Sys/Kernel/Sys.v:1065-1207`) -/

/-- LPS `Sys/Kernel/Sys.v:1077` `prctl_modeled_options`. -/
def prctlModeledOptions : List Int := [PR_CAPBSET_READ]

/-- LPS `Sys/Kernel/Sys.v:1204` `prctl_spec`: `PR_CAPBSET_READ` against an unnarrowed bounding
set; `arg2` is compared unsigned on the full register. -/
def prctlSpec (option arg2 : Word) : Sys SyscallEffect :=
  if !(uns option == PR_CAPBSET_READ) then unmodeled
  else if CAP_LAST_CAP < uns arg2 then errRet EINVAL
  else retOnly 1

/-! ## Supplementary groups (LPS `Sys/Kernel/Groups.v`) -/

/-- LPS `Sys/Kernel/Groups.v:121` `getgroups_spec`. -/
def getgroupsSpec (gidsetsize : Word) : Sys SyscallEffect :=
  let n := sint32 gidsetsize
  if n < 0 then errRet EINVAL
  else do
    let m ← getModel
    let ng : Int := m.creds.groups.length
    if NGROUPS_MAX < ng then unmodeled
    else if n = 0 then retOnly (zw ng)
    else if n < ng then errRet EINVAL
    else if ng = 0 then retOnly 0
    else unmodeled

/-- LPS `Sys/Kernel/Groups.v:169` `setgroups_spec`. -/
def setgroupsSpec : Sys SyscallEffect := do
  let m ← getModel
  if m.creds.privileged then unmodeled else errRet EPERM

/-! ## Scheduling (LPS `Sys/Kernel/Sched/Syscalls.v`) -/

/-- LPS `Sys/Kernel/Sched/Syscalls.v:204` `affinity_len_einval_b`: the bit count wraps to 0
(so `len * 8 < nr_cpu_ids` for every `nr_cpu_ids ≥ 1`) or the length is not a multiple
of 8. -/
def affinityLenEinvalB (len : Word) : Bool :=
  let l := uns (abiLow32 len)
  l * 8 % 2 ^ 32 == 0 || !(l % 8 == 0)

/-- LPS `Sys/Kernel/Sched/Syscalls.v:208` `sched_getaffinity_spec`. -/
def schedGetaffinitySpec (len : Word) : Sys SyscallEffect :=
  if affinityLenEinvalB len then errRet EINVAL else unmodeled

/-- x86-64: the lengths `sched_getaffinity` refuses for every `nr_cpu_ids`, including 0
(see the module docstring): those that are not a multiple of 8. -/
def affinityLenEinvalX86B (len : Word) : Bool := !(uns (abiLow32 len) % 8 == 0)

/-- x86-64 form of LPS `Sys/Kernel/Sched/Syscalls.v:208` `sched_getaffinity_spec`: the
wrapping multiples of 8 decline, since x86 does not guarantee `nr_cpu_ids ≥ 1`. -/
def schedGetaffinitySpecX86 (len : Word) : Sys SyscallEffect :=
  if affinityLenEinvalX86B len then errRet EINVAL else unmodeled

/-- LPS `Sys/Kernel/Sched/Syscalls.v:405` `sched_valid_policy_b` (`valid_policy` without
`SCHED_EXT`). -/
def schedValidPolicyB (pol : Int) : Bool :=
  pol == SCHED_NORMAL || pol == SCHED_FIFO || pol == SCHED_RR || pol == SCHED_BATCH
    || pol == SCHED_IDLE || pol == SCHED_DEADLINE

/-- LPS `Sys/Kernel/Sched/Syscalls.v:411` `sched_rt_policy_b`. -/
def schedRtPolicyB (pol : Int) : Bool := pol == SCHED_FIFO || pol == SCHED_RR

/-- LPS `Sys/Kernel/Sched/Syscalls.v:421` `sched_targets_self_b`: `pid` 0, or the pinned
tid. -/
def schedTargetsSelfB (pid : Word) (m : Model) : Bool :=
  wIs0 (pid32 pid) ||
    match m.tid with
    | some tid => pid32 pid == tid
    | none => false

/-- LPS `Sys/Kernel/Sched/Syscalls.v:447` `sched_setscheduler_answer`: `some r` is the
return value, `none` the decline. -/
def schedSetschedulerAnswer (pol prio : Int) : Option Word :=
  if !(zland pol SCHED_RESET_ON_FORK == 0) then none
  else if pol == SCHED_EXT then none
  else if !schedValidPolicyB pol then some (errnoRet EINVAL)
  else if MAX_RT_PRIO - 1 < prio then some (errnoRet EINVAL)
  else if pol == SCHED_DEADLINE then some (errnoRet EINVAL)
  else if Bool.xor (schedRtPolicyB pol) !(prio == 0) then some (errnoRet EINVAL)
  else if pol == SCHED_IDLE then some 0
  else none

/-- LPS `Sys/Kernel/Sched/Syscalls.v:458` `sched_setscheduler_spec`, over the architecture's
`access_ok`. -/
def schedSetschedulerSpecWith (ok : Word → Int → Bool) (pid policy param : Word) :
    Sys SyscallEffect :=
  if sint32 policy < 0 then errRet EINVAL
  else if wIs0 param || decide (sint32 pid < 0) then errRet EINVAL
  else do
    let i ← input
    let m ← getModel
    match readBytesMap i.mem param 4 with
    | none => if !ok param 4 then errRet EFAULT else unmodeled
    | some bs =>
      recordCopyins [(param, 4)]
        (if !schedTargetsSelfB pid m then unmodeled
        else
          match schedSetschedulerAnswer (uns (abiLow32 policy)) (uns (leBytesToWord bs)) with
          | some r => retOnly r
          | none => unmodeled)

/-- LPS `Sys/Kernel/Sched/Syscalls.v:458` `sched_setscheduler_spec`. -/
def schedSetschedulerSpec (pid policy param : Word) : Sys SyscallEffect :=
  schedSetschedulerSpecWith accessOkb pid policy param

/-- x86-64 form of LPS `Sys/Kernel/Sched/Syscalls.v:458` `sched_setscheduler_spec`: x86-64
`access_ok`. -/
def schedSetschedulerSpecX86 (pid policy param : Word) : Sys SyscallEffect :=
  schedSetschedulerSpecWith accessOkbX86 pid policy param

/-- LPS `Sys/Kernel/Sched/Syscalls.v:523` `sched_yield_spec`. -/
def schedYieldSpec : Sys SyscallEffect := retOnly 0

/-! ## `getrandom` on x86-64 (LPS `Sys/Drivers/Char/Random.v:90`) -/

/-- x86-64 form of LPS `Sys/Drivers/Char/Random.v:90` `getrandom_spec`: `getrandomSpec` with
x86-64 `access_ok` in the zero-length arm (the only place it consults `access_ok`). -/
def getrandomSpecX86 (buf buflen flags : Word) : Sys SyscallEffect :=
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
      else if accessOkbX86 buf (uns buflen) then Sys.alt interrupted (retOnly 0)
      else Sys.alt interrupted (errRet EFAULT)

/-! ## Arms -/

/-- The arms of this lane in the LPS (asm-generic) numbering, as LPS
`Sys/SyscallTable.v:78-128` builds them. They are rows of `specTable` (see `Table`); the
`getpid`, `get*id`, `gettid` and `getrandom` arms are `Table.kernelLpsArms`. -/
def kernelSysLpsArms : List SpecArm :=
  [ arm 101 "nanosleep" (fun i => nanosleepSpec (i.arg 0) (i.arg 1)),
    arm 113 "clock_gettime" (fun i => clockGettimeSpec (clockid32 (i.arg 0)) (i.arg 1)),
    arm 119 "sched_setscheduler"
      (fun i => schedSetschedulerSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 123 "sched_getaffinity" (fun i => schedGetaffinitySpec (i.arg 1)),
    arm 124 "sched_yield" (fun _ => schedYieldSpec),
    arm 144 "setgid" (fun i => setidSpec credGids setCredGids false (uid32 (i.arg 0))),
    arm 146 "setuid" (fun i => setidSpec credUids setCredUids true (uid32 (i.arg 0))),
    arm 147 "setresuid" (fun i =>
      setresidSpec credUids setCredUids true (uid32 (i.arg 0)) (uid32 (i.arg 1))
        (uid32 (i.arg 2))),
    arm 149 "setresgid" (fun i =>
      setresidSpec credGids setCredGids false (uid32 (i.arg 0)) (uid32 (i.arg 1))
        (uid32 (i.arg 2))),
    arm 157 "setsid" (fun _ => setsidSpec),
    arm 158 "getgroups" (fun i => getgroupsSpec (i.arg 0)),
    arm 159 "setgroups" (fun _ => setgroupsSpec),
    arm 160 "uname" (fun i => unameSpec (i.arg 0)),
    arm 167 "prctl" (fun i => prctlSpec (int32 (i.arg 0)) (i.arg 1)),
    arm 169 "gettimeofday" (fun i => gettimeofdaySpec (i.arg 0) (i.arg 1)),
    arm 261 "prlimit64" (fun i => prlimit64Spec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)) ]

/-- The arms of this lane in the native x86-64 numbering
(`arch/x86/entry/syscalls/syscall_64.tbl`), with the x86-64 form of each specification
where it differs, including the audited `getpid`, `get*id`, `gettid` and `getrandom`. The
legacy `getrlimit` (97) and `setrlimit` (160) are deliberately absent (`unmodeled`). -/
def kernelSysX86Arms : List SpecArm :=
  [ arm 24 "sched_yield" (fun _ => schedYieldSpec),
    arm 35 "nanosleep" (fun i => nanosleepSpec (i.arg 0) (i.arg 1)),
    arm 39 "getpid" (fun _ => getpidSpec),
    arm 63 "uname" (fun i => unameSpecX86 (i.arg 0)),
    arm 96 "gettimeofday" (fun i => gettimeofdaySpecX86 (i.arg 0) (i.arg 1)),
    arm 102 "getuid" (fun _ => getidSpec (·.uid)),
    arm 104 "getgid" (fun _ => getidSpec (·.gid)),
    arm 105 "setuid" (fun i => setidSpec credUids setCredUids true (uid32 (i.arg 0))),
    arm 106 "setgid" (fun i => setidSpec credGids setCredGids false (uid32 (i.arg 0))),
    arm 107 "geteuid" (fun _ => getidSpec (·.euid)),
    arm 108 "getegid" (fun _ => getidSpec (·.egid)),
    arm 112 "setsid" (fun _ => setsidSpec),
    arm 115 "getgroups" (fun i => getgroupsSpec (i.arg 0)),
    arm 116 "setgroups" (fun _ => setgroupsSpec),
    arm 117 "setresuid" (fun i =>
      setresidSpec credUids setCredUids true (uid32 (i.arg 0)) (uid32 (i.arg 1))
        (uid32 (i.arg 2))),
    arm 119 "setresgid" (fun i =>
      setresidSpec credGids setCredGids false (uid32 (i.arg 0)) (uid32 (i.arg 1))
        (uid32 (i.arg 2))),
    arm 144 "sched_setscheduler"
      (fun i => schedSetschedulerSpecX86 (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 157 "prctl" (fun i => prctlSpec (int32 (i.arg 0)) (i.arg 1)),
    arm 186 "gettid" (fun _ => gettidSpec),
    arm 204 "sched_getaffinity" (fun i => schedGetaffinitySpecX86 (i.arg 1)),
    arm 228 "clock_gettime" (fun i => clockGettimeSpec (clockid32 (i.arg 0)) (i.arg 1)),
    arm 302 "prlimit64" (fun i => prlimit64SpecX86 (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 318 "getrandom" (fun i => getrandomSpecX86 (i.arg 0) (i.arg 1) (i.arg 2)) ]

end Silmaril.Process.LPS
