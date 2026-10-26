module

public import Silmaril.Process.LPS.State

/-!
# LPS in Lean: the rest of `State.v`'s shared helpers

`State.lean` translates every record and inductive of LPS `State.v` with all its fields and
constructors (`SyscallInput`, `MemCopy`, `SyscallEffect`, `SockState`, `FdEntry`, `VmMaps`,
`FdState`, `VmState`, `IoState`, `FsState`, `Creds`, `ProcState`, `LimState`, `TimeState`,
`Model`, `Event`, `ProcInput`; `PeerAddr` is in `Stream`; `cstr_result`, `iov_import` and
`iov_entry` are in `Uaccess`), and the helpers the first translated arms needed. This module
adds the helpers of `State.v` that the remaining syscall families share:

* the `Model` accessors and setters not yet translated (`m_conn_ix`, `m_sigmask`,
  `m_utsname`, `m_statpins`, `m_rlimit_core`, `m_nofile`, `m_clock`, `with_rlimit_core`,
  `with_utsname`, `with_statpin`, `with_setsid_succeeded`, `with_sigaltstack_installed`,
  `with_sigabrt_pending`, `with_accepted`, …);
* descriptor and pipe helpers (`alloc_fd2`, `pipe_new_id`, `le32_bytes`, `pipe_fd_bytes`);
* VM-ledger helpers (`mkVmMaps`, `vm_live_bytes`, `page_base`, `access_pages`,
  `vm_backed_bytes`, `vm_resize_backing`);
* `mkProcInput`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Fs (Path FileSystem)

namespace Model

variable (m : Model)

/-- LPS `State.v:3450` `m_conn_ix`: the number of connections handed over so far. -/
def connIx : Word := m.io.connIx
/-- LPS `State.v:3454` `m_setsid_succeeded`. -/
def setsidSucceeded : Bool := m.proc.setsidSucceeded
/-- LPS `State.v:3457` `m_sigaltstack_installed`. -/
def sigaltstackInstalled : Bool := m.proc.sigaltstackInstalled
/-- LPS `State.v:3459` `m_sigmask`. -/
def sigmask : Word := m.proc.sigmask
/-- LPS `State.v:3470` `m_utsname`. -/
def utsname : Option (List Byte) := m.proc.utsname
/-- LPS `State.v:3472` `m_statpins`. -/
def statpins : List (Path × List Byte) := m.proc.statpins
/-- LPS `State.v:3474` `m_rlimit_core`. -/
def rlimitCore : Option (List Byte) := m.lim.core
/-- LPS `State.v:3475` `m_nofile`. -/
def nofile : Word := m.lim.nofile
/-- LPS `State.v:3476` `m_clock`: `CLOCK_MONOTONIC`, in nanoseconds. -/
def clock : Word := m.time.clock

/-- LPS `State.v:3623` `with_rlimit_core`: pin `RLIMIT_CORE`. -/
def withRlimitCore (bs : List Byte) : Model := { m with lim.core := some bs }
/-- LPS `State.v:3636` `with_utsname`: pin the `uname` answer. -/
def withUtsname (bs : List Byte) : Model := { m with proc.utsname := some bs }
/-- LPS `State.v:3671` `with_statpin`: pin a path's stable `struct stat` members. -/
def withStatpin (p : Path) (bs : List Byte) : Model :=
  { m with proc.statpins := (p, bs) :: m.proc.statpins }
/-- LPS `State.v:3720` `with_setsid_succeeded`. -/
def withSetsidSucceeded : Model := { m with proc.setsidSucceeded := true }
/-- LPS `State.v:3793` `with_sigaltstack_installed`. -/
def withSigaltstackInstalled : Model := { m with proc.sigaltstackInstalled := true }
/-- LPS `State.v:3817` `with_sigabrt_pending`. -/
def withSigabrtPending : Model := { m with proc.sigabrtPending := true }
/-- LPS `State.v:3890` `with_accepted`: the new table, the queue advanced past the
connection taken, and one more connection handed over. -/
def withAccepted (fds : List (Word × FdEntry)) : Model :=
  { m with fd.table := fds, io.net := nqRest m.io.net, io.connIx := m.io.connIx + 1 }

end Model

/-- LPS `State.v:3649` `statpin_lookup`: first match wins. -/
def statpinLookup : List (Path × List Byte) → Path → Option (List Byte)
  | [], _ => none
  | (q, bs) :: rest, p => if Fs.pathEqb q p then some bs else statpinLookup rest p

/-- LPS `State.v:3862` `killed_is_halted`. -/
theorem killed_is_halted (sig : Word) (m : Model) :
    (m.withKilled sig).halted = some sig ∧ (m.withKilled sig).killedBy = some sig :=
  ⟨rfl, rfl⟩

/-- LPS `State.v:3874` `m_killed_of_m_halted_none`. -/
theorem killedBy_of_halted_none (m : Model) (h : m.halted = none) : m.killedBy = none := by
  unfold Model.killedBy
  unfold Model.halted at h
  split <;> simp_all

/-- LPS `State.v:3964` `alloc_fd2`: the lowest free descriptor above `alloc_fd`. -/
def allocFd2 (fds : List (Word × FdEntry)) : Word := allocFdAux fds (allocFd fds + 1) 4096

/-- LPS `State.v:4110` `pipe_new_id`: the number of pipes created so far. -/
def pipeNewId (ps : List (Word × PipeBuf)) : Word := zw ps.length

/-- LPS `State.v:4248` `le32_bytes`: the four little-endian bytes of an `int`. -/
def le32Bytes (v : Word) : List Byte :=
  let z := uns v
  [zb z, zb (z >>> 8), zb (z >>> 16), zb (z >>> 24)]

/-- LPS `State.v:4259` `pipe_fd_bytes`: `int fildes[2]`, read end then write end. -/
def pipeFdBytes (fdr fdw : Word) : List Byte := le32Bytes fdr ++ le32Bytes fdw

/-- LPS `State.v:2798` `mkVmMaps`: a ledger with no `PROT_NONE` ranges, mmap base zero, and
the initial stack pointer at the bottom of the SP window (`sp_window_lo`), so its `alloc_top`
is the smallest any admissible run has. -/
def mkVmMaps (reserved maps : List (Word × Word)) (startBrk brk : Word) (limit : Int) :
    VmMaps := ⟨reserved, maps, [], startBrk, brk, limit, 0, zw spWindowLo⟩

/-- LPS `State.v:2857` `vm_live_bytes`. -/
def vmLiveBytes (h : VmMaps) : Int := liveBytes h.maps

/-- LPS `State.v:4533` `page_base`. -/
def pageBase (a : Word) : Word := pageBaseOf (uns a)

/-- LPS `State.v:4557` `access_pages`: the pages `[a, a+n)` touches. -/
def accessPages (a : Word) (n : Nat) : List Word := accessPagesAcc (uns a) n []

/-- LPS `State.v:4616` `vm_backed_bytes`: the readable mappings' size, lazy or not. -/
def vmBackedBytes (h : VmMaps) : Int := liveBytes (vmBackedMaps h)

/-- LPS `State.v:4765` `page_in_half_open`. -/
def pageInHalfOpen (lo hi : Int) (p : Word) : Bool := decide (lo ≤ uns p) && decide (uns p < hi)

/-- LPS `State.v:4768` `move_page_base`. -/
def movePageBase (old dst p : Word) : Word := zw (uns dst + (uns p - uns old))

/-- LPS `State.v:4771` `vm_resize_backing`: move or resize a mapping's lazy backing; the
materialized pages keep their offset, pages cut by a shrink are released, and a grown lazy
tail starts unmaterialized. -/
def vmResizeBacking (sourceLazy : Bool) (old oldN dst newN : Word) (m : Model) : Model :=
  let oldLo := uns old
  let oldHi := oldLo + uns oldN
  let dstLo := uns dst
  let dstHi := dstLo + uns newN
  let keptLazy := mapsSubtract (mapsSubtract m.vmLazy oldLo oldHi) dstLo dstHi
  let keptPages :=
    (m.vmMaterialized.filter (pageOutsideRange oldLo oldHi)).filter
      (pageOutsideRange dstLo dstHi)
  let movedPages :=
    if sourceLazy then
      (m.vmMaterialized.filter fun p =>
          pageInHalfOpen oldLo oldHi p && decide (uns p - oldLo < uns newN)).map
        (movePageBase old dst)
    else []
  m.withVmBacking (if sourceLazy then lazyInterior dst newN ++ keptLazy else keptLazy)
    (movedPages ++ keptPages)

/-- LPS `State.v:5302` `mkProcInput`: an input with the default `/dev/urandom` stream and an
empty `/tmp`. -/
def mkProcInput (argv envp : List (List Byte)) (imageFs : FileSystem) (stdin : InputStream)
    (uid gid : Word) (groups : List Word) (net : NetQueue) (nofile sigmask hwcap : Word)
    (abortTerminal : Bool) (vaSize : VaSize) : ProcInput :=
  ⟨argv, envp, imageFs, stdin, uid, gid, groups, net, nofile, sigmask, hwcap, abortTerminal,
    vaSize, InputStream.defaultUrandom, []⟩

end Silmaril.Process.LPS
