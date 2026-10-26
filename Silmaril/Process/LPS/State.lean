module

public import Silmaril.Process.LPS.Fs
public import Silmaril.Process.LPS.Stream
public import Silmaril.Process.LPS.Architecture

/-!
# LPS in Lean: the process state

Translation of LPS `State.v` (upstream commit `f1006fe8`): the syscall input and effect, the
user-memory readers, file descriptors, sockets and pipes, the virtual-memory ledger with its
lazy backing and budget, the seven sub-states of `Model`, observable events, the process
input `ProcInput` and the initial model `init_model`.

Each `with_*` setter of LPS is a Lean structure update; the setters are kept, under the same
names, because the syscall specifications use them.

What is left out here, and why:
* the chunked readers `read_bytes_chunks`/`readable_bytes_chunks` are kernel-performance
  devices; LPS proves them equal to the plain readers (`read_bytes_map_eq`,
  `readable_bytes_eq`), and the plain readers are what is translated;
* C-string, `iovec` and `struct` readers (`read_cstr`, `read_iovecs`, …) serve arms that are
  not yet translated (see `Silmaril.Process.LPS.Table`).
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Fs (Path FileSystem)

/-! ## Syscall input and effect -/

/-- LPS `State.v:562` `SyscallInput`: the syscall number, the six argument registers, the
readable view and the writable view of user memory at the trap. -/
structure SyscallInput where
  sysno : Word
  args : List Word
  mem : Word → Option Byte
  wmem : Word → Option Byte

/-- LPS `State.v:585` `in_arg`. -/
def SyscallInput.arg (i : SyscallInput) (k : Nat) : Word := i.args.getD k 0

/-- LPS `State.v:591` `MemCopy`. -/
structure MemCopy where
  src : Word
  dst : Word
  len : Word
  deriving DecidableEq, Repr

/-- LPS `State.v:627` `SyscallEffect`: the return value and the declared memory effects.
A syscall can change only the memory it declares (framing by construction). -/
structure SyscallEffect where
  ret : Word
  writes : List (Word × List Byte)
  zeros : List (Word × Word)
  unmaps : List (Word × Word) := []
  copies : List MemCopy := []
  copyins : List (Word × Nat) := []
  deriving DecidableEq, Repr

/-- LPS `State.v:637` `mkEffect`. -/
def mkEffect (r : Word) (ws : List (Word × List Byte)) (zs : List (Word × Word)) :
    SyscallEffect := { ret := r, writes := ws, zeros := zs }

/-- LPS `State.v:639` `with_copyins`. -/
def SyscallEffect.withCopyins (reads : List (Word × Nat)) (eff : SyscallEffect) :
    SyscallEffect := { eff with copyins := reads }

/-! ## Reading user memory -/

/-- LPS `State.v:652` `read_bytes_aux`: `k` consecutive bytes, all present. -/
def readBytesAux (mp : Word → Option Byte) (a : Word) : Nat → Option (List Byte)
  | 0 => some []
  | k + 1 =>
    match mp a with
    | none => none
    | some b => (readBytesAux mp (a + 1) k).map (b :: ·)

/-- LPS `State.v:706` `read_bytes_map` (equal to `read_bytes_aux` by LPS `read_bytes_map_eq`). -/
def readBytesMap (mp : Word → Option Byte) (a len : Word) : Option (List Byte) :=
  readBytesAux mp a len.toNat

/-- LPS `State.v:842` `readable_bytes_aux`: the longest present prefix, at most `k` bytes. -/
def readableBytesAux (mp : Word → Option Byte) (a : Word) : Nat → List Byte
  | 0 => []
  | k + 1 =>
    match mp a with
    | none => []
    | some b => b :: readableBytesAux mp (a + 1) k

/-- LPS `State.v:894` `readable_bytes` (equal to `readable_bytes_aux` by LPS
`readable_bytes_eq`). -/
def readableBytes (mp : Word → Option Byte) (a len : Word) : List Byte :=
  readableBytesAux mp a len.toNat

/-- LPS `State.v:1083` `read_u64`. -/
def readU64 (mp : Word → Option Byte) (a : Word) : Option Word :=
  (readBytesMap mp a 8).map leBytesToWord

/-- LPS `State.v:1132` `MAX_RW_COUNT`. -/
def MAX_RW_COUNT : Int := 0x7ffff000

/-- LPS `State.v:1150` `rw_count_clamp`. -/
def rwCountClamp (count : Word) : Int := min (uns count) MAX_RW_COUNT

/-- LPS `State.v:1344` `access_okb`: `access_ok` against the Sv48 `TASK_SIZE`. -/
def accessOkb (base : Word) (len : Int) : Bool :=
  accessOkbFor legacySv48AddressSpace base len

/-- The legacy public gate retains exactly its original scalar formula. -/
theorem accessOkb_legacy_def (base : Word) (len : Int) :
    accessOkb base len =
      (decide (len ≤ taskSize) && decide (uns base ≤ taskSize - len)) := rfl

/-! ## Descriptors, sockets and pipes -/

/-- LPS `State.v:2424` `SockState`. -/
inductive SockState where
  | fresh
  | bound
  | listening
  | connected (peer : PeerAddr) (chan : Word) (rx : NetStream)
  | reset (peer : PeerAddr) (chan : Word)

/-- LPS `State.v:2434` `PIPE_BUF`. -/
def PIPE_BUF : Int := 4096

/-- LPS `State.v:2462` `PipeBuf`: queued bytes and the bytes counted against the pipe. -/
abbrev PipeBuf := List Byte × Int

/-- LPS `State.v:2611` `FdEntry`. Channels 0, 1, 2 are stdin, stdout and stderr. -/
inductive FdEntry where
  | channel (chan : Word)
  | file (p : Path) (offset : Word)
  | fileW (p : Path) (offset : Word)
  | fileA (p : Path) (offset : Word)
  | fileRW (p : Path) (offset : Word)
  | dir
  | socket (sk : SockState)
  | pipe (id : Word) (writer : Bool)
  | devNull (rd wr : Bool)
  | urandom

/-! ## The virtual-memory ledger -/

/-- LPS `State.v:2704` `VmMaps`. Ranges are `(base, size)`. -/
structure VmMaps where
  reserved : List (Word × Word)
  maps : List (Word × Word)
  noaccess : List (Word × Word)
  startBrk : Word
  brk : Word
  limit : Int
  mmapBase : Word
  initSp : Word

/-- LPS `State.v:2737` `alloc_top`: mappings stay below the 8 MiB stack band. -/
def allocTop (h : VmMaps) : Int := uns h.initSp - stackMaxSize

/-- LPS `State.v:2852` `live_bytes`. -/
def liveBytes : List (Word × Word) → Int
  | [] => 0
  | (_, sz) :: r => uns sz + liveBytes r

/-- LPS `State.v:2888` `FdState`. -/
structure FdState where
  table : List (Word × FdEntry)
  pipes : List (Word × PipeBuf)

/-- LPS `State.v:2897` `VmState`: the ledger, the lazy (`MAP_NORESERVE`) reservations and
the pages already materialized. -/
structure VmState where
  maps : VmMaps
  lazy : List (Word × Word)
  materialized : List Word

/-- LPS `State.v:2907` `IoState`. -/
structure IoState where
  stdin : InputStream
  urandom : InputStream
  net : NetQueue
  connIx : Word

/-- LPS `State.v:2930` `FsState`. -/
structure FsState where
  image : FileSystem

/-- LPS `State.v:2964` `Creds`. -/
structure Creds where
  uid : Word
  euid : Word
  suid : Word
  gid : Word
  egid : Word
  sgid : Word
  groups : List Word

/-- LPS `State.v:3030` `creds_privileged`. -/
def Creds.privileged (c : Creds) : Bool := c.euid == 0

/-- LPS `State.v:3035` `ProcState`. Facts the model cannot know in advance are either
quantified inputs, pinned at first observation (`tid`, `utsname`, the `statpins`) or
carried and advanced (the clock). -/
structure ProcState where
  halted : Option Word
  tid : Option Word
  creds : Creds
  setsidSucceeded : Bool
  sigmask : Word
  children : Bool
  utsname : Option (List Byte)
  sigaltstackInstalled : Bool
  killed : Bool
  sigabrtPending : Bool
  abortTerminal : Bool
  statpins : List (Path × List Byte)

/-- LPS `State.v:3337` `LimState`. -/
structure LimState where
  core : Option (List Byte)
  nofile : Word

/-- LPS `State.v:3381` `TimeState`. -/
structure TimeState where
  clock : Word

/-- LPS `State.v:3429` `Model`: the kernel-side state of the process. -/
structure Model where
  fd : FdState
  vm : VmState
  io : IoState
  fsys : FsState
  proc : ProcState
  lim : LimState
  time : TimeState
  /-- Kernel buffer and mapping boundary. Default preserves the literal LPS port,
  including its fixed Sv48 gate under alternative declared virtual-address widths. -/
  addressSpace : AddressSpaceProfile := legacySv48AddressSpace

namespace Model

variable (m : Model)

/-- Select an address boundary without changing the process state. -/
def withAddressSpace (profile : AddressSpaceProfile) : Model :=
  { m with addressSpace := profile }

@[simp] theorem withAddressSpace_addressSpace (profile : AddressSpaceProfile) :
    (m.withAddressSpace profile).addressSpace = profile := rfl

@[simp] theorem withAddressSpace_self : m.withAddressSpace m.addressSpace = m := rfl

@[simp] theorem withAddressSpace_withAddressSpace (p q : AddressSpaceProfile) :
    (m.withAddressSpace p).withAddressSpace q = m.withAddressSpace q := rfl

/-- LPS `State.v:3441` `m_fds`. -/
def fds : List (Word × FdEntry) := m.fd.table
/-- LPS `State.v:3442` `m_pipes`. -/
def pipes : List (Word × PipeBuf) := m.fd.pipes
/-- LPS `State.v:3443` `m_vmmaps`. -/
def vmmaps : VmMaps := m.vm.maps
/-- LPS `State.v:3444` `m_vm_lazy`. -/
def vmLazy : List (Word × Word) := m.vm.lazy
/-- LPS `State.v:3445` `m_vm_materialized`. -/
def vmMaterialized : List Word := m.vm.materialized
/-- LPS `State.v:3447` `m_stdin`. -/
def stdin : InputStream := m.io.stdin
/-- LPS `State.v:3448` `m_urandom`. -/
def urandom : InputStream := m.io.urandom
/-- LPS `State.v:3449` `m_net`. -/
def net : NetQueue := m.io.net
/-- LPS `State.v:3451` `m_fs`. -/
def fs : FileSystem := m.fsys.image
/-- LPS `State.v:3452` `m_halted`. -/
def halted : Option Word := m.proc.halted
/-- LPS `State.v:3453` `m_tid`. -/
def tid : Option Word := m.proc.tid
/-- LPS `State.v:3456` `m_has_children`. -/
def hasChildren : Bool := m.proc.children
/-- LPS `State.v:3464` `m_killed`: the killing signal, if the process was killed. -/
def killedBy : Option Word := if m.proc.killed then m.proc.halted else none
/-- LPS `State.v:3466` `m_sigabrt_pending`. -/
def sigabrtPending : Bool := m.proc.sigabrtPending
/-- LPS `State.v:3468` `m_abort_terminal`. -/
def abortTerminal : Bool := m.proc.abortTerminal
/-- LPS `State.v:3477` `m_creds`. -/
def creds : Creds := m.proc.creds

/-- LPS `State.v:3528` `with_fds`. -/
def withFds (fds : List (Word × FdEntry)) : Model := { m with fd.table := fds }
/-- LPS `State.v:3531` `with_pipes`. -/
def withPipes (ps : List (Word × PipeBuf)) : Model := { m with fd.pipes := ps }
/-- LPS `State.v:3534` `with_vmmaps`. -/
def withVmmaps (h : VmMaps) : Model := { m with vm.maps := h }
/-- LPS `State.v:3538` `with_vm_backing`. -/
def withVmBacking (lazy : List (Word × Word)) (materialized : List Word) : Model :=
  { m with vm.lazy := lazy, vm.materialized := materialized }
/-- LPS `State.v:3542` `with_stdin`. -/
def withStdin (s : InputStream) : Model := { m with io.stdin := s }
/-- LPS `State.v:3548` `with_urandom`. -/
def withUrandom (s : InputStream) : Model := { m with io.urandom := s }
/-- LPS `State.v:3556` `with_net`. -/
def withNet (q : NetQueue) : Model := { m with io.net := q }

/-- LPS `State.v:3581` `statpins_restrict`. -/
def statpinsRestrict (fs : FileSystem) (ps : List (Path × List Byte)) :
    List (Path × List Byte) :=
  ps.filter fun e => (Fs.lookup fs e.1).isSome

/-- LPS `State.v:3588` `with_fs`: also drops the pins of removed files. -/
def withFs (fs : FileSystem) : Model :=
  { m with fsys.image := fs, proc.statpins := statpinsRestrict fs m.proc.statpins }
/-- LPS `State.v:3605` `with_halted`: exit with `code`; not killed. -/
def withHalted (code : Word) : Model :=
  { m with proc.halted := some code, proc.killed := false }
/-- LPS `State.v:3614` `with_tid`. -/
def withTid (tid : Word) : Model := { m with proc.tid := some tid }
/-- LPS `State.v:3698` `with_abort_terminal`. -/
def withAbortTerminal (b : Bool) : Model := { m with proc.abortTerminal := b }
/-- LPS `State.v:3708` `with_nofile`. -/
def withNofile (n : Word) : Model := { m with lim.nofile := n }
/-- LPS `State.v:3711` `with_creds`. -/
def withCreds (c : Creds) : Model := { m with proc.creds := c }
/-- LPS `State.v:3746` `with_children`. -/
def withChildren : Model := { m with proc.children := true }
/-- LPS `State.v:3766` `with_sigmask`. -/
def withSigmask (s : Word) : Model := { m with proc.sigmask := s }
/-- LPS `State.v:3847` `with_killed`: killed by signal `sig`. -/
def withKilled (sig : Word) : Model :=
  { m with proc.halted := some sig, proc.killed := true }
/-- LPS `State.v:3881` `with_clock`. -/
def withClock (t : Word) : Model := { m with time.clock := t }

end Model

/-- LPS `State.v:3491` `overflow_id`. -/
def overflowId : Word := 65534
/-- LPS `State.v:3506` `default_nofile`. -/
def defaultNofile : Word := 1024

/-- LPS `State.v:3513` `mkModel`. -/
def mkModel (fds : List (Word × FdEntry)) (vm : VmMaps) (stdin : InputStream)
    (fs : FileSystem) (halted tid : Option Word) (rlim : Option (List Byte)) : Model where
  fd := ⟨fds, []⟩
  vm := ⟨vm, [], []⟩
  io := ⟨stdin, InputStream.eof, netSilent, 0⟩
  fsys := ⟨fs⟩
  proc :=
    { halted, tid
      creds := ⟨overflowId, overflowId, overflowId, overflowId, overflowId, overflowId, []⟩
      setsidSucceeded := false, sigmask := 0, children := false, utsname := none
      sigaltstackInstalled := false, killed := false, sigabrtPending := false
      abortTerminal := false, statpins := [] }
  lim := ⟨rlim, defaultNofile⟩
  time := ⟨0⟩

/-! ## Observable events -/

/-- LPS `State.v:3902` `event`. Reads and writes are byte-granular, so
`write("a"); write("b")` and `write("ab")` are the same trace; the file system is observed
only at exit or death. -/
inductive Event where
  | readEv (ch : Word) (b : Byte)
  | writeEv (ch : Word) (b : Byte)
  | exitEv (code : Word) (fs : FileSystem)
  | killEv (sig : Word) (fs : FileSystem)
  deriving DecidableEq

/-! ## Descriptor and pipe tables -/

/-- LPS `State.v:3922` `fd_lookup`. -/
def fdLookup : List (Word × FdEntry) → Word → Option FdEntry
  | [], _ => none
  | (k, e) :: r, fd => if k == fd then some e else fdLookup r fd

/-- LPS `State.v:3929` `fd_insert`. -/
def fdInsert (fds : List (Word × FdEntry)) (fd : Word) (e : FdEntry) : List (Word × FdEntry) :=
  (fd, e) :: fds.filter fun p => !(p.1 == fd)

/-- LPS `State.v:3933` `fd_remove`. -/
def fdRemove (fds : List (Word × FdEntry)) (fd : Word) : List (Word × FdEntry) :=
  fds.filter fun p => !(p.1 == fd)

/-- LPS `State.v:3943` `alloc_fd_aux`. -/
def allocFdAux (fds : List (Word × FdEntry)) : Word → Nat → Word
  | cand, 0 => cand
  | cand, f + 1 => match fdLookup fds cand with
    | none => cand
    | some _ => allocFdAux fds (cand + 1) f

/-- LPS `State.v:3952` `alloc_fd`: the lowest free descriptor. -/
def allocFd (fds : List (Word × FdEntry)) : Word := allocFdAux fds 0 4096

/-- LPS `State.v:3974` `pipe_lookup`. -/
def pipeLookup : List (Word × PipeBuf) → Word → Option PipeBuf
  | [], _ => none
  | (k, st) :: r, id => if k == id then some st else pipeLookup r id

/-- LPS `State.v:3982` `pipe_insert`. -/
def pipeInsert (ps : List (Word × PipeBuf)) (id : Word) (st : PipeBuf) :
    List (Word × PipeBuf) :=
  (id, st) :: ps.filter fun p => !(p.1 == id)

/-- LPS `State.v:4014` `pipe_write_room`. -/
def pipeWriteRoom : PipeBuf → Int → Bool
  | ([], _), n => decide (n ≤ PIPE_BUF)
  | (_ :: _, used), n => decide (used + n ≤ PIPE_BUF)

/-- LPS `State.v:4022` `pipe_append`. -/
def pipeAppend : PipeBuf → List Byte → PipeBuf
  | ([], _), bs => (bs, bs.length)
  | (q, used), bs => (q ++ bs, used + bs.length)

/-- LPS `State.v:4040` `pipe_take`. -/
def pipeTake (q : List Byte) (n : Int) : List Byte := q.take (min n q.length).toNat

/-- LPS `State.v:4073` `pipe_consume`. -/
def pipeConsume (st : PipeBuf) (k : Nat) : PipeBuf := (st.1.drop k, st.2)

/-- LPS `State.v:4217` `pipe_end_live`: some descriptor holds this end of the pipe. -/
def pipeEndLive : List (Word × FdEntry) → Word → Bool → Bool
  | [], _, _ => false
  | (_, .pipe id' w) :: r, id, writer => (id' == id && w == writer) || pipeEndLive r id writer
  | _ :: r, id, writer => pipeEndLive r id writer

/-! ## Address ranges -/

/-- LPS `State.v:4268` `iv_overlap`. -/
def ivOverlap (a1 n1 a2 n2 : Word) : Bool :=
  decide (uns a1 < uns a2 + uns n2) && decide (uns a2 < uns a1 + uns n1)

/-- LPS `State.v:4273` `region_free`. -/
def regionFree : List (Word × Word) → Word → Word → Bool
  | [], _, _ => true
  | (a, sz) :: r, lo, n => !ivOverlap lo n a sz && regionFree r lo n

/-- LPS `State.v:4325` `map_remove`. -/
def mapRemove (maps : List (Word × Word)) (lo : Word) : List (Word × Word) :=
  maps.filter fun p => !(p.1 == lo)

/-- LPS `State.v:4336` `reserved_top`. -/
def reservedTop : List (Word × Word) → Int
  | [] => 0
  | (a, sz) :: r => max (uns a + uns sz) (reservedTop r)

/-- LPS `State.v:4360` `iv_subtract`: what is left of `[a, a+sz)` outside `[lo, hi)`. -/
def ivSubtract (a sz : Word) (lo hi : Int) : List (Word × Word) :=
  let aZ := uns a
  let szZ := uns sz
  let left := if aZ < lo then [(a, zw (min szZ (lo - aZ)))] else []
  let right := if hi < aZ + szZ then [(zw (max aZ hi), zw (aZ + szZ - max aZ hi))] else []
  left ++ right

/-- LPS `State.v:4369` `maps_subtract`. -/
def mapsSubtract : List (Word × Word) → Int → Int → List (Word × Word)
  | [], _, _ => []
  | (a, sz) :: r, lo, hi => ivSubtract a sz lo hi ++ mapsSubtract r lo hi

/-- LPS `State.v:4381` `maps_subtract_all`. -/
def mapsSubtractAll (maps : List (Word × Word)) : List (Word × Word) → List (Word × Word)
  | [] => maps
  | (a, n) :: rest => mapsSubtractAll (mapsSubtract maps (uns a) (uns a + uns n)) rest

/-- LPS `State.v:4509` `vm_backed_maps`: mappings that need backing (not `PROT_NONE`). -/
def vmBackedMaps (h : VmMaps) : List (Word × Word) := mapsSubtractAll h.maps h.noaccess

/-! ## Lazy backing and the allocation budget -/

/-- LPS `State.v:4530` `page_base_of`. -/
def pageBaseOf (z : Int) : Word := zw (z / pageSize * pageSize)

/-- LPS `State.v:4535` `page_mem`. -/
def pageMem (p : Word) (pages : List Word) : Bool := pages.any (· == p)

/-- LPS `State.v:4538` `page_insert`. -/
def pageInsert (p : Word) (pages : List Word) : List Word :=
  if pageMem p pages then pages else p :: pages

/-- LPS `State.v:4549` `access_pages_acc`. -/
def accessPagesAcc : Int → Nat → List Word → List Word
  | _, 0, pages => pages
  | base, n + 1, pages => accessPagesAcc (base + 1) n (pageInsert (pageBaseOf base) pages)

/-- LPS `State.v:4560` `accesses_pages`. -/
def accessesPages : List (Word × Nat) → List Word → List Word
  | [], pages => pages
  | (a, n) :: rest, pages => accessesPages rest (accessPagesAcc (uns a) n pages)

/-- LPS `State.v:4568` `page_in_ranges`. -/
def pageInRanges (p : Word) (ranges : List (Word × Word)) : Bool :=
  ranges.any fun r => decide (uns r.1 ≤ uns p) && decide (uns p + pageSize ≤ uns r.1 + uns r.2)

/-- LPS `State.v:4577` `newly_materialized_pages`. -/
def newlyMaterializedPages (lazy : List (Word × Word)) (materialized : List Word)
    (accesses : List (Word × Nat)) : List Word :=
  (accessesPages accesses []).filter fun p => pageInRanges p lazy && !pageMem p materialized

/-- LPS `State.v:4583` `materialize_accesses`: charge newly touched lazy pages, or refuse
when the budget would be exceeded. -/
def materializeAccesses (lazy : List (Word × Word)) (materialized : List Word) (used limit : Int)
    (accesses : List (Word × Nat)) : Option (List Word) :=
  match newlyMaterializedPages lazy materialized accesses with
  | [] => some materialized
  | new => if used + new.length * pageSize ≤ limit then some (new ++ materialized) else none

/-- LPS `State.v:4650` `vm_backing_used`: the bytes charged against the budget. -/
def vmBackingUsed (m : Model) : Int :=
  liveBytes (mapsSubtractAll (vmBackedMaps m.vmmaps) m.vmLazy)
    + m.vmMaterialized.length * pageSize

/-- LPS `State.v:4659` `vm_backing_within_limit`. -/
def vmBackingWithinLimit (m : Model) : Bool := decide (vmBackingUsed m ≤ m.vmmaps.limit)

/-- LPS `State.v:4662` `materialize_model_accesses`. -/
def materializeModelAccesses (m : Model) (accesses : List (Word × Nat)) : Option Model :=
  (materializeAccesses m.vmLazy m.vmMaterialized (vmBackingUsed m) m.vmmaps.limit accesses).map
    fun pages => m.withVmBacking m.vmLazy pages

/-- LPS `State.v:4670` `page_outside_range`. -/
def pageOutsideRange (lo hi : Int) (p : Word) : Bool :=
  !(decide (lo ≤ uns p) && decide (uns p < hi))

/-- LPS `State.v:4676` `vm_forget_range`. -/
def vmForgetRange (lo hi : Int) (m : Model) : Model :=
  m.withVmBacking (mapsSubtract m.vmLazy lo hi) (m.vmMaterialized.filter (pageOutsideRange lo hi))

/-- LPS `State.v:4697` `write_accesses`. -/
def writeAccesses : List (Word × List Byte) → List (Word × Nat)
  | [] => []
  | (a, bs) :: rest => (a, bs.length) :: writeAccesses rest

/-- LPS `State.v:4704` `syscall_effect_accesses`. -/
def syscallEffectAccesses (eff : SyscallEffect) : List (Word × Nat) :=
  eff.copyins ++ writeAccesses eff.writes

/-- LPS `State.v:4746` `lazy_interior`: the whole pages inside `[a, a+n)`. -/
def lazyInterior (a n : Word) : List (Word × Word) :=
  let lo := uns a
  let hi := lo + uns n
  let lo' := (lo + pageSize - 1) / pageSize * pageSize
  let hi' := hi / pageSize * pageSize
  if lo' < hi' then [(zw lo', zw (hi' - lo'))] else []

/-- LPS `State.v:4755` `vm_add_lazy`. -/
def vmAddLazy (a n : Word) (m : Model) : Model :=
  m.withVmBacking (lazyInterior a n ++ m.vmLazy) m.vmMaterialized

/-- LPS `State.v:4809` `map_contains`. -/
def mapContains (maps : List (Word × Word)) (lo n : Word) : Bool :=
  maps.any fun p => decide (uns p.1 ≤ uns lo) && decide (uns lo + uns n ≤ uns p.1 + uns p.2)

/-- LPS `State.v:4821` `map_has`. -/
def mapHas (maps : List (Word × Word)) (lo n : Word) : Bool :=
  maps.any fun p => p.1 == lo && p.2 == n

/-! ## Process input -/

/-- LPS `State.v:4930` `tmp_prefix`: `"/tmp/"`. -/
def tmpPrefix : Path := [47, 116, 109, 112, 47]
/-- LPS `State.v:4934` `tmp_key`. -/
def tmpKey (name : Path) : Path := tmpPrefix ++ name
/-- LPS `State.v:4943` `tmp_nul_free`. -/
def tmpNulFree (name : Path) : Bool := !name.any (· == 0)

/-- LPS `State.v:4961` `fs_seed_tmp`: seed the private `/tmp`. -/
def fsSeedTmp (fs t : FileSystem) : FileSystem :=
  t.foldl (fun acc e => if tmpNulFree e.1 then Fs.set acc (tmpKey e.1) e.2 else acc) fs

/-- LPS `State.v:5150` `ProcInput`: everything the environment supplies, quantified once and
shared by the two binaries a statement compares. -/
structure ProcInput where
  argv : List (List Byte)
  envp : List (List Byte)
  imageFs : FileSystem
  stdin : InputStream
  uid : Word
  gid : Word
  groups : List Word
  net : NetQueue
  nofile : Word
  sigmask : Word
  hwcap : Word
  abortTerminal : Bool
  vaSize : VaSize
  urandom : InputStream
  tmp : FileSystem

/-- LPS `State.v:5327` `in_fs`. -/
def ProcInput.fs (inp : ProcInput) : FileSystem := fsSeedTmp inp.imageFs inp.tmp

/-- LPS `State.v:5370` `init_model`: descriptors 0, 1, 2 are the three channels; the ledger
holds the image reservations, the break and the mmap base; the credentials and limits come
from the input. -/
def initModel (reserved : List (Word × Word)) (brk0 mbase sp : Word) (lim : Int)
    (inp : ProcInput) : Model :=
  (((((((mkModel [(0, .channel 0), (1, .channel 1), (2, .channel 2)]
      ⟨reserved, [], [], brk0, brk0, lim, mbase, sp⟩ inp.stdin inp.fs none none none).withCreds
      ⟨inp.uid, inp.uid, inp.uid, inp.gid, inp.gid, inp.gid, inp.groups⟩).withUrandom
      inp.urandom).withNet inp.net).withNofile inp.nofile).withSigmask
      inp.sigmask).withAbortTerminal inp.abortTerminal)

/-- Explicit-profile initialization. `initModel` retains the literal LPS boundary. -/
def initModelFor (profile : AddressSpaceProfile) (reserved : List (Word × Word))
    (brk0 mbase sp : Word) (lim : Int) (inp : ProcInput) : Model :=
  (initModel reserved brk0 mbase sp lim inp).withAddressSpace profile

@[simp] theorem initModelFor_addressSpace (profile : AddressSpaceProfile)
    (reserved : List (Word × Word)) (brk0 mbase sp : Word) (lim : Int) (inp : ProcInput) :
    (initModelFor profile reserved brk0 mbase sp lim inp).addressSpace = profile := rfl

theorem initModelFor_legacy (reserved : List (Word × Word)) (brk0 mbase sp : Word)
    (lim : Int) (inp : ProcInput) :
    initModelFor legacySv48AddressSpace reserved brk0 mbase sp lim inp =
      initModel reserved brk0 mbase sp lim inp := rfl

end Silmaril.Process.LPS
