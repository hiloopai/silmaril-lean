module

public import Silmaril.X86.Concurrency.Cir.Pool.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Thms
public import Silmaril.X86.Concurrency.Cir.ParHash.Defs
public import Silmaril.X86.Concurrency.Cir.Thms
public import Silmaril.X86.Concurrency.Cir.Progress.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Cert
import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Live
import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Values
import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Ok

/-!
# A worker pool over a mutex-protected queue: theorems

PROVED (standard axioms; proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Pool/`), except where a statement names a Task.

* `Wp.ok_of_okB`: the layout check decides the layout conditions.
* **`Wp.proved`**: every pool meeting the layout conditions is proved against the mutex
  interface (`Mutex.Client.Proved`), once, from the interface's fields only.
* **`Wp.any_mutex`** (by `link_any_mutex`): linked with **any** mutex `M : Iface` that fits
  the slot, at every loop bound, every finished, drained state of the CIR-native TSO or XL
  machine satisfies the goal; `Wp.any_mutex_sc` on the SC machine; `Wp.no_race`.
* **`Wp.exactly_once`**: so every well-formed job ran **exactly once** (its counter is `1`) and
  **correctly** (its output cells hold `fn arg`).
* **`Wp.behav`**: the same for every axiomatic behaviour under every model `M ⊑ XL`, for a
  lowering of the linked pool to a program that is uniform and spawn-free (by the bridge
  `Csl.Task.cirXlOpAx`, proved as `Csl.cirXlOpAx_holds`). `Wp.behav_of_bridge` is the
  earlier form, conditional on the bridge.
* Instances: `Wp.spin`, `Wp.fmutex` (the spin mutex and the futex mutex).
* **No deadlock** (`Task.poolNoDeadlock` restated): `poolNoDeadlock_of_live` (every
  mutex whose code is `Progress.MutexLive`), `poolNoDeadlock_spin`, `poolNoDeadlock_spinSc`,
  `poolNoDeadlock_fmutex`; `exHash_noDeadlock` for the concrete hashing pool. The original
  statement is false (`poolNoDeadlockAsStated_false`, in `Pool/Run/Thms.lean`).
* **Parallel hashing on the pool**: `hash_pool` (jobs are `crc32_z` leaf jobs, whose
  summary ties to the verified x86 contract) and the concrete `exHash`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex (Iface Client spinMutex link_any_mutex link_any_mutex_sc
  link_no_race)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (Final leValue)
open Silmaril.X86.Ladder.ZlibChecksums (crc32)

namespace Wp

variable {P : Wp}

/-- **The layout check is sound.** -/
theorem ok_of_okB (h : P.okB = true) : P.Ok := Silmaril.Proofs.X86.Concurrency.Cir.Pool.ok_of_okB h

/-- **The pool is proved against the mutex interface**, for every pool meeting the layout
conditions: a CSL certificate at every mutex `M : Iface` fitting the slot, at every loop bound,
whose postconditions give the goal. -/
theorem proved (hP : P.Ok) : P.client.Proved P.goal :=
  Silmaril.Proofs.X86.Concurrency.Cir.Pool.pool_proved hP

/-- **Any mutex**: linked with any `M : Iface` that fits the slot, every finished, drained state
of the TSO or XL store-buffer machine satisfies the goal, at every loop bound. -/
theorem any_mutex (hP : P.Ok) (M : Iface) (hM : M.size ≤ P.slot) (L : Nat) {model : OModel}
    {Cf : OCfg} (hr : OReach model P.K (P.client.link M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < P.K, (Cf.ts t).1 = .skip) : P.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutex (proved hP) M hM L hr hd hf

/-- The same on the SC machine. -/
theorem any_mutex_sc (hP : P.Ok) (M : Iface) (hM : M.size ≤ P.slot) (L : Nat) {Cf : Cfg}
    (hr : ScReach P.K (P.client.link M L) Cf) (hf : Cf.Done P.K) :
    P.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutex_sc (proved hP) M hM L hr hf

/-- **The linked pool is race-free** in every SC-reachable state (`no_race`). -/
theorem no_race (hP : P.Ok) (M : Iface) (hM : M.size ≤ P.slot) (L : Nat) {Cf : Cfg}
    (hr : ScReach P.K (P.client.link M L) Cf) : ¬ Race P.K Cf :=
  link_no_race (proved hP) M hM L hr

/-- **The goal, in values**: every well-formed job's counter is `1` and its output cells hold
`fn arg`. -/
theorem goal_values {rs : Nat → Regs} {mem : Heap} (hg : P.goal rs mem) {it : Item}
    (hit : it ∈ P.items) (hwf : it.wfB = true) :
    mem it.cnt = some 1 ∧ it.job.outs.map (fun c => mem c.1) = (it.job.fn it.arg).map some := by
  have hle := hg it hit
  refine ⟨hle _ _ (Silmaril.Proofs.X86.Concurrency.Cir.Pool.Item.doneH_cnt_one hwf), ?_⟩
  have hd := Silmaril.Proofs.X86.Concurrency.Cir.Pool.Item.doneH_outs hwf
  rw [← hd]
  apply List.map_congr_left
  intro c hc
  have : it.doneH c.1 ∈ (it.job.fn it.arg).map some := hd ▸ List.mem_map_of_mem hc
  obtain ⟨v, -, hv⟩ := List.mem_map.mp this
  rw [← hv]
  exact hle _ _ hv.symm

/-- **Every job runs exactly once, with its contract**, under any mutex meeting the interface,
on TSO and XL, at every loop bound: in every finished, drained state, each well-formed job's
run counter is `1` and its output cells hold `fn arg`. -/
theorem exactly_once (hP : P.Ok) (M : Iface) (hM : M.size ≤ P.slot) (L : Nat)
    {model : OModel} {Cf : OCfg} (hr : OReach model P.K (P.client.link M L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < P.K, (Cf.ts t).1 = .skip) :
    ∀ it ∈ P.items, it.wfB = true → Cf.mem it.cnt = some 1 ∧
      it.job.outs.map (fun c => Cf.mem c.1) = (it.job.fn it.arg).map some :=
  fun _ hit hwf => goal_values (any_mutex hP M hM L hr hd hf) hit hwf

/-- **Under every axiomatic model `M ⊑ XL`** (Task-conditional form, kept; the bridge
`Csl.Task.cirXlOpAx` is proved, so `behav` below is unconditional). Let `Pr` be a program whose
CIR-native start is the linked pool,
uniform and spawn-free. Every behaviour of `Pr` under any `Mod ⊑ XL` is, in its registers and
location values, a finished state of the CIR-native machine satisfying the goal. -/
theorem behav_of_bridge (hb : Csl.Task.cirXlOpAx) (hP : P.Ok) (M : Iface)
    (hM : M.size ≤ P.slot) (L : Nat) {Pr : Prog} (hinit : progInit Pr = P.client.link M L)
    (hlen : Pr.threads.length = P.K) (hu : Pr.uniformB = true)
    (ht : (Pr.threads.all fun th => th.body.threadFree && th.body.posSizes && !th.spawned) = true)
    {Mod : Exec → Prop} (hMod : Mod ⊑ Exec.Xl) {f : Final} (hf : Behav Pr Mod f) :
    ∃ C : OCfg, (∀ t < P.K, (C.ts t).1 = .skip ∧ f.regs t = (C.ts t).2) ∧
      (∀ l ∈ Pr.locs, leValue f.mem l.addr l.size = C.mem l.addr) ∧
      P.goal (fun t => (C.ts t).2) C.mem := by
  have G := Silmaril.Proofs.X86.Concurrency.Cir.Pool.ginv hP M hM L
  rw [← hinit, ← hlen] at G
  obtain ⟨C, -, hfin, hm, hs', hI', q, -, l1, -⟩ :=
    drf_behav_of_bridge hb hu ht G (behav_mono hMod hf)
  rw [hlen] at hfin q
  refine ⟨C, hfin, hm, fun it hit => ?_⟩
  have h0 := q 0 hP.kpos
  simp only [Silmaril.Proofs.X86.Concurrency.Cir.Pool.Qt, ite_true] at h0
  exact Silmaril.Proofs.X86.Concurrency.Cir.Pool.le_trans' (h0 it hit) (l1 0)

/-- **Under every axiomatic model `M ⊑ XL`** (unconditional: the bridge is `cirXlOpAx_holds`).
Let `Pr` be a program whose CIR-native start is the linked pool, uniform and spawn-free.
Every behaviour of `Pr` under any `Mod ⊑ XL` is, in its registers and location values, a
finished state of the CIR-native machine satisfying the goal. -/
theorem behav (hP : P.Ok) (M : Iface)
    (hM : M.size ≤ P.slot) (L : Nat) {Pr : Prog} (hinit : progInit Pr = P.client.link M L)
    (hlen : Pr.threads.length = P.K) (hu : Pr.uniformB = true)
    (ht : (Pr.threads.all fun th => th.body.threadFree && th.body.posSizes && !th.spawned) = true)
    {Mod : Exec → Prop} (hMod : Mod ⊑ Exec.Xl) {f : Final} (hf : Behav Pr Mod f) :
    ∃ C : OCfg, (∀ t < P.K, (C.ts t).1 = .skip ∧ f.regs t = (C.ts t).2) ∧
      (∀ l ∈ Pr.locs, leValue f.mem l.addr l.size = C.mem l.addr) ∧
      P.goal (fun t => (C.ts t).2) C.mem :=
  behav_of_bridge cirXlOpAx_holds hP M hM L hinit hlen hu ht hMod hf

/-- **With the spin mutex.** -/
theorem spin (hP : P.Ok) (hs : 8 ≤ P.slot) (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model P.K (P.client.link spinMutex L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < P.K, (Cf.ts t).1 = .skip) : P.goal (fun t => (Cf.ts t).2) Cf.mem :=
  any_mutex hP spinMutex hs L hr hd hf

/-- **With the futex mutex** (Drepper's `fmutex_lock`/`fmutex_unlock`). -/
theorem fmutex (hP : P.Ok) (hs : 8 ≤ P.slot) (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model P.K (P.client.link Mutex.Futex.fmutex L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < P.K, (Cf.ts t).1 = .skip) : P.goal (fun t => (Cf.ts t).2) Cf.mem :=
  any_mutex hP Mutex.Futex.fmutex hs L hr hd hf

end Wp

/-! ## Parallel hashing on the pool -/

/-- The hashing jobs: buffer `k` (its cells and their values) to the result cell `res + 8k`, with
counter `cnt0 + 8k`. Each job is a `crc32_z` leaf job (`ParHash.leafJob`). -/
def hashItems (bufs : List ((Nat × Nat) × List Nat)) (res cnt0 : Nat) : List Item :=
  bufs.mapIdx fun k b => ⟨ParHash.leafJob b.1 (res + 8 * k), b.2, cnt0 + 8 * k⟩

/-- **Parallel hashing on the pool**: every finished, drained TSO/XL state of a hashing pool,
linked with any mutex, holds `crc32_z(0, buf_k)` in each result cell and `1` in each counter. -/
theorem hash_pool {P : Wp} {bufs : List ((Nat × Nat) × List Nat)} {res cnt0 : Nat}
    (hi : P.items = hashItems bufs res cnt0) (hP : P.okB = true)
    (hwf : P.items.all Item.wfB = true) (M : Iface) (hM : M.size ≤ P.slot) (L : Nat)
    {model : OModel} {Cf : OCfg} (hr : OReach model P.K (P.client.link M L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < P.K, (Cf.ts t).1 = .skip) :
    ∀ k (hk : k < bufs.length), Cf.mem (res + 8 * k) =
        some (crc32 0 (ParHash.toBytes (bufs[k]'hk).2)).toNat ∧
      Cf.mem (cnt0 + 8 * k) = some 1 := by
  intro k hk
  have hmem : (⟨ParHash.leafJob (bufs[k]'hk).1 (res + 8 * k), (bufs[k]'hk).2, cnt0 + 8 * k⟩ :
      Item) ∈ P.items := by
    rw [hi, hashItems, List.mem_mapIdx]
    exact ⟨k, hk, rfl⟩
  have h := Wp.exactly_once (Wp.ok_of_okB hP) M hM L hr hd hf _ hmem
    (List.all_eq_true.mp hwf _ hmem)
  refine ⟨?_, h.1⟩
  have h2 := h.2
  simp only [ParHash.leafJob, List.map_cons, List.map_nil, ParHash.crcFn, List.cons.injEq,
    and_true] at h2
  exact h2

/-- A concrete hashing pool: two workers, three 2-byte buffers. -/
def exHash : Wp where
  K := 2
  items := hashItems [((0x1000, 2), [1, 2]), ((0x1010, 2), [3, 4]), ((0x1020, 2), [5, 6])]
    0x2000 0x3000
  m := 0x100
  slot := 8
  qa := 0x200
  da := 0x208
  ea := 0x210
  cur0 := 0x300
  W := 4

theorem exHash_okB : exHash.okB = true := by decide +kernel

theorem exHash_wfB : exHash.items.all Item.wfB = true := by decide +kernel

/-- **The concrete hashing pool, under any mutex.** -/
theorem exHash_correct (M : Iface) (hM : M.size ≤ 8) (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (exHash.client.link M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) :
    Cf.mem 0x2000 = some (crc32 0 (ParHash.toBytes [1, 2])).toNat ∧
    Cf.mem 0x2008 = some (crc32 0 (ParHash.toBytes [3, 4])).toNat ∧
    Cf.mem 0x2010 = some (crc32 0 (ParHash.toBytes [5, 6])).toNat ∧
    Cf.mem 0x3000 = some 1 ∧ Cf.mem 0x3008 = some 1 ∧ Cf.mem 0x3010 = some 1 := by
  have H := hash_pool (P := exHash) rfl exHash_okB exHash_wfB M hM L hr hd hf
  exact ⟨(H 0 (by decide)).1, (H 1 (by decide)).1, (H 2 (by decide)).1, (H 0 (by decide)).2,
    (H 1 (by decide)).2, (H 2 (by decide)).2⟩

/-! ## No deadlock -/

/-- **No deadlock, for every live mutex** (`Task.poolNoDeadlock`, restated). Linked with a
mutex `M` whose code cannot get stuck (`Progress.MutexLive M`) and that fits the slot, a pool
meeting the layout conditions whose jobs are total reaches, on TSO or XL and at every loop bound,
no stuck configuration other than a finished, drained one or one with a thread out of a loop
bound. -/
theorem poolNoDeadlock_of_live {M : Iface} (ML : Progress.MutexLive M) (P : Wp) :
    Task.poolNoDeadlock P M :=
  Silmaril.Proofs.X86.Concurrency.Cir.Pool.noDeadlock ML P

/-- **No deadlock with the spin mutex.** -/
theorem poolNoDeadlock_spin (P : Wp) : Task.poolNoDeadlock P spinMutex :=
  poolNoDeadlock_of_live Progress.spinLive P

/-- **No deadlock with the spin mutex and the `seq_cst` unlock.** -/
theorem poolNoDeadlock_spinSc (P : Wp) : Task.poolNoDeadlock P Mutex.spinMutexSc :=
  poolNoDeadlock_of_live Progress.spinScLive P

/-- **No deadlock with the futex mutex.** -/
theorem poolNoDeadlock_fmutex (P : Wp) : Task.poolNoDeadlock P Mutex.Futex.fmutex :=
  poolNoDeadlock_of_live Progress.fmutexLive P

/-- The hashing jobs of `exHash` are total. -/
theorem exHash_total : ∀ it ∈ exHash.items, it.Total := by
  intro it hit
  simp only [exHash, hashItems, List.mapIdx_cons, List.mapIdx_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl <;>
    exact ⟨fun _ _ => rfl, by simp [ParHash.leafJob]⟩

/-- **The concrete hashing pool cannot deadlock**, with either mutex, on TSO or XL, at every loop
bound: a stuck reachable configuration is finished and drained, or a thread is out of a bound. -/
theorem exHash_noDeadlock (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (exHash.client.link spinMutex L).toO Cf ∨
      OReach model 2 (exHash.client.link Mutex.Futex.fmutex L).toO Cf)
    (hst : ∀ Cf', ¬ OStep model 2 Cf Cf') :
    (Cf.Drained ∧ ∀ t < 2, (Cf.ts t).1 = .skip) ∨ ∃ t < 2, Exhausted (Cf.ts t) := by
  rcases hr with hr | hr
  · exact poolNoDeadlock_spin exHash (Wp.ok_of_okB exHash_okB) (Nat.le_refl _) exHash_total L
      model Cf hr hst
  · exact poolNoDeadlock_fmutex exHash (Wp.ok_of_okB exHash_okB) (Nat.le_refl _) exHash_total L
      model Cf hr hst

end Silmaril.X86.Concurrency.Cir.Pool
