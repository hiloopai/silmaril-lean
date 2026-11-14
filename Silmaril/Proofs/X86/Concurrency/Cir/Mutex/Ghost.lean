module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Rel
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms
public import Silmaril.X86.Concurrency.Cir.Prim.Tasks.Thms

/-!
# Proofs: the Mutex interface with ghost state

* `link_any_mutexG`: a client proved against `IfaceG` gets its goal on TSO with any `IfaceG`
  (`Csl.Rel.rel_tso`).
* `IfaceG.ofIfaceR`: every `IfaceR` is an `IfaceG` (no ghost cells; the specs framed by
  `Csl.Rel.safeR_inv_frame`); so `spinMov`, `fmutexDec`, `spinMutexR` are `IfaceG`s.
* `ticketMutexG : IfaceG`: the ticket lock (`ticket_lock`, `ticket_unlock` with its plain-`mov`
  release), with the ghost invariant `Prim.Clients.ticketInvG` at `B = 2 ^ 32 - 1` permits, for
  clients of fewer than `2 ^ 32` threads.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Mutex

/-! ## Linking -/

theorem link_any_mutexG {C : Client} {goal : (Nat → Regs) → Heap → Prop} (hC : C.ProvedG goal)
    (M : IfaceG) (hM : M.size ≤ C.slot) (hN : M.thrOk C.N) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso C.N (C.linkG M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < C.N, (Cf.ts t).1 = .skip) : goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨I, Q, hs, gs, hI, gI, G, hgoal⟩ := hC M hM hN L
  obtain ⟨hs', gs', hI', gI', ps', q, i, l1, l2, -, -, -⟩ :=
    rel_tso (G0 := Heap.empty) G (fun _ e => by simp [Heap.empty] at e) hr hd hf
  exact hgoal _ _ hs' gs' hI' gI' ps' q i l1 l2

/-! ## `IfaceR`s are `IfaceG`s -/

/-- **Every `IfaceR` is an `IfaceG`**, with no ghost cells. -/
def IfaceG.ofIfaceR (M : IfaceR) : IfaceG where
  size := M.size
  init := M.init
  ginit := fun _ => Heap.empty
  gthr := fun _ _ => Heap.empty
  thrOk := fun _ => True
  inv := fun l R => liftI (M.inv l R ∗ hemp)
  ready := fun _ g => g = Heap.empty
  locked := fun l h g => M.locked l h ∧ g = Heap.empty
  lockCode := M.lockCode
  unlockCode := M.unlockCode
  init_dom := M.init_dom
  gdom l a h := by rcases h with e | ⟨_, e⟩ <;> simp [Heap.empty] at e
  gthr_disj _ _ _ _ := disjoint_empty _
  ginit_disj _ _ := disjoint_empty _
  init_inv l R hR r d := sep_emp (M.init_inv l R hR r d)
  ready_thr _ _ _ _ _ := rfl
  locked_excl l R h g := by
    rintro ⟨h12, -, -, -, -, -, -, -, ⟨h1, h2, -, -, d, rfl, -, -, ⟨l1, -⟩, ⟨l2, -⟩⟩, -⟩
    exact M.locked_excl l _ (sep_iff.mpr ⟨h1, h2, d, rfl, l1, l2⟩)
  lock_spec l R J L rs p g hrs _ hg := by
    subst hg
    refine safeR_conseq (fun p' _ h g' ⟨hp, hRL, hg'⟩ => ?_)
      (safeR_inv_frame (J := J) (M.lock_spec l R hemp L rs p hrs))
    obtain ⟨h1, h2, d, rfl, r, lk⟩ := sep_iff.mp hRL
    subst hg'
    exact ⟨hp, h1, h2, Heap.empty, Heap.empty, d, rfl, disjoint_empty _,
      (union_empty_left _).symm, ⟨r, rfl⟩, ⟨lk, rfl⟩⟩
  unlock_spec l R J L rs h g hrs _ hh := by
    obtain ⟨h1, h2, g1, g2, d, rfl, -, rfl, ⟨r, rfl⟩, ⟨lk, rfl⟩⟩ := hh
    rw [union_empty_left]
    exact safeR_conseq (fun _ _ _ _ x => x) (safeR_inv_frame (J := J)
      (M.unlock_spec l R hemp L rs false (Heap.union h1 h2) hrs (sep_iff.mpr ⟨h1, h2, d, rfl, r, lk⟩)))

/-! ## The ticket lock -/

/-- The ticket lock's permits: one fewer than `2 ^ 32`. -/
def tkB : Nat := 2 ^ 32 - 1

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex

namespace Silmaril.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.Proofs.X86.Concurrency.Cir.Mutex

/-- **The ticket lock as an `IfaceG`**: `next` at `l`, `serving` at `l + 4`, both
`0`; the ghost invariant `ticketInvG l (2 ^ 32 - 1) R`; thread `t` starts with permit `t`;
clients of fewer than `2 ^ 32` threads. The lock is `ticketLock_acquireR`, the unlock (a plain
`mov` of `serving + 1`) `ticketUnlock_rel`, both framed by `safeR_inv_frame`. -/
noncomputable def ticketMutexG : IfaceG where
  size := 8
  init := fun l => Heap.union (Heap.single l 0) (Heap.single (l + 4) 0)
  ginit := fun l => gsetL l (tkSet 0 0 ∅ false)
  gthr := fun l t => gsetL l (tkReady t (fun _ => False))
  thrOk := fun N => N < 2 ^ 32
  inv := fun l R => ticketInvG l tkB R
  ready := fun l g => tkReadyG l tkB g
  locked := fun l => tkLockedG l tkB
  lockCode := Prim.TicketLock.cert.body
  unlockCode := Prim.TicketUnlock.cert.body
  init_dom l a h := by
    simp only [union_apply, single_apply] at h
    by_cases h1 : a = l
    · omega
    · by_cases h2 : a = l + 4
      · omega
      · simp [h1, h2] at h
  gdom l a h := by
    rcases h with e | ⟨_, e⟩
    · exact tk_gdom e
    · exact tk_gdom e
  gthr_disj l _ _ ne := tk_ready_disj l ne
  ginit_disj l t := tk_init_ready_disj l t
  init_inv l R hR r d := tk_init_inv l tkB R hR r d
  ready_thr l N t hN ht := ⟨t, fun _ => False, by simp only [tkB]; omega, rfl⟩
  locked_excl l R h g := tk_locked_excl l tkB R h g
  lock_spec l R J L rs p g hrs hs hg := by
    obtain ⟨u, F, hu, rfl⟩ := hg
    refine safeR_conseq (fun p' _ h g' ⟨hp, _, hR, k, u', hu', hg'⟩ => ?_)
      (safeR_inv_frame (J := J) (ticketLock_acquireR l tkB R L rs p u F hrs (by omega)
        (by simp only [tkB]; omega) hu))
    exact ⟨hp, h, Heap.empty, Heap.empty, g', disjoint_empty_right _,
      (union_empty_right _).symm, disjoint_empty _, (union_empty_left _).symm, ⟨hR, rfl⟩,
      ⟨rfl, k, u', F, hu', hg'⟩⟩
  unlock_spec l R J L rs h g hrs hs hh := by
    obtain ⟨h1, h2, g1, g2, -, rfl, -, rfl, ⟨hR, rfl⟩, ⟨rfl, k, u, F, hu, rfl⟩⟩ := hh
    rw [union_empty_right, union_empty_left]
    exact safeR_conseq (fun _ _ _ _ ⟨e1, e2⟩ => ⟨e1, u, _, hu, e2⟩)
      (safeR_inv_frame (J := J) (ticketUnlock_rel l tkB R L rs h1 k u F hrs (by omega) hR))

/-- The `mov`-unlock spin mutex, the `fmutexDec`-style `IfaceR`s, and base-CSL mutexes that drain
first, as `IfaceG`s. -/
def spinMovG : IfaceG := IfaceG.ofIfaceR spinMov

end Silmaril.X86.Concurrency.Cir.Mutex
