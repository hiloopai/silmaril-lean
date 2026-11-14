module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Frame
public import Silmaril.X86.Concurrency.Cir.Prim.Thms

/-!
# Proofs: the spin mutex meets the interface

* `spin_lock_spec`: `spinLock_acquire` at the resource `locked l ∗ R`, with the
  postcondition commuted and the invariant framed (`safe_inv_frame`);
* `spin_unlock_spec`: the CIR program of `mutex_unlock` (`xor eax,eax; xchg [rdi],eax`), from
  `R ∗ locked l`, is safe under `inv l R` and ends with `emp`. The exchange (a draining atomic)
  hands `R` and the token back to the invariant. If the lock were free, the invariant would hold
  a token too, and two tokens cannot be disjoint: that case is impossible;
* the static facts `spin_init_dom`, `spin_init_inv`, `spin_locked_excl`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Prim (at_ lockInv op32)
open Silmaril.X86.Concurrency.Cir.TvCfg (mask32)

theorem at_rdi {rs : Regs} : ((at_ .rdi 0).eval rs).toNat = (rs .rdi).toNat := by
  simp [at_, Expr.eval, BinOp.eval]

theorem tok_ne (l : Nat) : Spin.tok l ≠ l := by simp [Spin.tok]

/-- A heap holding the token maps the token cell. -/
theorem locked_some {l : Nat} {h : Heap} (H : Spin.locked l h) : (h (Spin.tok l)).isSome := by
  obtain ⟨v, rfl⟩ := H; simp [single_apply]

/-- A heap holding `locked l ∗ R` (either order) maps the token cell. -/
theorem sepLocked_some {l : Nat} {R : HProp} {h : Heap} (H : (R ∗ Spin.locked l) h) :
    (h (Spin.tok l)).isSome := by
  obtain ⟨h₁, h₂, d, rfl, -, hl⟩ := sep_iff.mp H
  have := locked_some hl
  cases e : h₁ (Spin.tok l) with
  | some v => simp [union_some e]
  | none => rw [union_none e]; exact this

/-! ## Lock -/

theorem spin_lock_spec (l : Nat) (R J : HProp) (L : Nat) (rs : Regs) (hl : (rs .rdi).toNat = l) :
    Csl.Safe (Spin.inv l R ∗ J) (fun _ => R ∗ Spin.locked l) (Prim.SpinLock.cert.body L) rs
      Heap.empty :=
  safe_inv_frame (safe_conseq (fun _ _ H => sep_comm H)
    (Prim.spinLock_acquire l (Spin.locked l ∗ R) L rs hl))

/-! ## Unlock -/

theorem zero_eval (rs : Regs) : (op32 .xor .rax (.reg .rax)).eval rs = 0 := by
  simp [op32, mask32, Expr.eval, BinOp.eval]

theorem unlock_body (L : Nat) :
    Spin.unlockCert.body L = .seq Spin.zero (.seq Spin.xchgRel .skip) := rfl

theorem unlockSc_body (L : Nat) :
    Spin.unlockScCert.body L = .seq Spin.zero (.seq Spin.xchgSc .skip) := rfl

/-- **The releasing exchange**, for either mode: with `rax = 0`, from `R ∗ locked l`, the
exchange gives `R` and the token back to the invariant. -/
theorem safe_xchg0 {m : Mode} {l : Nat} {R : HProp} {Q : Regs → HProp} {rs : Regs} {h : Heap}
    (hl : (rs .rdi).toNat = l) (hax : rs .rax = 0) (hh : (R ∗ Spin.locked l) h)
    (hQ : ∀ rs', Q rs' Heap.empty) :
    Csl.Safe (Spin.inv l R) Q (.rmw .rax m 4 .xchg (at_ .rdi 0) (.reg .rax)) rs h := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | rmw hv =>
    rename_i old
    have hnew : RmwOp.result rs 4 old ((Expr.reg .rax).eval rs) .xchg = 0 := by
      simp [RmwOp.result, Expr.eval, hax]
    have htok := sepLocked_some hh
    refine ⟨rfl, rfl, (fun e => by cases e), (fun _ hI hIi hd => ?_)⟩
    -- the invariant's heap holds the lock word, and not the token
    have hIl : (hI l).isSome := by
      rcases hIi with ⟨hR, -, -, rfl⟩ | ⟨v, -, rfl⟩
      · simp [union_apply, single_apply]
      · simp [single_apply]
    have hhl : h l = none := by
      rcases hd l with e | e
      · exact e
      · simp [e] at hIl
    refine ⟨?_, (fun e => by cases e), fun hok => ?_⟩
    · intro a ha
      simp only [Lab.Touches, Lab.reads, Lab.wval, at_rdi, hl, List.mem_singleton,
        Prod.mk.injEq] at ha
      have ha' : a = l := by
        rcases ha with ⟨v, h1, -⟩ | h2
        · exact h1
        · by_contra hne; simp [Ne.symm hne] at h2
      subst ha'
      rw [union_none hhl]; exact hIl
    · rcases hIi with ⟨hR, hRR, hdR, rfl⟩ | ⟨v, hv0, rfl⟩
      · -- free: the invariant holds a token too, impossible
        exfalso
        have : (Heap.union (Heap.single l 0) hR (Spin.tok l)).isSome := by
          rw [union_none (by simp [single_apply, tok_ne])]
          obtain ⟨k₁, k₂, -, rfl, hk, -⟩ := sep_iff.mp hRR
          have := locked_some hk
          cases e : k₁ (Spin.tok l) with
          | some w => simp [union_some e]
          | none => simp [e] at this
        exact disjoint_some hd htok this
      · -- taken: release
        refine ⟨Heap.empty, Heap.union (Heap.single l 0) h, disjoint_empty _, ?_,
          Or.inl ⟨h, sep_comm hh, disjoint_single_left hhl, rfl⟩, hQ _, fun e => by cases e⟩
        rw [union_empty_left]
        funext x
        simp only [Lab.updH, Lab.wval, at_rdi, hl, hnew]
        by_cases hx : x = l
        · subst hx; simp [union_apply, single_apply]
        · have : l ≠ x := Ne.symm hx
          simp only [this, ite_false, Option.none_or]
          rw [union_none (by simp [single_apply, hx])]
          cases e : h x with
          | some w => simp [union_some e]
          | none => rw [union_none e]; simp [single_apply, hx]

theorem safe_unlock_gen {m : Mode} {l : Nat} {R : HProp} {rs : Regs} {h : Heap}
    (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h) :
    Csl.Safe (Spin.inv l R) (fun _ => hemp)
      (.seq Spin.zero (.seq (.rmw .rax m 4 .xchg (at_ .rdi 0) (.reg .rax)) .skip)) rs h := by
  apply safe_seq
  apply safe_assign
  apply safe_seq
  refine safe_xchg0 (by simpa [Regs.set] using hl) (by simp [Regs.set, zero_eval]) hh
    (fun rs' => safe_skip rfl)

theorem spin_unlock_spec (l : Nat) (R J : HProp) (L : Nat) (rs : Regs) (h : Heap)
    (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h) :
    Csl.Safe (Spin.inv l R ∗ J) (fun _ => hemp) (Spin.unlockCert.body L) rs h := by
  rw [unlock_body]; exact safe_inv_frame (safe_unlock_gen hl hh)

theorem spin_unlockSc_spec (l : Nat) (R J : HProp) (L : Nat) (rs : Regs) (h : Heap)
    (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h) :
    Csl.Safe (Spin.inv l R ∗ J) (fun _ => hemp) (Spin.unlockScCert.body L) rs h := by
  rw [unlockSc_body]; exact safe_inv_frame (safe_unlock_gen hl hh)

/-! ## Static facts -/

theorem spin_init_dom (l a : Nat) (h : (Spin.init l a).isSome) : l ≤ a ∧ a < l + 8 := by
  by_cases h1 : a = l
  · omega
  · by_cases h2 : a = l + 4
    · omega
    · exfalso
      simp [Spin.init, Spin.tok, union_none, single_apply, h1, h2] at h

theorem spin_init_inv (l : Nat) (R : HProp) (hR : Heap) (hr : R hR)
    (d : Heap.Disjoint (Spin.init l) hR) : Spin.inv l R (Heap.union (Spin.init l) hR) := by
  obtain ⟨d1, d2⟩ := disjoint_union_left.mp d
  refine Or.inl ⟨Heap.union (Heap.single (Spin.tok l) 0) hR,
    sep_iff.mpr ⟨_, hR, d2, rfl, ⟨0, rfl⟩, hr⟩, ?_, union_assoc _ _ _⟩
  exact disjoint_union_right.mpr ⟨disjoint_single (Ne.symm (tok_ne l)), d1⟩

theorem spin_locked_excl (l : Nat) (h : Heap) : ¬ (Spin.locked l ∗ Spin.locked l) h := by
  intro H
  obtain ⟨h₁, h₂, d, -, a, b⟩ := sep_iff.mp H
  exact disjoint_some d (locked_some a) (locked_some b)

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex

namespace Silmaril.X86.Concurrency.Cir.Mutex

open Silmaril.Proofs.X86.Concurrency.Cir.Mutex

/-- **The spin mutex of `mutex.c` as an `Iface`**: `mutex_lock` (`spin_lock` bytes) and
`mutex_unlock` (`xchg`), with the lock invariant around the token and the resource. -/
def spinMutex : Iface where
  size := 8
  init := Spin.init
  inv := Spin.inv
  locked := Spin.locked
  lockCode := Prim.SpinLock.cert.body
  unlockCode := Spin.unlockCert.body
  init_dom := spin_init_dom
  init_inv := spin_init_inv
  locked_excl := spin_locked_excl
  lock_spec := spin_lock_spec
  unlock_spec := spin_unlock_spec

/-- The same mutex with `mutex_unlock_sc` (C11 `store(seq_cst)`, the same bytes). -/
def spinMutexSc : Iface := { spinMutex with
  unlockCode := Spin.unlockScCert.body
  unlock_spec := spin_unlockSc_spec }

end Silmaril.X86.Concurrency.Cir.Mutex
