module

public import Silmaril.Proofs.X86.Concurrency.Cir.Chan.DropTraces
public import Silmaril.X86.Concurrency.Cir.Chan.Defs

/-!
# Spin retries add no behaviour (`Cir.Chan.Task.spinRetry`)

A run of a spin `r = load a; while (c r) r = load a` with `k` retries reads `a`
`k + 1` times; the first `k` reads are **failed** (their values only make the condition true
and are overwritten). `spin_run`: every run of `withBound n s` is, with the failed reads
dropped (`LDrop`), a run of `withBound 0 s` with the same final registers. Lowered to memory
actions, a dropped read is an unlocked plain load whose twin (the spin's last read, same
address, size and flavour) is kept, so `Drop.cand_drops` keeps every candidate execution:
`spinRetry`.

Literal addresses are what uniformity (`Prog.uniformB`) is used for: with an address computed
from the spun-on register the failed reads would be at other addresses than the kept one.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Chan.Spin

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Chan
open Silmaril.Proofs.X86.Concurrency.Cir.Chan.Drop
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Model Final AxReach)

/-! ## Label traces with failed reads dropped -/

/-- `t'` is `t` with some reads dropped, each with a **twin** later in `t'` (a read of the same
address, size and flavour). -/
inductive LDrop : List Lab → List Lab → Prop
  | nil : LDrop [] []
  | keep (l : Lab) {t t' : List Lab} : LDrop t t' → LDrop (l :: t) (l :: t')
  | drop (m : Mode) (fl : Flav) (a sz v : Nat) {t t' : List Lab} :
      (∃ m' v', Lab.rd m' fl a sz v' ∈ t') → LDrop t t' → LDrop (.rd m fl a sz v :: t) t'

theorem LDrop.refl : ∀ t : List Lab, LDrop t t
  | [] => .nil
  | l :: t => .keep l (LDrop.refl t)

theorem LDrop.append {t₁ t₁' t₂ t₂' : List Lab} (h₁ : LDrop t₁ t₁') (h₂ : LDrop t₂ t₂') :
    LDrop (t₁ ++ t₂) (t₁' ++ t₂') := by
  induction h₁ with
  | nil => exact h₂
  | keep l _ ih => exact .keep l ih
  | drop m fl a sz v htw _ ih =>
    obtain ⟨m', v', hm⟩ := htw
    exact .drop m fl a sz v ⟨m', v', List.mem_append_left _ hm⟩ ih

/-! ## Spins -/

theorem spinsOnly_seq {s t : Stmt} (h : spinsOnly (.seq s t) = true) :
    (∃ r m sz fl a n c, s = .load r m sz fl a ∧ t = .loop n c (.load r m sz fl a)) ∨
      (spinsOnly s = true ∧ spinsOnly t = true) := by
  by_cases hs : ∃ r m sz fl a n c r' m' sz' fl' a', s = .load r m sz fl a ∧
      t = .loop n c (.load r' m' sz' fl' a')
  · obtain ⟨r, m, sz, fl, a, n, c, r', m', sz', fl', a', rfl, rfl⟩ := hs
    rw [spinsOnly.eq_1] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
    exact Or.inl ⟨_, _, _, _, _, _, _, rfl, rfl⟩
  · right
    rw [spinsOnly.eq_2 s t (fun r m sz fl a n c r' m' sz' fl' a' h1 h2 =>
      hs ⟨r, m, sz, fl, a, n, c, r', m', sz', fl', a', h1, h2⟩)] at h
    simpa only [Bool.and_eq_true] using h

theorem mem_bind {x : Res} {k : Regs → Res} {tr : List Lab} {rs : Regs} :
    (tr, rs) ∈ Res.bind x k ↔ ∃ p ∈ x, ∃ q ∈ k p.2, tr = p.1 ++ q.1 ∧ rs = q.2 := by
  simp only [Res.bind, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨p, hp, q, hq, h1, h2⟩; exact ⟨p, hp, q, hq, h1.symm, h2.symm⟩
  · rintro ⟨p, hp, q, hq, h1, h2⟩; exact ⟨p, hp, q, hq, h1.symm, h2.symm⟩

theorem Regs.set_set (rs : Regs) (r : Reg) (v w : Word) : (rs.set r v).set r w = rs.set r w := by
  funext q; simp only [Regs.set]; split <;> rfl

/-- The retries of a spin, read off a run of its loop: the last value read ends the spin, and
the reads before it are dropped. -/
theorem spin_iter (dom : List Nat) (r : Reg) (m : Mode) (sz : Nat) (fl : Flav) (a : Nat) (c : Expr)
    (rs₀ : Regs) :
    ∀ (k v0 : Nat) (tr : List Lab) (rs' : Regs),
      (tr, rs') ∈ iter (run dom (.load r m sz fl (.lit a))) c k (rs₀.set r (BitVec.ofNat 64 v0)) →
      v0 ∈ pick dom sz →
      ∃ v ∈ pick dom sz, rs' = rs₀.set r (BitVec.ofNat 64 v) ∧ truthy (c.eval rs') = false ∧
        LDrop (.rd m fl (BitVec.ofNat 64 a).toNat sz v0 :: tr) [.rd m fl (BitVec.ofNat 64 a).toNat sz v]
  | 0, v0, tr, rs', h, hv0 => by
    simp only [iter] at h
    split at h
    · simp at h
    · rename_i hc
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨v0, hv0, rfl, by simpa using hc, LDrop.refl _⟩
  | k + 1, v0, tr, rs', h, hv0 => by
    simp only [iter] at h
    split at h
    · rw [mem_bind] at h
      obtain ⟨p, hp, q, hq, rfl, rfl⟩ := h
      simp only [run, List.mem_map] at hp
      obtain ⟨v1, hv1, rfl⟩ := hp
      simp only [Regs.set_set] at hq
      obtain ⟨v, hv, hrs, hc, hd⟩ := spin_iter dom r m sz fl a c rs₀ k v1 q.1 q.2 hq hv1
      refine ⟨v, hv, hrs, hc, ?_⟩
      exact .drop m fl _ sz v0 ⟨m, v, List.mem_singleton_self _⟩ hd
    · rename_i hc
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨v0, hv0, rfl, by simpa using hc, LDrop.refl _⟩

/-- A load reads a literal address on uniform programs. -/
theorem lit_of_onCells {cs : List (Nat × Nat)} {r : Reg} {m : Mode} {sz : Nat} {fl : Flav} {a : Expr}
    (h : (Stmt.load r m sz fl a).onCells cs = true) : ∃ n, a = .lit n := by
  cases a <;> simp [Stmt.onCells] at h ⊢

/-- **Spin retries are dropped reads.** -/
theorem spin_run (dom : List Nat) (n : Nat) (cs : List (Nat × Nat)) :
    ∀ (s : Stmt), spinsOnly s = true → s.onCells cs = true →
      ∀ (rs : Regs) (tr : List Lab) (rs' : Regs), (tr, rs') ∈ run dom (withBound n s) rs →
        ∃ tr0, (tr0, rs') ∈ run dom (withBound 0 s) rs ∧ LDrop tr tr0 := by
  intro s
  induction s with
  | seq s t ihs iht =>
    intro hsp hon rs tr rs' h
    simp only [Stmt.onCells, Bool.and_eq_true] at hon
    rcases spinsOnly_seq hsp with ⟨r, m, sz, fl, a, k, c, rfl, rfl⟩ | ⟨hs, ht⟩
    · obtain ⟨a, rfl⟩ := lit_of_onCells hon.1
      simp only [withBound, run] at h ⊢
      rw [mem_bind] at h
      obtain ⟨p, hp, q, hq, rfl, rfl⟩ := h
      simp only [List.mem_map] at hp
      obtain ⟨v0, hv0, rfl⟩ := hp
      obtain ⟨v, hv, hrs, hc, hd⟩ := spin_iter dom r m sz fl a c rs n v0 q.1 q.2 hq hv0
      refine ⟨[.rd m fl (BitVec.ofNat 64 a).toNat sz v], ?_, hd⟩
      rw [mem_bind]
      refine ⟨([.rd m fl (BitVec.ofNat 64 a).toNat sz v], rs.set r (BitVec.ofNat 64 v)),
        List.mem_map.2 ⟨v, hv, rfl⟩, ([], rs.set r (BitVec.ofNat 64 v)), ?_, by simp, hrs⟩
      simp only [iter, ← hrs, hc]
      simp
    · simp only [withBound, run] at h ⊢
      rw [mem_bind] at h
      obtain ⟨p, hp, q, hq, rfl, rfl⟩ := h
      obtain ⟨t1, ht1, hd1⟩ := ihs hs hon.1 rs p.1 p.2 hp
      obtain ⟨t2, ht2, hd2⟩ := iht ht hon.2 p.2 q.1 q.2 hq
      exact ⟨t1 ++ t2, mem_bind.2 ⟨(t1, p.2), ht1, (t2, q.2), ht2, rfl, rfl⟩, hd1.append hd2⟩
  | ite c s t ihs iht =>
    intro hsp hon rs tr rs' h
    simp only [spinsOnly, Bool.and_eq_true] at hsp
    simp only [Stmt.onCells, Bool.and_eq_true] at hon
    simp only [withBound, run] at h ⊢
    split at h
    · rename_i hc; simp only [hc, ↓reduceIte]; exact ihs hsp.1 hon.1 rs tr rs' h
    · rename_i hc; simp only [hc]; exact iht hsp.2 hon.2 rs tr rs' h
  | loop k c b _ =>
    intro hsp; simp [spinsOnly] at hsp
  | _ =>
    intro _ _ rs tr rs' h
    exact ⟨tr, h, LDrop.refl tr⟩

/-! ## Lowering to actions -/

/-- Twins of dropped reads are kept loads with the same event. -/
theorem ldrop_acts {t t' : List Lab} (h : LDrop t t') :
    Drops (fun a => ∃ b ∈ t'.flatMap Lab.acts, b.ev = a.ev) (t.flatMap Lab.acts) (t'.flatMap Lab.acts) := by
  induction h with
  | nil => exact .nil
  | keep l h ih =>
    simp only [List.flatMap_cons]
    refine (Drops.refl _).append (ih.mono fun a ⟨b, hb, he⟩ => ⟨b, ?_, he⟩)
    exact List.mem_append_right _ hb
  | drop m fl a sz v htw h ih =>
    obtain ⟨m', v', hm⟩ := htw
    simp only [List.flatMap_cons, Lab.acts, List.singleton_append]
    refine .drop _ rfl rfl ⟨ldAct fl a sz v', List.mem_flatMap.2 ⟨_, hm, by simp [Lab.acts]⟩, rfl⟩ ih

/-- An action that is not a locked load. -/
def OkL (a : XAct) : Prop := a.ev.kind = .load → a.ev.locked = false

theorem okL_ld (fl : Flav) (a sz v : Nat) : OkL (ldAct fl a sz v) := fun _ => rfl
theorem okL_st (fl : Flav) (a sz v : Nat) : OkL (stAct fl a sz v) := fun h => by cases h
theorem okL_rmw (a sz o n : Nat) : OkL (rmwAct a sz o n) := fun h => by cases h
theorem okL_fence (k : Silmaril.X86.Atomic9.FenceKind) : OkL (fenceAct k) := fun h => by cases h

/-- No CIR action is a locked load. -/
theorem lab_loads (l : Lab) : ∀ a ∈ l.acts, OkL a := by
  cases l <;> simp only [Lab.acts, ctlAct, endAct] <;> (try split) <;>
    simp only [List.forall_mem_cons, List.forall_mem_append, List.forall_mem_map, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, okL_ld, okL_st, okL_rmw, okL_fence]

theorem thread_acts_loads (th : Thread) (i : Nat) (tr : List Lab) : ∀ a ∈ th.acts i tr, OkL a := by
  intro a ha
  simp only [Thread.acts, List.mem_append, List.mem_flatMap] at ha
  rcases ha with (ha | ⟨l, -, ha⟩) | ha
  · split at ha <;> simp only [List.mem_singleton, List.not_mem_nil] at ha
    subst ha; exact okL_rmw _ _ _ _
  · exact lab_loads l a ha
  · split at ha <;> simp only [List.mem_singleton, List.not_mem_nil] at ha
    subst ha; exact okL_rmw _ _ _ _

theorem thread_drops (th : Thread) (i : Nat) {tr tr0 : List Lab} (h : LDrop tr tr0) :
    Drops (fun a => ∃ b ∈ th.acts i tr0, b.ev = a.ev) (th.acts i tr) (th.acts i tr0) := by
  simp only [Thread.acts]
  refine ((Drops.refl _).append (ldrop_acts h)).append (Drops.refl _) |>.mono ?_
  rintro a ⟨b, hb, he⟩
  exact ⟨b, List.mem_append_left _ (List.mem_append_right _ hb), he⟩

theorem xtrace_acts (th : Thread) (i : Nat) (p : List Lab × Regs) :
    (th.xtrace i p).acts = th.acts i p.1 := by
  simp [Thread.xtrace, Silmaril.X86.Litmus.Trace.acts]

theorem traces_getElem (P : Prog) (n : Nat) (dom : List Nat) (k : Nat) (hk : k < P.threads.length) :
    ((boundProg P n).traces dom)[k]'(by simp [Prog.traces, boundProg, hk]) =
      (run dom (withBound n P.threads[k].body) Regs.zero).map
        ((⟨withBound n P.threads[k].body, P.threads[k].spawned⟩ : Thread).xtrace k) := by
  simp [Prog.traces, boundProg]

theorem traces_length (P : Prog) (n : Nat) (dom : List Nat) :
    ((boundProg P n).traces dom).length = P.threads.length := by
  simp [Prog.traces, boundProg]

theorem forall₂_iff_getElem' {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} :
    List.Forall₂ R l₁ l₂ ↔ l₁.length = l₂.length ∧
      ∀ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i] := by
  rw [List.forall₂_iff_get]; simp only [List.get_eq_getElem]

/-- **Spin retries add no behaviour** (`Cir.Chan.Task.spinRetry`). -/
theorem spinRetry : Task.spinRetry := by
  intro P hu hsp n dom M f hb
  obtain ⟨trs, hF, hc⟩ := hb
  rw [forall₂_iff_getElem'] at hF
  obtain ⟨hlen, hmem⟩ := hF
  rw [traces_length] at hlen
  simp only [Prog.uniformB, Bool.and_eq_true, List.all_eq_true] at hu
  simp only [List.all_eq_true] at hsp
  -- one bound-0 trace per thread
  have hQ : ∀ k : Fin trs.length, ∃ tr0 : XTrace,
      tr0 ∈ ((boundProg P 0).traces dom)[k.val]'(by rw [traces_length]; omega) ∧
      tr0.final = trs[k.val].final ∧
      Drops (fun a => ∃ b ∈ tr0.acts, b.ev = a.ev) trs[k.val].acts tr0.acts := by
    intro k
    have hk : k.val < P.threads.length := by omega
    have h1 := hmem k.val k.2 (by rw [traces_length]; omega)
    rw [traces_getElem P n dom k.val hk, List.mem_map] at h1
    obtain ⟨p, hp, hpe⟩ := h1
    set th := P.threads[k.val] with hth
    obtain ⟨tr0, h0, hd⟩ := spin_run dom n _ th.body (hsp th (List.getElem_mem hk))
      (hu.2 th (List.getElem_mem hk)) Regs.zero p.1 p.2 hp
    refine ⟨(⟨withBound 0 th.body, th.spawned⟩ : Thread).xtrace k (tr0, p.2), ?_, ?_, ?_⟩
    · rw [traces_getElem P 0 dom k.val hk, List.mem_map]
      exact ⟨(tr0, p.2), h0, rfl⟩
    · rw [← hpe]; rfl
    · rw [← hpe, xtrace_acts, xtrace_acts]
      exact thread_drops _ _ hd
  let trs0 := List.ofFn fun k : Fin trs.length => Classical.choose (hQ k)
  have hl0 : trs0.length = trs.length := by simp [trs0]
  have hget : ∀ k (h : k < trs0.length), trs0[k] = Classical.choose (hQ ⟨k, by omega⟩) := by
    intro k h; simp [trs0]
  refine ⟨trs0, ?_, ?_⟩
  · rw [forall₂_iff_getElem']
    refine ⟨by rw [traces_length]; omega, fun k h1 h2 => ?_⟩
    rw [hget k h1]
    exact (Classical.choose_spec (hQ ⟨k, by omega⟩)).1
  · refine cand_drops _ M (size trs) trs trs0 le_rfl hl0.symm (fun k h1 h2 => ?_) ?_ hc
    · rw [hget k h2]
      have := Classical.choose_spec (hQ ⟨k, h1⟩)
      exact ⟨this.2.1.symm, this.2.2⟩
    · intro tr htr a ha hka
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem htr
      have h1 := hmem k hk (by rw [traces_length]; omega)
      rw [traces_getElem P n dom k (by omega), List.mem_map] at h1
      obtain ⟨p, -, hpe⟩ := h1
      rw [← hpe, xtrace_acts] at ha
      exact thread_acts_loads _ _ _ a ha hka

end Silmaril.Proofs.X86.Concurrency.Cir.Chan.Spin
