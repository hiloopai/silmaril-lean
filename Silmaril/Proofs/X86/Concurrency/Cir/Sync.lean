module

public import Silmaril.X86.Concurrency.Cir.Sync.Defs
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms

/-!
# CIR spawn and join: proofs

The synchronisation edges `Exec.swHb` are paths of each model's own
global order, so adding them changes no model (`scS_iff`, `tsoS_iff`, `xlS_iff`). The
operational lemmas: a control event is an `rmw`, which needs an empty buffer; a join needs the
end byte to hold `1`; and, when only the thread operations touch the end byte, a `1` there
means the child has finished and drained (`end_finished`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Sync

open Relation
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Axiomatic.BRel (union_iff inter_iff seq_elim)
open Silmaril.X86.Concurrency.Cir

/-! ## Synchronisation edges are model edges -/

theorem path3 {n : Nat} {G : BRel n} {a w r b : Fin n} (h1 : a = w ∨ G a w = true)
    (h2 : G w r = true) (h3 : r = b ∨ G r b = true) : TransGen G.Holds a b := by
  have hwb : TransGen G.Holds w b := by
    rcases h3 with rfl | h3
    · exact .single h2
    · exact .tail (.single h2) h3
  rcases h1 with rfl | h1
  · exact hwb
  · exact .head h1 hwb

/-- The pieces of a `swHb` edge. -/
theorem swHb_elim {x : Exec} {a b : Fin x.n} (h : x.swHb a b = true) :
    (x.ev a).isM = true ∧ (x.ev b).isM = true ∧ ∃ w r,
      (a = w ∨ x.po a w = true) ∧ x.rfe w r = true ∧ (x.ev w).isA = true ∧ (x.ev r).isA = true ∧
        (r = b ∨ x.po r b = true) := by
  simp only [Exec.swHb, Bool.and_eq_true] at h
  obtain ⟨⟨ha, hb⟩, h⟩ := h
  obtain ⟨r, h1, h3⟩ := seq_elim h
  obtain ⟨w, h1, h2⟩ := seq_elim h1
  simp only [Exec.sw, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨hrfe, hwA⟩, hrA⟩, -⟩, -⟩ := h2
  simp only [Exec.poq, Bool.or_eq_true, decide_eq_true_eq] at h1 h3
  exact ⟨ha, hb, w, r, h1, hrfe, hwA, hrA, h3⟩

theorem rfe_wr {x : Exec} {w r : Fin x.n} (h : x.rfe w r = true) :
    (x.ev w).isW = true ∧ (x.ev r).isR = true ∧ x.rfR w r = true := by
  have h' := (inter_iff.mp h).1
  simp only [Exec.rfR, Bool.and_eq_true] at h'
  exact ⟨h'.1.1, h'.1.2, (inter_iff.mp h).1⟩

theorem isM_cases {e : Ev} (h : e.isM = true) : e.isR = true ∨ e.isW = true := by
  simpa [Ev.isM] using h

theorem isA_isM {e : Ev} (h : e.isA = true) : e.isM = true := by
  simp only [Ev.isA, Bool.and_eq_true] at h; exact h.2

/-- **TSO**: every `swHb` edge is a `ghb` path (`ppo; rfe; ppo`). -/
theorem swHb_ghb {x : Exec} {a b : Fin x.n} (h : x.swHb a b = true) :
    TransGen x.ghb.Holds a b := by
  obtain ⟨ha, hb, w, r, h1, hrfe, -, -, h3⟩ := swHb_elim h
  obtain ⟨hw, hr, -⟩ := rfe_wr hrfe
  have hppo : ∀ {u v : Fin x.n}, x.ppo u v = true → x.ghb u v = true := fun hu => by
    simp [Exec.ghb, BRel.union, hu]
  refine path3 (G := x.ghb) (w := w) (r := r) ?_ ?_ ?_
  · rcases h1 with h1 | h1
    · exact .inl h1
    · refine .inr (hppo ?_)
      simp only [Exec.ppo, h1, hw, Bool.true_and, Bool.and_true, Bool.or_eq_true]
      rcases isM_cases ha with h' | h'
      · exact .inr (by simp [h', Ev.isM, hw])
      · exact .inl h'
  · have : x.comGhb w r = true :=
      BRel.seq_of_left (fun c => x.sm_refl c) (union_iff.mpr (.inl hrfe))
    simp [Exec.ghb, BRel.union, this]
  · rcases h3 with h3 | h3
    · exact .inl h3
    · exact .inr (hppo (by simp [Exec.ppo, h3, hr, hb]))

/-- **XL**: every `swHb` edge is a `ghbXl` path (`lockXl; rfe; lockXl`). -/
theorem swHb_ghbXl {x : Exec} {a b : Fin x.n} (h : x.swHb a b = true) :
    TransGen x.ghbXl.Holds a b := by
  obtain ⟨ha, hb, w, r, h1, hrfe, hwA, hrA, h3⟩ := swHb_elim h
  have hlock : ∀ {u v : Fin x.n}, x.lockXl u v = true → x.ghbXl u v = true := fun hu => by
    simp [Exec.ghbXl, BRel.union, hu]
  refine path3 (G := x.ghbXl) (w := w) (r := r) ?_ ?_ ?_
  · rcases h1 with h1 | h1
    · exact .inl h1
    · exact .inr (hlock (by simp [Exec.lockXl, ha, isA_isM hwA, h1, hwA]))
  · have : x.comGhbXl w r = true :=
      BRel.seq_of_left (fun c => by simp [Exec.smT]) (union_iff.mpr (.inl hrfe))
    simp [Exec.ghbXl, BRel.union, this]
  · rcases h3 with h3 | h3
    · exact .inl h3
    · exact .inr (hlock (by simp [Exec.lockXl, hb, isA_isM hrA, h3, hrA]))

/-- **SC**: every `swHb` edge is a `po | com;sm` path. -/
theorem swHb_sc {x : Exec} {a b : Fin x.n} (h : x.swHb a b = true) :
    TransGen x.scRel.Holds a b := by
  obtain ⟨-, -, w, r, h1, hrfe, -, -, h3⟩ := swHb_elim h
  have hpo : ∀ {u v : Fin x.n}, x.po u v = true → x.scRel u v = true := fun hu => by
    simp [Exec.scRel, BRel.union, hu]
  refine path3 (G := x.scRel) (h1.imp id hpo) ?_ (h3.imp id hpo)
  have : (x.com.seq x.sm) w r = true :=
    BRel.seq_of_left (fun c => x.sm_refl c) (x.rfe_com hrfe)
  simp [Exec.scRel, BRel.union, this]

theorem union_path {n : Nat} {G H : BRel n} (hH : ∀ a b, H a b = true → TransGen G.Holds a b) :
    ∀ a b, (G.union H) a b = true → TransGen G.Holds a b := by
  intro a b h
  rcases union_iff.mp h with h | h
  · exact .single h
  · exact hH a b h

theorem scS_iff (x : Exec) : x.ScS ↔ x.Sc :=
  ⟨fun h => h.1, fun h => ⟨h, BRel.acyclic_mono (union_path fun _ _ => swHb_sc) h.2⟩⟩

theorem tsoS_iff (x : Exec) : x.TsoS ↔ x.Tso :=
  ⟨fun h => h.1, fun h => ⟨h, BRel.acyclic_mono (union_path fun _ _ => swHb_ghb) h.2.2⟩⟩

theorem xlS_iff (x : Exec) : x.XlS ↔ x.Xl :=
  ⟨fun h => h.1, fun h => ⟨h, BRel.acyclic_mono (union_path fun _ _ => swHb_ghbXl) h.2.2.2⟩⟩

/-! ## Operational TSO -/

namespace Op

open Silmaril.X86.MemoryModel.Tso
open Silmaril.X86.MemoryModel.Litmus (ACfg AStep)
open Silmaril.X86.MemoryModel.OpAx (ThreadsOk)

/-- A locked read-modify-write step needs the issuing thread's buffer empty. -/
theorem rmw_drained {s s' : XState Nat} {i a : Nat} {old new : List Byte}
    (h : XStep s (.rmw i a old new) s') : s.buffer i = [] := by
  cases h; assumption

/-- A one-byte `rmw` reading `o` needs memory to hold `o`. -/
theorem rmw_reads {s s' : XState Nat} {i a : Nat} {o n : Byte}
    (h : XStep s (.rmw i a [o] [n]) s') : s.memory a = some o := by
  cases h
  rename_i _ hm _
  simp only [List.length_singleton, readMem] at hm
  split at hm
  · rename_i b bs hb _; simp at hm; rw [hb, hm.1]
  · cases hm

theorem writeMem_outside {m : Silmaril.X86.MemoryModel.Tso.Mem} {a y : Nat} {bs : List Byte} (h : ¬ (a ≤ y ∧ y < a + bs.length)) :
    writeMem m a bs y = m y := by
  simp only [writeMem, entryByte]
  split
  · rename_i hay
    have : bs.length ≤ y - a := by omega
    simp [List.getElem?_eq_none this]
  · simp

theorem writeMem_one {m : Silmaril.X86.MemoryModel.Tso.Mem} {a : Nat} {b : Byte} : writeMem m a [b] a = some b := by
  simp [writeMem, entryByte]

/-- The invariant: the remaining events are suffixes of the program's, buffered entries avoid
end byte `t`, and a `1` there means thread `t` has finished and drained. -/
structure CtlInv (es : List (List (XEvent Nat))) (t : Nat) (c : ACfg) : Prop where
  suffix : ∀ (i : Nat) (l' : List (XEvent Nat)), c.rest[i]? = some l' → ∃ (l pre : List (XEvent Nat)), es[i]? = some l ∧ l = pre ++ l'
  buf : ∀ (j : Nat), ∀ p ∈ c.st.buffer j, ¬ (p.1 ≤ endAddr t ∧ endAddr t < p.1 + p.2.length)
  done : c.st.memory (endAddr t) = some 1 → c.rest[t]? = some [] ∧ c.st.buffer t = []

theorem covers_of {e : XEvent Nat} {a n : Nat} (hf : evFoot e = some (a, n)) {y : Nat}
    (h : a ≤ y ∧ y < a + n) : evCovers e y := ⟨a, n, hf, h.1, h.2⟩

theorem inv_step {es : List (List (XEvent Nat))} {t : Nat} (hok : CtlOk es t) (htag : ThreadsOk es)
    {c c' : ACfg} (hc : CtlInv es t c) (h : AStep c c') : CtlInv es t c' := by
  cases h with
  | flush rest s s' hfl =>
    cases hfl with
    | head j a bs rst hold =>
      have hav := hc.buf j (a, bs) (by rw [hold]; exact List.mem_cons_self ..)
      refine ⟨hc.suffix, ?_, ?_⟩
      · intro k p hp
        by_cases hk : k = j
        · subst hk
          simp only [Function.update_self] at hp
          exact hc.buf k p (by rw [hold]; exact List.mem_cons_of_mem _ hp)
        · simp only [Function.update_of_ne hk] at hp
          exact hc.buf k p hp
      · intro h3
        simp only at h3
        rw [writeMem_outside hav] at h3
        obtain ⟨hr, hb⟩ := hc.done h3
        refine ⟨hr, ?_⟩
        by_cases hk : t = j
        · subst hk; rw [hold] at hb; cases hb
        · simp only [Function.update_of_ne hk]; exact hb
  | ev rest s s' i e es' hi hs =>
    obtain ⟨l, pre, hl, hpre⟩ := hc.suffix i _ hi
    have hk : l[pre.length]? = some e := by simp [hpre]
    have hthr : e.thread = i := htag i l hl e (by rw [hpre]; simp)
    have hsuf : ∀ (k : Nat) (l' : List (XEvent Nat)), (rest.set i es')[k]? = some l' →
        ∃ (l pre : List (XEvent Nat)), es[k]? = some l ∧ l = pre ++ l' := by
      intro k l' hk'
      by_cases hki : k = i
      · subst hki
        rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1] at hk'
        cases hk'
        exact ⟨l, pre ++ [e], hl, by simp [hpre]⟩
      · rw [List.getElem?_set_ne (Ne.symm hki)] at hk'
        exact hc.suffix k l' hk'
    -- thread `t` has not finished if it is the one stepping
    have hnt : i = t → rest[t]? ≠ some [] := by
      intro hit; subst hit; rw [hi]; simp
    have hrest_t : i ≠ t → (rest.set i es')[t]? = rest[t]? := fun hit =>
      List.getElem?_set_ne hit
    cases hs with
    | load j a bs hv =>
      refine ⟨hsuf, hc.buf, fun h3 => ?_⟩
      obtain ⟨hr, hb⟩ := hc.done h3
      have hit : i ≠ t := fun hit => hnt hit hr
      exact ⟨by rw [hrest_t hit]; exact hr, hb⟩
    | fence j hemp =>
      refine ⟨hsuf, hc.buf, fun h3 => ?_⟩
      obtain ⟨hr, hb⟩ := hc.done h3
      have hit : i ≠ t := fun hit => hnt hit hr
      exact ⟨by rw [hrest_t hit]; exact hr, hb⟩
    | store j a bs =>
      simp only [XEvent.thread] at hthr
      subst hthr
      have hav : ¬ (a ≤ endAddr t ∧ endAddr t < a + bs.length) := by
        intro hcov
        obtain ⟨o, n, he, -⟩ := hok j l hl pre.length _ hk (covers_of rfl hcov)
        cases he
      refine ⟨hsuf, ?_, fun h3 => ?_⟩
      · intro k p hp
        simp only [enqueue] at hp
        by_cases hkj : k = j
        · subst hkj
          simp only [Function.update_self, List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact hc.buf k p hp
          · exact hav
        · simp only [Function.update_of_ne hkj] at hp
          exact hc.buf k p hp
      · obtain ⟨hr, hb⟩ := hc.done h3
        have hit : j ≠ t := fun hit => hnt hit hr
        refine ⟨by rw [hrest_t hit]; exact hr, ?_⟩
        simp only [enqueue, Function.update_of_ne (Ne.symm hit)]
        exact hb
    | rmw j a old new hemp hm hlen =>
      simp only [XEvent.thread] at hthr
      subst hthr
      refine ⟨hsuf, hc.buf, fun h3 => ?_⟩
      simp only at h3
      by_cases hcov : a ≤ endAddr t ∧ endAddr t < a + old.length
      · obtain ⟨o, n, he, h3t⟩ := hok j l hl pre.length _ hk (covers_of rfl hcov)
        cases he
        rw [writeMem_one] at h3
        cases h3
        obtain ⟨rfl, hlast⟩ := h3t rfl
        have hes : es' = [] := by
          have := congrArg List.length hpre
          simp at this
          cases es' with
          | nil => rfl
          | cons _ _ => simp at this; omega
        subst hes
        refine ⟨?_, hemp⟩
        rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]
      · rw [writeMem_outside (by rwa [hlen])] at h3
        obtain ⟨hr, hb⟩ := hc.done h3
        have hit : j ≠ t := fun hit => hnt hit hr
        exact ⟨by rw [hrest_t hit]; exact hr, hb⟩

/-- **A `1` in end byte `t` means child `t` has finished and drained**, in every reachable
configuration, when only the thread operations touch the end byte. -/
theorem end_finished {es : List (List (XEvent Nat))} {t : Nat} (hok : CtlOk es t)
    (htag : ThreadsOk es) {m0 : Silmaril.X86.MemoryModel.Tso.Mem} (h0 : m0 (endAddr t) ≠ some 1) {c : ACfg}
    (hr : Relation.ReflTransGen AStep ⟨es, ⟨m0, fun _ => []⟩⟩ c)
    (h3 : c.st.memory (endAddr t) = some 1) : c.rest[t]? = some [] ∧ c.st.buffer t = [] := by
  have hinv : CtlInv es t c := by
    clear h3
    induction hr with
    | refl =>
      exact ⟨fun i l' h => ⟨l', [], h, rfl⟩, fun _ _ hp => by simp at hp,
        fun h => absurd h h0⟩
    | tail _ hstep ih => exact inv_step hok htag ih hstep
  exact hinv.done h3

end Op

end Silmaril.Proofs.X86.Concurrency.Cir.Sync
