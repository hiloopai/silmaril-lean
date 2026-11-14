module

public import Silmaril.Proofs.X86.Concurrency.Cir.Chan.DropUnits

/-!
# Dropping plain loads from a choice of traces

`Drops P l l'`: `l'` is `l` with some unlocked loads removed, each satisfying `P`
(for us: having a twin in `l'`). `cand_drops`: a candidate (under SC, TSO or XL) of a choice
of traces gives one of the traces with those loads dropped, with the same final state.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Chan.Drop

open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Byte units Test finalOf Model)
open Silmaril.X86.MemEvent (Kind)

/-- `l'` is `l` with some unlocked loads satisfying `P` removed. -/
inductive Drops (P : XAct → Prop) : List XAct → List XAct → Prop
  | nil : Drops P [] []
  | keep (a : XAct) {l l' : List XAct} : Drops P l l' → Drops P (a :: l) (a :: l')
  | drop (a : XAct) {l l' : List XAct} : a.ev.kind = .load → a.ev.locked = false → P a →
      Drops P l l' → Drops P (a :: l) l'

namespace Drops
variable {P : XAct → Prop}

theorem refl : ∀ l : List XAct, Drops P l l
  | [] => .nil
  | a :: l => .keep a (refl l)

theorem sublist {l l' : List XAct} (h : Drops P l l') : l'.Sublist l := by
  induction h with
  | nil => exact .slnil
  | keep a _ ih => exact ih.cons_cons a
  | drop a _ _ _ _ ih => exact ih.cons a

theorem length_le {l l' : List XAct} (h : Drops P l l') : l'.length ≤ l.length :=
  h.sublist.length_le

/-- A proper drop removes one load first. -/
theorem split {l l' : List XAct} (h : Drops P l l') (hne : l ≠ l') :
    ∃ as1 d as2, l = as1 ++ d :: as2 ∧ d.ev.kind = .load ∧ d.ev.locked = false ∧ P d ∧
      Drops P (as1 ++ as2) l' := by
  induction h with
  | nil => exact absurd rfl hne
  | keep a h ih =>
    obtain ⟨as1, d, as2, rfl, h1, h2, h3, h4⟩ := ih (fun he => hne (by rw [he]))
    exact ⟨a :: as1, d, as2, rfl, h1, h2, h3, .keep a h4⟩
  | drop a h1 h2 h3 h => exact ⟨[], a, _, rfl, h1, h2, h3, h⟩

theorem mono {P Q : XAct → Prop} (hPQ : ∀ a, P a → Q a) {l l' : List XAct} (h : Drops P l l') :
    Drops Q l l' := by
  induction h with
  | nil => exact .nil
  | keep a _ ih => exact .keep a ih
  | drop a h1 h2 h3 _ ih => exact .drop a h1 h2 (hPQ a h3) ih

theorem append {P : XAct → Prop} {l₁ l₁' l₂ l₂' : List XAct} (h₁ : Drops P l₁ l₁')
    (h₂ : Drops P l₂ l₂') : Drops P (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | keep a _ ih => exact .keep a ih
  | drop a h1 h2 h3 _ ih => exact .drop a h1 h2 h3 ih

end Drops

/-- A one-step trace with given actions and final core. -/
def mkTrace (acts : List XAct) (fin : Silmaril.X86.State) : XTrace := ⟨[⟨acts, fin⟩], fin⟩

theorem mkTrace_acts (acts : List XAct) (fin : Silmaril.X86.State) : (mkTrace acts fin).acts = acts := by
  simp [mkTrace, Silmaril.X86.Litmus.Trace.acts]

theorem finalOf_congr {trs trs' : List XTrace} (hl : trs.length = trs'.length)
    (hf : ∀ k (h : k < trs.length) (h' : k < trs'.length), trs[k].final = trs'[k].final)
    (m : Nat → Option Byte) : finalOf trs m = finalOf trs' m := by
  simp only [finalOf]
  congr 1
  funext k r
  by_cases hk : k < trs.length
  · rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (hl ▸ hk)]
    simp [hf k hk (hl ▸ hk)]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem units_congr {trs trs' : List XTrace} (h : trs.map (fun tr => tr.acts) = trs'.map (fun tr => tr.acts)) :
    units trs = units trs' := by
  rw [units_eq, units_eq, h]

/-- Unlocked loads. -/
def LoadsOk (trs : List XTrace) : Prop :=
  ∀ tr ∈ trs, ∀ a ∈ tr.acts, a.ev.kind = .load → a.ev.locked = false

/-- The total number of actions. -/
def size (trs : List XTrace) : Nat := (trs.map fun tr => tr.acts.length).sum

theorem le_sum_of_mem' : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | b :: l, a, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := le_sum_of_mem' h; simp; omega

theorem Drops.nil_inv {P : XAct → Prop} {l : List XAct} (h : Drops P [] l) : l = [] := by
  cases h; rfl

theorem sum_set_lt : ∀ (l : List Nat) (k v : Nat) (hk : k < l.length), v < l[k] →
    (l.set k v).sum < l.sum
  | a :: l, 0, v, _, h => by simp at h ⊢; omega
  | a :: l, k + 1, v, hk, h => by
    simp only [List.getElem_cons_succ] at h
    have := sum_set_lt l k v (by simpa using hk) h
    simp only [List.set_cons_succ, List.sum_cons]; omega

theorem size_set_lt {trs : List XTrace} {k : Nat} (hk : k < trs.length) {tr : XTrace}
    (h : tr.acts.length < trs[k].acts.length) : size (trs.set k tr) < size trs := by
  simp only [size]
  rw [List.map_set]
  exact sum_set_lt _ _ _ (by simpa using hk) (by simpa using h)

theorem cand_same (t : Test) {M : Exec → Prop} {trs trs' : List XTrace} (hl : trs.length = trs'.length)
    (hk : ∀ k (h : k < trs.length) (h' : k < trs'.length), trs[k].final = trs'[k].final ∧
      trs[k].acts = trs'[k].acts) {fin} (h : Cand t trs M fin) : Cand t trs' M fin := by
  have hu : units trs = units trs' := by
    apply units_congr
    apply List.ext_getElem (by simp [hl])
    intro k h1 h2
    simp only [List.getElem_map]
    exact (hk k (by simpa using h1) (by simpa using h2)).2
  obtain ⟨x, h1, h2, h3, h4, h5, rfl⟩ := h
  refine ⟨x, hu ▸ h1, hu ▸ h2, h3, hu ▸ h4, h5, ?_⟩
  simp only [Silmaril.X86.MemoryModel.Litmus.finalAx]
  exact finalOf_congr hl (fun k h h' => (hk k h h').1) _

/-- **Dropping twinned plain loads keeps a candidate.** -/
theorem cand_drops (t : Test) (M : Model) :
    ∀ (n : Nat) (trs trs' : List XTrace), size trs ≤ n → trs.length = trs'.length →
      (∀ k (h : k < trs.length) (h' : k < trs'.length), trs[k].final = trs'[k].final ∧
        Drops (fun a => ∃ b ∈ trs'[k].acts, b.ev = a.ev) trs[k].acts trs'[k].acts) →
      LoadsOk trs → ∀ {fin}, Cand t trs M.Holds fin → Cand t trs' M.Holds fin := by
  intro n
  induction n with
  | zero =>
    intro trs trs' hs hl hk _ fin h
    refine cand_same t hl (fun k h1 h2 => ⟨(hk k h1 h2).1, ?_⟩) h
    have hd := (hk k h1 h2).2
    have : trs[k].acts = [] := by
      have : trs[k].acts.length ≤ size trs := by
        simp only [size]
        have := le_sum_of_mem' (List.mem_map_of_mem (f := fun tr : XTrace => tr.acts.length)
          (List.getElem_mem h1))
        exact this
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [this] at hd ⊢
    exact hd.nil_inv.symm
  | succ n ih =>
    intro trs trs' hs hl hk hlo fin h
    by_cases hall : ∀ k (h : k < trs.length) (h' : k < trs'.length), trs[k].acts = trs'[k].acts
    · exact cand_same t hl (fun k h1 h2 => ⟨(hk k h1 h2).1, hall k h1 h2⟩) h
    · simp only [not_forall] at hall
      obtain ⟨k, h1, h2, hne⟩ := hall
      obtain ⟨hfk, hdk⟩ := hk k h1 h2
      obtain ⟨as1, d, as2, heq, hd, hdl, ⟨b, hb, hbe⟩, hrest⟩ := hdk.split hne
      set trs₁ := trs.set k (mkTrace (as1 ++ as2) trs[k].final) with htrs₁
      have hL1 : trs₁.map (fun tr => tr.acts) = (trs.map fun tr => tr.acts).set k (as1 ++ as2) := by
        rw [htrs₁, List.map_set, mkTrace_acts]
      have hlen1 : trs₁.length = trs.length := by simp [htrs₁]
      have hsz : size trs₁ < size trs := size_set_lt h1 (by
        rw [mkTrace_acts, heq]; simp)
      obtain ⟨UA, UB, UC, f, hu, hu', H⟩ := units_drop (trs.map fun tr => tr.acts) k as1 as2 d
        (by simp [h1, heq]) hd hdl
        ⟨k, as1 ++ as2, by simp [h1], b, hrest.sublist.subset hb, hbe⟩
        (by
          intro k' as hk' a ha hka
          simp only [List.getElem?_map, Option.map_eq_some_iff] at hk'
          obtain ⟨tr, htr, rfl⟩ := hk'
          exact hlo tr (List.mem_of_getElem? htr) a ha hka)
      have h₁ : Cand t trs₁ M.Holds fin := by
        refine cand_drop t M (by rw [units_eq]; exact hu) (by rw [units_eq, hL1]; exact hu') H ?_ h
        intro m
        refine finalOf_congr hlen1 (fun k' h h' => ?_) m
        simp only [htrs₁, List.getElem_set]
        split
        · subst_vars; rfl
        · rfl
      refine ih trs₁ trs' (by omega) (by rw [hlen1, hl]) ?_ ?_ h₁
      · intro k' g1 g2
        have g1' : k' < trs.length := by rwa [hlen1] at g1
        obtain ⟨hf', hd'⟩ := hk k' g1' g2
        simp only [htrs₁, List.getElem_set]
        split
        · subst_vars; exact ⟨by rw [hfk]; rfl, by rw [mkTrace_acts]; exact hrest⟩
        · exact ⟨hf', hd'⟩
      · intro tr htr a ha hka
        rw [htrs₁] at htr
        rcases List.mem_or_eq_of_mem_set htr with htr | rfl
        · exact hlo tr htr a ha hka
        · rw [mkTrace_acts] at ha
          apply hlo trs[k] (List.getElem_mem h1) a _ hka
          rw [heq]; simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto

end Silmaril.Proofs.X86.Concurrency.Cir.Chan.Drop
