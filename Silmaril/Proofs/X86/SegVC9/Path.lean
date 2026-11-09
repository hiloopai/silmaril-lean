module

public import Silmaril.X86.SegVC9.Defs
public import Silmaril.X86.SegVC.Tactic
public import Silmaril.X86.FnContract.Defs

/-!
# Segment VCs on `Ext9`: proofs

Proofs behind `Silmaril.X86.SegVC9.Thms`:

* `onOk_retire_pushWord`: a `push` with its successor memory named by a `storeN` equation;
* `nextAt_exits_mem`, `nextAt_exits_not_mem`: arriving at an offset of a segment with exits;
* `path_runsIn`, `seg_runsIn`: **segment VCs run inside the code.** `SegVC.path` turns a
  segment VC into a `Reaches` run; for a segment with no cut points, contracted calls or
  summaries, on an instance whose decoder rejects `[]`, the run is a
  `FnContract.RunsIn I (InCode I base code.length)`: every step is taken from a state whose
  program counter lies inside the code.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SegVC9

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded retire)
open Silmaril.X86.SegVC
open Silmaril.X86.SegVC9 (segStops)
open Silmaril.X86.FnContract (RunsIn InCode)

theorem onOk_retire_pushWord {P : State → Memory → Prop} {next : Word} {s : State}
    {memory : Memory} {v : Word} :
    onOk P (retire next (Silmaril.X86.pushWord s memory v)) ↔
      memory.Permitted .write (s.read .rsp - 8#64).toNat 8 ∧
        ∀ after, Silmaril.X86.Ext.storeN memory (s.read .rsp - 8#64) 8 v = some after →
          P { s.write .rsp (s.read .rsp - 8#64) with rip := next } after := by
  have hw : Silmaril.X86.pushWord s memory v =
      (Silmaril.X86.Ext.storeN memory (s.read .rsp - 8#64) 8 v).map
        fun after => (s.write .rsp (s.read .rsp - 8#64), after) := by
    simp only [Silmaril.X86.pushWord, Silmaril.X86.Ext.storeN, Silmaril.X86.Ext.leBytes_eight]
  rw [hw]
  exact onOk_retire_storeN

variable {σ : Type} {I : Isa σ}

theorem lookup_segStops_mem {exits : List Nat} {Q : σ → Prop} {o : Nat} (h : o ∈ exits) :
    (segStops exits Q).lookup o = some Q := by
  induction exits with
  | nil => cases h
  | cons e es ih =>
    simp only [segStops, List.map_cons, List.lookup_cons] at ih ⊢
    by_cases he : o = e
    · simp [he]
    · have hb : (o == e) = false := by simpa using he
      rw [hb]
      exact ih (by simpa [he] using h)

theorem lookup_segStops_not_mem {exits : List Nat} {Q : σ → Prop} {o : Nat} (h : o ∉ exits) :
    (segStops exits Q).lookup o = none := by
  induction exits with
  | nil => rfl
  | cons e es ih =>
    simp only [segStops, List.map_cons, List.lookup_cons] at ih ⊢
    have he : o ≠ e := fun he => h (he ▸ List.mem_cons_self)
    have hb : (o == e) = false := by simpa using he
    rw [hb]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

theorem nextAt_exits_mem {exits : List Nat} {Q : σ → Prop} {μ : Option Nat}
    {cont : Nat → σ → Prop} {o : Nat} {s : σ} (h : o ∈ exits) :
    nextAt [] (segStops exits Q) μ cont o s = Q s := by
  simp only [nextAt, List.lookup_nil, lookup_segStops_mem h]

theorem nextAt_exits_not_mem {exits : List Nat} {Q : σ → Prop} {μ : Option Nat}
    {cont : Nat → σ → Prop} {o : Nat} {s : σ} (h : o ∉ exits) :
    nextAt [] (segStops exits Q) μ cont o s = cont o s := by
  simp only [nextAt, List.lookup_nil, lookup_segStops_not_mem h]

/-- A listed instruction has positive length when the decoder rejects `[]`. -/
theorem len_pos (h0 : I.decode [] = none) {code : List Byte} {o l : Nat} {i : I.Instr}
    (h : I.decode ((code.drop o).take l) = some (i, l)) : 0 < l := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    simp [h0] at h
  · exact hl

/-- A lookup in a list of pairs with one common second component. -/
theorem lookup_map_const {α : Type} {e : Nat} {q a : α} :
    ∀ {es : List Nat}, (es.map fun x => (x, a)).lookup e = some q → q = a
  | [], h => by simp at h
  | x :: es, h => by
    simp only [List.map_cons, List.lookup_cons] at h
    split at h
    · exact (Option.some.inj h).symm
    · exact lookup_map_const h

theorem path_runsIn (h0 : I.decode [] = none) {code : List Byte} {L : Listing I}
    {stops : List (Nat × (σ → Prop))} {base : Word} (hv : L.valid I code = true)
    (μ : Option Nat) :
    ∀ (k o : Nat) (s : σ), wpN I code L [] stops [] [] base μ k o s → I.live s →
      Loaded (I.mem s) base code → (I.core s).rip = base + BitVec.ofNat 64 o →
      ∃ o' q t, stops.lookup o' = some q ∧ q t ∧
        RunsIn I (InCode I base code.length) s t := by
  intro k
  induction k with
  | zero => intro o s h; exact absurd h id
  | succ k ih =>
    intro o s h hlv hl hrip
    simp only [wpN, List.lookup_nil] at h
    cases hi : L.lookup o with
    | none => rw [hi] at h; exact h.elim
    | some il =>
      obtain ⟨i, l⟩ := il
      rw [hi] at h
      obtain ⟨hdec, hfit⟩ := valid_entry hv hi
      have hin : InCode I base code.length s := ⟨o, by have := len_pos h0 hdec; omega, hrip⟩
      simp only [wpI] at h
      cases hx : I.exec i (I.core s) (I.mem s) l with
      | ok c m =>
        rw [hx] at h
        simp only [onOk, after, List.lookup_nil] at h
        obtain ⟨hok, hl', hn⟩ := h
        have hs := I.step_of hlv hl hrip hfit hdec hx hok
        have hlv' := I.live_step hlv hs
        unfold nextAt at hn
        simp only [List.lookup_nil] at hn
        cases hq : stops.lookup (offOf base c) with
        | some q =>
          rw [hq] at hn
          exact ⟨_, q, _, hq, hn, .step hin hs (.refl _)⟩
        | none =>
          rw [hq] at hn
          have hrip' : (I.core (I.upd s c m)).rip =
              base + BitVec.ofNat 64 (offOf base c) := by
            rw [I.core_upd]; exact rip_offOf base c
          rw [← I.mem_upd s c m] at hl'
          obtain ⟨o', q, t, hq', ht, hr⟩ := ih _ _ hn hlv' hl' hrip'
          exact ⟨o', q, t, hq', ht, .step hin hs hr⟩
      | dataFault => rw [hx] at h; exact h.elim
      | divideError => rw [hx] at h; exact h.elim
      | undefinedCondition _ => rw [hx] at h; exact h.elim
      | trap => rw [hx] at h; exact h.elim

theorem seg_runsIn (h0 : I.decode [] = none) {code : List Byte} {L : Listing I}
    {exits : List Nat} {base : Word} {Q : σ → Prop} (hv : L.valid I code = true)
    {μ : Option Nat} {k o : Nat} {s : σ}
    (h : wpN I code L [] (segStops exits Q) [] [] base μ k o s) (hlv : I.live s)
    (hl : Loaded (I.mem s) base code) (hrip : (I.core s).rip = base + BitVec.ofNat 64 o) :
    ∃ t, RunsIn I (InCode I base code.length) s t ∧ Q t := by
  obtain ⟨_, q, t, hq, ht, hr⟩ := path_runsIn h0 hv μ k o s h hlv hl hrip
  exact ⟨t, hr, lookup_map_const hq ▸ ht⟩

end Silmaril.Proofs.X86.SegVC9
