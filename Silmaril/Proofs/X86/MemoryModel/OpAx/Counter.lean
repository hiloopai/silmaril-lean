module

public import Silmaril.X86.MemoryModel.OpAx.Defs
public import Silmaril.X86.MemoryModel.Xl.Thms
public import Silmaril.Proofs.X86.MemoryModel.OpAx.Timed

/-!
# Partial store forwarding: the cells condition is needed

Program `pfP`: thread 0 stores the byte `1` at address 0, then loads two bytes at address 0;
thread 1 stores the two bytes `2, 1` at address 0. The store-buffer machine forwards byte 0 of
the load from thread 0's buffer and takes byte 1 from memory (`0`), then flushes thread 1's
store and then thread 0's: the load returns `1, 0` and memory ends with `1` at address 0
(`pf_run`). No candidate over the program's units explains this run under any model whose
consistency makes `com` acyclic — SC, x86-TSO and XL (`pf_not_explained`): the load reads byte 0
from thread 0's store `v` and byte 1 from the initial state, so `v →rf R →fr X →co v` with `X`
thread 1's store, coherence-before `v` because `v`'s byte is the final one.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.OpAx.Proofs

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.OpAx
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush Byte Mem readView enqueue xembed
  writeMem)
open Silmaril.X86.MemoryModel.Litmus (ACfg AStep)
open Relation

/-- The program: a one-byte store and a two-byte load in thread 0, a two-byte store in
thread 1, all at address 0. -/
def pfP : List (List (XEvent Nat)) := [[.store 0 0 [1], .load 0 0 [1, 0]], [.store 1 0 [2, 1]]]

/-- Thread 0's store. -/
def pfV : Ev := { tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] }
/-- Thread 0's load. -/
def pfR : Ev := { tid := 0, pos := 2, act := .read, addr := 0, size := 2 }
/-- Thread 1's store. -/
def pfX : Ev := { tid := 1, pos := 0, act := .write, addr := 0, size := 2, data := [2, 1] }

theorem pf_units : progUnits pfP = [(pfV, []), (pfR, [1, 0]), (pfX, [])] := by decide

theorem pf_threadsOk : ThreadsOk pfP := by
  intro i es h ev hev
  match i, h with
  | 0, h =>
    simp only [pfP, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp at hev; rcases hev with rfl | rfl <;> rfl
  | 1, h =>
    simp only [pfP, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp at hev; subst hev; rfl
  | n + 2, h => simp [pfP] at h

theorem pf_not_cells : ¬ ThreadCells pfP := by
  intro h
  have := h 0 [.store 0 0 [1], .load 0 0 [1, 0]] rfl (.store 0 0 [1]) (by simp)
    (.load 0 0 [1, 0]) (by simp) (0, 1) (by simp [footOf]) (0, 2) (by simp [footOf])
    ⟨0, by omega, by omega, by omega, by omega⟩
  simp at this

/-! ## The run -/

/-- The states of the run. -/
def pf0 : XState Nat := xembed Tso.Litmus.zeroMem
def pf1 : XState Nat := enqueue pf0 0 0 [1]
def pf3 : XState Nat := enqueue pf1 1 0 [2, 1]
def pf4 : XState Nat := ⟨writeMem pf3.memory 0 [2, 1], Function.update pf3.buffer 1 []⟩
def pf5 : XState Nat := ⟨writeMem pf4.memory 0 [1], Function.update pf4.buffer 0 []⟩

theorem pf_run : Run pfP Tso.Litmus.zeroMem pf5 := by
  refine ⟨?_, fun t => ?_⟩
  · have s1 : AStep ⟨pfP, pf0⟩ ⟨[[.load 0 0 [1, 0]], [.store 1 0 [2, 1]]], pf1⟩ :=
      AStep.ev pfP pf0 pf1 0 (.store 0 0 [1]) [.load 0 0 [1, 0]] rfl (XStep.store _ _ _ _)
    have s2 : AStep ⟨[[.load 0 0 [1, 0]], [.store 1 0 [2, 1]]], pf1⟩
        ⟨[[], [.store 1 0 [2, 1]]], pf1⟩ :=
      AStep.ev _ pf1 pf1 0 (.load 0 0 [1, 0]) [] rfl (XStep.load _ _ _ _ (by decide))
    have s3 : AStep ⟨[[], [.store 1 0 [2, 1]]], pf1⟩ ⟨[[], []], pf3⟩ :=
      AStep.ev _ pf1 pf3 1 (.store 1 0 [2, 1]) [] rfl (XStep.store _ _ _ _)
    have s4 : AStep ⟨[[], []], pf3⟩ ⟨[[], []], pf4⟩ :=
      AStep.flush _ pf3 pf4 (XFlush.head pf3 1 0 [2, 1] [] (by decide))
    have s5 : AStep ⟨[[], []], pf4⟩ ⟨[[], []], pf5⟩ :=
      AStep.flush _ pf4 pf5 (XFlush.head pf4 0 0 [1] [] (by decide))
    exact (((((ReflTransGen.refl.tail s1).tail s2).tail s3).tail s4).tail s5)
  · simp only [pf5, pf4, pf3, pf1, pf0, enqueue, xembed, Function.update]
    split <;> simp_all

theorem pf_mem0 : pf5.memory 0 = some 1 := by decide

/-! ## No candidate explains it -/

theorem before_of_last : ∀ {l : List Nat}, l.Nodup → ∀ {a b : Nat}, a ∈ l → l.getLast? = some b →
    a ≠ b → before l a b = true
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, hnd, a, b, ha, hl, hne => by
    rw [List.nodup_cons] at hnd
    simp only [before]
    rw [List.getLast?_cons] at hl
    simp only [Option.some.injEq] at hl
    by_cases hca : c = a
    · subst hca
      simp only [beq_self_eq_true, ↓reduceIte, List.contains_iff_mem]
      cases hl' : l.getLast? with
      | none => rw [hl'] at hl; simp at hl; exact absurd hl hne
      | some d => rw [hl'] at hl; simp at hl; subst hl; exact List.mem_of_getLast? hl'
    · have hca' : (c == a) = false := by simpa using hca
      rw [hca']
      simp only [Bool.false_eq_true, ↓reduceIte]
      have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hca
        · exact h
      cases hl' : l.getLast? with
      | none => simp only [List.getLast?_eq_none_iff] at hl'; subst hl'; simp at ha'
      | some d =>
        rw [hl'] at hl; simp only [Option.getD_some] at hl; subst hl
        exact before_of_last hnd.2 ha' hl' hne

/-- Any candidate that explains the run under any model has a `com` cycle. -/
theorem pf_com_cycle {M : Exec → Prop} {x : Exec}
    (h : Explains M pfP Tso.Litmus.zeroMem pf5 x) : ¬ x.com.Acyclic := by
  obtain ⟨us, hperm, hevs, -, hreads, hrfW, hco, hnd, hmem⟩ := h
  rw [pf_units] at hperm
  have hfst : (us.map Prod.fst).Perm [pfV, pfR, pfX] := by
    have := hperm.map Prod.fst; simpa using this
  have hlen : x.n = 3 := by simp [Exec.n, hevs, hfst.length_eq]
  have hnodup : (us.map Prod.fst).Nodup := hfst.nodup_iff.mpr (by decide)
  have hlenU : x.n = (us.map Prod.fst).length := by simp [Exec.n, hevs]
  have hevN : ∀ w (hw : w < (us.map Prod.fst).length), x.evN w = (us.map Prod.fst)[w] := by
    intro w hw
    simp only [Exec.evN, hevs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw,
      Option.getD_some]
  have hcases : ∀ w < x.n, x.evN w = pfV ∨ x.evN w = pfR ∨ x.evN w = pfX := by
    intro w hw
    rw [hlenU] at hw
    rw [hevN w hw]
    have := hfst.mem_iff.mp (List.getElem_mem hw)
    simpa using this
  have hinj : ∀ a < x.n, ∀ b < x.n, x.evN a = x.evN b → a = b := by
    intro a ha b hb hab
    rw [hlenU] at ha hb
    rw [hevN a ha, hevN b hb] at hab
    exact (hnodup.getElem_inj_iff).mp hab
  -- the load and thread 1's store
  have hRmem : (pfR, [(1 : Byte), 0]) ∈ us := hperm.mem_iff.mpr (by simp)
  obtain ⟨iR, hiR, hRget⟩ := List.mem_iff_getElem.mp hRmem
  have hiRn : iR < x.n := by simpa [Exec.n, hevs] using hiR
  have hER : x.evN iR = pfR := by rw [hevN iR (by simpa using hiR)]; simp [hRget]
  have hXmem : pfX ∈ us.map Prod.fst := hfst.mem_iff.mpr (by simp)
  obtain ⟨iX, hiX, hXget⟩ := List.mem_iff_getElem.mp hXmem
  have hiXn : iX < x.n := by simpa [Exec.n, hevs] using hiX
  have hEX : x.evN iX = pfX := by rw [hevN iX hiX]; exact hXget
  -- what the load returns
  have hrd := hreads iR hiRn (by rw [hER]; rfl)
  have hgd : us.getD iR (dflt, []) = (pfR, [1, 0]) := by
    simp [List.getD_eq_getElem?_getD, hiR, hRget]
  rw [hgd] at hrd
  simp only [Exec.readBytes, hER] at hrd
  have hb : pfR.bytes = [0, 1] := by decide
  rw [hb] at hrd
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hrd
  obtain ⟨hrd0, hrd1⟩ := hrd
  -- byte 0 comes from thread 0's store
  have hwrites : ∀ w < x.n, (x.evN w).isW = true → x.evN w = pfV ∨ x.evN w = pfX := by
    intro w hw hW
    rcases hcases w hw with h | h | h
    · exact .inl h
    · rw [h] at hW; simp [pfR, Ev.isW] at hW
    · exact .inr h
  obtain ⟨iv, hrf0⟩ : ∃ iv, x.rf iR 0 = some iv := by
    cases h : x.rf iR 0 with
    | none => simp [Exec.readByte, h, Tso.Litmus.zeroMem] at hrd0
    | some w => exact ⟨w, rfl⟩
  obtain ⟨hivn, hivW, -⟩ := hrfW _ _ _ hrf0
  have hEv : x.evN iv = pfV := by
    rcases hwrites iv hivn hivW with h | h
    · exact h
    · simp [Exec.readByte, hrf0, h, pfX, Ev.byte] at hrd0
  -- byte 1 comes from the initial state
  have hrf1 : x.rf iR 1 = none := by
    cases h : x.rf iR 1 with
    | none => rfl
    | some w =>
      obtain ⟨hwn, hwW, hwc⟩ := hrfW _ _ _ h
      rcases hwrites w hwn hwW with h' | h'
      · rw [h'] at hwc; simp [pfV, Ev.covers] at hwc
      · simp [Exec.readByte, h, h', pfX, Ev.byte] at hrd1
  -- the final byte 0 is thread 0's store, so `X` is coherence-before it
  have hm0 := hmem 0
  rw [pf_mem0] at hm0
  obtain ⟨u, hlast, hEu⟩ : ∃ u, (x.co 0).getLast? = some u ∧ x.evN u = pfV := by
    cases h : (x.co 0).getLast? with
    | none => rw [h] at hm0; simp [Tso.Litmus.zeroMem] at hm0
    | some u =>
      rw [h] at hm0
      have hu := (hco 0 u).mp (List.mem_of_getLast? h)
      refine ⟨u, rfl, ?_⟩
      rcases hwrites u hu.1 hu.2.1 with h' | h'
      · exact h'
      · simp [h', pfX, Ev.byte] at hm0
  have hu := (hco 0 u).mp (List.mem_of_getLast? hlast)
  have huv : u = iv := hinj u hu.1 iv hivn (hEu.trans hEv.symm)
  subst huv
  have hXco : iX ∈ x.co 0 := (hco 0 iX).mpr ⟨hiXn, by rw [hEX]; rfl, by rw [hEX]; rfl⟩
  have hXne : iX ≠ u := fun h => by rw [h, hEu] at hEX; simp [pfV, pfX] at hEX
  have hbef := before_of_last (hnd 0) hXco hlast hXne
  -- the cycle
  intro hac
  have e1 : x.com ⟨u, hu.1⟩ ⟨iR, hiRn⟩ = true := by
    simp only [Exec.com, BRel.union_iff]
    left
    simp only [Exec.rfR, ev_eq, hEu, hER]
    simp [pfV, pfR, Ev.isW, Ev.isR, Ev.bytes, Ev.covers, hrf0, List.range']
  have e2 : x.com ⟨iR, hiRn⟩ ⟨iX, hiXn⟩ = true := by
    simp only [Exec.com, BRel.union_iff]
    right; right
    simp only [Exec.frR, ev_eq, hEX, hER]
    simp [pfX, pfR, Ev.isW, Ev.isR, Ev.bytes, Ev.covers, hrf1, List.range']
  have e3 : x.com ⟨iX, hiXn⟩ ⟨u, hu.1⟩ = true := by
    simp only [Exec.com, BRel.union_iff]
    right; left
    simp only [Exec.coR, ev_eq, hEX, hEu]
    simp [pfX, pfV, Ev.isW, Ev.bytes, Ev.covers, hbef, List.range']
  exact hac _ (((TransGen.single (r := x.com.Holds) e1).tail e2).tail e3)

theorem com_of_tso {x : Exec} (h : x.Tso) : x.com.Acyclic :=
  BRel.acyclic_mono (fun _ _ hab => TransGen.single (BRel.union_iff.mpr
    (.inr (BRel.seq_of_left x.sm_refl hab)))) h.2.1

theorem com_of_xl {x : Exec} (h : x.Xl) : x.com.Acyclic :=
  BRel.acyclic_mono (fun _ _ hab => TransGen.single (BRel.union_iff.mpr
    (.inr (BRel.seq_of_left (fun a => by simp [Exec.smT]) hab)))) h.2.1

theorem pf_not_tso (x : Exec) : ¬ Explains Exec.Tso pfP Tso.Litmus.zeroMem pf5 x := fun h =>
  pf_com_cycle h (com_of_tso h.choose_spec.2.2.1)

theorem pf_not_xl (x : Exec) : ¬ Explains Exec.Xl pfP Tso.Litmus.zeroMem pf5 x := fun h =>
  pf_com_cycle h (com_of_xl h.choose_spec.2.2.1)

end Silmaril.X86.MemoryModel.OpAx.Proofs
