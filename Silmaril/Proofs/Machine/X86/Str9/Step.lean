module

public import Silmaril.Machine.X86.Str9.Defs
public import Silmaril.Machine.X86.Open9.Thms
public import Silmaril.Proofs.Machine.X86.Str9.Decode

/-!
# `Str9`: conservative extension, the string listing law and the `rep` run lemmas

Proofs for `Silmaril/Machine/X86/Str9/Thms.lean`.

* `step_of_open9`, `step_cases`, `run_of_open9`: every `Open9` step is a step, and every step
  is one of those or a string step.
* `step_of_fetch_str`, `step_of_listed_str`: a listed string form at the program counter that
  executes is one step.
* `storeN_writesWithin`: a store changes only writable bytes, so it keeps the instruction
  bytes of a non-writable code range fetchable (`fetch_keep`).
* `rep_movsq_copy`, `rep_stosq_fill`: `k > 0` elements are exactly `k` steps.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Str9

open Silmaril.X86 (State MState Word Byte Reg fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.Str9

/-! ## Conservative extension -/

/-- **Every `Open9` step is a step.** -/
theorem step_of_open9 {m m' : MState} (h : Open9.step m = some m') : step m = some m' := by
  by_cases he : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl .undecodable
  · unfold Open9.step at h
    rw [he] at h
    simp only at h
    unfold step
    rw [he]
    simp only
    split
    · rename_i i n hf
      rw [hf] at h
      exact h
    · rename_i hf
      rw [hf] at h
      cases h
    · rename_i hf
      rw [hf] at h
      cases h
  · rw [Open9.step_eq_open he] at h
    unfold step
    split
    · rename_i he'; exact absurd he' he
    · exact h

/-- **Every step is an `Open9` step, or a string step** at bytes that `Ext8` and `Ext9`
reject. -/
theorem step_cases {m m' : MState} (h : step m = some m') :
    Open9.step m = some m' ∨
      (Open9.step m = none ∧ ∃ i n, fetchStr m.memory m.core.rip.toNat = some (some (i, n)) ∧
        Open.ofResult (execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 n)) = some m') := by
  unfold step at h
  split at h
  · rename_i he
    split at h
    · rename_i i n hf
      left
      unfold Open9.step
      rw [he]
      simp only
      rw [hf]
      exact h
    · cases h
    · rename_i hf
      split at h
      · rename_i i n hs
        right
        refine ⟨?_, i, n, hs, h⟩
        unfold Open9.step
        rw [he]
        simp only
        rw [hf]
      · cases h
  · rename_i he
    left
    unfold Open9.step
    split
    · rename_i he'; exact absurd he' he
    · exact h

/-- `Open9` runs are runs. -/
theorem run_of_open9 : ∀ (k : Nat) {a b : MState}, run Open9.step k a = some b → run step k a = some b
  | 0, a, b, h => h
  | k + 1, a, b, h => by
    simp only [run] at h ⊢
    cases hs : Open9.step a with
    | none => rw [hs] at h; cases h
    | some a' =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      rw [step_of_open9 hs]
      exact run_of_open9 k h

theorem reaches_of_open9 {a b : MState} (h : Reaches Open9.step a b) : Reaches step a b := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, run_of_open9 k hk⟩

/-! ## The string listing law -/

/-- **The fetch form of the string law**: bytes `w` fetched (with execute permission) at the
program counter that `decodeL` reads as a string form of length `l`, and that execute, are one
step. -/
theorem step_of_fetch_str {m : MState} {l : Nat} {w : List Byte} {i : Str} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨hnone, hbad, hne, hbad9, hstr, h15⟩ := decodeL_spec hdec
  obtain ⟨more, hmore, hf8⟩ := Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    rw [hmore, decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : fetchStr m.memory m.core.rip.toNat = some (some (i, l)) := by
    unfold fetchStr
    rw [hmore, decodeStr_append hstr more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn, hfs, hx, Open.ofResult]

/-- **The string listing law.** -/
theorem step_of_listed_str {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Str}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  have h1 : 0 < l := by
    obtain ⟨-, -, -, -, hstr, -⟩ := decodeL_spec hdec
    obtain ⟨-, rfl⟩ := decodeStr_some hstr
    cases i <;> decide
  have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_str fetched hdec hx

/-- **The listing law of the whole machine.** -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  unfold decode at hdec
  split at hdec
  · rename_i j n hj
    simp only [Option.some.injEq, Prod.mk.injEq] at hdec
    obtain ⟨rfl, rfl⟩ := hdec
    exact step_of_open9 (Open9.step_of_listed hl hrip hfit hj hx)
  · cases hs : decodeL ((code.drop o).take l) with
    | none => rw [hs] at hdec; cases hdec
    | some p =>
      obtain ⟨j, n⟩ := p
      rw [hs] at hdec
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl⟩ := hdec
      exact step_of_listed_str hl hrip hfit hs hx

/-! ## Stores keep non-writable code -/

/-- A store changes only bytes the memory lets it write, and no mapping. -/
theorem storeN_writesWithin {mem mem' : Memory} {a : Word} {k : Nat} {v : Word}
    (h : storeN mem a k v = some mem') :
    Silmaril.Process.Memory.WritesWithin mem mem' (Writable mem) := by
  unfold storeN at h
  have hp := Silmaril.Process.Memory.writeBytes_permitted h
  have hw := Silmaril.Process.Memory.writeBytes_writesOnly h
  refine ⟨hw.1, fun x hx => hw.2 x ?_⟩
  by_contra hin
  apply hx
  unfold Silmaril.Process.Memory.Permitted at hp
  rw [Silmaril.Process.Memory.checkSpan_iff] at hp
  have := hp.2.2 (x - a.toNat) (by omega)
  unfold Writable
  rwa [show a.toNat + (x - a.toNat) = x by omega] at this

/-- A store keeps the bytes fetched from a range with no writable byte, and the
non-writability of that range. -/
theorem fetch_keep {mem mem' : Memory} {a : Word} {k : Nat} {v : Word}
    (h : storeN mem a k v = some mem') {p l : Nat}
    (hro : ∀ o < l, mem.permits .write (p + o) = false) :
    mem'.fetchBytes p l = mem.fetchBytes p l ∧ ∀ o < l, mem'.permits .write (p + o) = false := by
  have hw := storeN_writesWithin h
  refine ⟨hw.fetchBytes fun o ho hin => ?_, fun o ho => by rw [hw.permits]; exact hro o ho⟩
  unfold Writable at hin
  rw [hro o ho] at hin
  cases hin

/-! ## The `rep` run lemmas -/

theorem decodeL_repMovsq : decodeL Str.repMovsq.bytes = some (.repMovsq, 3) := by decide
theorem decodeL_repStosq : decodeL Str.repStosq.bytes = some (.repStosq, 3) := by decide

/-- One element of `rep movsq` (`rcx ≠ 0`). -/
theorem step_movsq_elem {c : State} {mem mem1 : Memory} {v : Word}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes) (hc : c.read .rcx ≠ 0)
    (hl : loadN mem (c.read .rsi) 8 = some v) (hs : storeN mem (c.read .rdi) 8 v = some mem1) :
    step ⟨c, mem⟩ = some ⟨{ ((c.write .rsi (c.read .rsi + 8)).write .rdi (c.read .rdi + 8)).write
        .rcx (c.read .rcx - 1) with
      rip := if c.read .rcx - 1 = 0 then c.rip + BitVec.ofNat 64 3 else c.rip }, mem1⟩ :=
  step_of_fetch_str (m := ⟨c, mem⟩) hf decodeL_repMovsq (by
    simp only [execStr, hc, ite_false, hl, repElem, hs, ite_true])

/-- One element of `rep stosq` (`rcx ≠ 0`). -/
theorem step_stosq_elem {c : State} {mem mem1 : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes) (hc : c.read .rcx ≠ 0)
    (hs : storeN mem (c.read .rdi) 8 (c.read .rax) = some mem1) :
    step ⟨c, mem⟩ = some ⟨{ (c.write .rdi (c.read .rdi + 8)).write .rcx (c.read .rcx - 1) with
      rip := if c.read .rcx - 1 = 0 then c.rip + BitVec.ofNat 64 3 else c.rip }, mem1⟩ :=
  step_of_fetch_str (m := ⟨c, mem⟩) hf decodeL_repStosq (by
    simp only [execStr, hc, ite_false, repElem, hs, Bool.false_eq_true])

/-- `rep movsq` with `rcx = 0` only advances RIP. -/
theorem rep_movsq_zero {c : State} {mem : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes) (hc : c.read .rcx = 0) :
    step ⟨c, mem⟩ = some ⟨{ c with rip := c.rip + BitVec.ofNat 64 3 }, mem⟩ :=
  step_of_fetch_str (m := ⟨c, mem⟩) hf decodeL_repMovsq (by simp only [execStr, hc, ite_true])

/-- `rep stosq` with `rcx = 0` only advances RIP. -/
theorem rep_stosq_zero {c : State} {mem : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes) (hc : c.read .rcx = 0) :
    step ⟨c, mem⟩ = some ⟨{ c with rip := c.rip + BitVec.ofNat 64 3 }, mem⟩ :=
  step_of_fetch_str (m := ⟨c, mem⟩) hf decodeL_repStosq (by simp only [execStr, hc, ite_true])

/-- **`rep movsq` of `k + 1` quadwords is `k + 1` steps** (the code bytes not writable). -/
theorem rep_movsq_copy : ∀ (k : Nat) {c : State} {mem mem' : Memory},
    mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes →
    (∀ o < 3, mem.permits .write (c.rip.toNat + o) = false) →
    k + 1 < 2 ^ 64 → c.read .rcx = BitVec.ofNat 64 (k + 1) →
    copyQ (k + 1) (c.read .rsi) (c.read .rdi) mem = some mem' →
    ∃ c', run step (k + 1) ⟨c, mem⟩ = some ⟨c', mem'⟩ ∧ RepDone true (k + 1) c c'
  | k, c, mem, mem', hf, hro, hk, hc, hcopy => by
    simp only [copyQ, Option.bind_eq_bind] at hcopy
    cases hl : loadN mem (c.read .rsi) 8 with
    | none => rw [hl] at hcopy; cases hcopy
    | some v =>
      rw [hl] at hcopy
      simp only [Option.bind_some] at hcopy
      cases hs : storeN mem (c.read .rdi) 8 v with
      | none => rw [hs] at hcopy; cases hcopy
      | some mem1 =>
        rw [hs] at hcopy
        simp only [Option.bind_some] at hcopy
        have hc0 : c.read .rcx ≠ 0 := by rw [hc]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
        have h1 := step_movsq_elem hf hc0 hl hs
        obtain ⟨hf1, hro1⟩ := fetch_keep hs hro
        rw [hf] at hf1
        cases k with
        | zero =>
          simp only [copyQ, Option.some.injEq] at hcopy
          subst hcopy
          refine ⟨_, by rw [Silmaril.Machine.Execution.run_succ, h1]; rfl, ?_⟩
          refine ⟨by simp [hc], by simp [hc], by simp, by simp, ?_, rfl, rfl⟩
          intro r h1 h2 h3
          simp [h1, h2, h3]
        | succ k =>
          have hnz : c.read .rcx - 1 ≠ 0 := by
            rw [hc]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
          simp only [hnz, ↓reduceIte] at h1
          set c1 : State := { ((c.write .rsi (c.read .rsi + 8)).write .rdi (c.read .rdi + 8)).write
              .rcx (c.read .rcx - 1) with rip := c.rip } with hc1
          have hrip1 : c1.rip = c.rip := rfl
          have hrcx1 : c1.read .rcx = BitVec.ofNat 64 (k + 1) := by
            simp only [hc1, Silmaril.X86.State.read_mk_regs]
            rw [Silmaril.X86.State.read_write_same, hc]
            apply BitVec.eq_of_toNat_eq; simp; omega
          have hsi : c1.read .rsi = c.read .rsi + 8 := by simp [hc1]
          have hdi : c1.read .rdi = c.read .rdi + 8 := by simp [hc1]
          obtain ⟨c', hrun, hd⟩ := rep_movsq_copy k (c := c1) (mem := mem1) (mem' := mem')
            (by rw [hrip1]; exact hf1) (by rw [hrip1]; exact hro1) (by omega) hrcx1
            (by rw [hsi, hdi]; exact hcopy)
          obtain ⟨hr, hcx, hdi', hsi', hoth, hfl, hfs⟩ := hd
          refine ⟨c', by rw [Silmaril.Machine.Execution.run_succ, h1]; exact hrun, ?_⟩
          refine ⟨by rw [hr, hrip1], hcx, ?_, ?_, ?_, by rw [hfl]; rfl, by rw [hfs]; rfl⟩
          · rw [hdi', hdi]; apply BitVec.eq_of_toNat_eq; simp; omega
          · simp only [ite_true] at hsi' ⊢
            rw [hsi', hsi]; apply BitVec.eq_of_toNat_eq; simp; omega
          · intro r h1 h2 h3
            rw [hoth r h1 h2 h3]
            simp [hc1, h1, h2, h3]

/-- **`rep stosq` of `k + 1` quadwords is `k + 1` steps** (the code bytes not writable). -/
theorem rep_stosq_fill : ∀ (k : Nat) {c : State} {mem mem' : Memory},
    mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes →
    (∀ o < 3, mem.permits .write (c.rip.toNat + o) = false) →
    k + 1 < 2 ^ 64 → c.read .rcx = BitVec.ofNat 64 (k + 1) →
    fillQ (k + 1) (c.read .rax) (c.read .rdi) mem = some mem' →
    ∃ c', run step (k + 1) ⟨c, mem⟩ = some ⟨c', mem'⟩ ∧ RepDone false (k + 1) c c'
  | k, c, mem, mem', hf, hro, hk, hc, hfill => by
    simp only [fillQ, Option.bind_eq_bind] at hfill
    cases hs : storeN mem (c.read .rdi) 8 (c.read .rax) with
    | none => rw [hs] at hfill; cases hfill
    | some mem1 =>
      rw [hs] at hfill
      simp only [Option.bind_some] at hfill
      have hc0 : c.read .rcx ≠ 0 := by rw [hc]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
      have h1 := step_stosq_elem hf hc0 hs
      obtain ⟨hf1, hro1⟩ := fetch_keep hs hro
      rw [hf] at hf1
      cases k with
      | zero =>
        simp only [fillQ, Option.some.injEq] at hfill
        subst hfill
        refine ⟨_, by rw [Silmaril.Machine.Execution.run_succ, h1]; rfl, ?_⟩
        refine ⟨by simp [hc], by simp [hc], by simp, by simp, ?_, rfl, rfl⟩
        intro r h1 h2 h3
        simp [h1, h3]
      | succ k =>
        have hnz : c.read .rcx - 1 ≠ 0 := by
          rw [hc]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
        simp only [hnz, ↓reduceIte] at h1
        set c1 : State := { (c.write .rdi (c.read .rdi + 8)).write .rcx (c.read .rcx - 1) with
            rip := c.rip } with hc1
        have hrip1 : c1.rip = c.rip := rfl
        have hrcx1 : c1.read .rcx = BitVec.ofNat 64 (k + 1) := by
          simp only [hc1, Silmaril.X86.State.read_mk_regs]
          rw [Silmaril.X86.State.read_write_same, hc]
          apply BitVec.eq_of_toNat_eq; simp; omega
        have hax : c1.read .rax = c.read .rax := by simp [hc1]
        have hdi : c1.read .rdi = c.read .rdi + 8 := by simp [hc1]
        obtain ⟨c', hrun, hd⟩ := rep_stosq_fill k (c := c1) (mem := mem1) (mem' := mem')
          (by rw [hrip1]; exact hf1) (by rw [hrip1]; exact hro1) (by omega) hrcx1
          (by rw [hax, hdi]; exact hfill)
        obtain ⟨hr, hcx, hdi', hsi', hoth, hfl, hfs⟩ := hd
        refine ⟨c', by rw [Silmaril.Machine.Execution.run_succ, h1]; exact hrun, ?_⟩
        refine ⟨by rw [hr, hrip1], hcx, ?_, ?_, ?_, by rw [hfl]; rfl, by rw [hfs]; rfl⟩
        · rw [hdi', hdi]; apply BitVec.eq_of_toNat_eq; simp; omega
        · simp only [Bool.false_eq_true, ite_false] at hsi' ⊢
          rw [hsi']; simp [hc1]
        · intro r h1 h2 h3
          rw [hoth r h1 h2 h3]
          simp [hc1, h1, h3]

end Silmaril.Proofs.Machine.X86.Str9
