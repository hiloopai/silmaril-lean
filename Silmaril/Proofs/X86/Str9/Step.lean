module

public import Silmaril.X86.Str9.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.Proofs.X86.Str9.Decode

/-!
# `Str9`: conservative extension, the string listing law and the `rep` run lemmas

* `step_of_open9`, `step_eq_open9`, `step_cases`: every `Open9` step is a step; where `Ext8`
  or `Ext9` fetches a form the two machines agree; every step is an `Open9` step or a
  string step.
* `step_of_fetch_str`, `step_of_listed_str`, `step_of_listed`: a listed form at the program
  counter that executes is one step.
* `storeN_writesWithin`, `fetch_keep`: a store changes only writable bytes, so it keeps the
  instruction bytes of a non-writable code range fetchable.
* `rep_movsq_copy`, `rep_stosq_fill`: `k > 0` elements are exactly `k` steps.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Str9

open Silmaril.X86 (State MState Word Byte Reg fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Str9

/-! ## Conservative extension -/

/-- **Every `Open9` step is a step.** -/
theorem step_of_open9 {m m' : MState} (h : Silmaril.X86.Open9.step m = some m') :
    step m = some m' := by
  by_cases he : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl .undecodable
  · unfold Silmaril.X86.Open9.step at h
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
  · rw [Silmaril.X86.Open9.step_eq_open he] at h
    unfold step
    split
    · rename_i he'; exact absurd he' he
    · exact h

/-- **Where `Ext8` or `Ext9` fetches a form, `Str9` is `Open9`.** -/
theorem step_eq_open9 {m : MState}
    (h : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat ≠ .inl .undecodable ∨
      Silmaril.X86.Ext9.fetchNew m.memory m.core.rip.toNat ≠ none) :
    step m = Silmaril.X86.Open9.step m := by
  by_cases he : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl .undecodable
  · have hn := h.resolve_left (not_not_intro he)
    unfold step Silmaril.X86.Open9.step
    rw [he]
    simp only
    cases hf : Silmaril.X86.Ext9.fetchNew m.memory m.core.rip.toNat with
    | none => exact absurd hf hn
    | some o => rcases o with _ | ⟨i, n⟩ <;> rfl
  · rw [Silmaril.X86.Open9.step_eq_open he]
    unfold step
    split
    · rename_i he'; exact absurd he' he
    · rfl

/-- **Every step is an `Open9` step, or a string step** at bytes that `Ext8` and `Ext9`
reject. -/
theorem step_cases {m m' : MState} (h : step m = some m') :
    Silmaril.X86.Open9.step m = some m' ∨
      (Silmaril.X86.Open9.step m = none ∧
        ∃ i n, fetchStr m.memory m.core.rip.toNat = some (some (i, n)) ∧
          Silmaril.X86.Open.ofResult
            (execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 n)) = some m') := by
  unfold step at h
  split at h
  · rename_i he
    split at h
    · rename_i i n hf
      left
      unfold Silmaril.X86.Open9.step
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
        unfold Silmaril.X86.Open9.step
        rw [he]
        simp only
        rw [hf]
      · cases h
  · rename_i he
    left
    unfold Silmaril.X86.Open9.step
    split
    · rename_i he'; exact absurd he' he
    · exact h

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
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Silmaril.X86.Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : fetchStr m.memory m.core.rip.toNat = some (some (i, l)) := by
    unfold fetchStr
    rw [hmore, decodeStr_append hstr more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn, hfs, hx, Silmaril.X86.Open.ofResult]

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
    exact step_of_open9 (Silmaril.X86.Open9.step_of_listed hl hrip hfit hj hx)
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

/-! ## The core after one element -/

theorem elemCore_rcx (src : Bool) (s : State) (nx : Word) :
    (elemCore src s nx).read .rcx = s.read .rcx - 1 := by
  cases src <;> simp [elemCore]

theorem elemCore_rdi (src : Bool) (s : State) (nx : Word) :
    (elemCore src s nx).read .rdi = s.read .rdi + 8 := by
  cases src <;> simp [elemCore]

theorem elemCore_rsi (src : Bool) (s : State) (nx : Word) :
    (elemCore src s nx).read .rsi = if src then s.read .rsi + 8 else s.read .rsi := by
  cases src <;> simp [elemCore]

theorem elemCore_other (src : Bool) (s : State) (nx : Word) {r : Reg} (h1 : r ≠ .rcx)
    (h2 : r ≠ .rsi) (h3 : r ≠ .rdi) : (elemCore src s nx).read r = s.read r := by
  cases src <;> simp [elemCore, h1, h2, h3]

theorem elemCore_rip (src : Bool) (s : State) (nx : Word) :
    (elemCore src s nx).rip = if s.read .rcx - 1 = 0 then nx else s.rip := by
  cases src <;> rfl

theorem elemCore_flags (src : Bool) (s : State) (nx : Word) :
    (elemCore src s nx).flags = s.flags := by
  cases src <;> rfl

theorem elemCore_fsBase (src : Bool) (s : State) (nx : Word) :
    (elemCore src s nx).fsBase = s.fsBase := by
  cases src <;> rfl

/-! ## The `rep` run lemmas -/

theorem decodeL_repMovsq : decodeL Str.repMovsq.bytes = some (.repMovsq, 3) := by decide
theorem decodeL_repStosq : decodeL Str.repStosq.bytes = some (.repStosq, 3) := by decide
theorem decodeL_movsb : decodeL Str.movsb.bytes = some (.movsb, 1) := by decide

/-- `movsb`. -/
theorem step_movsb {c : State} {mem mem1 : Memory} {v : Word}
    (hf : mem.fetchBytes c.rip.toNat 1 = some Str.movsb.bytes)
    (hl : loadN mem (c.read .rsi) 1 = some v) (hs : storeN mem (c.read .rdi) 1 v = some mem1) :
    step ⟨c, mem⟩ = some ⟨movsbCore c (c.rip + BitVec.ofNat 64 1), mem1⟩ :=
  step_of_fetch_str (m := ⟨c, mem⟩) hf decodeL_movsb (by simp only [execStr, hl, hs])

/-- One element of `rep movsq` (`rcx ≠ 0`). -/
theorem step_movsq_elem {c : State} {mem mem1 : Memory} {v : Word}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repMovsq.bytes) (hc : c.read .rcx ≠ 0)
    (hl : loadN mem (c.read .rsi) 8 = some v) (hs : storeN mem (c.read .rdi) 8 v = some mem1) :
    step ⟨c, mem⟩ = some ⟨elemCore true c (c.rip + BitVec.ofNat 64 3), mem1⟩ :=
  step_of_fetch_str (m := ⟨c, mem⟩) hf decodeL_repMovsq (by
    simp only [execStr, hc, ite_false, hl, repElem, hs])

/-- One element of `rep stosq` (`rcx ≠ 0`). -/
theorem step_stosq_elem {c : State} {mem mem1 : Memory}
    (hf : mem.fetchBytes c.rip.toNat 3 = some Str.repStosq.bytes) (hc : c.read .rcx ≠ 0)
    (hs : storeN mem (c.read .rdi) 8 (c.read .rax) = some mem1) :
    step ⟨c, mem⟩ = some ⟨elemCore false c (c.rip + BitVec.ofNat 64 3), mem1⟩ :=
  step_of_fetch_str (m := ⟨c, mem⟩) hf decodeL_repStosq (by
    simp only [execStr, hc, ite_false, repElem, hs])

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

private theorem ofNat_succ_ne_zero {k : Nat} (hk : k + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (k + 1) ≠ 0 := by
  intro h; have := congrArg BitVec.toNat h; simp at this; omega

private theorem ofNat_succ_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp; omega

private theorem add_eight_add (x : Word) (k : Nat) :
    x + 8 + BitVec.ofNat 64 (8 * (k + 1)) = x + BitVec.ofNat 64 (8 * (k + 1 + 1)) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- The induction step of the `rep` run lemmas: a first element that leaves `rcx ≠ 0`, then
a finished `rep` of `k + 1` elements, is a finished `rep` of `k + 2` elements. -/
private theorem repDone_succ {src : Bool} {k : Nat} {c c' : State} {nx : Word}
    (hnz : c.read .rcx - 1 ≠ 0) (hd : RepDone src (k + 1) (elemCore src c nx) c') :
    RepDone src (k + 1 + 1) c c' := by
  obtain ⟨hr, hcx, hdi, hsi, hoth, hfl, hfs⟩ := hd
  have hrip : (elemCore src c nx).rip = c.rip := by simp only [elemCore_rip, hnz, ↓reduceIte]
  refine ⟨by rw [hr, hrip], hcx, ?_, ?_, ?_, by rw [hfl, elemCore_flags],
    by rw [hfs, elemCore_fsBase]⟩
  · rw [hdi, elemCore_rdi, add_eight_add]
  · rw [hsi, elemCore_rsi]
    cases src
    · rfl
    · simp only [↓reduceIte]; exact add_eight_add _ _
  · intro r h1 h2 h3; rw [hoth r h1 h2 h3, elemCore_other src c nx h1 h2 h3]

/-- The base case: one element that leaves `rcx = 0` is a finished `rep` of one element. -/
private theorem repDone_one {src : Bool} {c : State} (hc : c.read .rcx = 1) :
    RepDone src 1 c (elemCore src c (c.rip + BitVec.ofNat 64 3)) := by
  refine ⟨by rw [elemCore_rip, hc]; rfl, by rw [elemCore_rcx, hc]; rfl, by rw [elemCore_rdi]; rfl,
    by rw [elemCore_rsi]; cases src <;> rfl, fun r h1 h2 h3 => elemCore_other src c _ h1 h2 h3,
    elemCore_flags src c _, elemCore_fsBase src c _⟩

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
        have h1 := step_movsq_elem hf (hc ▸ ofNat_succ_ne_zero hk) hl hs
        obtain ⟨hf1, hro1⟩ := fetch_keep hs hro
        rw [hf] at hf1
        cases k with
        | zero =>
          simp only [copyQ, Option.some.injEq] at hcopy
          subst hcopy
          exact ⟨_, by rw [Silmaril.Machine.Execution.run_succ, h1]; rfl, repDone_one hc⟩
        | succ k =>
          have hnz : c.read .rcx - 1 ≠ 0 := by
            rw [hc, ofNat_succ_sub_one (k + 1)]; exact ofNat_succ_ne_zero (by omega)
          have hrip1 : (elemCore true c (c.rip + BitVec.ofNat 64 3)).rip = c.rip := by
            simp only [elemCore_rip, hnz, ↓reduceIte]
          obtain ⟨c', hrun, hd⟩ := rep_movsq_copy k
            (c := elemCore true c (c.rip + BitVec.ofNat 64 3)) (mem := mem1) (mem' := mem')
            (by rw [hrip1]; exact hf1) (by rw [hrip1]; exact hro1) (by omega)
            (by rw [elemCore_rcx, hc, ofNat_succ_sub_one (k + 1)])
            (by rw [elemCore_rsi, elemCore_rdi]; exact hcopy)
          exact ⟨c', by rw [Silmaril.Machine.Execution.run_succ, h1]; exact hrun,
            repDone_succ hnz hd⟩

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
      have h1 := step_stosq_elem hf (hc ▸ ofNat_succ_ne_zero hk) hs
      obtain ⟨hf1, hro1⟩ := fetch_keep hs hro
      rw [hf] at hf1
      cases k with
      | zero =>
        simp only [fillQ, Option.some.injEq] at hfill
        subst hfill
        exact ⟨_, by rw [Silmaril.Machine.Execution.run_succ, h1]; rfl, repDone_one hc⟩
      | succ k =>
        have hnz : c.read .rcx - 1 ≠ 0 := by
          rw [hc, ofNat_succ_sub_one (k + 1)]; exact ofNat_succ_ne_zero (by omega)
        have hrip1 : (elemCore false c (c.rip + BitVec.ofNat 64 3)).rip = c.rip := by
          simp only [elemCore_rip, hnz, ↓reduceIte]
        have hax : (elemCore false c (c.rip + BitVec.ofNat 64 3)).read .rax = c.read .rax :=
          elemCore_other false c _ (by decide) (by decide) (by decide)
        obtain ⟨c', hrun, hd⟩ := rep_stosq_fill k
          (c := elemCore false c (c.rip + BitVec.ofNat 64 3)) (mem := mem1) (mem' := mem')
          (by rw [hrip1]; exact hf1) (by rw [hrip1]; exact hro1) (by omega)
          (by rw [elemCore_rcx, hc, ofNat_succ_sub_one (k + 1)])
          (by rw [hax, elemCore_rdi]; exact hfill)
        exact ⟨c', by rw [Silmaril.Machine.Execution.run_succ, h1]; exact hrun,
          repDone_succ hnz hd⟩

end Silmaril.Proofs.X86.Str9
