module

public import Silmaril.X86.Weak9.Defs
public import Silmaril.X86.Atomic9.Thms
public import Silmaril.X86.Str9.Thms
public import Silmaril.X86.Ext9.Thms

/-!
# `Weak9`: decoder laws, conservative extension and the listing law

Proofs for `Silmaril/X86/Weak9/Thms.lean`.

* `good_pWeak`, `good_atomicPNew`: the parsers have the prefix laws of `ByteParser.Good`
  (the second repeats `Atomic9`'s own proof, which its header does not export);
* `step_of_atomic9`: every `Atomic9` step is a step;
* `step_of_fetch_weak`, `step_of_fetch_str`: a listed `Weak`/`Str9` form at the program counter
  that executes is one step;
* `step_of_listed`: the listing law of the whole machine.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Weak9

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded PResult ByteParser)
open Silmaril.X86.Ext.ByteParser
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Weak9

/-! ## Parser laws -/

theorem good_memP (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (Atomic9.memP rex mp) := by
  unfold Atomic9.memP
  split
  · exact good_pure _
  · exact good_fail

theorem good_rmP (l : Bool) (rex : Option Silmaril.X86.Ext.Rex)
    (mp : Silmaril.X86.Ext.ModrmPart) : Good (Atomic9.rmP l rex mp) := by
  unfold Atomic9.rmP
  exact good_ite (good_map _ (good_memP _ _)) (good_pure _)

theorem good_rm8P (l : Bool) (rex : Option Silmaril.X86.Ext.Rex)
    (mp : Silmaril.X86.Ext.ModrmPart) : Good (Atomic9.rm8P l rex mp) := by
  unfold Atomic9.rm8P
  refine good_ite ?_ (good_pure _)
  split
  · exact good_pure _
  · exact good_fail

theorem good_pIb32 : Good Ext9.pIb32 := good_map _ good_byte

/-- Discharge `Good` goals of parsers built from the combinators. -/
macro "good_tac" : tactic => `(tactic| repeat (first
  | exact good_fail | exact good_byte | exact Silmaril.X86.Ext8.good_pM
  | exact Silmaril.X86.Ext.good_pImm32 | exact good_pIb32 | exact good_pure _
  | exact Silmaril.X86.Ext8.good_optP _
  | exact good_memP _ _ | exact good_rmP _ _ _ | exact good_rm8P _ _ _
  | apply good_ite | apply good_map | apply good_bind | intro _))

theorem good_pBody (l : Bool) (rex : Option Silmaril.X86.Ext.Rex) (opc : Silmaril.X86.Ext.Opc) :
    Good (Atomic9.pBody l rex opc) := by
  cases opc <;> simp only [Atomic9.pBody] <;> good_tac

theorem good_pLocked : Good Atomic9.pLocked :=
  good_bind Silmaril.X86.Ext.good_pHead fun _ => good_ite (good_pBody _ _ _) good_fail

/-- `Atomic9`'s parser has the prefix laws. -/
theorem good_atomicPNew : Good Atomic9.pNew := by
  refine good_bind Silmaril.X86.Ext.good_pHead fun h => ?_
  refine good_ite good_fail ?_
  split
  · exact good_ite good_pLocked (good_pBody _ _ _)
  · exact good_ite (good_pure _) good_fail
  · exact good_fail

/-- `Weak9`'s parser has the prefix laws. -/
theorem good_pWeak : Good pWeak := by
  refine good_bind Silmaril.X86.Ext.good_pHead fun h => ?_
  refine good_ite good_fail ?_
  split
  · exact good_ite (good_bind Silmaril.X86.Ext8.good_pM fun _ => good_map _ (good_memP _ _))
      good_fail
  · exact good_ite (good_pure _) good_fail
  · exact good_fail

/-- A decoded `Weak` form keeps its reading whatever bytes follow. -/
theorem decodeWeak_append {bytes : List Byte} {i : Weak} {n : Nat}
    (h : decodeWeak bytes = some (i, n)) (more : List Byte) :
    decodeWeak (bytes ++ more) = some (i, n) := by
  unfold decodeWeak at h ⊢
  split at h
  · rename_i j rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, ext⟩ := good_pWeak.ok hp
    rw [ext more]
    simp only [List.length_append, Option.some.injEq, Prod.mk.injEq, true_and]
    omega
  · simp at h

theorem decodeWeak_none_of_bad {w : List Byte} (h : weakBad w = true) (more : List Byte) :
    decodeWeak (w ++ more) = none := by
  unfold weakBad at h
  split at h
  · rename_i hb
    unfold decodeWeak
    rw [good_pWeak.bad hb more]
  · cases h

theorem atomicDecodeNew_none_of_bad {w : List Byte} (h : atomicBad w = true) (more : List Byte) :
    Atomic9.decodeNew (w ++ more) = none := by
  unfold atomicBad at h
  split at h
  · rename_i hb
    unfold Atomic9.decodeNew
    rw [good_atomicPNew.bad hb more]
  · cases h

theorem ext9DecodeNew_none_of_bad {w : List Byte} (h : Sse9.ext9Bad w = true)
    (more : List Byte) : Ext9.decodeNew (w ++ more) = none := by
  unfold Sse9.ext9Bad at h
  split at h
  · rename_i hb
    unfold Ext9.decodeNew
    rw [Ext9.good_pNew.bad hb more]
  · cases h

theorem str9Ext9_none_of_bad {w : List Byte} (h : Str9.ext9Bad w = true)
    (more : List Byte) : Ext9.decodeNew (w ++ more) = none := by
  unfold Str9.ext9Bad at h
  split at h
  · rename_i hb
    unfold Ext9.decodeNew
    rw [Ext9.good_pNew.bad hb more]
  · cases h

/-- A decoded string form keeps its reading whatever bytes follow. -/
theorem decodeStr_append {bytes : List Byte} {i : Str9.Str} {n : Nat}
    (h : Str9.decodeStr bytes = some (i, n)) (more : List Byte) :
    Str9.decodeStr (bytes ++ more) = some (i, n) := by
  unfold Str9.decodeStr at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp [Str9.decodeStr]

/-! ## Listing specifications -/

theorem decodeLW_spec {bytes : List Byte} {i : Weak} {n : Nat} (h : decodeLW bytes = some (i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
      Open9.rawNotEof bytes = true ∧ Sse9.ext9Bad bytes = true ∧ atomicBad bytes = true ∧
      decodeWeak bytes = some (i, n) ∧ 0 < n ∧ n ≤ maxInstrLength := by
  unfold decodeLW at h
  split at h
  · rename_i i' n' hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hd, hc.2.2.2.2.2⟩
    · cases h
  · cases h

theorem decodeLS_spec {bytes : List Byte} {i : Str9.Str} {n : Nat}
    (h : decodeLS bytes = some (i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
      Open9.rawNotEof bytes = true ∧ Str9.ext9Bad bytes = true ∧ atomicBad bytes = true ∧
      weakBad bytes = true ∧ Str9.decodeStr bytes = some (i, n) ∧ 0 < n ∧
      n ≤ maxInstrLength := by
  unfold decodeLS at h
  split at h
  · rename_i i' n' hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold Str9.decodeL at hd
      split at hd
      · rename_i j k hs
        split at hd
        · rename_i hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          have hpos : 0 < k := by
            unfold Str9.decodeStr at hs
            split at hs <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs <;>
              omega
          exact ⟨hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2.1, hc.1, hc.2, hs, hpos, hc'.2.2.2.2⟩
        · cases hd
      · cases hd
    · cases h
  · cases h

/-! ## Conservative extension -/

/-- **Every `Atomic9` step is a step.** -/
theorem step_of_atomic9 {m m' : MState} (h : Atomic9.step m = some m') : step m = some m' := by
  unfold Atomic9.step at h
  unfold step
  split at h
  · rename_i he
    rw [he]
    simp only
    split at h
    · rename_i i n hf
      rw [hf]
      exact h
    · cases h
    · rename_i hf
      rw [hf]
      simp only
      split at h
      · rename_i i n hs
        rw [hs]
        exact h
      · cases h
  · rename_i he
    split
    · rename_i he'; exact absurd he' he
    · exact h

/-! ## The listing laws of the new forms -/

theorem step_of_fetch_weak {m : MState} {l : Nat} {w : List Byte} {i : Weak} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decodeLW w = some (i, l))
    (hx : execWeak i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨hnone, hbad, hne, hbad9, hbadA, hw, -, h15⟩ := decodeLW_spec hdec
  obtain ⟨more, hmore, hf8⟩ := Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    rw [hmore, ext9DecodeNew_none_of_bad hbad9 more]
    rfl
  have hfa : Atomic9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Atomic9.fetchNew
    rw [hmore, atomicDecodeNew_none_of_bad hbadA more]
    rfl
  have hfw : fetchWeak m.memory m.core.rip.toNat = some (some (i, l)) := by
    unfold fetchWeak
    rw [hmore, decodeWeak_append hw more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn, hfa, hfw, hx, Open.ofResult]

theorem step_of_fetch_str {m : MState} {l : Nat} {w : List Byte} {i : Str9.Str} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decodeLS w = some (i, l))
    (hx : Str9.execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨hnone, hbad, hne, hbad9, hbadA, hbadW, hs, -, h15⟩ := decodeLS_spec hdec
  obtain ⟨more, hmore, hf8⟩ := Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    rw [hmore, str9Ext9_none_of_bad hbad9 more]
    rfl
  have hfa : Atomic9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Atomic9.fetchNew
    rw [hmore, atomicDecodeNew_none_of_bad hbadA more]
    rfl
  have hfw : fetchWeak m.memory m.core.rip.toNat = none := by
    unfold fetchWeak
    rw [hmore, decodeWeak_none_of_bad hbadW more]
    rfl
  have hfs : Str9.fetchStr m.memory m.core.rip.toNat = some (some (i, l)) := by
    unfold Str9.fetchStr
    rw [hmore, decodeStr_append hs more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn, hfa, hfw, hfs, hx, Open.ofResult]

/-- What the listing decoder reads. -/
theorem decode_cases {bytes : List Byte} {i : Instr} {n : Nat} (h : decode bytes = some (i, n)) :
    (∃ j, i = .atomic j ∧ Atomic9.decode bytes = some (j, n)) ∨
      (∃ j, i = .weak j ∧ decodeLW bytes = some (j, n)) ∨
      (∃ j, i = .str j ∧ decodeLS bytes = some (j, n)) := by
  unfold decode at h
  split at h
  · rename_i j n' hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨j, rfl, hd⟩
  · split at h
    · rename_i j n' hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inl ⟨j, rfl, hd⟩)
    · cases hl : decodeLS bytes with
      | none => rw [hl] at h; cases h
      | some p =>
        obtain ⟨j, n'⟩ := p
        rw [hl] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr (Or.inr ⟨j, rfl, rfl⟩)

/-- **The listing law of the machine.** -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  rcases decode_cases hdec with ⟨j, rfl, hd⟩ | ⟨j, rfl, hd⟩ | ⟨j, rfl, hd⟩
  · exact step_of_atomic9 (Atomic9.step_of_listed hl hrip hfit hd hx)
  · obtain ⟨-, -, -, -, -, -, h1, -⟩ := decodeLW_spec hd
    have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
    have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
      rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
    exact step_of_fetch_weak fetched hd hx
  · obtain ⟨-, -, -, -, -, -, -, h1, -⟩ := decodeLS_spec hd
    have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
    have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
      rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
    exact step_of_fetch_str fetched hd hx

end Silmaril.Proofs.X86.Weak9
