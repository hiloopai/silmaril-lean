module

public import Silmaril.X86.Sse9.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Ext9.Thms

/-!
# `Sse9`: the conservative-extension laws and the SSE listing law

Proofs for `Silmaril/X86/Sse9/Thms.lean`.

* `good_pSse`, `decodeSse_append`: the SSE parser has the prefix laws.
* `step_of_open9`, `step_cases`, `run_of_open9`: every `Open9` step is a step with the XMM
  file unchanged, and every step is one of those or an SSE step.
* `step_of_fetch_sse`, `step_of_listed_sse`: a listed SSE form (`decodeL`) at the program
  counter that executes is one step.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sse9

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (PResult ByteParser Loaded)
open Silmaril.X86.Ext.ByteParser
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86
open Silmaril.X86.Sse9

/-! ## Decoder laws -/

theorem good_pBody (pfx : Silmaril.X86.Ext.Pfx) (rex : Option Silmaril.X86.Ext.Rex) (b : Byte) :
    Good (pBody pfx rex b) := by
  cases pfx <;> simp only [pBody] <;>
    repeat (first
      | exact good_fail | exact Silmaril.X86.Ext8.good_pM
      | apply good_ite | apply good_map)

theorem good_pSse : Good pSse := by
  refine good_bind Silmaril.X86.Ext.good_pHead fun h => ?_
  refine good_ite good_fail ?_
  split
  · exact good_pBody _ _ _
  · exact good_fail

/-- A decoded SSE form keeps its reading whatever bytes follow. -/
theorem decodeSse_append {bytes : List Byte} {i : Sse9.Instr} {n : Nat}
    (h : decodeSse bytes = some (i, n)) (more : List Byte) :
    decodeSse (bytes ++ more) = some (i, n) := by
  unfold decodeSse at h ⊢
  split at h
  · rename_i j rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, ext⟩ := good_pSse.ok hp
    rw [ext more]
    simp only [List.length_append, Option.some.injEq, Prod.mk.injEq, true_and]
    omega
  · simp at h

/-- `Ext9`'s new-form decoder rejects every extension of a slice its parser rejects. -/
theorem decodeNew_none_of_bad {w : List Byte} (h : ext9Bad w = true) (more : List Byte) :
    Ext9.decodeNew (w ++ more) = none := by
  unfold ext9Bad at h
  split at h
  · rename_i hb
    unfold Ext9.decodeNew
    rw [Ext9.good_pNew.bad hb more]
  · cases h

/-! ## Conservative extension -/

/-- **Every `Open9` step is a step, with the XMM file unchanged.** -/
theorem step_of_open9 {x : XState} {m' : MState} (h : Open9.step x.m = some m') :
    step x = some ⟨m', x.xmm⟩ := by
  by_cases he : Silmaril.X86.Ext8.fetch x.m.memory x.m.core.rip.toNat = .inl .undecodable
  · unfold Open9.step at h
    rw [he] at h
    simp only at h
    unfold Sse9.step
    rw [he]
    simp only
    split
    · rename_i i n hf
      rw [hf] at h
      simp only at h
      rw [h]; rfl
    · rename_i hf
      rw [hf] at h
      cases h
    · rename_i hf
      rw [hf] at h
      cases h
  · rw [Open9.step_eq_open he] at h
    unfold Sse9.step
    split
    · rename_i he'; exact absurd he' he
    · rw [h]; rfl

/-- **Every step is an `Open9` step with the XMM file unchanged, or an SSE step** at bytes
that `Ext8` and `Ext9` reject. -/
theorem step_cases {x y : XState} (h : step x = some y) :
    (Open9.step x.m = some y.m ∧ y.xmm = x.xmm) ∨
      (Open9.step x.m = none ∧ ∃ i n, fetchSse x.m.memory x.m.core.rip.toNat = some (some (i, n)) ∧
        (exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 n)).toOption =
          some y) := by
  unfold Sse9.step at h
  split at h
  · rename_i he
    split at h
    · rename_i i n hf
      cases ho : Open.ofResult (Ext9.execNew i x.m.core x.m.memory
          (x.m.core.rip + BitVec.ofNat 64 n)) with
      | none => rw [ho] at h; cases h
      | some m' =>
        rw [ho] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        left
        refine ⟨?_, rfl⟩
        unfold Open9.step
        rw [he]
        simp only
        rw [hf]
        exact ho
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
    cases ho : Open.step x.m with
    | none => rw [ho] at h; cases h
    | some m' =>
      rw [ho] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      left
      refine ⟨?_, rfl⟩
      unfold Open9.step
      split
      · rename_i he'; exact absurd he' he
      · exact ho

/-- `Open9` runs are runs, with the XMM file unchanged. -/
theorem run_of_open9 (xs : XFile) : ∀ (k : Nat) {a b : MState},
    run Open9.step k a = some b → run step k ⟨a, xs⟩ = some ⟨b, xs⟩
  | 0, a, b, h => by simp only [run, Option.some.injEq] at h ⊢; rw [h]
  | k + 1, a, b, h => by
    simp only [run] at h ⊢
    cases hs : Open9.step a with
    | none => rw [hs] at h; cases h
    | some a' =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      have h1 : step ⟨a, xs⟩ = some ⟨a', xs⟩ := step_of_open9 (x := ⟨a, xs⟩) hs
      rw [h1]
      exact run_of_open9 xs k h

theorem reaches_of_open9 (xs : XFile) {a b : MState} (h : Reaches Open9.step a b) :
    Reaches step ⟨a, xs⟩ ⟨b, xs⟩ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, run_of_open9 xs k hk⟩

/-! ## The SSE listing law -/

theorem decodeL_spec {bytes : List Byte} {i : Sse9.Instr} {n : Nat} (h : decodeL bytes = some (i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
      Open9.rawNotEof bytes = true ∧ ext9Bad bytes = true ∧ decodeSse bytes = some (i, n) ∧
      0 < n ∧ n ≤ maxInstrLength := by
  unfold decodeL at h
  split at h
  · rename_i i' n' hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hd, hc.2.2.2.2⟩
    · cases h
  · cases h

/-- **The fetch form of the SSE law**: bytes `w` fetched (with execute permission) at the
program counter that `decodeL` reads as an SSE form of length `l`, and that execute, are one
step. -/
theorem step_of_fetch_sse {x : XState} {l : Nat} {w : List Byte} {i : Sse9.Instr} {c : State}
    {xs : XFile} {mem : Memory} (fetched : x.m.memory.fetchBytes x.m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) = .ok c xs mem) :
    step x = some ⟨⟨c, mem⟩, xs⟩ := by
  obtain ⟨hnone, hbad, hne, hbad9, hsse, -, h15⟩ := decodeL_spec hdec
  obtain ⟨more, hmore, hf8⟩ := Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Ext9.fetchNew x.m.memory x.m.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    rw [hmore, decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : fetchSse x.m.memory x.m.core.rip.toNat = some (some (i, l)) := by
    unfold fetchSse
    rw [hmore, decodeSse_append hsse more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [Sse9.step, hf8, hfn, hfs, hx, XResult.toOption]

/-- **The SSE listing law.** -/
theorem step_of_listed_sse {x : XState} {base : Word} {code : List Byte} {o l : Nat} {i : Sse9.Instr}
    {c : State} {xs : XFile} {mem : Memory} (hl : Loaded x.m.memory base code)
    (hrip : x.m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) = .ok c xs mem) :
    step x = some ⟨⟨c, mem⟩, xs⟩ := by
  obtain ⟨-, -, -, -, -, h1, -⟩ := decodeL_spec hdec
  have hA : x.m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : x.m.memory.fetchBytes x.m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_sse fetched hdec hx

end Silmaril.Proofs.X86.Sse9
