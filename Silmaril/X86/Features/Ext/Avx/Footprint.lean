module

public import Silmaril.X86.Features.Ext.Avx.Semantics

/-!
# Memory footprint of the `avx` lane

What a retiring `exec` reads and writes in memory, stated against the
operand of the instruction (ModRM.rm when it is a memory operand):

* `exec_writesWithin`: a retiring instruction changes no mapping metadata and
  no byte outside the store operand of a store form (`store?`: the full-width
  stores write 32 bytes at VEX.256, 16 otherwise; the 128-bit extracts 16).
  Every other form leaves memory unchanged (`exec_memory_of_store_none`).
* `exec_reads`: a retiring form that is not a store depends on memory only
  through the `memBytes` bytes of its ModRM.rm memory operand: on any memory
  with the same bytes there, it retires to the same state, with that memory.

These are the facts an access report of the lane must cover
(`Process.LPS.Machines.X86Features.avxSpans_footprint`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.X86.Features.Avx

open Silmaril.Process (Memory)

/-- The bytes a store form writes at its memory operand. -/
def storeBytesLen (kind : StoreKind) (l : Bool) : Nat := if kind == .full && l then 32 else 16

theorem retireV_frame {s t : State} {memory memory' : Memory} {length : Nat} {l : Bool}
    {n : BitVec 4} {r : Except Fault (BitVec 256)}
    (h : retireV s memory length l n r = .retired t memory') :
    memory' = memory ∧ ∀ memory₂ : Memory, retireV s memory₂ length l n r = .retired t memory₂ := by
  cases r with
  | ok v =>
    simp only [retireV, Result.retired.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl⟩
  | error f => simp [retireV] at h

/-- `readSrc` reads only the `k` bytes at the memory operand. -/
theorem readSrc_congr (s : State) {memory memory₂ : Memory} (next : X86.Word) (rm : Opnd)
    (k : Nat) (align : Bool)
    (h : ∀ m, rm = .mem m → memory₂.readBytes (addr s m next) k = memory.readBytes (addr s m next) k) :
    readSrc s memory₂ next rm k align = readSrc s memory next rm k align := by
  cases rm with
  | reg n => rfl
  | mem m => simp only [readSrc, load, h m rfl]

/-- **Non-store forms**: a retiring form that is not a store leaves memory
unchanged, and retires to the same state on every memory on which its source
read gives the same value. -/
theorem exec_frame {i : Syntax} {n : Nat} {s t : State} {memory memory' : Memory}
    (hst : store? i.1.op = none) (h : exec i n s memory = .retired t memory') :
    memory' = memory ∧ ∀ memory₂ : Memory,
      readSrc s memory₂ (s.rip + BitVec.ofNat 64 n) i.1.rm (memBytes i.1.op i.1.l)
          (aligned i.1.op) =
        readSrc s memory (s.rip + BitVec.ofNat 64 n) i.1.rm (memBytes i.1.op i.1.l)
          (aligned i.1.op) →
      exec i n s memory₂ = .retired t memory₂ := by
  suffices key : ∀ src : Except Fault (BitVec 256),
      readSrc s memory (s.rip + BitVec.ofNat 64 n) i.1.rm (memBytes i.1.op i.1.l)
        (aligned i.1.op) = src →
      memory' = memory ∧ ∀ memory₂ : Memory,
        readSrc s memory₂ (s.rip + BitVec.ofNat 64 n) i.1.rm (memBytes i.1.op i.1.l)
          (aligned i.1.op) = src →
        exec i n s memory₂ = .retired t memory₂ from
    key _ rfl
  intro src hsrc
  simp only [exec, hsrc] at h
  cases h1 : intOp? i.1.op i.1.w with
  | some f =>
    simp only [h1] at h
    obtain ⟨hm, hr⟩ := retireV_frame h
    exact ⟨hm, fun memory₂ h₂ => by simp only [exec, h₂, h1]; exact hr memory₂⟩
  | none =>
  simp only [h1] at h
  cases h2 : intOpI? i.1.op with
  | some f =>
    simp only [h2] at h
    obtain ⟨hm, hr⟩ := retireV_frame h
    exact ⟨hm, fun memory₂ h₂ => by simp only [exec, h₂, h1, h2]; exact hr memory₂⟩
  | none =>
  simp only [h2] at h
  cases h3 : unOp? i.1.op with
  | some f =>
    simp only [h3] at h
    obtain ⟨hm, hr⟩ := retireV_frame h
    exact ⟨hm, fun memory₂ h₂ => by simp only [exec, h₂, h1, h2, h3]; exact hr memory₂⟩
  | none =>
  simp only [h3] at h
  cases h4 : shiftImm? i.1.op with
  | some f =>
    simp only [h4] at h
    obtain ⟨hm, hr⟩ := retireV_frame h
    exact ⟨hm, fun memory₂ h₂ => by simp only [exec, h₂, h1, h2, h3, h4]; exact hr memory₂⟩
  | none =>
  simp only [h4] at h
  cases h5 : blendV? i.1.op with
  | some f =>
    simp only [h5] at h
    obtain ⟨hm, hr⟩ := retireV_frame h
    exact ⟨hm, fun memory₂ h₂ => by simp only [exec, h₂, h1, h2, h3, h4, h5]; exact hr memory₂⟩
  | none =>
  simp only [h5] at h
  cases h6 : fpOp? i.1.op with
  | some q =>
    obtain ⟨p, kind, scalar⟩ := q
    simp only [h6] at h
    cases src with
    | error f => simp at h
    | ok b =>
      simp only at h
      cases h7 : Float.signal s.mxcsr
          (fpEval s.mxcsr p kind scalar i.1.l (s.ymm (vreg i.1.vvvv)) b).2 with
      | error e => simp [h7] at h
      | ok m =>
        simp only [h7, Result.retired.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, fun memory₂ h₂ => by simp only [exec, h₂, h1, h2, h3, h4, h5, h6, h7]⟩
  | none =>
  simp only [h6, hst] at h
  cases h8 : zero? i.1.op with
  | some f =>
    simp only [h8, Result.retired.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun memory₂ _ => by simp only [exec, h1, h2, h3, h4, h5, h6, hst, h8]⟩
  | none => simp [h8] at h

theorem exec_memory_of_store_none {i : Syntax} {n : Nat} {s t : State} {memory memory' : Memory}
    (hst : store? i.1.op = none) (h : exec i n s memory = .retired t memory') : memory' = memory :=
  (exec_frame hst h).1

/-- **Reads**: a retiring non-store form retires to the same state on every
memory with the same `memBytes` bytes at its memory operand. -/
theorem exec_reads {i : Syntax} {n : Nat} {s t : State} {memory memory' : Memory}
    (hst : store? i.1.op = none) (h : exec i n s memory = .retired t memory')
    (memory₂ : Memory)
    (hb : ∀ m, i.1.rm = .mem m →
      memory₂.readBytes (addr s m (s.rip + BitVec.ofNat 64 n)) (memBytes i.1.op i.1.l) =
        memory.readBytes (addr s m (s.rip + BitVec.ofNat 64 n)) (memBytes i.1.op i.1.l)) :
    exec i n s memory₂ = .retired t memory₂ :=
  (exec_frame hst h).2 memory₂ (readSrc_congr s _ _ _ _ hb)

theorem natLe_length (k v : Nat) : (natLe k v).length = k := by
  simp [natLe]

/-- **Writes**: a retiring instruction changes no mapping metadata and no byte
outside the store operand of a store form. -/
theorem exec_writesWithin {i : Syntax} {n : Nat} {s t : State} {memory memory' : Memory}
    (h : exec i n s memory = .retired t memory') :
    memory.WritesWithin memory' fun location =>
      ∃ m kind, i.1.rm = .mem m ∧ store? i.1.op = some kind ∧
        addr s m (s.rip + BitVec.ofNat 64 n) ≤ location ∧
        location < addr s m (s.rip + BitVec.ofNat 64 n) + storeBytesLen kind i.1.l := by
  cases hst : store? i.1.op with
  | none =>
    rw [exec_memory_of_store_none hst h]
    exact Memory.WritesWithin.refl _ _
  | some kind =>
    simp only [exec] at h
    split at h
    · obtain ⟨rfl, -⟩ := retireV_frame h; exact Memory.WritesWithin.refl _ _
    split at h
    · obtain ⟨rfl, -⟩ := retireV_frame h; exact Memory.WritesWithin.refl _ _
    split at h
    · obtain ⟨rfl, -⟩ := retireV_frame h; exact Memory.WritesWithin.refl _ _
    split at h
    · obtain ⟨rfl, -⟩ := retireV_frame h; exact Memory.WritesWithin.refl _ _
    split at h
    · obtain ⟨rfl, -⟩ := retireV_frame h; exact Memory.WritesWithin.refl _ _
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Result.retired.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Memory.WritesWithin.refl _ _
    simp only [hst] at h
    cases hrm : i.1.rm with
    | reg r =>
      simp only [hrm, Result.retired.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Memory.WritesWithin.refl _ _
    | mem m =>
      simp only [hrm] at h
      cases hc : (kind == .full && i.1.l) <;>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at h <;>
      · split at h
        · cases h
        · split at h
          · rename_i memory'' hw
            unfold storeBytes at hw
            simp only [Result.retired.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hwo := Memory.writeBytes_writesOnly hw
            rw [natLe_length] at hwo
            refine ⟨hwo.1, fun location hout => hwo.2 location ?_⟩
            by_contra hin
            apply hout
            exact ⟨m, kind, rfl, rfl, by
              simp only [storeBytesLen, hc, Bool.false_eq_true, ↓reduceIte]; omega⟩
          · cases h

end Silmaril.X86.Features.Avx
