module

public import Silmaril.Raw.Wasm.Component.ChunkedDecode.Frame
public import Silmaril.Wasm.Component.Chunked.Defs

/-!
# Chunked checks give runs of silmaril's core decoder on the whole input (raw proofs)

A reader run alone on a slice (`runAll`) runs the same inside the whole input (`run_of_runAll`);
vectors checked in pieces (`chkSeq`, `chkVec`) are `readVec` runs; instruction plans (`chkI`) are
`readSeq` runs (`readSeq_of_chkI`); code entry plans (`chkCode`) are `readCode` runs. Header:
`Silmaril.Wasm.Component.ChunkedDecode.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ChunkedDecode

open Silmaril.Wasm.Binary.Core.Decode

/-! ## Slices of a large input -/

open Silmaril.Wasm.Component.Chunked (arr runAll slice readAllOf readInstrs chkSeq chkVec chkSection)

theorem arr_toList (l : List UInt8) : (arr l).data.toList = l := rfl

theorem arr_size (l : List UInt8) : (arr l).size = l.length := rfl

/-- The bytes `l` occur at position `i` of `B`. -/
def At (B : List UInt8) (i : Nat) (l : List UInt8) : Prop :=
  (B.drop i).take l.length = l ∧ i + l.length ≤ B.length

theorem At.inside {B l : List UInt8} {i : Nat} (h : At B i l) (k : Nat) (hk : k ≤ l.length) :
    Inside (B.take i) (B.drop (i + l.length)) ⟨arr l, k⟩ ⟨arr B, i + k⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [arr_toList]
    conv_lhs => rw [← List.take_append_drop i B]
    rw [List.append_assoc]
    congr 1
    conv_lhs => rw [← List.take_append_drop l.length (B.drop i)]
    rw [h.1, List.drop_drop]
  · simp only [List.length_take]; have := h.2; omega
  · simp only [arr_size]; omega

/-- **A reader run on a slice runs the same inside the whole input.** -/
theorem run_of_runAll {α : Type} {p : DecodeM α} (hp : Frame p) {l B : List UInt8} {i : Nat}
    {a : α} (h : runAll p l = some a) (hB : At B i l) :
    p ⟨arr B, i⟩ = .ok (a, ⟨arr B, i + l.length⟩) := by
  unfold runAll at h
  split at h
  · rename_i x c hrun
    split at h
    · rename_i hpos
      cases h
      have hI := hB.inside 0 (Nat.zero_le _)
      simp only [Nat.add_zero] at hI
      obtain ⟨hb, C', hC', hI'⟩ := hp.run hI hrun
      rw [hC']
      have hC'b : C'.bytes = arr B := by
        apply ByteArray.ext; apply Array.ext'
        rw [hI'.1, hb, ← hI.1]
      have hC'p : C'.pos = i + l.length := by
        rw [hI'.2.1, hpos]; simp only [List.length_take]; have := hB.2; omega
      cases C'
      simp only at hC'b hC'p
      rw [hC'b, hC'p]
    · cases h
  · cases h

theorem cursor_eq_of_inside {l B : List UInt8} {i : Nat} (hB : At B i l) {c C : Cursor}
    (hI : Inside (B.take i) (B.drop (i + l.length)) c C) (hc : c.bytes = arr l) :
    C = ⟨arr B, i + c.pos⟩ := by
  obtain ⟨Cb, Cp⟩ := C
  have h1 : Cb = arr B := by
    apply ByteArray.ext; apply Array.ext'
    have := hI.1
    simp only at this
    rw [this, hc]
    exact (hB.inside 0 (Nat.zero_le _)).1.symm
  have h2 : Cp = i + c.pos := by
    have := hI.2.1
    simp only [List.length_take] at this
    have := hB.2
    omega
  rw [h1, h2]

theorem readVec_go_succ {α : Type} (f : DecodeM α) (n : Nat) (c : Cursor) :
    readVec.go f (n + 1) c = (do let x ← f; let xs ← readVec.go f n; pure (x :: xs)) c := rfl

/-- **Elements read until the end of a slice are elements of a vector of the whole input.** -/
theorem readVec_go_of_readAllOf {α : Type} {f : DecodeM α} (hf : Frame f) {l B : List UInt8}
    {i : Nat} (hB : At B i l) {m : Nat} {ys : List α} {D : Cursor}
    (hD : readVec.go f m ⟨arr B, i + l.length⟩ = .ok (ys, D)) :
    ∀ (fuel k : Nat) {xs : List α} {c' : Cursor}, k ≤ l.length →
      readAllOf f fuel ⟨arr l, k⟩ = .ok (xs, c') → c'.pos = l.length →
      readVec.go f (xs.length + m) ⟨arr B, i + k⟩ = .ok (xs ++ ys, D) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k xs c' hk h hc'
    simp only [readAllOf, pure, StateT.pure, Except.pure] at h
    cases h
    simp only at hc'
    subst hc'
    simpa using hD
  | succ fuel ih =>
    intro k xs c' hk h hc'
    unfold readAllOf at h
    rw [bind_ok (remaining_apply _)] at h
    simp only [arr_size] at h
    by_cases hz : l.length - k = 0
    · simp only [hz, ↓reduceIte, pure, StateT.pure, Except.pure] at h
      cases h
      simp only at hc'
      subst hc'
      simpa using hD
    · simp only [hz, ↓reduceIte] at h
      obtain ⟨x, c₁, h₁, h⟩ := ok_bind h
      obtain ⟨xs', c₂, h₂, h⟩ := ok_bind h
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hI := hB.inside k hk
      obtain ⟨hb₁, C₁, hC₁, hI₁⟩ := hf.run hI h₁
      have hc₁ : c₁ = ⟨arr l, c₁.pos⟩ := by cases c₁; simp only at hb₁ ⊢; rw [hb₁]
      have hk₁ : c₁.pos ≤ l.length := by have := hI₁.2.2; rw [hb₁] at this; exact this
      have hC₁' := cursor_eq_of_inside hB hI₁ hb₁
      rw [hc₁] at h₂
      have := ih c₁.pos hk₁ h₂ hc'
      rw [show (x :: xs').length + m = (xs'.length + m) + 1 by simp; omega, readVec_go_succ,
        bind_ok hC₁, hC₁', bind_ok this]
      rfl

theorem At.take {B r : List UInt8} {i : Nat} (h : At B i r) (k : Nat) : At B i (r.take k) := by
  refine ⟨?_, ?_⟩
  · have := h.1
    rw [List.length_take]
    conv_rhs => rw [← this]
    rw [List.take_take, Nat.min_comm]
  · have := h.2; simp only [List.length_take]; omega

theorem At.drop {B r : List UInt8} {i : Nat} (h : At B i r) (k : Nat) :
    At B (i + (r.take k).length) (r.drop k) := by
  refine ⟨?_, ?_⟩
  · have := h.1
    simp only [List.length_take, List.length_drop]
    conv_rhs => rw [← this]
    rw [List.drop_take, List.drop_drop]
    have h2 := h.2
    by_cases hk : k ≤ r.length
    · rw [Nat.min_eq_left hk]
    · rw [Nat.min_eq_right (by omega), show r.length - k = 0 by omega, List.take_zero,
        List.take_zero]
  · have := h.2; simp only [List.length_take, List.length_drop]; omega

theorem chkSeq_rest {α : Type} {f : DecodeM α} : ∀ {ks : List Nat} {r : List UInt8} {xs : List α}
    {rest : List UInt8}, chkSeq f ks r = some (xs, rest) → rest.length ≤ r.length
  | [], r, xs, rest, h => by simp only [chkSeq, Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]
  | k :: ks, r, xs, rest, h => by
    simp only [chkSeq] at h
    split at h
    · obtain ⟨⟨_, _⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at h''
      rw [← h''.2]
      exact (chkSeq_rest h').trans (by simp)
    · cases h

/-- **Pieces checked separately are one vector run of the whole input.** -/
theorem readVec_go_of_chkSeq {α : Type} {f : DecodeM α} (hf : Frame f) {B : List UInt8} :
    ∀ {ks : List Nat} {r : List UInt8} {i : Nat} {xs : List α} {rest : List UInt8} {m : Nat}
      {ys : List α} {D : Cursor}, chkSeq f ks r = some (xs, rest) → At B i r →
      readVec.go f m ⟨arr B, i + (r.length - rest.length)⟩ = .ok (ys, D) →
      readVec.go f (xs.length + m) ⟨arr B, i⟩ = .ok (xs ++ ys, D)
  | [], r, i, xs, rest, m, ys, D, h, _, hD => by
    simp only [chkSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hD
  | k :: ks, r, i, xs, rest, m, ys, D, h, hB, hD => by
    simp only [chkSeq] at h
    split at h
    · rename_i xs₁ h₁
      obtain ⟨⟨xs₂, rest₂⟩, h₂, h₃⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at h₃
      obtain ⟨rfl, rfl⟩ := h₃
      have hl := chkSeq_rest h₂
      have hlen : (r.take k).length + (r.drop k).length = r.length := by simp; omega
      have hD' : readVec.go f m ⟨arr B, i + (r.take k).length + ((r.drop k).length - rest₂.length)⟩
          = .ok (ys, D) := by
        rw [show i + (r.take k).length + ((r.drop k).length - rest₂.length) =
          i + (r.length - rest₂.length) by omega]
        exact hD
      have ih := readVec_go_of_chkSeq hf h₂ (hB.drop k) hD'
      unfold runAll at h₁
      split at h₁
      · rename_i x c hrun
        split at h₁
        · rename_i hpos
          cases h₁
          have := readVec_go_of_readAllOf hf (hB.take k) (m := xs₂.length + m) ih (k + 1) 0
            (Nat.zero_le _) hrun hpos
          rw [List.length_append, Nat.add_assoc, List.append_assoc]
          simpa using this
        · cases h₁
      · cases h₁
    · cases h

theorem readCount_at {B : List UInt8} {x n k : Nat} (hu : readU 32 ⟨arr B, x⟩ = .ok (n, ⟨arr B, x + k⟩))
    (hn : n ≤ B.length - (x + k)) : readCount ⟨arr B, x⟩ = .ok (n, ⟨arr B, x + k⟩) := by
  unfold readCount
  rw [bind_ok hu, bind_ok (remaining_apply _)]
  simp only [arr_size, hn, ↓reduceIte]
  rfl

/-- **A vector checked in pieces is read by `readVec` on the whole input.** -/
theorem readVec_of_chkVec {α : Type} {f : DecodeM α} (hf : Frame f) {B body : List UInt8}
    {x kc : Nat} {ks : List Nat} {xs : List α} (h : chkVec f kc ks body = some xs)
    (hB : At B x body)
    (hn : ∀ n, runAll (readU 32) (body.take kc) = some n → n ≤ body.length - kc) :
    readVec f ⟨arr B, x⟩ = .ok (xs, ⟨arr B, x + body.length⟩) := by
  unfold chkVec at h
  split at h
  · rename_i n xs' hc hs
    split at h
    · rename_i hlen
      cases h
      have hu := run_of_runAll (frame_readU 32) hc (hB.take kc)
      have hk : (body.take kc).length ≤ body.length := by simp
      have hcount := readCount_at hu (by have := hn n hc; have := hB.2; simp at this ⊢; omega)
      unfold readVec
      rw [bind_ok hcount]
      have hD : readVec.go f 0 ⟨arr B, x + (body.take kc).length +
          ((body.drop kc).length - ([] : List UInt8).length)⟩ =
          .ok ([], ⟨arr B, x + body.length⟩) := by
        simp only [readVec.go, List.length_nil, Nat.sub_zero, List.length_drop, pure,
          StateT.pure, Except.pure, List.length_take]
        congr 3
        omega
      have := readVec_go_of_chkSeq hf hs (hB.drop kc) hD
      rw [← hlen]
      simpa using this
    · cases h
  · cases h

/-! ## Sections of a module -/

theorem readByte_at {B : List UInt8} {p : Nat} {b : UInt8} (h : B[p]? = some b) :
    readByte ⟨arr B, p⟩ = .ok (b, ⟨arr B, p + 1⟩) := by
  have hp : p < B.length := (List.getElem?_eq_some_iff.1 h).1
  rw [readByte_apply]
  simp only [arr_size, hp, ↓reduceDIte]
  congr
  rw [bget]
  exact (List.getElem?_eq_some_iff.1 h).2

theorem go_known {B : List UInt8} {fuel last p x size : Nat} {b : UInt8} {S S' : Sections}
    (hb : B[p]? = some b) (hu : readU 32 ⟨arr B, p + 1⟩ = .ok (size, ⟨arr B, x⟩))
    (hsz : x + size ≤ B.length) (hid : b.toNat ≠ 0) (hlast : last < sectionRank b.toNat)
    (hbody : readSectionBody b.toNat S ⟨arr B, x⟩ = .ok (S', ⟨arr B, x + size⟩)) :
    readModule.go (fuel + 1) last S ⟨arr B, p⟩ =
      readModule.go fuel (sectionRank b.toNat) S' ⟨arr B, x + size⟩ := by
  have hp : p < B.length := (List.getElem?_eq_some_iff.1 hb).1
  simp only [readModule.go]
  rw [bind_ok (remaining_apply _)]
  simp only [arr_size, show (B.length - p == 0) = false by simp; omega, Bool.false_eq_true,
    ↓reduceIte]
  rw [bind_ok (readByte_at hb), bind_ok hu, bind_ok (remaining_apply _)]
  simp only [arr_size, show size ≤ B.length - x by omega, ↓reduceIte]
  simp only [show (b.toNat == 0) = false by simp; omega, Bool.false_eq_true, ↓reduceIte, hlast]
  rw [bind_ok hbody, bind_ok (remaining_apply _)]
  simp only [arr_size, show B.length - x - (B.length - (x + size)) = size by omega, beq_self_eq_true,
    ↓reduceIte]

/-! ## Instruction plans -/

open Silmaril.Wasm.Component.Chunked (IPlan chkI blockInstr) in
theorem readInstr_term_fails (f : Nat) {b : UInt8} (hb : (b == 0x0B || b == 0x05) = true)
    (c : Cursor) (r : Silmaril.Wasm.Instr × Cursor) : readInstr f b.toNat c ≠ .ok r := by
  have hb' : b.toNat = 11 ∨ b.toNat = 5 := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with rfl | rfl <;> simp
  cases f with
  | zero => simp only [readInstr]; exact decodeError_ne_ok _ _ _
  | succ f =>
    rcases hb' with h | h <;> rw [h] <;>
      simp only [readInstr, readPlain, readOpOnly] <;> exact decodeError_ne_ok _ _ _

theorem readSeq_step {F : Nat} {C C₁ C₂ D : Cursor} {b : UInt8} {i : Silmaril.Wasm.Instr}
    {rest : List Silmaril.Wasm.Instr} {t : UInt8} (h₁ : readByte C = .ok (b, C₁))
    (hb : (b == 0x0B || b == 0x05) = false) (h₂ : readInstr F b.toNat C₁ = .ok (i, C₂))
    (h₃ : readSeq F C₂ = .ok ((rest, t), D)) : readSeq (F + 1) C = .ok ((i :: rest, t), D) := by
  simp only [readSeq]
  rw [bind_ok h₁]
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  rw [bind_ok h₂, bind_ok h₃]
  rfl

theorem readSeq_term {F : Nat} {C C₁ : Cursor} {b : UInt8} (h₁ : readByte C = .ok (b, C₁))
    (hb : (b == 0x0B || b == 0x05) = true) : readSeq (F + 1) C = .ok (([], b), C₁) := by
  simp only [readSeq]
  rw [bind_ok h₁]
  simp only [hb, ↓reduceIte]
  rfl

theorem readSeq_pos {F : Nat} {c : Cursor} {r : List Silmaril.Wasm.Instr × UInt8} {c' : Cursor}
    (h : readSeq F c = .ok (r, c')) : 1 ≤ F := by
  cases F with
  | zero => simp only [readSeq] at h; exact absurd h (decodeError_ne_ok _ _ _)
  | succ F => omega

theorem le_apply {α : Type} {p q : DecodeM α} (h : Le p q) {c : Cursor} {r : α × Cursor}
    (hp : p c = .ok r) : q c = .ok r := by
  unfold Le at h; exact h c r hp

theorem mono_apply {α : Type} {p : DecodeM α} (h : Mono p) {c c' : Cursor} {x : α}
    (hp : p c = .ok (x, c')) : c.pos ≤ c'.pos := by
  unfold Mono at h; exact h c x c' hp

/-- **A leaf of an instruction plan**: instructions decoded alone on their slice are read by
`readSeq` inside the whole input, before what follows. -/
theorem readSeq_of_readInstrs {l B : List UInt8} {y : Nat} (hB : At B y l) {G : Nat}
    {is₂ : List Silmaril.Wasm.Instr} {t : UInt8} {D : Cursor}
    (hcont : readSeq G ⟨arr B, y + l.length⟩ = .ok ((is₂, t), D)) :
    ∀ (fuel j : Nat) {xs : List Silmaril.Wasm.Instr} {c' : Cursor}, j ≤ l.length →
      Silmaril.Wasm.Component.Chunked.readInstrs fuel ⟨arr l, j⟩ = .ok (xs, c') → c'.pos = l.length →
      ∀ F, fuel ≤ F → G + (l.length - j) ≤ F →
        readSeq F ⟨arr B, y + j⟩ = .ok ((xs ++ is₂, t), D) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j xs c' hj h hc' F _ hF
    simp only [Silmaril.Wasm.Component.Chunked.readInstrs, pure, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only at hc'
    subst hc'
    simpa using le_apply ((readSeq_mono G F (by omega)).2) hcont
  | succ fuel ih =>
    intro j xs c' hj h hc' F hfF hF
    unfold Silmaril.Wasm.Component.Chunked.readInstrs at h
    rw [bind_ok (remaining_apply _)] at h
    simp only [arr_size] at h
    by_cases hz : l.length - j = 0
    · simp only [hz, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only at hc'
      subst hc'
      simpa using le_apply ((readSeq_mono G F (by omega)).2) hcont
    · simp only [hz, ↓reduceIte] at h
      obtain ⟨b, c₁, h₁, h⟩ := ok_bind h
      obtain ⟨i, c₂, h₂, h⟩ := ok_bind h
      obtain ⟨xs', c₃, h₃, h⟩ := ok_bind h
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hI := hB.inside j hj
      obtain ⟨hb₁, C₁, hC₁, hI₁⟩ := frame_readByte.run hI h₁
      have hp₁ : c₁.pos = j + 1 := by
        rw [readByte_apply] at h₁; split at h₁
        · cases h₁; rfl
        · cases h₁
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hterm : (b == 0x0B || b == 0x05) = false := by
        cases hbt : (b == 0x0B || b == 0x05)
        · rfl
        · exact absurd h₂ (readInstr_term_fails fuel hbt _ _)
      have h₂' := le_apply ((readSeq_mono fuel F' (by omega)).1 b.toNat) h₂
      obtain ⟨hb₂, C₂, hC₂, hI₂⟩ := (frame_readInstr_readSeq F').1 b.toNat |>.run hI₁ h₂'
      have hm₂ : c₁.pos ≤ c₂.pos := mono_apply ((mono_readInstr_readSeq fuel).1 b.toNat) h₂
      have hc₂ : c₂ = ⟨arr l, c₂.pos⟩ := by
        cases c₂; simp only at hb₂ hb₁ ⊢; rw [hb₂, hb₁]
      have hj₂ : c₂.pos ≤ l.length := by have := hI₂.2.2; rw [hb₂, hb₁] at this; exact this
      rw [hc₂] at h₃
      have := ih c₂.pos hj₂ h₃ hc' F' (by omega) (by omega)
      have e₁ := cursor_eq_of_inside hB hI₁ (by rw [hb₁])
      rw [e₁] at hC₁ hC₂
      rw [cursor_eq_of_inside hB hI₂ (by rw [hb₂, hb₁])] at hC₂
      exact readSeq_step hC₁ hterm hC₂ this

open Silmaril.Wasm.Component.Chunked (IPlan chkI blockInstr)

theorem chkI_rest : ∀ {p : IPlan} {r : List UInt8} {is : List Silmaril.Wasm.Instr}
    {rest : List UInt8}, chkI p r = some (is, rest) → rest.length ≤ r.length
  | .nil, r, is, rest, h => by simp only [chkI, Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]
  | .leaf k p, r, is, rest, h => by
    simp only [chkI] at h
    split at h
    · obtain ⟨⟨_, _⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at h''
      rw [← h''.2]
      exact (chkI_rest h').trans (by simp)
    · cases h
  | .block k body p, r, is, rest, h => by
    simp only [chkI] at h
    split at h
    · rename_i op r₁
      split at h
      · rename_i bt is' r₂ _ hbody
        split at h
        · obtain ⟨⟨_, _⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at h''
          rw [← h''.2]
          have := chkI_rest hbody
          have := chkI_rest h'
          simp at *; omega
        · cases h
      · cases h
    · cases h
  | .ifElse k thn els p, r, is, rest, h => by
    simp only [chkI] at h
    split at h
    · rename_i op r₁
      split at h
      · split at h
        · rename_i bt is₁ r₂ _ hthn
          split at h
          · rename_i is₂ r₃ hels
            obtain ⟨⟨_, _⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at h''
            rw [← h''.2]
            have := chkI_rest hthn
            have := chkI_rest hels
            have := chkI_rest h'
            simp at *; omega
          · cases h
        · cases h
      · cases h
    · cases h

theorem readInstr_block {F : Nat} {op : UInt8} {C C₁ C₂ : Cursor} {bt : Silmaril.Wasm.BlockType}
    {body : List Silmaril.Wasm.Instr} {i : Silmaril.Wasm.Instr}
    (hbt : readBlockType C = .ok (bt, C₁)) (hs : readSeq F C₁ = .ok ((body, 0x0B), C₂))
    (hi : blockInstr op bt body = some i) : readInstr (F + 1) op.toNat C = .ok (i, C₂) := by
  unfold blockInstr at hi
  by_cases h2 : op = 0x02
  · subst h2
    simp only [↓reduceIte, Option.some.injEq] at hi
    subst hi
    simp only [readInstr, show (0x02 : UInt8).toNat = 2 from rfl]
    rw [bind_ok hbt, bind_ok hs]
    rfl
  · by_cases h3 : op = 0x03
    · subst h3
      simp only [show ¬ (0x03 : UInt8) = 0x02 by decide, ↓reduceIte, Option.some.injEq] at hi
      subst hi
      simp only [readInstr, show (0x03 : UInt8).toNat = 3 from rfl]
      rw [bind_ok hbt, bind_ok hs]
      rfl
    · by_cases h4 : op = 0x04
      · subst h4
        simp only [show ¬ (0x04 : UInt8) = 0x02 by decide, show ¬ (0x04 : UInt8) = 0x03 by decide,
          ↓reduceIte, Option.some.injEq] at hi
        subst hi
        simp only [readInstr, show (0x04 : UInt8).toNat = 4 from rfl]
        rw [bind_ok hbt, bind_ok hs]
        rfl
      · simp only [h2, h3, h4, ↓reduceIte] at hi
        cases hi

theorem readInstr_ifElse {F : Nat} {C C₁ C₂ C₃ : Cursor} {bt : Silmaril.Wasm.BlockType}
    {thn els : List Silmaril.Wasm.Instr}
    (hbt : readBlockType C = .ok (bt, C₁)) (hs : readSeq F C₁ = .ok ((thn, 0x05), C₂))
    (he : readSeq F C₂ = .ok ((els, 0x0B), C₃)) :
    readInstr (F + 1) (0x04 : UInt8).toNat C = .ok (.if_ bt thn els, C₃) := by
  simp only [readInstr, show (0x04 : UInt8).toNat = 4 from rfl]
  rw [bind_ok hbt, bind_ok hs]
  simp only [show ((0x05 : UInt8) == 0x0B) = false by decide, Bool.false_eq_true, ↓reduceIte]
  rw [bind_ok he]
  rfl

theorem chkI_prefix : ∀ {p : IPlan} {r : List UInt8} {is : List Silmaril.Wasm.Instr}
    {rest : List UInt8}, chkI p r = some (is, rest) → ∃ P, r = P ++ rest
  | .nil, r, is, rest, h => by
    simp only [chkI, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨[], by rw [← h.2]; rfl⟩
  | .leaf k p, r, is, rest, h => by
    simp only [chkI] at h
    split at h
    · obtain ⟨⟨_, _⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at h''
      obtain ⟨P, hP⟩ := chkI_prefix h'
      refine ⟨r.take k ++ P, ?_⟩
      rw [← h''.2, List.append_assoc, ← hP, List.take_append_drop]
    · cases h
  | .block k body p, r, is, rest, h => by
    simp only [chkI] at h
    split at h
    · rename_i op r₁
      split at h
      · rename_i bt is' r₂ _ hbody
        split at h
        · obtain ⟨⟨_, _⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at h''
          obtain ⟨P₁, hP₁⟩ := chkI_prefix hbody
          obtain ⟨P₂, hP₂⟩ := chkI_prefix h'
          refine ⟨op :: (r₁.take (k - 1) ++ P₁ ++ 0x0B :: P₂), ?_⟩
          rw [← h''.2, List.cons_append]
          congr 1
          conv_lhs => rw [← List.take_append_drop (k - 1) r₁, hP₁, hP₂]
          simp
        · cases h
      · cases h
    · cases h
  | .ifElse k thn els p, r, is, rest, h => by
    simp only [chkI] at h
    split at h
    · rename_i op r₁
      split at h
      · split at h
        · rename_i bt is₁ r₂ _ hthn
          split at h
          · rename_i is₂ r₃ hels
            obtain ⟨⟨_, _⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at h''
            obtain ⟨P₁, hP₁⟩ := chkI_prefix hthn
            obtain ⟨P₂, hP₂⟩ := chkI_prefix hels
            obtain ⟨P₃, hP₃⟩ := chkI_prefix h'
            refine ⟨op :: (r₁.take (k - 1) ++ P₁ ++ 0x05 :: P₂ ++ 0x0B :: P₃), ?_⟩
            rw [← h''.2, List.cons_append]
            congr 1
            conv_lhs => rw [← List.take_append_drop (k - 1) r₁, hP₁, hP₂, hP₃]
            simp
          · cases h
        · cases h
      · cases h
    · cases h

theorem At.left {B P Q : List UInt8} {y : Nat} (h : At B y (P ++ Q)) : At B y P := by
  have := h.take P.length
  rwa [List.take_left] at this

theorem At.right {B P Q : List UInt8} {y : Nat} (h : At B y (P ++ Q)) : At B (y + P.length) Q := by
  have := h.drop P.length
  rwa [List.take_left, List.drop_left] at this

theorem At.get {B r : List UInt8} {y : Nat} {b : UInt8} (h : At B y (b :: r)) : B[y]? = some b := by
  have h1 := h.1
  have h2 := h.2
  simp only [List.length_cons] at h1 h2
  have : (List.take (r.length + 1) (List.drop y B))[0]? = some b := by rw [h1]; rfl
  rw [List.getElem?_take, List.getElem?_drop] at this
  · simpa using this

theorem blockInstr_op {op : UInt8} {bt : Silmaril.Wasm.BlockType} {is : List Silmaril.Wasm.Instr}
    {i : Silmaril.Wasm.Instr} (h : blockInstr op bt is = some i) :
    (op == 0x0B || op == 0x05) = false := by
  unfold blockInstr at h
  by_cases h2 : op = 0x02
  · subst h2; decide
  · by_cases h3 : op = 0x03
    · subst h3; decide
    · by_cases h4 : op = 0x04
      · subst h4; decide
      · simp only [h2, h3, h4, ↓reduceIte] at h; cases h

theorem readSeq_end {B : List UInt8} {y : Nat} {r : List UInt8} {b : UInt8}
    (hB : At B y (b :: r)) (hb : (b == 0x0B || b == 0x05) = true) :
    readSeq 1 ⟨arr B, y⟩ = .ok (([], b), ⟨arr B, y + 1⟩) :=
  readSeq_term (readByte_at hB.get) hb

/-- **An instruction plan's instructions are read by `readSeq`** inside the whole input, before
what follows them. -/
theorem readSeq_of_chkI {B : List UInt8} : ∀ (p : IPlan) {r : List UInt8} {y : Nat}
    {is : List Silmaril.Wasm.Instr} {rest P : List UInt8}, chkI p r = some (is, rest) →
    rest ≠ [] → At B y r → r = P ++ rest →
    ∀ {G : Nat} {is₂ : List Silmaril.Wasm.Instr} {t : UInt8} {D : Cursor},
      readSeq G ⟨arr B, y + P.length⟩ = .ok ((is₂, t), D) →
      ∀ F, G + P.length ≤ F → readSeq F ⟨arr B, y⟩ = .ok ((is ++ is₂, t), D)
  | .nil, r, y, is, rest, P, h, _, _, hP, G, is₂, t, D, hc, F, hF => by
    simp only [chkI, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hP0 : P = [] := by simpa using congrArg List.length hP
    subst hP0
    simpa using le_apply ((readSeq_mono G F (by simpa using hF)).2) (by simpa using hc)
  | .leaf k p, r, y, is, rest, P, h, hne, hB, hP, G, is₂, t, D, hc, F, hF => by
    simp only [chkI] at h
    split at h
    · rename_i is₁ h₁
      obtain ⟨⟨q₁, q₂⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at h''
      obtain ⟨rfl, rfl⟩ := h''
      obtain ⟨P', hP'⟩ := chkI_prefix h'
      have hk : k < r.length := by
        have h1 : (r.drop k).length = P'.length + q₂.length := by rw [hP']; simp
        have h2 : q₂.length ≠ 0 := fun h0 => hne (List.length_eq_zero_iff.1 h0)
        rw [List.length_drop] at h1
        omega
      have htk : (r.take k).length = k := by simp; omega
      have hPP : P = r.take k ++ P' := by
        have : r.take k ++ (P' ++ q₂) = P ++ q₂ := by rw [← hP', List.take_append_drop, ← hP]
        rw [← List.append_assoc] at this
        exact (List.append_cancel_right this).symm
      have hBt : At B y (r.take k) := by
        have := hB; rw [← List.take_append_drop k r] at this; exact this.left
      have hBd : At B (y + k) (r.drop k) := by
        have := hB; rw [← List.take_append_drop k r] at this; have := this.right; rwa [htk] at this
      have hG := readSeq_pos hc
      have hc' : readSeq G ⟨arr B, y + k + P'.length⟩ = .ok ((is₂, t), D) := by
        rw [hPP, List.length_append, htk, ← Nat.add_assoc] at hc; exact hc
      have ih := readSeq_of_chkI p h' hne hBd hP' hc'
      have hcont := ih (G + P'.length) le_rfl
      unfold runAll at h₁
      split at h₁
      · rename_i x c hrun
        split at h₁
        · rename_i hpos
          cases h₁
          have hcont' : readSeq (G + P'.length) ⟨arr B, y + (r.take k).length⟩ =
              .ok ((q₁ ++ is₂, t), D) := by rw [htk]; exact hcont
          have := readSeq_of_readInstrs hBt hcont' (k + 1) 0 (Nat.zero_le _) hrun hpos F
            (by rw [hPP] at hF; simp at hF; omega) (by rw [hPP] at hF; simp at hF ⊢; omega)
          simpa using this
        · cases h₁
      · cases h₁
    · cases h
  | .block k body p, r, y, is, rest, P, h, hne, hB, hP, G, is₂, t, D, hc, F, hF => by
    simp only [chkI] at h
    split at h
    · rename_i op r₁
      split at h
      · rename_i bt isb r₂ hbt hbody
        split at h
        · rename_i i hi
          obtain ⟨⟨q₁, q₂⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at h''
          obtain ⟨rfl, rfl⟩ := h''
          obtain ⟨Pb, hPb⟩ := chkI_prefix hbody
          obtain ⟨Pp, hPp⟩ := chkI_prefix h'
          have hr₁ : r₁ = r₁.take (k - 1) ++ (Pb ++ 0x0B :: (Pp ++ q₂)) := by
            rw [← hPp, ← hPb, List.take_append_drop]
          have hPP : P = op :: (r₁.take (k - 1) ++ Pb ++ 0x0B :: Pp) := by
            have : op :: r₁ = P ++ q₂ := hP
            rw [hr₁] at this
            have e : op :: (r₁.take (k - 1) ++ Pb ++ 0x0B :: Pp) ++ q₂ = P ++ q₂ := by
              rw [← this]; simp
            exact (List.append_cancel_right e).symm
          set a := (r₁.take (k - 1)).length with ha
          have hB₁ : At B (y + 1) r₁ := by
            have := hB; rw [show op :: r₁ = [op] ++ r₁ from rfl] at this; exact this.right
          have hBt : At B (y + 1) (r₁.take (k - 1)) := by
            have := hB₁; rw [hr₁] at this; exact this.left
          have hBd : At B (y + 1 + a) (Pb ++ 0x0B :: (Pp ++ q₂)) := by
            have := hB₁; rw [hr₁] at this; exact this.right
          have hB0 : At B (y + 1 + a + Pb.length) (0x0B :: (Pp ++ q₂)) := hBd.right
          have hB₂ : At B (y + 1 + a + Pb.length + 1) (Pp ++ q₂) := by
            have := hB0; rw [show (0x0B : UInt8) :: (Pp ++ q₂) = [0x0B] ++ (Pp ++ q₂) from rfl] at this
            exact this.right
          have hend := readSeq_end hB0 (by decide)
          have hBd' : At B (y + 1 + a) (r₁.drop (k - 1)) := by rw [hPb, hPp]; exact hBd
          have hbody' := readSeq_of_chkI body hbody (by simp) hBd' hPb hend
          have hbtB : readBlockType ⟨arr B, y + 1⟩ = .ok (bt, ⟨arr B, y + 1 + a⟩) :=
            run_of_runAll frame_readBlockType hbt hBt
          have hB₂' : At B (y + 1 + a + Pb.length + 1) r₂ := by rw [hPp]; exact hB₂
          have hG := readSeq_pos hc
          have hPl : P.length = a + Pb.length + Pp.length + 2 := by
            rw [hPP]; simp only [List.length_cons, List.length_append, ← ha]; omega
          have hc' : readSeq G ⟨arr B, y + 1 + a + Pb.length + 1 + Pp.length⟩ = .ok ((is₂, t), D) := by
            rw [show y + 1 + a + Pb.length + 1 + Pp.length = y + P.length by omega]; exact hc
          have ihp := readSeq_of_chkI p h' hne hB₂' hPp hc'
          obtain ⟨F₁, rfl⟩ : ∃ F₁, F = F₁ + 2 := ⟨F - 2, by omega⟩
          have hi' : readInstr (F₁ + 1) op.toNat ⟨arr B, y + 1⟩ =
              .ok (i, ⟨arr B, y + 1 + a + Pb.length + 1⟩) :=
            readInstr_block hbtB (by simpa using hbody' F₁ (by omega)) hi
          have := readSeq_step (readByte_at hB.get) (blockInstr_op hi) hi' (ihp (F₁ + 1) (by omega))
          simpa using this
        · cases h
      · cases h
    · cases h
  | .ifElse k thn els p, r, y, is, rest, P, h, hne, hB, hP, G, is₂, t, D, hc, F, hF => by
    simp only [chkI] at h
    split at h
    · rename_i op r₁
      split at h
      · rename_i h4
        subst h4
        split at h
        · rename_i bt ist r₂ hbt hthn
          split at h
          · rename_i ise r₃ hels
            obtain ⟨⟨q₁, q₂⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at h''
            obtain ⟨rfl, rfl⟩ := h''
            obtain ⟨P₁, hP₁⟩ := chkI_prefix hthn
            obtain ⟨P₂, hP₂⟩ := chkI_prefix hels
            obtain ⟨Pp, hPp⟩ := chkI_prefix h'
            have hr₁ : r₁ = r₁.take (k - 1) ++ (P₁ ++ 0x05 :: (P₂ ++ 0x0B :: (Pp ++ q₂))) := by
              rw [← hPp, ← hP₂, ← hP₁, List.take_append_drop]
            have hPP : P = 0x04 :: (r₁.take (k - 1) ++ P₁ ++ 0x05 :: P₂ ++ 0x0B :: Pp) := by
              have : (0x04 : UInt8) :: r₁ = P ++ q₂ := hP
              rw [hr₁] at this
              have e : (0x04 : UInt8) :: (r₁.take (k - 1) ++ P₁ ++ 0x05 :: P₂ ++ 0x0B :: Pp) ++ q₂ =
                  P ++ q₂ := by rw [← this]; simp
              exact (List.append_cancel_right e).symm
            set a := (r₁.take (k - 1)).length with ha
            have hB₁ : At B (y + 1) r₁ := by
              have := hB; rw [show (0x04 : UInt8) :: r₁ = [0x04] ++ r₁ from rfl] at this
              exact this.right
            have hBt : At B (y + 1) (r₁.take (k - 1)) := by
              have := hB₁; rw [hr₁] at this; exact this.left
            have hBd : At B (y + 1 + a) (P₁ ++ 0x05 :: (P₂ ++ 0x0B :: (Pp ++ q₂))) := by
              have := hB₁; rw [hr₁] at this; exact this.right
            have hB5 : At B (y + 1 + a + P₁.length) (0x05 :: (P₂ ++ 0x0B :: (Pp ++ q₂))) :=
              hBd.right
            have hBe : At B (y + 1 + a + P₁.length + 1) (P₂ ++ 0x0B :: (Pp ++ q₂)) := by
              have := hB5
              rw [show (0x05 : UInt8) :: (P₂ ++ 0x0B :: (Pp ++ q₂)) =
                [0x05] ++ (P₂ ++ 0x0B :: (Pp ++ q₂)) from rfl] at this
              exact this.right
            have hB0 : At B (y + 1 + a + P₁.length + 1 + P₂.length) (0x0B :: (Pp ++ q₂)) :=
              hBe.right
            have hB₃ : At B (y + 1 + a + P₁.length + 1 + P₂.length + 1) (Pp ++ q₂) := by
              have := hB0
              rw [show (0x0B : UInt8) :: (Pp ++ q₂) = [0x0B] ++ (Pp ++ q₂) from rfl] at this
              exact this.right
            have hthnB : At B (y + 1 + a) (r₁.drop (k - 1)) := by
              rw [hP₁, hP₂, hPp]; exact hBd
            have helsB : At B (y + 1 + a + P₁.length + 1) r₂ := by rw [hP₂, hPp]; exact hBe
            have hthn' := readSeq_of_chkI thn hthn (by simp) hthnB hP₁
              (readSeq_end hB5 (by decide))
            have hels' := readSeq_of_chkI els hels (by simp) helsB hP₂
              (readSeq_end hB0 (by decide))
            have hbtB : readBlockType ⟨arr B, y + 1⟩ = .ok (bt, ⟨arr B, y + 1 + a⟩) :=
              run_of_runAll frame_readBlockType hbt hBt
            have hB₃' : At B (y + 1 + a + P₁.length + 1 + P₂.length + 1) r₃ := by
              rw [hPp]; exact hB₃
            have hG := readSeq_pos hc
            have hPl : P.length = a + P₁.length + P₂.length + Pp.length + 3 := by
              rw [hPP]; simp only [List.length_cons, List.length_append, ← ha]; omega
            have hc' : readSeq G ⟨arr B, y + 1 + a + P₁.length + 1 + P₂.length + 1 + Pp.length⟩ =
                .ok ((is₂, t), D) := by
              rw [show y + 1 + a + P₁.length + 1 + P₂.length + 1 + Pp.length = y + P.length by
                omega]
              exact hc
            have ihp := readSeq_of_chkI p h' hne hB₃' hPp hc'
            obtain ⟨F₁, rfl⟩ : ∃ F₁, F = F₁ + 2 := ⟨F - 2, by omega⟩
            have hi' := readInstr_ifElse hbtB (by simpa using hthn' F₁ (by omega))
              (by simpa using hels' F₁ (by omega))
            have := readSeq_step (readByte_at hB.get) (by decide) hi' (ihp (F₁ + 1) (by omega))
            simpa using this
          · cases h
        · cases h
      · cases h
    · cases h

/-! ## Code entries -/

/-- The locals group reader of `readCode`. -/
def groupR : DecodeM (Nat × Silmaril.Wasm.ValType) := do
  let n ← readU 32
  let t ← readValType
  pure (n, t)

theorem frame_groupR : Frame groupR := by unfold groupR; frame_tac

theorem readLocalsGroup_eq : Silmaril.Wasm.Component.Chunked.readLocalsGroup =
    (fun p => List.replicate p.1 p.2) <$> groupR := by
  funext c
  show _ = StateT.map _ _ c
  simp only [StateT.map, Silmaril.Wasm.Component.Chunked.readLocalsGroup, groupR, bind_apply]
  show _ = Except.bind _ _
  rcases h₁ : readU 32 c with e | ⟨n, c₁⟩
  · rfl
  · dsimp only
    rcases h₂ : readValType c₁ with e | ⟨t, c₂⟩ <;> rfl

theorem readVec_go_map {α β : Type} (g : DecodeM α) (h : α → β) : ∀ (n : Nat) (c : Cursor)
    {ys : List β} {c' : Cursor}, readVec.go (h <$> g) n c = .ok (ys, c') →
    ∃ xs, readVec.go g n c = .ok (xs, c') ∧ ys = xs.map h
  | 0, c, ys, c', hy => by
    simp only [readVec.go, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨[], rfl, rfl⟩
  | n + 1, c, ys, c', hy => by
    rw [readVec_go_succ] at hy
    obtain ⟨y, c₁, h₁, hy⟩ := ok_bind hy
    obtain ⟨ys', c₂, h₂, hy⟩ := ok_bind hy
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    have h₁' : (g >>= fun a => pure (h a)) c = .ok (y, c₁) := by
      rw [← h₁]; show _ = StateT.map _ _ _; simp only [StateT.map, bind_apply]
      show _ = Except.bind _ _
      cases g c <;> rfl
    obtain ⟨x, c₀, hx, hx'⟩ := ok_bind h₁'
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    obtain ⟨xs, hxs, rfl⟩ := readVec_go_map g h n c₀ h₂
    exact ⟨x :: xs, by rw [readVec_go_succ, bind_ok hx, bind_ok hxs]; rfl, rfl⟩

theorem readVec_map {α β : Type} (g : DecodeM α) (h : α → β) {c : Cursor} {ys : List β}
    {c' : Cursor} (hy : readVec (h <$> g) c = .ok (ys, c')) :
    ∃ xs, readVec g c = .ok (xs, c') ∧ ys = xs.map h := by
  unfold readVec at hy ⊢
  obtain ⟨n, c₁, h₁, hy⟩ := ok_bind hy
  obtain ⟨xs, hxs, rfl⟩ := readVec_go_map g h n c₁ hy
  exact ⟨xs, by rw [bind_ok h₁]; exact hxs, rfl⟩

theorem foldl_add_fst (xs : List (Nat × Silmaril.Wasm.ValType)) (a : Nat) :
    xs.foldl (fun s p => s + p.1) a = a + (xs.map fun p => List.replicate p.1 p.2).flatten.length := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.flatten_cons,
      List.length_append, List.length_replicate]; omega

open Silmaril.Wasm.Component.Chunked (CPlan chkCode chkCodes) in
theorem readCode_of_chkCode {B r : List UInt8} {y : Nat} {p : CPlan}
    {code : List Silmaril.Wasm.ValType × Silmaril.Wasm.Expr} {rest : List UInt8}
    (h : chkCode p r = some (code, rest)) (hB : At B y r) (hloc : code.1.length ≤ maxLocals) :
    ∃ P, r = P ++ rest ∧ readCode ⟨arr B, y⟩ = .ok (code, ⟨arr B, y + P.length⟩) := by
  unfold chkCode at h
  split at h
  · rename_i len hlen
    dsimp only at h
    split at h
    · rename_i hcl
      split at h
      · rename_i lss is hlss hbody
        split at h
        · cases h
          set c := (r.drop p.kSize).take len with hc
          set s := (r.take p.kSize).length with hs
          have hr : r = r.take p.kSize ++ c ++ (r.drop p.kSize).drop len := by
            rw [hc, List.append_assoc, List.take_append_drop, List.take_append_drop]
          refine ⟨r.take p.kSize ++ c, hr, ?_⟩
          have hB' := hB; rw [hr] at hB'
          have hBs : At B y (r.take p.kSize) := hB'.left.left
          have hBc : At B (y + s) c := hB'.left.right
          have hc' : c = c.take p.kLocals ++ c.drop p.kLocals := (List.take_append_drop _ _).symm
          have hBl : At B (y + s) (c.take p.kLocals) := by rw [hc'] at hBc; exact hBc.left
          set kl := (c.take p.kLocals).length with hkl
          have hBb : At B (y + s + kl) (c.drop p.kLocals) := by rw [hc'] at hBc; exact hBc.right
          obtain ⟨Pi, hPi⟩ := chkI_prefix hbody
          have hBe : At B (y + s + kl + Pi.length) [0x0B] := by rw [hPi] at hBb; exact hBb.right
          have hBend := hBc.2
          have hclen : c.length = kl + Pi.length + 1 := by
            rw [hc']; simp only [List.length_append, ← hkl, hPi, List.length_cons, List.length_nil]
            omega
          -- the reads
          have h₁ : readU 32 ⟨arr B, y⟩ = .ok (len, ⟨arr B, y + s⟩) :=
            run_of_runAll (frame_readU 32) hlen hBs
          have hgr : ∃ groups, runAll (readVec groupR) (c.take p.kLocals) = some groups ∧
              lss = groups.map fun q => List.replicate q.1 q.2 := by
            unfold runAll at hlss ⊢
            rw [readLocalsGroup_eq] at hlss
            split at hlss
            · rename_i x c₁ hrun
              obtain ⟨groups, hg, rfl⟩ := readVec_map _ _ hrun
              refine ⟨groups, ?_, ?_⟩
              · simp only [StateT.run] at hg ⊢
                rw [hg]; split at hlss
                · rename_i hpos; simp only [hpos, ↓reduceIte]
                · cases hlss
              · split at hlss
                · cases hlss; rfl
                · cases hlss
            · cases hlss
          obtain ⟨groups, hgroups, rfl⟩ := hgr
          have h₂ := run_of_runAll (frame_readVec frame_groupR) hgroups hBl
          have hseq := readSeq_of_chkI p.body hbody (by simp) hBb hPi (readSeq_end hBe (by decide))
          have h₃ : readExpr ⟨arr B, y + s + kl⟩ = .ok (is, ⟨arr B, y + s + kl + Pi.length + 1⟩) := by
            unfold readExpr
            rw [bind_ok (remaining_apply _)]
            simp only [arr_size]
            rw [bind_ok (by simpa using hseq _ (by omega))]
            rfl
          unfold readCode
          rw [bind_ok h₁, bind_ok (remaining_apply _)]
          simp only [arr_size, show len ≤ B.length - (y + s) by omega, ↓reduceIte]
          have h₂' : readVec (do let n ← readU 32; let t ← readValType; pure (n, t))
              ⟨arr B, y + s⟩ = .ok (groups, ⟨arr B, y + s + kl⟩) := h₂
          rw [bind_ok h₂']
          have htot : List.foldl (fun s p => s + p.1) 0 groups ≤ maxLocals := by
            rw [foldl_add_fst]; simpa using hloc
          simp only [htot, ↓reduceIte]
          rw [bind_ok h₃, bind_ok (remaining_apply _)]
          clear_value s kl c
          have hfit : y + s + (kl + Pi.length + 1) ≤ B.length := hclen ▸ hBend
          have hlen' : len = kl + Pi.length + 1 := hcl ▸ hclen
          have hdiff : B.length - (y + s) - (B.length - (y + s + kl + Pi.length + 1)) = len := by
            rw [hlen']; omega
          simp only [arr_size, hdiff, beq_self_eq_true, ↓reduceIte, List.flatMap_def]
          have hpos : y + s + kl + Pi.length + 1 = y + (List.take p.kSize r ++ c).length := by
            rw [List.length_append, ← hs, hclen]; omega
          rw [hpos]
          rfl
        · cases h
      · cases h
    · cases h
  · cases h

end Silmaril.Wasm.Component.ChunkedDecode

end
