module

public import Silmaril.Wasm.Binary.Core.Decode

/-!
# Frame lemmas for silmaril's core decoder (raw proofs)

`Frame p`: what the reader `p` does on an input, it does inside any larger input. Proved for every
reader of `Silmaril.Wasm.Binary.Core.Decode` that `decode?` uses, with `Eats` (fails at the end of
the input), the fuel monotonicity of `readSeq`/`readInstr` (`Le`), `FrameP` for the two readers
that compare positions (`readCode`, `readCustom`), and `Mono` (positions only move forward).
Header: `Silmaril.Wasm.Component.ChunkedDecode.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ChunkedDecode

open Silmaril.Wasm.Binary.Core.Decode

/-- `C` is the cursor `c` inside a larger input: the input of `C` is that of `c` with `pre`
before and `post` after it, and `C` points at the same byte. -/
def Inside (pre post : List UInt8) (c C : Cursor) : Prop :=
  C.bytes.data.toList = pre ++ c.bytes.data.toList ++ post ∧ C.pos = pre.length + c.pos ∧
    c.pos ≤ c.bytes.size

/-- **Frame property** of a reader: what it does on an input, it does inside any larger input
(same value, same bytes consumed). -/
@[irreducible] def Frame {α : Type} (p : DecodeM α) : Prop :=
  ∀ ⦃pre post : List UInt8⦄ ⦃c C : Cursor⦄ ⦃x : α⦄ ⦃c' : Cursor⦄,
    Inside pre post c C → p c = .ok (x, c') →
    c'.bytes = c.bytes ∧ ∃ C', p C = .ok (x, C') ∧ Inside pre post c' C'

/-- A reader that fails at the end of its input. -/
@[irreducible] def Eats {α : Type} (p : DecodeM α) : Prop :=
  ∀ c : Cursor, c.bytes.size ≤ c.pos → ∃ e, p c = .error e

theorem bind_apply {α β : Type} (p : DecodeM α) (f : α → DecodeM β) (c : Cursor) :
    (p >>= f) c = match p c with
      | .ok (a, c') => f a c'
      | .error e => .error e := by
  show (StateT.bind p f) c = _
  simp only [StateT.bind]
  show (Except.bind (p c) _) = _
  cases p c <;> rfl

theorem frame_pure {α : Type} (a : α) : Frame (pure a : DecodeM α) := by
  (try unfold Frame at *)
  intro pre post c C x c' hI h
  simp only [pure, StateT.pure, Except.pure] at h
  cases h
  exact ⟨rfl, C, rfl, hI⟩

theorem frame_bind {α β : Type} {p : DecodeM α} {f : α → DecodeM β} (hp : Frame p)
    (hf : ∀ a, Frame (f a)) : Frame (p >>= f) := by
  (try unfold Frame at *)
  intro pre post c C x c' hI h
  rw [bind_apply] at h
  rcases hpc : p c with e | ⟨a, c₁⟩
  · rw [hpc] at h; cases h
  · rw [hpc] at h
    obtain ⟨hb₁, C₁, hC₁, hI₁⟩ := hp hI hpc
    obtain ⟨hb₂, C₂, hC₂, hI₂⟩ := hf a hI₁ h
    refine ⟨hb₂.trans hb₁, C₂, ?_, hI₂⟩
    rw [bind_apply, hC₁]
    exact hC₂

theorem eats_bind {α β : Type} {p : DecodeM α} {f : α → DecodeM β} (hp : Eats p) :
    Eats (p >>= f) := by
  (try unfold Eats at *)
  intro c hc
  obtain ⟨e, he⟩ := hp c hc
  exact ⟨e, by rw [bind_apply, he]⟩

theorem frame_throw {α : Type} (e : String) : Frame (throw e : DecodeM α) := by
  (try unfold Frame at *)
  intro pre post c C x c' _ h
  cases h

theorem frame_decodeError {α : Type} (m : String) : Frame (decodeError m : DecodeM α) := by
  (try unfold Frame at *)
  intro pre post c C x c' _ h
  simp only [decodeError, bind_apply] at h
  cases h

theorem eats_decodeError {α : Type} (m : String) : Eats (decodeError m : DecodeM α) := by
  (try unfold Eats at *)
  intro c _
  exact ⟨_, by simp only [decodeError, bind_apply]; rfl⟩

/-! ## Bytes inside a larger input -/

theorem bsize (b : ByteArray) : b.size = b.data.toList.length := rfl

theorem bget (b : ByteArray) (i : Nat) (h : i < b.size) :
    b[i] = b.data.toList[i]'(by rw [← bsize]; exact h) := rfl

theorem Inside.size {pre post : List UInt8} {c C : Cursor} (h : Inside pre post c C) :
    C.bytes.size = pre.length + c.bytes.size + post.length := by
  rw [bsize, bsize, h.1]
  simp only [List.length_append]

theorem Inside.get {pre post : List UInt8} {c C : Cursor} (h : Inside pre post c C)
    (hc : c.pos < c.bytes.size) (hC : C.pos < C.bytes.size) : C.bytes[C.pos] = c.bytes[c.pos] := by
  rw [bget, bget]
  have hc' : c.pos < c.bytes.data.toList.length := by rw [← bsize]; exact hc
  simp only [h.1, h.2]
  rw [List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  simp


theorem get_apply (c : Cursor) : (get : DecodeM Cursor) c = .ok (c, c) := rfl

theorem set_map_apply {α : Type} (c c₁ : Cursor) (a : α) :
    ((fun _ => a) <$> (set c₁ : DecodeM PUnit)) c = .ok (a, c₁) := rfl

theorem throw_apply {α : Type} (e : String) (c : Cursor) :
    (throw e : DecodeM α) c = .error e := rfl

theorem readByte_apply (c : Cursor) : readByte c =
    if h : c.pos < c.bytes.size then .ok (c.bytes[c.pos], { c with pos := c.pos + 1 })
    else .error s!"decoder: unexpected end of input at {c.pos}" := by
  simp only [readByte, bind_apply, get_apply]
  split <;> rfl

theorem peekByte_apply (c : Cursor) : peekByte c = .ok (c.bytes[c.pos]?, c) := rfl

theorem remaining_apply (c : Cursor) : remaining c = .ok (c.bytes.size - c.pos, c) := rfl

theorem readBytes_apply (c : Cursor) (n : Nat) : readBytes n c =
    if c.pos + n ≤ c.bytes.size then .ok (c.bytes.extract c.pos (c.pos + n), { c with pos := c.pos + n })
    else (decodeError s!"{n} bytes requested past the end" : DecodeM ByteArray) c := by
  simp only [readBytes, bind_apply, get_apply]
  split <;> rfl


theorem frame_readByte : Frame readByte := by
  (try unfold Frame at *)
  intro pre post c C x c' hI h
  rw [readByte_apply] at h
  split at h
  · rename_i hc
    cases h
    have hC : C.pos < C.bytes.size := by rw [hI.size, hI.2.1]; omega
    refine ⟨rfl, { C with pos := C.pos + 1 }, ?_, ?_⟩
    · simp only [readByte_apply, hC, ↓reduceDIte, hI.get hc hC]
    · exact ⟨hI.1, by simp only [hI.2.1]; omega, by simp only; omega⟩
  · cases h

theorem eats_readByte : Eats readByte := by
  (try unfold Eats at *)
  intro c hc
  exact ⟨_, by simp only [readByte_apply, show ¬ c.pos < c.bytes.size by omega, ↓reduceDIte]; rfl⟩

theorem frame_peek_bind {α : Type} {f : Option UInt8 → DecodeM α}
    (hs : ∀ b, Frame (f (some b))) (hn : Eats (f none)) : Frame (peekByte >>= f) := by
  (try unfold Frame at *); (try unfold Eats at *)
  intro pre post c C x c' hI h
  rw [bind_apply, peekByte_apply] at h
  by_cases hc : c.pos < c.bytes.size
  · have hC : C.pos < C.bytes.size := by rw [hI.size, hI.2.1]; omega
    rw [getElem?_pos c.bytes c.pos hc] at h
    obtain ⟨hb, C', hC', hI'⟩ := hs _ hI h
    refine ⟨hb, C', ?_, hI'⟩
    rw [bind_apply, peekByte_apply, getElem?_pos C.bytes C.pos hC, hI.get hc hC]
    exact hC'
  · rw [getElem?_neg c.bytes c.pos hc] at h
    dsimp only at h
    obtain ⟨e, he⟩ := hn c (by omega)
    rw [he] at h
    cases h

theorem eats_peek_bind {α : Type} {f : Option UInt8 → DecodeM α} (hn : Eats (f none)) :
    Eats (peekByte >>= f) := by
  (try unfold Eats at *)
  intro c hc
  obtain ⟨e, he⟩ := hn c hc
  refine ⟨e, ?_⟩
  rw [bind_apply, peekByte_apply, getElem?_neg c.bytes c.pos (by omega)]
  exact he

theorem extract_inside {pre post : List UInt8} {c C : Cursor} (hI : Inside pre post c C) (n : Nat)
    (h : c.pos + n ≤ c.bytes.size) :
    C.bytes.extract C.pos (C.pos + n) = c.bytes.extract c.pos (c.pos + n) := by
  apply ByteArray.ext
  apply Array.ext'
  simp only [ByteArray.data_extract, Array.toList_extract]
  rw [hI.1, hI.2.1]
  have hl : c.pos + n ≤ c.bytes.data.toList.length := by rw [← bsize]; exact h
  rw [List.extract_eq_take_drop, List.extract_eq_take_drop, List.append_assoc, List.drop_append,
    List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left,
    List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  congr 1
  · omega
  · congr 1; omega

theorem frame_readBytes (n : Nat) : Frame (readBytes n) := by
  (try unfold Frame at *)
  intro pre post c C x c' hI h
  rw [readBytes_apply] at h
  split at h
  · rename_i hc
    cases h
    have hC : C.pos + n ≤ C.bytes.size := by rw [hI.size, hI.2.1]; omega
    refine ⟨rfl, { C with pos := C.pos + n }, ?_, ?_⟩
    · simp only [readBytes_apply, hC, ↓reduceIte, extract_inside hI n hc]
    · exact ⟨hI.1, by simp only [hI.2.1]; omega, by simp only; omega⟩
  · exact absurd h (by simp only [decodeError, bind_apply, get_apply]; exact fun h => nomatch h)


theorem frame_map {α β : Type} {p : DecodeM α} (g : α → β) (hp : Frame p) : Frame (g <$> p) := by
  have : (g <$> p) = (p >>= fun a => pure (g a)) := by
    funext c
    show StateT.map g p c = _
    simp only [StateT.map, bind_apply]
    show Except.bind (p c) _ = _
    cases p c <;> rfl
  rw [this]
  exact frame_bind hp fun a => frame_pure _

theorem eats_map {α β : Type} {p : DecodeM α} (g : α → β) (hp : Eats p) : Eats (g <$> p) := by
  have : (g <$> p) = (p >>= fun a => pure (g a)) := by
    funext c
    show StateT.map g p c = _
    simp only [StateT.map, bind_apply]
    show Except.bind (p c) _ = _
    cases p c <;> rfl
  rw [this]
  exact eats_bind hp

/-- Leaf lemmas of `frame_tac` (extended below with `macro_rules`). -/
syntax "frame_leaf" : tactic
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readByte)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readBytes _)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_decodeError _)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_throw _)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_pure _)

/-- Leaf lemmas of `eats_tac`. -/
syntax "eats_leaf" : tactic
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readByte)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_decodeError _)

/-- Prove `Eats p` for a reader that reads a byte (or fails) first. -/
macro "eats_tac" : tactic => `(tactic| repeat ((fail_if_success done); first | dsimp only | split | with_reducible eats_leaf | with_reducible apply eats_peek_bind | with_reducible apply eats_bind | with_reducible apply eats_map _))

/-- Prove `Frame p` from the frame lemmas of the readers `p` calls. -/
macro "frame_tac" : tactic => do
  let ih := Lean.mkIdent `ih
  `(tactic| repeat ((fail_if_success done); first | dsimp only | split | with_reducible frame_leaf | exact $ih _ | exact $ih _ _ | assumption | with_reducible apply frame_peek_bind | with_reducible apply frame_bind | with_reducible apply frame_map _ | intro _ | (eats_tac; done)))

theorem frame_readU_go (shift fuel : Nat) : Frame (readU.go shift fuel) := by
  induction fuel generalizing shift with
  | zero => unfold readU.go; frame_tac
  | succ n ih => unfold readU.go; frame_tac

theorem eats_readU_go (shift fuel : Nat) : Eats (readU.go shift fuel) := by
  cases fuel with
  | zero => unfold Eats; intro c _; exact ⟨_, rfl⟩
  | succ n => unfold readU.go; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readU_go _ _)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readU_go _ _)

theorem frame_readU (N : Nat) : Frame (readU N) := by unfold readU; frame_tac
theorem eats_readU (N : Nat) : Eats (readU N) := by unfold readU; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readU _)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readU _)

theorem frame_readS_go (shift fuel : Nat) (acc : Int) : Frame (readS.go shift fuel acc) := by
  induction fuel generalizing shift acc with
  | zero => unfold readS.go; frame_tac
  | succ n ih => unfold readS.go; frame_tac

theorem eats_readS_go (shift fuel : Nat) (acc : Int) : Eats (readS.go shift fuel acc) := by
  cases fuel with
  | zero => unfold Eats; intro c _; exact ⟨_, rfl⟩
  | succ n => unfold readS.go; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readS_go _ _ _)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readS_go _ _ _)

theorem frame_readS (N : Nat) : Frame (readS N) := by unfold readS; frame_tac
theorem eats_readS (N : Nat) : Eats (readS N) := by unfold readS; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readS _)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readS _)

theorem frame_readIdx {k : Silmaril.Wasm.IndexKind} : Frame (readIdx (k := k)) := by
  unfold readIdx; frame_tac
theorem eats_readIdx {k : Silmaril.Wasm.IndexKind} : Eats (readIdx (k := k)) := by
  unfold readIdx; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readIdx)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readIdx)


theorem frame_readCount : Frame readCount := by
  unfold readCount
  with_reducible apply frame_bind (frame_readU _)
  intro n
  unfold Frame
  intro pre post c C x c' hI h
  rw [bind_apply, remaining_apply] at h
  dsimp only at h
  split at h
  · rename_i hn
    cases h
    refine ⟨rfl, C, ?_, hI⟩
    have : n ≤ C.bytes.size - C.pos := by rw [hI.size, hI.2.1]; omega
    rw [bind_apply, remaining_apply]
    dsimp only
    simp only [this, ↓reduceIte]
    rfl
  · simp only [decodeError, bind_apply, get_apply] at h
    cases h

theorem eats_readCount : Eats readCount := by unfold readCount; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readCount)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readCount)

theorem frame_readVec_go {α : Type} {f : DecodeM α} (hf : Frame f) (n : Nat) :
    Frame (readVec.go f n) := by
  induction n with
  | zero => unfold readVec.go; frame_tac
  | succ n ih => unfold readVec.go; frame_tac

theorem frame_readVec {α : Type} {f : DecodeM α} (hf : Frame f) : Frame (readVec f) := by
  unfold readVec; frame_tac; exact frame_readVec_go hf _

theorem eats_readVec {α : Type} (f : DecodeM α) : Eats (readVec f) := by
  unfold readVec; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| apply frame_readVec)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readVec _)

theorem frame_readName : Frame readName := by unfold readName; frame_tac
theorem eats_readName : Eats readName := by unfold readName; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readName)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readName)

theorem frame_absHeapType : Frame readRefType.absHeapType := by
  unfold readRefType.absHeapType; frame_tac
theorem eats_absHeapType : Eats readRefType.absHeapType := by
  unfold readRefType.absHeapType; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_absHeapType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_absHeapType)

theorem eats_heapType : Eats readRefType.heapType := by
  unfold readRefType.heapType; eats_tac
theorem frame_heapType : Frame readRefType.heapType := by
  unfold readRefType.heapType; frame_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_heapType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_heapType)

theorem eats_readRefType : Eats readRefType := by unfold readRefType; eats_tac
theorem frame_readRefType : Frame readRefType := by unfold readRefType; frame_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readRefType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readRefType)

theorem eats_readValType : Eats readValType := by unfold readValType; eats_tac
theorem frame_readValType : Frame readValType := by unfold readValType; frame_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readValType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readValType)

theorem eats_readBlockType : Eats readBlockType := by unfold readBlockType; eats_tac
theorem frame_readBlockType : Frame readBlockType := by unfold readBlockType; frame_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readBlockType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readBlockType)

theorem frame_readBound (N : Nat) : Frame (readLimits.readBound N) := by
  unfold readLimits.readBound; frame_tac
theorem eats_readBound (N : Nat) : Eats (readLimits.readBound N) := by
  unfold readLimits.readBound; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readBound _)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readBound _)

theorem frame_readLimits : Frame readLimits := by unfold readLimits; frame_tac
theorem eats_readLimits : Eats readLimits := by unfold readLimits; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readLimits)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readLimits)

theorem frame_readTableType : Frame readTableType := by unfold readTableType; frame_tac
theorem eats_readTableType : Eats readTableType := by unfold readTableType; eats_tac
theorem frame_readMemType : Frame readMemType := by unfold readMemType; frame_tac
theorem eats_readMemType : Eats readMemType := by unfold readMemType; eats_tac
theorem frame_readMemArg : Frame readMemArg := by unfold readMemArg; frame_tac
theorem eats_readMemArg : Eats readMemArg := by unfold readMemArg; eats_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readTableType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readTableType)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readMemType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readMemType)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readMemArg)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readMemArg)

theorem frame_readOpOnly (op : Nat) : Frame (readOpOnly op) := by unfold readOpOnly; frame_tac
theorem frame_readVecInstr : Frame readVecInstr := by unfold readVecInstr; frame_tac
theorem frame_readCastOp : Frame readCastOp := by unfold readCastOp; frame_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readOpOnly _)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readVecInstr)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readCastOp)

theorem frame_readGCInstr : Frame readGCInstr := by unfold readGCInstr; frame_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readGCInstr)

theorem frame_readPlain (op : Nat) : Frame (readPlain op) := by unfold readPlain; frame_tac
theorem frame_readCatch : Frame readCatch := by unfold readCatch; frame_tac

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readPlain _)
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readCatch)

/-! ## Instructions: frame, and monotonicity in the fuel -/

theorem frame_readInstr_readSeq (n : Nat) :
    (∀ op, Frame (readInstr n op)) ∧ Frame (readSeq n) := by
  induction n with
  | zero =>
    refine ⟨fun op => ?_, ?_⟩
    · unfold readInstr; frame_tac
    · unfold readSeq; frame_tac
  | succ n ih =>
    obtain ⟨ih, ih₂⟩ := ih
    refine ⟨fun op => ?_, ?_⟩
    · unfold readInstr; frame_tac
    · unfold readSeq; frame_tac

/-- Success of `p` implies the same success of `q`. -/
@[irreducible] def Le {α : Type} (p q : DecodeM α) : Prop :=
  ∀ c r, p c = .ok r → q c = .ok r

theorem le_refl {α : Type} (p : DecodeM α) : Le p p := by unfold Le; exact fun _ _ h => h

theorem le_bind {α β : Type} {p q : DecodeM α} {f g : α → DecodeM β} (hp : Le p q)
    (hf : ∀ a, Le (f a) (g a)) : Le (p >>= f) (q >>= g) := by
  unfold Le at *
  intro c r h
  rw [bind_apply] at h ⊢
  rcases hpc : p c with e | ⟨a, c₁⟩
  · rw [hpc] at h; cases h
  · rw [hpc] at h
    rw [hp c _ hpc]
    exact hf a c₁ r h

theorem readSeq_mono : ∀ n m, n ≤ m →
    (∀ op, Le (readInstr n op) (readInstr m op)) ∧ Le (readSeq n) (readSeq m) := by
  intro n
  induction n with
  | zero =>
    intro m _
    unfold Le
    refine ⟨fun op c r h => ?_, fun c r h => ?_⟩
    · simp only [readInstr, decodeError, bind_apply, get_apply] at h; cases h
    · simp only [readSeq, decodeError, bind_apply, get_apply] at h; cases h
  | succ n ih =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨ih₁, ih₂⟩ := ih m (by omega)
    refine ⟨fun op => ?_, ?_⟩
    · unfold readInstr
      split <;> (repeat (first | exact le_refl _ | exact ih₂ | apply le_bind | intro _ | split))
    · unfold readSeq
      repeat (first | exact le_refl _ | exact ih₂ | exact ih₁ _ | apply le_bind | intro _ | split)

theorem frame_readExpr : Frame readExpr := by
  unfold Frame
  intro pre post c C x c' hI h
  unfold readExpr at h ⊢
  rw [bind_apply, remaining_apply] at h ⊢
  dsimp only at h ⊢
  rw [bind_apply] at h ⊢
  rcases hs : readSeq (c.bytes.size - c.pos + 1) c with e | ⟨⟨is, t⟩, c₁⟩
  · rw [hs] at h; cases h
  · rw [hs] at h
    have hle : c.bytes.size - c.pos + 1 ≤ C.bytes.size - C.pos + 1 := by
      rw [hI.size, hI.2.1]; omega
    have hs' := (readSeq_mono _ _ hle).2
    unfold Le at hs'
    have hs' := hs' c _ hs
    have hF := (frame_readInstr_readSeq (C.bytes.size - C.pos + 1)).2
    unfold Frame at hF
    obtain ⟨hb, C₁, hC₁, hI₁⟩ := hF hI hs'
    rw [hC₁]
    dsimp only at h ⊢
    split at h
    · cases h
      refine ⟨hb, C₁, ?_, hI₁⟩
      simp only [*, ↓reduceIte]; rfl
    · simp only [decodeError, bind_apply, get_apply] at h; cases h

theorem eats_readExpr : Eats readExpr := by
  unfold Eats
  intro c hc
  unfold readExpr
  rw [bind_apply, remaining_apply]
  dsimp only
  rw [bind_apply]
  have := eats_readByte
  unfold Eats at this
  obtain ⟨e, he⟩ := this c hc
  refine ⟨e, ?_⟩
  simp only [show c.bytes.size - c.pos = 0 by omega, readSeq, bind_apply, he]

macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readExpr)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readExpr)

/-! ## Types, imports, globals, exports, tables, tags -/

theorem eats_readStorageType : Eats readStorageType := by unfold readStorageType; eats_tac
theorem frame_readStorageType : Frame readStorageType := by unfold readStorageType; frame_tac
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readStorageType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readStorageType)

theorem eats_readFieldType : Eats readFieldType := by unfold readFieldType; eats_tac
theorem frame_readFieldType : Frame readFieldType := by unfold readFieldType; frame_tac
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readFieldType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readFieldType)

theorem eats_readCompType : Eats readCompType := by unfold readCompType; eats_tac
theorem frame_readCompType : Frame readCompType := by unfold readCompType; frame_tac
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readCompType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readCompType)

theorem eats_readSubType : Eats readSubType := by unfold readSubType; eats_tac
theorem frame_readSubType : Frame readSubType := by unfold readSubType; frame_tac
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readSubType)
macro_rules | `(tactic| eats_leaf) => `(tactic| exact eats_readSubType)

theorem frame_readRecType : Frame readRecType := by unfold readRecType; frame_tac
theorem frame_readTable : Frame readTable := by unfold readTable; frame_tac
theorem frame_readTag : Frame readTag := by unfold readTag; frame_tac
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readTag)
theorem frame_readImport : Frame readImport := by unfold readImport; frame_tac
theorem frame_readGlobal : Frame readGlobal := by unfold readGlobal; frame_tac
theorem frame_readExport : Frame readExport := by unfold readExport; frame_tac
theorem frame_readByteVec : Frame readData.readByteVec := by unfold readData.readByteVec; frame_tac
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_readByteVec)
theorem frame_readData : Frame readData := by unfold readData; frame_tac
theorem frame_funcInits : Frame readElem.funcInits := by unfold readElem.funcInits; frame_tac
macro_rules | `(tactic| frame_leaf) => `(tactic| exact frame_funcInits)
theorem frame_readElem : Frame readElem := by unfold readElem; frame_tac

/-! ## Readers that compare positions: code entries and custom sections -/

theorem ok_bind {α β : Type} {p : DecodeM α} {f : α → DecodeM β} {c : Cursor} {r : β × Cursor}
    (h : (p >>= f) c = .ok r) : ∃ a c₁, p c = .ok (a, c₁) ∧ f a c₁ = .ok r := by
  rw [bind_apply] at h
  rcases hp : p c with e | ⟨a, c₁⟩
  · rw [hp] at h; cases h
  · rw [hp] at h; exact ⟨a, c₁, rfl, h⟩

theorem bind_ok {α β : Type} {p : DecodeM α} {f : α → DecodeM β} {c c₁ : Cursor} {a : α}
    (h : p c = .ok (a, c₁)) : (p >>= f) c = f a c₁ := by
  rw [bind_apply, h]

theorem Frame.run {α : Type} {p : DecodeM α} (hp : Frame p) {pre post : List UInt8}
    {c C c' : Cursor} {x : α} (hI : Inside pre post c C) (h : p c = .ok (x, c')) :
    c'.bytes = c.bytes ∧ ∃ C', p C = .ok (x, C') ∧ Inside pre post c' C' := by
  unfold Frame at hp
  exact hp hI h

theorem Inside.remaining {pre post : List UInt8} {c C : Cursor} (hI : Inside pre post c C) :
    C.bytes.size - C.pos = c.bytes.size - c.pos + post.length := by
  have := hI.2.2
  rw [hI.size, hI.2.1]; omega

theorem error_ne_ok {α : Type} {e : String} {r : α × Cursor} :
    (Except.error e : Except String (α × Cursor)) ≠ .ok r := fun h => nomatch h

theorem decodeError_ne_ok {α : Type} (m : String) (c : Cursor) (r : α × Cursor) :
    (decodeError m : DecodeM α) c ≠ .ok r := by
  simp only [decodeError, bind_apply, get_apply]; exact fun h => nomatch h

/-- The frame property between two readers, for a fixed suffix `post`. -/
@[irreducible] def FrameP {α : Type} (post : List UInt8) (p q : DecodeM α) : Prop :=
  ∀ ⦃pre : List UInt8⦄ ⦃c C : Cursor⦄ ⦃x : α⦄ ⦃c' : Cursor⦄,
    Inside pre post c C → p c = .ok (x, c') →
    c'.bytes = c.bytes ∧ ∃ C', q C = .ok (x, C') ∧ Inside pre post c' C'

theorem frameP_of_frame {α : Type} {p : DecodeM α} (hp : Frame p) (post : List UInt8) :
    FrameP post p p := by
  unfold FrameP; unfold Frame at hp
  exact fun _ _ _ _ _ hI h => hp hI h

theorem frame_of_frameP {α : Type} {p : DecodeM α} (hp : ∀ post, FrameP post p p) : Frame p := by
  unfold Frame
  intro pre post c C x c' hI h
  have := hp post
  unfold FrameP at this
  exact this hI h

theorem frameP_bind {α β : Type} {post : List UInt8} {p q : DecodeM α} {f g : α → DecodeM β}
    (hp : FrameP post p q) (hf : ∀ a, FrameP post (f a) (g a)) :
    FrameP post (p >>= f) (q >>= g) := by
  unfold FrameP at *
  intro pre c C x c' hI h
  obtain ⟨a, c₁, h₁, h⟩ := ok_bind h
  obtain ⟨hb₁, C₁, hC₁, hI₁⟩ := hp hI h₁
  obtain ⟨hb₂, C₂, hC₂, hI₂⟩ := hf a hI₁ h
  exact ⟨hb₂.trans hb₁, C₂, by rw [bind_ok hC₁]; exact hC₂, hI₂⟩

theorem frameP_remaining {α : Type} {post : List UInt8} {f g : Nat → DecodeM α}
    (hf : ∀ r, FrameP post (f r) (g (r + post.length))) :
    FrameP post (remaining >>= f) (remaining >>= g) := by
  unfold FrameP at *
  intro pre c C x c' hI h
  rw [bind_ok (remaining_apply c)] at h
  rw [bind_ok (remaining_apply C), hI.remaining]
  exact hf _ hI h

theorem frameP_pure {α : Type} {post : List UInt8} (a : α) :
    FrameP post (pure a : DecodeM α) (pure a) :=
  frameP_of_frame (frame_pure a) post

/-- A reader that always fails. -/
def Fails {α : Type} (p : DecodeM α) : Prop := ∀ c r, p c ≠ .ok r

theorem fails_decodeError_bind {α β : Type} (m : String) (f : α → DecodeM β) :
    Fails (decodeError m >>= f) := by
  intro c r h
  obtain ⟨a, c₁, h₁, _⟩ := ok_bind h
  exact decodeError_ne_ok m c _ h₁

theorem frameP_ite {α : Type} {post : List UInt8} {P Q : Prop} [Decidable P] [Decidable Q]
    {a a' b b' : DecodeM α} (hPQ : P → Q) (ha : FrameP post a a') (hb : Fails b) :
    FrameP post (if P then a else b) (if Q then a' else b') := by
  unfold FrameP at *
  intro pre c C x c' hI h
  by_cases hP : P
  · simp only [hP, hPQ hP, ↓reduceIte] at h ⊢
    exact ha hI h
  · simp only [hP, ↓reduceIte] at h
    exact absurd h (hb c _)

theorem frame_readCode : Frame readCode := by
  have hg : Frame (do let n ← readU 32; let t ← readValType; pure (n, t) :
      DecodeM (Nat × Silmaril.Wasm.ValType)) := by frame_tac
  refine frame_of_frameP fun post => ?_
  unfold readCode
  refine frameP_bind (frameP_of_frame (frame_readU 32) post) fun size => ?_
  refine frameP_remaining fun r₀ => ?_
  refine frameP_ite (fun h => by omega) ?_ (fails_decodeError_bind _ _)
  refine frameP_bind (frameP_of_frame (frame_readVec hg) post) fun groups => ?_
  refine frameP_ite id ?_ (fails_decodeError_bind _ _)
  refine frameP_bind (frameP_of_frame frame_readExpr post) fun body => ?_
  refine frameP_remaining fun r₁ => ?_
  rw [Nat.add_sub_add_right]
  exact frameP_ite id (frameP_pure _) (fails_decodeError_bind _ _)

theorem frame_readCustom (size : Nat) : Frame (readCustom size) := by
  refine frame_of_frameP fun post => ?_
  unfold readCustom
  refine frameP_remaining fun before => ?_
  refine frameP_bind (frameP_of_frame frame_readName post) fun _ => ?_
  refine frameP_remaining fun after => ?_
  rw [Nat.add_sub_add_right]
  refine frameP_ite id ?_ (fails_decodeError_bind _ _)
  refine frameP_bind (frameP_of_frame (frame_readBytes _) post) fun _ => frameP_pure _

/-! ## Positions only move forward -/

/-- A reader that never moves the cursor back. -/
@[irreducible] def Mono {α : Type} (p : DecodeM α) : Prop :=
  ∀ c x c', p c = .ok (x, c') → c.pos ≤ c'.pos

theorem mono_bind {α β : Type} {p : DecodeM α} {f : α → DecodeM β} (hp : Mono p)
    (hf : ∀ a, Mono (f a)) : Mono (p >>= f) := by
  unfold Mono at *
  intro c x c' h
  obtain ⟨a, c₁, h₁, h₂⟩ := ok_bind h
  exact (hp _ _ _ h₁).trans (hf a _ _ _ h₂)

theorem mono_pure {α : Type} (a : α) : Mono (pure a : DecodeM α) := by
  unfold Mono; intro c x c' h; cases h; exact Nat.le_refl _

theorem mono_map {α β : Type} {p : DecodeM α} (g : α → β) (hp : Mono p) : Mono (g <$> p) := by
  have : (g <$> p) = (p >>= fun a => pure (g a)) := by
    funext c
    show StateT.map g p c = _
    simp only [StateT.map, bind_apply]
    show Except.bind (p c) _ = _
    cases p c <;> rfl
  rw [this]
  exact mono_bind hp fun a => mono_pure _

theorem mono_readByte : Mono readByte := by
  unfold Mono; intro c x c' h
  rw [readByte_apply] at h
  split at h
  · cases h; exact Nat.le_succ _
  · cases h

theorem mono_readBytes (n : Nat) : Mono (readBytes n) := by
  unfold Mono; intro c x c' h
  rw [readBytes_apply] at h
  split at h
  · cases h; exact Nat.le_add_right _ _
  · exact absurd h (decodeError_ne_ok _ _ _)

theorem mono_peekByte : Mono peekByte := by
  unfold Mono; intro c x c' h; rw [peekByte_apply] at h; cases h; exact Nat.le_refl _

theorem mono_remaining : Mono remaining := by
  unfold Mono; intro c x c' h; rw [remaining_apply] at h; cases h; exact Nat.le_refl _

theorem mono_decodeError {α : Type} (m : String) : Mono (decodeError m : DecodeM α) := by
  unfold Mono; intro c x c' h; exact absurd h (decodeError_ne_ok _ _ _)

theorem mono_throw {α : Type} (e : String) : Mono (throw e : DecodeM α) := by
  unfold Mono; intro c x c' h; cases h

syntax "mono_leaf" : tactic
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readByte)
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readBytes _)
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_peekByte)
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_remaining)
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_decodeError _)
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_throw _)
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_pure _)

/-- Prove `Mono p` from the lemmas of the readers `p` calls. -/
macro "mono_tac" : tactic => do
  let ih := Lean.mkIdent `ih
  `(tactic| repeat ((fail_if_success done); first | dsimp only | split | with_reducible mono_leaf | exact $ih _ | exact $ih _ _ | assumption | with_reducible apply mono_bind | with_reducible apply mono_map _ | intro _))

theorem mono_readU_go (shift fuel : Nat) : Mono (readU.go shift fuel) := by
  induction fuel generalizing shift with
  | zero => unfold readU.go; mono_tac
  | succ n ih => unfold readU.go; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readU_go _ _)
theorem mono_readU (N : Nat) : Mono (readU N) := by unfold readU; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readU _)
theorem mono_readS_go (shift fuel : Nat) (acc : Int) : Mono (readS.go shift fuel acc) := by
  induction fuel generalizing shift acc with
  | zero => unfold readS.go; mono_tac
  | succ n ih => unfold readS.go; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readS_go _ _ _)
theorem mono_readS (N : Nat) : Mono (readS N) := by unfold readS; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readS _)
theorem mono_readIdx {k : Silmaril.Wasm.IndexKind} : Mono (readIdx (k := k)) := by
  unfold readIdx; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readIdx)
theorem mono_readCount : Mono readCount := by unfold readCount; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readCount)
theorem mono_readVec_go {α : Type} {f : DecodeM α} (hf : Mono f) (n : Nat) :
    Mono (readVec.go f n) := by
  induction n with
  | zero => unfold readVec.go; mono_tac
  | succ n ih => unfold readVec.go; mono_tac
theorem mono_readVec {α : Type} {f : DecodeM α} (hf : Mono f) : Mono (readVec f) := by
  unfold readVec; mono_tac; exact mono_readVec_go hf _
macro_rules | `(tactic| mono_leaf) => `(tactic| apply mono_readVec)
theorem mono_absHeapType : Mono readRefType.absHeapType := by
  unfold readRefType.absHeapType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_absHeapType)
theorem mono_heapType : Mono readRefType.heapType := by unfold readRefType.heapType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_heapType)
theorem mono_readRefType : Mono readRefType := by unfold readRefType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readRefType)
theorem mono_readValType : Mono readValType := by unfold readValType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readValType)
theorem mono_readBlockType : Mono readBlockType := by unfold readBlockType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readBlockType)
theorem mono_readMemArg : Mono readMemArg := by unfold readMemArg; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readMemArg)
theorem mono_readOpOnly (op : Nat) : Mono (readOpOnly op) := by unfold readOpOnly; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readOpOnly _)
theorem mono_readVecInstr : Mono readVecInstr := by unfold readVecInstr; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readVecInstr)
theorem mono_readCastOp : Mono readCastOp := by unfold readCastOp; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readCastOp)
theorem mono_readGCInstr : Mono readGCInstr := by unfold readGCInstr; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readGCInstr)
theorem mono_readPlain (op : Nat) : Mono (readPlain op) := by unfold readPlain; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readPlain _)
theorem mono_readCatch : Mono readCatch := by unfold readCatch; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readCatch)

theorem mono_readInstr_readSeq (n : Nat) : (∀ op, Mono (readInstr n op)) ∧ Mono (readSeq n) := by
  induction n with
  | zero =>
    refine ⟨fun op => ?_, ?_⟩
    · unfold readInstr; mono_tac
    · unfold readSeq; mono_tac
  | succ n ih =>
    obtain ⟨ih, ih₂⟩ := ih
    refine ⟨fun op => ?_, ?_⟩
    · unfold readInstr; mono_tac
    · unfold readSeq; mono_tac

end Silmaril.Wasm.Component.ChunkedDecode

end
