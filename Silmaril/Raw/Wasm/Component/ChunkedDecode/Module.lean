module

public import Silmaril.Raw.Wasm.Component.ChunkedDecode.Plans
public import Silmaril.Wasm.Component.ChunkedDecode.Defs

/-!
# Chunked checks of a whole core module give `decode?` (raw proofs)

Vectors over consecutive slices (`VecSeg`), code groups (`chkCodes` with `chkLocals`), data
segments (`chkDatas`), custom sections (`chkCustom`), sections (`chkSection`) as steps of
`readModule.go`, and the module header and final checks: `decode_of_go`. Header:
`Silmaril.Wasm.Component.ChunkedDecode.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ChunkedDecode

open Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Component.Chunked (arr runAll slice readAllOf chkSeq chkVec chkSection CPlan chkCode
  chkCodes codesOf codesOk chkData0 chkDatas chkDataVec chkCustom)

/-! ## Vectors over consecutive slices -/

/-- The elements `xs` of `f` occupy the bytes `[y, e)` of `B`, before any further elements. -/
def VecSeg {α : Type} (f : DecodeM α) (B : List UInt8) (y e : Nat) (xs : List α) : Prop :=
  ∀ (m : Nat) (ys : List α) (D : Cursor), readVec.go f m ⟨arr B, e⟩ = .ok (ys, D) →
    readVec.go f (xs.length + m) ⟨arr B, y⟩ = .ok (xs ++ ys, D)

theorem VecSeg.nil {α : Type} {f : DecodeM α} {B : List UInt8} {y : Nat} : VecSeg f B y y [] :=
  fun _ _ _ h => by simpa using h

theorem VecSeg.append {α : Type} {f : DecodeM α} {B : List UInt8} {y e e' : Nat} {xs xs' : List α}
    (h₁ : VecSeg f B y e xs) (h₂ : VecSeg f B e e' xs') : VecSeg f B y e' (xs ++ xs') := by
  intro m ys D h
  have := h₁ _ _ _ (h₂ m ys D h)
  rw [List.length_append, Nat.add_assoc, List.append_assoc]
  exact this

theorem VecSeg.cons {α : Type} {f : DecodeM α} {B : List UInt8} {y e e' : Nat} {x : α}
    {xs : List α} (h₁ : f ⟨arr B, y⟩ = .ok (x, ⟨arr B, e⟩)) (h₂ : VecSeg f B e e' xs) :
    VecSeg f B y e' (x :: xs) := by
  intro m ys D h
  have := h₂ m ys D h
  rw [List.length_cons, show xs.length + 1 + m = (xs.length + m) + 1 by omega, readVec_go_succ,
    bind_ok h₁, bind_ok this]
  rfl

theorem vecSeg_of_chkSeq {α : Type} {f : DecodeM α} (hf : Frame f) {B r : List UInt8} {y : Nat}
    {ks : List Nat} {xs : List α} (h : chkSeq f ks r = some (xs, [])) (hB : At B y r) :
    VecSeg f B y (y + r.length) xs := by
  intro m ys D hD
  exact readVec_go_of_chkSeq hf h hB (by simpa using hD)

/-- **A vector**: its count, then its elements. -/
theorem readVec_of_seg {α : Type} {f : DecodeM α} {B : List UInt8} {x k e : Nat} {xs : List α}
    (hu : readU 32 ⟨arr B, x⟩ = .ok (xs.length, ⟨arr B, x + k⟩))
    (hn : xs.length ≤ B.length - (x + k)) (hs : VecSeg f B (x + k) e xs) :
    readVec f ⟨arr B, x⟩ = .ok (xs, ⟨arr B, e⟩) := by
  unfold readVec
  rw [bind_ok (readCount_at hu hn)]
  have := hs 0 [] ⟨arr B, e⟩ rfl
  simpa using this

/-! ## Positions only move forward: the element readers of sections -/

theorem mono_readName : Mono readName := by unfold readName; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readName)
theorem mono_readBound (N : Nat) : Mono (readLimits.readBound N) := by
  unfold readLimits.readBound; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readBound _)
theorem mono_readLimits : Mono readLimits := by unfold readLimits; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readLimits)
theorem mono_readTableType : Mono readTableType := by unfold readTableType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readTableType)
theorem mono_readMemType : Mono readMemType := by unfold readMemType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readMemType)
theorem mono_readStorageType : Mono readStorageType := by unfold readStorageType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readStorageType)
theorem mono_readFieldType : Mono readFieldType := by unfold readFieldType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readFieldType)
theorem mono_readCompType : Mono readCompType := by unfold readCompType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readCompType)
theorem mono_readSubType : Mono readSubType := by unfold readSubType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readSubType)
theorem mono_readRecType : Mono readRecType := by unfold readRecType; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact (mono_readInstr_readSeq _).2)
theorem mono_readExpr : Mono readExpr := by unfold readExpr; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readExpr)
theorem mono_readTable : Mono readTable := by unfold readTable; mono_tac
theorem mono_readTag : Mono readTag := by unfold readTag; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_readTag)
theorem mono_readImport : Mono readImport := by unfold readImport; mono_tac
theorem mono_readGlobal : Mono readGlobal := by unfold readGlobal; mono_tac
theorem mono_readExport : Mono readExport := by unfold readExport; mono_tac
theorem mono_funcInits : Mono readElem.funcInits := by unfold readElem.funcInits; mono_tac
macro_rules | `(tactic| mono_leaf) => `(tactic| exact mono_funcInits)
theorem mono_readElem : Mono readElem := by unfold readElem; mono_tac

/-! ## Counting the elements of a piece -/

theorem inside_self {c : Cursor} (hc : c.pos ≤ c.bytes.size) : Inside [] [] c c :=
  ⟨by simp, by simp, hc⟩

theorem Frame.self {α : Type} {f : DecodeM α} (hf : Frame f) {c c' : Cursor} {x : α}
    (h : f c = .ok (x, c')) (hc : c.pos ≤ c.bytes.size) :
    c'.bytes = c.bytes ∧ c'.pos ≤ c'.bytes.size := by
  obtain ⟨hb, C', _, hI'⟩ := hf.run (inside_self hc) h
  exact ⟨hb, hI'.2.2⟩

theorem readAllOf_stuck {α : Type} {f : DecodeM α} {c : Cursor} {x : α} (hx : f c = .ok (x, c))
    (hr : c.pos < c.bytes.size) :
    ∀ fuel {xs : List α} {c' : Cursor}, readAllOf f fuel c = .ok (xs, c') → c' = c := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs c' h
    simp only [readAllOf, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | succ fuel ih =>
    intro xs c' h
    unfold readAllOf at h
    rw [bind_ok (remaining_apply _)] at h
    simp only [show ¬ c.bytes.size - c.pos = 0 by omega, ↓reduceIte] at h
    rw [bind_ok hx] at h
    obtain ⟨xs', c₁, h₁, h⟩ := ok_bind h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact ih h₁

/-- **A piece read to its end has at most one element per byte.** -/
theorem readAllOf_length {α : Type} {f : DecodeM α} (hf : Frame f) (hm : Mono f) :
    ∀ fuel {c : Cursor} {xs : List α} {c' : Cursor}, readAllOf f fuel c = .ok (xs, c') →
      c'.pos = c.bytes.size → c.pos ≤ c.bytes.size → xs.length ≤ c'.pos - c.pos := by
  intro fuel
  induction fuel with
  | zero =>
    intro c xs c' h _ _
    simp only [readAllOf, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; simp
  | succ fuel ih =>
    intro c xs c' h hend hc
    unfold readAllOf at h
    rw [bind_ok (remaining_apply _)] at h
    by_cases hz : c.bytes.size - c.pos = 0
    · simp only [hz, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; simp
    · simp only [hz, ↓reduceIte] at h
      obtain ⟨x, c₁, h₁, h⟩ := ok_bind h
      obtain ⟨xs', c₂, h₂, h⟩ := ok_bind h
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hb₁, hc₁⟩ := hf.self h₁ hc
      have hm₁ := mono_apply hm h₁
      by_cases hadv : c₁.pos = c.pos
      · have hce : c₁ = c := by cases c; cases c₁; simp only at hb₁ hadv; rw [hb₁, hadv]
        rw [hce] at h₁ h₂
        have := readAllOf_stuck h₁ (by omega) fuel h₂
        rw [this] at hend; omega
      · have := ih h₂ (by rw [hend, hb₁]) hc₁
        simp only [List.length_cons]
        omega

theorem runAll_readAllOf_length {α : Type} {f : DecodeM α} (hf : Frame f) (hm : Mono f)
    {fuel : Nat} {l : List UInt8} {xs : List α} (h : runAll (readAllOf f fuel) l = some xs) :
    xs.length ≤ l.length := by
  unfold runAll at h
  split at h
  · rename_i x c hrun
    split at h
    · rename_i hpos
      cases h
      have := readAllOf_length hf hm fuel hrun (by rw [hpos]; rfl) (Nat.zero_le _)
      simpa [hpos] using this
    · cases h
  · cases h

theorem chkSeq_length {α : Type} {f : DecodeM α} (hf : Frame f) (hm : Mono f) :
    ∀ {ks : List Nat} {r : List UInt8} {xs : List α} {rest : List UInt8},
      chkSeq f ks r = some (xs, rest) → xs.length + rest.length ≤ r.length
  | [], r, xs, rest, h => by
    simp only [chkSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | k :: ks, r, xs, rest, h => by
    simp only [chkSeq] at h
    split at h
    · rename_i xs₁ h₁
      obtain ⟨⟨xs₂, rest₂⟩, h₂, h₃⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at h₃
      obtain ⟨rfl, rfl⟩ := h₃
      have l₁ := runAll_readAllOf_length hf hm h₁
      have l₂ := chkSeq_length hf hm h₂
      have : (r.take k).length + (r.drop k).length = r.length := by
        rw [← List.length_append, List.take_append_drop]
      simp only [List.length_append]
      omega
    · cases h

/-- **A vector checked in pieces is a `readVec` run** (the count is at most the bytes left). -/
theorem readVec_of_chkVec' {α : Type} {f : DecodeM α} (hf : Frame f) (hm : Mono f)
    {B body : List UInt8} {x kc : Nat} {ks : List Nat} {xs : List α}
    (h : chkVec f kc ks body = some xs) (hB : At B x body) :
    readVec f ⟨arr B, x⟩ = .ok (xs, ⟨arr B, x + body.length⟩) := by
  refine readVec_of_chkVec hf h hB fun n hn => ?_
  unfold chkVec at h
  rw [hn] at h
  split at h
  · rename_i n' xs' hc hs
    split at h
    · cases h
      rename_i hlen
      have := chkSeq_length hf hm hs
      cases hc
      simp only [List.length_drop, List.length_nil] at this
      omega
    · cases h
  · cases h

/-! ## Code entries -/

theorem chkCode_locals {p : CPlan} {r : List UInt8}
    {code : List Silmaril.Wasm.ValType × Silmaril.Wasm.Expr} {rest : List UInt8}
    (h : chkCode p r = some (code, rest)) :
    ∃ len lss, runAll (readU 32) (r.take p.kSize) = some len ∧ rest = (r.drop p.kSize).drop len ∧
      runAll (readVec Silmaril.Wasm.Component.Chunked.readLocalsGroup)
        (((r.drop p.kSize).take len).take p.kLocals) = some lss ∧ code.1 = lss.flatten := by
  unfold chkCode at h
  split at h
  · rename_i len hlen
    dsimp only at h
    split at h
    · split at h
      · rename_i lss is hlss _
        split at h
        · cases h
          exact ⟨len, lss, hlen, rfl, hlss, rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Code entries checked by their plans are a vector run of `readCode`.** -/
theorem codes_seg {B : List UInt8} : ∀ {ps : List CPlan} {r : List UInt8} {y : Nat}
    {cs : List (List Silmaril.Wasm.ValType × Silmaril.Wasm.Expr)} {rest : List UInt8},
    chkCodes ps r = some (cs, rest) → chkLocals ps r = true → At B y r →
    ∃ P, r = P ++ rest ∧ VecSeg readCode B y (y + P.length) cs
  | [], r, y, cs, rest, h, _, _ => by
    simp only [chkCodes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simpa using VecSeg.nil⟩
  | p :: ps, r, y, cs, rest, h, hl, hB => by
    simp only [chkCodes] at h
    split at h
    · rename_i code r₁ hc
      obtain ⟨⟨cs', rest'⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at h''
      obtain ⟨rfl, rfl⟩ := h''
      obtain ⟨len, lss, hlen, hr₁, hlss, hcode⟩ := chkCode_locals hc
      simp only [chkLocals, hlen, hlss, Bool.and_eq_true, decide_eq_true_eq] at hl
      rw [← hr₁] at hl
      obtain ⟨P₁, hP₁, hrc⟩ := readCode_of_chkCode hc hB (by rw [hcode]; exact hl.1)
      have hB₁ : At B (y + P₁.length) r₁ := by rw [hP₁] at hB; exact hB.right
      obtain ⟨P₂, hP₂, hseg⟩ := codes_seg h' hl.2 hB₁
      refine ⟨P₁ ++ P₂, by rw [hP₁, hP₂, List.append_assoc], ?_⟩
      rw [List.length_append, ← Nat.add_assoc]
      exact VecSeg.cons hrc hseg
    · cases h

theorem codes_seg_of_ok {B : List UInt8} {ps : List CPlan} {r : List UInt8} {y : Nat}
    (h : codesOk ps r = true) (hl : chkLocals ps r = true) (hB : At B y r) :
    VecSeg readCode B y (y + r.length) (codesOf ps r) := by
  unfold codesOk at h
  unfold codesOf
  split at h
  · rename_i cs hcs
    obtain ⟨P, hP, hseg⟩ := codes_seg hcs hl hB
    simp only [List.append_nil] at hP
    rw [hP]; exact hseg
  · cases h

/-! ## Data segments -/

theorem extract_arr (B : List UInt8) (x n : Nat) :
    (arr B).extract x (x + n) = Silmaril.Wasm.Binary.Core.dataBytes ((B.drop x).take n) := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, Silmaril.Wasm.Binary.Core.dataBytes]
  apply Array.ext'
  simp only [Array.toList_extract]
  rw [List.extract_eq_take_drop]
  show List.take (x + n - x) (List.drop x B) = _
  rw [Nat.add_sub_cancel_left]

theorem readData_of_chkData0 {B r : List UInt8} {y kk ke kl : Nat} {d : Silmaril.Wasm.Data}
    {rest : List UInt8} (h : chkData0 kk ke kl r = some (d, rest)) (hB : At B y r) :
    ∃ P, r = P ++ rest ∧ readData ⟨arr B, y⟩ = .ok (d, ⟨arr B, y + P.length⟩) ∧ 1 ≤ P.length := by
  unfold chkData0 at h
  split at h
  · rename_i e n hk he hn
    dsimp only at h
    split at h
    · rename_i hbs
      cases h
      set r₁ := r.drop kk
      set r₂ := r₁.drop ke
      set r₃ := r₂.drop kl
      set bs := r₃.take n
      have hr : r = r.take kk ++ (r₁.take ke ++ (r₂.take kl ++ (bs ++ r₃.drop n))) := by
        rw [List.take_append_drop n r₃, List.take_append_drop kl r₂, List.take_append_drop ke r₁,
          List.take_append_drop kk r]
      clear_value bs r₃ r₂ r₁
      have hne : (r.take kk) ≠ [] := by
        intro h0; rw [h0] at hk; exact absurd hk (by decide)
      refine ⟨r.take kk ++ r₁.take ke ++ r₂.take kl ++ bs, by simpa only [List.append_assoc] using hr,
        ?_, by simp only [List.length_append]; have := List.length_pos_iff.2 hne; omega⟩
      have hB' := hB; rw [hr] at hB'
      have h₁ := run_of_runAll (frame_readU 32) hk hB'.left
      have hB₁ := hB'.right
      have h₂ := run_of_runAll frame_readExpr he hB₁.left
      have hB₂ := hB₁.right
      have h₃ := run_of_runAll (frame_readU 32) hn hB₂.left
      have hB₃ := hB₂.right
      have hfit := hB₃.left.2
      unfold readData
      rw [bind_ok h₁]
      simp only
      rw [bind_ok h₂]
      unfold readData.readByteVec
      rw [bind_apply, bind_ok (readCount_at h₃ (by rw [← hbs]; omega)), readBytes_apply]
      simp only [arr_size, show y + (r.take kk).length + (r₁.take ke).length + (r₂.take kl).length + n
        ≤ B.length by rw [← hbs]; omega, ↓reduceIte]
      have hx := extract_arr B (y + (r.take kk).length + (r₁.take ke).length + (r₂.take kl).length) n
      rw [hx]
      have hbsB : (B.drop (y + (r.take kk).length + (r₁.take ke).length + (r₂.take kl).length)).take n
          = bs := by
        have := hB₃.left.1; rw [hbs] at this; exact this
      rw [hbsB]
      simp only [List.length_append]
      rw [hbs, ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc]
      rfl
    · cases h
  · cases h

/-- **Data segments checked by their plans are a vector run of `readData`.** -/
theorem datas_seg {B : List UInt8} : ∀ {ps : List (Nat × Nat × Nat)} {r : List UInt8} {y : Nat}
    {ds : List Silmaril.Wasm.Data} {rest : List UInt8},
    chkDatas ps r = some (ds, rest) → At B y r →
    ∃ P, r = P ++ rest ∧ VecSeg readData B y (y + P.length) ds ∧ ds.length ≤ P.length
  | [], r, y, ds, rest, h, _ => by
    simp only [chkDatas, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simpa using VecSeg.nil, by simp⟩
  | (a, b, c) :: ps, r, y, ds, rest, h, hB => by
    simp only [chkDatas] at h
    split at h
    · rename_i d r₁ hd
      obtain ⟨⟨ds', rest'⟩, h', h''⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at h''
      obtain ⟨rfl, rfl⟩ := h''
      obtain ⟨P₁, hP₁, hrd, hP₁l⟩ := readData_of_chkData0 hd hB
      have hB₁ : At B (y + P₁.length) r₁ := by rw [hP₁] at hB; exact hB.right
      obtain ⟨P₂, hP₂, hseg, hl⟩ := datas_seg h' hB₁
      refine ⟨P₁ ++ P₂, by rw [hP₁, hP₂, List.append_assoc], ?_, ?_⟩
      · rw [List.length_append, ← Nat.add_assoc]
        exact VecSeg.cons hrd hseg
      · simp only [List.length_cons, List.length_append]; omega
    · cases h

/-! ## Sections as steps of `readModule.go` -/

theorem chkSection_parts {α : Type} {N : UInt8} {kS : Nat} {inner : List UInt8 → Option α}
    {r : List UInt8} {v : α} (h : chkSection N kS inner r = some v) :
    ∃ r₁ len, r = N :: r₁ ∧ runAll (readU 32) (r₁.take kS) = some len ∧
      (r₁.drop kS).length = len ∧ inner (r₁.drop kS) = some v := by
  unfold chkSection at h
  split at h
  · rename_i id r₁
    split at h
    · rename_i hid
      split at h
      · rename_i len hlen
        split at h
        · rename_i hl
          exact ⟨r₁, len, by rw [hid], hlen, hl, h⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- **A known section is one step of `readModule.go`.** -/
theorem go_section {α : Type} {B : List UInt8} {N : UInt8} {kS : Nat}
    {inner : List UInt8 → Option α} {r : List UInt8} {v : α} {y fuel last : Nat} {S S' : Sections}
    (h : chkSection N kS inner r = some v) (hB : At B y r) (hN : N.toNat ≠ 0)
    (hlast : last < sectionRank N.toNat)
    (hbody : ∀ x b, inner b = some v → At B x b →
      readSectionBody N.toNat S ⟨arr B, x⟩ = .ok (S', ⟨arr B, x + b.length⟩)) :
    readModule.go (fuel + 1) last S ⟨arr B, y⟩ =
      readModule.go fuel (sectionRank N.toNat) S' ⟨arr B, y + r.length⟩ := by
  obtain ⟨r₁, len, rfl, hlen, hl, hin⟩ := chkSection_parts h
  have hB₁ : At B (y + 1) r₁ := by
    have := hB; rw [show N :: r₁ = [N] ++ r₁ from rfl] at this; exact this.right
  have hB₁' := hB₁; rw [← List.take_append_drop kS r₁] at hB₁'
  have hu := run_of_runAll (frame_readU 32) hlen hB₁'.left
  have hbd := hB₁'.right
  have hb := hbody _ _ hin hbd
  have hfit := hbd.2
  rw [hl] at hb hfit
  rw [go_known hB.get hu hfit hN hlast hb]
  congr 2
  simp only [List.length_cons]
  have : (r₁.take kS).length + (r₁.drop kS).length = r₁.length := by
    rw [← List.length_append, List.take_append_drop]
  omega

theorem go_custom {B : List UInt8} {fuel last p x size : Nat} {S : Sections}
    (hb : B[p]? = some 0) (hu : readU 32 ⟨arr B, p + 1⟩ = .ok (size, ⟨arr B, x⟩))
    (hsz : x + size ≤ B.length)
    (hc : readCustom size ⟨arr B, x⟩ = .ok ((), ⟨arr B, x + size⟩)) :
    readModule.go (fuel + 1) last S ⟨arr B, p⟩ = readModule.go fuel last S ⟨arr B, x + size⟩ := by
  have hp : p < B.length := (List.getElem?_eq_some_iff.1 hb).1
  simp only [readModule.go]
  rw [bind_ok (remaining_apply _)]
  simp only [arr_size, show (B.length - p == 0) = false by simp; omega, Bool.false_eq_true,
    ↓reduceIte]
  rw [bind_ok (readByte_at hb), bind_ok hu, bind_ok (remaining_apply _)]
  simp only [arr_size, show size ≤ B.length - x by omega, ↓reduceIte]
  simp only [show ((0 : UInt8).toNat == 0) = true from rfl, ↓reduceIte]
  rw [bind_ok hc]

/-- **A custom section is one step of `readModule.go`.** -/
theorem go_customSec {B r : List UInt8} {kS kN y fuel last : Nat} {S : Sections}
    (h : chkCustom kS kN r = true) (hB : At B y r) :
    readModule.go (fuel + 1) last S ⟨arr B, y⟩ = readModule.go fuel last S ⟨arr B, y + r.length⟩ := by
  unfold chkCustom at h
  obtain ⟨nm, hnm⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨r₁, len, rfl, hlen, hl, hin⟩ := chkSection_parts hnm
  have hB₁ : At B (y + 1) r₁ := by
    have := hB; rw [show (0 : UInt8) :: r₁ = [0] ++ r₁ from rfl] at this; exact this.right
  have hB₁' := hB₁; rw [← List.take_append_drop kS r₁] at hB₁'
  have hu := run_of_runAll (frame_readU 32) hlen hB₁'.left
  have hbd := hB₁'.right
  set x := y + 1 + (r₁.take kS).length with hxdef
  clear_value x
  have hbd' := hbd; rw [← List.take_append_drop kN (r₁.drop kS)] at hbd'
  have hn := run_of_runAll frame_readName hin hbd'.left
  have hfit := hbd.2
  rw [hl] at hfit
  have hkn : ((r₁.drop kS).take kN).length ≤ len := by rw [← hl]; simp
  have hc : readCustom len ⟨arr B, x⟩ = .ok ((), ⟨arr B, x + len⟩) := by
    unfold readCustom
    rw [bind_ok (remaining_apply _), bind_ok hn, bind_ok (remaining_apply _)]
    simp only [arr_size, show B.length - x - (B.length - (x + ((r₁.drop kS).take kN).length)) =
      ((r₁.drop kS).take kN).length by omega, hkn, ↓reduceIte]
    rw [bind_apply, readBytes_apply]
    simp only [show x + ((r₁.drop kS).take kN).length + (len - ((r₁.drop kS).take kN).length) ≤
      (arr B).size by simp only [arr_size]; omega, ↓reduceIte]
    rw [show x + ((r₁.drop kS).take kN).length + (len - ((r₁.drop kS).take kN).length) = x + len by
      omega]
    rfl
  rw [go_custom hB.get hu hfit hc]
  congr 2
  simp only [List.length_cons, hxdef]
  have : (r₁.take kS).length + (r₁.drop kS).length = r₁.length := by
    rw [← List.length_append, List.take_append_drop]
  omega

theorem go_end {B : List UInt8} {fuel last : Nat} {S : Sections} :
    readModule.go (fuel + 1) last S ⟨arr B, B.length⟩ = .ok (S, ⟨arr B, B.length⟩) := by
  simp only [readModule.go]
  rw [bind_ok (remaining_apply _)]
  simp only [arr_size, Nat.sub_self, beq_self_eq_true, ↓reduceIte]
  rfl

/-! ## Section bodies -/

/-- How a section body updates the sections read so far. -/
def BodyOf {α : Type} (N : Nat) (f : DecodeM α) (upd : Sections → List α → Sections) : Prop :=
  ∀ S c xs c', readVec f c = .ok (xs, c') → readSectionBody N S c = .ok (upd S xs, c')

theorem body_types : BodyOf 1 readRecType fun S xs => { S with types := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_imports : BodyOf 2 readImport fun S xs => { S with imports := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_funcs : BodyOf 3 (readIdx (k := .type_)) fun S xs => { S with funcTypes := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_tables : BodyOf 4 readTable fun S xs => { S with tables := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_mems : BodyOf 5 readMemType fun S xs => { S with memories := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_globals : BodyOf 6 readGlobal fun S xs => { S with globals := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_exports : BodyOf 7 readExport fun S xs => { S with exports := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_elems : BodyOf 9 readElem fun S xs => { S with elems := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_code : BodyOf 10 readCode fun S xs => { S with code := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_data : BodyOf 11 readData fun S xs => { S with data := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl
theorem body_tags : BodyOf 13 readTag fun S xs => { S with tags := xs } := by
  intro S c xs c' h; simp only [readSectionBody]; rw [bind_ok h]; rfl

/-- **A vector section checked by its plan is one step of `readModule.go`.** -/
theorem go_vec {α : Type} {f : DecodeM α} (hf : Frame f) (hm : Mono f) {N : UInt8}
    {upd : Sections → List α → Sections} (hbody : BodyOf N.toNat f upd) {B r : List UInt8}
    {kS kc y fuel last : Nat} {ks : List Nat} {xs : List α} {S : Sections}
    (h : chkSection N kS (chkVec f kc ks) r = some xs) (hB : At B y r) (hN : N.toNat ≠ 0)
    (hlast : last < sectionRank N.toNat) :
    readModule.go (fuel + 1) last S ⟨arr B, y⟩ =
      readModule.go fuel (sectionRank N.toNat) (upd S xs) ⟨arr B, y + r.length⟩ :=
  go_section h hB hN hlast fun _ _ hin hb => hbody _ _ _ _ (readVec_of_chkVec' hf hm hin hb)

/-- **The data section checked by its plan is one step of `readModule.go`.** -/
theorem go_data {B r : List UInt8} {kS kC y fuel last : Nat} {ps : List (Nat × Nat × Nat)}
    {ds : List Silmaril.Wasm.Data} {S : Sections}
    (h : chkSection 11 kS (chkDataVec kC ps) r = some ds) (hB : At B y r) (hlast : last < 13) :
    readModule.go (fuel + 1) last S ⟨arr B, y⟩ =
      readModule.go fuel 13 { S with data := ds } ⟨arr B, y + r.length⟩ := by
  refine go_section (N := 11) h hB (by decide) hlast fun x b hin hb => body_data _ _ _ _ ?_
  unfold chkDataVec at hin
  split at hin
  · rename_i n ds' hc hs
    split at hin
    · rename_i hlen
      cases hin
      have hb' := hb; rw [← List.take_append_drop kC b] at hb'
      have hu := run_of_runAll (frame_readU 32) hc hb'.left
      obtain ⟨P, hP, hseg, hPl⟩ := datas_seg hs hb'.right
      simp only [List.append_nil] at hP
      have hlenb : (b.take kC).length + P.length = b.length := by
        rw [← List.length_append, ← hP, List.take_append_drop]
      have hfit := hb.2
      refine readVec_of_seg (by rw [hlen]; exact hu) (by omega) ?_
      rw [Nat.add_assoc, hlenb] at hseg
      exact hseg
    · cases hin
  · cases hin

/-- **The code section, from its id, size, count and groups**, is one step of `readModule.go`. -/
theorem go_code {B : List UInt8} {s x z e len fuel last : Nat}
    {cs : List (List Silmaril.Wasm.ValType × Silmaril.Wasm.Expr)} {S : Sections}
    (hid : B[s]? = some 10) (hsz : readU 32 ⟨arr B, s + 1⟩ = .ok (len, ⟨arr B, x⟩))
    (hxe : x + len = e) (he : e ≤ B.length)
    (hcnt : readU 32 ⟨arr B, x⟩ = .ok (cs.length, ⟨arr B, z⟩)) (hn : cs.length ≤ B.length - z)
    (hseg : VecSeg readCode B z e cs) (hlast : last < 12) :
    readModule.go (fuel + 1) last S ⟨arr B, s⟩ =
      readModule.go fuel 12 { S with code := cs } ⟨arr B, e⟩ := by
  have hzx : x ≤ z := by have := mono_apply (mono_readU 32) hcnt; simpa using this
  obtain ⟨k, rfl⟩ : ∃ k, z = x + k := ⟨z - x, by omega⟩
  have hv := readVec_of_seg hcnt hn hseg
  have hbody := body_code S _ _ _ hv
  rw [← hxe] at hbody
  have := go_known (b := 10) (fuel := fuel) (last := last) hid hsz (by omega) (by decide) hlast hbody
  rw [this, hxe]
  rfl

/-! ## The whole module -/

/-- **`decode?` from a run of the section loop.** -/
theorem decode_of_go {B : List UInt8} {S : Sections}
    (hhdr : B.take 8 = Silmaril.Wasm.Binary.magic ++ Silmaril.Wasm.Binary.version)
    (h8 : 8 ≤ B.length)
    (hgo : readModule.go B.length 0 {} ⟨arr B, 8⟩ = .ok (S, ⟨arr B, B.length⟩))
    (hf : S.funcTypes.length = S.code.length) (hdc : S.dataCount = none)
    (hdi : Silmaril.Wasm.Binary.Core.codesDataIdxs S.code = []) :
    Silmaril.Wasm.Binary.Core.decode? (arr B) = some
      { types := S.types, imports := S.imports, tags := S.tags, globals := S.globals,
        tables := S.tables, memories := S.memories, elems := S.elems,
        funcs := Silmaril.Wasm.Binary.Core.zipFuncs S.funcTypes S.code, data := S.data,
        start := S.start, exports := S.exports } := by
  have hhead : readHeader ⟨arr B, 0⟩ = .ok ((), ⟨arr B, 8⟩) := by
    unfold readHeader
    rw [bind_apply, readBytes_apply]
    simp only [arr_size, Nat.zero_add, h8, ↓reduceIte]
    have : ((arr B).extract 0 8).data.toList = Silmaril.Wasm.Binary.magic ++ Silmaril.Wasm.Binary.version := by
      rw [extract_arr B 0 8]; simpa [Silmaril.Wasm.Binary.Core.dataBytes] using hhdr
    simp only [this, beq_self_eq_true, ↓reduceIte]
    rfl
  unfold Silmaril.Wasm.Binary.Core.decode? Silmaril.Wasm.Binary.Core.Decode.decodeModule
  simp only [StateT.run']
  show (match (readModule ⟨arr B, 0⟩).map Prod.fst with
    | .ok m => some m | .error _ => none) = _
  unfold readModule
  rw [bind_ok hhead]
  rw [bind_ok (get_apply _)]
  simp only [arr_size]
  rw [bind_ok hgo, bind_ok (remaining_apply _)]
  simp only [arr_size, Nat.sub_self, beq_self_eq_true, ↓reduceIte, hf, hdc, hdi, Option.all_none,
    Option.isSome_none, List.isEmpty_nil, Bool.or_true]
  rfl

end Silmaril.Wasm.Component.ChunkedDecode

end
