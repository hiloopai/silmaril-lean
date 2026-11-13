module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Lift

/-!
# Byte memory on Core 3.0: `i32.load8_u`, `i32.store8`, `memory.copy`

`MemR s F ma m`: memory `0` of frame `F` is the store's memory at address `ma`, of `MSZ` bytes,
and byte `a` of it is `m a`. On it:

* `memR_load`: `i32.load8_u` at an address below `MSZ` pushes `m a`;
* `memR_store`: `i32.store8` at an address below `MSZ` leaves a store whose memory is
  `upd m a (v % 256)` (and whose other parts are unchanged);
* `memR_copy`: `memory.copy d s n` with `d ≤ s` and `s + n ≤ MSZ` (Core's `memory.copy-le`
  rule, a byte at a time from the front) leaves `KCore.mcopy m d s n`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Memory
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (BI M32 upd mcopy)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix ma0)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma : Nat}

/-! ## Bytes -/

theorem load1 (b : ByteArray) (a : Nat) (h : a < b.size) :
    load b a 1 = some (BitVec.ofNat 8 (b[a]'h).toNat) := by
  have hr : readBytes b a 1 = some (b.extract a (a + 1)) := by simp [readBytes]; omega
  simp only [load, hr, Option.map_some]
  congr 1
  simp only [decodeLE, ByteArray.data_extract]
  have : (b.data.extract a (a + 1)) = #[b.data[a]'(by simpa using h)] := by
    apply Array.ext
    · simp; omega
    · intro i h1 h2
      have hi : i = 0 := by simp at h2; omega
      subst hi; simp
  rw [this]; simp [ByteArray.getElem_eq_getElem_data]

theorem store1 (b : ByteArray) (a : Nat) (c : BitVec (8 * 1)) :
    store b a c = writeBytes b a ⟨#[UInt8.ofNat c.toNat]⟩ := rfl

theorem wb_get (mem bs after : ByteArray) (p a : Nat) (h : writeBytes mem p bs = some after)
    (ha : a < mem.size) :
    ∃ ha' : a < after.size, after[a]'ha' =
      if hb : p ≤ a ∧ a < p + bs.size then bs[a - p]'(by omega) else mem[a]'ha := by
  obtain ⟨bound, rfl⟩ := (writeBytes_eq_some_iff mem bs _ p).mp h
  refine ⟨by simp; omega, ?_⟩
  simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_append, ByteArray.data_extract]
  simp [Array.getElem_append, Array.getElem_extract]
  repeat' split
  all_goals first | rfl | omega | (congr 1; omega)

theorem wb1 (mem after : ByteArray) (p : Nat) (v : UInt8)
    (h : writeBytes mem p ⟨#[v]⟩ = some after) (a : Nat) (ha : a < mem.size) :
    ∃ ha' : a < after.size, after[a]'ha' = if p = a then v else mem[a]'ha := by
  obtain ⟨ha', e⟩ := wb_get mem _ after p a h ha
  refine ⟨ha', ?_⟩
  rw [e]
  split
  · rename_i hc
    have hpa : p = a := by simp [ByteArray.size] at hc; omega
    subst hpa
    simp [ByteArray.getElem_eq_getElem_data]
  · rename_i hc
    have hpa : p ≠ a := by
      intro hpa; subst hpa; exact hc ⟨Nat.le_refl _, by simp [ByteArray.size]⟩
    simp [hpa]

theorem wb1_some (mem : ByteArray) (p : Nat) (v : UInt8) (hp : p < mem.size) :
    ∃ after, writeBytes mem p ⟨#[v]⟩ = some after := by
  unfold writeBytes
  split
  · exact ⟨_, rfl⟩
  · rename_i hc
    exfalso
    exact hc (by show p + 1 ≤ mem.size; omega)

/-! ## `i32`s -/

theorem w_toNat {a : Nat} (ha : a < M32) : (w a).toNat = a := by
  simp only [w, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ha

theorem setWidth_byte (n : Nat) (h : n < 256) : (BitVec.ofNat 8 n).setWidth 32 = w n := by
  apply BitVec.eq_of_toNat_eq
  simp [w]
  omega

theorem w_succ {a : Nat} : w a + 1 = w (a + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [w, BitVec.toNat_add]

theorem w_pred (n : Nat) : w (n + 1) - 1 = w n := by
  rw [← w_succ]
  exact BitVec.add_sub_cancel _ _

/-! ## The memory relation -/

/-- Memory `0` of `F` is the store's memory `ma`, of `MSZ` bytes, holding `m`. -/
def MemR (s : Store H) (F : Frame) (ma : Nat) (m : Nat → Nat) : Prop :=
  ∃ mi, F.module.mems[0]? = some ma ∧ s.mems[ma]? = some mi ∧ mi.bytes.size = MSZ ∧
    ∀ a (h : a < mi.bytes.size), (mi.bytes[a]'h).toNat = m a

theorem MemR.mem? {s : Store H} {F : Frame} {mi : MemInst}
    (h0 : F.module.mems[0]? = some ma) (h1 : s.mems[ma]? = some mi) :
    s.mem? F (ix 0) = some (ma, mi) := by
  have e : (ix 0 : MemIdx).toNat = 0 := rfl
  simp [Store.mem?, e, h0, h1]

theorem MemR.byte_lt {s : Store H} {F : Frame} {m : Nat → Nat} (h : MemR s F ma m) {a : Nat}
    (ha : a < MSZ) : m a < 256 := by
  obtain ⟨mi, -, -, hs, hb⟩ := h
  rw [← hb a (by omega)]
  exact UInt8.toNat_lt _

/-- `i32.load8_u` at an address below `MSZ`. -/
theorem memR_load {q : HQ} {s : Store H} {F : Frame} {m : Nat → Nat} (h : MemR s F ma m)
    {arg : MemArg} (hoff : arg.offset.val = 0) {a : Nat} (ha : a < MSZ) (ops : List W)
    (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨s, F, stackA (w a :: ops) ++
        .plain (.intLoad .i32 (some (.i8, .unsigned)) (ix 0) arg) :: rest⟩)
      (q, ⟨s, F, stackA (w (m a) :: ops) ++ rest⟩) := by
  obtain ⟨mi, h0, h1, hs, hb'⟩ := h
  have hm := MemR.mem? h0 h1
  have ha' : a < mi.bytes.size := by omega
  have ha32 : a < M32 := by unfold MSZ at ha; unfold M32; omega
  have hl : load mi.bytes (effAddr (w a).toNat arg) (PackSize.i8.width / 8) =
      some (BitVec.ofNat 8 (mi.bytes[a]'ha').toNat) := by
    simp only [effAddr, hoff, Nat.add_zero, w_toNat ha32]
    exact load1 mi.bytes a ha'
  have hstep := MemoryStep.loadPackVal (P := Pf) (sx := .unsigned) (t := .i32) (a := .i32)
    (i := w a) hm hl
  have e₁ : stackA (w a :: ops) ++ .plain (.intLoad .i32 (some (.i8, .unsigned)) (ix 0) arg) :: rest =
      stackA ops ++ [aconst .i32 (w a), .plain (.intLoad .i32 (some (.i8, .unsigned)) (ix 0) arg)] ++
        rest := by
    simp [stackA, vals, aconst, AddrType.intType, i32_toAdmin]
  have e₂ : stackA (w (m a) :: ops) ++ rest =
      stackA ops ++ [Admin.plain (.intConst .i32 ((BitVec.ofNat 8 (mi.bytes[a]'ha').toNat).setWidth 32))] ++
        rest := by
    rw [stackA_cons, setWidth_byte _ (UInt8.toNat_lt _), hb' a ha']
    rfl
  rw [e₁, e₂]
  exact top ops rest (.memory hstep)

theorem global?_of_globals {s s' : Store H} (he : s'.globals = s.globals) (F : Frame)
    (x : GlobalIdx) : s'.global? F x = s.global? F x := by
  simp [Store.global?, he]

/-- `i32.store8` at an address below `MSZ`. -/
theorem memR_store {q : HQ} {s : Store H} {F : Frame} {m : Nat → Nat} (h : MemR s F ma m)
    {arg : MemArg} (hoff : arg.offset.val = 0) {a : Nat} (ha : a < MSZ) (v : Nat) :
    ∃ s', MemR s' F ma (upd m a (v % 256)) ∧ s'.globals = s.globals ∧ s'.funcs = s.funcs ∧
      ∀ (ops : List W) (rest : List Admin), HSteps Pf hb ma (q, ⟨s, F, stackA (w v :: w a :: ops) ++
          .plain (.intStore .i32 (some .i8) (ix 0) arg) :: rest⟩)
        (q, ⟨s', F, stackA ops ++ rest⟩) := by
  obtain ⟨mi, h0, h1, hs, hb'⟩ := h
  have hm := MemR.mem? h0 h1
  have ha' : a < mi.bytes.size := by omega
  have ha32 : a < M32 := by unfold MSZ at ha; unfold M32; omega
  obtain ⟨after, hw⟩ := wb1_some mi.bytes a (UInt8.ofNat ((w v).setWidth 8).toNat) ha'
  have hst : store mi.bytes (effAddr (w a).toNat arg) (count := PackSize.i8.width / 8)
      ((w v).setWidth _) = some after := by
    simp only [effAddr, hoff, Nat.add_zero, w_toNat ha32]
    exact hw
  have hstep := MemoryStep.storePackVal (P := Pf) (t := .i32) (sz := .i8) (a := .i32) (i := w a)
    (c := w v) hm hst
  have hsz : after.size = mi.bytes.size := writeBytes_size _ _ _ _ hw
  refine ⟨s.setMem ma { mi with bytes := after }, ⟨{ mi with bytes := after }, h0, ?_, ?_, ?_⟩,
    rfl, rfl, ?_⟩
  · simp [Store.setMem, (List.getElem?_eq_some_iff.mp h1).1]
  · show after.size = MSZ; omega
  · show ∀ (j : Nat) (hj : j < after.size), (after[j]'hj).toNat = upd m a (v % 256) j
    intro j hj
    obtain ⟨hj', e⟩ := wb1 mi.bytes after a _ hw j (by simpa [hsz] using hj)
    show (after[j]'hj).toNat = _
    rw [e]
    by_cases hja : a = j
    · subst hja
      simp only [upd, ↓reduceIte]
      simp [w]
    · simp only [hja, upd, Ne.symm hja, ↓reduceIte]
      exact hb' j _
  · intro ops rest
    have e₁ : stackA (w v :: w a :: ops) ++ .plain (.intStore .i32 (some .i8) (ix 0) arg) :: rest =
        stackA ops ++ [aconst .i32 (w a), .plain (.intConst .i32 (w v)),
          .plain (.intStore .i32 (some .i8) (ix 0) arg)] ++ rest := by
      simp [stackA, vals, aconst, AddrType.intType, i32_toAdmin]
    rw [e₁]
    simpa using top (q := q) (hb := hb) (ma := ma) ops rest (.memory hstep)

/-! ## `memory.copy` -/

theorem mcopy_zero (m : Nat → Nat) (d src : Nat) : mcopy m d src 0 = m := by
  funext x
  simp only [mcopy]
  split
  · omega
  · rfl

/-- One byte copied at the front, then the rest. -/
theorem mcopy_succ (m : Nat → Nat) {d src : Nat} (hle : d ≤ src) (n : Nat) :
    mcopy (upd m d (m src)) (d + 1) (src + 1) n = mcopy m d src (n + 1) := by
  funext x
  simp only [mcopy, upd]
  by_cases h1 : d + 1 ≤ x ∧ x < d + 1 + n
  · have h2 : d ≤ x ∧ x < d + (n + 1) := by omega
    have h3 : src + 1 + (x - (d + 1)) ≠ d := by omega
    have h4 : src + 1 + (x - (d + 1)) = src + (x - d) := by omega
    have h5 : src + (x - d) ≠ d := by omega
    simp only [h1, h2, h4, h5, ↓reduceIte, and_self]
  · simp only [h1, ↓reduceIte]
    by_cases hx : x = d
    · subst hx
      simp
    · have h2 : ¬ (d ≤ x ∧ x < d + (n + 1)) := by omega
      simp only [hx, h2, ↓reduceIte]

theorem src_lt {d src n : Nat} (hb : src + n ≤ MSZ) (h : d ≤ src) : d < M32 ∧ src < M32 ∧ n < M32 := by
  unfold MSZ at hb; unfold M32; omega

/-- **`memory.copy d s n`** with `d ≤ s` within memory: Core's front-to-back byte copy leaves
`mcopy m d s n`. -/
theorem memR_copy {q : HQ} {F : Frame} :
    ∀ (n : Nat) {s : Store H} {m : Nat → Nat} {d src : Nat}, MemR s F ma m → d ≤ src →
      src + n ≤ MSZ →
      ∃ s', MemR s' F ma (mcopy m d src n) ∧ s'.globals = s.globals ∧ s'.funcs = s.funcs ∧
        ∀ (ops : List W) (rest : List Admin), HSteps Pf hb ma (q, ⟨s, F, stackA (w n :: w src :: w d :: ops) ++
            .plain (.memoryCopy (ix 0) (ix 0)) :: rest⟩)
          (q, ⟨s', F, stackA ops ++ rest⟩)
  | 0, s, m, d, src, h, hle, hb' => by
    obtain ⟨mi, h0, h1, hs, -⟩ := id h
    have hm := MemR.mem? (s := s) (F := F) h0 h1
    obtain ⟨hd, hsr, -⟩ := src_lt (n := 0) hb' hle
    have hstep := MemoryStep.copyZero (P := Pf) (a₁ := .i32) (a₂ := .i32) (a' := .i32)
      (i₁ := w d) (i₂ := w src) hm hm (by simp only [w, AddrType.intType, IntType.width, BitVec.toNat_ofNat]; unfold M32 at *; omega)
    refine ⟨s, by rw [mcopy_zero]; exact h, rfl, rfl, fun ops rest => ?_⟩
    have e₁ : stackA (w 0 :: w src :: w d :: ops) ++ .plain (.memoryCopy (ix 0) (ix 0)) :: rest =
        stackA ops ++ [Admin.plain (.intConst .i32 (w d)), Admin.plain (.intConst .i32 (w src)),
          Admin.plain (.intConst .i32 (w 0)), .plain (.memoryCopy (ix 0) (ix 0))] ++ rest := by
      simp [stackA, vals, i32_toAdmin]
    have r := top (q := q) (hb := hb) (ma := ma) ops rest (.memory hstep)
    rw [List.append_nil] at r
    rw [e₁]
    exact r
  | n + 1, s, m, d, src, h, hle, hb' => by
    obtain ⟨mi, h0, h1, hs, -⟩ := id h
    have hm := MemR.mem? (s := s) (F := F) h0 h1
    obtain ⟨hd, hsr, hn⟩ := src_lt hb' hle
    have hn0 : w (n + 1) ≠ 0 := by
      intro h0'
      have := congrArg BitVec.toNat h0'
      rw [w_toNat hn] at this
      simp at this
    have hstep := MemoryStep.copyLe (P := Pf) (a₁ := .i32) (a₂ := .i32) (a' := .i32)
      (i₁ := w d) (i₂ := w src) (n := w (n + 1)) hm hm
      (by simp only [w, AddrType.intType, IntType.width, BitVec.toNat_ofNat]; unfold M32 at *; omega) hn0
      (by simp only [w, AddrType.intType, IntType.width, BitVec.toNat_ofNat]; unfold M32 at *; omega)
    obtain ⟨s₁, h₁, hg₁, hf₁, r₃⟩ := memR_store (Pf := Pf) (hb := hb) (q := q) h (arg := memarg0)
      rfl (a := d) (by omega) (m src)
    have hbyte : m src % 256 = m src := Nat.mod_eq_of_lt (h.byte_lt (by omega))
    rw [hbyte] at h₁
    obtain ⟨s₂, h₂, hg₂, hf₂, r₄⟩ := memR_copy n h₁ (d := d + 1) (src := src + 1)
      (by omega) (by omega)
    refine ⟨s₂, by rw [← mcopy_succ m hle]; exact h₂, hg₂.trans hg₁, hf₂.trans hf₁, fun ops rest => ?_⟩
    have e₁ : stackA (w (n + 1) :: w src :: w d :: ops) ++ .plain (.memoryCopy (ix 0) (ix 0)) :: rest =
        stackA ops ++ [Admin.plain (.intConst .i32 (w d)), Admin.plain (.intConst .i32 (w src)), Admin.plain (.intConst .i32 (w (n + 1))),
          .plain (.memoryCopy (ix 0) (ix 0))] ++ rest := by
      simp [stackA, vals, i32_toAdmin]
    have e₂ : stackA ops ++ [Admin.plain (.intConst .i32 (w d)), Admin.plain (.intConst .i32 (w src)), load8u (ix 0), store8 (ix 0),
          Admin.plain (.intConst .i32 (w d + 1 : W)), Admin.plain (.intConst .i32 (w src + 1 : W)), Admin.plain (.intConst .i32 (w (n + 1) - 1 : W)),
          .plain (.memoryCopy (ix 0) (ix 0))] ++ rest =
        stackA (w src :: w d :: ops) ++ load8u (ix 0) :: store8 (ix 0) ::
          ([Admin.plain (.intConst .i32 (w (d + 1))), Admin.plain (.intConst .i32 (w (src + 1))), Admin.plain (.intConst .i32 (w n))] ++
            .plain (.memoryCopy (ix 0) (ix 0)) :: rest) := by
      rw [w_succ, w_succ, w_pred]
      simp [stackA, vals, i32_toAdmin]
    have e₃ : stackA ops ++ ([Admin.plain (.intConst .i32 (w (d + 1))), Admin.plain (.intConst .i32 (w (src + 1))), Admin.plain (.intConst .i32 (w n))] ++
          .plain (.memoryCopy (ix 0) (ix 0)) :: rest) =
        stackA (w n :: w (src + 1) :: w (d + 1) :: ops) ++ .plain (.memoryCopy (ix 0) (ix 0)) :: rest := by
      simp [stackA, vals, i32_toAdmin]
    have r₁ : HSteps Pf hb ma (q, ⟨s, F, stackA (w (n + 1) :: w src :: w d :: ops) ++
        .plain (.memoryCopy (ix 0) (ix 0)) :: rest⟩)
        (q, ⟨s, F, stackA (w src :: w d :: ops) ++ load8u (ix 0) :: store8 (ix 0) ::
          ([Admin.plain (.intConst .i32 (w (d + 1))), Admin.plain (.intConst .i32 (w (src + 1))), Admin.plain (.intConst .i32 (w n))] ++
            .plain (.memoryCopy (ix 0) (ix 0)) :: rest)⟩) := by
      rw [e₁, ← e₂]
      exact top ops rest (.memory hstep)
    have r₂ := memR_load (Pf := Pf) (hb := hb) (q := q) h (arg := memarg0) rfl
      (a := src) (by omega) (w d :: ops)
      (store8 (ix 0) :: ([Admin.plain (.intConst .i32 (w (d + 1))), Admin.plain (.intConst .i32 (w (src + 1))), Admin.plain (.intConst .i32 (w n))] ++
        .plain (.memoryCopy (ix 0) (ix 0)) :: rest))
    have r₃' := r₃ ops ([Admin.plain (.intConst .i32 (w (d + 1))),
      Admin.plain (.intConst .i32 (w (src + 1))), Admin.plain (.intConst .i32 (w n))] ++
        .plain (.memoryCopy (ix 0) (ix 0)) :: rest)
    rw [e₃] at r₃'
    exact r₁.trans (r₂.trans (r₃'.trans (r₄ ops rest)))

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
