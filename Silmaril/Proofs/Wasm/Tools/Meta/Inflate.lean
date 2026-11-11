module

public import Silmaril.Wasm.Tools.Meta.Inflate.Defs

/-!
# Raw proofs: inflate on stored streams

Restated in `Silmaril.Wasm.Tools.Meta.Inflate.Thms`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Tools.Meta.Inflate

open Silmaril.Wasm.Tools.Meta.Inflate

/-- The Adler-32 checksum as a list fold. -/
def adlerL (l : List UInt8) : Nat × Nat :=
  l.foldl (fun (ab : Nat × Nat) x => ((ab.1 + x.toNat) % 65521, (ab.2 + (ab.1 + x.toNat) % 65521) % 65521)) (1, 0)

/-- The stored-block encoder (`zlibStored`). -/
abbrev storedStream (d : ByteArray) : ByteArray := zlibStored d

theorem get!_mk (a : Array UInt8) (i : Nat) (h : i < a.size) : (ByteArray.mk a).get! i = a[i] := by
  simp [ByteArray.get!, h]

theorem size_mk (a : Array UInt8) : (ByteArray.mk a).size = a.size := rfl

/-- `fill` takes one byte when the buffer is empty. -/
theorem fill_byte (s : IS) (need f : Nat) (h0 : s.bitcnt = 0) (hn : 0 < need) (hn8 : need ≤ 8)
    (hp : s.pos < s.src.size) :
    (fill need (f + 2)).run s = .ok ((), { s with bitbuf := s.bitbuf + (s.src.get! s.pos).toNat, pos := s.pos + 1, bitcnt := 8 }) := by
  have hne : need ≠ 0 := by omega
  have h2 : ¬ s.src.size ≤ s.pos := by omega
  simp [fill, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, modify, modifyGet, StateT.modifyGet, MonadState.modifyGet, h0, hne, h2, hn8]

/-- `bits n` when the buffer holds enough bits. -/
theorem bits_have (s : IS) (need : Nat) (h : need ≤ s.bitcnt) :
    (bits need).run s = .ok (s.bitbuf % 2 ^ need, { s with bitbuf := s.bitbuf / 2 ^ need, bitcnt := s.bitcnt - need }) := by
  simp [bits, fill, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, modify, modifyGet, StateT.modifyGet, MonadState.modifyGet, h]

/-- `bits n` on an empty buffer: the low bits of the next byte. -/
theorem bits_byte (s : IS) (need : Nat) (h0 : s.bitcnt = 0) (h00 : s.bitbuf = 0) (hn : 0 < need)
    (hn8 : need ≤ 8) (hp : s.pos < s.src.size) :
    (bits need).run s = .ok ((s.src.get! s.pos).toNat % 2 ^ need, { s with bitbuf := (s.src.get! s.pos).toNat / 2 ^ need, pos := s.pos + 1, bitcnt := 8 - need }) := by
  have hf := fill_byte s need 1 h0 hn hn8 hp
  simp only [StateT.run] at hf
  simp only [bits, StateT.run, bind, StateT.bind]
  rw [show (3 : Nat) = 1 + 2 from rfl, hf]
  simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, modify, modifyGet, StateT.modifyGet, MonadState.modifyGet, h00]

/-- `emit` below the cap. -/
theorem emit_ok (s : IS) (b : UInt8) (h : s.out.size < s.cap) :
    (emit b).run s = .ok ((), { s with out := s.out.push b }) := by
  have : ¬ s.cap < s.out.size + 1 := by omega
  simp [emit, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, modify, modifyGet, StateT.modifyGet, MonadState.modifyGet, ByteArray.size_push, this]

/-- One step of the copy: a byte of the input moved to the output. -/
def copyStep (s : IS) : IS :=
  { s with pos := s.pos + 1, out := s.out.push (s.src.get! s.pos) }

/-- `k` steps of the copy. -/
def copyN : Nat → IS → IS
  | 0, s => s
  | k + 1, s => copyN k (copyStep s)

/-- The state after copying `k` bytes. -/
theorem copyN_eq (k : Nat) : ∀ s : IS, s.pos + k ≤ s.src.size →
    (copyN k s).out.data = s.out.data ++ s.src.data.extract s.pos (s.pos + k) ∧
      (copyN k s).pos = s.pos + k ∧ (copyN k s).src = s.src ∧ (copyN k s).cap = s.cap := by
  induction k with
  | zero => intro s _; simp [copyN]; omega
  | succ k ih =>
    show ∀ s : IS, s.pos + (k + 1) ≤ s.src.size →
      (copyN (k + 1) s).out.data = s.out.data ++ s.src.data.extract s.pos (s.pos + (k + 1)) ∧
        (copyN (k + 1) s).pos = s.pos + (k + 1) ∧ (copyN (k + 1) s).src = s.src ∧
        (copyN (k + 1) s).cap = s.cap
    intro s hp
    have hlt : s.pos < s.src.data.size := by
      have : s.src.size = s.src.data.size := rfl
      omega
    obtain ⟨h1, h2, h3, h4⟩ := ih (copyStep s) (by show s.pos + 1 + k ≤ s.src.size; omega)
    refine ⟨?_, ?_, h3, h4⟩
    · show (copyN (k + 1) s).out.data = s.out.data ++ s.src.data.extract s.pos (s.pos + (k + 1))
      rw [copyN, h1]
      show (s.out.push (s.src.get! s.pos)).data ++ s.src.data.extract (s.pos + 1) (s.pos + 1 + k) = _
      have hg : s.src.get! s.pos = s.src.data[s.pos] := by
        simp only [ByteArray.get!]; exact getElem!_pos s.src.data s.pos hlt
      rw [ByteArray.data_push, hg]
      apply Array.ext'
      simp only [Array.toList_append, Array.toList_push, Array.toList_extract, List.extract_eq_take_drop]
      rw [show s.pos + 1 + k = s.pos + (k + 1) by omega]
      have hl : s.pos < s.src.data.toList.length := by simpa using hlt
      have hd : s.src.data.toList.drop s.pos = s.src.data.toList[s.pos] :: s.src.data.toList.drop (s.pos + 1) :=
        List.drop_eq_getElem_cons hl
      rw [show s.pos + (k + 1) - (s.pos + 1) = k by omega, show s.pos + (k + 1) - s.pos = k + 1 by omega,
        hd, List.take_succ_cons]
      simp
    · rw [copyN, h2]; show s.pos + 1 + k = s.pos + (k + 1); omega

/-- A loop whose body copies one byte while input and room remain. -/
theorem copy_loop (g : Nat → PUnit → IM (ForInStep PUnit))
    (hg : ∀ i (s : IS), s.pos < s.src.size → s.out.size < s.cap →
      (g i PUnit.unit).run s = .ok (.yield PUnit.unit, copyStep s)) :
    ∀ (l : List Nat) (s : IS), s.pos + l.length ≤ s.src.size → s.out.size + l.length ≤ s.cap →
      (forIn l PUnit.unit g).run s = .ok (PUnit.unit, copyN l.length s)
  | [], s, _, _ => rfl
  | i :: l, s, hp, hc => by
    simp only [List.length_cons] at hp hc
    have h1 := hg i s (by omega) (by omega)
    simp only [List.forIn_cons, StateT.run, bind, StateT.bind] at h1 ⊢
    rw [h1]
    simp only [Except.bind]
    have ih := copy_loop g hg l (copyStep s) (by simp [copyStep]; omega)
      (by simp [copyStep, ByteArray.size_push]; omega)
    simp only [StateT.run] at ih
    rw [ih, List.length_cons, copyN]

theorem run_bind {α β : Type} {x : IM α} {g : α → IM β} {s s' : IS} {a : α}
    (h : x.run s = .ok (a, s')) : (x >>= g).run s = (g a).run s' := by
  simp only [StateT.run, bind, StateT.bind] at h ⊢
  rw [h]; rfl

/-- The header bytes of `storedStream`. -/
def hdr (n : Nat) : Array UInt8 :=
  #[0x78, 0x01, 0x01, (n % 256).toUInt8, (n / 256).toUInt8, ((65535 - n) % 256).toUInt8,
    ((65535 - n) / 256).toUInt8]

def trl (c : Nat) : Array UInt8 :=
  #[(c / 16777216 % 256).toUInt8, (c / 65536 % 256).toUInt8, (c / 256 % 256).toUInt8, (c % 256).toUInt8]

theorem storedStream_data (d : ByteArray) :
    (storedStream d).data = hdr d.size ++ d.data ++ trl (adler32 d) := rfl


theorem hdr_size (n : Nat) : (hdr n).size = 7 := rfl
theorem trl_size (c : Nat) : (trl c).size = 4 := rfl
theorem bsize (d : ByteArray) : d.size = d.data.size := rfl

theorem storedStream_size (d : ByteArray) : (storedStream d).size = d.size + 11 := by
  rw [bsize, storedStream_data, Array.size_append, Array.size_append, hdr_size, trl_size, ← bsize]
  omega

theorem get_hdr (d : ByteArray) (i : Nat) (h : i < 7) :
    (storedStream d).get! i = (hdr d.size)[i]'(by rw [hdr_size]; omega) := by
  simp only [ByteArray.get!]
  have hs : i < (storedStream d).data.size := by
    have := storedStream_size d; rw [bsize] at this; omega
  rw [getElem!_pos (storedStream d).data i hs]
  simp only [storedStream_data]
  rw [Array.getElem_append_left (by rw [Array.size_append, hdr_size]; omega),
    Array.getElem_append_left (by rw [hdr_size]; omega)]

theorem get_data (d : ByteArray) (i : Nat) (h : i < d.size) :
    (storedStream d).get! (7 + i) = d.data[i]'(by rw [← bsize]; omega) := by
  simp only [ByteArray.get!]
  have hs : 7 + i < (storedStream d).data.size := by
    have := storedStream_size d; rw [bsize] at this; omega
  rw [getElem!_pos (storedStream d).data (7 + i) hs]
  simp only [storedStream_data]
  rw [Array.getElem_append_left (by rw [Array.size_append, hdr_size, ← bsize]; omega),
    Array.getElem_append_right (by rw [hdr_size]; omega)]
  simp only [hdr_size, Nat.add_sub_cancel_left]

theorem get_trl (d : ByteArray) (j : Nat) (h : j < 4) :
    (storedStream d).get! (7 + d.size + j) = (trl (adler32 d))[j]'(by rw [trl_size]; omega) := by
  simp only [ByteArray.get!]
  have hs : 7 + d.size + j < (storedStream d).data.size := by
    have := storedStream_size d; rw [bsize] at this; omega
  rw [getElem!_pos (storedStream d).data (7 + d.size + j) hs]
  simp only [storedStream_data]
  rw [Array.getElem_append_right (by rw [Array.size_append, hdr_size, ← bsize]; omega)]
  simp only [Array.size_append, hdr_size, ← bsize, Nat.add_sub_cancel_left]

theorem loop_inv {β : Type} (as : ByteArray) (P : β → Prop) (f : UInt8 → β → Id (ForInStep β))
    (hf : ∀ x b, P b → P (match f x b with | .yield b' => b' | .done b' => b')) :
    ∀ (i : Nat) (h : i ≤ as.size) (b : β), P b → P (ByteArray.forIn.loop as f i h b)
  | 0, _, b, hb => by rw [ByteArray.forIn.loop]; exact hb
  | i + 1, h, b, hb => by
    rw [ByteArray.forIn.loop]
    have := hf as[as.size - 1 - i] b hb
    cases hc : f as[as.size - 1 - i] b with
    | done b' => rw [hc] at this; simp only [hc]; exact this
    | yield b' => rw [hc] at this; simp only [hc]; exact loop_inv as P f hf i _ b' this

/-- An invariant of every state of a `for … in` loop over a `ByteArray` in `Id`. -/
theorem forIn_inv {β : Type} (as : ByteArray) (P : β → Prop) (f : UInt8 → β → Id (ForInStep β))
    (hf : ∀ x b, P b → P (match f x b with | .yield b' => b' | .done b' => b')) :
    ∀ b, P b → P (forIn as b f) := fun b hb => loop_inv as P f hf as.size (Nat.le_refl _) b hb

theorem adler32_lt (d : ByteArray) : adler32 d < 2 ^ 32 := by
  unfold adler32
  simp only [Id.run]
  have hr := forIn_inv d (fun s : Nat × Nat => s.1 < 65521 ∧ s.2 < 65521)
    (fun (x : UInt8) (s : Nat × Nat) =>
      (pure (ForInStep.yield ((s.fst + x.toNat) % 65521, (s.snd + (s.fst + x.toNat) % 65521) % 65521)) : Id _))
    (fun x b _ => ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega)⟩) ((1 : Nat), (0 : Nat)) ⟨by omega, by omega⟩
  revert hr
  generalize (forIn d ((1 : Nat), (0 : Nat)) fun (x : UInt8) (s : Nat × Nat) =>
    (pure (ForInStep.yield ((s.fst + x.toNat) % 65521, (s.snd + (s.fst + x.toNat) % 65521) % 65521)) : Id _)) = r
  intro hr
  show r.snd * 65536 + r.fst < 2 ^ 32
  omega


theorem run_get (s : IS) : (get : IM IS).run s = .ok (s, s) := rfl
theorem run_modify (s : IS) (f : IS → IS) : (modify f : IM Unit).run s = .ok ((), f s) := rfl
theorem run_set (s s' : IS) : (set s' : IM Unit).run s = .ok ((), s') := rfl
theorem run_pure {α : Type} (s : IS) (a : α) : (pure a : IM α).run s = .ok (a, s) := rfl

/-- The state at the start of the copy: after the header, the block header and `LEN`/`NLEN`. -/
def s7 (d : ByteArray) (cap : Nat) : IS := { src := storedStream d, pos := 7, cap }

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]

/-- The stored block's body, from `LEN`. -/
theorem stored_run (d : ByteArray) (cap bb bc : Nat) (hn : d.size < 65536) (hc : d.size ≤ cap) :
    stored.run { src := storedStream d, pos := 3, bitbuf := bb, bitcnt := bc, cap } =
      .ok ((), copyN d.size (s7 d cap)) := by
  have hS := storedStream_size d
  have g3 := get_hdr d 3 (by omega)
  have g4 := get_hdr d 4 (by omega)
  have g5 := get_hdr d 5 (by omega)
  have g6 := get_hdr d 6 (by omega)
  simp only [hdr, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero] at g3 g4 g5 g6
  unfold stored
  rw [run_bind (run_modify _ _), run_bind (run_get _)]
  dsimp only
  rw [ite_f (by rw [hS]; omega)]
  rw [g3, g4, g5, g6]
  simp only [toNat_toUInt8]
  have hl : d.size % 256 % 256 + 256 * (d.size / 256 % 256) = d.size := by omega
  have hnl : (65535 - d.size) % 256 % 256 + 256 * ((65535 - d.size) / 256 % 256) = 65535 - d.size := by omega
  rw [hl, hnl]
  rw [ite_f (by simp; omega)]
  rw [run_bind (run_set _ _)]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine (run_bind (copy_loop _ ?_ _ _ ?_ ?_)).trans ?_
  · intro i s hp hcap
    rw [run_bind (run_get _)]
    try dsimp only
    rw [ite_f (by omega)]
    rw [run_bind (run_set _ _), run_bind (emit_ok { s with pos := s.pos + 1 } _ hcap)]
    rfl
  · simp only [List.length_range', Std.Legacy.Range.size]; rw [hS]; omega
  · simp only [List.length_range', Std.Legacy.Range.size]; show 0 + _ ≤ cap; omega
  · simp only [List.length_range', Std.Legacy.Range.size]
    rw [show (d.size - 0 + 1 - 1) / 1 = d.size by omega]
    rfl

/-- The stored block of `storedStream`, from the block header bit at offset 2. -/
theorem blocks_stored (d : ByteArray) (cap f : Nat) (hn : d.size < 65536) (hc : d.size ≤ cap) :
    (blocks (f + 1)).run { src := storedStream d, pos := 2, cap } =
      .ok ((), copyN d.size (s7 d cap)) := by
  have hS := storedStream_size d
  have g2 : (storedStream d).get! 2 = 0x01 := get_hdr d 2 (by omega)
  have hb1 := bits_byte { src := storedStream d, pos := 2, cap } 1 rfl rfl (by omega) (by omega) (by simp; omega)
  simp only [g2] at hb1
  unfold blocks
  rw [run_bind hb1]
  have hb2 := bits_have { src := storedStream d, pos := 2 + 1, bitbuf := UInt8.toNat 1 / 2 ^ 1, bitcnt := 8 - 1, cap } 2 (by simp)
  rw [run_bind hb2]
  dsimp only
  rw [ite_t (by decide)]
  rw [run_bind (stored_run d cap _ _ hn hc)]
  rw [ite_f (by decide)]
  rfl


/-- The final state's output is the stored data. -/
theorem copyN_s7 (d : ByteArray) (cap : Nat) :
    (copyN d.size (s7 d cap)).out = d ∧ (copyN d.size (s7 d cap)).pos = 7 + d.size ∧
      (copyN d.size (s7 d cap)).src = storedStream d := by
  have hS := storedStream_size d
  obtain ⟨h1, h2, h3, -⟩ := copyN_eq d.size (s7 d cap) (by show 7 + d.size ≤ (storedStream d).size; omega)
  refine ⟨?_, h2, h3⟩
  have hx : ∀ (x y : ByteArray), x.data = y.data → x = y := fun ⟨_⟩ ⟨_⟩ h => by cases h; rfl
  apply hx
  rw [h1]
  show ByteArray.empty.data ++ (storedStream d).data.extract 7 (7 + d.size) = d.data
  rw [storedStream_data]
  apply Array.ext'
  simp only [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop]
  have h7 : (hdr d.size).toList.length = 7 := rfl
  rw [List.append_assoc, List.drop_left' h7,
    show 7 + d.size - 7 = d.data.toList.length by rw [Array.length_toList, ← bsize]; omega,
    List.take_left]
  rfl

/-- **`zlibM` on a stored stream** ends with the data as output. -/
theorem zlibM_stored (d : ByteArray) (cap : Nat) (hn : d.size < 65536) (hc : d.size ≤ cap) :
    ∃ s', zlibM.run { src := storedStream d, cap } = .ok ((), s') ∧ s'.out = d := by
  have hS := storedStream_size d
  have g0 : (storedStream d).get! 0 = 0x78 := get_hdr d 0 (by omega)
  have g1 : (storedStream d).get! 1 = 0x01 := get_hdr d 1 (by omega)
  have h1 := bits_byte { src := storedStream d, cap } 8 rfl rfl (by omega) (by omega) (by simp; omega)
  simp only [g0] at h1
  have h2 := bits_byte { src := storedStream d, pos := 0 + 1, bitbuf := UInt8.toNat 120 / 2 ^ 8, bitcnt := 8 - 8, cap } 8 rfl (by show UInt8.toNat 120 / 2 ^ 8 = 0; decide) (by omega) (by omega) (by simp; omega)
  simp only [g1] at h2
  obtain ⟨ho, hp, hsrc⟩ := copyN_s7 d cap
  refine ⟨{ copyN d.size (s7 d cap) with bitbuf := 0, bitcnt := 0 }, ?_, ho⟩
  unfold zlibM
  rw [run_bind h1, run_bind h2]
  try dsimp only
  rw [ite_f (by decide)]
  rw [run_bind (run_get _)]
  have hb := blocks_stored d cap ((storedStream d).size * 8) hn hc
  refine (run_bind (x := blocks _) (s := { src := storedStream d, pos := 0 + 1 + 1, bitbuf := UInt8.toNat 1 / 2 ^ 8, bitcnt := 8 - 8, cap := cap }) hb).trans ?_
  rw [run_bind (run_modify _ _), run_bind (run_get _)]
  try dsimp only
  rw [hp, hsrc, ho]
  rw [ite_f (by rw [hS]; omega)]
  have t0 := get_trl d 0 (by omega)
  have t1 := get_trl d 1 (by omega)
  have t2 := get_trl d 2 (by omega)
  have t3 := get_trl d 3 (by omega)
  simp only [Nat.add_zero, trl, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero] at t0 t1 t2 t3
  rw [show 7 + d.size + 1 + 1 = 7 + d.size + 2 by omega] at t2
  rw [t0, t1, t2, t3]
  simp only [toNat_toUInt8]
  have hlt := adler32_lt d
  rw [ite_f (by simp; omega)]
  rfl


/-- **Inflate decodes a stored stream.** -/
theorem zlibInflate_stored_raw (cap : Nat) (d : ByteArray) (hn : d.size < 65536) (hc : d.size ≤ cap) :
    zlibInflate cap (zlibStored d) = .ok (some d) := by
  obtain ⟨s', h, ho⟩ := zlibM_stored d cap hn hc
  unfold zlibInflate
  have h' : StateT.run zlibM { src := zlibStored d, cap := cap } = Except.ok ((), s') := h
  rw [h']
  show Except.ok (some s'.out) = _
  rw [ho]

end Silmaril.Proofs.Wasm.Tools.Meta.Inflate

end
