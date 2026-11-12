module

public import Silmaril.Elf.Exe.Defs
public import Silmaril.Elf.Link.Dyn.Image.Thms
public import Silmaril.Elf.Link.Dyn.Elf.Thms

/-! # `ExeLoaded ⊑ RoLoaded` (proofs for `Silmaril.Elf.Exe.Thms`)

The loader relation `Dyn.ExeLoaded` constrains every byte of the executable's `PT_LOAD`s:
a byte no loader write covers holds its file byte, with the segment's permissions
(`ImageOk`). When no write covers a read-only segment (`NoTextRelD`) and the segments are placed
(`ElfBind.Placement`: `p_filesz ≤ p_memsz`, below `2^47`), the read-only segments are therefore
loaded as `ElfBind.RoLoaded` says. -/

@[expose] public section

namespace Silmaril.Elf.Exe

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.ElfBind (isLoad isRo isExec isReadable RoLoaded leBytes phdrsOf)

/-- The headers' program headers are `phdrsOf`. -/
theorem phdrsOf_of_finfo {f : Blob} {i : Elf.DynInfo} (h : finfo f = some i) : phdrsOf f = some i.phs := by
  unfold finfo frun Elf.dynInfo at h
  change ((Elf.phdrs).bind _).run _ = _ at h
  rw [Rd.run_bind] at h
  unfold phdrsOf
  cases hp : Elf.phdrs.run (blobRead f) with
  | none => rw [hp] at h; cases h
  | some phs =>
    rw [hp, Option.bind_some] at h
    change ((Elf.dynEntries phs).bind _).run _ = _ at h
    rw [Rd.run_bind] at h
    cases hd : (Elf.dynEntries phs).run (blobRead f) with
    | none => rw [hd] at h; cases h
    | some d => rw [hd, Option.bind_some] at h; cases h; rfl

/-- `mapM` into pairs keeps a key in the first component. -/
theorem mapM_fst {α β : Type} {g : α → Option (Nat × β)} {key : α → Nat}
    (hg : ∀ x y, g x = some y → y.1 = key x) :
    ∀ {l : List α} {r : List (Nat × β)}, l.mapM g = some r → ∀ e ∈ r, ∃ x ∈ l, e.1 = key x := by
  intro l
  induction l with
  | nil => intro r h e he; simp at h; subst h; cases he
  | cons x xs ih =>
    intro r h e he
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases e1 : g x with
    | none => simp [e1] at h
    | some y =>
      rw [e1, Option.bind_some] at h
      cases e2 : xs.mapM g with
      | none => simp [e2] at h
      | some r' =>
        rw [e2, Option.bind_some] at h
        cases h
        rcases List.mem_cons.1 he with rfl | he'
        · exact ⟨x, List.mem_cons_self, hg x _ e1⟩
        · obtain ⟨z, hz, hk⟩ := ih e2 e he'
          exact ⟨z, List.mem_cons_of_mem _ hz, hk⟩

/-- **The slot table's positions are loader writes** (`slotPositions`). -/
theorem slotsWith_pos {R : Resolver} {lazy : Bool} {f : Blob} {i : Elf.DynInfo} {D : List (Nat × Val)}
    (h : slotsWith R lazy f i = some D) :
    ∃ ps, slotPositions lazy f i = some ps ∧ ∀ e ∈ D, e.1 ∈ ps := by
  unfold slotsWith at h
  unfold slotPositions
  cases hr : frun f (Elf.relas i) with
  | none => rw [hr] at h; cases h
  | some aj =>
    obtain ⟨a, j⟩ := aj
    rw [hr] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨ra, ha, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨rj, hj, h⟩ := h
    have hA := mapM_fst (key := fun r : Elf.Rela => r.off) (fun x y hy => by
      cases e : relocVal R f i x with
      | none => simp [e] at hy
      | some w => simp [e] at hy; rw [← hy]) ha
    have hJ := mapM_fst (key := fun r : Elf.Rela => r.off) (fun x y hy => by
      split at hy
      · split at hy
        · cases e : fileWord f i x.off with
          | none => simp [e] at hy
          | some w => simp [e] at hy; rw [← hy]
        · cases hy
      · cases e : relocVal R f i x with
        | none => simp [e] at hy
        | some w => simp [e] at hy; rw [← hy]) hj
    by_cases hl : lazy = true ∧ j ≠ []
    · simp only [hl, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at h
      dsimp only; simp only [hl, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      cases ht : i.tag 3 with
      | none => rw [ht] at h; cases h
      | some p =>
        rw [ht] at h
        simp only [Option.map_some, Option.bind_some, Option.some.injEq] at h ⊢
        subst h
        refine ⟨_, rfl, fun e he => ?_⟩
        simp only [List.mem_append, List.mem_cons, List.mem_map] at he ⊢
        rcases he with (he | he) | he
        · rcases he with rfl | rfl | he
          · exact Or.inl (Or.inl (Or.inl rfl))
          · exact Or.inl (Or.inl (Or.inr (Or.inl rfl)))
          · cases he
        · obtain ⟨x, hx, hk⟩ := hA e he; exact Or.inl (Or.inr ⟨x, hx, hk.symm⟩)
        · obtain ⟨x, hx, hk⟩ := hJ e he; exact Or.inr ⟨x, hx, hk.symm⟩
    · have hl' : ¬ (lazy = true ∧ j ≠ []) := hl
      simp only [hl', ↓reduceIte] at h
      dsimp only; simp only [hl', ↓reduceIte]
      simp only [Option.some.injEq, Option.map_some] at h ⊢
      subst h
      refine ⟨_, rfl, fun e he => ?_⟩
      simp only [List.mem_append, List.nil_append, List.mem_map] at he ⊢
      rcases he with he | he
      · obtain ⟨x, hx, hk⟩ := hA e he; exact Or.inl ⟨x, hx, hk.symm⟩
      · obtain ⟨x, hx, hk⟩ := hJ e he; exact Or.inr ⟨x, hx, hk.symm⟩

/-- The check gives `NoTextRelD`. -/
theorem noTextRelD_of_check {f : Blob} {lazy : Bool} (h : noTextRel f lazy = true) : NoTextRelD f lazy := by
  intro i hi ps hps p hp
  unfold noTextRel at h
  simp only [hi, hps] at h
  exact List.all_eq_true.1 h p hp

/-- Byte `k < w` of a `w`-byte read is the one-byte read at `o + k`. -/
theorem shift_byte (N o w k : Nat) (hk : k < w) :
    BitVec.ofNat 8 (((N >>> (8 * o)) % 2 ^ (8 * w)) >>> (8 * k)) =
      BitVec.ofNat 8 ((N >>> (8 * (o + k))) % 2 ^ (8 * 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hw : 2 ^ (8 * w) = 2 ^ (8 * k) * 2 ^ (8 * (w - k)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hw, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 8 * o + 8 * k = 8 * (o + k) by omega, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    show 8 * 1 = 8 by rfl, Nat.mod_mod]

/-- **`ImageOk` with no slot on a read-only segment gives `RoLoaded`.** -/
theorem roLoaded_of_imageOk {f : Blob} {b : Word} {i : Elf.DynInfo} {T : List (Nat × Option Word)}
    {mem : Memory} (h : ImageOk ⟨f, b⟩ i T mem) (hi : finfo f = some i)
    (hp : Silmaril.Elf.Link.ElfBind.Placement f b) (hT : ∀ e ∈ T, avoidsRo i.phs e.1 = true) :
    RoLoaded f b mem := by
  intro phs hphs ph hph hl hro o w n ho hw hn
  have hph0 := phdrsOf_of_finfo hi
  rw [hph0, Option.some.injEq] at hphs
  subst hphs
  obtain ⟨t, phs', -, hphs', -, hsz⟩ := hp
  rw [hph0, Option.some.injEq] at hphs'
  subst hphs'
  obtain ⟨hfm, htop⟩ := hsz ph hph hl
  have hk1 : ph.kind = 1 := by simpa [isLoad] using hl
  -- every byte of the range
  have hpt : ∀ k, k < w → mem.permits .read (b.toNat + ph.vaddr + (o - ph.off) + k) = (ph.flags / 4 % 2 == 1) ∧
      mem.permits .execute (b.toNat + ph.vaddr + (o - ph.off) + k) = (ph.flags % 2 == 1) ∧
      mem.bytes.get? (b.toNat + ph.vaddr + (o - ph.off) + k) = some ((leBytes n w)[k]?.getD 0) := by
    intro k hk
    obtain ⟨-, hr, hx, -, e, he, -, hget⟩ := ImageOk.point h hph hk1 (v := ph.vaddr + (o - ph.off) + k)
      (by omega) (by omega)
    dsimp only at hr hx hget he
    have eA : b.toNat + (ph.vaddr + (o - ph.off) + k) = b.toNat + ph.vaddr + (o - ph.off) + k := by omega
    rw [eA] at hr hx hget
    have hnone : T.find? (fun e => decide (e.1 ≤ ph.vaddr + (o - ph.off) + k ∧
        ph.vaddr + (o - ph.off) + k < e.1 + 8)) = none := by
      rw [List.find?_eq_none]
      intro e' he' hc
      simp only [decide_eq_true_eq] at hc
      have ha := List.all_eq_true.1 (hT e' he') ph hph
      simp only [hl, hro, Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at ha
      omega
    unfold expectedByte at he
    rw [hnone] at he
    unfold imageByte at he
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))] at he
    have hlen : o + w ≤ f.len := by
      unfold blobRead Blob.readLEN at hn
      split at hn
      · rename_i hc
        rcases hc with hc | hc
        · omega
        · exact hc
      · cases hn
    have hb1 : frun f (Elf.u8 (ph.vaddr + (o - ph.off) + k - ph.vaddr + ph.off)) =
        some ((f.n >>> (8 * (o + k))) % 2 ^ (8 * 1)) := by
      have hr1 : blobRead f (ph.vaddr + (o - ph.off) + k - ph.vaddr + ph.off) 1 =
          some ((f.n >>> (8 * (o + k))) % 2 ^ (8 * 1)) := by
        unfold blobRead Blob.readLEN
        rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (by omega))), show ph.vaddr + (o - ph.off) + k - ph.vaddr + ph.off = o + k by omega]
      show Rd.run _ (Rd.read _ 1 Rd.pure) = _
      rw [Rd.run_read_some _ hr1]
      rfl
    rw [hb1] at he
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    refine ⟨hr, hx, ?_⟩
    rw [hget _ rfl]
    congr 1
    have hn' : n = (f.n >>> (8 * o)) % 2 ^ (8 * w) := by
      unfold blobRead Blob.readLEN at hn
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (by omega)))] at hn
      exact (Option.some.inj hn).symm
    subst hn'
    simp only [leBytes, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
    exact (shift_byte f.n o w k hk).symm
  have hbase : b.toNat + ph.vaddr + (o - ph.off) + w ≤ 2 ^ 47 := by omega
  have hread : ∀ acc : Silmaril.Process.Access,
      (∀ k, k < w → mem.permits acc (b.toNat + ph.vaddr + (o - ph.off) + k) = true) →
      mem.readWith acc (b.toNat + ph.vaddr + (o - ph.off)) w = some (leBytes n w) := by
    intro acc hacc
    have hlenw : (leBytes n w).length = w := by simp [leBytes]
    have := readWith_of_points (mem := mem) (acc := acc) (l := leBytes n w)
      (a := b.toNat + ph.vaddr + (o - ph.off)) (by rw [hlenw]; omega) (by omega) (fun k hk => by
        rw [hlenw] at hk
        refine ⟨hacc k hk, ?_⟩
        rw [(hpt k hk).2.2, List.getElem?_eq_getElem (by rw [hlenw]; exact hk), Option.getD_some])
    rw [hlenw] at this
    exact this
  refine ⟨fun hrd => hread .read fun k hk => ?_, fun hex => hread .execute fun k hk => ?_⟩
  · rw [(hpt k hk).1]; simpa [isReadable] using hrd
  · rw [(hpt k hk).2.1]; simpa [isExec] using hex

/-- **`ExeLoaded ⊑ RoLoaded`**: in memory where the loader relation holds for the executable
`F` (the head of the scope, at base `b`), the read-only segments of `F` are loaded at `b`, when
no loader write touches them (`NoTextRelD`) and `F` is placed at `b`. -/
theorem roLoaded_of_exeLoaded {F : Blob} {fs : List Blob} {b : Word} {bs : List Word}
    {ifn : Word → Option Word} {lazy : Bool} {res : Word} {mem : Memory}
    (hp : Silmaril.Elf.Link.ElfBind.Placement F b) (hn : NoTextRelD F lazy)
    (h : ExeLoaded (F :: fs) (b :: bs) ifn lazy res mem) : RoLoaded F b mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  obtain ⟨ps, hps, hDp⟩ := slotsWith_pos hD
  refine roLoaded_of_imageOk himg hi hp fun e he => ?_
  obtain ⟨d, hd, hk⟩ := mapM_fst (key := fun d : Nat × Val => d.1) (fun x y hy => by
    cases e : x.2.word (b :: bs) ifn res with
    | none => simp [e] at hy
    | some w => simp [e] at hy; rw [← hy]) hT e he
  rw [hk]
  exact hn i hi ps hps d.1 (hDp d hd)

end Silmaril.Elf.Exe
