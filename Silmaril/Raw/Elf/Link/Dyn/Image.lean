module

public import Silmaril.Elf.Link.Dyn.Loader.Thms
public import Silmaril.X86.Ext.SymExec

/-! # Reading the loaded image

PROVED (standard axioms): from `ImageOk` (the loader relation's image clause),

* `ImageOk.readPlain`: a byte range of a `PT_LOAD` that no slot covers reads (with the
  segment's read or execute permission) as the file's bytes, checked by the closed Boolean
  `plainOk` (one `decide +kernel` on the file and the position-relative slot table);
* `ImageOk.loadSlot`: an 8-byte slot loads as its value at the given bases (`slotOk`);
* `ImageOk.permits`, `ImageOk.get`: the permissions and contents of one byte.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)

theorem readWith_of_points {mem : Memory} {acc : Access} {l : List Byte} :
    ∀ {a : Nat}, a + l.length ≤ 2 ^ 64 → a < 2 ^ 64 →
    (∀ k (hk : k < l.length), mem.permits acc (a + k) = true ∧ mem.bytes.get? (a + k) = some (l[k]'hk)) →
    mem.readWith acc a l.length = some l := by
  intro a hw ha h
  unfold Memory.readWith
  have hc : mem.checkSpan acc a l.length = true := by
    rw [Memory.checkSpan_iff]
    exact ⟨ha, hw, fun k hk => (h k hk).1⟩
  simp only [hc, ↓reduceIte]
  clear hc hw ha
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have h0 := (h 0 (by simp)).2
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    simp only [List.length_cons, Memory.readBacking, h0]
    rw [ih (a := a + 1) (fun k hk => by
      have := h (k + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)]
    rfl

/-- The address of `v` at base `b`, without wrapping. -/
theorem addr_toNat {b : Word} {v : Nat} (h : b.toNat + v < 2 ^ 64) :
    (b + BitVec.ofNat 64 v).toNat = b.toNat + v := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : v < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h]

/-- The positions of the interpreted slot table are those of the relative one. -/
theorem find_mapM {bases : List Word} {ifn : Word → Option Word} {res : Word} {p : Nat → Bool} :
    ∀ {D : List (Nat × Val)} {T : List (Nat × Option Word)},
    D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) = some T →
    ∀ {s : Nat} {val : Val}, D.find? (fun e => p e.1) = some (s, val) →
      ∃ x, val.word bases ifn res = some x ∧ T.find? (fun e => p e.1) = some (s, x) := by
  intro D
  induction D with
  | nil => intro T _ s val h; cases h
  | cons d D ih =>
    intro T hT s val hf
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hT
    cases e1 : (d.2.word bases ifn res).map fun w => (d.1, w) with
    | none => simp [e1] at hT
    | some y =>
      rw [e1, obind_some] at hT
      cases e2 : D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) with
      | none => simp [e2] at hT
      | some T' =>
        rw [e2, obind_some] at hT
        cases hT
        obtain ⟨w, hw, rfl⟩ : ∃ w, d.2.word bases ifn res = some w ∧ y = (d.1, w) := by
          cases e3 : d.2.word bases ifn res with
          | none => simp [e3] at e1
          | some w => simp [e3] at e1; exact ⟨w, rfl, e1.symm⟩
        rw [List.find?_cons] at hf ⊢
        cases hp : p d.1 with
        | true =>
          simp only [hp] at hf ⊢
          cases hf
          exact ⟨w, hw, rfl⟩
        | false =>
          simp only [hp] at hf ⊢
          exact ih e2 hf

theorem find_mapM_none {bases : List Word} {ifn : Word → Option Word} {res : Word}
    {p : Nat → Bool} :
    ∀ {D : List (Nat × Val)} {T : List (Nat × Option Word)},
    D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) = some T →
    D.find? (fun e => p e.1) = none → T.find? (fun e => p e.1) = none := by
  intro D
  induction D with
  | nil => intro T hT _; simp at hT; cases hT; rfl
  | cons d D ih =>
    intro T hT hf
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hT
    cases e1 : (d.2.word bases ifn res).map fun w => (d.1, w) with
    | none => simp [e1] at hT
    | some y =>
      rw [e1, obind_some] at hT
      cases e2 : D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) with
      | none => simp [e2] at hT
      | some T' =>
        rw [e2, obind_some] at hT
        cases hT
        have hy : y.1 = d.1 := by
          cases e3 : d.2.word bases ifn res with
          | none => simp [e3] at e1
          | some w => simp [e3] at e1; rw [← e1]
        rw [List.find?_cons] at hf ⊢
        cases hp : p d.1 with
        | true => simp [hp] at hf
        | false =>
          simp only [hp] at hf
          simp only [hy, hp]
          exact ih e2 hf

/-- The plain bytes `l` at `v` of segment `ph`: no slot covers them, and the file has them. -/
def plainOk (f : Blob) (ph : Elf.Phdr) (D : List (Nat × Val)) (v : Nat) (l : List Byte) : Bool :=
  (List.range l.length).all fun k =>
    (D.find? fun e => decide (e.1 ≤ v + k ∧ v + k < e.1 + 8)).isNone &&
      imageByte f ph (v + k) == l[k]?

/-- The access a segment's flags allow. -/
def flagAllows (ph : Elf.Phdr) : Access → Bool
  | .read => ph.flags / 4 % 2 == 1
  | .execute => ph.flags % 2 == 1
  | .write => false

theorem ImageOk.readPlain {f : Blob} {b : Word} {i : Elf.DynInfo} {bases : List Word}
    {ifn : Word → Option Word} {res : Word} {D : List (Nat × Val)} {T : List (Nat × Option Word)}
    {mem : Memory} (h : ImageOk ⟨f, b⟩ i T mem)
    (hT : D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) = some T)
    {ph : Elf.Phdr} (hph : ph ∈ i.phs) (hk : ph.kind = 1) {v : Nat} {l : List Byte}
    (hv : ph.vaddr ≤ v) (hend : v + l.length ≤ ph.vaddr + ph.memsz) (hl : 0 < l.length)
    {acc : Access} (hacc : flagAllows ph acc = true) (hok : plainOk f ph D v l = true) :
    mem.readWith acc (b + BitVec.ofNat 64 v).toNat l.length = some l := by
  have hpt := fun k (hk' : k < l.length) => h ph hph hk (v + k) (by omega) (by omega)
  have hw0 := (hpt 0 hl).1
  have hlast := (hpt (l.length - 1) (by omega)).1
  dsimp only at hw0 hlast
  rw [addr_toNat (by omega)]
  refine readWith_of_points (by omega) (by omega) (fun k hk' => ?_)
  obtain ⟨hwrap, hr, hx, _, e, he, -, hb⟩ := hpt k hk'
  dsimp only at hwrap hr hx hb he
  rw [addr_toNat hwrap, ← Nat.add_assoc] at hr hx hb
  have hc := List.all_eq_true.mp hok k (List.mem_range.mpr hk')
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hc
  obtain ⟨hnone, himg⟩ := hc
  have hTn := find_mapM_none (p := fun x => decide (x ≤ v + k ∧ v + k < x + 8)) hT hnone
  unfold expectedByte at he
  rw [hTn] at he
  rw [himg, List.getElem?_eq_getElem hk'] at he
  simp only [Option.map_some, Option.some.injEq] at he
  subst he
  refine ⟨?_, hb _ rfl⟩
  cases acc with
  | read => rw [hr]; simpa [flagAllows] using hacc
  | execute => rw [hx]; simpa [flagAllows] using hacc
  | write => simp [flagAllows] at hacc

/-- The slot at `s` is the entry `(s, val)`, covering its 8 bytes alone. -/
def slotOk (D : List (Nat × Val)) (s : Nat) (val : Val) : Bool :=
  (List.range 8).all fun k => D.find? (fun e => decide (e.1 ≤ s + k ∧ s + k < e.1 + 8)) == some (s, val)

theorem leValue_wordBytes (w : Word) :
    Silmaril.X86.Ext.leValue ((List.range 8).map (wordByte w)) = w.toNat := by
  have hw := w.isLt
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, Silmaril.X86.Ext.leValue, wordByte,
    BitVec.toNat_ofNat]
  omega

theorem ImageOk.loadSlot {f : Blob} {b : Word} {i : Elf.DynInfo} {bases : List Word}
    {ifn : Word → Option Word} {res : Word} {D : List (Nat × Val)} {T : List (Nat × Option Word)}
    {mem : Memory} (h : ImageOk ⟨f, b⟩ i T mem)
    (hT : D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) = some T)
    {ph : Elf.Phdr} (hph : ph ∈ i.phs) (hk : ph.kind = 1) {s : Nat} {val : Val} {w : Word}
    (hv : ph.vaddr ≤ s) (hend : s + 8 ≤ ph.vaddr + ph.memsz) (hr : ph.flags / 4 % 2 = 1)
    (hok : slotOk D s val = true) (hval : val.word bases ifn res = some (some w)) :
    Silmaril.X86.Ext.loadN mem (b + BitVec.ofNat 64 s) 8 = some w := by
  have hpt := fun k (hk' : k < 8) => h ph hph hk (s + k) (by omega) (by omega)
  have hrd : mem.readBytes (b + BitVec.ofNat 64 s).toNat 8 = some ((List.range 8).map (wordByte w)) := by
    have hw0 := (hpt 0 (by omega)).1
    have hw7 := (hpt 7 (by omega)).1
    dsimp only at hw0 hw7
    rw [addr_toNat (by omega)]
    have := readWith_of_points (mem := mem) (acc := .read) (l := (List.range 8).map (wordByte w))
      (a := b.toNat + s) (by simp; omega) (by omega) (fun k hk' => by
        simp only [List.length_map, List.length_range] at hk'
        obtain ⟨hwrap, hrp, _, _, e, he, -, hb⟩ := hpt k hk'
        dsimp only at hwrap hrp hb he
        rw [addr_toNat hwrap, ← Nat.add_assoc] at hrp hb
        have hc := List.all_eq_true.mp hok k (List.mem_range.mpr hk')
        simp only [beq_iff_eq] at hc
        obtain ⟨x, hx, hTf⟩ := find_mapM (p := fun y => decide (y ≤ s + k ∧ s + k < y + 8)) hT hc
        rw [hval] at hx; cases hx
        unfold expectedByte at he
        rw [hTf] at he
        simp only [Option.some.injEq] at he
        subst he
        refine ⟨by rw [hrp]; simpa using hr, ?_⟩
        rw [hb _ rfl]
        simp)
    simpa [Memory.readBytes] using this
  simp only [Silmaril.X86.Ext.loadN, hrd, Option.map_some, leValue_wordBytes, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- One byte's permissions and value (`expectedByte`). -/
theorem ImageOk.point {o : Obj} {i : Elf.DynInfo} {T : List (Nat × Option Word)} {mem : Memory}
    (h : ImageOk o i T mem) {ph : Elf.Phdr} (hph : ph ∈ i.phs) (hk : ph.kind = 1) {v : Nat}
    (hv : ph.vaddr ≤ v) (hend : v < ph.vaddr + ph.memsz) :
    o.base.toNat + v < 2 ^ 64 ∧
    mem.permits .read (o.base.toNat + v) = (ph.flags / 4 % 2 == 1) ∧
    mem.permits .execute (o.base.toNat + v) = (ph.flags % 2 == 1) ∧
    mem.permits .write (o.base.toNat + v) = (ph.flags / 2 % 2 == 1 && !inRelro i v) ∧
    ∃ e, expectedByte o.file T ph v = some e ∧ (mem.bytes.get? (o.base.toNat + v)).isSome ∧
      ∀ x, e = some x → mem.bytes.get? (o.base.toNat + v) = some x := by
  have := h ph hph hk v hv hend
  rw [addr_toNat this.1] at this
  exact this

/-- An 8-byte readable range of the image always loads some word (its bytes are backed). -/
theorem ImageOk.loadSome {f : Blob} {b : Word} {i : Elf.DynInfo} {T : List (Nat × Option Word)}
    {mem : Memory} (h : ImageOk ⟨f, b⟩ i T mem) {ph : Elf.Phdr} (hph : ph ∈ i.phs) (hk : ph.kind = 1)
    {s : Nat} (hv : ph.vaddr ≤ s) (hend : s + 8 ≤ ph.vaddr + ph.memsz) (hr : ph.flags / 4 % 2 = 1) :
    ∃ w, Silmaril.X86.Ext.loadN mem (b + BitVec.ofNat 64 s) 8 = some w := by
  have hpt := fun k (hk' : k < 8) => h ph hph hk (s + k) (by omega) (by omega)
  have hw0 := (hpt 0 (by omega)).1
  have hw7 := (hpt 7 (by omega)).1
  dsimp only at hw0 hw7
  choose bs hbs using fun (k : Fin 8) => Option.isSome_iff_exists.mp (hpt k.1 k.2).2.2.2.2.choose_spec.2.1
  have hrd : mem.readBytes (b + BitVec.ofNat 64 s).toNat 8 = some (List.ofFn bs) := by
    rw [addr_toNat (by omega)]
    have := readWith_of_points (mem := mem) (acc := .read) (l := List.ofFn bs) (a := b.toNat + s)
      (by simp; omega) (by omega) (fun k hk' => by
        simp only [List.length_ofFn] at hk'
        obtain ⟨hwrap, hrp, -⟩ := hpt k hk'
        dsimp only at hwrap hrp
        rw [addr_toNat hwrap, ← Nat.add_assoc] at hrp
        refine ⟨by rw [hrp]; simpa using hr, ?_⟩
        have := hbs ⟨k, hk'⟩
        dsimp only at this
        rw [addr_toNat hwrap, ← Nat.add_assoc] at this
        rw [List.getElem_ofFn]
        exact this)
    simpa [Memory.readBytes] using this
  exact ⟨_, by simp only [Silmaril.X86.Ext.loadN, hrd]; rfl⟩

/-- A writable, non-RELRO range of a segment is readable and writable. -/
theorem ImageOk.permittedRW {o : Obj} {i : Elf.DynInfo} {T : List (Nat × Option Word)} {mem : Memory}
    (h : ImageOk o i T mem) {ph : Elf.Phdr} (hph : ph ∈ i.phs) (hk : ph.kind = 1) {v len : Nat}
    (hv : ph.vaddr ≤ v) (hend : v + len ≤ ph.vaddr + ph.memsz) (hlen : 0 < len)
    (hr : ph.flags / 4 % 2 = 1) (hw : ph.flags / 2 % 2 = 1)
    (hrel : ∀ k < len, inRelro i (v + k) = false) :
    mem.Permitted .read (o.base + BitVec.ofNat 64 v).toNat len ∧
      mem.Permitted .write (o.base + BitVec.ofNat 64 v).toNat len := by
  have hpt := fun k (hk' : k < len) => h ph hph hk (v + k) (by omega) (by omega)
  have hlast := (hpt (len - 1) (by omega)).1
  rw [addr_toNat (by omega)]
  simp only [Memory.Permitted, Memory.checkSpan_iff, Silmaril.Process.addressLimit]
  refine ⟨⟨by omega, by omega, fun k hk' => ?_⟩, ⟨by omega, by omega, fun k hk' => ?_⟩⟩
  · obtain ⟨hwrap, hrp, -⟩ := hpt k hk'
    rw [addr_toNat hwrap, ← Nat.add_assoc] at hrp
    rw [hrp]; simpa using hr
  · obtain ⟨hwrap, -, -, hwp, -⟩ := hpt k hk'
    rw [addr_toNat hwrap, ← Nat.add_assoc] at hwp
    rw [hwp, hrel k hk']; simpa using hw

end Silmaril.Elf.Link.Dyn
