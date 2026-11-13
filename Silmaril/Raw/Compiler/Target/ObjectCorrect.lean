module

public import Silmaril.Semantics.CPort.Formats.ELF.Write.Defs
public import Silmaril.Semantics.CPort.Formats.ELF.ObjectRecordCertificates.Defs
public import Silmaril.Semantics.CPort.Formats.ELF.ObjectCertificates.Defs
public meta import Mathlib.Data.List.Forall2
public import Silmaril.Compiler.Target.Backends.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # The ELF writer round trip

`Formats.ELF.Object.readObject` reads back what `Formats.ELF.Write.writeRelocatable`
writes: the null section, one section per written section (its name, flags, alignment
and bytes), the `.note.GNU-stack`, `.symtab`, `.strtab` and `.shstrtab` sections, the
null symbol and one global symbol per written symbol (its name, kind, section, value
and size), and no relocation.

The writer is imperative (`for` and `while` loops over `ByteArray`); its bytes are
first rewritten into a list model (`le_toList`, `pad_toList`, `strtab_eq`), then each
reader of the profile is run on the model. The reader works on `Array (BitVec 8)`; the
writer's bytes are converted with `toBits`.
-/

@[expose] public section

namespace Silmaril.Compile.Target.ObjectCorrect

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Write

/-! ## The bytes of the writer's primitives -/

/-- `n` little-endian bytes of `v`. -/
def leL : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => (v % 256).toUInt8 :: leL n (v / 256)

@[simp] theorem leL_length (n v : Nat) : (leL n v).length = n := by
  induction n generalizing v <;> simp_all [leL]

theorem foldl_push_toList {α : Type} (l : List α) (f : α → UInt8) (b : ByteArray) :
    (l.foldl (fun b a => b.push (f a)) b).data.toList = b.data.toList ++ l.map f := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, ByteArray.data_push]

theorem leL_eq_map (n v : Nat) :
    leL n v = (List.range n).map (fun i => ((v >>> (8 * i)) % 256).toUInt8) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [leL, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.shiftRight_zero, List.cons.injEq,
      true_and]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
    congr 3
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem le_toList (n v : Nat) : (le n v).data.toList = leL n v := by
  simp only [le, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    bind_pure, Id.run_pure]
  rw [foldl_push_toList, leL_eq_map]
  simp [Std.Legacy.Range.size, List.range_eq_range', ByteArray.emptyWithCapacity]
  rfl

/-- The number of zero bytes `pad` adds to `size` bytes for alignment `a`. -/
def padN (size a : Nat) : Nat := if a > 1 then (a - size % a) % a else 0

theorem loop_unfold {β : Type} (b : β) (f : Unit → β → Id (ForInStep β)) :
    (forIn Lean.Loop.mk b f : Id β) = (match f () b with
      | .done v => pure v
      | .yield v => forIn Lean.Loop.mk v f) := by
  show Lean.Loop.forIn _ _ _ = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

theorem pad_go (align : Nat) (h : align > 1) (f : Unit → ByteArray → Id (ForInStep ByteArray))
    (hf : ∀ b, f () b = if b.size % align = 0 then pure (.done b) else pure (.yield (b.push 0))) :
    ∀ k (b : ByteArray), (align - b.size % align) % align = k →
    (Id.run (forIn Lean.Loop.mk b f)).data.toList = b.data.toList ++ List.replicate k 0 := by
  intro k
  induction k with
  | zero =>
    intro b hk
    rw [loop_unfold, hf]
    have : b.size % align = 0 := by
      have := Nat.mod_lt b.size (by omega : align > 0)
      rcases Nat.eq_zero_or_pos (b.size % align) with h0 | h0
      · exact h0
      · rw [Nat.mod_eq_of_lt (by omega)] at hk; omega
    rw [ite_eq_left this]; simp; rfl
  | succ k ih =>
    intro b hk
    rw [loop_unfold, hf]
    have hlt := Nat.mod_lt b.size (by omega : align > 0)
    have hne : b.size % align ≠ 0 := by
      intro h0; simp [h0] at hk
    have hk' : (align - (b.push 0).size % align) % align = k := by
      rw [Nat.mod_eq_of_lt (by omega)] at hk
      simp only [ByteArray.size_push]
      rw [Nat.add_mod, Nat.mod_eq_of_lt (a := 1) (by omega)]
      by_cases hc : b.size % align + 1 = align
      · rw [hc, Nat.mod_self, Nat.sub_zero, Nat.mod_self]; omega
      · have e1 : (b.size % align + 1) % align = b.size % align + 1 := Nat.mod_eq_of_lt (by omega)
        rw [e1]
        have e2 : (align - (b.size % align + 1)) % align = align - (b.size % align + 1) :=
          Nat.mod_eq_of_lt (by omega)
        rw [e2]; omega
    rw [ite_eq_right hne]
    show (Id.run (forIn Lean.Loop.mk (b.push 0) f)).data.toList = _
    rw [ih _ hk']
    simp [ByteArray.data_push]
    rfl

theorem pad_toList (b : ByteArray) (a : Nat) :
    (pad b a).data.toList = b.data.toList ++ List.replicate (padN b.size a) 0 := by
  unfold pad padN
  split
  · rename_i h
    simp only [bind_pure]
    exact pad_go a h _ (fun b => by by_cases h0 : b.size % a = 0 <;> simp [h0]) _ _ rfl
  · simp

theorem pad_size (b : ByteArray) (a : Nat) : (pad b a).size = b.size + padN b.size a := by
  have := congrArg List.length (pad_toList b a)
  simp only [List.length_append, List.length_replicate, Array.length_toList] at this
  exact this

/-- The bytes of a name and its terminator. -/
def nameL (n : String) : List UInt8 := n.toUTF8.data.toList ++ [0]

/-- The offsets of the names in a string table whose next free byte is `c`. -/
def strOffs : Nat → List String → List Nat
  | _, [] => []
  | c, n :: ns => c :: strOffs (c + (nameL n).length) ns

theorem strtab_foldl (names : List String) (b : ByteArray) (offs : Array Nat) :
    let r := names.foldl (fun (st : ByteArray × Array Nat) n =>
      (st.1 ++ n.toUTF8 ++ ByteArray.mk #[0], st.2.push st.1.size)) (b, offs)
    r.1.data.toList = b.data.toList ++ names.flatMap nameL ∧
      r.2.toList = offs.toList ++ strOffs b.size names := by
  induction names generalizing b offs with
  | nil => simp [strOffs]
  | cons n ns ih =>
    obtain ⟨h1, h2⟩ := ih (b ++ n.toUTF8 ++ ByteArray.mk #[0]) (offs.push b.size)
    simp only [List.foldl_cons] at h1 h2 ⊢
    refine ⟨?_, ?_⟩
    · rw [h1]; simp [ByteArray.data_append, nameL]
    · rw [h2]
      conv_rhs => rw [strOffs]
      have : (b ++ n.toUTF8 ++ ByteArray.mk #[0]).size = b.size + (nameL n).length := by
        simp only [ByteArray.size_append, nameL, List.length_append, Array.length_toList]
        rfl
      rw [this]; simp

theorem strtab_eq (names : List String) :
    (strtab names).1.data.toList = 0 :: names.flatMap nameL ∧
      (strtab names).2 = strOffs 1 names := by
  obtain ⟨h1, h2⟩ := strtab_foldl names (ByteArray.mk #[0]) #[]
  simp only [strtab, List.forIn_pure_yield_eq_foldl]
  have e : (ByteArray.mk #[0]).size = 1 := rfl
  rw [e] at h2
  exact ⟨by simpa using h1, by simpa using h2⟩

/-! ## Reading little-endian fields -/

/-- The reader's bytes of the writer's bytes. -/
def toBits (b : ByteArray) : Bytes := b.data.map UInt8.toBitVec

/-- The reader's bytes of a list of writer bytes. -/
abbrev bits (l : List UInt8) : List (BitVec 8) := l.map UInt8.toBitVec

theorem readLE_drop (L : List (BitVec 8)) (off w : Nat) :
    readLE ⟨L⟩ off w = readLE ⟨L.drop off⟩ 0 w :=
  readLE_congr _ _ _ _ _ fun i _ => by simp [List.getElem?_drop]

theorem readLE_cons (a : BitVec 8) (L : List (BitVec 8)) (off w : Nat) :
    readLE ⟨a :: L⟩ (off + 1) w = readLE ⟨L⟩ off w :=
  readLE_congr _ _ _ _ _ fun i _ => by
    simp only [List.getElem?_cons_succ, Nat.add_right_comm off 1 i]

theorem readLE_leL (w v : Nat) (post : List (BitVec 8)) :
    readLE ⟨bits (leL w v) ++ post⟩ 0 w = some (v % 2 ^ (8 * w)) := by
  induction w generalizing v with
  | zero => simp [readLE, Nat.mod_one]
  | succ w ih =>
    simp only [readLE, leL, List.map_cons, List.cons_append]
    rw [show (1 : Nat) = 0 + 1 from rfl, readLE_cons, ih]
    simp only [List.getElem?_cons_zero, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq]
    rw [show 2 ^ (8 * (w + 1)) = 256 * 2 ^ (8 * w) by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm], Nat.mod_mul]
    simp

theorem readLE_of_drop {L post : List (BitVec 8)} {off w v : Nat}
    (h : L.drop off = bits (leL w v) ++ post) : readLE ⟨L⟩ off w = some (v % 2 ^ (8 * w)) := by
  rw [readLE_drop, h, readLE_leL]

theorem drop_append_ge {α : Type} {l₁ l₂ : List α} {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).drop i = l₂.drop (i - l₁.length) := by
  simp [List.drop_append, List.drop_eq_nil_of_le h]

theorem readLE_of_take {L : List (BitVec 8)} {off w v : Nat}
    (h : (L.drop off).take w = bits (leL w v)) : readLE ⟨L⟩ off w = some (v % 2 ^ (8 * w)) := by
  rw [readLE_drop, ← List.take_append_drop w (L.drop off), h, readLE_leL]

/-! ## Records -/

/-- The bytes of one section header. -/
def shdrL (name type flags addr offset size link info align entsize : Nat) : List UInt8 :=
  leL 4 name ++ leL 4 type ++ leL 8 flags ++ leL 8 addr ++ leL 8 offset ++ leL 8 size ++
    leL 4 link ++ leL 4 info ++ leL 8 align ++ leL 8 entsize

theorem shdr_toList (name type flags addr offset size link info align entsize : Nat) :
    (shdr name type flags addr offset size link info align entsize).data.toList =
      shdrL name type flags addr offset size link info align entsize := by
  simp [shdr, shdrL, ByteArray.data_append, le_toList]

@[simp] theorem shdrL_length (name type flags addr offset size link info align entsize : Nat) :
    (shdrL name type flags addr offset size link info align entsize).length = 64 := by
  simp [shdrL]

theorem readSectionHeader_of_drop {L post : List (BitVec 8)} {off : Nat}
    {name type flags addr offset size link info align entsize : Nat}
    (h : L.drop off = bits (shdrL name type flags addr offset size link info align entsize) ++ post) :
    readSectionHeader ⟨L⟩ off = some ⟨name % 2 ^ 32, type % 2 ^ 32, flags % 2 ^ 64,
      addr % 2 ^ 64, offset % 2 ^ 64, size % 2 ^ 64, link % 2 ^ 32, info % 2 ^ 32,
      align % 2 ^ 64, entsize % 2 ^ 64⟩ := by
  have d : ∀ k, L.drop (off + k) = (L.drop off).drop k := fun k => by rw [List.drop_drop]
  simp only [readSectionHeader]
  rw [readLE_of_take (w := 4) (v := name) (by rw [h]; simp [shdrL]),
    readLE_of_take (w := 4) (v := type) (by rw [d, h]; simp [shdrL]),
    readLE_of_take (w := 8) (v := flags) (by rw [d, h]; simp [shdrL, drop_append_ge]),
    readLE_of_take (w := 8) (v := addr) (by rw [d, h]; simp [shdrL, drop_append_ge]),
    readLE_of_take (w := 8) (v := offset) (by rw [d, h]; simp [shdrL, drop_append_ge]),
    readLE_of_take (w := 8) (v := size) (by rw [d, h]; simp [shdrL, drop_append_ge]),
    readLE_of_take (w := 4) (v := link) (by rw [d, h]; simp [shdrL, drop_append_ge]),
    readLE_of_take (w := 4) (v := info) (by rw [d, h]; simp [shdrL, drop_append_ge]),
    readLE_of_take (w := 8) (v := align) (by rw [d, h]; simp [shdrL, drop_append_ge]),
    readLE_of_take (w := 8) (v := entsize) (by rw [d, h]; simp [shdrL, drop_append_ge])]
  rfl

/-- The bytes of one symbol. -/
def symL (name info other shndx value size : Nat) : List UInt8 :=
  leL 4 name ++ leL 1 info ++ leL 1 other ++ leL 2 shndx ++ leL 8 value ++ leL 8 size

@[simp] theorem symL_length (name info other shndx value size : Nat) :
    (symL name info other shndx value size).length = 24 := by
  simp [symL]

theorem symL_zero : symL 0 0 0 0 0 0 = List.replicate 24 0 := by decide

theorem readSymbol_of_drop {L post : List (BitVec 8)} {off : Nat}
    {name info other shndx value size : Nat}
    (h : L.drop off = bits (symL name info other shndx value size) ++ post) :
    readSymbol ⟨L⟩ off = some ⟨name % 2 ^ 32, info % 2 ^ 8, other % 2 ^ 8, shndx % 2 ^ 16,
      value % 2 ^ 64, size % 2 ^ 64⟩ := by
  have d : ∀ k, L.drop (off + k) = (L.drop off).drop k := fun k => by rw [List.drop_drop]
  simp only [readSymbol]
  rw [readLE_of_take (w := 4) (v := name) (by rw [h]; simp [symL]),
    readLE_of_take (w := 1) (v := info) (by
      rw [d, h]; simp [symL]),
    readLE_of_take (w := 1) (v := other) (by
      rw [d, h]; simp [symL, drop_append_ge]),
    readLE_of_take (w := 2) (v := shndx) (by
      rw [d, h]; simp [symL, drop_append_ge]),
    readLE_of_take (w := 8) (v := value) (by
      rw [d, h]; simp [symL, drop_append_ge]),
    readLE_of_take (w := 8) (v := size) (by
      rw [d, h]; simp [symL, drop_append_ge])]
  rfl

/-- The bytes of the ELF header the writer emits. -/
def ehdrL (machine shoff flags count shstrIdx : Nat) : List UInt8 :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ leL 2 1 ++ leL 2 machine ++ leL 4 1 ++ leL 8 0 ++ leL 8 0 ++ leL 8 shoff ++ leL 4 flags ++
    leL 2 64 ++ leL 2 0 ++ leL 2 0 ++ leL 2 64 ++ leL 2 count ++ leL 2 shstrIdx

@[simp] theorem ehdrL_length (machine shoff flags count shstrIdx : Nat) :
    (ehdrL machine shoff flags count shstrIdx).length = 64 := by
  simp [ehdrL]

theorem readHeader_of_take {L : List (BitVec 8)} {machine shoff flags count shstrIdx : Nat}
    (size : 64 ≤ L.length) (h : L.take 64 = bits (ehdrL machine shoff flags count shstrIdx)) :
    readHeader ⟨L⟩ = some ⟨0, 0, 1, machine % 2 ^ 16, 1, 0, 0, shoff % 2 ^ 64, flags % 2 ^ 32,
      64, 0, 0, 64, count % 2 ^ 16, shstrIdx % 2 ^ 16⟩ := by
  have e : L = bits (ehdrL machine shoff flags count shstrIdx) ++ L.drop 64 := by
    rw [← h, List.take_append_drop]
  generalize L.drop 64 = rest at e
  subst e
  have ident : ([0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8) =
      leL 4 0x464c457f ++ leL 1 2 ++ leL 1 1 ++ leL 1 1 ++ leL 1 0 ++ leL 1 0 ++
        List.replicate 7 0 := by decide
  simp only [ehdrL, ident] at size ⊢
  simp only [readHeader]
  rw [readLE_of_take (off := 0) (w := 4) (v := 0x464c457f) (by simp ),
    readLE_of_take (off := 4) (w := 1) (v := 2) (by simp ),
    readLE_of_take (off := 5) (w := 1) (v := 1) (by simp [drop_append_ge]),
    readLE_of_take (off := 6) (w := 1) (v := 1) (by simp [drop_append_ge]),
    readLE_of_take (off := 7) (w := 1) (v := 0) (by simp [drop_append_ge]),
    readLE_of_take (off := 8) (w := 1) (v := 0) (by simp [drop_append_ge]),
    readLE_of_take (off := 16) (w := 2) (v := 1) (by simp [drop_append_ge]),
    readLE_of_take (off := 18) (w := 2) (v := machine) (by simp [drop_append_ge]),
    readLE_of_take (off := 20) (w := 4) (v := 1) (by simp [drop_append_ge]),
    readLE_of_take (off := 24) (w := 8) (v := 0) (by simp [drop_append_ge]),
    readLE_of_take (off := 32) (w := 8) (v := 0) (by simp [drop_append_ge]),
    readLE_of_take (off := 40) (w := 8) (v := shoff) (by simp [drop_append_ge]),
    readLE_of_take (off := 48) (w := 4) (v := flags) (by simp [drop_append_ge]),
    readLE_of_take (off := 52) (w := 2) (v := 64) (by simp [drop_append_ge]),
    readLE_of_take (off := 54) (w := 2) (v := 0) (by simp [drop_append_ge]),
    readLE_of_take (off := 56) (w := 2) (v := 0) (by simp [drop_append_ge]),
    readLE_of_take (off := 58) (w := 2) (v := 64) (by simp [drop_append_ge]),
    readLE_of_take (off := 60) (w := 2) (v := count) (by simp [drop_append_ge]),
    readLE_of_take (off := 62) (w := 2) (v := shstrIdx) (by simp [drop_append_ge])]
  simp at size
  simp [size]

/-! ## The layout of the object -/

/-- The section contents from file offset `c`: each section padded to its alignment. -/
def secBytes : Nat → List Section → List UInt8
  | _, [] => []
  | c, s :: ss => List.replicate (padN c (max s.align 1)) 0 ++ s.data.data.toList ++
      secBytes (c + padN c (max s.align 1) + s.data.size) ss

/-- The file offset of each section's contents, from file offset `c`. -/
def secOffs : Nat → List Section → List Nat
  | _, [] => []
  | c, s :: ss => (c + padN c (max s.align 1)) ::
      secOffs (c + padN c (max s.align 1) + s.data.size) ss

theorem secFold (S : List Section) (out : ByteArray) (offs : Array Nat) :
    let r := S.foldl (fun (b : ByteArray × Array Nat) (a : Section) =>
      (pad b.1 (max a.align 1) ++ a.data, b.2.push (pad b.1 (max a.align 1)).size)) (out, offs)
    r.1.data.toList = out.data.toList ++ secBytes out.size S ∧
      r.2.toList = offs.toList ++ secOffs out.size S := by
  induction S generalizing out offs with
  | nil => simp [secBytes, secOffs]
  | cons s S ih =>
    obtain ⟨h1, h2⟩ := ih (pad out (max s.align 1) ++ s.data)
      (offs.push (pad out (max s.align 1)).size)
    simp only [List.foldl_cons] at h1 h2 ⊢
    have hs : (pad out (max s.align 1) ++ s.data).size =
        out.size + padN out.size (max s.align 1) + s.data.size := by
      rw [ByteArray.size_append, pad_size]
    rw [hs] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [h1, ByteArray.data_append, Array.toList_append, pad_toList, secBytes]
      simp
    · rw [h2, secOffs, pad_size]
      simp

/-- `e_shndx` of a written symbol. -/
def shndx (s : Sym) : Nat :=
  match s.sec with
  | some i => i + 1
  | none => 65521

/-- The bytes of a written symbol whose name is at `nameOff`. -/
def symRec (a : Sym × Nat) : List UInt8 :=
  symL a.2 (16 + a.1.kind) 0 (shndx a.1) a.1.value a.1.size

theorem symFold (Z : List (Sym × Nat)) (out : ByteArray) (F : ByteArray → Sym × Nat → ByteArray)
    (hF : ∀ b a, (F b a).data.toList = b.data.toList ++ symRec a) :
    (Z.foldl F out).data.toList = out.data.toList ++ (Z.map symRec).flatten := by
  induction Z generalizing out with
  | nil => simp
  | cons a Z ih => simp [ih, hF]

/-- The section header of the written section `a.1.1`, at `a.1.2`, with index `a.2`. -/
def shdrRec (shoffs : List Nat) (a : (Section × Nat) × Nat) : List UInt8 :=
  shdrL shoffs[a.2]! 1 a.1.1.flags 0 a.1.2 a.1.1.data.size 0 0 (max a.1.1.align 1) 0

theorem shdrFold (shoffs : List Nat) (W : List ((Section × Nat) × Nat)) (out : ByteArray) :
    (W.foldl (fun (b : ByteArray) (a : (Section × Nat) × Nat) =>
      b ++ shdr shoffs[a.2]! 1 a.1.1.flags 0 a.1.2 a.1.1.data.size 0 0 (max a.1.1.align 1) 0)
      out).data.toList = out.data.toList ++ (W.map (shdrRec shoffs)).flatten := by
  induction W generalizing out with
  | nil => simp
  | cons a W ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.flatten_cons]
    simp [ByteArray.data_append, shdr_toList, shdrRec]

/-- The section names, in section-header order from section 1. -/
def shNames (S : List Section) : List String :=
  S.map (·.name) ++ [".note.GNU-stack", ".symtab", ".strtab", ".shstrtab"]

/-- The section-name string table. -/
def shstrL (S : List Section) : List UInt8 := 0 :: (shNames S).flatMap nameL

/-- The symbol string table. -/
def strL (Y : List Sym) : List UInt8 := 0 :: (Y.map (·.name)).flatMap nameL

/-- The offset of each section name in `shstrL`. -/
def shoffs (S : List Section) : List Nat := strOffs 1 (shNames S)

/-- The offset of each symbol name in `strL`. -/
def soffs (Y : List Sym) : List Nat := strOffs 1 (Y.map (·.name))

/-- The file offset of `.note.GNU-stack` (empty): the end of the section contents. -/
def noteOff (S : List Section) : Nat := 64 + (secBytes 64 S).length

/-- The file offset of `.symtab`. -/
def symOff (S : List Section) : Nat := noteOff S + padN (noteOff S) 8

/-- The file offset of `.strtab`. -/
def strOff (S : List Section) (Y : List Sym) : Nat := symOff S + 24 * (Y.length + 1)

/-- The file offset of `.shstrtab`. -/
def shstrOff (S : List Section) (Y : List Sym) : Nat := strOff S Y + (strL Y).length

/-- The file offset of the section header table. -/
def shOff (S : List Section) (Y : List Sym) : Nat :=
  shstrOff S Y + (shstrL S).length + padN (shstrOff S Y + (shstrL S).length) 8

/-- The section headers of `.note.GNU-stack`, `.symtab`, `.strtab` and `.shstrtab`. -/
def tailShdrs (S : List Section) (Y : List Sym) : List UInt8 :=
  shdrL (shoffs S)[S.length]! 1 0 0 (noteOff S) 0 0 0 1 0 ++
    shdrL (shoffs S)[S.length + 1]! 2 0 0 (symOff S) (24 * (Y.length + 1)) (S.length + 3) 1 8 24 ++
    shdrL (shoffs S)[S.length + 2]! 3 0 0 (strOff S Y) (strL Y).length 0 0 1 0 ++
    shdrL (shoffs S)[S.length + 3]! 3 0 0 (shstrOff S Y) (shstrL S).length 0 0 1 0

/-- **The bytes `writeRelocatable` writes**, as a list. -/
def model (machine flags : Nat) (S : List Section) (Y : List Sym) : List UInt8 :=
  ehdrL machine (shOff S Y) flags (S.length + 5) (S.length + 4) ++
    secBytes 64 S ++ List.replicate (padN (noteOff S) 8) 0 ++ List.replicate 24 0 ++
    ((Y.zip (soffs Y)).map symRec).flatten ++ strL Y ++ shstrL S ++
    List.replicate (padN (shstrOff S Y + (shstrL S).length) 8) 0 ++ List.replicate 64 0 ++
    (((S.zip (secOffs 64 S)).zipIdx).map (shdrRec (shoffs S))).flatten ++ tailShdrs S Y

theorem size_eq (b : ByteArray) : b.size = b.data.toList.length := by
  simp only [ByteArray.size, Array.length_toList]

theorem extract_toList (b : ByteArray) (n : Nat) :
    (b.extract n b.size).data.toList = b.data.toList.drop n := by
  rw [ByteArray.data_extract, Array.toList_extract, size_eq, List.extract_eq_take_drop,
    List.take_of_length_le (by simp)]

theorem strOffs_length (c : Nat) (ns : List String) : (strOffs c ns).length = ns.length := by
  induction ns generalizing c <;> simp_all [strOffs]

theorem symRecs_length (Y : List Sym) :
    ((Y.zip (soffs Y)).map symRec).flatten.length = 24 * Y.length := by
  have : ∀ (Z : List (Sym × Nat)), (Z.map symRec).flatten.length = 24 * Z.length := by
    intro Z; induction Z <;> simp_all [symRec]; omega
  rw [this, List.length_zip, soffs, strOffs_length]; simp

theorem writeRelocatable_toList (machine flags : Nat) (S : List Section) (Y : List Sym) :
    (writeRelocatable machine flags S Y).data.toList = model machine flags S Y := by
  have hsh := strtab_eq (shNames S)
  have hst := strtab_eq (Y.map (·.name))
  unfold writeRelocatable
  simp only [shNames] at hsh
  generalize strtab (List.map (fun x => x.name) S ++
    [".note.GNU-stack", ".symtab", ".strtab", ".shstrtab"]) = st1 at hsh
  generalize strtab (List.map (fun x => x.name) Y) = st2 at hst
  rcases st1 with ⟨shstr, shoffs'⟩
  rcases st2 with ⟨str, soffs'⟩
  obtain ⟨hsh1, hsh2⟩ := hsh
  obtain ⟨hst1, hst2⟩ := hst
  simp only at hsh1 hsh2 hst1 hst2
  subst hsh2 hst2
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  obtain ⟨hA1, hA2⟩ := secFold S ⟨Array.replicate 64 0⟩ #[]
  generalize List.foldl (fun (b : ByteArray × Array Nat) (a : Section) =>
      (pad b.1 (max a.align 1) ++ a.data, b.2.push (pad b.1 (max a.align 1)).size))
      (⟨Array.replicate 64 0⟩, #[]) S = A at hA1 hA2 ⊢
  simp only [size_eq, Array.toList_replicate, List.length_replicate,
    List.nil_append] at hA1 hA2
  simp only [ByteArray.data_append, Array.toList_append, extract_toList, shdrFold]
  generalize hB : List.foldl _ (pad A.1 8 ++ ⟨Array.replicate 24 0⟩) _ = B
  have sA : A.1.size = noteOff S := by
    rw [size_eq, hA1, List.length_append, List.length_replicate]; rfl
  have hB1 : B.data.toList = List.replicate 64 0 ++ secBytes 64 S ++
      List.replicate (padN (noteOff S) 8) 0 ++ List.replicate 24 0 ++
      ((Y.zip (soffs Y)).map symRec).flatten := by
    rw [← hB, symFold]
    · simp [ByteArray.data_append, pad_toList, hA1, sA, soffs]
    · rintro b ⟨⟨name, sec, value, size, kind⟩, o⟩
      cases sec <;> simp [ByteArray.data_append, le_toList, symRec, symL, shndx]
  have sP : (pad A.1 8).size = symOff S := by rw [pad_size, sA]; rfl
  have sB : B.size = strOff S Y := by
    rw [size_eq, hB1]
    simp only [List.length_append, List.length_replicate, symRecs_length, strOff, symOff, noteOff]
    omega
  have sBs : (B ++ str).size = shstrOff S Y := by
    rw [ByteArray.size_append, sB, size_eq str, hst1]; rfl
  have sBss : (B ++ str ++ shstr).size = shstrOff S Y + (shstrL S).length := by
    rw [ByteArray.size_append, sBs, size_eq shstr, hsh1]; rfl
  have sPad : (pad (B ++ str ++ shstr) 8).size = shOff S Y := by rw [pad_size, sBss]; rfl
  simp only [sA, sP, sB, sBs, sPad, sBss, pad_toList, ByteArray.data_append, Array.toList_append,
    le_toList, shdr_toList, hA2, hB1, hsh1, hst1]
  simp only [size_eq, hsh1, hst1]
  simp only [model, ehdrL, tailShdrs, shstrL, strL, shoffs, soffs, shNames, Array.toList_replicate,
    List.append_assoc, List.nil_append, List.cons_append, drop_append_ge, List.length_replicate,
    Nat.le_refl, Nat.sub_self, List.drop_zero]

/-! ## Locating the parts of the object -/

theorem drop_mid {α : Type} (P X R : List α) (k : Nat) (hk : k ≤ X.length) :
    (P ++ X ++ R).drop (P.length + k) = X.drop k ++ R := by
  rw [List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left, List.drop_append, Nat.sub_eq_zero_of_le hk, List.drop_zero]

theorem drop_flatten_chunks {α : Type} (w : Nat) (cs : List (List α))
    (hw : ∀ c ∈ cs, c.length = w) (i : Nat) (hi : i < cs.length) :
    cs.flatten.drop (w * i) = cs[i] ++ (cs.drop (i + 1)).flatten := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hc := hw c (by simp)
      simp only [List.flatten_cons, List.getElem_cons_succ, List.drop_succ_cons]
      rw [Nat.mul_succ, Nat.add_comm, List.drop_append, List.drop_eq_nil_of_le (by omega),
        List.nil_append, hc, Nat.add_sub_cancel_left]
      exact ih (fun c h => hw c (by simp [h])) i (by simpa using hi)

theorem strOffs_getElem (c : Nat) (names : List String) (i : Nat) (hi : i < (strOffs c names).length) :
    (strOffs c names)[i] = c + ((names.take i).flatMap nameL).length := by
  induction names generalizing c i with
  | nil => simp [strOffs] at hi
  | cons n ns ih =>
    cases i with
    | zero => simp [strOffs]
    | succ i =>
      simp only [strOffs, List.getElem_cons_succ, List.take_succ_cons, List.flatMap_cons,
        List.length_append]
      rw [ih]; omega

theorem flatMap_drop_name (names : List String) (i : Nat) (hi : i < names.length) :
    (names.flatMap nameL).drop ((names.take i).flatMap nameL).length =
      nameL names[i] ++ (names.drop (i + 1)).flatMap nameL := by
  rw [show names.flatMap nameL = (names.take i).flatMap nameL ++ (names.drop i).flatMap nameL by
    rw [← List.flatMap_append, List.take_append_drop]]
  rw [List.drop_left' rfl, List.drop_eq_getElem_cons hi, List.flatMap_cons]

theorem secOffs_length (c : Nat) (S : List Section) : (secOffs c S).length = S.length := by
  induction S generalizing c <;> simp_all [secOffs]

theorem secBytes_drop (c : Nat) (S : List Section) (i o : Nat) (ho : (secOffs c S)[i]? = some o) :
    ∃ hi : i < S.length, c ≤ o ∧ o + S[i].data.size ≤ c + (secBytes c S).length ∧
      ((secBytes c S).drop (o - c)).take S[i].data.size = S[i].data.data.toList := by
  induction S generalizing c i with
  | nil => simp [secOffs] at ho
  | cons s S ih =>
    cases i with
    | zero =>
      simp only [secOffs, List.getElem?_cons_zero, Option.some.injEq] at ho
      subst ho
      refine ⟨by simp, by omega, ?_, ?_⟩
      · simp [secBytes]; omega
      · simp only [List.getElem_cons_zero, secBytes, Nat.add_sub_cancel_left, List.append_assoc]
        rw [List.drop_left' (by simp), List.take_append_of_le_length (by simp),
          List.take_of_length_le (by simp)]
    | succ i =>
      simp only [secOffs, List.getElem?_cons_succ] at ho
      obtain ⟨hi, h1, h2, h3⟩ := ih _ i ho
      refine ⟨by simpa using hi, by omega, ?_, ?_⟩
      · simp only [secBytes, List.getElem_cons_succ, List.length_append, List.length_replicate,
          Array.length_toList, ByteArray.size_data] at h2 ⊢
        omega
      · simp only [secBytes, List.getElem_cons_succ]
        rw [show o - c = (List.replicate (padN c (max s.align 1)) 0 ++ s.data.data.toList).length +
            (o - (c + padN c (max s.align 1) + s.data.size)) by simp; omega]
        rw [List.append_assoc, ← List.append_assoc (List.replicate _ _), List.drop_append,
          List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
        exact h3

/-- The bytes of a section header record. -/
def shdrOf (h : SectionHeader) : List UInt8 :=
  shdrL h.name h.kind h.flags h.address h.offset h.size h.link h.info h.alignment h.entrySize

/-- The null section header. -/
def nullHdr : SectionHeader := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The header of the written section `x.1.1`, at file offset `x.1.2`, with index `x.2`. -/
def userHdr (S : List Section) (x : (Section × Nat) × Nat) : SectionHeader :=
  ⟨(shoffs S)[x.2]!, 1, x.1.1.flags, 0, x.1.2, x.1.1.data.size, 0, 0, max x.1.1.align 1, 0⟩

def noteHdr (S : List Section) : SectionHeader :=
  ⟨(shoffs S)[S.length]!, 1, 0, 0, noteOff S, 0, 0, 0, 1, 0⟩

def symtabHdr (S : List Section) (Y : List Sym) : SectionHeader :=
  ⟨(shoffs S)[S.length + 1]!, 2, 0, 0, symOff S, 24 * (Y.length + 1), S.length + 3, 1, 8, 24⟩

def strtabHdr (S : List Section) (Y : List Sym) : SectionHeader :=
  ⟨(shoffs S)[S.length + 2]!, 3, 0, 0, strOff S Y, (strL Y).length, 0, 0, 1, 0⟩

def shstrtabHdr (S : List Section) (Y : List Sym) : SectionHeader :=
  ⟨(shoffs S)[S.length + 3]!, 3, 0, 0, shstrOff S Y, (shstrL S).length, 0, 0, 1, 0⟩

/-- The written user sections, with their file offsets and indices. -/
def userSecs (S : List Section) : List ((Section × Nat) × Nat) := (S.zip (secOffs 64 S)).zipIdx

/-- The section header table, in order. -/
def hdrs (S : List Section) (Y : List Sym) : List SectionHeader :=
  nullHdr :: (userSecs S).map (userHdr S) ++
    [noteHdr S, symtabHdr S Y, strtabHdr S Y, shstrtabHdr S Y]

theorem hdrs_length (S : List Section) (Y : List Sym) : (hdrs S Y).length = S.length + 5 := by
  simp [hdrs, userSecs, secOffs_length]

/-- The bytes of the symbol table. -/
def symtabL (Y : List Sym) : List UInt8 := List.replicate 24 0 ++ ((Y.zip (soffs Y)).map symRec).flatten

theorem model_ehdr (machine flags : Nat) (S : List Section) (Y : List Sym) :
    ∃ R, model machine flags S Y =
      ehdrL machine (shOff S Y) flags (S.length + 5) (S.length + 4) ++ R :=
  ⟨(secBytes 64 S ++ List.replicate (padN (noteOff S) 8) 0 ++ List.replicate 24 0 ++ ((Y.zip (soffs Y)).map symRec).flatten ++ strL Y ++ shstrL S ++ List.replicate (padN (shstrOff S Y + (shstrL S).length) 8) 0 ++ (List.replicate 64 0 ++ (((S.zip (secOffs 64 S)).zipIdx).map (shdrRec (shoffs S))).flatten ++ tailShdrs S Y)), by simp only [model, List.append_assoc]⟩

theorem model_secs (machine flags : Nat) (S : List Section) (Y : List Sym) :
    ∃ P R, model machine flags S Y = P ++ secBytes 64 S ++ R ∧ P.length = 64 :=
  ⟨ehdrL machine (shOff S Y) flags (S.length + 5) (S.length + 4), (List.replicate (padN (noteOff S) 8) 0 ++ List.replicate 24 0 ++ ((Y.zip (soffs Y)).map symRec).flatten ++ strL Y ++ shstrL S ++ List.replicate (padN (shstrOff S Y + (shstrL S).length) 8) 0 ++ (List.replicate 64 0 ++ (((S.zip (secOffs 64 S)).zipIdx).map (shdrRec (shoffs S))).flatten ++ tailShdrs S Y)), by simp only [model, List.append_assoc], by simp⟩

theorem model_symtab (machine flags : Nat) (S : List Section) (Y : List Sym) :
    ∃ P R, model machine flags S Y = P ++ symtabL Y ++ R ∧ P.length = symOff S :=
  ⟨(ehdrL machine (shOff S Y) flags (S.length + 5) (S.length + 4) ++ secBytes 64 S ++ List.replicate (padN (noteOff S) 8) 0), (strL Y ++ shstrL S ++ List.replicate (padN (shstrOff S Y + (shstrL S).length) 8) 0 ++ (List.replicate 64 0 ++ (((S.zip (secOffs 64 S)).zipIdx).map (shdrRec (shoffs S))).flatten ++ tailShdrs S Y)), by simp only [model, symtabL, List.append_assoc],
    by simp only [List.length_append, List.length_replicate, ehdrL_length, strOff, symOff, noteOff, shstrOff, shOff]⟩

theorem model_strtab (machine flags : Nat) (S : List Section) (Y : List Sym) :
    ∃ P R, model machine flags S Y = P ++ strL Y ++ R ∧ P.length = strOff S Y :=
  ⟨(ehdrL machine (shOff S Y) flags (S.length + 5) (S.length + 4) ++ secBytes 64 S ++ List.replicate (padN (noteOff S) 8) 0 ++ List.replicate 24 0 ++ ((Y.zip (soffs Y)).map symRec).flatten), (shstrL S ++ List.replicate (padN (shstrOff S Y + (shstrL S).length) 8) 0 ++ (List.replicate 64 0 ++ (((S.zip (secOffs 64 S)).zipIdx).map (shdrRec (shoffs S))).flatten ++ tailShdrs S Y)), by simp only [model, List.append_assoc],
    by simp only [List.length_append, List.length_replicate, ehdrL_length, symRecs_length, strOff, symOff, noteOff, shstrOff, shOff]; omega⟩

theorem model_shstrtab (machine flags : Nat) (S : List Section) (Y : List Sym) :
    ∃ P R, model machine flags S Y = P ++ shstrL S ++ R ∧ P.length = shstrOff S Y :=
  ⟨(ehdrL machine (shOff S Y) flags (S.length + 5) (S.length + 4) ++ secBytes 64 S ++ List.replicate (padN (noteOff S) 8) 0 ++ List.replicate 24 0 ++ ((Y.zip (soffs Y)).map symRec).flatten ++ strL Y), (List.replicate (padN (shstrOff S Y + (shstrL S).length) 8) 0 ++ (List.replicate 64 0 ++ (((S.zip (secOffs 64 S)).zipIdx).map (shdrRec (shoffs S))).flatten ++ tailShdrs S Y)), by simp only [model, List.append_assoc],
    by simp only [List.length_append, List.length_replicate, ehdrL_length, symRecs_length, strOff, symOff, noteOff, shstrOff, shOff]; omega⟩

theorem shdrOf_null : shdrOf nullHdr = List.replicate 64 0 := by decide

theorem model_shdrs (machine flags : Nat) (S : List Section) (Y : List Sym) :
    ∃ P, model machine flags S Y = P ++ ((hdrs S Y).map shdrOf).flatten ∧ P.length = shOff S Y := by
  refine ⟨(ehdrL machine (shOff S Y) flags (S.length + 5) (S.length + 4) ++ secBytes 64 S ++ List.replicate (padN (noteOff S) 8) 0 ++ List.replicate 24 0 ++ ((Y.zip (soffs Y)).map symRec).flatten ++ strL Y ++ shstrL S ++ List.replicate (padN (shstrOff S Y + (shstrL S).length) 8) 0), ?_, ?_⟩
  · simp only [model, hdrs, List.map_cons, List.map_append, List.flatten_cons,
      List.flatten_append, shdrOf_null, tailShdrs, List.map_map, List.append_assoc]
    rfl
  · simp only [List.length_append, List.length_replicate, ehdrL_length, symRecs_length, strOff, symOff, noteOff, shstrOff, shOff]; omega

/-! ## Names and section contents -/

/-- A name the writer can encode: its UTF-8 bytes contain no NUL. -/
def NameOk (n : String) : Prop := ∀ b ∈ n.toUTF8.data.toList, b ≠ 0

theorem toBits_eq (b : ByteArray) : toBits b = ⟨bits b.data.toList⟩ := by
  apply Array.ext'; simp [toBits]

theorem readName_of_drop {T post : List (BitVec 8)} {off : Nat} {nm : List UInt8}
    (hnz : ∀ b ∈ nm, b ≠ 0) (h : T.drop off = bits nm ++ 0 :: post) :
    readName ⟨T⟩ off = some (bits nm) := by
  have hlen := congrArg List.length h
  simp only [List.length_drop, List.length_append, List.length_map, List.length_cons] at hlen
  have ht : (bits nm ++ 0 :: post).takeWhile (fun b => b != 0) = bits nm := by
    rw [List.takeWhile_append_of_pos]
    · simp
    · intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have := hnz b hb
      simpa [← UInt8.toBitVec_inj] using this
  simp [readName, h, guard, show off < T.length by omega]
  erw [ht]
  simp

theorem sectionData_of_take {L X : List (BitVec 8)} {h : SectionHeader}
    (hk : h.kind ≠ 8) (hb : h.offset + h.size ≤ L.length) (hx : (L.drop h.offset).take h.size = X) :
    sectionData ⟨L⟩ h = some ⟨X⟩ := by
  simp [sectionData, hk, hb, hx, guard]

theorem getElem!_strOffs (c : Nat) (ns : List String) (i : Nat) (hi : i < ns.length) :
    (strOffs c ns)[i]! = c + ((ns.take i).flatMap nameL).length := by
  have hi' : i < (strOffs c ns).length := by rw [strOffs_length]; exact hi
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
    strOffs_getElem]

theorem strtab_drop (ns : List String) (i : Nat) (hi : i < ns.length) :
    (0 :: ns.flatMap nameL).drop (strOffs 1 ns)[i]! =
      ns[i].toUTF8.data.toList ++ 0 :: (ns.drop (i + 1)).flatMap nameL := by
  rw [getElem!_strOffs 1 ns i hi, Nat.add_comm, List.drop_succ_cons, flatMap_drop_name ns i hi]
  simp [nameL]

theorem strOffs_lt (ns : List String) (i : Nat) (hi : i < ns.length) :
    (strOffs 1 ns)[i]! < (0 :: ns.flatMap nameL).length := by
  have := congrArg List.length (strtab_drop ns i hi)
  simp only [List.length_drop, List.length_append, List.length_cons] at this ⊢
  omega

theorem readName_strtab (ns : List String) (i : Nat) (hi : i < ns.length) (ok : NameOk ns[i]) :
    readName ⟨bits (0 :: ns.flatMap nameL)⟩ (strOffs 1 ns)[i]! =
      some (bits ns[i].toUTF8.data.toList) := by
  apply readName_of_drop (post := bits ((ns.drop (i + 1)).flatMap nameL)) ok
  rw [← List.map_drop, strtab_drop ns i hi]
  simp

theorem readName_zero (ns : List String) :
    readName ⟨bits (0 :: ns.flatMap nameL)⟩ 0 = some [] :=
  readName_of_drop (nm := []) (post := bits (ns.flatMap nameL)) (by simp) (by simp)

/-! ## What the reader gives back -/

/-- The bytes of a string's name. -/
abbrev nameBits (n : String) : NameBytes := bits n.toUTF8.data.toList

/-- The section read back for a written section. -/
def userSec (S : List Section) (x : (Section × Nat) × Nat) : ObjectSection :=
  ⟨userHdr S x, nameBits x.1.1.name, ⟨bits x.1.1.data.data.toList⟩⟩

/-- The sections read back: null, the written ones, `.note.GNU-stack`, `.symtab`, `.strtab`,
`.shstrtab`. -/
def secs (S : List Section) (Y : List Sym) : List ObjectSection :=
  ⟨nullHdr, [], ⟨[]⟩⟩ :: (userSecs S).map (userSec S) ++
    [⟨noteHdr S, nameBits ".note.GNU-stack", ⟨[]⟩⟩,
     ⟨symtabHdr S Y, nameBits ".symtab", ⟨bits (symtabL Y)⟩⟩,
     ⟨strtabHdr S Y, nameBits ".strtab", ⟨bits (strL Y)⟩⟩,
     ⟨shstrtabHdr S Y, nameBits ".shstrtab", ⟨bits (shstrL S)⟩⟩]

/-- The symbol read back for a written symbol whose name is at `a.2`: global (binding 1). -/
def symOf (a : Sym × Nat) : ObjectSymbol :=
  ⟨⟨a.2, 16 + a.1.kind, 0, shndx a.1, a.1.value, a.1.size⟩, nameBits a.1.name⟩

/-- The symbols read back: the null symbol, then one per written symbol. -/
def syms (Y : List Sym) : List ObjectSymbol :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩, []⟩ :: (Y.zip (soffs Y)).map symOf

/-- The ELF header read back. -/
def header (machine flags : Nat) (S : List Section) (Y : List Sym) : Header :=
  ⟨0, 0, 1, machine, 1, 0, 0, shOff S Y, flags, 64, 0, 0, 64, S.length + 5, S.length + 4⟩

/-- **The object read back** from `writeRelocatable machine flags S Y`. -/
def expected (machine flags : Nat) (S : List Section) (Y : List Sym) : ObjectFile :=
  ⟨header machine flags S Y, secs S Y, syms Y, []⟩

/-- What the writer can encode faithfully: field widths, NUL-free names, at most `0xff00`
sections, a file under 4 GiB (string-table offsets are 32-bit), power-of-two alignments,
symbols in a written section or absolute. -/
structure Fits (machine flags : Nat) (S : List Section) (Y : List Sym) : Prop where
  machine : machine < 2 ^ 16
  flags : flags < 2 ^ 32
  count : S.length + 5 < 0xff00
  size : shOff S Y + 64 * (S.length + 5) < 2 ^ 32
  secs : ∀ s ∈ S, NameOk s.name ∧ s.flags < 2 ^ 64 ∧ max s.align 1 < 2 ^ 64 ∧
    validSectionAlignment (max s.align 1) = true
  syms : ∀ y ∈ Y, NameOk y.name ∧ 16 + y.kind < 2 ^ 8 ∧ y.value < 2 ^ 64 ∧ y.size < 2 ^ 64 ∧
    ∀ i, y.sec = some i → i < S.length

/-! ## The section header table -/

theorem shstrOff_le (S : List Section) (Y : List Sym) :
    noteOff S ≤ symOff S ∧ symOff S ≤ strOff S Y ∧ strOff S Y ≤ shstrOff S Y ∧
      shstrOff S Y + (shstrL S).length ≤ shOff S Y := by
  simp only [symOff, strOff, shstrOff, shOff]; omega

theorem model_length (machine flags : Nat) (S : List Section) (Y : List Sym) :
    (model machine flags S Y).length = shOff S Y + 64 * (S.length + 5) := by
  obtain ⟨P, hP, hl⟩ := model_shdrs machine flags S Y
  have : ∀ (hs : List SectionHeader), (hs.map shdrOf).flatten.length = 64 * hs.length := by
    intro hs; induction hs <;> simp_all [shdrOf]; omega
  rw [hP, List.length_append, this, hdrs_length, hl]

/-- A section header whose fields fit their widths. -/
def HdrFits (h : SectionHeader) : Prop :=
  h.name < 2 ^ 32 ∧ h.kind < 2 ^ 32 ∧ h.flags < 2 ^ 64 ∧ h.address < 2 ^ 64 ∧
    h.offset < 2 ^ 64 ∧ h.size < 2 ^ 64 ∧ h.link < 2 ^ 32 ∧ h.info < 2 ^ 32 ∧
    h.alignment < 2 ^ 64 ∧ h.entrySize < 2 ^ 64

theorem secOffs_getElem? (S : List Section) (i : Nat) (hi : i < S.length) :
    ∃ o, (secOffs 64 S)[i]? = some o := by
  refine ⟨(secOffs 64 S)[i]'(by rw [secOffs_length]; exact hi), ?_⟩
  simp

theorem mem_userSecs {S : List Section} {x : (Section × Nat) × Nat} (hx : x ∈ userSecs S) :
    ∃ hi : x.2 < S.length, S[x.2] = x.1.1 ∧ (secOffs 64 S)[x.2]? = some x.1.2 := by
  rw [userSecs, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] at hx
  obtain ⟨h1, h2⟩ := hx
  have hi : x.2 < S.length := by
    rcases (List.getElem?_eq_some_iff.1 h1) with ⟨hi, _⟩; exact hi
  exact ⟨hi, by simpa [List.getElem?_eq_getElem hi] using h1, h2⟩

theorem shNames_getElem (S : List Section) (i : Nat) (hi : i < S.length) :
    (shNames S)[i]'(by simp [shNames]; omega) = S[i].name := by
  simp [shNames, List.getElem_append_left (by simpa using hi : i < (S.map (·.name)).length)]

theorem shoffs_lt (S : List Section) (i : Nat) (hi : i < S.length + 4) :
    (shoffs S)[i]! < (shstrL S).length :=
  strOffs_lt (shNames S) i (by simp [shNames]; omega)

theorem userHdr_fits {machine flags : Nat} {S : List Section} {Y : List Sym}
    (F : Fits machine flags S Y) {x : (Section × Nat) × Nat} (hx : x ∈ userSecs S) :
    HdrFits (userHdr S x) := by
  obtain ⟨hi, hs, ho⟩ := mem_userSecs hx
  obtain ⟨hi', h1, h2, -⟩ := secBytes_drop 64 S x.2 x.1.2 ho
  have hS := F.secs x.1.1 (by rw [← hs]; exact List.getElem_mem hi)
  have hn := shoffs_lt S x.2 (by omega)
  have h3 := shstrOff_le S Y
  have h4 := F.size
  rw [hs] at h2
  simp only [noteOff] at h3
  refine ⟨show (shoffs S)[x.2]! < 2 ^ 32 by omega, by simp [userHdr], hS.2.1, by simp [userHdr],
    show x.1.2 < 2 ^ 64 by omega, show x.1.1.data.size < 2 ^ 64 by omega, by simp [userHdr], by simp [userHdr],
    hS.2.2.1, by simp [userHdr]⟩

theorem hdrs_fit {machine flags : Nat} {S : List Section} {Y : List Sym}
    (F : Fits machine flags S Y) : ∀ h ∈ hdrs S Y, HdrFits h := by
  have hle := shstrOff_le S Y
  have hsz := F.size
  have hcount := F.count
  have hn : ∀ i, i < S.length + 4 → (shoffs S)[i]! < 2 ^ 32 := fun i hi => by
    have := shoffs_lt S i hi; omega
  intro h hh
  simp only [hdrs, List.mem_cons, List.mem_append, List.mem_map] at hh
  rcases hh with (rfl | ⟨x, hx, rfl⟩) | hh
  · simp [nullHdr, HdrFits]
  · exact userHdr_fits F hx
  · simp only [List.not_mem_nil, or_false] at hh
    simp only [strOff, symOff, shstrOff] at hle
    rcases hh with rfl | rfl | rfl | rfl
    · exact ⟨hn _ (by omega), by simp [noteHdr], by simp [noteHdr], by simp [noteHdr],
        show noteOff S < 2 ^ 64 by omega, by simp [noteHdr], by simp [noteHdr],
        by simp [noteHdr], by simp [noteHdr], by simp [noteHdr]⟩
    · exact ⟨hn _ (by omega), by simp [symtabHdr], by simp [symtabHdr], by simp [symtabHdr],
        show symOff S < 2 ^ 64 by simp only [symOff]; omega,
        show 24 * (Y.length + 1) < 2 ^ 64 by omega,
        show S.length + 3 < 2 ^ 32 by omega, by simp [symtabHdr], by simp [symtabHdr],
        by simp [symtabHdr]⟩
    · exact ⟨hn _ (by omega), by simp [strtabHdr], by simp [strtabHdr], by simp [strtabHdr],
        show strOff S Y < 2 ^ 64 by simp only [strOff, symOff]; omega,
        show (strL Y).length < 2 ^ 64 by omega, by simp [strtabHdr], by simp [strtabHdr],
        by simp [strtabHdr], by simp [strtabHdr]⟩
    · exact ⟨hn _ (by omega), by simp [shstrtabHdr], by simp [shstrtabHdr],
        by simp [shstrtabHdr], show shstrOff S Y < 2 ^ 64 by simp only [shstrOff, strOff, symOff]; omega,
        show (shstrL S).length < 2 ^ 64 by omega, by simp [shstrtabHdr], by simp [shstrtabHdr],
        by simp [shstrtabHdr], by simp [shstrtabHdr]⟩

theorem readSectionHeader_fits {L post : List (BitVec 8)} {off : Nat} {h : SectionHeader}
    (hd : L.drop off = bits (shdrOf h) ++ post) (hf : HdrFits h) :
    readSectionHeader ⟨L⟩ off = some h := by
  rw [readSectionHeader_of_drop hd]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hf
  simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4,
    Nat.mod_eq_of_lt h5, Nat.mod_eq_of_lt h6, Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt h8,
    Nat.mod_eq_of_lt h9, Nat.mod_eq_of_lt h10]

theorem shdrOf_length (h : SectionHeader) : (shdrOf h).length = 64 := by simp [shdrOf]

theorem readSectionHeaders_model {machine flags : Nat} {S : List Section} {Y : List Sym}
    (F : Fits machine flags S Y) :
    readSectionHeaders ⟨bits (model machine flags S Y)⟩ (header machine flags S Y) =
      some (hdrs S Y) := by
  have hcount := F.count
  have hle := shstrOff_le S Y
  have hlen := model_length machine flags S Y
  apply readSectionHeaders_of_records
  · simp only [header]; omega
  · simp [header]
  · simp only [header]; refine ⟨by simp, ?_⟩; simp only [noteOff] at hle; omega
  · simp [header]
  · rw [List.size_toArray]
    simp only [header, List.length_map]; omega
  · rw [List.forall₂_iff_get]
    refine ⟨by simp [header, hdrs_length], fun i h₁ h₂ => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_range]
    obtain ⟨P, hP, hl⟩ := model_shdrs machine flags S Y
    apply readSectionHeader_fits (post := bits (((hdrs S Y).map shdrOf).drop (i + 1)).flatten)
    · simp only [header]
      rw [hP, ← hl]
      simp only [bits, List.map_append]
      rw [List.drop_append, List.drop_eq_nil_of_le (by simp),
        List.nil_append, List.length_map, Nat.add_sub_cancel_left, ← List.map_drop,
        drop_flatten_chunks 64 _ (by simp [shdrOf_length]) i (by simpa using h₂)]
      simp
    · exact hdrs_fit F _ (List.getElem_mem _)

/-! ## The sections -/

theorem take_drop_bits {M P X R D : List UInt8} {o n : Nat} (h : M = P ++ X ++ R)
    (hk : P.length ≤ o) (hb : o - P.length + n ≤ X.length) (hx : (X.drop (o - P.length)).take n = D) :
    ((bits M).drop o).take n = bits D := by
  rw [h, ← List.map_drop, ← List.map_take, show o = P.length + (o - P.length) by omega,
    drop_mid P X R _ (by omega), List.take_append_of_le_length (by simp; omega), hx]

theorem objSection_of {bytes strings : Bytes} {h : SectionHeader} {nm : NameBytes} {d : Bytes}
    (hv : validSectionAlignment h.alignment = true) (hn : readName strings h.name = some nm)
    (hd : sectionData bytes h = some d) :
    (do
      guard (validSectionAlignment h.alignment)
      let name ← readName strings h.name
      let data ← sectionData bytes h
      pure ({ header := h, name, data } : ObjectSection)) = some ⟨h, nm, d⟩ := by
  simp [hv, hn, hd, guard]

theorem symtabL_length (Y : List Sym) : (symtabL Y).length = 24 * (Y.length + 1) := by
  simp only [symtabL, List.length_append, List.length_replicate, symRecs_length]; omega

theorem nameOk_fixed : NameOk ".note.GNU-stack" ∧ NameOk ".symtab" ∧ NameOk ".strtab" ∧
    NameOk ".shstrtab" := by
  have h : ∀ (n : String) (l : List UInt8), n.toUTF8.data.toList = l → (∀ b ∈ l, b ≠ 0) →
      NameOk n := fun n l e hl => by unfold NameOk; rw [e]; exact hl
  have e0 : ".note.GNU-stack".toUTF8.data.toList = [46, 110, 111, 116, 101, 46, 71, 78, 85, 45, 115, 116, 97, 99, 107] := by
    show (String.ofList ['.', 'n', 'o', 't', 'e', '.', 'G', 'N', 'U', '-', 's', 't', 'a', 'c', 'k']).toUTF8.data.toList = _
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]; decide
  have e1 : ".symtab".toUTF8.data.toList = [46, 115, 121, 109, 116, 97, 98] := by
    show (String.ofList ['.', 's', 'y', 'm', 't', 'a', 'b']).toUTF8.data.toList = _
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]; decide
  have e2 : ".strtab".toUTF8.data.toList = [46, 115, 116, 114, 116, 97, 98] := by
    show (String.ofList ['.', 's', 't', 'r', 't', 'a', 'b']).toUTF8.data.toList = _
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]; decide
  have e3 : ".shstrtab".toUTF8.data.toList = [46, 115, 104, 115, 116, 114, 116, 97, 98] := by
    show (String.ofList ['.', 's', 'h', 's', 't', 'r', 't', 'a', 'b']).toUTF8.data.toList = _
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]; decide
  exact ⟨h _ _ e0 (by decide), h _ _ e1 (by decide), h _ _ e2 (by decide), h _ _ e3 (by decide)⟩

theorem readObjectSections_model {machine flags : Nat} {S : List Section} {Y : List Sym}
    (F : Fits machine flags S Y) :
    readObjectSections ⟨bits (model machine flags S Y)⟩ (hdrs S Y) ⟨bits (shstrL S)⟩ =
      some (secs S Y) := by
  have hle := shstrOff_le S Y
  have hlen := model_length machine flags S Y
  have hfix := nameOk_fixed
  have tailName : ∀ k (hk : k < 4), readName ⟨bits (shstrL S)⟩ (shoffs S)[S.length + k]! =
      some (nameBits ((shNames S)[S.length + k]'(by simp [shNames]; omega))) := fun k hk =>
    readName_strtab (shNames S) (S.length + k) (by simp [shNames]; omega) (by
      have : (shNames S)[S.length + k]'(by simp [shNames]; omega) =
          [".note.GNU-stack", ".symtab", ".strtab", ".shstrtab"][k] := by
        simp [shNames, List.getElem_append_right]
      rw [this]
      rcases k with _ | _ | _ | _ | k
      · exact hfix.1
      · exact hfix.2.1
      · exact hfix.2.2.1
      · exact hfix.2.2.2
      · omega)
  apply mapM_record_certificates
  simp only [hdrs, secs]
  refine List.Forall₂.cons ?_ (List.rel_append ?_ ?_)
  · apply objSection_of rfl (readName_zero _)
    simp [sectionData, nullHdr, guard]
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro x hx
    obtain ⟨hi, hs, ho⟩ := mem_userSecs hx
    obtain ⟨hi', h1, h2, h3⟩ := secBytes_drop 64 S x.2 x.1.2 ho
    have hS := F.secs x.1.1 (by rw [← hs]; exact List.getElem_mem hi)
    apply objSection_of hS.2.2.2
    · have := readName_strtab (shNames S) x.2 (by simp [shNames]; omega)
        (by rw [shNames_getElem S x.2 hi, hs]; exact hS.1)
      rw [shNames_getElem S x.2 hi, hs] at this
      exact this
    · obtain ⟨P, R, hM, hP⟩ := model_secs machine flags S Y
      apply sectionData_of_take (by simp [userHdr])
      · simp only [userHdr, List.length_map]; simp only [noteOff] at hle; rw [hs] at h2; omega
      · simp only [userHdr]
        rw [hs] at h3
        rw [take_drop_bits hM (by omega) (by rw [hP]; rw [hs] at h2; omega) (by rw [hP])]
        rw [hP] at *; rw [h3]
  · obtain ⟨Pa, Ra, hMa, hPa⟩ := model_symtab machine flags S Y
    obtain ⟨Pb, Rb, hMb, hPb⟩ := model_strtab machine flags S Y
    obtain ⟨Pc, Rc, hMc, hPc⟩ := model_shstrtab machine flags S Y
    simp only [strOff, symOff, shstrOff, noteOff] at hle hPa hPb hPc
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
    · apply objSection_of (by simp [noteHdr, validSectionAlignment]) (by simpa [noteHdr, shNames] using tailName 0 (by omega))
      apply sectionData_of_take (by simp [noteHdr]) (by simp [noteHdr, noteOff]; omega)
      simp [noteHdr]
    · apply objSection_of (by simp [symtabHdr, validSectionAlignment]) (by simpa [symtabHdr, shNames] using tailName 1 (by omega))
      apply sectionData_of_take (by simp [symtabHdr]) (by simp [symtabHdr, symOff, noteOff]; omega)
      simp only [symtabHdr]
      rw [take_drop_bits hMa (by simp only [symOff, noteOff]; omega)
        (by simp only [symOff, noteOff, symtabL_length]; omega)
        (by rw [show symOff S - Pa.length = 0 by simp only [symOff, noteOff]; omega, List.drop_zero,
          ← symtabL_length, List.take_length])]
    · apply objSection_of (by simp [strtabHdr, validSectionAlignment]) (by simpa [strtabHdr, shNames] using tailName 2 (by omega))
      apply sectionData_of_take (by simp [strtabHdr])
        (by simp [strtabHdr, strOff, symOff, noteOff]; omega)
      simp only [strtabHdr]
      rw [take_drop_bits hMb (by simp only [strOff, symOff, noteOff]; omega)
        (by simp only [strOff, symOff, noteOff]; omega)
        (by rw [show strOff S Y - Pb.length = 0 by simp only [strOff, symOff, noteOff]; omega,
          List.drop_zero, List.take_length])]
    · apply objSection_of (by simp [shstrtabHdr, validSectionAlignment]) (by simpa [shstrtabHdr, shNames] using tailName 3 (by omega))
      apply sectionData_of_take (by simp [shstrtabHdr])
        (by simp [shstrtabHdr, shstrOff, strOff, symOff, noteOff]; omega)
      simp only [shstrtabHdr]
      rw [take_drop_bits hMc (by simp only [shstrOff, strOff, symOff, noteOff]; omega)
        (by simp only [shstrOff, strOff, symOff, noteOff]; omega)
        (by rw [show shstrOff S Y - Pc.length = 0 by
          simp only [shstrOff, strOff, symOff, noteOff]; omega, List.drop_zero, List.take_length])]

/-! ## The symbol table -/

theorem secs_kinds (S : List Section) (Y : List Sym) :
    (secs S Y).map (·.header.kind) = 0 :: List.replicate S.length 1 ++ [1, 2, 3, 3] := by
  simp only [secs, List.map_cons, List.map_append, List.map_map]
  congr 1
  rw [show ((fun x : ObjectSection => x.header.kind) ∘ userSec S) = fun _ => 1 from rfl,
    List.map_const']
  simp [userSecs, secOffs_length]
  rfl

theorem secs_length (S : List Section) (Y : List Sym) : (secs S Y).length = S.length + 5 := by
  have := congrArg List.length (secs_kinds S Y)
  simp only [List.length_map, List.length_cons, List.length_append, List.length_replicate] at this
  omega

theorem filter_range_eq (k j : Nat) (hj : j < k) :
    (List.range k).filter (fun i => decide (i = j)) = [j] := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.filter_append]
    by_cases h : j = k
    · subst h
      rw [List.filter_eq_nil_iff.2 (fun i hi => by simp at hi; simp; omega)]
      simp
    · rw [ih (by omega)]; simp; omega

theorem symtab_unique (S : List Section) (Y : List Sym) :
    (List.range (secs S Y).length).filter (fun index =>
      ((secs S Y)[index]?.map (fun part => part.header.kind)) == some 2) = [S.length + 2] := by
  rw [List.filter_congr (q := fun i => decide (i = S.length + 2)), secs_length,
    filter_range_eq _ _ (by omega)]
  intro i hi
  rw [secs_length, List.mem_range] at hi
  rw [← List.getElem?_map, secs_kinds]
  rcases Nat.lt_or_ge i (S.length + 1) with h | h
  · rcases i with _ | i
    · simp
    · rw [List.getElem?_append_left (by simp; omega)]
      simp only [List.getElem?_cons_succ, List.getElem?_replicate, ite_eq_left (by omega : i < S.length)]
      simp; omega
  · obtain ⟨k, rfl⟩ : ∃ k, i = S.length + 1 + k := ⟨i - (S.length + 1), by omega⟩
    rcases k with _ | _ | _ | _ | k
    all_goals simp
    all_goals omega

theorem secs_getElem_tail (S : List Section) (Y : List Sym) (k : Nat) :
    (secs S Y)[S.length + 1 + k]? =
      [(⟨noteHdr S, nameBits ".note.GNU-stack", ⟨[]⟩⟩ : ObjectSection),
       ⟨symtabHdr S Y, nameBits ".symtab", ⟨bits (symtabL Y)⟩⟩,
       ⟨strtabHdr S Y, nameBits ".strtab", ⟨bits (strL Y)⟩⟩,
       ⟨shstrtabHdr S Y, nameBits ".shstrtab", ⟨bits (shstrL S)⟩⟩][k]? := by
  have hl : ((⟨nullHdr, [], ⟨[]⟩⟩ : ObjectSection) :: (userSecs S).map (userSec S)).length =
      S.length + 1 := by simp [userSecs, secOffs_length]
  simp only [secs]
  rw [List.getElem?_append_right (by rw [hl]; omega), hl,
    show S.length + 1 + k - (S.length + 1) = k by omega]

theorem symtabL_chunks (Y : List Sym) :
    symtabL Y = (symL 0 0 0 0 0 0 :: (Y.zip (soffs Y)).map symRec).flatten := by
  simp [symtabL, symL_zero]

theorem soffs_getElem (Y : List Sym) (k : Nat) (hk : k < (soffs Y).length) :
    (soffs Y)[k] = (strOffs 1 (Y.map (·.name)))[k]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [soffs] using hk)]
  rfl

theorem readObjectSymbols_model {machine flags : Nat} {S : List Section} {Y : List Sym}
    (F : Fits machine flags S Y) :
    readObjectSymbols ⟨bits (model machine flags S Y)⟩ (secs S Y) (S.length + 2) =
      some (syms Y) := by
  have hle := shstrOff_le S Y
  have hsz := F.size
  have hcount := F.count
  have hsl : (soffs Y).length = Y.length := by simp [soffs, strOffs_length]
  apply readObjectSymbols_of_records (table := ⟨symtabHdr S Y, nameBits ".symtab", ⟨bits (symtabL Y)⟩⟩)
    (strings := ⟨strtabHdr S Y, nameBits ".strtab", ⟨bits (strL Y)⟩⟩)
  · simpa using secs_getElem_tail S Y 1
  · simp [symtabHdr]
  · simp only [symtabHdr]; omega
  · simpa [symtabHdr, Nat.add_assoc] using secs_getElem_tail S Y 2
  · simp [strtabHdr]
  · rw [List.forall₂_iff_get]
    refine ⟨by simp [symtabHdr, syms, hsl], fun j h₁ h₂ => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_range]
    obtain ⟨P, R, hM, hP⟩ := model_symtab machine flags S Y
    have hj : j < Y.length + 1 := by simpa [syms, hsl] using h₂
    have hdrop : ∀ (c : List UInt8), c = ((symL 0 0 0 0 0 0 :: (Y.zip (soffs Y)).map symRec))[j]'(by
        simp [hsl]; omega) →
        (bits (model machine flags S Y)).drop ((symtabHdr S Y).offset + 24 * j) =
          bits c ++ bits (((symL 0 0 0 0 0 0 :: (Y.zip (soffs Y)).map symRec).drop (j + 1)).flatten ++ R) := by
      intro c hc
      simp only [symtabHdr]
      rw [hM, ← hP, ← List.map_drop, drop_mid _ _ _ _ (by rw [symtabL_length]; omega), symtabL_chunks,
        drop_flatten_chunks 24 _ (by
          intro c hc; simp only [List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨a, _, rfl⟩ <;> simp [symRec]) j (by simp [hsl]; omega), ← hc]
      simp
    rcases j with _ | k
    · apply objectSymbol_of_raw
      · rw [readSymbol_of_drop (hdrop _ rfl)]; simp [syms]
      · simpa [syms, strtabHdr, strL] using readName_zero (Y.map (·.name))
      · simp [syms, secs_length]
    · have hk : k < Y.length := by omega
      have hY := F.syms Y[k] (List.getElem_mem hk)
      have hsym : (syms Y)[k + 1]'h₂ = symOf (Y[k], (soffs Y)[k]'(by omega)) := by
        simp [syms, List.getElem_zip]
      have hoff := strOffs_lt (Y.map (·.name)) k (by simpa using hk)
      have hshndx : shndx Y[k] < 2 ^ 16 ∧ (shndx Y[k] < (secs S Y).length ∨ 0xff00 ≤ shndx Y[k]) := by
        rw [secs_length]
        unfold shndx
        split
        · rename_i i hi
          have := hY.2.2.2.2 i hi; omega
        · omega
      rw [hsym]
      apply objectSymbol_of_raw
      · rw [readSymbol_of_drop (hdrop (symL ((soffs Y)[k]'(by omega)) (16 + Y[k].kind) 0
          (shndx Y[k]) Y[k].value Y[k].size) (by simp [List.getElem_zip, symRec]))]
        simp only [symOf]
        rw [soffs_getElem Y k (by omega)]
        simp only [strOff, symOff, shstrOff] at hle
        simp only [strL, List.length_cons] at hle hoff
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hY.2.1, Nat.mod_eq_of_lt hshndx.1,
          Nat.mod_eq_of_lt hY.2.2.1, Nat.mod_eq_of_lt hY.2.2.2.1]
        rfl
      · simp only [symOf]
        rw [soffs_getElem Y k (by omega)]
        have := readName_strtab (Y.map (·.name)) k (by simpa using hk) (by simpa using hY.1)
        simpa [strL, nameBits] using this
      · exact hshndx.2

/-! ## Relocations and the header -/

theorem secs_kind_le (S : List Section) (Y : List Sym) : ∀ s ∈ secs S Y, s.header.kind ≤ 3 := by
  intro s hs
  have : s.header.kind ∈ (secs S Y).map (·.header.kind) := List.mem_map_of_mem hs
  rw [secs_kinds] at this
  simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at this
  omega

theorem readObjectRelocations_model (L : List (BitVec 8)) (S : List Section) (Y : List Sym)
    (t c : Nat) : readObjectRelocations ⟨L⟩ (secs S Y) t c = some [] := by
  rw [show ([] : List ObjectRelocation) = ((secs S Y).map fun _ => ([] : List ObjectRelocation)).flatten
    by simp]
  apply readObjectRelocations_of_records
  rw [List.forall₂_map_right_iff, List.forall₂_same]
  intro s hs
  have := secs_kind_le S Y s hs
  exact relocationTable_empty _ _ _ _ _ (by omega) ⟨by omega, by omega⟩

theorem readHeader_model {machine flags : Nat} {S : List Section} {Y : List Sym}
    (F : Fits machine flags S Y) :
    readHeader ⟨bits (model machine flags S Y)⟩ = some (header machine flags S Y) := by
  obtain ⟨R, hR⟩ := model_ehdr machine flags S Y
  have hlen := model_length machine flags S Y
  have hsz := F.size
  have hm := F.machine
  have hf := F.flags
  have hc := F.count
  rw [readHeader_of_take (by simp; omega) (by rw [hR, ← List.map_take,
    List.take_left' (by simp)]), header]
  simp only [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt (by omega : shOff S Y < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : S.length + 5 < 2 ^ 16), Nat.mod_eq_of_lt (by omega : S.length + 4 < 2 ^ 16)]

/-! ## The round trip -/

/-- **The ELF writer round trip.** Reading back what `writeRelocatable` writes gives the
expected object: its header, the null section, every written section (name, flags,
alignment, file bytes), `.note.GNU-stack`, `.symtab`, `.strtab`, `.shstrtab`, the null
symbol, every written symbol (name, kind, section, value, size), and no relocation. -/
theorem readObject_writeRelocatable {machine flags : Nat} {S : List Section} {Y : List Sym}
    (F : Fits machine flags S Y) :
    readObject (toBits (writeRelocatable machine flags S Y)) = some (expected machine flags S Y) := by
  rw [toBits_eq, writeRelocatable_toList]
  have hc := F.count
  apply readObject_of_parts (headers := hdrs S Y) (null := nullHdr)
    (names := shstrtabHdr S Y) (strings := ⟨bits (shstrL S)⟩) (symbolTable := S.length + 2)
  · exact readHeader_model F
  · simp [header]
  · rfl
  · exact readSectionHeaders_model F
  · simp [hdrs_length]
  · simp [hdrs]
  · simp [nullHdr]
  · simp only [header, hdrs]
    rw [List.getElem?_append_right (by simp [userSecs, secOffs_length])]
    simp [userSecs, secOffs_length]
  · rfl
  · obtain ⟨P, R, hM, hP⟩ := model_shstrtab machine flags S Y
    have hle := shstrOff_le S Y
    have hlen := model_length machine flags S Y
    apply sectionData_of_take (by simp [shstrtabHdr])
      (by simp only [shstrtabHdr, List.length_map]; omega)
    simp only [shstrtabHdr]
    rw [take_drop_bits hM (by omega) (by omega)
      (by rw [hP, Nat.sub_self, List.drop_zero, List.take_length])]
  · exact readObjectSections_model F
  · exact symtab_unique S Y
  · exact readObjectSymbols_model F
  · exact readObjectRelocations_model _ S Y _ _

/-! ## Names -/

theorem utf8EncodeChar_ne_zero (c : Char) (hc : c.val ≠ 0) :
    ∀ b ∈ String.utf8EncodeChar c, b ≠ 0 := by
  have h1 := Char.utf8Size_pos c
  have h4 := Char.utf8Size_le_four c
  rcases (by omega : c.utf8Size = 1 ∨ c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4)
    with h | h | h | h
  · rw [String.utf8EncodeChar_eq_singleton h]
    have hv := Char.utf8Size_eq_one_iff.1 h
    simp only [List.mem_singleton]
    rintro b rfl
    rw [ne_eq, ← UInt8.toNat_inj, UInt32.toNat_toUInt8, UInt8.toNat_zero]
    rw [ne_eq, ← UInt32.toNat_inj] at hc
    rw [UInt32.le_iff_toNat_le] at hv
    simp only [UInt32.toNat_zero] at hc
    have : c.val.toNat ≤ 127 := by simpa using hv
    omega
  · rw [String.utf8EncodeChar_eq_cons_cons h]; simp
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h]; simp
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h]; simp

/-- A string without NUL characters encodes without NUL bytes. -/
theorem nameOk_of_chars (n : String) (h : ∀ c ∈ n.toList, c.val ≠ 0) : NameOk n := by
  unfold NameOk
  rw [← String.ofList_toList (s := n), String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    List.utf8Encode_eq_toByteArray]
  simp only [List.data_toByteArray, List.toList_toArray, List.mem_flatMap]
  rintro b ⟨c, hc, hb⟩
  exact utf8EncodeChar_ne_zero c (h c hc) b hb

theorem nameOk_dispatch (i : Nat) : NameOk s!"__ccomp_dispatch.{i}" := by
  apply nameOk_of_chars
  intro c hc
  simp only [String.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · revert c; decide
  · have hd : c.isDigit := Nat.isDigit_of_mem_toDigits (b := 10) (n := i) (by decide) (by decide)
      (by simpa [Nat.toString_eq_repr, Nat.toList_repr] using hc)
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    intro h0
    have : c.val = 0 := h0
    have h48 := hd.1
    rw [this] at h48
    exact absurd h48 (by decide)

/-- One step of `objectNames`'s loop. -/
def fillStep (a : Array (Option String)) (p : String × Nat) : Array (Option String) :=
  if p.2 < a.size then a.set! p.2 (some p.1) else a

theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  rw [show f = fun a b => pure (.yield (g b a)) from funext fun a => funext fun b => h a b]
  exact List.forIn_pure_yield_eq_foldl _ _

theorem objectNames_eq (l : Mir.Linked) (code : Code) :
    objectNames l code = (l.funcs.toList.foldl fillStep (Array.replicate code.entries.size none)).mapIdx
      fun i o => o.getD s!"__ccomp_dispatch.{i}" := by
  unfold objectNames
  dsimp only
  rw [forIn_id_yield _ _ _ fillStep (fun a b => by unfold fillStep; split <;> rfl)]
  rfl

theorem fill_size (L : List (String × Nat)) (a : Array (Option String)) :
    (L.foldl fillStep a).size = a.size := by
  induction L generalizing a with
  | nil => rfl
  | cons p L ih => rw [List.foldl_cons, ih]; unfold fillStep; split <;> simp

theorem fill_some (L : List (String × Nat)) (a : Array (Option String)) (i : Nat) (m : String)
    (h : (L.foldl fillStep a)[i]? = some (some m)) : (m, i) ∈ L ∨ a[i]? = some (some m) := by
  induction L generalizing a with
  | nil => exact .inr h
  | cons p L ih =>
    rcases ih _ h with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · unfold fillStep at h
      split at h
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h; rename_i h'; subst h'
          exact .inl List.mem_cons_self
        · exact .inr h
      · exact .inr h

theorem fill_keep (L : List (String × Nat)) (a : Array (Option String)) (i : Nat) (m : String)
    (h : a[i]? = some (some m)) : ∃ m', (L.foldl fillStep a)[i]? = some (some m') := by
  induction L generalizing a m with
  | nil => exact ⟨m, h⟩
  | cons p L ih =>
    rw [List.foldl_cons]
    unfold fillStep
    split
    · rename_i h1
      by_cases hpi : p.2 = i
      · subst hpi; exact ih _ p.1 (by simp [Array.set!_eq_setIfInBounds, h1])
      · exact ih _ m (by
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [hpi, h])
    · exact ih _ m h

theorem fill_filled (L : List (String × Nat)) (a : Array (Option String)) (n : String) (i : Nat)
    (hn : (n, i) ∈ L) (hi : i < a.size) : ∃ m, (L.foldl fillStep a)[i]? = some (some m) := by
  induction L generalizing a with
  | nil => simp at hn
  | cons p L ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hn with rfl | hn
    · apply fill_keep _ _ _ n
      simp [fillStep, hi, Array.set!_eq_setIfInBounds]
    · exact ih _ hn (by unfold fillStep; split <;> simp_all)

theorem sum_set_le {β : Type} (f : β → Nat) (l : List β) (i : Nat) (x : β) :
    ((l.set i x).map f).sum ≤ (l.map f).sum + f x := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero => simp; omega
    | succ i => simp only [List.set_cons_succ, List.map_cons, List.sum_cons]; have := ih i; omega

/-- The bytes of the names an array of optional names holds. -/
def weight (a : Array (Option String)) : Nat :=
  (a.toList.map fun o => (o.map String.utf8ByteSize).getD 0).sum

theorem fill_weight (L : List (String × Nat)) (a : Array (Option String)) :
    weight (L.foldl fillStep a) ≤ weight a + (L.map (·.1.utf8ByteSize)).sum := by
  induction L generalizing a with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons]
    have := ih (fillStep a p)
    have hs : weight (fillStep a p) ≤ weight a + p.1.utf8ByteSize := by
      unfold fillStep weight
      split
      · rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
        exact sum_set_le _ _ _ _
      · omega
    simp only [List.map_cons, List.sum_cons]
    omega

theorem utf8ByteSize_le (s : String) : s.utf8ByteSize ≤ 4 * s.length := by
  rw [← String.ofList_toList (s := s), ← String.size_toByteArray, String.toByteArray_ofList,
    List.utf8Encode_eq_toByteArray]
  simp only [List.size_toByteArray, List.length_flatMap, String.length_utf8EncodeChar,
    String.ofList_toList, ← String.length_toList]
  generalize s.toList = l
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]; have := Char.utf8Size_le_four c; omega

theorem dispatch_size (i : Nat) (hi : i < 2 ^ 20) : (s!"__ccomp_dispatch.{i}").utf8ByteSize ≤ 96 := by
  have h := utf8ByteSize_le s!"__ccomp_dispatch.{i}"
  have hd : (Nat.toDigits 10 i).length ≤ 7 :=
    (Nat.length_toDigits_le_iff (by decide) (by decide)).2 (by omega)
  have : (s!"__ccomp_dispatch.{i}").length = 17 + (Nat.toDigits 10 i).length := by
    rw [← String.length_toList]; simp [Nat.toString_eq_repr, Nat.toList_repr]
    show "__ccomp_dispatch.".toList.length = 17
    simp
  omega

/-- The table filled by the names of the link. -/
abbrev filled (l : Mir.Linked) (code : Code) : Array (Option String) :=
  l.funcs.toList.foldl fillStep (Array.replicate code.entries.size none)

theorem names_size (l : Mir.Linked) (code : Code) :
    (objectNames l code).size = code.entries.size := by
  rw [objectNames_eq, Array.size_mapIdx, fill_size, Array.size_replicate]

theorem names_getElem (l : Mir.Linked) (code : Code) (i : Nat) (hi : i < code.entries.size) :
    (objectNames l code)[i]'(by rw [names_size]; exact hi) =
      ((filled l code)[i]'(by rw [fill_size, Array.size_replicate]; exact hi)).getD
        s!"__ccomp_dispatch.{i}" := by
  simp only [objectNames_eq, Array.getElem_mapIdx]

theorem filled_some (l : Mir.Linked) (code : Code) (i : Nat) (m : String)
    (h : (filled l code)[i]? = some (some m)) : l.funcs[m]? = some i := by
  rcases fill_some _ _ i m h with h | h
  · exact Std.HashMap.mem_toList_iff_getElem?_eq_some.1 h
  · simp [Array.getElem?_replicate] at h

theorem names_funcs (l : Mir.Linked) (code : Code)
    (hinj : ∀ (n m : String) (i : Nat), l.funcs[n]? = some i → l.funcs[m]? = some i → n = m)
    (n : String) (i : Nat) (h : l.funcs[n]? = some i) (hi : i < code.entries.size) :
    (objectNames l code)[i]'(by rw [names_size]; exact hi) = n := by
  obtain ⟨m, hm⟩ := fill_filled l.funcs.toList (Array.replicate code.entries.size none) n i
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.2 h) (by simpa using hi)
  have := hinj _ _ _ (filled_some l code i m hm) h
  subst this
  rw [names_getElem l code i hi]
  rw [Array.getElem?_eq_getElem (by rw [fill_size, Array.size_replicate]; exact hi)] at hm
  simp only [Option.some.injEq] at hm
  rw [hm]; rfl

theorem names_cases (l : Mir.Linked) (code : Code) (i : Nat) (hi : i < code.entries.size) :
    (∃ m, l.funcs[m]? = some i ∧ (objectNames l code)[i]'(by rw [names_size]; exact hi) = m) ∨
      (objectNames l code)[i]'(by rw [names_size]; exact hi) = s!"__ccomp_dispatch.{i}" := by
  rw [names_getElem l code i hi]
  generalize hm : (filled l code)[i]'(by rw [fill_size, Array.size_replicate]; exact hi) = o
  rcases o with _ | m
  · exact .inr rfl
  · refine .inl ⟨m, filled_some l code i m ?_, rfl⟩
    rw [Array.getElem?_eq_getElem (by rw [fill_size, Array.size_replicate]; exact hi), hm]

theorem zipIdx_weight (d : Nat → String) (B : Nat) (l : List (Option String)) (k : Nat)
    (hd : ∀ i, i < k + l.length → (d i).utf8ByteSize ≤ B) :
    ((l.zipIdx k).map (fun x => (x.1.getD (d x.2)).utf8ByteSize)).sum ≤
      (l.map fun o => (o.map String.utf8ByteSize).getD 0).sum + B * l.length := by
  induction l generalizing k with
  | nil => simp
  | cons o l ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons]
    have := ih (k + 1) (fun i hi => hd i (by simp at hi ⊢; omega))
    have h0 := hd k (by simp)
    rcases o with _ | m <;> simp at h0 ⊢ <;> rw [Nat.mul_succ] <;> omega

theorem names_weight (l : Mir.Linked) (code : Code) (hN : code.entries.size < 2 ^ 20) :
    ((objectNames l code).toList.map String.utf8ByteSize).sum ≤
      (l.funcs.toList.map (·.1.utf8ByteSize)).sum + 96 * code.entries.size := by
  rw [objectNames_eq, Array.toList_mapIdx, List.mapIdx_eq_zipIdx_map, List.map_map]
  have h1 := zipIdx_weight (fun i => s!"__ccomp_dispatch.{i}") 96 (filled l code).toList 0
    (fun i hi => dispatch_size i (by simp [fill_size] at hi; omega))
  have h2 : weight (filled l code) ≤ weight (Array.replicate code.entries.size none) +
      (l.funcs.toList.map (·.1.utf8ByteSize)).sum :=
    fill_weight l.funcs.toList (Array.replicate code.entries.size none)
  have h3 : weight (Array.replicate code.entries.size none) = 0 := by
    simp [weight, List.map_replicate]
  simp only [weight] at h2 h3
  simp only [Array.length_toList, fill_size, Array.size_replicate] at h1
  have : (List.map ((fun x => x.utf8ByteSize) ∘ fun x => match x with | (a, i) => a.getD s!"__ccomp_dispatch.{i}")
      (filled l code).toList.zipIdx) =
      ((filled l code).toList.zipIdx.map (fun x => (x.1.getD s!"__ccomp_dispatch.{x.2}").utf8ByteSize)) := by
    apply List.map_congr_left; intro x _; rfl
  rw [this]
  omega

theorem digitChar_inj (a b : Nat) (ha : a < 10) (_hb : b < 10) (h : Nat.digitChar a = Nat.digitChar b) :
    a = b := by
  have e : ∀ k, k < 10 → Nat.digitChar k = Nat.digitChar b → k = b := by
    intro k hk hkb
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · rw [(Nat.digitChar_eq_zero (n := 0)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_one (n := 1)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_two (n := 2)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_three (n := 3)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_four (n := 4)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_five (n := 5)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_six (n := 6)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_seven (n := 7)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_eight (n := 8)).2 rfl] at hkb; simp at hkb; omega
    · rw [(Nat.digitChar_eq_nine (n := 9)).2 rfl] at hkb; simp at hkb; omega
    · omega
  exact e a ha h

theorem toDigits_inj : ∀ (n m : Nat), Nat.toDigits 10 n = Nat.toDigits 10 m → n = m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m h
    rw [Nat.toDigits_eq_ite (by decide), Nat.toDigits_eq_ite (b := 10) (n := m) (by decide)] at h
    by_cases hn : n < 10 <;> by_cases hm : m < 10 <;> simp only [hn, hm, ite_true, ite_false] at h
    · exact digitChar_inj n m hn hm (by simpa using h)
    · have := congrArg List.length h
      simp only [List.length_singleton, List.length_append] at this
      have := List.length_pos_of_ne_nil (Nat.toDigits_ne_nil (b := 10) (n := m / 10)); omega
    · have := congrArg List.length h
      simp only [List.length_singleton, List.length_append] at this
      have := List.length_pos_of_ne_nil (Nat.toDigits_ne_nil (b := 10) (n := n / 10)); omega
    · obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      have e1 := ih (n / 10) (by omega) (m / 10) h1
      have e2 := digitChar_inj _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (by simpa using h2)
      omega

theorem dispatch_inj (i j : Nat) (h : s!"__ccomp_dispatch.{i}" = s!"__ccomp_dispatch.{j}") : i = j := by
  have := congrArg String.toList h
  simp [Nat.toString_eq_repr, Nat.toList_repr] at this
  exact toDigits_inj i j this

theorem dispatch_prefix (i : Nat) : (s!"__ccomp_dispatch.{i}").startsWith "__ccomp_dispatch." := by
  rw [String.startsWith_string_iff]
  simp only [String.toList_append]
  exact List.prefix_append _ _

theorem objectNames_ok (l : Mir.Linked) (code : Code) (h : ∀ p ∈ l.funcs.toList, NameOk p.1) :
    ∀ x ∈ (objectNames l code).toList, NameOk x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < code.entries.size := by simpa [names_size] using hi
  rcases names_cases l code i hi' with ⟨m, hm, he⟩ | he
  · simp only [Array.getElem_toList]; rw [he]
    exact h (m, i) (Std.HashMap.mem_toList_iff_getElem?_eq_some.2 hm)
  · simp only [Array.getElem_toList]; rw [he]; exact nameOk_dispatch i

/-! ## What is read back -/

/-- The written section `i` is read back as section `i + 1`: its name and its bytes. -/
theorem secs_getElem_user (S : List Section) (Y : List Sym) (i : Nat) (hi : i < S.length) :
    ∃ o, (secs S Y)[i + 1]? = some ⟨userHdr S ((S[i], o), i), nameBits S[i].name, toBits S[i].data⟩ := by
  obtain ⟨o, ho⟩ := secOffs_getElem? S i hi
  refine ⟨o, ?_⟩
  have hu : (userSecs S)[i]? = some ((S[i], o), i) := by
    simp [userSecs, List.getElem?_zipIdx, List.getElem?_zip_eq_some, ho, hi]
  simp only [secs]
  rw [List.getElem?_append_left (by simp [userSecs, secOffs_length]; omega),
    List.getElem?_cons_succ, List.getElem?_map, hu]
  simp [userSec, toBits_eq]

/-- The written symbol `j` is read back as symbol `j + 1`: its name, value, size, kind,
section and global binding. -/
theorem syms_getElem (Y : List Sym) (j : Nat) (hj : j < Y.length) :
    ∃ off, (syms Y)[j + 1]? = some (symOf (Y[j], off)) ∧
      (symOf (Y[j], off)).name = nameBits Y[j].name ∧ (symOf (Y[j], off)).raw.value = Y[j].value ∧
      (symOf (Y[j], off)).raw.size = Y[j].size ∧ (symOf (Y[j], off)).kind = Y[j].kind % 16 ∧
      (symOf (Y[j], off)).binding = 1 + Y[j].kind / 16 ∧
      (symOf (Y[j], off)).raw.sectionIndex = shndx Y[j] := by
  have hl : j < (soffs Y).length := by simp [soffs, strOffs_length]; exact hj
  refine ⟨(soffs Y)[j], ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [syms, hj, hl]
  · simp [symOf, ObjectSymbol.kind]
  · simp [symOf, ObjectSymbol.binding]; omega

/-! ## The object stage -/

/-- What `Target.object` needs of its inputs: NUL-free function names, and 64-bit function
offsets, image base and control-block address. -/
structure ObjectInputs (l : Mir.Linked) (code : Code) : Prop where
  names : ∀ p ∈ l.funcs.toList, NameOk p.1
  entries : ∀ e ∈ code.entries.toList, e < 2 ^ 64
  base : l.dataBase < 2 ^ 64
  ctl : l.data[ctlSymbol]?.getD dataBase < 2 ^ 64

theorem object_size (arch : Arch) (l : Mir.Linked) (code : Code) :
    (object arch l code).size =
      shOff (objectSections l code) (objectSymbols l code) + 64 * (2 + 5) := by
  rw [object, size_eq, writeRelocatable_toList, model_length]; rfl

theorem section_size_le (S : List Section) (i : Nat) (hi : i < S.length) :
    S[i].data.size ≤ (secBytes 64 S).length := by
  obtain ⟨o, ho⟩ := secOffs_getElem? S i hi
  obtain ⟨_, h1, h2, -⟩ := secBytes_drop 64 S i o ho
  omega

theorem object_fits (arch : Arch) {l : Mir.Linked} {code : Code} (h : ObjectInputs l code)
    (hsize : (object arch l code).size < 2 ^ 32) :
    Fits arch.machine 0 (objectSections l code) (objectSymbols l code) := by
  rw [object_size] at hsize
  have hle := shstrOff_le (objectSections l code) (objectSymbols l code)
  have hcode : code.bytes.size ≤ (secBytes 64 (objectSections l code)).length :=
    section_size_le (objectSections l code) 0 (by simp [objectSections])
  have himg : l.image.size ≤ (secBytes 64 (objectSections l code)).length :=
    section_size_le (objectSections l code) 1 (by simp [objectSections])
  simp only [noteOff, symOff, strOff, shstrOff] at hle
  have hlen : (objectSections l code).length = 2 := rfl
  refine ⟨by cases arch <;> decide, by simp, by simp [objectSections],
    by rw [hlen]; exact hsize, ?_, ?_⟩
  · intro s hs
    simp only [objectSections, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨nameOk_of_chars _ (by simp), by simp, by simp, by simp [validSectionAlignment]⟩
    · exact ⟨nameOk_of_chars _ (by simp), by simp, by simp, by simp [validSectionAlignment]⟩
  · have names := objectNames_ok l code h.names
    intro y hy
    simp only [objectSymbols, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hy
    rcases hy with ⟨⟨n, s, e⟩, hm, rfl⟩ | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨hn, hse⟩ := List.of_mem_zip hm
      obtain ⟨hs, he⟩ := List.of_mem_zip hse
      have hs' := h.entries s hs
      have he' : e < 2 ^ 64 := by
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h.entries e (List.mem_of_mem_drop he)
        · omega
      refine ⟨names n hn, by simp, hs', by simp only; omega, ?_⟩
      intro i hi; simp only [Option.some.injEq] at hi; subst hi; simp [objectSections]
    · exact ⟨nameOk_of_chars _ (by simp), by simp, by simp, by simp only; omega,
        fun i hi => by simp only [Option.some.injEq] at hi; subst hi; simp [objectSections]⟩
    · exact ⟨nameOk_of_chars _ (by simp), by simp, h.base, by simp, by simp⟩
    · exact ⟨nameOk_of_chars _ (by simp), by simp, by simp only; omega, by simp, by simp⟩
    · exact ⟨nameOk_of_chars _ (by simp), by simp, by simp [memSize], by simp, by simp⟩
    · exact ⟨nameOk_of_chars _ (by simp), by simp, h.ctl, by simp, by simp⟩

/-- **The object stage round trip.** The ELF reader gives back the object `Target.object`
writes: `.text` holds the code bytes, `.rodata.ccomp` the memory image, and the symbols are
one `FUNC` per function and the startup symbols, as `objectSections` and `objectSymbols`
list them. The object must be under 4 GiB. -/
theorem readObject_object (arch : Arch) {l : Mir.Linked} {code : Code} (h : ObjectInputs l code)
    (hsize : (object arch l code).size < 2 ^ 32) :
    readObject (toBits (object arch l code)) =
      some (expected arch.machine 0 (objectSections l code) (objectSymbols l code)) :=
  readObject_writeRelocatable (object_fits arch h hsize)

end Silmaril.Compile.Target.ObjectCorrect
