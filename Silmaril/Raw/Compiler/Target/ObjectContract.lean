module

public meta import Mathlib.Data.List.Nodup
public import Silmaril.Compiler.Contract.Defs
public import Silmaril.Compiler.Target.ObjectCorrect.Defs
/-! # The object stage meets `Contract.object`

`object_contract` proves `Contract.object` for the object stage as the registry runs it
(`Target.object .x86_64` of the backend's bytes and function offsets): the bytes read back
with `Formats.ELF.readObject` (`ObjectCorrect.readObject_object`) are an x86-64
relocatable object with no relocations whose `.text` is the code, whose `.rodata.ccomp`
is the memory image, with a global `FUNC` symbol at its offset for every named function,
the startup symbols, and pairwise distinct symbol names.

The contract's size hypotheses bound the object under 4 GiB (`stage_size`), and its name
hypotheses (no NUL, not reserved, one name per function index) make the names the writer
emits NUL-free and distinct.
-/

@[expose] public section

namespace Silmaril.Compile.Target.ObjectContract

open Silmaril.Machine
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Write
open ObjectCorrect

/-! ## The contract's byte views -/

theorem toList_loop (bs : ByteArray) : ∀ k i r, bs.size - i = k →
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro k
  induction k with
  | zero =>
    intro i r hk
    rw [ByteArray.toList.loop, ite_eq_right (by omega), List.drop_eq_nil_of_le (by
      simp only [Array.length_toList]; simp only [ByteArray.size] at hk; omega)]
    simp
  | succ k ih =>
    intro i r hk
    rw [ByteArray.toList.loop, ite_eq_left (by omega), ih (i + 1) _ (by omega)]
    have hi : i < bs.data.toList.length := by
      simp only [Array.length_toList]; simp only [ByteArray.size] at hk; omega
    rw [List.drop_eq_getElem_cons hi]
    simp [ByteArray.get!]
    exact getElem!_pos bs.data i (by simpa using hi)

theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop bs _ 0 [] rfl]; simp

theorem elfBytes_eq (b : ByteArray) : Contract.elfBytes b = toBits b := by
  apply Array.ext'
  simp [Contract.elfBytes, toBits, byteArray_toList]

theorem nameBytes_eq (s : String) : Contract.nameBytes s = nameBits s := by
  simp [Contract.nameBytes, nameBits, byteArray_toList]

theorem toBits_toBytes (l : List (BitVec 8)) : toBits (toBytes l) = l.toArray := by
  apply Array.ext'
  simp only [toBits, toBytes, Array.toList_map, List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro b _
  apply BitVec.eq_of_toNat_eq
  simp

theorem nameBits_inj {s t : String} (h : nameBits s = nameBits t) : s = t := by
  have h1 : s.toUTF8.data.toList = t.toUTF8.data.toList :=
    List.map_injective_iff.2 (fun a b hab => UInt8.toBitVec_inj.1 hab) h
  have h2 : s.toUTF8 = t.toUTF8 := by
    cases hs : s.toUTF8; cases ht : t.toUTF8
    rw [hs, ht] at h1
    simp only [Array.toList_inj] at h1
    rw [h1]
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray] at h2
  exact String.toByteArray_inj.1 h2

/-! ## The stage's code and symbols -/

/-- The code the object stage wraps: the backend's bytes and function offsets. -/
abbrev stageCode (q : Lir.Prog (Fin 9)) (img : X86.Backend.Image) : Code :=
  ⟨toBytes img.code, ((List.range q.funcs.length).map img.layout.func).toArray⟩

/-- The symbols the startup code reads, after the function symbols. -/
abbrev startupSyms (l : Mir.Linked) : List Sym := [
    { name := "__ccomp_image", sec := some 1, value := 0, size := l.image.size, kind := 1 },
    { name := "__ccomp_image_base", sec := none, value := l.dataBase, size := 0, kind := 0 },
    { name := "__ccomp_image_size", sec := none, value := l.image.size, size := 0, kind := 0 },
    { name := "__ccomp_lmem_size", sec := none, value := memSize, size := 0, kind := 0 },
    { name := "__ccomp_ctl", sec := none, value := l.data[ctlSymbol]?.getD dataBase, size := 0,
      kind := 0 } ]

theorem ends_length (code : Code) :
    code.entries.size ≤ (code.entries.toList.drop 1 ++ [code.bytes.size]).length := by
  simp; omega

/-- The function symbols of the object. -/
def funcSyms (l : Mir.Linked) (code : Code) : List Sym :=
  ((objectNames l code).toList.zip (code.entries.toList.zip
    (code.entries.toList.drop 1 ++ [code.bytes.size]))).map
    fun (n, (s, e)) => ({ name := n, sec := some 0, value := s, size := e - s, kind := 2 } : Sym)

theorem objectSymbols_eq (l : Mir.Linked) (code : Code) :
    objectSymbols l code = funcSyms l code ++ startupSyms l := rfl

theorem funcSyms_length (l : Mir.Linked) (code : Code) :
    (funcSyms l code).length = code.entries.size := by
  have := ends_length code
  simp only [funcSyms, List.length_map, List.length_zip, Array.length_toList, names_size]
  omega

theorem funcSyms_getElem (l : Mir.Linked) (code : Code) (i : Nat) (hi : i < code.entries.size) :
    ∃ sz, (funcSyms l code)[i]'(by rw [funcSyms_length]; exact hi) =
      { name := (objectNames l code)[i]'(by rw [names_size]; exact hi), sec := some 0,
        value := code.entries[i], size := sz, kind := 2 } := by
  simp only [funcSyms, List.getElem_map, List.getElem_zip, Array.getElem_toList]
  exact ⟨_, rfl⟩

theorem funcSyms_names (l : Mir.Linked) (code : Code) :
    (funcSyms l code).map (·.name) = (objectNames l code).toList := by
  apply List.ext_getElem
  · rw [List.length_map, funcSyms_length, Array.length_toList, names_size]
  · intro i h1 h2
    have hi : i < code.entries.size := by
      rw [← funcSyms_length l code]; simpa only [List.length_map] using h1
    obtain ⟨sz, h⟩ := funcSyms_getElem l code i hi
    simp only [List.getElem_map, h, Array.getElem_toList]

/-- Function names and generated dispatcher names are distinct at distinct indices. -/
theorem names_nodup (l : Mir.Linked) (code : Code)
    (hnames : ∀ n i, l.funcs[n]? = some i → ¬ Contract.reservedName n) :
    (objectNames l code).toList.Nodup := by
  apply List.nodup_iff_injective_getElem.2
  intro i j hij
  apply Fin.ext
  have hi : i.val < code.entries.size := by simpa [names_size] using i.isLt
  have hj : j.val < code.entries.size := by simpa [names_size] using j.isLt
  simp only [Array.getElem_toList] at hij
  rcases names_cases l code i.val hi with ⟨n, hn, he⟩ | he <;>
    rcases names_cases l code j.val hj with ⟨m, hm, hf⟩ | hf
  · rw [he, hf] at hij
    rw [hij, hm] at hn
    exact (Option.some.inj hn).symm
  · rw [he, hf] at hij
    exact False.elim (hnames n i.val hn (.inr (by rw [hij]; exact dispatch_prefix j.val)))
  · rw [he, hf] at hij
    exact False.elim (hnames m j.val hm (.inr (by rw [← hij]; exact dispatch_prefix i.val)))
  · rw [he, hf] at hij
    exact dispatch_inj _ _ hij

/-- Startup symbols cannot collide with user functions or generated dispatchers. -/
theorem names_disjoint_startup (l : Mir.Linked) (code : Code)
    (hnames : ∀ n i, l.funcs[n]? = some i → ¬ Contract.reservedName n) :
    ∀ x ∈ (objectNames l code).toList, ∀ y ∈ (startupSyms l).map (·.name), x ≠ y := by
  intro x hx y hy hxy
  subst y
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < code.entries.size := by simpa [names_size] using hi
  simp only [Array.getElem_toList] at hy
  rcases names_cases l code i hi' with ⟨n, hn, he⟩ | he
  · rw [he] at hy
    exact hnames n i hn (.inl (by simpa [startupSyms] using hy))
  · rw [he] at hy
    have hp := dispatch_prefix i
    simp only [startupSyms, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hy
    rcases hy with h | h | h | h | h <;> rw [h] at hp <;>
      simp [String.startsWith_string_iff] at hp

/-- The non-null symbol names read back are exactly the written symbol names. -/
theorem syms_names (Y : List Sym) :
    ((syms Y).drop 1).map (·.name) = (Y.map (·.name)).map nameBits := by
  simp only [syms, List.drop_succ_cons, List.drop_zero, List.map_map]
  have hlen : (soffs Y).length = Y.length := by simp [soffs, strOffs_length]
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_zip]
    rfl

/-! ## The size of the object -/

theorem padN_lt (c a : Nat) (ha : 0 < a) : padN c a < a := by
  unfold padN
  split
  · exact Nat.mod_lt _ ha
  · omega

theorem secBytes_length_le (c : Nat) (S : List Section) :
    (secBytes c S).length ≤ (S.map fun s => s.data.size + max s.align 1).sum := by
  induction S generalizing c with
  | nil => simp [secBytes]
  | cons s S ih =>
    have := padN_lt c (max s.align 1) (by omega)
    have := ih (c + padN c (max s.align 1) + s.data.size)
    simp only [secBytes, List.length_append, List.length_replicate, Array.length_toList,
      ByteArray.size_data, List.map_cons, List.sum_cons]
    omega

theorem nameL_length (n : String) : (nameL n).length = n.utf8ByteSize + 1 := by
  simp only [nameL, List.length_append, List.length_singleton, Array.length_toList]
  rw [show n.toUTF8.data.size = n.toUTF8.size from rfl, String.toUTF8_eq_toByteArray,
    String.size_toByteArray]

theorem flatMap_nameL_length (ns : List String) :
    (ns.flatMap nameL).length = (ns.map String.utf8ByteSize).sum + ns.length := by
  induction ns with
  | nil => simp
  | cons n ns ih => simp only [List.flatMap_cons, List.length_append, ih, nameL_length,
      List.map_cons, List.sum_cons, List.length_cons]; omega

theorem literal_size (s : String) (n : Nat) (h : s.toList.length = n) : s.utf8ByteSize ≤ 4 * n := by
  have := utf8ByteSize_le s
  rw [← String.length_toList, h] at this
  exact this

theorem code_size (l : Mir.Linked) (c : Code)
    (hcode : c.bytes.size < 2 ^ 30) (himg : l.image.size < 2 ^ 30)
    (hq : c.entries.size < 2 ^ 20)
    (hsum : (l.funcs.toList.map fun (n, _) => n.utf8ByteSize).sum < 2 ^ 28) :
    (object .x86_64 l c).size < 2 ^ 32 := by
  rw [object_size]
  -- the section contents
  have hsec : (secBytes 64 (objectSections l c)).length ≤
      c.bytes.size + 16 + (l.image.size + 16) := by
    have := secBytes_length_le 64 (objectSections l c)
    simpa [objectSections] using this
  -- the symbol names
  have hnames := names_weight l c hq
  have hsum' : (l.funcs.toList.map (·.1.utf8ByteSize)).sum < 2 ^ 28 := hsum
  have hY : (objectSymbols l c).map (·.name) =
      (objectNames l c).toList ++ (startupSyms l).map (·.name) := by
    rw [objectSymbols_eq, List.map_append, funcSyms_names]
  have hYlen : (objectSymbols l c).length = c.entries.size + 5 := by
    rw [objectSymbols_eq, List.length_append, funcSyms_length]; rfl
  have hstr : (strL (objectSymbols l c)).length ≤
      1 + (2 ^ 28 + 96 * c.entries.size) + c.entries.size + 5 * 81 := by
    simp only [strL, List.length_cons, flatMap_nameL_length, hY, List.map_append,
      List.sum_append, List.length_append, Array.length_toList, names_size]
    have h1 := literal_size "__ccomp_image" 13 (by simp)
    have h2 := literal_size "__ccomp_image_base" 18 (by simp)
    have h3 := literal_size "__ccomp_image_size" 18 (by simp)
    have h4 := literal_size "__ccomp_lmem_size" 17 (by simp)
    have h5 := literal_size "__ccomp_ctl" 11 (by simp)
    simp only [startupSyms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    omega
  have hshstr : (shstrL (objectSections l c)).length ≤ 1 + 4 * 66 + 6 := by
    have h1 := literal_size ".text" 5 (by simp)
    have h2 := literal_size ".rodata.ccomp" 13 (by simp)
    have h3 := literal_size ".note.GNU-stack" 15 (by simp)
    have h4 := literal_size ".symtab" 7 (by simp)
    have h5 := literal_size ".strtab" 7 (by simp)
    have h6 := literal_size ".shstrtab" 9 (by simp)
    simp only [shstrL, shNames, objectSections, List.length_cons, flatMap_nameL_length,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.sum_cons,
      List.sum_nil, List.length_nil]
    omega
  have p1 := padN_lt (noteOff (objectSections l c)) 8 (by decide)
  have p2 := padN_lt (shstrOff (objectSections l c) (objectSymbols l c) +
    (shstrL (objectSections l c)).length) 8 (by decide)
  simp only [shOff, shstrOff, strOff, symOff, noteOff, hYlen] at p1 p2 ⊢
  omega

/-! ## The contract -/

theorem nameOk_of_noNul (n : String) (h : '\x00' ∉ n.toList) : NameOk n := by
  apply nameOk_of_chars
  intro c hc hc0
  apply h
  have : c = '\x00' := Char.ext hc0
  exact this ▸ hc

/-- **The object of any code meets the contract's conclusion**, for that code's bytes and
function offsets. -/
theorem object_contract_code (l : Mir.Linked) (c : Code)
    (hnames : ∀ (n : String) (i : Nat), l.funcs[n]? = some i →
      '\x00' ∉ n.toList ∧ ¬ Contract.reservedName n)
    (hinj : ∀ (n m : String) (i : Nat), l.funcs[n]? = some i → l.funcs[m]? = some i → n = m)
    (hcode : c.bytes.size < 2 ^ 30) (himg : l.image.size < 2 ^ 30) (hq : c.entries.size < 2 ^ 20)
    (hsum : (l.funcs.toList.map fun (n, _) => n.utf8ByteSize).sum < 2 ^ 28)
    (hentries : ∀ (i : Nat) (h : i < c.entries.size), c.entries[i] < 2 ^ 64)
    (hbase : l.dataBase < 2 ^ 64)
    (hctl : ∀ a : Nat, l.data[ctlSymbol]? = some a → a < 2 ^ 64) :
    ∃ file, Formats.ELF.readObject (Contract.elfBytes (object .x86_64 l c)) = some file ∧
      file.header.machine = 62 ∧ file.header.fileType = 1 ∧ file.relocations = [] ∧
      Contract.HasSection file ".text" 6 (Contract.elfBytes c.bytes) ∧
      Contract.HasSection file ".rodata.ccomp" 2 (Contract.elfBytes l.image) ∧
      (∀ (n : String) (i : Nat), l.funcs[n]? = some i → (h : i < c.entries.size) →
        Contract.HasSymbol file n 2 (some ".text") c.entries[i]) ∧
      Contract.HasSymbol file "__ccomp_image" 1 (some ".rodata.ccomp") 0 ∧
      Contract.HasSymbol file "__ccomp_image_base" 0 none l.dataBase ∧
      Contract.HasSymbol file "__ccomp_image_size" 0 none l.image.size ∧
      Contract.HasSymbol file "__ccomp_lmem_size" 0 none memSize ∧
      (∀ a : Nat, l.data[ctlSymbol]? = some a →
        Contract.HasSymbol file "__ccomp_ctl" 0 none a) ∧
      ((file.symbols.drop 1).map (·.name)).Nodup := by
  have inputs : ObjectInputs l c := by
    refine ⟨fun p hp => ?_, fun e he => ?_, hbase, ?_⟩
    · exact nameOk_of_noNul p.1
        (hnames p.1 p.2 (Std.HashMap.mem_toList_iff_getElem?_eq_some.1 hp)).1
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      have hi' : i < c.entries.size := by simpa using hi
      simpa using hentries i hi'
    · cases h : l.data[ctlSymbol]? with
      | none => simp [dataBase]
      | some a => simpa using hctl a h
  have hread := readObject_object .x86_64 inputs (code_size l c hcode himg hq hsum)
  generalize hS : objectSections l c = S at hread
  generalize hYd : objectSymbols l c = Y at hread
  have hS0 : S[0]? = some { name := ".text", flags := 6, align := 16, data := c.bytes } := by
    rw [← hS]; rfl
  have hS1 : S[1]? = some { name := ".rodata.ccomp", flags := 2, align := 16, data := l.image } := by
    rw [← hS]; rfl
  have hSlen : S.length = 2 := by rw [← hS]; rfl
  obtain ⟨o0, h0⟩ := secs_getElem_user S Y 0 (by omega)
  obtain ⟨o1, h1⟩ := secs_getElem_user S Y 1 (by omega)
  have e0 : S[0] = { name := ".text", flags := 6, align := 16, data := c.bytes } := by
    simpa [List.getElem?_eq_getElem (by omega : 0 < S.length)] using hS0
  have e1 : S[1] = { name := ".rodata.ccomp", flags := 2, align := 16, data := l.image } := by
    simpa [List.getElem?_eq_getElem (by omega : 1 < S.length)] using hS1
  rw [e0] at h0
  rw [e1] at h1
  let textPart : ObjectSection :=
    ⟨userHdr S ((S[0], o0), 0), nameBits ".text", toBits c.bytes⟩
  let imagePart : ObjectSection :=
    ⟨userHdr S ((S[1], o1), 1), nameBits ".rodata.ccomp", toBits l.image⟩
  have hYlen : Y.length = c.entries.size + 5 := by
    rw [← hYd, objectSymbols_eq, List.length_append, funcSyms_length]; rfl
  have hYf : ∀ i (hi : i < c.entries.size), ∃ sz, Y[i]'(by omega) =
      { name := (objectNames l c)[i]'(by rw [names_size]; exact hi),
        sec := some 0, value := c.entries[i], size := sz, kind := 2 } := by
    intro i hi
    obtain ⟨sz, h⟩ := funcSyms_getElem l c i hi
    refine ⟨sz, ?_⟩
    subst hYd
    simp only [objectSymbols_eq]
    rw [List.getElem_append_left (by rw [funcSyms_length]; exact hi), h]
  have hYs : ∀ k (hk : k < 5), Y[c.entries.size + k]'(by omega) = (startupSyms l)[k] := by
    intro k hk
    subst hYd
    simp only [objectSymbols_eq]
    rw [List.getElem_append_right (by rw [funcSyms_length]; omega)]
    simp only [funcSyms_length, Nat.add_sub_cancel_left]
  have symAt : ∀ j (hj : j < Y.length), ∃ sym ∈ (expected 62 0 S Y).symbols,
      sym.name = nameBits Y[j].name ∧ sym.kind = Y[j].kind % 16 ∧
      sym.binding = 1 + Y[j].kind / 16 ∧ sym.raw.value = Y[j].value ∧
      sym.raw.sectionIndex = shndx Y[j] := by
    intro j hj
    obtain ⟨off, hget, hn, hv, -, hk, hb, hsec⟩ := syms_getElem Y j hj
    exact ⟨_, List.mem_of_getElem? hget, hn, hk, hb, hv, hsec⟩
  refine ⟨expected 62 0 S Y, by rw [elfBytes_eq]; exact hread, rfl, rfl, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨_, List.mem_of_getElem? h0, by rw [nameBytes_eq], rfl, rfl, (elfBytes_eq _).symm⟩
  · exact ⟨_, List.mem_of_getElem? h1, by rw [nameBytes_eq], rfl, rfl, (elfBytes_eq _).symm⟩
  · intro n i hn hi
    obtain ⟨sz, hy⟩ := hYf i hi
    obtain ⟨sym, hmem, hname, hkind, hbind, hval, hsec⟩ := symAt i (by omega)
    rw [hy] at hname hkind hbind hval hsec
    refine ⟨sym, hmem, ?_, hkind, by simpa using hbind, hval, ⟨textPart, ?_, ?_⟩⟩
    · rw [hname, nameBytes_eq, names_funcs l _ hinj n i hn hi]
    · simp only [Contract.symSection, hsec, shndx, expected]
      simpa only [textPart, e0] using h0
    · simp [textPart, nameBytes_eq]
  · obtain ⟨sym, hm, hn, hk, hb, hv, hs⟩ := symAt (c.entries.size + 0) (by omega)
    rw [hYs 0 (by decide)] at hn hk hb hv hs
    simp only [startupSyms, List.getElem_cons_zero] at hn hk hb hv hs
    refine ⟨sym, hm, ?_, ?_, ?_, ?_, ⟨imagePart, ?_, ?_⟩⟩
    · exact hn.trans (nameBytes_eq _).symm
    · simpa using hk
    · simpa using hb
    · exact hv
    · simp only [Contract.symSection, hs, shndx, expected]
      simpa only [imagePart, e1] using h1
    · simp [imagePart, nameBytes_eq]
  · obtain ⟨sym, hm, hn, hk, hb, hv, hs⟩ := symAt (c.entries.size + 1) (by omega)
    rw [hYs 1 (by decide)] at hn hk hb hv hs
    simp only [startupSyms, List.getElem_cons_zero, List.getElem_cons_succ] at hn hk hb hv hs
    refine ⟨sym, hm, ?_, ?_, ?_, ?_, ?_⟩
    · exact hn.trans (nameBytes_eq _).symm
    · simpa using hk
    · simpa using hb
    · exact hv
    · simpa [shndx] using hs
  · obtain ⟨sym, hm, hn, hk, hb, hv, hs⟩ := symAt (c.entries.size + 2) (by omega)
    rw [hYs 2 (by decide)] at hn hk hb hv hs
    simp only [startupSyms, List.getElem_cons_zero, List.getElem_cons_succ] at hn hk hb hv hs
    refine ⟨sym, hm, ?_, ?_, ?_, ?_, ?_⟩
    · exact hn.trans (nameBytes_eq _).symm
    · simpa using hk
    · simpa using hb
    · exact hv
    · simpa [shndx] using hs
  · obtain ⟨sym, hm, hn, hk, hb, hv, hs⟩ := symAt (c.entries.size + 3) (by omega)
    rw [hYs 3 (by decide)] at hn hk hb hv hs
    simp only [startupSyms, List.getElem_cons_zero, List.getElem_cons_succ] at hn hk hb hv hs
    refine ⟨sym, hm, ?_, ?_, ?_, ?_, ?_⟩
    · exact hn.trans (nameBytes_eq _).symm
    · simpa using hk
    · simpa using hb
    · exact hv
    · simpa [shndx] using hs
  · intro a ha
    obtain ⟨sym, hm, hn, hk, hb, hv, hs⟩ := symAt (c.entries.size + 4) (by omega)
    rw [hYs 4 (by decide)] at hn hk hb hv hs
    simp only [startupSyms, List.getElem_cons_zero, List.getElem_cons_succ] at hn hk hb hv hs
    refine ⟨sym, hm, ?_, ?_, ?_, ?_, ?_⟩
    · exact hn.trans (nameBytes_eq _).symm
    · simpa using hk
    · simpa using hb
    · simpa [ha] using hv
    · simpa [shndx] using hs
  · rw [show (expected 62 0 S Y).symbols = syms Y from rfl, syms_names, ← hYd,
      objectSymbols_eq, List.map_append, funcSyms_names]
    apply List.Nodup.map (fun _ _ h => nameBits_inj h)
    apply List.nodup_append.2
    refine ⟨names_nodup l _ (fun n i hn => (hnames n i hn).2), ?_,
      names_disjoint_startup l _ (fun n i hn => (hnames n i hn).2)⟩
    simp [startupSyms]

/-- The code `Stage.object` wraps: the verified backend's bytes and offsets, or the native
emitter's. -/
def codeOf (q : Lir.Prog (Fin 9)) : X86.Backend.Image ⊕ (ByteArray × Array Nat) → Code
  | .inl img => stageCode q img
  | .inr (bytes, entries) => ⟨bytes, entries⟩

/-- **The object stage meets its contract**, for both kinds of code. -/
theorem object_contract (f : Mir.Linked → Lir.Prog (Fin 9) →
      X86.Backend.Image ⊕ (ByteArray × Array Nat) → ByteArray)
    (hf : ∀ l q x, f l q x = object .x86_64 l (codeOf q x)) : Contract.object f := by
  intro l q x hnames hinj hcode himg hq hsum hentries hbase hctl
  rw [hf]
  cases x with
  | inl img =>
    have hb : (stageCode q img).bytes.size = img.code.length := by
      simp [toBytes, ByteArray.size]
    obtain ⟨file, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
      object_contract_code l (stageCode q img) hnames hinj
        (by simpa [hb, Contract.objectCode] using hcode) himg (by simpa [Contract.objectCode] using hq)
        hsum (fun i h => by simpa [Contract.objectCode] using hentries i (by simpa [Contract.objectCode] using h))
        hbase hctl
    refine ⟨file, h1, h2, h3, h4, ?_, h6, fun n i hn h => ?_, h8, h9, h10, h11, h12, h13⟩
    · simpa [Contract.objectCode, elfBytes_eq, toBits_toBytes] using h5
    · exact h7 n i hn h
  | inr p =>
    obtain ⟨bytes, entries⟩ := p
    have hb : (Contract.elfBytes bytes).size = bytes.size := by
      rw [elfBytes_eq, toBits, Array.size_map]; rfl
    exact object_contract_code l ⟨bytes, entries⟩ hnames hinj
      (by simpa [Contract.objectCode, hb] using hcode) himg hq hsum hentries hbase hctl

end Silmaril.Compile.Target.ObjectContract
