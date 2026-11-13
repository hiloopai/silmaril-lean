module

public import Silmaril.Compiler.Core.Spec.Defs

/-! # The argument block of the specification, byte by byte

`Spec.argBlock base args` is what the loader writes at linear address `base`: the `argc + 1`
pointer words of `argv` (the last null), then the strings, each null-terminated. For the
arguments `ArgsOk` accepts (printable ASCII), every character is one UTF-8 byte, and this file
gives the block in closed form (`argBlock_eq`): the word of slot `i` is `le8 (strAddr base args i)`
(`argBlock_slot`), the null word ends the array (`argBlock_slot_null`), and string `i` is at
`strAddr base args i` with its bytes and terminator (`argBlock_char`, `argBlock_nul`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgBlock

open Silmaril.Compile.Core.Spec

/-- Every character is ASCII: one UTF-8 byte. -/
def Ascii (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 128

/-- The bytes of an ASCII string. -/
def bytesOf (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

theorem utf8EncodeChar_ascii {c : Char} (h : c.toNat < 128) :
    String.utf8EncodeChar c = [c.toNat.toUInt8] := by
  have hv : c.val.toNat < 128 := h
  rw [String.utf8EncodeChar_eq_singleton (by simp [Char.utf8Size, UInt32.le_iff_toNat_le]; omega)]
  rfl

theorem flatMap_utf8EncodeChar_ascii {cs : List Char} (h : ∀ c ∈ cs, c.toNat < 128) :
    cs.flatMap String.utf8EncodeChar = cs.map fun c => c.toNat.toUInt8 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, utf8EncodeChar_ascii (h c (by simp)),
      ih fun d hd => h d (by simp [hd])]
    rfl

/-- `ByteArray.toList` is the list of the underlying array (as in
`Silmaril.Compression.ByteArray_toList_eq`, restated here to keep the import graph small). -/
theorem byteArray_toList_loop (b : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r hlt ih =>
    have hi : i < b.data.toList.length := by simpa using hlt
    rw [ih, List.drop_eq_getElem_cons hi]
    have hget : b.get! i = b.data.toList[i] := by
      simp [ByteArray.get!, getElem!_pos, hlt]
    simp [hget]
  | case2 i r hlt =>
    have hle : b.data.toList.length ≤ i := by simpa using Nat.le_of_not_lt hlt
    simp [List.drop_eq_nil_of_le hle]

theorem byteArray_toList (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, byteArray_toList_loop]

theorem toUTF8_data_ascii {s : String} (h : Ascii s) : s.toUTF8.data.toList = bytesOf s := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList, List.utf8Encode_eq_toByteArray,
    List.toList_data_toByteArray, bytesOf, flatMap_utf8EncodeChar_ascii h]

theorem toUTF8_ascii {s : String} (h : Ascii s) : s.toUTF8.toList = bytesOf s := by
  rw [byteArray_toList, toUTF8_data_ascii h]

theorem length_bytesOf (s : String) : (bytesOf s).length = s.length := by
  simp [bytesOf, String.length_toList]

theorem utf8ByteSize_ascii {s : String} (h : Ascii s) : s.utf8ByteSize = s.length := by
  rw [← String.size_toByteArray]
  show s.toByteArray.data.toList.length = _
  rw [← String.toUTF8_eq_toByteArray, toUTF8_data_ascii h, length_bytesOf]

/-- `ArgsOk` arguments are ASCII. -/
theorem ascii_of_argsOk {args : List String} (h : ArgsOk args) : ∀ s ∈ args, Ascii s :=
  fun s hs c hc => by have := h.2.1 s hs c hc; omega

@[simp] theorem length_le8 (n : Nat) : (le8 n).length = 8 := by simp [le8]

/-- The string offsets of `argBlock`, from position `pos` on. -/
def offsets (pos : Nat) : List String → List Nat
  | [] => []
  | s :: ss => pos :: offsets (pos + s.length + 1) ss

theorem foldl_offsets (args : List String) (h : ∀ s ∈ args, Ascii s) (acc : List Nat) (pos : Nat) :
    args.foldl (fun (acc : List Nat × Nat) s => (acc.1 ++ [acc.2], acc.2 + s.utf8ByteSize + 1))
      (acc, pos) = (acc ++ offsets pos args, pos + (args.map fun s => s.length + 1).sum) := by
  induction args generalizing acc pos with
  | nil => simp [offsets]
  | cons s ss ih =>
    simp only [List.foldl_cons]
    rw [utf8ByteSize_ascii (h s (by simp)), ih (fun t ht => h t (by simp [ht]))]
    simp [offsets]
    omega

/-- The linear address of string `i` in the block at `base`. -/
def strAddr (base : Nat) (args : List String) (i : Nat) : Nat :=
  base + 8 * (args.length + 1) + ((args.take i).map fun s => s.length + 1).sum

theorem offsets_eq (pos : Nat) (args : List String) :
    offsets pos args = (List.range args.length).map fun i =>
      pos + ((args.take i).map fun s => s.length + 1).sum := by
  induction args generalizing pos with
  | nil => rfl
  | cons s ss ih =>
    rw [offsets, ih, List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero,
      List.map_map, List.cons.injEq, true_and]
    apply List.map_congr_left
    intro i _
    simp [List.take_succ_cons]
    omega

/-- The block in closed form, for ASCII arguments. -/
theorem argBlock_eq (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) :
    argBlock base args =
      ((List.range args.length).map (strAddr base args)).flatMap le8 ++ le8 0 ++
        args.flatMap fun s => bytesOf s ++ [0] := by
  simp only [argBlock]
  rw [foldl_offsets args h, List.nil_append, offsets_eq]
  congr 1
  exact List.flatMap_congr fun s hs => by rw [toUTF8_ascii (h s hs)]

/-- Dropping the first `i` pieces of a concatenation. -/
theorem drop_sum_flatMap {α β : Type} (g : α → List β) :
    ∀ (l : List α) (i : Nat),
      (l.flatMap g).drop (((l.take i).map fun x => (g x).length).sum) = (l.drop i).flatMap g
  | [], i => by simp
  | x :: xs, 0 => by simp
  | x :: xs, i + 1 => by
    simp only [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons,
      List.drop_succ_cons]
    rw [← List.drop_drop, List.drop_left]
    exact drop_sum_flatMap g xs i

/-- The pointer words of `argv`, the null last. -/
def slots (base : Nat) (args : List String) : List Nat :=
  (List.range args.length).map (strAddr base args) ++ [0]

theorem length_slots (base : Nat) (args : List String) :
    (slots base args).length = args.length + 1 := by simp [slots]

theorem argBlock_eq_slots (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) :
    argBlock base args = (slots base args).flatMap le8 ++ args.flatMap fun s => bytesOf s ++ [0] := by
  rw [argBlock_eq base args h, slots, List.flatMap_append]
  simp

theorem sum_const_take {α : Type} (l : List α) (c i : Nat) (hi : i ≤ l.length) :
    ((l.take i).map fun _ => c).sum = c * i := by
  rw [List.map_const', List.sum_replicate, List.length_take, Nat.min_eq_left hi, smul_eq_mul,
    Nat.mul_comm]

/-- The word of slot `i ≤ argc`. -/
theorem argBlock_word (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) {i : Nat}
    (hi : i ≤ args.length) :
    ((argBlock base args).drop (8 * i)).take 8 = le8 ((slots base args)[i]'(by
      rw [length_slots]; omega)) := by
  have hi' : i < (slots base args).length := by rw [length_slots]; omega
  have hd := drop_sum_flatMap le8 (slots base args) i
  simp only [length_le8] at hd
  rw [sum_const_take _ _ _ (by omega)] at hd
  rw [argBlock_eq_slots base args h, List.drop_append_of_le_length (by
    simp [List.length_flatMap, length_slots]; omega), hd, List.drop_eq_getElem_cons hi',
    List.flatMap_cons, List.append_assoc, List.take_left' (length_le8 _)]

/-- Slot `i < argc` holds the address of string `i`. -/
theorem argBlock_slot (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) {i : Nat}
    (hi : i < args.length) :
    ((argBlock base args).drop (8 * i)).take 8 = le8 (strAddr base args i) := by
  rw [argBlock_word base args h hi.le]
  simp only [slots]
  rw [List.getElem_append_left (by simpa using hi)]
  simp

/-- Slot `argc` is the null pointer. -/
theorem argBlock_slot_null (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) :
    ((argBlock base args).drop (8 * args.length)).take 8 = le8 0 := by
  rw [argBlock_word base args h (Nat.le_refl _)]
  simp [slots]

theorem length_slots_flatMap (base : Nat) (args : List String) :
    ((slots base args).flatMap le8).length = 8 * (args.length + 1) := by
  simp [List.length_flatMap, length_slots, List.sum_replicate, Nat.mul_comm]

/-- From string `i` on, the block is string `i`, its terminator, then the later strings. -/
theorem argBlock_drop_string (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) {i : Nat}
    (hi : i < args.length) :
    (argBlock base args).drop (strAddr base args i - base) =
      bytesOf args[i] ++ [0] ++ (args.drop (i + 1)).flatMap fun s => bytesOf s ++ [0] := by
  have hd := drop_sum_flatMap (fun s => bytesOf s ++ [0]) args i
  simp only [List.length_append, length_bytesOf, List.length_singleton] at hd
  rw [argBlock_eq_slots base args h, strAddr,
    show base + 8 * (args.length + 1) + ((args.take i).map fun s => s.length + 1).sum - base =
      ((slots base args).flatMap le8).length + ((args.take i).map fun s => s.length + 1).sum by
      rw [length_slots_flatMap]; omega,
    ← List.drop_drop, List.drop_left, hd, List.drop_eq_getElem_cons hi, List.flatMap_cons]

/-- Character `j` of string `i`. -/
theorem argBlock_char (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) {i j : Nat}
    (hi : i < args.length) (hj : j < args[i].length) :
    (argBlock base args)[strAddr base args i - base + j]? =
      some (args[i].toList[j]'(by rw [String.length_toList]; exact hj)).toNat.toUInt8 := by
  rw [← List.getElem?_drop, argBlock_drop_string base args h hi, List.append_assoc,
    List.getElem?_append_left (by rw [length_bytesOf]; exact hj), bytesOf, List.getElem?_map,
    List.getElem?_eq_getElem]
  rfl

/-- The terminator of string `i`. -/
theorem argBlock_nul (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) {i : Nat}
    (hi : i < args.length) :
    (argBlock base args)[strAddr base args i - base + args[i].length]? = some 0 := by
  rw [← List.getElem?_drop, argBlock_drop_string base args h hi, List.append_assoc,
    List.getElem?_append_right (by rw [length_bytesOf]), length_bytesOf, Nat.sub_self]
  rfl

/-- The block ends after the last string. -/
theorem length_argBlock (base : Nat) (args : List String) (h : ∀ s ∈ args, Ascii s) :
    (argBlock base args).length = strAddr base args args.length - base := by
  rw [argBlock_eq_slots base args h, List.length_append, length_slots_flatMap, strAddr,
    List.take_length, List.length_flatMap]
  simp only [List.length_append, length_bytesOf, List.length_singleton]
  omega

end Silmaril.Compile.Core.Verified.ArgBlock
