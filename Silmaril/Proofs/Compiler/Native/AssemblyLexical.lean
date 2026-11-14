module

public import Silmaril.Compiler.Native.Assembly.Defs
import Init.Data.Nat.ToString
import Init.Data.Int.ToString

/-! Decimal lexical support for the actual imported assembly parser,
tokenizer and structural line splitter. Public Nat digit/rendering identities
prove the roundtrips; no alternate parser or assumed success is introduced. -/
@[expose] public section
set_option maxHeartbeats 1000000
namespace Silmaril.Compiler.Native.Assembly
open Silmaril.X86

private theorem decimal_fold (text : String) (chars : List Char) (initial : Nat)
    (digits : ∀ c ∈ chars, c.isDigit = true) :
    chars.foldlM (m := Except String)
      (fun n c => do
        let d := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
          else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 10
        if d ≥ 10 then throw s!"invalid integer: {text}"
        return 10 * n + d) initial = .ok (Nat.ofDigitChars 10 chars initial) := by
  induction chars generalizing initial with
  | nil =>
    simp only [List.foldlM_nil, Nat.ofDigitChars_nil]
    rfl
  | cons c cs ih =>
    have digit : c.isDigit = true := digits c (by simp)
    have ascii : ('0' ≤ c && c ≤ '9') = true := digit
    have bounds := Char.isDigit_iff_toNat.mp digit
    have small : ¬ c.toNat - '0'.toNat ≥ 10 := by
      simp only [Char.reduceToNat] at bounds ⊢
      omega
    simpa only [List.foldlM_cons, ascii, ite_true, small, ite_false,
      pure_bind, Nat.ofDigitChars_cons] using
      ih (10 * initial + (c.toNat - '0'.toNat)) (fun d hd => digits d (by simp [hd]))

theorem natural_of_digits (text : String) (nonempty : text.toList ≠ [])
    (digits : ∀ c ∈ text.toList, c.isDigit = true) :
    Silmaril.X86.Assembly.natural text = .ok (Nat.ofDigitChars 10 text.toList 0) := by
  unfold Silmaril.X86.Assembly.natural
  split
  next pair radix chars radixMatch =>
    split at radixMatch
    next suffix shape =>
      have invalid : 'x'.isDigit = true := digits 'x' (by simp [shape])
      contradiction
    next original shape =>
      rcases Prod.mk.inj radixMatch with ⟨rfl, rfl⟩
      have not_empty : text.toList.isEmpty = false := by simpa using nonempty
      simp only [not_empty, Bool.false_eq_true, ite_false]
      exact decimal_fold text text.toList 0 digits

theorem natural_repr (number : Nat) :
    Silmaril.X86.Assembly.natural (Nat.repr number) = .ok number := by
  have digits : ∀ c ∈ (Nat.repr number).toList, c.isDigit = true := by
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) (by simpa using hc)
  rw [natural_of_digits (Nat.repr number) (by simp) digits]
  simp only [Nat.toList_repr, Nat.ofDigitChars_ten_toDigits]

theorem natural_toString (number : Nat) :
    Silmaril.X86.Assembly.natural (toString number) = .ok number :=
  natural_repr number

theorem integer_nat_repr (number : Nat) :
    Silmaril.X86.Assembly.integer [Nat.repr number] = .ok (number : Int) := by
  simp [Silmaril.X86.Assembly.integer, natural_repr]

theorem integer_neg_repr (number : Nat) :
    Silmaril.X86.Assembly.integer ["-", Nat.repr number] = .ok (-(number : Int)) := by
  simp [Silmaril.X86.Assembly.integer, natural_repr]

private theorem digit_not_delimiter (c : Char) (digit : c.isDigit = true) :
    (c = ' ' || c = '\t' || c = '\r') = false ∧
      [',', '[', ']', '+', '-', '*'].contains c = false := by
  constructor
  · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨⟨fun h => by subst c; contradiction,
      fun h => by subst c; contradiction⟩, fun h => by subst c; contradiction⟩
  · simp only [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_cons,
      List.mem_nil_iff, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> contradiction

/-- Digits are consumed by the real tokenizer into the current token buffer. -/
theorem tokenizeChars_digits_append (digits suffix buffer : List Char) (tokens : List String)
    (onlyDigits : ∀ c ∈ digits, c.isDigit = true) :
    Silmaril.X86.Assembly.tokenizeChars (digits ++ suffix) buffer tokens =
      Silmaril.X86.Assembly.tokenizeChars suffix (digits.reverse ++ buffer) tokens := by
  induction digits generalizing buffer with
  | nil => rfl
  | cons c cs ih =>
    have delimiter := digit_not_delimiter c (onlyDigits c (by simp))
    simp only [List.cons_append, Silmaril.X86.Assembly.tokenizeChars,
      delimiter.1, delimiter.2, Bool.false_eq_true, ite_false]
    rw [ih (c :: buffer) (fun d hd => onlyDigits d (by simp [hd]))]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- A nonempty decimal spelling is one complete token in the real tokenizer. -/
theorem tokenizeChars_digits_end (digits buffer : List Char) (tokens : List String)
    (nonempty : digits ≠ []) (onlyDigits : ∀ c ∈ digits, c.isDigit = true) :
    Silmaril.X86.Assembly.tokenizeChars digits buffer tokens =
      (String.ofList (buffer.reverse ++ digits) :: tokens).reverse := by
  have buffered : (digits.reverse ++ buffer).isEmpty = false := by simp [nonempty]
  have consumed := tokenizeChars_digits_append digits [] buffer tokens onlyDigits
  simpa only [List.append_nil, Silmaril.X86.Assembly.tokenizeChars,
    Silmaril.X86.Assembly.flushToken, buffered, Bool.false_eq_true, ite_false,
    List.reverse_append, List.reverse_reverse] using consumed

private theorem repr_digits (number : Nat) :
    ∀ c ∈ (Nat.repr number).toList, c.isDigit = true := by
  intro c hc
  exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) (by simpa using hc)

theorem tokenize_repr (number : Nat) :
    Silmaril.X86.Assembly.tokenize (Nat.repr number) = [Nat.repr number] := by
  unfold Silmaril.X86.Assembly.tokenize
  rw [tokenizeChars_digits_end _ [] [] (by simp) (repr_digits number)]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, String.ofList_toList]

/-- The varying immediate emitted by the native literal compiler has the
expected independent grammar derivation for every actual64-bit word. -/
theorem movabs_repr (value : BitVec 64) :
    Spells ["movabs", "rax", ",", Nat.repr value.toNat] (.plain (.movabs .rax value)) := by
  have parsed := Spells.movabs (destination := "rax") (d := .rax)
    (n := value.toNat) (by cbv) (natural_repr value.toNat) value.isLt
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using parsed

theorem tokenize_movabs_repr (value : BitVec 64) :
    Silmaril.X86.Assembly.tokenize ("movabs rax, " ++ Nat.repr value.toNat) =
      ["movabs", "rax", ",", Nat.repr value.toNat] := by
  have consumed := tokenizeChars_digits_end (Nat.repr value.toNat).toList []
    [",", "rax", "movabs"] (by simp) (repr_digits value.toNat)
  simpa [Silmaril.X86.Assembly.tokenize, Silmaril.X86.Assembly.tokenizeChars,
    Silmaril.X86.Assembly.flushToken, String.toList_append,
    ← Nat.repr_eq_ofList_toDigits] using consumed

theorem tokenize_minus_repr (number : Nat) :
    Silmaril.X86.Assembly.tokenize ("-" ++ Nat.repr number) = ["-", Nat.repr number] := by
  have consumed := tokenizeChars_digits_end (Nat.repr number).toList [] ["-"]
    (by simp) (repr_digits number)
  simpa [Silmaril.X86.Assembly.tokenize, Silmaril.X86.Assembly.tokenizeChars,
    Silmaril.X86.Assembly.flushToken, String.toList_append,
    ← Nat.repr_eq_ofList_toDigits] using consumed

/-- Decimal integer text roundtrips through the actual tokenizer and integer
parser together, including its separately tokenized minus sign. -/
theorem integer_tokenize_repr (number : Int) :
    Silmaril.X86.Assembly.integer (Silmaril.X86.Assembly.tokenize (Int.repr number)) =
      .ok number := by
  rw [Int.repr_eq_ite]
  split
  next nonnegative =>
    rw [tokenize_repr, integer_nat_repr, Int.toNat_of_nonneg nonnegative]
  next negative =>
    rw [tokenize_minus_repr, integer_neg_repr, Int.toNat_of_nonneg (by omega)]
    simp

/-- Separator-free text is accumulated by the actual structural line splitter. -/
theorem splitAux_append_without {α : Type} [BEq α] (separator : α)
    (segment suffix buffer : List α) (chunks : List (List α))
    (without : ∀ c ∈ segment, (c == separator) = false) :
    Silmaril.X86.Assembly.splitAux separator (segment ++ suffix) buffer chunks =
      Silmaril.X86.Assembly.splitAux separator suffix (segment.reverse ++ buffer) chunks := by
  induction segment generalizing buffer with
  | nil => rfl
  | cons c cs ih =>
    have different : (c == separator) = false := without c (by simp)
    simp only [List.cons_append, Silmaril.X86.Assembly.splitAux, different,
      Bool.false_eq_true, ite_false]
    rw [ih (c :: buffer) (fun d hd => without d (by simp [hd]))]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Decimal digits do not create extra source lines in the actual splitter. -/
theorem splitAux_repr_append (number : Nat) (suffix buffer : List Char)
    (chunks : List (List Char)) :
    Silmaril.X86.Assembly.splitAux '\n' ((Nat.repr number).toList ++ suffix) buffer chunks =
      Silmaril.X86.Assembly.splitAux '\n' suffix
        ((Nat.repr number).toList.reverse ++ buffer) chunks := by
  apply splitAux_append_without
  intro c member
  have digit : c.isDigit = true := repr_digits number c member
  have different : c ≠ '\n' := fun equality => by subst c; contradiction
  exact beq_eq_false_iff_ne.mpr different

end Silmaril.Compiler.Native.Assembly
