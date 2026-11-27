module

public import Silmaril.Formats.Csv.Typed.Defs
import Silmaril.Formats.Csv.Thms

/-! Proofs for `Silmaril.Formats.Csv.Typed.Thms`. -/

public section

namespace Silmaril.Proofs.Formats.Csv.Typed

open Silmaril.Relational
open Silmaril.Formats.Csv (Field Row Rows Bytes)
open Silmaril.Formats.Csv.Typed
open Silmaril.Formats.Csv.Typed.Internal

universe u v

@[local simp] private theorem pure_ok {E α : Type*} (a : α) :
    (pure a : Except E α) = .ok a := rfl

@[local simp] private theorem ok_bind {E : Type u} {α β : Type v} (a : α) (f : α → Except E β) :
    ((.ok a : Except E α) >>= f) = f a := rfl

@[local simp] private theorem error_bind {E : Type u} {α β : Type v} (e : E) (f : α → Except E β) :
    ((.error e : Except E α) >>= f) = .error e := rfl

theorem collect_ok {E : Type*} {n : Nat} {α : Fin n → Type*}
    (f : (i : Fin n) → Except E (α i)) (v : (i : Fin n) → α i) :
    collect f = .ok v ↔ ∀ i, f i = .ok (v i) := by
  induction n with
  | zero =>
    constructor
    · intro _ i
      exact i.elim0
    · intro _
      have eq : (fun i : Fin 0 => i.elim0 : (i : Fin 0) → α i) = v :=
        funext fun i => i.elim0
      rw [collect, eq]
  | succ n ih =>
    constructor
    · intro h
      cases hfirst : f 0 with
      | error e => simp [collect, hfirst] at h
      | ok first =>
        cases hrest : collect (fun (i : Fin n) => f i.succ) with
        | error e => simp [collect, hfirst, hrest] at h
        | ok rest =>
          have eq : Fin.cases first rest = v := by simpa [collect, hfirst, hrest] using h
          rw [← eq]
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hfirst
          · simpa using (ih _ _).mp hrest j
    · intro h
      have tail := (ih (fun i => f i.succ) (fun i => v i.succ)).mpr (fun i => h i.succ)
      have eta : Fin.cases (v 0) (fun i => v i.succ) = v := by
        funext i
        exact Fin.cases (by simp) (fun j => by simp) i
      simp [collect, h 0, tail, eta]

private theorem null_ne_text : nullTag ≠ textTag := by decide

private theorem importCell_exportCell {α : Type*} {codec : CellCodec α}
    (exactPrint : codec.ParsePrint) {column : Nat} {value : Option α} {field : Field}
    (h : exportCell codec column value = .ok field) : importCell codec column field = .ok value := by
  cases value with
  | none =>
    cases h
    simp [importCell]
  | some v =>
    cases printed : codec.print v with
    | none => simp [exportCell, printed] at h
    | some text =>
      have eq : textTag :: text = field := by simpa [exportCell, printed] using h
      rw [← eq]
      simp [importCell, Ne.symm null_ne_text, exactPrint printed]

private theorem exportCell_importCell {α : Type*} {codec : CellCodec α}
    (exactParse : codec.PrintParse) {column : Nat} {value : Option α} {field : Field}
    (h : importCell codec column field = .ok value) : exportCell codec column value = .ok field := by
  by_cases null : field = [nullTag]
  · subst field
    have eq : none = value := by simpa [importCell] using h
    cases eq
    rfl
  · cases field with
    | nil => simp [importCell] at h
    | cons tag text =>
      by_cases textStart : tag = textTag
      · subst tag
        cases parsed : codec.parse text with
        | none => simp [importCell, null, parsed] at h
        | some v =>
          have eq : some v = value := by simpa [importCell, null, parsed] using h
          cases eq
          simp [exportCell, exactParse parsed]
      · simp [importCell, null, textStart] at h

private theorem row_eq_of_width_zero {Kind : Type*} {schema : Schema Kind} {Value : Kind → Type*}
    (zero : schema.width = 0) (a b : Scan.Row schema Value) : a = b :=
  funext fun i => (i.cast zero).elim0

private theorem get_ofFn_cast {n : Nat} {f : Fin n → Field} (i : Fin n)
    (shape : (List.ofFn f).length = n) : (List.ofFn f).get (i.cast shape.symm) = f i := by
  rw [List.get_eq_getElem, List.getElem_ofFn]
  rfl

private theorem ofFn_get_cast {n : Nat} {row : Row} (shape : row.length = n) :
    (List.ofFn fun i : Fin n => row.get (i.cast shape.symm)) = row := by
  subst n
  simpa only [List.get_eq_getElem, Fin.val_cast] using (List.ofFn_getElem (xs := row))

variable {Kind : Type*} {Value : Kind → Type*} {schema : Schema Kind}
variable {codecs : (kind : Kind) → CellCodec (Value kind)}

private theorem importRow_exportRow (law : ∀ k, (codecs k).ParsePrint)
    {row : Scan.Row schema Value} {fields : Row} (h : exportRow schema codecs row = .ok fields) :
    importRow schema codecs fields = .ok row := by
  by_cases zero : schema.width = 0
  · have eq : zeroColumnRow = fields := by simpa [exportRow, zero] using h
    subst fields
    simp only [importRow, zero, ↓reduceDIte, ↓reduceIte]
    exact congrArg Except.ok (row_eq_of_width_zero zero _ row)
  · cases produced : collect (fun i => exportCell (codecs (schema.kind i).2) i.val (row i)) with
    | error e => simp [exportRow, zero, produced] at h
    | ok result =>
      have eq : List.ofFn result = fields := by simpa [exportRow, zero, produced] using h
      subst fields
      have shape : (List.ofFn result).length = schema.width := List.length_ofFn
      simp only [importRow, zero, shape, ↓reduceDIte]
      apply (collect_ok _ _).mpr
      intro i
      rw [get_ofFn_cast i shape]
      exact importCell_exportCell (law (schema.kind i).2) ((collect_ok _ _).mp produced i)

private theorem exportRow_importRow (law : ∀ k, (codecs k).PrintParse)
    {row : Scan.Row schema Value} {fields : Row} (h : importRow schema codecs fields = .ok row) :
    exportRow schema codecs row = .ok fields := by
  by_cases zero : schema.width = 0
  · by_cases marker : fields = zeroColumnRow
    · simp [exportRow, zero, marker]
    · simp [importRow, zero, marker] at h
  · by_cases shape : fields.length = schema.width
    · have parsed := (collect_ok _ _).mp (by simpa [importRow, zero, shape] using h)
      have produced : collect (fun i => exportCell (codecs (schema.kind i).2) i.val (row i)) =
          .ok (fun i => fields.get (i.cast shape.symm)) :=
        (collect_ok _ _).mpr (fun i => exportCell_importCell (law (schema.kind i).2) (parsed i))
      simp [exportRow, zero, produced]
      simpa only [List.get_eq_getElem, Fin.val_cast] using ofFn_get_cast shape
    · simp [importRow, zero, shape] at h

private theorem mapM_inverse {E α β : Type*} {forward : α → Except E β} {back : β → Except E α}
    (inv : ∀ {a b}, forward a = .ok b → back b = .ok a)
    {as : List α} {bs : List β} (h : as.mapM forward = .ok bs) : bs.mapM back = .ok as := by
  induction as generalizing bs with
  | nil =>
    have eq : [] = bs := by simpa using h
    cases eq
    rfl
  | cons a as ih =>
    cases first : forward a with
    | error e => simp [first] at h
    | ok b =>
      cases tail : as.mapM forward with
      | error e => simp [first, tail] at h
      | ok rest =>
        have eq : b :: rest = bs := by simpa [first, tail] using h
        rw [← eq]
        simp [inv first, ih tail]

theorem importRows_exportRows (law : ∀ k, (codecs k).ParsePrint)
    {table : Table schema Value} {rows : Rows} (h : exportRows schema codecs table = .ok rows) :
    importRows schema codecs rows = .ok table := by
  cases body : table.mapM (exportRow schema codecs) with
  | error e => simp [exportRows, body] at h
  | ok fields =>
    have eq : header schema :: fields = rows := by simpa [exportRows, body] using h
    rw [← eq]
    simpa [importRows] using mapM_inverse (importRow_exportRow law) body

theorem exportRows_importRows (law : ∀ k, (codecs k).PrintParse)
    {table : Table schema Value} {rows : Rows} (h : importRows schema codecs rows = .ok table) :
    exportRows schema codecs table = .ok rows := by
  cases rows with
  | nil => simp [importRows] at h
  | cons first fields =>
    by_cases same : first = header schema
    · subst first
      have body : fields.mapM (importRow schema codecs) = .ok table := by simpa [importRows] using h
      simp [exportRows, mapM_inverse (exportRow_importRow law) body]
    · simp [importRows, same] at h

theorem exportRows_zeroColumns (zero : schema.width = 0) (table : Table schema Value) :
    exportRows schema codecs table = .ok (List.replicate (table.length + 1) [[]]) := by
  have body : table.mapM (exportRow schema codecs) = .ok (List.replicate table.length zeroColumnRow) := by
    induction table with
    | nil => rfl
    | cons row rest ih => simp [exportRow, zero, ih, List.replicate_succ]
  simp [exportRows, header, zero, body, zeroColumnRow, List.replicate_succ]

theorem decode_encode (law : ∀ k, (codecs k).ParsePrint)
    {table : Table schema Value} {wire : Bytes} (h : encode schema codecs table = .ok wire) :
    decode schema codecs wire = .ok table := by
  cases emitted : exportRows schema codecs table with
  | error e => simp [encode, emitted] at h
  | ok rows =>
    cases hcsv : Silmaril.Formats.Csv.encode rows with
    | none => simp [encode, emitted, hcsv] at h
    | some bytes =>
      have eq : bytes = wire := by simpa [encode, emitted, hcsv] using h
      subst wire
      simp [decode, Silmaril.Formats.Csv.decode_encode hcsv, importRows_exportRows law emitted]

theorem encode_of_decode (law : ∀ k, (codecs k).PrintParse)
    {table : Table schema Value} {input : Bytes} (h : decode schema codecs input = .ok table) :
    ∃ output, encode schema codecs table = .ok output ∧
      Silmaril.Formats.Csv.decode output = Silmaril.Formats.Csv.decode input := by
  cases hcsv : Silmaril.Formats.Csv.decode input with
  | none => simp [decode, hcsv] at h
  | some rows =>
    have parsed : importRows schema codecs rows = .ok table := by simpa [decode, hcsv] using h
    have wf := Silmaril.Formats.Csv.parses_wellFormed ((Silmaril.Formats.Csv.decode_eq_some_iff _ _).mp hcsv)
    cases rendered : Silmaril.Formats.Csv.encode rows with
    | none => exact (((Silmaril.Formats.Csv.encode_eq_none_iff _).mp rendered) wf).elim
    | some output =>
      exact ⟨output, by simp [encode, exportRows_importRows law parsed, rendered],
        Silmaril.Formats.Csv.decode_encode rendered⟩

end Silmaril.Proofs.Formats.Csv.Typed
