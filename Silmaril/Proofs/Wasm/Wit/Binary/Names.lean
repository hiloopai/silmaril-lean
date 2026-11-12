module

public import Silmaril.Wasm.Wit.Binary.Normal.Defs

/-!
# WIT binary names parse back

Function names demangle back (`demangle_mangled`) and interface ids parse
back (`parseIfaceName_id`, `nameKey_id`, `nameKey_plain`) under the
validity conditions of `Silmaril.Wasm.Wit.Binary.Normal`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

theorem dropPrefix?_append (p l : List Char) : dropPrefix? p (p ++ l) = some l := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [dropPrefix?, ih]

theorem splitAt?_append {c : Char} {x : List Char} (hx : c ∉ x) (y : List Char) :
    splitAt? c (x ++ c :: y) = some (x, y) := by
  induction x with
  | nil => simp [splitAt?]
  | cons a x ih =>
    simp only [List.mem_cons, not_or] at hx
    simp [splitAt?, ih hx.2, Ne.symm hx.1]

theorem splitAt?_none {c : Char} {x : List Char} (hx : c ∉ x) : splitAt? c x = none := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    simp only [List.mem_cons, not_or] at hx
    simp [splitAt?, ih hx.2, Ne.symm hx.1]

theorem dropPrefix?_head_ne {a b : Char} {p l : List Char} (h : a ≠ b) :
    dropPrefix? (a :: p) (b :: l) = none := by
  simp [dropPrefix?, h]

/-- Interface ids parse back. -/
theorem parseIfaceName_id {i : IfaceName} (h : i.Valid) : parseIfaceName i.idChars = some i := by
  obtain ⟨⟨ns, pn, v⟩, n⟩ := i
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  simp only [IfaceName.idChars, PackageName.prefix, parseIfaceName, List.append_assoc,
    List.cons_append, splitAt?_append h1, splitAt?_append h2, Option.bind_eq_bind,
    Option.bind_some]
  cases v with
  | none => simp [versionSuffix, splitAt?_none h3]
  | some v => simp [versionSuffix, splitAt?_append h3]

theorem colon_mem_id (i : IfaceName) : ':' ∈ i.idChars := by
  simp [IfaceName.idChars, PackageName.prefix]

/-- The key of an interface id is the interface. -/
theorem nameKey_id {i : IfaceName} (h : i.Valid) : nameKey i.id = .ok (.inl i) := by
  simp [nameKey, IfaceName.id, colon_mem_id, parseIfaceName_id h]; rfl

/-- The key of a plain name is the name. -/
theorem nameKey_plain {n : String} (h : ':' ∉ n.toList) : nameKey n = .ok (.inr n) := by
  simp [nameKey, h]; rfl

/-- A plain freestanding name: no prefix applies. -/
theorem demangleChars_plain {cs : List Char} (h : cs.head? ≠ some '[') :
    demangleChars cs = some (.freestanding, cs, false) := by
  cases cs with
  | nil => simp [demangleChars, dropPrefix?, pConstructor, pMethod, pStatic, pAsyncMethod,
      pAsyncStatic, pAsync]
  | cons c l =>
    have hc : c ≠ '[' := fun e => h (by simp [e])
    simp [demangleChars, pConstructor, pMethod, pStatic, pAsyncMethod, pAsyncStatic, pAsync,
      dropPrefix?_head_ne (Ne.symm hc), hc]

set_option linter.unusedSimpArgs false in
/-- Demangling a mangled name gives back the kind, name and asyncness. -/
theorem demangleChars_mangled {f : Func} (h : f.Valid) :
    demangleChars f.mangledChars = some (f.kind, f.name.toList, f.async) := by
  obtain ⟨n, k, a, ps, r, d, st⟩ := f
  cases k with
  | freestanding =>
    cases a with
    | true => simp [Func.mangledChars, demangleChars, pAsync, pConstructor, pMethod, pStatic,
        pAsyncMethod, pAsyncStatic, dropPrefix?]
    | false => exact demangleChars_plain (h rfl)
  | method res =>
    cases a <;> simp [Func.mangledChars, demangleChars, pAsync, pConstructor, pMethod, pStatic,
        pAsyncMethod, pAsyncStatic, dropPrefix?, splitAt?_append (show '.' ∉ res.toList from h)]
  | static res =>
    cases a <;> simp [Func.mangledChars, demangleChars, pAsync, pConstructor, pMethod, pStatic,
        pAsyncMethod, pAsyncStatic, dropPrefix?, splitAt?_append (show '.' ∉ res.toList from h)]
  | constructor res =>
    obtain ⟨h1, h2⟩ := h
    have e1 : n = res := h1
    have e2 : a = false := h2
    rw [e1, e2]
    simp [Func.mangledChars, demangleChars, pConstructor, dropPrefix?]

/-- A function is read back from its name and signature, without docs. -/
theorem demangle_mangled {f : Func} (h : f.Valid) : demangle f.mangled f.sig = .ok f.strip := by
  simp only [demangle, Func.mangled, String.toList_ofList, demangleChars_mangled h, Func.sig,
    ite_true, String.ofList_toList]
  rfl

end Silmaril.Wasm.Wit.Binary
