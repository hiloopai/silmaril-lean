module

public import Silmaril.Wasm.Component.Reference.ABI.Despecialize.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Package.Defs

/-!
# Canonical ABI type predicates

* Decidable equality for `WIT.ValType Ref Resource` and `WIT.FuncType Ref Resource` (the
  derive handler does not apply to the nested inductive outside its defining module, so a
  structural `ValType.beq` is proved lawful and the instance is built from it).
* REF `contains`, `contains_borrow`, `contains_async_value` and `none_or_number_type`
  (component-model `a25fc0b`, `design/mvp/canonical-abi/definitions.py` lines 1112–1140,
  https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py).
  `contains p t` applies `p` to `despecialize t` and recurses into the children of the
  despecialized form, exactly as REF does, so `p` never sees a tuple, enum, option, result or
  map (`contains_despecialize`). Deviation D-c: REF's `contains` hits `assert(False)` on
  `flags` and `error-context`; here they are leaves (`p t`).
* `containsListOrString`: the `CanonicalABI.md` §Canonical Definitions side condition
  "requires `memory`/`realloc` if `T` contains a `list` or `string`". A dynamic `list` (and
  hence a `map`, which despecializes to one) or a `string` counts; a fixed-length list stores
  its elements inline and counts only through its element type (as wasmparser's
  `contains_ptr`).
* Syntactic feature-usage predicates `ValType.usesFixedList/usesMap/usesErrorContext/
  usesAsyncValue` (deep, over the undespecialized syntax), consumed by validation and profiles.
* `ValType.WellFormedCM`: the component-model value-type rules of `Binary.md` §Type
  Definitions, applied to every nested value type: structural
  `WIT.ValType.WellFormed` (nonempty labels, flags `1..32`, fixed length `> 0`); every record
  field, variant case, enum case and flag label is a kebab-case `label` (`WIT.IsLabel`) and the
  labels of each type are strongly unique (`Explainer.md` §Name Uniqueness, `WIT.canonLabel`:
  hyphens removed, lowercased); no `borrow` inside `stream`/`future` elements; no
  `stream<char>`; and `elem_size(u, 'i64') < 2^28` for every subterm `u` (each nested type is
  its own `defvaltype` in the binary). Not feature-gated (gating is validation's job).
  `FuncType.WellFormedCM`: parameter names are labels and strongly unique, parameter and result
  types satisfy `ValType.WellFormedCM`, and the result contains no `borrow`.

Not modelled: REF `contains` on a `FuncType` (shallow, only used by the host-facing
`canon_lift`/`canon_lower` asserts); resource-type validity (resources are opaque here).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

universe u v w

section DecEq

variable {Ref : Type u} {Res : Type v} [DecidableEq Ref] [DecidableEq Res]

mutual
  /-- Structural boolean equality of value types. -/
  def ValType.beq : ValType Ref Res → ValType Ref Res → Bool
    | .prim a, .prim b => decide (a = b)
    | .ref a, .ref b => decide (a = b)
    | .list a, .list b => ValType.beq a b
    | .fixedList a n, .fixedList b m => ValType.beq a b && decide (n = m)
    | .record a, .record b => ValType.beqFields a b
    | .tuple a, .tuple b => ValType.beqList a b
    | .variant a, .variant b => ValType.beqCases a b
    | .enum a, .enum b => decide (a = b)
    | .flags a, .flags b => decide (a = b)
    | .option a, .option b => ValType.beq a b
    | .result a c, .result b d => ValType.beqOpt a b && ValType.beqOpt c d
    | .map k a, .map l b => decide (k = l) && ValType.beq a b
    | .own a, .own b => decide (a = b)
    | .borrow a, .borrow b => decide (a = b)
    | .future a, .future b => ValType.beqOpt a b
    | .stream a, .stream b => ValType.beqOpt a b
    | .errorContext, .errorContext => true
    | _, _ => false
  termination_by structural a _ => a

  def ValType.beqFields :
      List (String × ValType Ref Res) → List (String × ValType Ref Res) → Bool
    | [], [] => true
    | (l, a) :: as, (m, b) :: bs => decide (l = m) && ValType.beq a b && ValType.beqFields as bs
    | _, _ => false
  termination_by structural as _ => as

  def ValType.beqList : List (ValType Ref Res) → List (ValType Ref Res) → Bool
    | [], [] => true
    | a :: as, b :: bs => ValType.beq a b && ValType.beqList as bs
    | _, _ => false
  termination_by structural as _ => as

  def ValType.beqCases :
      List (String × Option (ValType Ref Res)) →
        List (String × Option (ValType Ref Res)) → Bool
    | [], [] => true
    | (l, a) :: as, (m, b) :: bs => decide (l = m) && ValType.beqOpt a b && ValType.beqCases as bs
    | _, _ => false
  termination_by structural as _ => as

  def ValType.beqOpt : Option (ValType Ref Res) → Option (ValType Ref Res) → Bool
    | none, none => true
    | some a, some b => ValType.beq a b
    | _, _ => false
  termination_by structural a _ => a
end

mutual
  theorem ValType.eq_of_beq : ∀ {a b : ValType Ref Res}, ValType.beq a b = true → a = b
    | .prim _, b, h | .ref _, b, h | .enum _, b, h | .flags _, b, h | .own _, b, h
    | .borrow _, b, h | .errorContext, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | rfl
        | (simp only [ValType.beq, decide_eq_true_eq] at h; rw [h])
    | .list _, b, h | .option _, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | (simp only [ValType.beq] at h; rw [ValType.eq_of_beq h])
    | .fixedList _ _, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | (simp only [ValType.beq, Bool.and_eq_true, decide_eq_true_eq] at h
           rw [ValType.eq_of_beq h.1, h.2])
    | .record _, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | (simp only [ValType.beq] at h; rw [ValType.eq_of_beqFields h])
    | .tuple _, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | (simp only [ValType.beq] at h; rw [ValType.eq_of_beqList h])
    | .variant _, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | (simp only [ValType.beq] at h; rw [ValType.eq_of_beqCases h])
    | .result _ _, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | (simp only [ValType.beq, Bool.and_eq_true] at h
           rw [ValType.eq_of_beqOpt h.1, ValType.eq_of_beqOpt h.2])
    | .map _ _, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | (simp only [ValType.beq, Bool.and_eq_true, decide_eq_true_eq] at h
           rw [h.1, ValType.eq_of_beq h.2])
    | .future _, b, h | .stream _, b, h => by
      cases b <;> first
        | exact absurd h Bool.false_ne_true
        | (simp only [ValType.beq] at h; rw [ValType.eq_of_beqOpt h])

  theorem ValType.eq_of_beqFields :
      ∀ {as bs : List (String × ValType Ref Res)}, ValType.beqFields as bs = true → as = bs
    | [], [], _ => rfl
    | (_, _) :: _, (_, _) :: _, h => by
      simp only [ValType.beqFields, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1, ValType.eq_of_beq h.1.2, ValType.eq_of_beqFields h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp only [ValType.beqFields, Bool.false_eq_true] at h

  theorem ValType.eq_of_beqList :
      ∀ {as bs : List (ValType Ref Res)}, ValType.beqList as bs = true → as = bs
    | [], [], _ => rfl
    | _ :: _, _ :: _, h => by
      simp only [ValType.beqList, Bool.and_eq_true] at h
      rw [ValType.eq_of_beq h.1, ValType.eq_of_beqList h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp only [ValType.beqList, Bool.false_eq_true] at h

  theorem ValType.eq_of_beqCases :
      ∀ {as bs : List (String × Option (ValType Ref Res))},
        ValType.beqCases as bs = true → as = bs
    | [], [], _ => rfl
    | (_, _) :: _, (_, _) :: _, h => by
      simp only [ValType.beqCases, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1, ValType.eq_of_beqOpt h.1.2, ValType.eq_of_beqCases h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp only [ValType.beqCases, Bool.false_eq_true] at h

  theorem ValType.eq_of_beqOpt :
      ∀ {a b : Option (ValType Ref Res)}, ValType.beqOpt a b = true → a = b
    | none, none, _ => rfl
    | some _, some _, h => by
      simp only [ValType.beqOpt] at h; rw [ValType.eq_of_beq h]
    | none, some _, h | some _, none, h => by simp only [ValType.beqOpt, Bool.false_eq_true] at h
end

mutual
  theorem ValType.beq_refl : ∀ (a : ValType Ref Res), ValType.beq a a = true
    | .prim _ | .ref _ | .enum _ | .flags _ | .own _ | .borrow _ | .errorContext => by
      simp only [ValType.beq, decide_true]
    | .list a | .option a => by simp only [ValType.beq, ValType.beq_refl a]
    | .fixedList a _ => by simp only [ValType.beq, ValType.beq_refl a, decide_true, Bool.and_self]
    | .record fs => by simp only [ValType.beq, ValType.beqFields_refl fs]
    | .tuple ts => by simp only [ValType.beq, ValType.beqList_refl ts]
    | .variant cs => by simp only [ValType.beq, ValType.beqCases_refl cs]
    | .result a b => by simp only [ValType.beq, ValType.beqOpt_refl a, ValType.beqOpt_refl b,
        Bool.and_self]
    | .map _ a => by simp only [ValType.beq, ValType.beq_refl a, decide_true, Bool.and_self]
    | .future a | .stream a => by simp only [ValType.beq, ValType.beqOpt_refl a]

  theorem ValType.beqFields_refl : ∀ (as : List (String × ValType Ref Res)),
      ValType.beqFields as as = true
    | [] => rfl
    | (_, a) :: as => by
      simp only [ValType.beqFields, decide_true, ValType.beq_refl a, ValType.beqFields_refl as,
        Bool.and_self]

  theorem ValType.beqList_refl : ∀ (as : List (ValType Ref Res)), ValType.beqList as as = true
    | [] => rfl
    | a :: as => by
      simp only [ValType.beqList, ValType.beq_refl a, ValType.beqList_refl as, Bool.and_self]

  theorem ValType.beqCases_refl : ∀ (as : List (String × Option (ValType Ref Res))),
      ValType.beqCases as as = true
    | [] => rfl
    | (_, a) :: as => by
      simp only [ValType.beqCases, decide_true, ValType.beqOpt_refl a, ValType.beqCases_refl as,
        Bool.and_self]

  theorem ValType.beqOpt_refl : ∀ (a : Option (ValType Ref Res)), ValType.beqOpt a a = true
    | none => rfl
    | some a => by simp only [ValType.beqOpt, ValType.beq_refl a]
end

theorem ValType.beq_iff {a b : ValType Ref Res} : ValType.beq a b = true ↔ a = b :=
  ⟨ValType.eq_of_beq, fun h => h ▸ ValType.beq_refl a⟩

instance : DecidableEq (ValType Ref Res) := fun a b =>
  decidable_of_iff (ValType.beq a b = true) ValType.beq_iff

instance : BEq (ValType Ref Res) := ⟨ValType.beq⟩

instance : LawfulBEq (ValType Ref Res) where
  eq_of_beq := ValType.eq_of_beq
  rfl := ValType.beq_refl _

instance : DecidableEq (FuncType Ref Res) := fun
  | ⟨p, r, a⟩, ⟨p', r', a'⟩ =>
    if h : p = p' ∧ r = r' ∧ a = a' then isTrue (by rw [h.1, h.2.1, h.2.2])
    else isFalse (fun e => h (by cases e; exact ⟨rfl, rfl, rfl⟩))

end DecEq

/-! ## Decidability of structural well-formedness -/

section WellFormed

variable {Ref : Type u} {Res : Type v} (refOk : Ref → Prop) (resOk : Res → Prop)
  [DecidablePred refOk] [DecidablePred resOk]

/-- `String.toLower` on the character list; unlike `String.map` it reduces in the kernel. -/
def lowerChars (s : String) : List Char := s.toList.map Char.toLower

/-- Case-insensitive uniqueness via `lowerChars` agrees with uniqueness under `String.toLower`
(the form used by `ValType.WellFormed`). -/
theorem nodup_lowerChars_iff {α : Type w} (g : α → String) (xs : List α) :
    (xs.map fun x => lowerChars (g x)).Nodup ↔ (xs.map fun x => (g x).toLower).Nodup := by
  have h : (xs.map fun x => lowerChars (g x)) =
      (xs.map fun x => (g x).toLower).map String.toList := by
    simp only [List.map_map, Function.comp_def, lowerChars, String.toLower, String.toList_map]
  rw [h]
  simp only [List.Nodup, List.pairwise_map, ne_eq, String.toList_inj]

mutual
  /-- Boolean checker for `ValType.WellFormed`. Lowercase uniqueness is checked on
  `lowerChars` so that the checker reduces in the kernel (`nodup_lowerChars_iff`). -/
  def ValType.checkWellFormed : ValType Ref Res → Bool
    | .prim _ | .errorContext => true
    | .ref r => decide (refOk r)
    | .own r | .borrow r => decide (resOk r)
    | .list t | .option t | .map _ t => ValType.checkWellFormed t
    | .fixedList t n => decide (0 < n) && ValType.checkWellFormed t
    | .record fs => decide (fs ≠ []) && decide ((fs.map (fun f => lowerChars f.1)).Nodup) &&
        ValType.checkWellFormedFields fs
    | .tuple ts => decide (ts ≠ []) && ValType.checkWellFormedList ts
    | .variant cs => decide (cs ≠ []) && decide (cs.length < 2 ^ 32) &&
        decide ((cs.map (fun c => lowerChars c.1)).Nodup) && ValType.checkWellFormedCases cs
    | .enum cs => decide (cs ≠ []) && decide (cs.length < 2 ^ 32) &&
        decide ((cs.map fun c => lowerChars c).Nodup)
    | .flags ls => decide (ls ≠ []) && decide (ls.length ≤ 32) &&
        decide ((ls.map fun l => lowerChars l).Nodup)
    | .result a b => ValType.checkWellFormedOpt a && ValType.checkWellFormedOpt b
    | .future t | .stream t => ValType.checkWellFormedOpt t

  def ValType.checkWellFormedFields : List (String × ValType Ref Res) → Bool
    | [] => true
    | (_, t) :: fs => ValType.checkWellFormed t && ValType.checkWellFormedFields fs

  def ValType.checkWellFormedList : List (ValType Ref Res) → Bool
    | [] => true
    | t :: ts => ValType.checkWellFormed t && ValType.checkWellFormedList ts

  def ValType.checkWellFormedCases : List (String × Option (ValType Ref Res)) → Bool
    | [] => true
    | (_, t) :: cs => ValType.checkWellFormedOpt t && ValType.checkWellFormedCases cs

  def ValType.checkWellFormedOpt : Option (ValType Ref Res) → Bool
    | none => true
    | some t => ValType.checkWellFormed t
end

mutual
  theorem ValType.checkWellFormed_iff : ∀ (t : ValType Ref Res),
      ValType.checkWellFormed refOk resOk t = true ↔ ValType.WellFormed refOk resOk t
    | .prim _ => by simp only [ValType.checkWellFormed, true_iff]; exact .prim _
    | .errorContext => by simp only [ValType.checkWellFormed, true_iff]; exact .errorContext
    | .ref _ => by
      simp only [ValType.checkWellFormed, decide_eq_true_eq]
      exact ⟨.ref, fun | .ref h => h⟩
    | .own _ => by
      simp only [ValType.checkWellFormed, decide_eq_true_eq]
      exact ⟨.own, fun | .own h => h⟩
    | .borrow _ => by
      simp only [ValType.checkWellFormed, decide_eq_true_eq]
      exact ⟨.borrow, fun | .borrow h => h⟩
    | .list t => by
      simp only [ValType.checkWellFormed, ValType.checkWellFormed_iff t]
      exact ⟨.list, fun | .list h => h⟩
    | .option t => by
      simp only [ValType.checkWellFormed, ValType.checkWellFormed_iff t]
      exact ⟨.option, fun | .option h => h⟩
    | .map _ t => by
      simp only [ValType.checkWellFormed, ValType.checkWellFormed_iff t]
      exact ⟨.map, fun | .map h => h⟩
    | .fixedList t _ => by
      simp only [ValType.checkWellFormed, Bool.and_eq_true, decide_eq_true_eq,
        ValType.checkWellFormed_iff t]
      exact ⟨fun h => .fixedList h.1 h.2, fun | .fixedList h1 h2 => ⟨h1, h2⟩⟩
    | .record fs => by
      simp only [ValType.checkWellFormed, Bool.and_eq_true, decide_eq_true_eq,
        ValType.checkWellFormedFields_iff fs, nodup_lowerChars_iff]
      exact ⟨fun h => .record h.1.1 h.1.2 h.2, fun | .record h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩⟩
    | .tuple ts => by
      simp only [ValType.checkWellFormed, Bool.and_eq_true, decide_eq_true_eq,
        ValType.checkWellFormedList_iff ts]
      exact ⟨fun h => .tuple h.1 h.2, fun | .tuple h1 h2 => ⟨h1, h2⟩⟩
    | .variant cs => by
      simp only [ValType.checkWellFormed, Bool.and_eq_true, decide_eq_true_eq,
        ValType.checkWellFormedCases_iff cs, nodup_lowerChars_iff]
      exact ⟨fun h => .variant h.1.1.1 h.1.1.2 h.1.2 h.2,
        fun | .variant h1 h2 h3 h4 => ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩
    | .enum _ => by
      simp only [ValType.checkWellFormed, Bool.and_eq_true, decide_eq_true_eq,
        nodup_lowerChars_iff (fun c => c)]
      exact ⟨fun h => .enum h.1.1 h.1.2 h.2, fun | .enum h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩⟩
    | .flags _ => by
      simp only [ValType.checkWellFormed, Bool.and_eq_true, decide_eq_true_eq,
        nodup_lowerChars_iff (fun c => c)]
      exact ⟨fun h => .flags h.1.1 h.1.2 h.2, fun | .flags h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩⟩
    | .result a b => by
      simp only [ValType.checkWellFormed, Bool.and_eq_true, ValType.checkWellFormedOpt_iff a,
        ValType.checkWellFormedOpt_iff b]
      exact ⟨fun h => .result h.1 h.2, fun | .result h1 h2 => ⟨h1, h2⟩⟩
    | .future t => by
      simp only [ValType.checkWellFormed, ValType.checkWellFormedOpt_iff t]
      exact ⟨.future, fun | .future h => h⟩
    | .stream t => by
      simp only [ValType.checkWellFormed, ValType.checkWellFormedOpt_iff t]
      exact ⟨.stream, fun | .stream h => h⟩

  theorem ValType.checkWellFormedFields_iff : ∀ (fs : List (String × ValType Ref Res)),
      ValType.checkWellFormedFields refOk resOk fs = true ↔
        ∀ f ∈ fs, ValType.WellFormed refOk resOk f.2
    | [] => by simp only [ValType.checkWellFormedFields, List.not_mem_nil, false_imp_iff,
        imp_true_iff]
    | (_, t) :: fs => by
      simp only [ValType.checkWellFormedFields, Bool.and_eq_true, ValType.checkWellFormed_iff t,
        ValType.checkWellFormedFields_iff fs, List.forall_mem_cons]

  theorem ValType.checkWellFormedList_iff : ∀ (ts : List (ValType Ref Res)),
      ValType.checkWellFormedList refOk resOk ts = true ↔
        ∀ t ∈ ts, ValType.WellFormed refOk resOk t
    | [] => by simp only [ValType.checkWellFormedList, List.not_mem_nil, false_imp_iff,
        imp_true_iff]
    | t :: ts => by
      simp only [ValType.checkWellFormedList, Bool.and_eq_true, ValType.checkWellFormed_iff t,
        ValType.checkWellFormedList_iff ts, List.forall_mem_cons]

  theorem ValType.checkWellFormedCases_iff : ∀ (cs : List (String × Option (ValType Ref Res))),
      ValType.checkWellFormedCases refOk resOk cs = true ↔
        ∀ c ∈ cs, ∀ t ∈ c.2, ValType.WellFormed refOk resOk t
    | [] => by simp only [ValType.checkWellFormedCases, List.not_mem_nil, false_imp_iff,
        imp_true_iff]
    | (_, t) :: cs => by
      simp only [ValType.checkWellFormedCases, Bool.and_eq_true, ValType.checkWellFormedOpt_iff t,
        ValType.checkWellFormedCases_iff cs, List.forall_mem_cons]

  theorem ValType.checkWellFormedOpt_iff : ∀ (t : Option (ValType Ref Res)),
      ValType.checkWellFormedOpt refOk resOk t = true ↔
        ∀ a ∈ t, ValType.WellFormed refOk resOk a
    | none => by simp only [ValType.checkWellFormedOpt, Option.mem_def, reduceCtorEq,
        false_imp_iff, imp_true_iff]
    | some t => by
      simp only [ValType.checkWellFormedOpt, ValType.checkWellFormed_iff t, Option.mem_def,
        Option.some.injEq, forall_eq']
end

instance (t : ValType Ref Res) : Decidable (ValType.WellFormed refOk resOk t) :=
  decidable_of_iff _ (ValType.checkWellFormed_iff refOk resOk t)

end WellFormed

end Silmaril.Wasm.Component.WIT

namespace Silmaril.Wasm.Component.ABI

universe u

variable {R : Type u}

open WIT

/-! ## REF `contains` and derived predicates -/

mutual
  /-- REF `contains(t, p)` (definitions.py 1118–1134): `p` is applied to `despecialize t` and
  the search recurses into the children of the despecialized type. Deviation D-c: `flags` and
  `error-context` are leaves (REF asserts). -/
  def contains (p : ClosedType R → Bool) : ClosedType R → Bool
    | .ref e => nomatch e
    | .prim t => p (.prim t)
    | .own r => p (.own r)
    | .borrow r => p (.borrow r)
    | .flags ls => p (.flags ls)
    | .errorContext => p .errorContext
    | .list u => p (.list u) || contains p u
    | .fixedList u n => p (.fixedList u n) || contains p u
    | .stream u => p (.stream u) || containsOpt p u
    | .future u => p (.future u) || containsOpt p u
    | .record fs => p (.record fs) || containsFields p fs
    | .tuple ts => p (despecialize (.tuple ts)) || containsList p ts
    | .variant cs => p (.variant cs) || containsCases p cs
    | .enum ls => p (despecialize (.enum ls))
    | .option u => p (despecialize (.option u)) || contains p u
    | .result a b => p (despecialize (.result a b)) || (containsOpt p a || containsOpt p b)
    | .map k v => p (despecialize (.map k v)) ||
        (p (.record (mapEntryFields k v)) || (p (.prim k.toPrimitive) || contains p v))

  def containsFields (p : ClosedType R → Bool) : List (String × ClosedType R) → Bool
    | [] => false
    | (_, t) :: fs => contains p t || containsFields p fs

  def containsList (p : ClosedType R → Bool) : List (ClosedType R) → Bool
    | [] => false
    | t :: ts => contains p t || containsList p ts

  def containsCases (p : ClosedType R → Bool) : List (String × Option (ClosedType R)) → Bool
    | [] => false
    | (_, t) :: cs => containsOpt p t || containsCases p cs

  /-- REF `contains(None, p) = False`. -/
  def containsOpt (p : ClosedType R → Bool) : Option (ClosedType R) → Bool
    | none => false
    | some t => contains p t
end

def isBorrow : ClosedType R → Bool
  | .borrow _ => true
  | _ => false

def isAsyncValue : ClosedType R → Bool
  | .stream _ | .future _ => true
  | _ => false

/-- A dynamically sized, out-of-line payload: a variable-length `list` or a `string`. -/
def isListOrString : ClosedType R → Bool
  | .list _ | .prim .string => true
  | _ => false

/-- REF `contains_borrow` (definitions.py 1112). -/
def containsBorrow (t : ClosedType R) : Bool := contains isBorrow t

/-- REF `contains_async_value` (definitions.py 1115). -/
def containsAsyncValue (t : ClosedType R) : Bool := contains isAsyncValue t

/-- `CanonicalABI.md` canonopt side condition: "`T` contains a `list` or `string`". -/
def containsListOrString (t : ClosedType R) : Bool := contains isListOrString t

/-- REF `none_or_number_type` (definitions.py 1136–1139): absent, or an integer or float
type (not `bool`, not `char`). No despecialization, as in REF. -/
def noneOrNumberType : Option (ClosedType R) → Bool
  | none => true
  | some (.prim .u8) | some (.prim .u16) | some (.prim .u32) | some (.prim .u64)
  | some (.prim .s8) | some (.prim .s16) | some (.prim .s32) | some (.prim .s64)
  | some (.prim .f32) | some (.prim .f64) => true
  | some _ => false

/-! ## Syntactic feature usage -/

mutual
  /-- Deep syntactic search: does `p` hold of some subterm (including `t` itself)? Unlike
  `contains`, nothing is despecialized, so `p` sees `map`, `option`, `tuple`, etc. -/
  def ValType.anySub (p : ClosedType R → Bool) : ClosedType R → Bool
    | .ref e => nomatch e
    | t@(.prim _) | t@(.own _) | t@(.borrow _) | t@(.flags _) | t@(.errorContext)
    | t@(.enum _) => p t
    | t@(.list u) | t@(.fixedList u _) | t@(.option u) | t@(.map _ u) =>
      p t || ValType.anySub p u
    | t@(.stream u) | t@(.future u) => p t || ValType.anySubOpt p u
    | t@(.record fs) => p t || ValType.anySubFields p fs
    | t@(.tuple ts) => p t || ValType.anySubList p ts
    | t@(.variant cs) => p t || ValType.anySubCases p cs
    | t@(.result a b) => p t || (ValType.anySubOpt p a || ValType.anySubOpt p b)

  def ValType.anySubFields (p : ClosedType R → Bool) : List (String × ClosedType R) → Bool
    | [] => false
    | (_, t) :: fs => ValType.anySub p t || ValType.anySubFields p fs

  def ValType.anySubList (p : ClosedType R → Bool) : List (ClosedType R) → Bool
    | [] => false
    | t :: ts => ValType.anySub p t || ValType.anySubList p ts

  def ValType.anySubCases (p : ClosedType R → Bool) :
      List (String × Option (ClosedType R)) → Bool
    | [] => false
    | (_, t) :: cs => ValType.anySubOpt p t || ValType.anySubCases p cs

  def ValType.anySubOpt (p : ClosedType R → Bool) : Option (ClosedType R) → Bool
    | none => false
    | some t => ValType.anySub p t
end

/-- Uses a fixed-length list (🔧 gate). -/
def ValType.usesFixedList : ClosedType R → Bool :=
  ValType.anySub fun | .fixedList _ _ => true | _ => false

/-- Uses a `map` (🗺️ gate). -/
def ValType.usesMap : ClosedType R → Bool :=
  ValType.anySub fun | .map _ _ => true | _ => false

/-- Uses `error-context` (📝 gate). -/
def ValType.usesErrorContext : ClosedType R → Bool :=
  ValType.anySub fun | .errorContext => true | _ => false

/-- Uses `stream` or `future` (🔀 gate). -/
def ValType.usesAsyncValue : ClosedType R → Bool := ValType.anySub isAsyncValue

/-! ## Component-model well-formedness -/

/-- A label list of `Binary.md`: every label is a kebab-case `label` and the list is
strongly unique (`WIT.canonLabel` removes hyphens and lowercases). -/
def labelsOk (ls : List String) : Bool :=
  ls.all WIT.isLabel && decide ((ls.map WIT.canonLabel).Nodup)

/-- The node-local label violation: a record, variant, enum or flags type whose own labels
fail `labelsOk`. -/
def badLabelsNode : ClosedType R → Bool
  | .record fs => !labelsOk (fs.map (·.1))
  | .variant cs => !labelsOk (cs.map (·.1))
  | .enum ls | .flags ls => !labelsOk ls
  | _ => false

/-- The node-local size violation: `elem_size(u, 'i64') ≥ 2^28`. -/
def oversizedNode (u : ClosedType R) : Bool := decide (2 ^ 28 ≤ (layout .i64 u).size)

/-- The value-type rules of `Binary.md` (not feature-gated), for `t` and every nested type:
structural well-formedness (nonempty labels, `0 < |flags| ≤ 32`, positive fixed lengths),
labels that are kebab-case `label`s and strongly unique per type, no `borrow` inside a
`stream`/`future` element, no `stream<char>`, and `elem_size(u, 'i64') < 2^28` for every
subterm `u` (Binary.md: "for every `defvaltype` `t`"; a nested type is its own `defvaltype`,
and `list`/`stream`/`future` hide their element's size). The size bound is stated at `i64`,
the widest pointer, as in `CanonicalABI.md` §Element Size. -/
def ValType.WellFormedCM (t : ClosedType R) : Prop :=
  ValType.WellFormed (fun _ => True) (fun _ => True) t ∧ ValType.badBorrow false t = false ∧
    ValType.streamChar t = false ∧ ValType.anySub badLabelsNode t = false ∧
    ValType.anySub oversizedNode t = false

instance (t : ClosedType R) : Decidable (ValType.WellFormedCM t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Function-type rules: parameter names are kebab-case labels and strongly unique
(`labelsOk`), parameter and result types satisfy `ValType.WellFormedCM`, and the result
contains no `borrow` (transitively). -/
def FuncType.WellFormedCM (ft : WIT.FuncType Empty R) : Prop :=
  labelsOk (ft.params.map (·.1)) = true ∧ (∀ p ∈ ft.params, ValType.WellFormedCM p.2) ∧
    (∀ t ∈ ft.result, ValType.WellFormedCM t ∧ containsBorrow t = false)

instance (ft : WIT.FuncType Empty R) : Decidable (FuncType.WellFormedCM ft) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Tests -/

end Silmaril.Wasm.Component.ABI
