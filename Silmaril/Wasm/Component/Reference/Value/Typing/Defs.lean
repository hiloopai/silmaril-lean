module

public import Silmaril.Wasm.Component.Reference.Value.Basic.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Despecialize.Defs
public import Silmaril.Wasm.Component.Reference.ABI.FloatChar.Defs

/-!
# Typing of component-level values

`Val.HasType v t` says that the component value `v` (`Value/Basic.lean`) is a value of the
closed WIT type `t`. It is a pointer-width-independent over-approximation of the Python
values that REF `lift_flat`/`load` can produce at type `t` (see the list-length and
handle caveats below), following `definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>):
`load` (L1256), `load_string_from_range` (L1338), `load_list` (L1376), `load_record`
(L1395), `load_variant` (L1403), `load_flags` (L1414), `lift_flat` (L1869). As in the REF,
the specialized types are typed through `despecialize` (L1101):

* `bool`; integers `int k n` with `IntKind.ofPrimitive p = some k` and `k.inRange n`;
  `f32`/`f64` with any bit pattern (NaN canonicality is the separate predicate
  `Val.IsNanCanonical`; see `Val.canonicalizeNaN`); `char` with any Lean `Char` (a Unicode
  scalar value by construction);
* `string s` with `s.Valid`: the code-unit hint is consistent with the text for the
  source pointer width (`ABI.StringValue.Consistent`) and the untagged byte length is at
  most `ABI.maxStringByteLength` (the `load_string_from_range` trap bound);
* `list` of well-typed elements; `fixed-list` with exactly `n` well-typed elements
  (represented by `Val.list`); `record` pointwise (`HasFields`); `variant c p` with
  `c < cases.length` and a payload exactly when the case has one (`HasCase`, `HasOpt`);
  `flags` with one `Bool` per label;
* `tuple`, `enum`, `option`, `result` and `map` hold of `v` iff `v` has the
  despecialized type;
* `own`/`borrow` with any representation (resource identity is not part of the value;
  handles are typed by lift/lower), `stream`/`future` with any end id,
  `error-context` with any id.

`Val.typeCheck?` is the executable check (structurally recursive, so it reduces in the
kernel) and `typeCheck?_iff` proves it equivalent to `HasType`; the `Decidable` instance
is derived from it. `Val.canonicalizeNaN` canonicalizes every float
(`ABI.canonicalizeNaN`, REF `canonicalize_nan32/64`, L1294–1305); its properties are in
`Value/Typing/Properties.lean`.

Not modelled or claimed: no well-formedness of the type itself is assumed
(`ValType.WellFormedCM` is separate), the store-side contents of handles and async ends
are not checked (REF `lift_own`/`lift_borrow` L1425/L1433 also check the handle's resource
type and `lift_stream`/`lift_future` L1441/L1444 the element type), and nothing is proved
here about lift/lower producing typed values. `list` and `map` lengths are unbounded,
unlike the string bound: REF `load_list_from_range` (L1384) traps when
`length * elem_size(elem_type, ptr_type) > MAX_LIST_BYTE_LENGTH = 2^28-1` (L1373), a bound
that depends on the pointer width through `elem_size`, so a lifted list additionally
satisfies it. Conversely `HasType` alone does not discharge REF `store_list_into_range`'s
`assert(byte_length <= REALLOC_I32_MAX)` (L1691); by deviation D-f that assert is a
precondition which callers lowering a value must establish separately.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Value

universe u

open ABI

/-! ## Integer kinds and primitives -/

namespace IntKind

/-- The WIT primitive of an integer kind. -/
def toPrimitive : IntKind → WIT.Primitive
  | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64
  | .s8 => .s8 | .s16 => .s16 | .s32 => .s32 | .s64 => .s64

/-- The integer kind of a WIT primitive (`none` for non-integer primitives). -/
def ofPrimitive : WIT.Primitive → Option IntKind
  | .u8 => some .u8 | .u16 => some .u16 | .u32 => some .u32 | .u64 => some .u64
  | .s8 => some .s8 | .s16 => some .s16 | .s32 => some .s32 | .s64 => some .s64
  | _ => none

end IntKind

/-! ## Valid strings -/

namespace StrVal

/-- A string value that REF `load_string_from_range` can produce: the code-unit hint is
consistent with the text for the source pointer width, and the byte length it denotes
(untagged, per `ABI.loadRange`) does not exceed `ABI.maxStringByteLength`. -/
def Valid (s : StrVal) : Prop :=
  s.v.Consistent s.srcAddr ∧
    (loadRange s.v.encoding s.srcAddr s.v.taggedCodeUnits).byteLength ≤ maxStringByteLength

instance (s : StrVal) : Decidable s.Valid := by unfold Valid; infer_instance

end StrVal

namespace Val

variable {R : Type u}

/-! ## Value constructors -/

/-- The integer value of a bit pattern of kind `k`: the unsigned or two's-complement
reading, per `k.signed`. -/
def ofBitVec (k : IntKind) (b : BitVec k.width) : Val :=
  .int k (if k.signed then b.toInt else (b.toNat : Int))

/-! ## The typing relation -/

mutual
/-- `HasType v t`: `v` is a component value of the closed type `t` (see the module
docstring; specialized types via REF `despecialize`). -/
inductive HasType : Val → WIT.ClosedType R → Prop where
  | bool (b : Bool) : HasType (.bool b) (.prim .bool)
  | int {p : WIT.Primitive} {k : IntKind} {n : Int} (kind : IntKind.ofPrimitive p = some k)
      (range : k.inRange n = true) : HasType (.int k n) (.prim p)
  | f32 (bits : BitVec 32) : HasType (.f32 bits) (.prim .f32)
  | f64 (bits : BitVec 64) : HasType (.f64 bits) (.prim .f64)
  | char (c : Char) : HasType (.char c) (.prim .char)
  | string {s : StrVal} (valid : s.Valid) : HasType (.string s) (.prim .string)
  | list {vs : List Val} {u : WIT.ClosedType R} (elems : ∀ x ∈ vs, HasType x u) :
      HasType (.list vs) (.list u)
  | fixedList {vs : List Val} {u : WIT.ClosedType R} {n : Nat} (length : vs.length = n)
      (elems : ∀ x ∈ vs, HasType x u) : HasType (.list vs) (.fixedList u n)
  | record {vs : List Val} {fs : List (String × WIT.ClosedType R)} (fields : HasFields vs fs) :
      HasType (.record vs) (.record fs)
  | variant {c : Nat} {p : Option Val} {cs : List (String × Option (WIT.ClosedType R))}
      (case : HasCase c p cs) : HasType (.variant c p) (.variant cs)
  | flags {bs : List Bool} {ls : List String} (length : bs.length = ls.length) :
      HasType (.flags bs) (.flags ls)
  | own (rep : Nat) (r : R) : HasType (.own rep) (.own r)
  | borrow (rep : Nat) (r : R) : HasType (.borrow rep) (.borrow r)
  | stream (e : Runtime.EndId) (u : Option (WIT.ClosedType R)) :
      HasType (.stream e) (.stream u)
  | future (e : Runtime.EndId) (u : Option (WIT.ClosedType R)) :
      HasType (.future e) (.future u)
  | errorContext (x : Runtime.ErrCtxId) : HasType (.errorContext x) .errorContext
  | tuple {v : Val} {ts : List (WIT.ClosedType R)} (h : HasType v (despecialize (.tuple ts))) :
      HasType v (.tuple ts)
  | enum {v : Val} {ls : List String} (h : HasType v (despecialize (.enum ls))) :
      HasType v (.enum ls)
  | option {v : Val} {u : WIT.ClosedType R} (h : HasType v (despecialize (.option u))) :
      HasType v (.option u)
  | result {v : Val} {a b : Option (WIT.ClosedType R)}
      (h : HasType v (despecialize (.result a b))) : HasType v (.result a b)
  | map {v : Val} {k : WIT.KeyType} {u : WIT.ClosedType R}
      (h : HasType v (despecialize (.map k u))) : HasType v (.map k u)

/-- Record fields typed pointwise (same length). -/
inductive HasFields : List Val → List (String × WIT.ClosedType R) → Prop where
  | nil : HasFields [] []
  | cons {v : Val} {vs : List Val} {l : String} {t : WIT.ClosedType R}
      {fs : List (String × WIT.ClosedType R)} (head : HasType v t) (tail : HasFields vs fs) :
      HasFields (v :: vs) ((l, t) :: fs)

/-- `HasCase c p cs`: `c < cs.length` and the payload `p` matches the `c`-th case. -/
inductive HasCase : Nat → Option Val → List (String × Option (WIT.ClosedType R)) → Prop where
  | here {p : Option Val} {l : String} {t : Option (WIT.ClosedType R)}
      {cs : List (String × Option (WIT.ClosedType R))} (payload : HasOpt p t) :
      HasCase 0 p ((l, t) :: cs)
  | there {c : Nat} {p : Option Val} {x : String × Option (WIT.ClosedType R)}
      {cs : List (String × Option (WIT.ClosedType R))} (tail : HasCase c p cs) :
      HasCase (c + 1) p (x :: cs)

/-- An optional payload: absent for a case without a type, typed otherwise. -/
inductive HasOpt : Option Val → Option (WIT.ClosedType R) → Prop where
  | none : HasOpt none none
  | some {v : Val} {t : WIT.ClosedType R} (h : HasType v t) : HasOpt (some v) (some t)
end

/-! ## The executable check -/

/-- Check a value against a primitive type. -/
def primCheck : WIT.Primitive → Val → Bool
  | .bool, .bool _ => true
  | .f32, .f32 _ => true
  | .f64, .f64 _ => true
  | .char, .char _ => true
  | .string, .string s => decide s.Valid
  | p, .int k n => IntKind.ofPrimitive p == some k && k.inRange n
  | _, _ => false

/-- `list` shape with an element check. -/
def listCheck (f : Val → Bool) : Val → Bool
  | .list vs => vs.all f
  | _ => false

/-- `fixed-list` shape with an element check. -/
def fixedListCheck (n : Nat) (f : Val → Bool) : Val → Bool
  | .list vs => vs.length == n && vs.all f
  | _ => false

/-- `record` shape with a fields check. -/
def recordCheck (g : List Val → Bool) : Val → Bool
  | .record vs => g vs
  | _ => false

/-- `variant` shape with a case check. -/
def variantCheck (g : Nat → Option Val → Bool) : Val → Bool
  | .variant c p => g c p
  | _ => false

/-- `enum` with `n` labels. -/
def enumCheck (n : Nat) : Val → Bool
  | .variant c none => decide (c < n)
  | _ => false

/-- `option` with a payload check. -/
def optionCheck (f : Val → Bool) : Val → Bool
  | .variant 0 none => true
  | .variant 1 (some x) => f x
  | _ => false

/-- `result` with payload checks for `ok` (case 0) and `error` (case 1). -/
def resultCheck (fa fb : Option Val → Bool) : Val → Bool
  | .variant 0 p => fa p
  | .variant 1 p => fb p
  | _ => false

/-- One `map` entry: a 2-field record of key and value. -/
def mapEntryCheck (k : WIT.KeyType) (f : Val → Bool) : Val → Bool
  | .record [a, b] => primCheck k.toPrimitive a && f b
  | _ => false

/-- `flags` with `n` labels. -/
def flagsCheck (n : Nat) : Val → Bool
  | .flags bs => bs.length == n
  | _ => false

/-- An `own` handle. -/
def isOwn : Val → Bool
  | .own _ => true
  | _ => false

/-- A `borrow` handle. -/
def isBorrow : Val → Bool
  | .borrow _ => true
  | _ => false

/-- A `stream` end. -/
def isStream : Val → Bool
  | .stream _ => true
  | _ => false

/-- A `future` end. -/
def isFuture : Val → Bool
  | .future _ => true
  | _ => false

/-- An `error-context`. -/
def isErrorContext : Val → Bool
  | .errorContext _ => true
  | _ => false

mutual
/-- Executable typing check; `typeCheck?_iff` proves it decides `HasType`. -/
def typeCheck? : WIT.ClosedType R → Val → Bool
  | .ref e, _ => nomatch e
  | .prim p, v => primCheck p v
  | .list u, v => listCheck (typeCheck? u) v
  | .fixedList u n, v => fixedListCheck n (typeCheck? u) v
  | .record fs, v => recordCheck (typeCheckFields? fs) v
  | .tuple ts, v => recordCheck (typeCheckList? ts) v
  | .variant cs, v => variantCheck (typeCheckCases? cs) v
  | .enum ls, v => enumCheck ls.length v
  | .flags ls, v => flagsCheck ls.length v
  | .option u, v => optionCheck (typeCheck? u) v
  | .result a b, v => resultCheck (typeCheckOpt? a) (typeCheckOpt? b) v
  | .map k u, v => listCheck (mapEntryCheck k (typeCheck? u)) v
  | .own _, v => isOwn v
  | .borrow _, v => isBorrow v
  | .stream _, v => isStream v
  | .future _, v => isFuture v
  | .errorContext, v => isErrorContext v

/-- Record fields, pointwise. -/
def typeCheckFields? : List (String × WIT.ClosedType R) → List Val → Bool
  | [], [] => true
  | (_, t) :: fs, v :: vs => typeCheck? t v && typeCheckFields? fs vs
  | _, _ => false

/-- Tuple components, pointwise. -/
def typeCheckList? : List (WIT.ClosedType R) → List Val → Bool
  | [], [] => true
  | t :: ts, v :: vs => typeCheck? t v && typeCheckList? ts vs
  | _, _ => false

/-- Variant case `c` with payload `p`. -/
def typeCheckCases? : List (String × Option (WIT.ClosedType R)) → Nat → Option Val → Bool
  | [], _, _ => false
  | (_, t) :: _, 0, p => typeCheckOpt? t p
  | _ :: cs, c + 1, p => typeCheckCases? cs c p

/-- Optional payloads. -/
def typeCheckOpt? : Option (WIT.ClosedType R) → Option Val → Bool
  | none, none => true
  | some t, some v => typeCheck? t v
  | _, _ => false
end

/-! ## Correctness of the check, case by case -/

theorem primCheck_iff (p : WIT.Primitive) (v : Val) :
    primCheck p v = true ↔ HasType (R := R) v (.prim p) := by
  constructor
  · intro h
    cases v <;> cases p <;>
      simp_all only [primCheck, Bool.false_eq_true, decide_eq_true_eq, Bool.and_eq_true,
        beq_iff_eq] <;>
      first
        | exact .bool _ | exact .f32 _ | exact .f64 _ | exact .char _ | exact .string h
        | exact .int h.1 h.2
  · intro h
    cases h with
    | bool => rfl
    | f32 => rfl
    | f64 => rfl
    | char => rfl
    | string hv => simp only [primCheck, hv, decide_true]
    | int hk hr => cases p <;> simp_all [primCheck, IntKind.ofPrimitive]

theorem listCheck_iff {u : WIT.ClosedType R} {f : Val → Bool}
    (hf : ∀ x, f x = true ↔ HasType x u) (v : Val) :
    listCheck f v = true ↔ HasType v (.list u) := by
  cases v with
  | list vs =>
    simp only [listCheck, List.all_eq_true]
    constructor
    · intro h; exact .list fun x hx => (hf x).1 (h x hx)
    · intro h; cases h with | list h => exact fun x hx => (hf x).2 (h x hx)
  | _ => exact ⟨nofun, nofun⟩

theorem fixedListCheck_iff {u : WIT.ClosedType R} {n : Nat} {f : Val → Bool}
    (hf : ∀ x, f x = true ↔ HasType x u) (v : Val) :
    fixedListCheck n f v = true ↔ HasType v (.fixedList u n) := by
  cases v with
  | list vs =>
    simp only [fixedListCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro h; exact .fixedList h.1 fun x hx => (hf x).1 (h.2 x hx)
    · intro h
      cases h with | fixedList hl h => exact ⟨hl, fun x hx => (hf x).2 (h x hx)⟩
  | _ => exact ⟨nofun, nofun⟩

theorem recordCheck_iff {fs : List (String × WIT.ClosedType R)} {g : List Val → Bool}
    (hg : ∀ vs, g vs = true ↔ HasFields vs fs) (v : Val) :
    recordCheck g v = true ↔ HasType v (.record fs) := by
  cases v with
  | record vs =>
    simp only [recordCheck]
    exact ⟨fun h => .record ((hg vs).1 h),
      fun h => by cases h with | record h => exact (hg vs).2 h⟩
  | _ => exact ⟨nofun, nofun⟩

theorem variantCheck_iff {cs : List (String × Option (WIT.ClosedType R))}
    {g : Nat → Option Val → Bool} (hg : ∀ c p, g c p = true ↔ HasCase c p cs) (v : Val) :
    variantCheck g v = true ↔ HasType v (.variant cs) := by
  cases v with
  | variant c p =>
    simp only [variantCheck]
    exact ⟨fun h => .variant ((hg c p).1 h),
      fun h => by cases h with | variant h => exact (hg c p).2 h⟩
  | _ => exact ⟨nofun, nofun⟩

theorem flagsCheck_iff (ls : List String) (v : Val) :
    flagsCheck ls.length v = true ↔ HasType (R := R) v (.flags ls) := by
  cases v with
  | flags bs =>
    simp only [flagsCheck, beq_iff_eq]
    exact ⟨fun h => .flags h, fun h => by cases h with | flags h => exact h⟩
  | _ => exact ⟨nofun, nofun⟩

theorem hasCase_enum_iff (ls : List String) (c : Nat) (p : Option Val) :
    HasCase (R := R) c p (ls.map fun l => (l, none)) ↔ p = none ∧ c < ls.length := by
  induction ls generalizing c with
  | nil => exact ⟨nofun, fun h => absurd h.2 (Nat.not_lt_zero _)⟩
  | cons l ls ih =>
    cases c with
    | zero =>
      simp only [List.map_cons, List.length_cons, Nat.zero_lt_succ, and_true]
      constructor
      · intro h; cases h with | here h => cases h; rfl
      · rintro rfl; exact .here .none
    | succ c =>
      simp only [List.map_cons, List.length_cons, Nat.add_lt_add_iff_right]
      constructor
      · intro h; cases h with | there h => exact (ih c).1 h
      · intro h; exact .there ((ih c).2 h)

theorem hasType_tuple_iff (ts : List (WIT.ClosedType R)) (v : Val) :
    HasType v (.tuple ts) ↔ HasType v (.record (tupleFieldsFrom 0 ts)) :=
  ⟨fun h => by cases h with | tuple h => exact h, fun h => .tuple h⟩

theorem hasType_enum_iff (ls : List String) (v : Val) :
    HasType (R := R) v (.enum ls) ↔
      HasType (R := R) v (.variant (ls.map fun l => (l, none))) :=
  ⟨fun h => by cases h with | enum h => exact h, fun h => .enum h⟩

theorem hasType_option_iff (u : WIT.ClosedType R) (v : Val) :
    HasType v (.option u) ↔ HasType v (.variant [("none", none), ("some", some u)]) :=
  ⟨fun h => by cases h with | option h => exact h, fun h => .option h⟩

theorem hasType_result_iff (a b : Option (WIT.ClosedType R)) (v : Val) :
    HasType v (.result a b) ↔ HasType v (.variant [("ok", a), ("error", b)]) :=
  ⟨fun h => by cases h with | result h => exact h, fun h => .result h⟩

theorem hasType_map_iff (k : WIT.KeyType) (u : WIT.ClosedType R) (v : Val) :
    HasType v (.map k u) ↔ HasType v (.list (.record (mapEntryFields k u))) :=
  ⟨fun h => by cases h with | map h => exact h, fun h => .map h⟩

theorem enumCheck_iff (ls : List String) (v : Val) :
    enumCheck ls.length v = true ↔ HasType (R := R) v (.enum ls) := by
  rw [hasType_enum_iff]
  cases v with
  | variant c p =>
    constructor
    · intro h
      cases p with
      | none =>
        simp only [enumCheck, decide_eq_true_eq] at h
        exact .variant ((hasCase_enum_iff ls c none).2 ⟨rfl, h⟩)
      | some _ => simp only [enumCheck, Bool.false_eq_true] at h
    · intro h
      cases h with
      | variant h =>
        obtain ⟨rfl, hc⟩ := (hasCase_enum_iff ls c p).1 h
        simp only [enumCheck, decide_eq_true_eq]; exact hc
  | _ => exact ⟨nofun, nofun⟩

theorem optionCheck_iff {u : WIT.ClosedType R} {f : Val → Bool}
    (hf : ∀ x, f x = true ↔ HasType x u) (v : Val) :
    optionCheck f v = true ↔ HasType v (.option u) := by
  rw [hasType_option_iff]
  constructor
  · intro h
    match v, h with
    | .variant 0 none, _ => exact .variant (.here .none)
    | .variant 1 (some x), h => exact .variant (.there (.here (.some ((hf x).1 h))))
  · intro h
    cases h with
    | variant h =>
      cases h with
      | here h => cases h; rfl
      | there h =>
        cases h with
        | here h => cases h with | some h => exact (hf _).2 h
        | there h => cases h

theorem resultCheck_iff {a b : Option (WIT.ClosedType R)} {fa fb : Option Val → Bool}
    (ha : ∀ p, fa p = true ↔ HasOpt p a) (hb : ∀ p, fb p = true ↔ HasOpt p b) (v : Val) :
    resultCheck fa fb v = true ↔ HasType v (.result a b) := by
  rw [hasType_result_iff]
  constructor
  · intro h
    match v, h with
    | .variant 0 p, h => exact .variant (.here ((ha p).1 h))
    | .variant 1 p, h => exact .variant (.there (.here ((hb p).1 h)))
  · intro h
    cases h with
    | variant h =>
      cases h with
      | here h => exact (ha _).2 h
      | there h =>
        cases h with
        | here h => exact (hb _).2 h
        | there h => cases h

theorem mapEntryCheck_iff {k : WIT.KeyType} {u : WIT.ClosedType R} {f : Val → Bool}
    (hf : ∀ x, f x = true ↔ HasType x u) (v : Val) :
    mapEntryCheck k f v = true ↔ HasType v (.record (mapEntryFields k u)) := by
  constructor
  · intro h
    match v, h with
    | .record [a, b], h =>
      simp only [mapEntryCheck, Bool.and_eq_true] at h
      exact .record (.cons ((primCheck_iff _ a).1 h.1) (.cons ((hf b).1 h.2) .nil))
  · intro h
    cases h with
    | record h =>
      cases h with
      | cons ha h =>
        cases h with
        | cons hb h =>
          cases h
          simp only [mapEntryCheck, Bool.and_eq_true]
          exact ⟨(primCheck_iff _ _).2 ha, (hf _).2 hb⟩

theorem mapCheck_iff {k : WIT.KeyType} {u : WIT.ClosedType R} {f : Val → Bool}
    (hf : ∀ x, f x = true ↔ HasType x u) (v : Val) :
    listCheck (mapEntryCheck k f) v = true ↔ HasType v (.map k u) := by
  rw [hasType_map_iff]; exact listCheck_iff (mapEntryCheck_iff hf) v

/-! ## `typeCheck?` decides `HasType` -/

mutual
/-- `typeCheck?` decides `HasType`. -/
theorem typeCheck?_iff : ∀ (t : WIT.ClosedType R) (v : Val),
    typeCheck? t v = true ↔ HasType v t
  | .ref e, _ => nomatch e
  | .prim p, v => by rw [typeCheck?]; exact primCheck_iff p v
  | .list u, v => by rw [typeCheck?]; exact listCheck_iff (typeCheck?_iff u) v
  | .fixedList u n, v => by rw [typeCheck?]; exact fixedListCheck_iff (typeCheck?_iff u) v
  | .record fs, v => by rw [typeCheck?]; exact recordCheck_iff (typeCheckFields?_iff fs) v
  | .tuple ts, v => by
    rw [typeCheck?, hasType_tuple_iff]; exact recordCheck_iff (typeCheckList?_iff ts 0) v
  | .variant cs, v => by rw [typeCheck?]; exact variantCheck_iff (typeCheckCases?_iff cs) v
  | .enum ls, v => by rw [typeCheck?]; exact enumCheck_iff ls v
  | .flags ls, v => by rw [typeCheck?]; exact flagsCheck_iff ls v
  | .option u, v => by rw [typeCheck?]; exact optionCheck_iff (typeCheck?_iff u) v
  | .result a b, v => by
    rw [typeCheck?]; exact resultCheck_iff (typeCheckOpt?_iff a) (typeCheckOpt?_iff b) v
  | .map k u, v => by rw [typeCheck?]; exact mapCheck_iff (typeCheck?_iff u) v
  | .own r, v => by
    rw [typeCheck?]
    cases v with
    | own => exact ⟨fun _ => .own _ _, fun _ => rfl⟩
    | _ => exact ⟨nofun, nofun⟩
  | .borrow r, v => by
    rw [typeCheck?]
    cases v with
    | borrow => exact ⟨fun _ => .borrow _ _, fun _ => rfl⟩
    | _ => exact ⟨nofun, nofun⟩
  | .stream u, v => by
    rw [typeCheck?]
    cases v with
    | stream => exact ⟨fun _ => .stream _ _, fun _ => rfl⟩
    | _ => exact ⟨nofun, nofun⟩
  | .future u, v => by
    rw [typeCheck?]
    cases v with
    | future => exact ⟨fun _ => .future _ _, fun _ => rfl⟩
    | _ => exact ⟨nofun, nofun⟩
  | .errorContext, v => by
    rw [typeCheck?]
    cases v with
    | errorContext => exact ⟨fun _ => .errorContext _, fun _ => rfl⟩
    | _ => exact ⟨nofun, nofun⟩

theorem typeCheckFields?_iff : ∀ (fs : List (String × WIT.ClosedType R)) (vs : List Val),
    typeCheckFields? fs vs = true ↔ HasFields vs fs
  | [], [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | [], _ :: _ => ⟨nofun, nofun⟩
  | _ :: _, [] => ⟨nofun, nofun⟩
  | (l, t) :: fs, v :: vs => by
    rw [typeCheckFields?, Bool.and_eq_true, typeCheck?_iff t v, typeCheckFields?_iff fs vs]
    exact ⟨fun h => .cons h.1 h.2, fun h => by cases h with | cons h1 h2 => exact ⟨h1, h2⟩⟩

theorem typeCheckList?_iff : ∀ (ts : List (WIT.ClosedType R)) (i : Nat) (vs : List Val),
    typeCheckList? ts vs = true ↔ HasFields vs (tupleFieldsFrom i ts)
  | [], _, [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | [], _, _ :: _ => ⟨nofun, nofun⟩
  | _ :: _, _, [] => ⟨nofun, nofun⟩
  | t :: ts, i, v :: vs => by
    rw [typeCheckList?, Bool.and_eq_true, typeCheck?_iff t v, typeCheckList?_iff ts (i + 1) vs,
      tupleFieldsFrom]
    exact ⟨fun h => .cons h.1 h.2, fun h => by cases h with | cons h1 h2 => exact ⟨h1, h2⟩⟩

theorem typeCheckCases?_iff :
    ∀ (cs : List (String × Option (WIT.ClosedType R))) (c : Nat) (p : Option Val),
      typeCheckCases? cs c p = true ↔ HasCase c p cs
  | [], _, _ => ⟨nofun, nofun⟩
  | (l, t) :: cs, 0, p => by
    rw [typeCheckCases?, typeCheckOpt?_iff t p]
    exact ⟨fun h => .here h, fun h => by cases h with | here h => exact h⟩
  | x :: cs, c + 1, p => by
    rw [typeCheckCases?, typeCheckCases?_iff cs c p]
    exact ⟨fun h => .there h, fun h => by cases h with | there h => exact h⟩

theorem typeCheckOpt?_iff : ∀ (t : Option (WIT.ClosedType R)) (p : Option Val),
    typeCheckOpt? t p = true ↔ HasOpt p t
  | none, none => ⟨fun _ => .none, fun _ => rfl⟩
  | none, some _ => ⟨nofun, nofun⟩
  | some _, none => ⟨nofun, nofun⟩
  | some t, some v => by
    rw [typeCheckOpt?, typeCheck?_iff t v]
    exact ⟨fun h => .some h, fun h => by cases h with | some h => exact h⟩
end

instance (v : Val) (t : WIT.ClosedType R) : Decidable (HasType v t) :=
  decidable_of_iff _ (typeCheck?_iff t v)

/-! ## NaN canonicalization -/

mutual
/-- Replace every float in a value by its canonical form (`ABI.canonicalizeNaN`, REF
`canonicalize_nan32/64`, L1294–1305): every NaN becomes the canonical NaN. -/
def canonicalizeNaN : Val → Val
  | .f32 b => .f32 (ABI.canonicalizeNaN .f32 b)
  | .f64 b => .f64 (ABI.canonicalizeNaN .f64 b)
  | .list vs => .list (canonicalizeNaNList vs)
  | .record vs => .record (canonicalizeNaNList vs)
  | .variant c p => .variant c (canonicalizeNaNOpt p)
  | v => v

/-- `canonicalizeNaN` on lists. -/
def canonicalizeNaNList : List Val → List Val
  | [] => []
  | v :: vs => canonicalizeNaN v :: canonicalizeNaNList vs

/-- `canonicalizeNaN` on optional payloads. -/
def canonicalizeNaNOpt : Option Val → Option Val
  | none => none
  | some v => some (canonicalizeNaN v)
end

/-- Every float in the value is canonical (no non-canonical NaN): the values of
`lift_flat`/`load`, which canonicalize every float they lift. -/
def IsNanCanonical (v : Val) : Prop := canonicalizeNaN v = v

instance (v : Val) : Decidable (IsNanCanonical v) := by unfold IsNanCanonical; infer_instance

/-! ## Tests -/

/-- The record type used by the typing tests. -/
def testPointType : WIT.ClosedType Nat :=
  .record [("x", .prim .s32), ("name", .prim .string), ("tags", .list (.prim .bool))]

end Val

end Silmaril.Wasm.Component.Value
