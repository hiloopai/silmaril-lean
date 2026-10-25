module

public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Computable interpreter: aggregate access and bulk rules

`aggAccessStep?` executes the `AggregateStep` rules for `struct.get`,
`struct.set`, `array.get`, `array.set`, `array.len`, `array.fill`,
`array.copy`, `array.init_data` and `array.init_elem` at the head of a
configuration, with soundness and completeness against `Head`.

Each instruction has a helper in `Exec.AggAcc` that pattern-matches the value
stack *top-first* (`vs.reverse`). Overlapping trap rules are tried in a fixed
order (null before out-of-bounds, first operand before second).
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace AggAcc

/-- The trapping configuration. -/
def trapC (s : Store H) (f : Frame) : Config H := ⟨s, f, [.trap]⟩

/-- The fields of a structure type, via `Expand`. -/
def structFields? (d : DefType) : Option (Ty (.list .field)) :=
  match d.expand? with
  | some (.struct fs) => some fs
  | _ => none

/-- The field of an array type, via `Expand`. -/
def arrayField? (d : DefType) : Option CFieldType :=
  match d.expand? with
  | some (.array ft) => some ft
  | _ => none

/-- `a` is an allocated array and `bound` exceeds its length. -/
def oobA (s : Store H) (a bound : Nat) : Bool :=
  match s.arrays[a]? with
  | some ai => decide (ai.fields.length < bound)
  | none => false

/-- The element segment `y` exists and `bound` exceeds its length. -/
def oobE (s : Store H) (f : Frame) (y : ElemIdx) (bound : Nat) : Bool :=
  match s.elem? f y with
  | some (_, ei) => decide (ei.refs.length < bound)
  | none => false

/-- The array type `x` and data segment `y` exist and `j + n·|zt|/8` exceeds the segment. -/
def oobD (s : Store H) (f : Frame) (x : TypeIdx) (y : DataIdx) (j n : Nat) : Bool :=
  match f.type? x, s.data? f y with
  | some d, some (_, di) =>
    match arrayField? d with
    | some ft => decide (0 < storageSize (fieldStorage ft) ∧
        di.bytes.size < j + n * storageSize (fieldStorage ft) / 8)
    | none => false
  | _, _ => false

def structGet (s : Store H) (f : Frame) (sx : Option Signedness) (x : TypeIdx) (i : FieldIdx) :
    List Val → Option (Nat × Config H)
  | .ref .null :: _ => some (1, trapC s f)
  | .ref (.struct a) :: _ =>
    match s.structs[a]? with
    | none => none
    | some si =>
      match si.fields[i.toNat]? with
      | none => none
      | some fv =>
        match f.type? x with
        | none => none
        | some d =>
          match structFields? d with
          | none => none
          | some fs =>
            match fs.toList[i.toNat]? with
            | none => none
            | some ft =>
              if unpackable (fieldStorage ft) sx fv then
                some (1, ⟨s, f, [(unpackField sx fv).toAdmin]⟩)
              else none
  | _ => none

def structSet (s : Store H) (f : Frame) (x : TypeIdx) (i : FieldIdx) :
    List Val → Option (Nat × Config H)
  | _ :: .ref .null :: _ => some (2, trapC s f)
  | v :: .ref (.struct a) :: _ =>
    match s.structs[a]? with
    | none => none
    | some si =>
      if i.toNat < si.fields.length then
        match f.type? x with
        | none => none
        | some d =>
          match structFields? d with
          | none => none
          | some fs =>
            match fs.toList[i.toNat]? with
            | none => none
            | some ft =>
              if packable (fieldStorage ft) v then
                some (2, ⟨s.setStructField a i.toNat (packField (fieldStorage ft) v), f, []⟩)
              else none
      else none
  | _ => none

def arrayGet (s : Store H) (f : Frame) (sx : Option Signedness) (x : TypeIdx) :
    List Val → Option (Nat × Config H)
  | .num ⟨.int .i32, _⟩ :: .ref .null :: _ => some (2, trapC s f)
  | .num ⟨.int .i32, i⟩ :: .ref (.array a) :: _ =>
    match s.arrays[a]? with
    | none => none
    | some ai =>
      match ai.fields[i.toNat]? with
      | none => some (2, trapC s f)
      | some fv =>
        match f.type? x with
        | none => none
        | some d =>
          match arrayField? d with
          | none => none
          | some ft =>
            if unpackable (fieldStorage ft) sx fv then
              some (2, ⟨s, f, [(unpackField sx fv).toAdmin]⟩)
            else none
  | _ => none

def arraySet (s : Store H) (f : Frame) (x : TypeIdx) : List Val → Option (Nat × Config H)
  | _ :: .num ⟨.int .i32, _⟩ :: .ref .null :: _ => some (3, trapC s f)
  | v :: .num ⟨.int .i32, i⟩ :: .ref (.array a) :: _ =>
    match s.arrays[a]? with
    | none => none
    | some ai =>
      if i.toNat < ai.fields.length then
        match f.type? x with
        | none => none
        | some d =>
          match arrayField? d with
          | none => none
          | some ft =>
            if packable (fieldStorage ft) v then
              some (3, ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v), f, []⟩)
            else none
      else some (3, trapC s f)
  | _ => none

def arrayLen (s : Store H) (f : Frame) : List Val → Option (Nat × Config H)
  | .ref .null :: _ => some (1, trapC s f)
  | .ref (.array a) :: _ =>
    match s.arrays[a]? with
    | none => none
    | some ai => some (1, ⟨s, f, [constI32 (BitVec.ofNat 32 ai.fields.length)]⟩)
  | _ => none

def fillArr (s : Store H) (f : Frame) (x : TypeIdx) (a : Nat) (i : BitVec 32) (v : Val)
    (n : BitVec 32) : Option (Nat × Config H) :=
  match s.arrays[a]? with
  | none => none
  | some ai =>
    if ai.fields.length < i.toNat + n.toNat then some (4, trapC s f)
    else if n = 0 then some (4, ⟨s, f, []⟩)
    else some (4, ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.arrayFill x)]⟩)

def arrayFill (s : Store H) (f : Frame) (x : TypeIdx) : List Val → Option (Nat × Config H)
  | .num ⟨.int .i32, _⟩ :: _ :: .num ⟨.int .i32, _⟩ :: .ref .null :: _ => some (4, trapC s f)
  | .num ⟨.int .i32, n⟩ :: v :: .num ⟨.int .i32, i⟩ :: .ref (.array a) :: _ =>
    fillArr s f x a i v n
  | _ => none

def copyArr (s : Store H) (f : Frame) (x₁ x₂ : TypeIdx) (r₁ : Ref) (i₁ : BitVec 32) (r₂ : Ref)
    (i₂ n : BitVec 32) : Option (Nat × Config H) :=
  if r₁ = .null then some (5, trapC s f)
  else if r₂ = .null then some (5, trapC s f)
  else
    match r₁, r₂ with
    | .array a₁, .array a₂ =>
      if oobA s a₁ (i₁.toNat + n.toNat) then some (5, trapC s f)
      else if oobA s a₂ (i₂.toNat + n.toNat) then some (5, trapC s f)
      else
        match s.arrays[a₁]?, s.arrays[a₂]? with
        | some ai₁, some ai₂ =>
          if n = 0 then
            if i₁.toNat ≤ ai₁.fields.length ∧ i₂.toNat ≤ ai₂.fields.length then
              some (5, ⟨s, f, []⟩)
            else none
          else
            match f.type? x₂ with
            | none => none
            | some d₂ =>
              match arrayField? d₂ with
              | none => none
              | some ft₂ =>
                if i₁.toNat ≤ i₂.toNat then
                  some (5, ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂,
                    .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁),
                    arrRef a₁, constI32 (i₁ + 1), arrRef a₂, constI32 (i₂ + 1), constI32 (n - 1),
                    .plain (.arrayCopy x₁ x₂)]⟩)
                else
                  some (5, ⟨s, f, [arrRef a₁, constI32 (i₁ + n - 1), arrRef a₂,
                    constI32 (i₂ + n - 1),
                    .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁),
                    arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 (n - 1),
                    .plain (.arrayCopy x₁ x₂)]⟩)
        | _, _ => none
    | _, _ => none

def arrayCopy (s : Store H) (f : Frame) (x₁ x₂ : TypeIdx) : List Val → Option (Nat × Config H)
  | .num ⟨.int .i32, n⟩ :: .num ⟨.int .i32, i₂⟩ :: .ref r₂ :: .num ⟨.int .i32, i₁⟩ :: .ref r₁ :: _ =>
    copyArr s f x₁ x₂ r₁ i₁ r₂ i₂ n
  | _ => none

def initElemArr (s : Store H) (f : Frame) (x : TypeIdx) (y : ElemIdx) (r : Ref)
    (i j n : BitVec 32) : Option (Nat × Config H) :=
  if r = .null then some (4, trapC s f)
  else
    match r with
    | .array a =>
      if oobA s a (i.toNat + n.toNat) then some (4, trapC s f)
      else if oobE s f y (j.toNat + n.toNat) then some (4, trapC s f)
      else
        match s.arrays[a]?, s.elem? f y with
        | some ai, some (_, ei) =>
          if n = 0 then
            if i.toNat ≤ ai.fields.length ∧ j.toNat ≤ ei.refs.length then
              some (4, ⟨s, f, []⟩)
            else none
          else
            match ei.refs[j.toNat]? with
            | none => none
            | some r' =>
              some (4, ⟨s, f, [arrRef a, constI32 i, .ref r', .plain (.arraySet x),
                arrRef a, constI32 (i + 1), constI32 (j + 1), constI32 (n - 1),
                .plain (.arrayInitElem x y)]⟩)
        | _, _ => none
    | _ => none

def arrayInitElem (s : Store H) (f : Frame) (x : TypeIdx) (y : ElemIdx) :
    List Val → Option (Nat × Config H)
  | .num ⟨.int .i32, n⟩ :: .num ⟨.int .i32, j⟩ :: .num ⟨.int .i32, i⟩ :: .ref r :: _ =>
    initElemArr s f x y r i j n
  | _ => none

def initDataArr (s : Store H) (f : Frame) (x : TypeIdx) (y : DataIdx) (r : Ref)
    (i j n : BitVec 32) : Option (Nat × Config H) :=
  if r = .null then some (4, trapC s f)
  else
    match r with
    | .array a =>
      if oobA s a (i.toNat + n.toNat) then some (4, trapC s f)
      else if oobD s f x y j.toNat n.toNat then some (4, trapC s f)
      else
        match s.arrays[a]?, s.data? f y with
        | some ai, some (_, di) =>
          if n = 0 then
            if i.toNat ≤ ai.fields.length ∧ j.toNat ≤ di.bytes.size then
              some (4, ⟨s, f, []⟩)
            else none
          else
            match f.type? x with
            | none => none
            | some d =>
              match arrayField? d with
              | none => none
              | some ft =>
                match readField? (fieldStorage ft) di.bytes j.toNat with
                | none => none
                | some v =>
                  some (4, ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
                    arrRef a, constI32 (i + 1),
                    constI32 (j + BitVec.ofNat 32 (storageSize (fieldStorage ft) / 8)),
                    constI32 (n - 1), .plain (.arrayInitData x y)]⟩)
        | _, _ => none
    | _ => none

def arrayInitData (s : Store H) (f : Frame) (x : TypeIdx) (y : DataIdx) :
    List Val → Option (Nat × Config H)
  | .num ⟨.int .i32, n⟩ :: .num ⟨.int .i32, j⟩ :: .num ⟨.int .i32, i⟩ :: .ref r :: _ =>
    initDataArr s f x y r i j n
  | _ => none

end AggAcc

open AggAcc in
/-- Head step for the aggregate access and bulk instructions. `vs` is the whole
bottom-first value prefix; the result consumes its top `k` values. -/
def aggAccessStep? (_o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match e with
  | .plain (.structGet sx x i) => structGet s f sx x i vs.reverse
  | .plain (.structSet x i) => structSet s f x i vs.reverse
  | .plain (.arrayGet sx x) => arrayGet s f sx x vs.reverse
  | .plain (.arraySet x) => arraySet s f x vs.reverse
  | .plain .arrayLen => arrayLen s f vs.reverse
  | .plain (.arrayFill x) => arrayFill s f x vs.reverse
  | .plain (.arrayCopy x₁ x₂) => arrayCopy s f x₁ x₂ vs.reverse
  | .plain (.arrayInitElem x y) => arrayInitElem s f x y vs.reverse
  | .plain (.arrayInitData x y) => arrayInitData s f x y vs.reverse
  | _ => none

/-- The instructions handled by `aggAccessStep?`. -/
def AggAccessInstr : Admin → Prop
  | .plain (.structGet ..) | .plain (.structSet ..) | .plain (.arrayGet ..)
  | .plain (.arraySet _) | .plain .arrayLen | .plain (.arrayFill _) | .plain (.arrayCopy ..)
  | .plain (.arrayInitElem ..) | .plain (.arrayInitData ..) => True
  | _ => False

/-! ## Soundness -/

namespace AggAcc

theorem structFields?_eq {d : DefType} {fs : Ty (.list .field)} :
    structFields? d = some fs ↔ Expand d (.struct fs) := by
  rw [Expand.iff]; unfold structFields?
  split <;> simp_all

theorem arrayField?_eq {d : DefType} {ft : CFieldType} :
    arrayField? d = some ft ↔ Expand d (.array ft) := by
  rw [Expand.iff]; unfold arrayField?
  split <;> simp_all

theorem oobA_true {s : Store H} {a b : Nat} (h : oobA s a b = true) :
    ∃ ai, s.arrays[a]? = some ai ∧ ai.fields.length < b := by
  unfold oobA at h; split at h
  · exact ⟨_, ‹_›, by simpa using h⟩
  · cases h

theorem oobA_false {s : Store H} {a b : Nat} {ai : ArrayInst} (h : ¬ oobA s a b = true)
    (ha : s.arrays[a]? = some ai) : b ≤ ai.fields.length := by
  unfold oobA at h; rw [ha] at h; simpa using h

theorem oobE_true {s : Store H} {f : Frame} {y : ElemIdx} {b : Nat} (h : oobE s f y b = true) :
    ∃ ea ei, s.elem? f y = some (ea, ei) ∧ ei.refs.length < b := by
  unfold oobE at h; split at h
  · exact ⟨_, _, ‹_›, by simpa using h⟩
  · cases h

theorem oobE_false {s : Store H} {f : Frame} {y : ElemIdx} {b ea : Nat} {ei : ElemInst}
    (h : ¬ oobE s f y b = true) (he : s.elem? f y = some (ea, ei)) : b ≤ ei.refs.length := by
  unfold oobE at h; rw [he] at h; simpa using h

theorem oobD_true {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {j n : Nat}
    (h : oobD s f x y j n = true) :
    ∃ d ft da di, f.type? x = some d ∧ Expand d (.array ft) ∧ s.data? f y = some (da, di) ∧
      0 < storageSize (fieldStorage ft) ∧
      di.bytes.size < j + n * storageSize (fieldStorage ft) / 8 := by
  unfold oobD at h
  split at h
  · rename_i d da di hd hdat
    split at h
    · simp only [decide_eq_true_eq] at h
      exact ⟨d, _, da, di, hd, arrayField?_eq.mp ‹_›, hdat, h.1, h.2⟩
    · cases h
  · cases h

theorem oobD_false {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {j n da : Nat}
    {d : DefType} {ft : CFieldType} {di : DataInst}
    (h : ¬ oobD s f x y j n = true) (hd : f.type? x = some d) (he : arrayField? d = some ft)
    (hdat : s.data? f y = some (da, di)) (hz : 0 < storageSize (fieldStorage ft)) :
    j + n * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size := by
  unfold oobD at h; rw [hd, hdat] at h; simp only [he, decide_eq_true_eq] at h
  exact Nat.le_of_not_lt fun h' => h ⟨hz, h'⟩

/-- The result of a helper: it consumed the top `xs` (bottom-first) of `rv`
(top-first) and took an `AggregateStep`. -/
def Ok (s : Store H) (f : Frame) (e : Admin) (rv : List Val) (k : Nat) (c : Config H) : Prop :=
  ∃ xs r, rv = xs.reverse ++ r ∧ k = xs.length ∧ AggregateStep ⟨s, f, vals xs ++ [e]⟩ c

theorem structGet_sound {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {i : FieldIdx} {rv : List Val} {k : Nat} {c : Config H}
    (h : structGet s f sx x i rv = some (k, c)) : Ok s f (.plain (.structGet sx x i)) rv k c := by
  unfold structGet at h
  split at h
  · cases h; exact ⟨[.ref .null], _, rfl, rfl, .structGetNull⟩
  · split at h
    · cases h
    · rename_i si hsi
      split at h
      · cases h
      · rename_i fv hfv
        split at h
        · cases h
        · rename_i d hd
          split at h
          · cases h
          · rename_i fs hfs
            split at h
            · cases h
            · rename_i ft hft
              split at h
              · cases h
                exact ⟨[.ref (.struct _)], _, rfl, rfl,
                  .structGetStruct hsi hfv hd (structFields?_eq.mp hfs) hft ‹_›⟩
              · cases h
  · cases h

theorem structSet_sound {s : Store H} {f : Frame} {x : TypeIdx}
    {i : FieldIdx} {rv : List Val} {k : Nat} {c : Config H}
    (h : structSet s f x i rv = some (k, c)) : Ok s f (.plain (.structSet x i)) rv k c := by
  unfold structSet at h
  split at h
  · cases h; exact ⟨[.ref .null, _], _, rfl, rfl, .structSetNull⟩
  · split at h
    · cases h
    · rename_i si hsi
      split at h
      · rename_i hlt
        split at h
        · cases h
        · rename_i d hd
          split at h
          · cases h
          · rename_i fs hfs
            split at h
            · cases h
            · rename_i ft hft
              split at h
              · cases h
                exact ⟨[.ref (.struct _), _], _, rfl, rfl,
                  .structSetStruct hd (structFields?_eq.mp hfs) hft hsi hlt ‹_›⟩
              · cases h
      · cases h
  · cases h

theorem arrayGet_sound {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {rv : List Val} {k : Nat} {c : Config H}
    (h : arrayGet s f sx x rv = some (k, c)) : Ok s f (.plain (.arrayGet sx x)) rv k c := by
  unfold arrayGet at h
  split at h
  · cases h; exact ⟨[.ref .null, .num ⟨.int .i32, _⟩], _, rfl, rfl, .arrayGetNull⟩
  · split at h
    · cases h
    · rename_i ai hai
      split at h
      · cases h
        exact ⟨[.ref (.array _), .num ⟨.int .i32, _⟩], _, rfl, rfl,
          .arrayGetOob hai (List.getElem?_eq_none_iff.mp ‹_›)⟩
      · rename_i fv hfv
        split at h
        · cases h
        · rename_i d hd
          split at h
          · cases h
          · rename_i ft hft
            split at h
            · cases h
              exact ⟨[.ref (.array _), .num ⟨.int .i32, _⟩], _, rfl, rfl,
                .arrayGetArray hai hfv hd (arrayField?_eq.mp hft) ‹_›⟩
            · cases h
  · cases h

theorem arraySet_sound {s : Store H} {f : Frame} {x : TypeIdx}
    {rv : List Val} {k : Nat} {c : Config H}
    (h : arraySet s f x rv = some (k, c)) : Ok s f (.plain (.arraySet x)) rv k c := by
  unfold arraySet at h
  split at h
  · cases h; exact ⟨[.ref .null, .num ⟨.int .i32, _⟩, _], _, rfl, rfl, .arraySetNull⟩
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i ft hft
            split at h
            · cases h
              exact ⟨[.ref (.array _), .num ⟨.int .i32, _⟩, _], _, rfl, rfl,
                .arraySetArray ‹_› ‹_› ‹_› (arrayField?_eq.mp hft) ‹_›⟩
            · cases h
      · cases h
        exact ⟨[.ref (.array _), .num ⟨.int .i32, _⟩, _], _, rfl, rfl,
          .arraySetOob ‹_› (Nat.le_of_not_lt ‹_›)⟩
  · cases h

theorem arrayLen_sound {s : Store H} {f : Frame}
    {rv : List Val} {k : Nat} {c : Config H}
    (h : arrayLen s f rv = some (k, c)) : Ok s f (.plain .arrayLen) rv k c := by
  unfold arrayLen at h
  split at h
  · cases h; exact ⟨[.ref .null], _, rfl, rfl, .arrayLenNull⟩
  · split at h
    · cases h
    · cases h
      exact ⟨[.ref (.array _)], _, rfl, rfl, .arrayLenArray ‹_›⟩
  · cases h

theorem fillArr_sound {s : Store H} {f : Frame} {x : TypeIdx} {a : Nat} {i n : BitVec 32}
    {v : Val} {k : Nat} {c : Config H} (h : fillArr s f x a i v n = some (k, c)) :
    k = 4 ∧ AggregateStep ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n,
      .plain (.arrayFill x)]⟩ c := by
  unfold fillArr at h
  split at h
  · cases h
  · rename_i ai ha
    split at h
    · cases h; exact ⟨rfl, .arrayFillOob ha ‹_›⟩
    · split at h
      · cases h; subst n; exact ⟨rfl, .arrayFillZero ha (by omega)⟩
      · cases h; exact ⟨rfl, .arrayFillSucc ha (by omega) ‹_›⟩

theorem arrayFill_sound {s : Store H} {f : Frame} {x : TypeIdx}
    {rv : List Val} {k : Nat} {c : Config H}
    (h : arrayFill s f x rv = some (k, c)) : Ok s f (.plain (.arrayFill x)) rv k c := by
  unfold arrayFill at h
  split at h
  · cases h
    exact ⟨[.ref .null, .num ⟨.int .i32, _⟩, _, .num ⟨.int .i32, _⟩], _, rfl, rfl, .arrayFillNull⟩
  · obtain ⟨rfl, hs⟩ := fillArr_sound h
    exact ⟨[.ref (.array _), .num ⟨.int .i32, _⟩, _, .num ⟨.int .i32, _⟩], _, rfl, rfl, hs⟩
  · cases h

theorem copyArr_sound {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {r₁ r₂ : Ref}
    {i₁ i₂ n : BitVec 32} {k : Nat} {c : Config H}
    (h : copyArr s f x₁ x₂ r₁ i₁ r₂ i₂ n = some (k, c)) :
    k = 5 ∧ AggregateStep ⟨s, f, [.ref r₁, constI32 i₁, .ref r₂, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩ c := by
  unfold copyArr at h
  by_cases h1 : r₁ = .null
  · subst h1; rw [ite_eq_left rfl] at h; cases h; exact ⟨rfl, .arrayCopyNull₁⟩
  rw [ite_eq_right h1] at h
  by_cases h2 : r₂ = .null
  · subst h2; rw [ite_eq_left rfl] at h; cases h; exact ⟨rfl, .arrayCopyNull₂⟩
  rw [ite_eq_right h2] at h
  split at h
  · rename_i a₁ a₂
    split at h
    · cases h
      obtain ⟨ai, ha, hb⟩ := oobA_true ‹_›
      exact ⟨rfl, .arrayCopyOob₁ ha hb⟩
    · rename_i ho₁
      split at h
      · cases h
        obtain ⟨ai, ha, hb⟩ := oobA_true ‹_›
        exact ⟨rfl, .arrayCopyOob₂ ha hb⟩
      · rename_i ho₂
        split at h
        · rename_i ai₁ ai₂ ha₁ ha₂
          have hb₁ := oobA_false ho₁ ha₁
          have hb₂ := oobA_false ho₂ ha₂
          split at h
          · split at h
            · cases h; subst n; exact ⟨rfl, .arrayCopyZero ha₁ ha₂ ‹_›⟩
            · cases h
          · rename_i hn
            split at h
            · cases h
            · split at h
              · cases h
              · rename_i d₂ hd ft₂ hft
                split at h
                · cases h
                  exact ⟨rfl, .arrayCopyLe ha₁ ha₂ ⟨hb₁, hb₂⟩ hn ‹_› (arrayField?_eq.mp ‹_›) ‹_›⟩
                · cases h
                  exact ⟨rfl, .arrayCopyGt ha₁ ha₂ ⟨hb₁, hb₂⟩ hn ‹_› (arrayField?_eq.mp ‹_›)
                    (Nat.lt_of_not_le ‹_›)⟩
        · cases h
  · cases h

theorem arrayCopy_sound {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx}
    {rv : List Val} {k : Nat} {c : Config H}
    (h : arrayCopy s f x₁ x₂ rv = some (k, c)) : Ok s f (.plain (.arrayCopy x₁ x₂)) rv k c := by
  unfold arrayCopy at h
  split at h
  · obtain ⟨rfl, hs⟩ := copyArr_sound h
    exact ⟨[.ref _, .num ⟨.int .i32, _⟩, .ref _, .num ⟨.int .i32, _⟩, .num ⟨.int .i32, _⟩], _,
      rfl, rfl, hs⟩
  · cases h

theorem initElemArr_sound {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {r : Ref}
    {i j n : BitVec 32} {k : Nat} {c : Config H}
    (h : initElemArr s f x y r i j n = some (k, c)) :
    k = 4 ∧ AggregateStep ⟨s, f, [.ref r, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitElem x y)]⟩ c := by
  unfold initElemArr at h
  by_cases h1 : r = .null
  · subst h1; rw [ite_eq_left rfl] at h; cases h; exact ⟨rfl, .arrayInitElemNull⟩
  rw [ite_eq_right h1] at h
  split at h
  · rename_i a
    split at h
    · cases h
      obtain ⟨ai, ha, hb⟩ := oobA_true ‹_›
      exact ⟨rfl, .arrayInitElemOob₁ ha hb⟩
    · rename_i ho₁
      split at h
      · cases h
        obtain ⟨ea, ei, he, hb⟩ := oobE_true ‹_›
        exact ⟨rfl, .arrayInitElemOob₂ he hb⟩
      · rename_i ho₂
        split at h
        · rename_i ai ea ei ha he
          have hb₁ := oobA_false ho₁ ha
          have hb₂ := oobE_false ho₂ he
          split at h
          · split at h
            · cases h; subst n; exact ⟨rfl, .arrayInitElemZero ha he ‹_›⟩
            · cases h
          · rename_i hn
            split at h
            · cases h
            · cases h
              exact ⟨rfl, .arrayInitElemSucc ha he ⟨hb₁, hb₂⟩ hn ‹_›⟩
        · cases h
  · cases h

theorem arrayInitElem_sound {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {rv : List Val} {k : Nat} {c : Config H}
    (h : arrayInitElem s f x y rv = some (k, c)) :
    Ok s f (.plain (.arrayInitElem x y)) rv k c := by
  unfold arrayInitElem at h
  split at h
  · obtain ⟨rfl, hs⟩ := initElemArr_sound h
    exact ⟨[.ref _, .num ⟨.int .i32, _⟩, .num ⟨.int .i32, _⟩, .num ⟨.int .i32, _⟩], _,
      rfl, rfl, hs⟩
  · cases h

theorem initDataArr_sound {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {r : Ref}
    {i j n : BitVec 32} {k : Nat} {c : Config H}
    (h : initDataArr s f x y r i j n = some (k, c)) :
    k = 4 ∧ AggregateStep ⟨s, f, [.ref r, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitData x y)]⟩ c := by
  unfold initDataArr at h
  by_cases h1 : r = .null
  · subst h1; rw [ite_eq_left rfl] at h; cases h; exact ⟨rfl, .arrayInitDataNull⟩
  rw [ite_eq_right h1] at h
  split at h
  · rename_i a
    split at h
    · cases h
      obtain ⟨ai, ha, hb⟩ := oobA_true ‹_›
      exact ⟨rfl, .arrayInitDataOob₁ ha hb⟩
    · rename_i ho₁
      split at h
      · cases h
        obtain ⟨d, ft, da, di, hd, he, hdat, hz, hb⟩ := oobD_true ‹_›
        exact ⟨rfl, .arrayInitDataOob₂ hd he hdat hz hb⟩
      · rename_i ho₂
        split at h
        · rename_i ai da di ha hdat
          have hb₁ := oobA_false ho₁ ha
          split at h
          · split at h
            · cases h; subst n; exact ⟨rfl, .arrayInitDataZero ha hdat ‹_›⟩
            · cases h
          · rename_i hn
            split at h
            · cases h
            · rename_i d hd
              split at h
              · cases h
              · rename_i ft hft
                split at h
                · cases h
                · rename_i v hv
                  have hb₂ := oobD_false ho₂ hd hft hdat (storageSize_pos_of_readField hv)
                  cases h
                  exact ⟨rfl, .arrayInitDataNum ha hd (arrayField?_eq.mp hft) hdat ⟨hb₁, hb₂⟩ hn
                    ‹_›⟩
        · cases h
  · cases h

theorem arrayInitData_sound {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx}
    {rv : List Val} {k : Nat} {c : Config H}
    (h : arrayInitData s f x y rv = some (k, c)) :
    Ok s f (.plain (.arrayInitData x y)) rv k c := by
  unfold arrayInitData at h
  split at h
  · obtain ⟨rfl, hs⟩ := initDataArr_sound h
    exact ⟨[.ref _, .num ⟨.int .i32, _⟩, .num ⟨.int .i32, _⟩, .num ⟨.int .i32, _⟩], _,
      rfl, rfl, hs⟩
  · cases h

theorem ok_of_step {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {k : Nat} {c : Config H} (h : aggAccessStep? o s f vs e = some (k, c)) :
    Ok s f e vs.reverse k c := by
  unfold aggAccessStep? at h
  split at h
  · exact structGet_sound h
  · exact structSet_sound h
  · exact arrayGet_sound h
  · exact arraySet_sound h
  · exact arrayLen_sound h
  · exact arrayFill_sound h
  · exact arrayCopy_sound h
  · exact arrayInitElem_sound h
  · exact arrayInitData_sound h
  · cases h

end AggAcc

theorem aggAccessStep?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {e : Admin} {k : Nat} {c : Config H} (h : aggAccessStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  obtain ⟨xs, r, hr, rfl, hs⟩ := AggAcc.ok_of_step h
  have hvs : vs = r.reverse ++ xs := by
    rw [← List.reverse_reverse vs, hr]; simp
  subst hvs
  refine ⟨by simp, ?_⟩
  have hd : (r.reverse ++ xs).drop ((r.reverse ++ xs).length - xs.length) = xs := by
    simp
  rw [hd]
  exact .aggregate hs

/-! ## Completeness -/

namespace AggAcc

theorem famOf_of_instr {e : Admin} (h : AggAccessInstr e) : famOf e = .aggregate := by
  rcases e with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [AggAccessInstr] at h
  cases i <;> simp at h <;> rfl

theorem val?_of_instr {e : Admin} (h : AggAccessInstr e) : e.val? = none := by
  rcases e with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [AggAccessInstr] at h
  cases i <;> simp at h <;> rfl

end AggAcc

open AggAcc in
theorem aggAccessStep?_complete {o : GrowOracle} {s : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {c : Config H} (h : Head (profile o) s f args e c) (hi : AggAccessInstr e)
    (hq : ∃ q, vs = q ++ args) : aggAccessStep? o s f vs e = some (args.length, c) := by
  have hfam := famOf_of_instr hi
  have hf := h.fam_inv (by rw [hfam]; decide)
  rw [hfam] at hf
  change AggregateStep ⟨s, f, vals args ++ [e]⟩ c at hf
  have hev := val?_of_instr hi
  obtain ⟨q, rfl⟩ := hq
  generalize hl : vals args ++ [e] = l at hf
  have H := congrArg fnv hl
  rw [fnv_vals_append, fnv_cons_of_none hev] at H
  cases hf <;> simp only [fnv_vals_append, fnv_toAdmin_cons, fnv_ref_cons, constI32,
      arrRef] at H <;> (try rw [fnv_cons_of_none rfl] at H) <;>
    simp only [Prod.mk.injEq, List.cons.injEq, and_true, List.append_nil] at H <;>
    obtain ⟨rfl, rfl⟩ := H <;> simp [AggAccessInstr] at hi
  all_goals clear h hl hev hfam hi
  all_goals try simp only [← structFields?_eq, ← arrayField?_eq] at *
  all_goals simp [aggAccessStep?, structGet, structSet, arrayGet, arraySet, arrayLen, arrayFill,
    fillArr, arrayCopy, copyArr, arrayInitElem, initElemArr, arrayInitData, initDataArr, trapC,
    oobA, oobE, oobD, Val.i32, *]
  all_goals (repeat' split) <;> (try dsimp only [NumType.width, IntType.width] at *) <;>
    first | rfl | (exfalso; omega) | (simp_all; done) |
      ((split at * <;> simp_all); omega)

end Silmaril.Wasm.SingleThreaded.Exec
