module

public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Computable interpreter: aggregate allocation rules

`aggNewStep?` executes the `AggregateStep` rules that allocate structures and
arrays: `struct.new`, `struct.new_default`, `array.new`, `array.new_default`,
`array.new_fixed`, `array.new_elem` (oob and alloc) and `array.new_data` (oob and
num). It is sound and complete with respect to `Head (profile o)` on these
instructions.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace AggNew

/-- The fields of an expanded structure type. -/
def structFields? : Option CCompType → Option (Ty (.list .field))
  | some (.struct fs) => some fs
  | _ => none

/-- The field of an expanded array type. -/
def arrayField? : Option CCompType → Option CFieldType
  | some (.array ft) => some ft
  | _ => none

theorem structFields?_eq_some {o : Option CCompType} {fs : Ty (.list .field)} :
    structFields? o = some fs ↔ o = some (.struct fs) := by
  rcases o with _ | ct
  · simp [structFields?]
  · cases ct <;> simp [structFields?]

theorem arrayField?_eq_some {o : Option CCompType} {ft : CFieldType} :
    arrayField? o = some ft ↔ o = some (.array ft) := by
  rcases o with _ | ct
  · simp [arrayField?]
  · cases ct <;> simp [arrayField?]

/-- The struct type of a type index. -/
def structType? (f : Frame) (x : TypeIdx) : Option (DefType × Ty (.list .field)) := do
  let d ← f.type? x
  let fs ← structFields? d.expand?
  return (d, fs)

/-- The array type of a type index. -/
def arrayType? (f : Frame) (x : TypeIdx) : Option (DefType × CFieldType) := do
  let d ← f.type? x
  let ft ← arrayField? d.expand?
  return (d, ft)

theorem structType?_eq_some {f : Frame} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)} :
    structType? f x = some (d, fs) ↔ f.type? x = some d ∧ Expand d (.struct fs) := by
  unfold structType?
  rw [Expand.iff, ← structFields?_eq_some]
  cases h : f.type? x with
  | none => simp
  | some d' =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases h' : structFields? d'.expand? with
    | none =>
      simp only [Option.bind_none, reduceCtorEq, false_iff, not_and]
      rintro ⟨⟩; rw [h']; simp
    | some fs' =>
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, h'⟩
      · rintro ⟨rfl, h''⟩; rw [h'] at h''; exact ⟨rfl, Option.some.inj h''⟩

theorem arrayType?_eq_some {f : Frame} {x : TypeIdx} {d : DefType} {ft : CFieldType} :
    arrayType? f x = some (d, ft) ↔ f.type? x = some d ∧ Expand d (.array ft) := by
  unfold arrayType?
  rw [Expand.iff, ← arrayField?_eq_some]
  cases h : f.type? x with
  | none => simp
  | some d' =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases h' : arrayField? d'.expand? with
    | none =>
      simp only [Option.bind_none, reduceCtorEq, false_iff, not_and]
      rintro ⟨⟩; rw [h']; simp
    | some ft' =>
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, h'⟩
      · rintro ⟨rfl, h''⟩; rw [h'] at h''; exact ⟨rfl, Option.some.inj h''⟩

/-- The top `k` values of `vs` (bottom-first). -/
def top (vs : List Val) (k : Nat) : List Val := vs.drop (vs.length - k)

theorem top_append (q a : List Val) : top (q ++ a) a.length = a := by
  simp [top]

theorem length_top_le (vs : List Val) (k : Nat) : (top vs k).length ≤ vs.length := by
  simp [top]

/-- The top value is an `i32`. -/
def i32s1 : List Val → Option (BitVec 32)
  | [.num ⟨.int .i32, n⟩] => some n
  | _ => none

/-- The top values are two `i32`s. -/
def i32s2 : List Val → Option (BitVec 32 × BitVec 32)
  | [.num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩] => some (i, n)
  | _ => none

/-- A value then an `i32`. -/
def valI32 : List Val → Option (Val × BitVec 32)
  | [v, .num ⟨.int .i32, n⟩] => some (v, n)
  | _ => none

theorem i32s1_eq_some {l : List Val} {n : BitVec 32} : i32s1 l = some n ↔ l = [.i32 n] := by
  constructor
  · intro h
    match l, h with
    | [.num ⟨.int .i32, n⟩], rfl => rfl
  · rintro rfl; rfl

theorem i32s2_eq_some {l : List Val} {i n : BitVec 32} :
    i32s2 l = some (i, n) ↔ l = [.i32 i, .i32 n] := by
  constructor
  · intro h
    match l, h with
    | [.num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩], rfl => rfl
  · rintro rfl; rfl

theorem valI32_eq_some {l : List Val} {v : Val} {n : BitVec 32} :
    valI32 l = some (v, n) ↔ l = [v, .i32 n] := by
  constructor
  · intro h
    match l, h with
    | [v, .num ⟨.int .i32, n⟩], rfl => rfl
  · rintro rfl; rfl

/-- `struct.new x`. -/
def structNew? (s : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) :
    Option (Nat × Config H) := do
  let (d, fs) ← structType? f x
  if fs.length ≤ vs.length ∧
      (fs.toList.zip (top vs fs.length)).all (fun p => packable (fieldStorage p.1) p.2) then
    some (fs.length, ⟨s.addStruct ⟨d, (fs.toList.zip (top vs fs.length)).map
      fun (ft, v) => packField (fieldStorage ft) v⟩, f, [.ref (.struct s.structs.length)]⟩)
  else none

/-- `struct.new_default x`. -/
def structNewDefault? (s : Store H) (f : Frame) (x : TypeIdx) : Option (Nat × Config H) := do
  let (_, fs) ← structType? f x
  let dv ← fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack)
  some (0, ⟨s, f, vals dv ++ [.plain (.structNew x)]⟩)

/-- `array.new x`. -/
def arrayNew? (s : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) :
    Option (Nat × Config H) := do
  let (v, n) ← valI32 (top vs 2)
  some (2, ⟨s, f, vals (List.replicate n.toNat v) ++
    [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩)

/-- `array.new_default x`. -/
def arrayNewDefault? (s : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) :
    Option (Nat × Config H) := do
  let n ← i32s1 (top vs 1)
  let (_, ft) ← arrayType? f x
  let v ← defaultVal? (fieldStorage ft).unpack
  some (1, ⟨s, f, vals (List.replicate n.toNat v) ++
    [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩)

/-- `array.new_fixed x n`. -/
def arrayNewFixed? (s : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) (n : Fin (2 ^ 32)) :
    Option (Nat × Config H) := do
  let (d, ft) ← arrayType? f x
  if n.val ≤ vs.length ∧ (top vs n.val).all (packable (fieldStorage ft)) then
    some (n.val, ⟨s.addArray ⟨d, (top vs n.val).map (packField (fieldStorage ft))⟩, f,
      [arrRef s.arrays.length]⟩)
  else none

/-- `array.new_elem x y`. -/
def arrayNewElem? (s : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) (y : ElemIdx) :
    Option (Nat × Config H) := do
  let (i, n) ← i32s2 (top vs 2)
  let (_, ei) ← s.elem? f y
  if ei.refs.length < i.toNat + n.toNat then
    some (2, ⟨s, f, [.trap]⟩)
  else
    some (2, ⟨s, f, ((ei.refs.drop i.toNat).take n.toNat).map .ref ++
      [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩)

/-- `array.new_data x y`. -/
def arrayNewData? (s : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) (y : DataIdx) :
    Option (Nat × Config H) := do
  let (i, n) ← i32s2 (top vs 2)
  let (_, ft) ← arrayType? f x
  let (_, di) ← s.data? f y
  if storageSize (fieldStorage ft) = 0 then none
  else if di.bytes.size < i.toNat + n.toNat * storageSize (fieldStorage ft) / 8 then
    some (2, ⟨s, f, [.trap]⟩)
  else
    let rs ← (List.range n.toNat).mapM (fun k =>
      readField? (fieldStorage ft) di.bytes (i.toNat + k * (storageSize (fieldStorage ft) / 8)))
    some (2, ⟨s, f, vals rs ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩)

end AggNew

open AggNew

/-- The seven allocating aggregate instructions. -/
def AggNewInstr : Admin → Prop
  | .plain (.structNew _) | .plain (.structNewDefault _) | .plain (.arrayNew _)
  | .plain (.arrayNewDefault _) | .plain (.arrayNewFixed ..) | .plain (.arrayNewElem ..)
  | .plain (.arrayNewData ..) => True
  | _ => False

/-- Head step of the aggregate allocation rules. -/
def aggNewStep? (_o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match e with
  | .plain (.structNew x) => structNew? s f vs x
  | .plain (.structNewDefault x) => structNewDefault? s f x
  | .plain (.arrayNew x) => arrayNew? s f vs x
  | .plain (.arrayNewDefault x) => arrayNewDefault? s f vs x
  | .plain (.arrayNewFixed x n) => arrayNewFixed? s f vs x n
  | .plain (.arrayNewElem x y) => arrayNewElem? s f vs x y
  | .plain (.arrayNewData x y) => arrayNewData? s f vs x y
  | _ => none

/-! ## Soundness -/

namespace AggNew

theorem top_eq_of_le {vs : List Val} {k : Nat} (h : k ≤ vs.length) : (top vs k).length = k := by
  simp [top]; omega

theorem le_of_top {vs : List Val} {k : Nat} {l : List Val} (h : top vs k = l) (hl : l.length = k) :
    k ≤ vs.length := by
  have := length_top_le vs k
  rw [h] at this; omega

theorem structNew?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {x : TypeIdx} {k : Nat} {c : Config H} (h : structNew? s f vs x = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) (.plain (.structNew x)) c := by
  unfold structNew? at h
  cases ht : structType? f x with
  | none => simp [ht] at h
  | some p =>
    obtain ⟨d, fs⟩ := p
    obtain ⟨hd, he⟩ := structType?_eq_some.mp ht
    simp only [ht, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hle.1, .aggregate (.structNew hd he (top_eq_of_le hle.1)
        (List.all_eq_true.mp hle.2))⟩
    · simp at h

theorem structNewDefault?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {x : TypeIdx} {k : Nat} {c : Config H} (h : structNewDefault? s f x = some (k, c)) :
    k ≤ vs.length ∧
      Head (profile o) s f (vs.drop (vs.length - k)) (.plain (.structNewDefault x)) c := by
  unfold structNewDefault? at h
  cases ht : structType? f x with
  | none => simp [ht] at h
  | some p =>
    obtain ⟨d, fs⟩ := p
    obtain ⟨hd, he⟩ := structType?_eq_some.mp ht
    simp only [ht, Option.bind_eq_bind, Option.bind_some] at h
    cases hm : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) with
    | none => simp [hm] at h
    | some dv =>
      simp only [hm, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨Nat.zero_le _, ?_⟩
      simp only [Nat.sub_zero, List.drop_length]
      exact .aggregate (.structNewDefault hd he hm)

theorem arrayNew?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {x : TypeIdx} {k : Nat} {c : Config H} (h : arrayNew? s f vs x = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) (.plain (.arrayNew x)) c := by
  unfold arrayNew? at h
  cases ht : valI32 (top vs 2) with
  | none => simp [ht] at h
  | some p =>
    obtain ⟨v, n⟩ := p
    have hl := valI32_eq_some.mp ht
    simp only [ht, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨le_of_top hl rfl, ?_⟩
    change Head _ s f (top vs 2) _ _
    rw [hl]
    exact .aggregate (.arrayNew v n)

theorem arrayNewDefault?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {x : TypeIdx} {k : Nat} {c : Config H} (h : arrayNewDefault? s f vs x = some (k, c)) :
    k ≤ vs.length ∧
      Head (profile o) s f (vs.drop (vs.length - k)) (.plain (.arrayNewDefault x)) c := by
  unfold arrayNewDefault? at h
  cases ht : i32s1 (top vs 1) with
  | none => simp [ht] at h
  | some n =>
    have hl := i32s1_eq_some.mp ht
    simp only [ht, Option.bind_eq_bind, Option.bind_some] at h
    cases ha : arrayType? f x with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨d, ft⟩ := p
      obtain ⟨hd, he⟩ := arrayType?_eq_some.mp ha
      simp only [ha, Option.bind_some] at h
      cases hv : defaultVal? (fieldStorage ft).unpack with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨le_of_top hl rfl, ?_⟩
        change Head _ s f (top vs 1) _ _
        rw [hl]
        exact .aggregate (.arrayNewDefault hd he hv)

theorem arrayNewFixed?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {x : TypeIdx} {n : Fin (2 ^ 32)} {k : Nat} {c : Config H}
    (h : arrayNewFixed? s f vs x n = some (k, c)) :
    k ≤ vs.length ∧
      Head (profile o) s f (vs.drop (vs.length - k)) (.plain (.arrayNewFixed x n)) c := by
  unfold arrayNewFixed? at h
  cases ha : arrayType? f x with
  | none => simp [ha] at h
  | some p =>
    obtain ⟨d, ft⟩ := p
    obtain ⟨hd, he⟩ := arrayType?_eq_some.mp ha
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hle.1, .aggregate (.arrayNewFixed hd he (top_eq_of_le hle.1)
        (List.all_eq_true.mp hle.2))⟩
    · simp at h

theorem arrayNewElem?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {x : TypeIdx} {y : ElemIdx} {k : Nat} {c : Config H}
    (h : arrayNewElem? s f vs x y = some (k, c)) :
    k ≤ vs.length ∧
      Head (profile o) s f (vs.drop (vs.length - k)) (.plain (.arrayNewElem x y)) c := by
  unfold arrayNewElem? at h
  cases ht : i32s2 (top vs 2) with
  | none => simp [ht] at h
  | some p =>
    obtain ⟨i, n⟩ := p
    have hl := i32s2_eq_some.mp ht
    simp only [ht, Option.bind_eq_bind, Option.bind_some] at h
    cases hel : s.elem? f y with
    | none => simp [hel] at h
    | some q =>
      obtain ⟨ea, ei⟩ := q
      simp only [hel, Option.bind_some] at h
      split at h
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨le_of_top hl rfl, ?_⟩
        change Head _ s f (top vs 2) _ _
        rw [hl]
        exact .aggregate (.arrayNewElemOob hel hlt)
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨le_of_top hl rfl, ?_⟩
        change Head _ s f (top vs 2) _ _
        rw [hl]
        exact .aggregate (.arrayNewElemAlloc hel (by omega))

theorem arrayNewData?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {x : TypeIdx} {y : DataIdx} {k : Nat} {c : Config H}
    (h : arrayNewData? s f vs x y = some (k, c)) :
    k ≤ vs.length ∧
      Head (profile o) s f (vs.drop (vs.length - k)) (.plain (.arrayNewData x y)) c := by
  unfold arrayNewData? at h
  cases ht : i32s2 (top vs 2) with
  | none => simp [ht] at h
  | some p =>
    obtain ⟨i, n⟩ := p
    have hl := i32s2_eq_some.mp ht
    simp only [ht, Option.bind_eq_bind, Option.bind_some] at h
    cases ha : arrayType? f x with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨d, ft⟩ := p
      obtain ⟨hd, he⟩ := arrayType?_eq_some.mp ha
      simp only [ha, Option.bind_some] at h
      cases hdat : s.data? f y with
      | none => simp [hdat] at h
      | some q =>
        obtain ⟨da, di⟩ := q
        simp only [hdat, Option.bind_some] at h
        split at h
        · simp at h
        rename_i hz0
        have hz : 0 < storageSize (fieldStorage ft) := Nat.pos_of_ne_zero hz0
        split at h
        · rename_i hlt
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨le_of_top hl rfl, ?_⟩
          change Head _ s f (top vs 2) _ _
          rw [hl]
          exact .aggregate (.arrayNewDataOob hd he hdat hz hlt)
        · rename_i hlt
          cases hm : (List.range n.toNat).mapM (fun k =>
              readField? (fieldStorage ft) di.bytes
                (i.toNat + k * (storageSize (fieldStorage ft) / 8))) with
          | none => simp [hm] at h
          | some rs =>
            simp only [hm, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨le_of_top hl rfl, ?_⟩
            change Head _ s f (top vs 2) _ _
            rw [hl]
            exact .aggregate (.arrayNewDataNum hd he hdat hz (by omega) hm)

end AggNew

theorem aggNewStep?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {k : Nat} {c : Config H} (h : aggNewStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  unfold aggNewStep? at h
  split at h
  · exact structNew?_sound h
  · exact structNewDefault?_sound h
  · exact arrayNew?_sound h
  · exact arrayNewDefault?_sound h
  · exact arrayNewFixed?_sound h
  · exact arrayNewElem?_sound h
  · exact arrayNewData?_sound h
  · simp at h

/-! ## Completeness -/

namespace AggNew

theorem vals_snoc_inj {a b : List Val} {e e' : Admin} (h : vals a ++ [e] = vals b ++ [e']) :
    a = b ∧ e = e' := by
  rw [append_singleton_inj, vals_inj] at h
  exact h

theorem i32s1_i32 (n : BitVec 32) : i32s1 [Val.i32 n] = some n := rfl
theorem i32s2_i32 (i n : BitVec 32) : i32s2 [Val.i32 i, Val.i32 n] = some (i, n) := rfl
theorem valI32_i32 (v : Val) (n : BitVec 32) : valI32 [v, Val.i32 n] = some (v, n) := rfl

variable {o : GrowOracle} {s : Store H} {f : Frame} {q args : List Val} {e : Admin}

theorem structNew_c {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)} {vs : List Val}
    (hl : vals args ++ [e] = vals vs ++ [.plain (.structNew x)])
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) :
    aggNewStep? o s f (q ++ args) e = some (args.length,
      ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩, f,
        [.ref (.struct s.structs.length)]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj hl
  have ht := structType?_eq_some.mpr ⟨hd, he⟩
  have htop := top_append q args
  rw [hn] at htop
  simp only [aggNewStep?, structNew?, ht, Option.bind_eq_bind, Option.bind_some, htop, hn,
    List.length_append]
  split
  · rfl
  · rename_i hne; exact absurd ⟨by omega, List.all_eq_true.mpr hp⟩ hne

theorem structNewDefault_c {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)} {vs : List Val}
    (hl : vals args ++ [e] = [.plain (.structNewDefault x)])
    (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hdef : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some vs) :
    aggNewStep? o s f (q ++ args) e = some (args.length,
      ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj (b := []) hl
  have ht := structType?_eq_some.mpr ⟨hd, he⟩
  simp [aggNewStep?, structNewDefault?, ht, hdef]

theorem arrayNew_c {x : TypeIdx} {v : Val} {n : BitVec 32}
    (hl : vals args ++ [e] = [v.toAdmin, constI32 n, .plain (.arrayNew x)]) :
    aggNewStep? o s f (q ++ args) e = some (args.length,
      ⟨s, f, vals (List.replicate n.toNat v) ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj (b := [v, .i32 n]) hl
  have htop := top_append q [v, .i32 n]
  simp only [List.length_cons, List.length_nil] at htop
  simp [aggNewStep?, arrayNew?, htop, valI32_i32]

theorem arrayNewDefault_c {x : TypeIdx} {n : BitVec 32} {d : DefType} {ft : CFieldType} {v : Val}
    (hl : vals args ++ [e] = [constI32 n, .plain (.arrayNewDefault x)])
    (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hv : defaultVal? (fieldStorage ft).unpack = some v) :
    aggNewStep? o s f (q ++ args) e = some (args.length,
      ⟨s, f, vals (List.replicate n.toNat v) ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj (b := [.i32 n]) hl
  have htop := top_append q [.i32 n]
  simp only [List.length_cons, List.length_nil] at htop
  have ht := arrayType?_eq_some.mpr ⟨hd, he⟩
  simp [aggNewStep?, arrayNewDefault?, htop, i32s1_i32, ht, hv]

theorem arrayNewFixed_c {x : TypeIdx} {n : Fin (2 ^ 32)} {d : DefType} {ft : CFieldType}
    {vs : List Val} (hl : vals args ++ [e] = vals vs ++ [.plain (.arrayNewFixed x n)])
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) :
    aggNewStep? o s f (q ++ args) e = some (args.length,
      ⟨s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩, f, [arrRef s.arrays.length]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj hl
  have ht := arrayType?_eq_some.mpr ⟨hd, he⟩
  have htop := top_append q args
  rw [hn] at htop
  simp only [aggNewStep?, arrayNewFixed?, ht, Option.bind_eq_bind, Option.bind_some, htop, hn,
    List.length_append]
  split
  · rfl
  · rename_i hne; exact absurd ⟨by omega, List.all_eq_true.mpr hp⟩ hne

theorem arrayNewElemOob_c {x : TypeIdx} {y : ElemIdx} {i n : BitVec 32} {ea : Nat} {ei : ElemInst}
    (hl : vals args ++ [e] = [constI32 i, constI32 n, .plain (.arrayNewElem x y)])
    (he : s.elem? f y = some (ea, ei)) (h : ei.refs.length < i.toNat + n.toNat) :
    aggNewStep? o s f (q ++ args) e = some (args.length, ⟨s, f, [.trap]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj (b := [.i32 i, .i32 n]) hl
  have htop := top_append q [.i32 i, .i32 n]
  simp only [List.length_cons, List.length_nil] at htop
  simp [aggNewStep?, arrayNewElem?, htop, i32s2_i32, he, h]

theorem arrayNewElemAlloc_c {x : TypeIdx} {y : ElemIdx} {i n : BitVec 32} {ea : Nat}
    {ei : ElemInst}
    (hl : vals args ++ [e] = [constI32 i, constI32 n, .plain (.arrayNewElem x y)])
    (he : s.elem? f y = some (ea, ei)) (h : i.toNat + n.toNat ≤ ei.refs.length) :
    aggNewStep? o s f (q ++ args) e = some (args.length,
      ⟨s, f, ((ei.refs.drop i.toNat).take n.toNat).map .ref ++
          [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj (b := [.i32 i, .i32 n]) hl
  have htop := top_append q [.i32 i, .i32 n]
  simp only [List.length_cons, List.length_nil] at htop
  have h' : ¬ ei.refs.length < i.toNat + n.toNat := by omega
  simp [aggNewStep?, arrayNewElem?, htop, i32s2_i32, he, h']

theorem arrayNewDataOob_c {x : TypeIdx} {y : DataIdx} {i n : BitVec 32}
    {d : DefType} {ft : CFieldType} {da : Nat} {di : DataInst}
    (hl : vals args ++ [e] = [constI32 i, constI32 n, .plain (.arrayNewData x y)])
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (hz : 0 < storageSize (fieldStorage ft))
    (h : di.bytes.size < i.toNat + n.toNat * storageSize (fieldStorage ft) / 8) :
    aggNewStep? o s f (q ++ args) e = some (args.length, ⟨s, f, [.trap]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj (b := [.i32 i, .i32 n]) hl
  have htop := top_append q [.i32 i, .i32 n]
  simp only [List.length_cons, List.length_nil] at htop
  have ht := arrayType?_eq_some.mpr ⟨hd, he⟩
  simp [aggNewStep?, arrayNewData?, htop, i32s2_i32, ht, hdat, h, hz.ne']

theorem arrayNewDataNum_c {x : TypeIdx} {y : DataIdx} {i n : BitVec 32}
    {d : DefType} {ft : CFieldType} {da : Nat} {di : DataInst} {vs : List Val}
    (hl : vals args ++ [e] = [constI32 i, constI32 n, .plain (.arrayNewData x y)])
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (hz : 0 < storageSize (fieldStorage ft))
    (hb : i.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size)
    (hvs : (List.range n.toNat).mapM (fun k =>
      readField? (fieldStorage ft) di.bytes (i.toNat + k * (storageSize (fieldStorage ft) / 8)))
        = some vs) :
    aggNewStep? o s f (q ++ args) e = some (args.length,
      ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩) := by
  obtain ⟨rfl, rfl⟩ := vals_snoc_inj (b := [.i32 i, .i32 n]) hl
  have htop := top_append q [.i32 i, .i32 n]
  simp only [List.length_cons, List.length_nil] at htop
  have ht := arrayType?_eq_some.mpr ⟨hd, he⟩
  have h' : ¬ di.bytes.size < i.toNat + n.toNat * storageSize (fieldStorage ft) / 8 := by omega
  simp [aggNewStep?, arrayNewData?, htop, i32s2_i32, ht, hdat, h', hvs, hz.ne']

end AggNew

theorem aggNewStep?_complete {o : GrowOracle} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {c : Config H} (h : Head (profile o) s f args e c) (hi : AggNewInstr e)
    (hvs : ∃ q, vs = q ++ args) : aggNewStep? o s f vs e = some (args.length, c) := by
  obtain ⟨q, rfl⟩ := hvs
  have hc : famOf e ≠ .control := by
    rcases e with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [AggNewInstr] at hi
    cases i <;> simp at hi <;> simp [famOf]
  have hf := h.fam_inv hc
  have hfa : famOf e = .aggregate := by
    rcases e with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [AggNewInstr] at hi
    cases i <;> simp at hi <;> rfl
  rw [hfa] at hf
  change AggregateStep ⟨s, f, vals args ++ [e]⟩ c at hf
  generalize hl : vals args ++ [e] = l at hf
  cases hf
  all_goals first
    | exact structNew_c hl ‹_› ‹_› ‹_› ‹_›
    | exact structNewDefault_c hl ‹_› ‹_› ‹_›
    | exact arrayNew_c hl
    | exact arrayNewDefault_c hl ‹_› ‹_› ‹_›
    | exact arrayNewFixed_c hl ‹_› ‹_› ‹_› ‹_›
    | exact arrayNewElemOob_c hl ‹_› ‹_›
    | exact arrayNewElemAlloc_c hl ‹_› ‹_›
    | exact arrayNewDataOob_c hl ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact arrayNewDataNum_c hl ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | (have he := congrArg List.getLast? hl
       simp at he
       subst he
       simp [AggNewInstr] at hi)

end Silmaril.Wasm.SingleThreaded.Exec
