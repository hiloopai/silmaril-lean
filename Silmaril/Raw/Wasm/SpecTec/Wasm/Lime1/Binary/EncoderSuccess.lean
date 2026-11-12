module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary.Encoder

/-! # When the Lime1 encoder succeeds

`encModule` (`Encoder.lean`) is partial: it fails on vectors, names, sections or function
bodies of `2³²` or more items or bytes, and on instructions with no opcode in the grammar's
tables. This file states exactly when it succeeds, so that the soundness theorem
`encModule_sound` is not vacuous:

* `Instr.hasEncoding`: every instruction has an opcode in the grammar's own tables
  (`plainTable`, `memTable`, the `0xFC` saturating truncations), and every `br_table` vector
  is shorter than `2³²`. The instructions the raw syntax has but no rule encodes are
  `i32.extend32_s` and the packed loads and stores whose width does not fit their type
  (`i32.load32_s`, `i32.store32`); `hasEncoding` is `false` exactly on modules that contain
  one of them (`encInstr_ok_iff`).
* `Encodable m`: the instruction condition on every expression, every vector and name
  shorter than `2³²`, and every section and function body shorter than `2³²` bytes. The
  sizes are stated through `lenOf`, the length of an encoding (`0` when there is none), so
  they are the actual byte sizes and not an approximation.
* `encModule_ok_iff : (∃ b, encModule m = .ok b) ↔ Encodable m`, and
  `encModule_isOk : Encodable m → ∃ b, encModule m = .ok b`.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Binary.Encoder

open Silmaril.Wasm.Binary

/-! ## `Except` success, compositionally -/

theorem ok_bind_iff {α β : Type} {x : Except Err α} {f : α → Except Err β} :
    (∃ b, (x >>= f) = .ok b) ↔ ∃ a, x = .ok a ∧ ∃ b, f a = .ok b := by
  cases x with
  | error e => simp only [reduceCtorEq, false_and, exists_false, iff_false, not_exists]; intro b h; cases h
  | ok a =>
    constructor
    · rintro ⟨b, h⟩; exact ⟨a, rfl, b, h⟩
    · rintro ⟨a', h, b, hb⟩; cases h; exact ⟨b, hb⟩

theorem ok_pure {α : Type} (a : α) : ∃ b, (pure a : Except Err α) = .ok b := ⟨a, rfl⟩

theorem ok_pure_iff {α : Type} (a : α) : (∃ b, (pure a : Except Err α) = .ok b) ↔ True :=
  iff_true_intro (ok_pure a)

theorem ok_ok_iff {α : Type} (a : α) : (∃ b, (Except.ok a : Except Err α) = .ok b) ↔ True :=
  iff_true_intro ⟨a, rfl⟩

theorem guardE_ok_iff {c : Prop} [Decidable c] {msg : Err} :
    (∃ u, guardE c msg = .ok u) ↔ c := by
  unfold guardE
  split
  · exact ⟨fun _ => ‹c›, fun _ => ⟨(), rfl⟩⟩
  · rename_i hc
    exact ⟨fun ⟨_, h⟩ => (by cases h), fun h => absurd h hc⟩

/-- The length of an encoding, `0` when there is none. -/
def lenOf (r : Except Err Bytes) : Nat :=
  match r with
  | .ok b => b.length
  | .error _ => 0

@[simp] theorem lenOf_ok (b : Bytes) : lenOf (.ok b) = b.length := rfl

theorem encSeq_ok_iff {α : Type} {f : α → Except Err Bytes} :
    ∀ xs : List α, (∃ b, encSeq f xs = .ok b) ↔ ∀ x ∈ xs, ∃ b, f x = .ok b
  | [] => by simp [encSeq]
  | a :: as => by
    simp only [encSeq, ok_bind_iff, List.forall_mem_cons, ← encSeq_ok_iff as]
    constructor
    · rintro ⟨b, hb, bs, hbs, _⟩; exact ⟨⟨b, hb⟩, bs, hbs⟩
    · rintro ⟨⟨b, hb⟩, bs, hbs⟩; exact ⟨b, hb, bs, hbs, ok_pure _⟩

theorem encVec_ok_iff {α : Type} {f : α → Except Err Bytes} {xs : List α} :
    (∃ b, encVec f xs = .ok b) ↔ xs.length < 2 ^ 32 ∧ ∀ x ∈ xs, ∃ b, f x = .ok b := by
  simp only [encVec, ok_bind_iff, ← encSeq_ok_iff xs]
  constructor
  · rintro ⟨u, hu, bs, hbs, _⟩; exact ⟨guardE_ok_iff.1 ⟨u, hu⟩, bs, hbs⟩
  · rintro ⟨hl, bs, hbs⟩
    obtain ⟨u, hu⟩ := guardE_ok_iff (msg := "vector longer than 2^32").2 hl
    exact ⟨u, hu, bs, hbs, ok_pure _⟩

theorem encSection_ok_iff {α : Type} {N : UInt8} {f : List α → Except Err Bytes}
    {xs : List α} :
    (∃ b, encSection N f xs = .ok b) ↔ xs = [] ∨ ((∃ c, f xs = .ok c) ∧ lenOf (f xs) < 2 ^ 32) := by
  cases xs with
  | nil => simp [encSection]
  | cons x xs =>
    simp only [encSection, ok_bind_iff, reduceCtorEq, false_or]
    constructor
    · rintro ⟨c, hc, u, hu, _⟩
      exact ⟨⟨c, hc⟩, by rw [hc]; exact guardE_ok_iff.1 ⟨u, hu⟩⟩
    · rintro ⟨⟨c, hc⟩, hl⟩
      rw [hc] at hl
      obtain ⟨u, hu⟩ := guardE_ok_iff (msg := "section longer than 2^32 bytes").2 hl
      exact ⟨c, hc, u, hu, ok_pure _⟩

theorem encName_ok_iff {s : String} :
    (∃ b, encName s = .ok b) ↔ s.toUTF8.data.toList.length < 2 ^ 32 := by
  simp only [encName, encVec_ok_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun x _ => ⟨[x], rfl⟩⟩⟩

/-! ## Instructions -/

/-- A conversion has an encoding: saturating truncations always, the rest by opcode. -/
def convertHasEncoding : ConvertOp → Bool
  | .truncSat _ _ _ => true
  | c => (plainOpcode? (.convert c)).isSome

mutual
/-- An instruction has an encoding: an opcode in the grammar's tables, and `br_table`
vectors shorter than `2³²`, recursively. -/
def Instr.hasEncoding : Lime1.Instr → Bool
  | .block _ body | .loop _ body => Instrs.hasEncoding body
  | .if_ _ th el => Instrs.hasEncoding th && Instrs.hasEncoding el
  | .brTable ls _ => decide (ls.length < 2 ^ 32)
  | i@(.intLoad _ _ a) | i@(.floatLoad _ a) | i@(.intStore _ _ a) | i@(.floatStore _ a) =>
    (memOpcode? i a).isSome
  | .convert c => convertHasEncoding c
  | i@.nop | i@.unreachable | i@.drop | i@.select | i@.return_ => (plainOpcode? i).isSome
  | i@(.intUnOp _ _) | i@(.intBinOp _ _) | i@(.intTestOp _ _) | i@(.intRelOp _ _) =>
    (plainOpcode? i).isSome
  | i@(.floatUnOp _ _) | i@(.floatBinOp _ _) | i@(.floatRelOp _ _) => (plainOpcode? i).isSome
  | .br _ | .brIf _ | .call _ | .callIndirect _ | .localGet _ | .localSet _ | .localTee _
  | .globalGet _ | .globalSet _ | .memorySize | .memoryGrow | .memoryCopy | .memoryFill
  | .intConst _ _ | .floatConst _ _ => true

/-- `Instr.hasEncoding` on every instruction of a sequence. -/
def Instrs.hasEncoding : List Lime1.Instr → Bool
  | [] => true
  | i :: is => Instr.hasEncoding i && Instrs.hasEncoding is
end

theorem encPlain_ok_iff {i : Lime1.Instr} :
    (∃ b, encPlain i = .ok b) ↔ (plainOpcode? i).isSome = true := by
  unfold encPlain
  split <;> rename_i h <;> simp [h]

theorem encMem_ok_iff {i : Lime1.Instr} {a : MemArg} :
    (∃ b, encMem i a = .ok b) ↔ (memOpcode? i a).isSome = true := by
  unfold encMem
  split <;> rename_i h <;> simp [h]

theorem encConvert_ok_iff {c : ConvertOp} :
    (∃ b, encConvert c = .ok b) ↔ convertHasEncoding c = true := by
  cases c <;> simp [encConvert, convertHasEncoding, encPlain_ok_iff]

mutual
theorem encInstr_ok_iff : ∀ i : Lime1.Instr, (∃ b, encInstr i = .ok b) ↔ Instr.hasEncoding i = true
  | .block t body => by
    simp only [encInstr, Instr.hasEncoding, ok_bind_iff, ← encInstrs_ok_iff body]
    exact ⟨fun ⟨b, hb, _⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb, ok_pure _⟩⟩
  | .loop t body => by
    simp only [encInstr, Instr.hasEncoding, ok_bind_iff, ← encInstrs_ok_iff body]
    exact ⟨fun ⟨b, hb, _⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb, ok_pure _⟩⟩
  | .if_ t th [] => by
    simp only [encInstr, Instr.hasEncoding, ok_bind_iff, ← encInstrs_ok_iff th,
      Instrs.hasEncoding, Bool.and_true]
    exact ⟨fun ⟨b, hb, _⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb, ok_pure _⟩⟩
  | .if_ t th (e :: es) => by
    simp only [encInstr, Instr.hasEncoding, ok_bind_iff, Bool.and_eq_true,
      ← encInstrs_ok_iff th, ← encInstrs_ok_iff (e :: es)]
    constructor
    · rintro ⟨b₁, h₁, b₂, h₂, _⟩; exact ⟨⟨b₁, h₁⟩, b₂, h₂⟩
    · rintro ⟨⟨b₁, h₁⟩, b₂, h₂⟩; exact ⟨b₁, h₁, b₂, h₂, ok_pure _⟩
  | .brTable ls l => by
    simp only [encInstr, Instr.hasEncoding, ok_bind_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨b, hb, _⟩; exact (encVec_ok_iff.1 ⟨b, hb⟩).1
    · intro hl
      obtain ⟨b, hb⟩ := encVec_ok_iff (f := fun x : LabelIdx => (.ok (encU x.toNat) :
        Except Err Bytes)) (xs := ls) |>.2 ⟨hl, fun x _ => ⟨_, rfl⟩⟩
      exact ⟨b, hb, ok_pure _⟩
  | .br _ | .brIf _ | .call _ | .callIndirect _ | .localGet _ | .localSet _ | .localTee _
  | .globalGet _ | .globalSet _ | .memorySize | .memoryGrow | .memoryCopy | .memoryFill =>
    by simp [encInstr, Instr.hasEncoding]
  | .intConst .i32 _ | .intConst .i64 _ | .floatConst .f32 _ | .floatConst .f64 _ =>
    by simp [encInstr, Instr.hasEncoding]
  | .intLoad _ _ _ | .floatLoad _ _ | .intStore _ _ _ | .floatStore _ _ => by
    simp only [encInstr, Instr.hasEncoding]; exact encMem_ok_iff
  | .convert c => by simp only [encInstr, Instr.hasEncoding]; exact encConvert_ok_iff
  | .nop | .unreachable | .drop | .select | .return_ | .intUnOp _ _ | .intBinOp _ _
  | .intTestOp _ _ | .intRelOp _ _ | .floatUnOp _ _ | .floatBinOp _ _ | .floatRelOp _ _ => by
    simp only [encInstr, Instr.hasEncoding]; exact encPlain_ok_iff

theorem encInstrs_ok_iff :
    ∀ is : List Lime1.Instr, (∃ b, encInstrs is = .ok b) ↔ Instrs.hasEncoding is = true
  | [] => by simp [encInstrs, Instrs.hasEncoding]
  | i :: is => by
    simp only [encInstrs, Instrs.hasEncoding, ok_bind_iff, Bool.and_eq_true,
      ← encInstr_ok_iff i, ← encInstrs_ok_iff is]
    constructor
    · rintro ⟨b₁, h₁, b₂, h₂, _⟩; exact ⟨⟨b₁, h₁⟩, b₂, h₂⟩
    · rintro ⟨⟨b₁, h₁⟩, b₂, h₂⟩; exact ⟨b₁, h₁, b₂, h₂, ok_pure _⟩
end

theorem encExpr_ok_iff {e : Lime1.Expr} :
    (∃ b, encExpr e = .ok b) ↔ Instrs.hasEncoding e = true := by
  simp only [encExpr, ok_bind_iff, ← encInstrs_ok_iff e]
  exact ⟨fun ⟨b, hb, _⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb, ok_pure _⟩⟩

/-- The two instructions of the raw syntax that the grammar cannot encode. -/
example : Instr.hasEncoding (.intUnOp .i64 (.extend .i32)) = true := by decide
example : Instr.hasEncoding (.intUnOp .i32 (.extend .i32)) = false := by decide

/-! ## Locals -/

theorem runs_pos {α : Type} [DecidableEq α] : ∀ (l : List α), ∀ p ∈ runs l, 0 < p.1
  | [] => by simp [runs]
  | a :: l => by
    have ih := runs_pos l
    unfold runs
    split
    · rename_i n b r hr
      rw [hr] at ih
      split
      · intro p hp
        simp only [List.mem_cons] at hp ih
        rcases hp with rfl | hp
        · simp
        · exact ih p (Or.inr hp)
      · intro p hp
        simp only [List.mem_cons] at hp ih
        rcases hp with rfl | rfl | hp
        · simp
        · exact ih _ (Or.inl rfl)
        · exact ih p (Or.inr hp)
    · simp

theorem runs_sum {α : Type} [DecidableEq α] (l : List α) :
    ((runs l).map (·.1)).sum = l.length := by
  have h := congrArg List.length (runs_flatten l)
  rw [List.length_flatten] at h
  simpa [Function.comp_def] using h

theorem le_sum_of_mem : ∀ {xs : List Nat} {x : Nat}, x ∈ xs → x ≤ xs.sum
  | _ :: _, _, .head _ => by simp
  | y :: _, _, .tail _ h => by have := le_sum_of_mem h; simp; omega

theorem length_le_sum : ∀ {xs : List Nat}, (∀ x ∈ xs, 0 < x) → xs.length ≤ xs.sum
  | [], _ => by simp
  | x :: xs, h => by
    have := length_le_sum (xs := xs) (fun y hy => h y (List.mem_cons_of_mem x hy))
    have := h x List.mem_cons_self
    simp; omega

theorem runs_bounds {α : Type} [DecidableEq α] {l : List α} (h : l.length < 2 ^ 32) :
    (runs l).length < 2 ^ 32 ∧ ∀ p ∈ runs l, p.1 < 2 ^ 32 := by
  have hs := runs_sum l
  refine ⟨?_, fun p hp => ?_⟩
  · have := length_le_sum (xs := (runs l).map (·.1))
      (fun x hx => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        exact runs_pos l p hp)
    simp only [List.length_map] at this
    omega
  · have := le_sum_of_mem (List.mem_map_of_mem (f := (·.1)) hp)
    omega

/-- The locals vector of a function. -/
def encLocals (locals : List V1.ValType) : Except Err Bytes := encVec encLocalRun (runs locals)

theorem encLocals_ok_iff {locals : List V1.ValType} (h : locals.length < 2 ^ 32) :
    ∃ b, encLocals locals = .ok b := by
  obtain ⟨h₁, h₂⟩ := runs_bounds h
  refine encVec_ok_iff.2 ⟨h₁, fun p hp => ?_⟩
  simp only [encLocalRun, ok_bind_iff]
  obtain ⟨u, hu⟩ := guardE_ok_iff (msg := "local run longer than 2^32").2 (h₂ p hp)
  exact ⟨u, hu, ok_pure _⟩

/-- The byte size of a function body (`locals` vector and expression) before its size
prefix. -/
def codeSize (f : Lime1.Func) : Nat := lenOf (encLocals f.locals) + lenOf (encExpr f.body)

theorem encCode_ok_iff {f : Lime1.Func} :
    (∃ b, encCode (f.locals, f.body) = .ok b) ↔
      f.locals.length < 2 ^ 32 ∧ Instrs.hasEncoding f.body = true ∧ codeSize f < 2 ^ 32 := by
  simp only [encCode, ok_bind_iff]
  constructor
  · rintro ⟨u, hu, bl, hl, be, he, u', hu', _⟩
    have h₁ := guardE_ok_iff.1 ⟨u, hu⟩
    have h₂ := guardE_ok_iff.1 ⟨u', hu'⟩
    refine ⟨h₁, encExpr_ok_iff.1 ⟨be, he⟩, ?_⟩
    simp only [codeSize, encLocals]
    rw [hl, he]
    simpa using h₂
  · rintro ⟨h₁, h₂, h₃⟩
    obtain ⟨u, hu⟩ := guardE_ok_iff (msg := "more than 2^32 locals").2 h₁
    obtain ⟨bl, hl⟩ := encLocals_ok_iff h₁
    obtain ⟨be, he⟩ := encExpr_ok_iff.2 h₂
    have h₄ : (bl ++ be).length < 2 ^ 32 := by
      simp only [codeSize, hl, he, lenOf_ok] at h₃; simpa using h₃
    obtain ⟨u', hu'⟩ := guardE_ok_iff (msg := "function body longer than 2^32 bytes").2 h₄
    exact ⟨u, hu, bl, hl, be, he, u', hu', ok_pure _⟩

/-! ## Module components -/

theorem encFuncType_ok_iff {t : V1.FuncType} :
    (∃ b, encFuncType t = .ok b) ↔ t.params.length < 2 ^ 32 ∧ t.results.length < 2 ^ 32 := by
  simp only [encFuncType, ok_bind_iff]
  constructor
  · rintro ⟨p, hp, r, hr, _⟩
    exact ⟨(encVec_ok_iff.1 ⟨p, hp⟩).1, (encVec_ok_iff.1 ⟨r, hr⟩).1⟩
  · rintro ⟨hp, hr⟩
    obtain ⟨p, hp'⟩ := encVec_ok_iff (f := fun v : V1.ValType => (.ok (encValType v) :
      Except Err Bytes)) (xs := t.params) |>.2 ⟨hp, fun _ _ => ⟨_, rfl⟩⟩
    obtain ⟨r, hr'⟩ := encVec_ok_iff (f := fun v : V1.ValType => (.ok (encValType v) :
      Except Err Bytes)) (xs := t.results) |>.2 ⟨hr, fun _ _ => ⟨_, rfl⟩⟩
    exact ⟨p, hp', r, hr', ok_pure _⟩

/-- Both names of an import, and an export's name, fit a `u32` length. -/
def NameFits (s : String) : Prop := s.toUTF8.data.toList.length < 2 ^ 32

theorem encImport_ok_iff {im : V1.Import} :
    (∃ b, encImport im = .ok b) ↔ NameFits im.moduleName ∧ NameFits im.name := by
  simp only [encImport, ok_bind_iff, NameFits, ← encName_ok_iff]
  constructor
  · rintro ⟨m, hm, n, hn, _⟩; exact ⟨⟨m, hm⟩, n, hn⟩
  · rintro ⟨⟨m, hm⟩, n, hn⟩; exact ⟨m, hm, n, hn, ok_pure _⟩

theorem encExport_ok_iff {ex : V1.Export} : (∃ b, encExport ex = .ok b) ↔ NameFits ex.name := by
  simp only [encExport, ok_bind_iff, NameFits, ← encName_ok_iff]
  exact ⟨fun ⟨n, hn, _⟩ => ⟨n, hn⟩, fun ⟨n, hn⟩ => ⟨n, hn, ok_pure _⟩⟩

theorem encGlobal_ok_iff {g : Lime1.Global} :
    (∃ b, encGlobal g = .ok b) ↔ Instrs.hasEncoding g.init = true := by
  simp only [encGlobal, ok_bind_iff, ← encExpr_ok_iff]
  exact ⟨fun ⟨e, he, _⟩ => ⟨e, he⟩, fun ⟨e, he⟩ => ⟨e, he, ok_pure _⟩⟩

theorem encElem_ok_iff {el : Lime1.Elem} :
    (∃ b, encElem el = .ok b) ↔ Instrs.hasEncoding el.offset = true ∧ el.init.length < 2 ^ 32 := by
  simp only [encElem, ok_bind_iff, ← encExpr_ok_iff]
  constructor
  · rintro ⟨e, he, ys, hys, _⟩
    exact ⟨⟨e, he⟩, (encVec_ok_iff.1 ⟨ys, hys⟩).1⟩
  · rintro ⟨⟨e, he⟩, hl⟩
    obtain ⟨ys, hys⟩ := encVec_ok_iff (f := fun x : FuncIdx => (.ok (encU x.toNat) :
      Except Err Bytes)) (xs := el.init) |>.2 ⟨hl, fun _ _ => ⟨_, rfl⟩⟩
    exact ⟨e, he, ys, hys, ok_pure _⟩

theorem encData_ok_iff {d : Lime1.Data} :
    (∃ b, encData d = .ok b) ↔ Instrs.hasEncoding d.offset = true ∧ d.bytes.size < 2 ^ 32 := by
  simp only [encData, ok_bind_iff, ← encExpr_ok_iff]
  constructor
  · rintro ⟨e, he, bs, hbs, _⟩
    have := (encVec_ok_iff.1 ⟨bs, hbs⟩).1
    have hsz : d.bytes.data.toList.length = d.bytes.size := Array.length_toList
    exact ⟨⟨e, he⟩, hsz ▸ this⟩
  · rintro ⟨⟨e, he⟩, hl⟩
    have hsz : d.bytes.data.toList.length = d.bytes.size := Array.length_toList
    obtain ⟨bs, hbs⟩ := encVec_ok_iff (f := fun x : UInt8 => (.ok [x] : Except Err Bytes))
      (xs := d.bytes.data.toList) |>.2 ⟨hsz ▸ hl, fun _ _ => ⟨_, rfl⟩⟩
    exact ⟨e, he, bs, hbs, ok_pure _⟩

theorem length_encU_le : ∀ n : Nat, (encU n).length ≤ n / 2 + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [encU]
    split
    · simp
    · have := ih (n / 128) (by omega)
      simp only [List.length_cons]
      omega

theorem encStart_ok {s : Option FuncIdx} (h : s.isSome) :
    ∃ c, encStart s.toList = .ok c ∧ c.length < 2 ^ 32 := by
  rcases s with _ | x
  · cases h
  · refine ⟨_, rfl, ?_⟩
    have := length_encU_le x.toNat
    have hx : x.toNat < 2 ^ 32 := x.value.isLt
    omega

/-! ## Modules -/

/-- The expressions of a module: function bodies, global initialisers, segment offsets. -/
def moduleExprs (m : Lime1.Module) : List Lime1.Expr :=
  m.funcs.map (·.body) ++ m.globals.map (·.init) ++ m.elems.map (·.offset) ++
    m.data.map (·.offset)

/-- **Exactly the modules the Lime1 encoder accepts.** Every field is a plain structural or
size condition on the module. -/
structure Encodable (m : Lime1.Module) : Prop where
  /-- Every instruction has an opcode, and every `br_table` vector fits. -/
  instrs : ∀ e ∈ moduleExprs m, Instrs.hasEncoding e = true
  /-- Every module-level vector is shorter than `2³²`. -/
  types : m.types.length < 2 ^ 32
  imports : m.imports.length < 2 ^ 32
  funcs : m.funcs.length < 2 ^ 32
  tables : m.tables.length < 2 ^ 32
  memories : m.memories.length < 2 ^ 32
  globals : m.globals.length < 2 ^ 32
  exports : m.exports.length < 2 ^ 32
  elems : m.elems.length < 2 ^ 32
  data : m.data.length < 2 ^ 32
  /-- Every inner vector and name is shorter than `2³²`. -/
  funcTypes : ∀ t ∈ m.types, t.params.length < 2 ^ 32 ∧ t.results.length < 2 ^ 32
  importNames : ∀ im ∈ m.imports, NameFits im.moduleName ∧ NameFits im.name
  exportNames : ∀ ex ∈ m.exports, NameFits ex.name
  locals : ∀ f ∈ m.funcs, f.locals.length < 2 ^ 32
  elemInits : ∀ e ∈ m.elems, e.init.length < 2 ^ 32
  dataBytes : ∀ d ∈ m.data, d.bytes.size < 2 ^ 32
  /-- Every function body, and every section, is shorter than `2³²` bytes. -/
  codeSizes : ∀ f ∈ m.funcs, codeSize f < 2 ^ 32
  typeSec : lenOf (encVec encFuncType m.types) < 2 ^ 32
  importSec : lenOf (encVec encImport m.imports) < 2 ^ 32
  funcSec : lenOf (encVec (fun x => .ok (encU (Idx.toNat x))) (m.funcs.map (·.type))) < 2 ^ 32
  tableSec : lenOf (encVec (fun t => .ok (encTableType t)) m.tables) < 2 ^ 32
  memSec : lenOf (encVec (fun t => .ok (encMemType t)) m.memories) < 2 ^ 32
  globalSec : lenOf (encVec encGlobal m.globals) < 2 ^ 32
  exportSec : lenOf (encVec encExport m.exports) < 2 ^ 32
  elemSec : lenOf (encVec encElem m.elems) < 2 ^ 32
  codeSec : lenOf (encVec encCode (m.funcs.map fun f => (f.locals, f.body))) < 2 ^ 32
  dataSec : lenOf (encVec encData m.data) < 2 ^ 32

/-- One section of `encModule`: it succeeds when its vector does and fits. -/
theorem section_ok {α : Type} {N : UInt8} {f : α → Except Err Bytes} {xs : List α}
    (h : ∃ c, encVec f xs = .ok c) (hl : lenOf (encVec f xs) < 2 ^ 32) :
    ∃ b, encSection N (encVec f) xs = .ok b :=
  encSection_ok_iff.2 (.inr ⟨h, hl⟩)

/-- A section that succeeded: its vector succeeded and fits (an empty one trivially). -/
theorem section_of_ok {α : Type} {N : UInt8} {f : α → Except Err Bytes} {xs : List α}
    (h : ∃ b, encSection N (encVec f) xs = .ok b) :
    (∃ c, encVec f xs = .ok c) ∧ lenOf (encVec f xs) < 2 ^ 32 := by
  rcases encSection_ok_iff.1 h with rfl | h
  · have he : encVec f ([] : List α) = .ok (encU 0 ++ []) := by
      have h0 : (0 : Nat) < 2 ^ 32 := by decide
      simp only [encVec, guardE, List.length_nil, h0, ↓reduceIte]
      rfl
    refine ⟨⟨_, he⟩, ?_⟩
    rw [he]
    simp [encU]
  · exact h

theorem mem_exprs {m : Lime1.Module} {e : Lime1.Expr} :
    e ∈ moduleExprs m ↔ (∃ f ∈ m.funcs, f.body = e) ∨ (∃ g ∈ m.globals, g.init = e) ∨
      (∃ el ∈ m.elems, el.offset = e) ∨ (∃ d ∈ m.data, d.offset = e) := by
  simp [moduleExprs]

/-- **When the encoder succeeds.** -/
theorem encModule_ok_iff {m : Lime1.Module} : (∃ b, encModule m = .ok b) ↔ Encodable m := by
  constructor
  · intro h
    simp only [encModule, ok_bind_iff] at h
    obtain ⟨u, hu, bty, hty, bim, him, bfn, hfn, btb, htb, bme, hme, bgl, hgl, bex, hex,
      bst, hst, bel, hel, bco, hco, bda, hda, _⟩ := h
    obtain ⟨⟨ty, hty'⟩, hty⟩ := section_of_ok ⟨bty, hty⟩
    obtain ⟨⟨im, him'⟩, him⟩ := section_of_ok ⟨bim, him⟩
    obtain ⟨_, hfn⟩ := section_of_ok ⟨bfn, hfn⟩
    obtain ⟨_, htb⟩ := section_of_ok ⟨btb, htb⟩
    obtain ⟨_, hme⟩ := section_of_ok ⟨bme, hme⟩
    obtain ⟨⟨gl, hgl'⟩, hgl⟩ := section_of_ok ⟨bgl, hgl⟩
    obtain ⟨⟨ex, hex'⟩, hex⟩ := section_of_ok ⟨bex, hex⟩
    obtain ⟨⟨el, hel'⟩, hel⟩ := section_of_ok ⟨bel, hel⟩
    obtain ⟨⟨co, hco'⟩, hco⟩ := section_of_ok ⟨bco, hco⟩
    obtain ⟨⟨da, hda'⟩, hda⟩ := section_of_ok ⟨bda, hda⟩
    obtain ⟨hlty, hty'⟩ := encVec_ok_iff.1 ⟨ty, hty'⟩
    obtain ⟨hlim, him'⟩ := encVec_ok_iff.1 ⟨im, him'⟩
    obtain ⟨hlgl, hgl'⟩ := encVec_ok_iff.1 ⟨gl, hgl'⟩
    obtain ⟨hlex, hex'⟩ := encVec_ok_iff.1 ⟨ex, hex'⟩
    obtain ⟨hlel, hel'⟩ := encVec_ok_iff.1 ⟨el, hel'⟩
    obtain ⟨_, hco'⟩ := encVec_ok_iff.1 ⟨co, hco'⟩
    obtain ⟨hlda, hda'⟩ := encVec_ok_iff.1 ⟨da, hda'⟩
    have hfun : ∀ f ∈ m.funcs, ∃ b, encCode (f.locals, f.body) = .ok b := fun f hf =>
      hco' _ (List.mem_map_of_mem (f := fun f : Lime1.Func => (f.locals, f.body)) hf)
    have htb' : m.tables.length < 2 ^ 32 := by
      have := encSection_ok_iff.1 ⟨btb, ‹_›⟩
      rcases this with h | ⟨⟨c, hc⟩, _⟩
      · simp [h]
      · exact (encVec_ok_iff.1 ⟨c, hc⟩).1
    have hme' : m.memories.length < 2 ^ 32 := by
      have := encSection_ok_iff.1 ⟨bme, ‹_›⟩
      rcases this with h | ⟨⟨c, hc⟩, _⟩
      · simp [h]
      · exact (encVec_ok_iff.1 ⟨c, hc⟩).1
    exact {
      instrs := fun e he => by
        rcases mem_exprs.1 he with ⟨f, hf, rfl⟩ | ⟨g, hg, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨d, hd, rfl⟩
        · exact (encCode_ok_iff.1 (hfun f hf)).2.1
        · exact encGlobal_ok_iff.1 (hgl' g hg)
        · exact (encElem_ok_iff.1 (hel' x hx)).1
        · exact (encData_ok_iff.1 (hda' d hd)).1
      types := hlty, imports := hlim, funcs := guardE_ok_iff.1 ⟨u, hu⟩, tables := htb'
      memories := hme', globals := hlgl, exports := hlex, elems := hlel, data := hlda
      funcTypes := fun t ht => encFuncType_ok_iff.1 (hty' t ht)
      importNames := fun im him => encImport_ok_iff.1 (him' im him)
      exportNames := fun ex hex => encExport_ok_iff.1 (hex' ex hex)
      locals := fun f hf => (encCode_ok_iff.1 (hfun f hf)).1
      elemInits := fun e he => (encElem_ok_iff.1 (hel' e he)).2
      dataBytes := fun d hd => (encData_ok_iff.1 (hda' d hd)).2
      codeSizes := fun f hf => (encCode_ok_iff.1 (hfun f hf)).2.2
      typeSec := hty, importSec := him, funcSec := hfn, tableSec := htb, memSec := hme
      globalSec := hgl, exportSec := hex, elemSec := hel, codeSec := hco, dataSec := hda }
  · intro hm
    have hcode : ∀ f ∈ m.funcs, ∃ b, encCode (f.locals, f.body) = .ok b := fun f hf =>
      encCode_ok_iff.2 ⟨hm.locals f hf,
        hm.instrs _ (mem_exprs.2 (.inl ⟨f, hf, rfl⟩)), hm.codeSizes f hf⟩
    obtain ⟨u, hu⟩ := guardE_ok_iff (msg := "more than 2^32 functions").2 hm.funcs
    obtain ⟨bty, hty⟩ := section_ok (N := 1)
      (encVec_ok_iff.2 ⟨hm.types, fun t ht => encFuncType_ok_iff.2 (hm.funcTypes t ht)⟩)
      hm.typeSec
    obtain ⟨bim, him⟩ := section_ok (N := 2)
      (encVec_ok_iff.2 ⟨hm.imports, fun i hi => encImport_ok_iff.2 (hm.importNames i hi)⟩)
      hm.importSec
    obtain ⟨bfn, hfn⟩ := section_ok (N := 3)
      (encVec_ok_iff.2 ⟨by simpa using hm.funcs, fun _ _ => ⟨_, rfl⟩⟩) hm.funcSec
    obtain ⟨btb, htb⟩ := section_ok (N := 4)
      (encVec_ok_iff.2 ⟨hm.tables, fun _ _ => ⟨_, rfl⟩⟩) hm.tableSec
    obtain ⟨bme, hme⟩ := section_ok (N := 5)
      (encVec_ok_iff.2 ⟨hm.memories, fun _ _ => ⟨_, rfl⟩⟩) hm.memSec
    obtain ⟨bgl, hgl⟩ := section_ok (N := 6)
      (encVec_ok_iff.2 ⟨hm.globals, fun g hg => encGlobal_ok_iff.2
        (hm.instrs _ (mem_exprs.2 (.inr (.inl ⟨g, hg, rfl⟩))))⟩) hm.globalSec
    obtain ⟨bex, hex⟩ := section_ok (N := 7)
      (encVec_ok_iff.2 ⟨hm.exports, fun e he => encExport_ok_iff.2 (hm.exportNames e he)⟩)
      hm.exportSec
    have hst : ∃ b, encSection 8 encStart m.start.toList = .ok b := by
      rcases hs : m.start with _ | x
      · exact ⟨[], rfl⟩
      · obtain ⟨c, hc, hl⟩ := encStart_ok (s := some x) rfl
        exact encSection_ok_iff.2 (.inr ⟨⟨c, hc⟩, by rw [hc]; exact hl⟩)
    obtain ⟨bst, hst⟩ := hst
    obtain ⟨bel, hel⟩ := section_ok (N := 9)
      (encVec_ok_iff.2 ⟨hm.elems, fun e he => encElem_ok_iff.2
        ⟨hm.instrs _ (mem_exprs.2 (.inr (.inr (.inl ⟨e, he, rfl⟩)))), hm.elemInits e he⟩⟩)
      hm.elemSec
    obtain ⟨bco, hco⟩ := section_ok (N := 10)
      (encVec_ok_iff.2 ⟨by simpa using hm.funcs, fun c hc => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hc
        exact hcode f hf⟩) hm.codeSec
    obtain ⟨bda, hda⟩ := section_ok (N := 11)
      (encVec_ok_iff.2 ⟨hm.data, fun d hd => encData_ok_iff.2
        ⟨hm.instrs _ (mem_exprs.2 (.inr (.inr (.inr ⟨d, hd, rfl⟩)))), hm.dataBytes d hd⟩⟩)
      hm.dataSec
    simp only [encModule, ok_bind_iff]
    exact ⟨u, hu, bty, hty, bim, him, bfn, hfn, btb, htb, bme, hme, bgl, hgl, bex, hex,
      bst, hst, bel, hel, bco, hco, bda, hda, ok_pure _⟩

/-- **The encoder succeeds on every encodable module.** -/
theorem encModule_isOk {m : Lime1.Module} (h : Encodable m) : ∃ b, encModule m = .ok b :=
  encModule_ok_iff.2 h

end Silmaril.Wasm.Lime1.Binary.Encoder
