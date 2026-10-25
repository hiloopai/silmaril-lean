module

public import Silmaril.Wasm.Execution.Core.Soundness.ConstEvalStep
public import Silmaril.Wasm.Execution.Core.Step

@[expose] public section

/-! # A computable constant-expression evaluator (Core 3.0)

`constInstr?` executes one constant instruction (spec 2.3 `Instr_const`, i.e.
`Instr.IsConstI`) on a value stack (top of stack at the end of the list),
transcribing the execution rules of `4.3-execution.instructions.spectec`
(`Step_read/ref.null`, `Step_read/ref.func`, `Step_pure/ref.i31`,
`Step/struct.new`, `Step_read/struct.new_default`, `Step_pure/array.new`,
`Step_read/array.new_default`, `Step/array.new_fixed`,
`Step_pure/any.convert_extern-*`, `Step_pure/extern.convert_any-*`,
`Step_read/global.get`, `Step_pure/binop-val` for `iNN.add/sub/mul`).
`constExpr?` folds it over an expression from the empty stack and `evalConst?`
requires exactly one result value.

Soundness: every successful run is a `Steps` reduction (`constInstr?_sound`,
`constExpr?_sound`, `evalConst?_sound`), for every profile and host.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Helpers -/

/-- Split off the top `n` values of a stack. -/
def popN? (vs : List Val) (n : Nat) : Option (List Val × List Val) :=
  if n ≤ vs.length then some (vs.take (vs.length - n), vs.drop (vs.length - n)) else none

theorem popN?_eq {vs pre args : List Val} {n : Nat} (h : popN? vs n = some (pre, args)) :
    vs = pre ++ args ∧ args.length = n := by
  unfold popN? at h
  split at h
  · cases h; exact ⟨(List.take_append_drop _ _).symm, by simp; omega⟩
  · cases h

/-- An integer value of type `t`. -/
def Val.int? (t : IntType) : Val → Option (BitVec t.width)
  | .num ⟨.int t', x⟩ => if h : t' = t then some (h ▸ x) else none
  | _ => none

theorem Val.int?_eq {t : IntType} {v : Val} {x : BitVec t.width} (h : v.int? t = some x) :
    v = .num ⟨.int t, x⟩ := by
  rcases v with ⟨⟨t' | t'⟩, b⟩ | _ | _ <;> simp [Val.int?] at h
  all_goals (obtain ⟨rfl, rfl⟩ := h; rfl)

/-- The binary integer operators allowed in constant expressions. -/
def constBinOp : IntBinOp → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- The structure fields a defined type expands to. -/
def expandStruct? (d : DefType) : Option (Ty (.list .field)) :=
  match d.expand? with
  | some (.struct fs) => some fs
  | _ => none

theorem expandStruct?_sound {d : DefType} {fs : Ty (.list .field)}
    (h : expandStruct? d = some fs) : Expand d (.struct fs) := by
  unfold expandStruct? at h
  split at h
  · cases h; exact Expand.iff.2 (by assumption)
  · cases h

/-- The array field type a defined type expands to. -/
def expandArray? (d : DefType) : Option CFieldType :=
  match d.expand? with
  | some (.array ft) => some ft
  | _ => none

theorem expandArray?_sound {d : DefType} {ft : CFieldType}
    (h : expandArray? d = some ft) : Expand d (.array ft) := by
  unfold expandArray? at h
  split at h
  · cases h; exact Expand.iff.2 (by assumption)
  · cases h

/-- `struct.new x` on a stack. -/
def structNew? (s : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) :
    Option (Store H × List Val) := do
  let d ← f.type? x
  let fs ← expandStruct? d
  let (pre, args) ← popN? vs fs.length
  if (fs.toList.zip args).all (fun p => packable (fieldStorage p.1) p.2) then
    some (s.addStruct ⟨d, (fs.toList.zip args).map fun (ft, v) => packField (fieldStorage ft) v⟩,
      pre ++ [.ref (.struct s.structs.length)])
  else none

/-- `array.new_fixed x n` on a stack. -/
def arrayNewFixed? (s : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) (n : Fin (2 ^ 32)) :
    Option (Store H × List Val) := do
  let d ← f.type? x
  let ft ← expandArray? d
  let (pre, args) ← popN? vs n.val
  if args.all (packable (fieldStorage ft)) then
    some (s.addArray ⟨d, args.map (packField (fieldStorage ft))⟩,
      pre ++ [.ref (.array s.arrays.length)])
  else none

/-- Pop one value. -/
def pop1? (vs : List Val) : Option (List Val × Val) := do
  let (pre, args) ← popN? vs 1
  match args with
  | [v] => some (pre, v)
  | _ => none

theorem pop1?_eq {vs pre : List Val} {v : Val} (h : pop1? vs = some (pre, v)) :
    vs = pre ++ [v] := by
  unfold pop1? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨pre', args, hp, h⟩ := h
  obtain ⟨rfl, -⟩ := popN?_eq hp
  split at h <;> simp_all

/-- Pop two values (`v₁` below `v₂`). -/
def pop2? (vs : List Val) : Option (List Val × Val × Val) := do
  let (pre, args) ← popN? vs 2
  match args with
  | [v₁, v₂] => some (pre, v₁, v₂)
  | _ => none

theorem pop2?_eq {vs pre : List Val} {v₁ v₂ : Val} (h : pop2? vs = some (pre, v₁, v₂)) :
    vs = pre ++ [v₁, v₂] := by
  unfold pop2? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨pre', args, hp, h⟩ := h
  obtain ⟨rfl, -⟩ := popN?_eq hp
  split at h <;> simp_all

/-! ## The evaluator -/

/-- Execute one constant instruction on a value stack. -/
def constInstr? (s : Store H) (f : Frame) (vs : List Val) : Instr → Option (Store H × List Val)
  | .intConst t x => some (s, vs ++ [.num ⟨.int t, x⟩])
  | .floatConst t x => some (s, vs ++ [.num ⟨.float t, x⟩])
  | .vecConst b => some (s, vs ++ [.vec b])
  | .refNull _ => some (s, vs ++ [.ref .null])
  | .refFunc x => do
      let a ← f.module.funcs[x.toNat]?
      some (s, vs ++ [.ref (.func a)])
  | .refI31 => do
      let (pre, v) ← pop1? vs
      let i ← v.int? .i32
      some (s, pre ++ [.ref (.i31 (i.setWidth 31))])
  | .globalGet x => do
      let (_, g) ← s.global? f x
      some (s, vs ++ [g.value])
  | .intBinOp t op =>
      if constBinOp op then do
        let (pre, v₁, v₂) ← pop2? vs
        let x ← v₁.int? t
        let y ← v₂.int? t
        match intBinOp t op x y with
        | .ok z => some (s, pre ++ [.num ⟨.int t, z⟩])
        | .error _ => none
      else none
  | .anyConvertExtern => do
      let (pre, v) ← pop1? vs
      match v with
      | .ref .null => some (s, pre ++ [.ref .null])
      | .ref (.extern r) => some (s, pre ++ [.ref r])
      | _ => none
  | .externConvertAny => do
      let (pre, v) ← pop1? vs
      match v with
      | .ref r => (if r = .null then some (s, pre ++ [.ref .null])
          else some (s, pre ++ [.ref (.extern r)]))
      | _ => none
  | .structNew x => structNew? s f vs x
  | .structNewDefault x => do
      let d ← f.type? x
      let fs ← expandStruct? d
      let dvs ← fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack)
      structNew? s f (vs ++ dvs) x
  | .arrayNew x => do
      let (pre, v, n) ← pop2? vs
      let n ← n.int? .i32
      arrayNewFixed? s f (pre ++ List.replicate n.toNat v) x ⟨n.toNat, n.isLt⟩
  | .arrayNewDefault x => do
      let (pre, n) ← pop1? vs
      let n ← n.int? .i32
      let d ← f.type? x
      let ft ← expandArray? d
      let v ← defaultVal? (fieldStorage ft).unpack
      arrayNewFixed? s f (pre ++ List.replicate n.toNat v) x ⟨n.toNat, n.isLt⟩
  | .arrayNewFixed x n => arrayNewFixed? s f vs x n
  | _ => none

/-- Evaluate an expression of constant instructions from the empty stack. -/
def constExpr? (s : Store H) (f : Frame) (e : Expr) : Option (Store H × List Val) :=
  e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (s, [])

/-- Evaluate a constant expression to exactly one value. -/
def evalConst? (s : Store H) (f : Frame) (e : Expr) : Option (Store H × Val) :=
  match constExpr? s f e with
  | some (s', [v]) => some (s', v)
  | _ => none

/-! ## Soundness -/

section Soundness

variable {P : Profile} {host : HostSemantics H}

/-- Lift a reduction of the top of the stack under a value prefix. -/
theorem Steps.under {s s' : Store H} {f : Frame} {pre : List Val} {is is' : List Admin}
    (h : Steps P host ⟨s, f, is⟩ ⟨s', f, is'⟩) :
    Steps P host ⟨s, f, vals pre ++ is⟩ ⟨s', f, vals pre ++ is'⟩ := by
  simpa using Steps.ctxtInstrs (vs := pre) (rest := []) h

@[simp] theorem vals_cons' (v : Val) (vs : List Val) : vals (v :: vs) = v.toAdmin :: vals vs :=
  rfl

theorem vals_snoc (vs : List Val) (v : Val) : vals (vs ++ [v]) = vals vs ++ [v.toAdmin] := by
  simp [vals]

theorem structNew?_sound {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    (h : structNew? s f vs x = some (s', vs')) :
    Steps P host ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩ ⟨s', f, vals vs'⟩ := by
  unfold structNew? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨d, hd, fs, hfs, pre, args, hp, h⟩ := h
  split at h
  case isFalse => cases h
  rename_i hall
  cases h
  obtain ⟨rfl, hn⟩ := popN?_eq hp
  have := Step.steps (P := P) (host := host) (Step.aggregate (AggregateStep.structNew (s := s)
    (f := f) hd (expandStruct?_sound hfs) hn (List.all_eq_true.mp hall)))
  simpa [vals_snoc, List.append_assoc, Val.toAdmin] using Steps.under (pre := pre) this

theorem arrayNewFixed?_sound {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    {n : Fin (2 ^ 32)} (h : arrayNewFixed? s f vs x n = some (s', vs')) :
    Steps P host ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩ ⟨s', f, vals vs'⟩ := by
  unfold arrayNewFixed? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨d, hd, ft, hft, pre, args, hp, h⟩ := h
  split at h
  case isFalse => cases h
  rename_i hall
  cases h
  obtain ⟨rfl, hn⟩ := popN?_eq hp
  have := Step.steps (P := P) (host := host) (Step.aggregate (AggregateStep.arrayNewFixed (s := s)
    (f := f) hd (expandArray?_sound hft) hn (List.all_eq_true.mp hall)))
  simpa [vals_snoc, List.append_assoc, arrRef, Val.toAdmin] using Steps.under (pre := pre) this

theorem constInstr?_sound {s s' : Store H} {f : Frame} {vs vs' : List Val} {i : Instr}
    (h : constInstr? s f vs i = some (s', vs')) :
    Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s', f, vals vs'⟩ := by
  cases i <;> simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    reduceCtorEq, Prod.exists] at h
  case intConst t x =>
    cases h; simp [Val.toAdmin]; exact .refl
  case floatConst t x =>
    cases h; simp [Val.toAdmin]; exact .refl
  case vecConst b =>
    cases h; simp [Val.toAdmin]; exact .refl
  case refNull ht =>
    cases h
    simpa [vals_snoc, Val.toAdmin] using
      Steps.under (P := P) (host := host) (pre := vs) (Step.reference (RefStep.refNull (s := s)
        (f := f) ht)).steps
  case refFunc x =>
    obtain ⟨a, ha, h⟩ := h
    cases h
    simpa [vals_snoc, Val.toAdmin] using
      Steps.under (P := P) (host := host) (pre := vs) (Step.reference (RefStep.refFunc (s := s)
        (f := f) ha)).steps
  case refI31 =>
    obtain ⟨pre, v, hp, b, hb, h⟩ := h
    cases h
    rw [pop1?_eq hp, Val.int?_eq hb]
    have := (Step.reference (P := P) (host := host) (RefStep.refI31 (s := s) (f := f) b)).steps
    have h2 := Steps.under (pre := pre) this
    simp only [vals_append, vals_cons', vals_nil', Val.toAdmin, constI32, Val.i32,
      List.append_assoc, List.cons_append, List.nil_append] at h2 ⊢
    exact h2
  case globalGet x =>
    obtain ⟨a, g, hg, h⟩ := h
    cases h
    simpa [vals_snoc] using
      Steps.under (P := P) (host := host) (pre := vs) (Step.variable (VariableStep.globalGet
        (s := s) (f := f) hg)).steps
  case intBinOp t op =>
    split at h
    · simp only [Option.bind_eq_some_iff, Prod.exists] at h
      obtain ⟨pre, v₁, v₂, hp, x, hx, y, hy, h⟩ := h
      rw [pop2?_eq hp, Val.int?_eq hx, Val.int?_eq hy]
      split at h
      · rename_i z hz
        cases h
        have := (Step.numeric (P := P) (host := host) (s := s) (f := f)
          (NumericStep.intBinOp (P := P) hz)).steps
        simpa [vals_snoc, Val.toAdmin, List.append_assoc] using Steps.under (pre := pre) this
      · cases h
    · cases h
  case anyConvertExtern =>
    obtain ⟨pre, v, hp, h⟩ := h
    rw [pop1?_eq hp]
    rcases v with _ | _ | r
    case num => simp at h
    case vec => simp at h
    cases r <;> simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · have := (Step.reference (P := P) (host := host)
        (RefStep.anyConvertNull (s := s) (f := f))).steps
      simpa [vals_snoc, Val.toAdmin, List.append_assoc] using Steps.under (pre := pre) this
    · rename_i r
      have := (Step.reference (P := P) (host := host)
        (RefStep.anyConvertAddr (s := s) (f := f) r)).steps
      simpa [vals_snoc, Val.toAdmin, List.append_assoc] using Steps.under (pre := pre) this
  case externConvertAny =>
    obtain ⟨pre, v, hp, h⟩ := h
    rw [pop1?_eq hp]
    rcases v with _ | _ | r
    case num => simp at h
    case vec => simp at h
    dsimp only at h
    split_ifs at h with hr <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · subst hr
      have := (Step.reference (P := P) (host := host)
        (RefStep.externConvertNull (s := s) (f := f))).steps
      simpa [vals_snoc, Val.toAdmin, List.append_assoc] using Steps.under (pre := pre) this
    · have := (Step.reference (P := P) (host := host)
        (RefStep.externConvertAddr (s := s) (f := f) hr)).steps
      simpa [vals_snoc, Val.toAdmin, List.append_assoc] using Steps.under (pre := pre) this
  case structNew x => exact structNew?_sound h
  case structNewDefault x =>
    obtain ⟨d, hd, fs, hfs, dvs, hdvs, h⟩ := h
    have h1 := (Step.aggregate (P := P) (host := host) (AggregateStep.structNewDefault (s := s)
      (f := f) hd (expandStruct?_sound hfs) hdvs)).steps
    refine (Steps.under (pre := vs) h1).trans ?_
    simpa [List.append_assoc] using structNew?_sound (P := P) (host := host) h
  case arrayNew x =>
    obtain ⟨pre, v, nv, hp, n, hn, h⟩ := h
    rw [pop2?_eq hp, Val.int?_eq hn]
    have h1 := (Step.aggregate (P := P) (host := host) (AggregateStep.arrayNew (s := s)
      (f := f) (x := x) v n)).steps
    have h2 := arrayNewFixed?_sound (P := P) (host := host) h
    have h3 := Steps.under (pre := pre) h1
    simp only [vals_append, vals_cons', vals_nil', constI32, Val.i32,
      List.append_assoc, List.cons_append, List.nil_append] at h3 ⊢
    rw [vals_append, List.append_assoc] at h2
    exact h3.trans h2
  case arrayNewDefault x =>
    obtain ⟨pre, nv, hp, n, hn, d, hd, ft, hft, v, hv, h⟩ := h
    rw [pop1?_eq hp, Val.int?_eq hn]
    have h1 := (Step.aggregate (P := P) (host := host) (AggregateStep.arrayNewDefault (s := s)
      (f := f) (n := n) hd (expandArray?_sound hft) hv)).steps
    have h2 := arrayNewFixed?_sound (P := P) (host := host) h
    have h3 := Steps.under (pre := pre) h1
    simp only [vals_append, vals_cons', vals_nil', constI32, Val.i32,
      List.append_assoc, List.cons_append, List.nil_append] at h3 ⊢
    rw [vals_append, List.append_assoc] at h2
    exact h3.trans h2
  case arrayNewFixed x n => exact arrayNewFixed?_sound h

theorem constFold_sound {f : Frame} :
    ∀ (e : Expr) {s s' : Store H} {vs vs' : List Val},
      e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (s, vs) =
        some (s', vs') →
      Steps P host ⟨s, f, vals vs ++ expression e⟩ ⟨s', f, vals vs'⟩
  | [], s, s', vs, vs', h => by
    simp only [List.foldlM_nil] at h
    cases h
    simpa [expression] using Relation.ReflTransGen.refl
  | i :: e, s, s', vs, vs', h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s₁, vs₁⟩, h₁, h₂⟩ := h
    have a := Steps.ctxtInstrs (rest := expression e) (vs := [])
      (constInstr?_sound (P := P) (host := host) h₁)
    have b := constFold_sound e h₂
    simp only [vals_nil', List.nil_append] at a
    simpa [expression, List.append_assoc] using a.trans b

theorem constExpr?_sound {s s' : Store H} {f : Frame} {e : Expr} {vs : List Val}
    (h : constExpr? s f e = some (s', vs)) :
    Steps P host ⟨s, f, expression e⟩ ⟨s', f, vals vs⟩ := by
  simpa using constFold_sound (P := P) (host := host) e (vs := []) h

theorem evalConst?_sound {s s' : Store H} {f : Frame} {e : Expr} {v : Val}
    (h : evalConst? s f e = some (s', v)) : EvalExpr P host s f e s' f [v] := by
  unfold evalConst? at h
  split at h
  · rename_i s₁ v₁ hc
    cases h
    exact constExpr?_sound hc
  · cases h

end Soundness

/-! ## Examples -/

section Examples

/-- A store with nothing in it. -/
def emptyStore : Store Empty := {}

/-- A frame with an empty module. -/
def emptyFrame : Frame := {}

example : evalConst? emptyStore emptyFrame [.intConst .i32 42] =
    some (emptyStore, .num ⟨.int .i32, 42⟩) := rfl

example : evalConst? emptyStore emptyFrame
    [.intConst .i32 40, .intConst .i32 2, .intBinOp .i32 .add] =
    some (emptyStore, .num ⟨.int .i32, 42⟩) := rfl

example : evalConst? emptyStore emptyFrame [.refNull (.abstract .func)] =
    some (emptyStore, .ref .null) := rfl

end Examples

end Silmaril.Wasm.Execution.Core
