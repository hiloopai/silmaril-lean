module

public import Silmaril.Wasm.SingleThreaded.Determinism
public import Silmaril.Wasm.Execution.Core.GrowImpl

@[expose] public section

/-! # Computable interpreter: variable and table families

`variableStep?` and `tableStep?` compute the head step of the `VariableStep` and
`TableStep` families of the single-threaded deterministic profile. Each returns
the number `k` of values consumed from the top of the value prefix together
with the resulting configuration; soundness and completeness are stated against
`Det.Head (profile o)`.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace VarTab

/-! ## Value-prefix helpers -/

/-- The top `n` values of the prefix (bottom-first). -/
def top (n : Nat) (vs : List Val) : List Val := vs.drop (vs.length - n)

theorem top_len {n : Nat} {vs l : List Val} (h : top n vs = l) (hl : l.length = n) :
    n ≤ vs.length := by
  have := congrArg List.length h
  simp only [top, List.length_drop] at this
  omega

theorem top_append_of (q args : List Val) (n : Nat) (h : args.length = n) :
    top n (q ++ args) = args := by
  subst h
  simp [top]

@[simp] theorem top_zero (vs : List Val) : top 0 vs = [] := by simp [top]

def top1? (vs : List Val) : Option Val :=
  match top 1 vs with
  | [v] => some v
  | _ => none

def top2? (vs : List Val) : Option (Val × Val) :=
  match top 2 vs with
  | [v, w] => some (v, w)
  | _ => none

def top3? (vs : List Val) : Option (Val × Val × Val) :=
  match top 3 vs with
  | [u, v, w] => some (u, v, w)
  | _ => none

theorem top1?_sound {vs : List Val} {v : Val} (h : top1? vs = some v) :
    1 ≤ vs.length ∧ top 1 vs = [v] := by
  unfold top1? at h
  split at h
  · next w hw => cases h; exact ⟨top_len hw rfl, hw⟩
  · cases h

theorem top2?_sound {vs : List Val} {p : Val × Val} (h : top2? vs = some p) :
    2 ≤ vs.length ∧ top 2 vs = [p.1, p.2] := by
  unfold top2? at h
  split at h
  · next v w hw => cases h; exact ⟨top_len hw rfl, hw⟩
  · cases h

theorem top3?_sound {vs : List Val} {p : Val × Val × Val} (h : top3? vs = some p) :
    3 ≤ vs.length ∧ top 3 vs = [p.1, p.2.1, p.2.2] := by
  unfold top3? at h
  split at h
  · next u v w hw => cases h; exact ⟨top_len hw rfl, hw⟩
  · cases h

@[simp] theorem top1?_append (q : List Val) (v : Val) : top1? (q ++ [v]) = some v := by
  unfold top1?; rw [top_append_of q [v] 1 rfl]

@[simp] theorem top2?_append (q : List Val) (v w : Val) : top2? (q ++ [v, w]) = some (v, w) := by
  unfold top2?; rw [top_append_of q [v, w] 2 rfl]

@[simp] theorem top3?_append (q : List Val) (u v w : Val) :
    top3? (q ++ [u, v, w]) = some (u, v, w) := by
  unfold top3?; rw [top_append_of q [u, v, w] 3 rfl]

/-! ## Operand recognisers -/

/-- `CONST at i` for some address type. -/
def asAddr? : Val → Option ((a : AddrType) × BitVec a.intType.width)
  | .num ⟨.int .i32, i⟩ => some ⟨.i32, i⟩
  | .num ⟨.int .i64, i⟩ => some ⟨.i64, i⟩
  | _ => none

theorem asAddr?_sound {v : Val} {p : (a : AddrType) × BitVec a.intType.width}
    (h : asAddr? v = some p) : v.toAdmin = aconst p.1 p.2 := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r
  all_goals cases h <;> rfl

@[simp] theorem asAddr?_aconst (a : AddrType) (i : BitVec a.intType.width) :
    asAddr? (.num ⟨.int a.intType, i⟩) = some ⟨a, i⟩ := by
  cases a <;> rfl

/-- `CONST at i` for the given address type. -/
def asAddrOf? : (a : AddrType) → Val → Option (BitVec a.intType.width)
  | .i32, .num ⟨.int .i32, i⟩ => some i
  | .i64, .num ⟨.int .i64, i⟩ => some i
  | _, _ => none

theorem asAddrOf?_sound {a : AddrType} {v : Val} {n : BitVec a.intType.width}
    (h : asAddrOf? a v = some n) : v.toAdmin = aconst a n := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r
  all_goals (try cases a) <;> cases h <;> rfl

@[simp] theorem asAddrOf?_aconst (a : AddrType) (i : BitVec a.intType.width) :
    asAddrOf? a (.num ⟨.int a.intType, i⟩) = some i := by
  cases a <;> rfl

def asI32? : Val → Option (BitVec 32)
  | .num ⟨.int .i32, i⟩ => some i
  | _ => none

theorem asI32?_sound {v : Val} {j : BitVec 32} (h : asI32? v = some j) :
    v.toAdmin = constI32 j := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r
  all_goals cases h <;> rfl

@[simp] theorem asI32?_i32 (j : BitVec 32) : asI32? (Val.i32 j) = some j := rfl

def asRef? : Val → Option Ref
  | .ref r => some r
  | _ => none

theorem asRef?_sound {v : Val} {r : Ref} (h : asRef? v = some r) : v.toAdmin = .ref r := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [asRef?] at h
  subst h; rfl

@[simp] theorem asRef?_ref (r : Ref) : asRef? (.ref r) = some r := rfl

/-! ## Table handlers -/

def tableGet? (s : Store H) (f : Frame) (x : TableIdx) (vs : List Val) :
    Option (Nat × Config H) := do
  let v ← top1? vs
  let p ← asAddr? v
  let t ← s.table? f x
  match t.2.refs[p.2.toNat]? with
  | some r => some (1, ⟨s, f, [.ref r]⟩)
  | none => some (1, ⟨s, f, [.trap]⟩)

def tableSet? (s : Store H) (f : Frame) (x : TableIdx) (vs : List Val) :
    Option (Nat × Config H) := do
  let q ← top2? vs
  let p ← asAddr? q.1
  let r ← asRef? q.2
  let t ← s.table? f x
  if p.2.toNat < t.2.refs.length then
    some (2, ⟨s.setTable t.1 { t.2 with refs := t.2.refs.set p.2.toNat r }, f, []⟩)
  else some (2, ⟨s, f, [.trap]⟩)

def tableSize? (s : Store H) (f : Frame) (x : TableIdx) : Option (Nat × Config H) := do
  let t ← s.table? f x
  some (0, ⟨s, f, [aconst t.2.type.address (BitVec.ofNat _ t.2.refs.length)]⟩)

def tableGrow? (o : GrowOracle) (s : Store H) (f : Frame) (x : TableIdx) (vs : List Val) :
    Option (Nat × Config H) := do
  let q ← top2? vs
  let r ← asRef? q.1
  let p ← asAddr? q.2
  let t ← s.table? f x
  if (profile o).growMaySucceed .table t.1 t.2.refs.length p.2.toNat then
    match t.2.grow? p.2.toNat r with
    | some ti' => some (2, ⟨s.setTable t.1 ti', f, [aconst p.1 (BitVec.ofNat _ t.2.refs.length)]⟩)
    | none => some (2, ⟨s, f, [aconst p.1 (BitVec.allOnes _)]⟩)
  else some (2, ⟨s, f, [aconst p.1 (BitVec.allOnes _)]⟩)

def tableFill? (s : Store H) (f : Frame) (x : TableIdx) (vs : List Val) :
    Option (Nat × Config H) := do
  let q ← top3? vs
  let p ← asAddr? q.1
  let n ← asAddrOf? p.1 q.2.2
  let t ← s.table? f x
  if t.2.refs.length < p.2.toNat + n.toNat then some (3, ⟨s, f, [.trap]⟩)
  else if n = 0 then some (3, ⟨s, f, []⟩)
  else some (3, ⟨s, f, [aconst p.1 p.2, q.2.1.toAdmin, .plain (.tableSet x),
    aconst p.1 (p.2 + 1), q.2.1.toAdmin, aconst p.1 (n - 1), .plain (.tableFill x)]⟩)

def tableCopy? (s : Store H) (f : Frame) (x₁ x₂ : TableIdx) (vs : List Val) :
    Option (Nat × Config H) := do
  let q ← top3? vs
  let p₁ ← asAddr? q.1
  let p₂ ← asAddr? q.2.1
  let p' ← asAddr? q.2.2
  let t₁ ← s.table? f x₁
  let t₂ ← s.table? f x₂
  if t₁.2.refs.length < p₁.2.toNat + p'.2.toNat ∨ t₂.2.refs.length < p₂.2.toNat + p'.2.toNat then
    some (3, ⟨s, f, [.trap]⟩)
  else if p'.2 = 0 then some (3, ⟨s, f, []⟩)
  else if p₁.2.toNat ≤ p₂.2.toNat then
    some (3, ⟨s, f, [aconst p₁.1 p₁.2, aconst p₂.1 p₂.2, .plain (.tableGet x₂),
      .plain (.tableSet x₁), aconst p₁.1 (p₁.2 + 1), aconst p₂.1 (p₂.2 + 1),
      aconst p'.1 (p'.2 - 1), .plain (.tableCopy x₁ x₂)]⟩)
  else
    some (3, ⟨s, f, [aconst p₁.1 (p₁.2 + BitVec.ofNat _ p'.2.toNat - 1),
      aconst p₂.1 (p₂.2 + BitVec.ofNat _ p'.2.toNat - 1),
      .plain (.tableGet x₂), .plain (.tableSet x₁),
      aconst p₁.1 p₁.2, aconst p₂.1 p₂.2, aconst p'.1 (p'.2 - 1), .plain (.tableCopy x₁ x₂)]⟩)

def tableInit? (s : Store H) (f : Frame) (x : TableIdx) (y : ElemIdx) (vs : List Val) :
    Option (Nat × Config H) := do
  let q ← top3? vs
  let p ← asAddr? q.1
  let j ← asI32? q.2.1
  let n ← asI32? q.2.2
  let t ← s.table? f x
  let el ← s.elem? f y
  if t.2.refs.length < p.2.toNat + n.toNat ∨ el.2.refs.length < j.toNat + n.toNat then
    some (3, ⟨s, f, [.trap]⟩)
  else if n = 0 then some (3, ⟨s, f, []⟩)
  else match el.2.refs[j.toNat]? with
    | some r => some (3, ⟨s, f, [aconst p.1 p.2, .ref r, .plain (.tableSet x),
        aconst p.1 (p.2 + 1), constI32 (j + 1), constI32 (n - 1), .plain (.tableInit x y)]⟩)
    | none => none

def elemDrop? (s : Store H) (f : Frame) (y : ElemIdx) : Option (Nat × Config H) := do
  let el ← s.elem? f y
  some (0, ⟨s.setElem el.1 [], f, []⟩)

/-! ## Handler soundness -/

set_option hygiene false in
/-- Close an `h : some (n, c₀) = some (k, c)` leaf into `k = n`, `c = c₀`. -/
macro "vt_leaf" : tactic =>
  `(tactic| (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h))

set_option hygiene false in
/-- Split off the length bound and expose the operand list. -/
macro "vt_pre" : tactic =>
  `(tactic| (refine ⟨hl, ?_⟩; rw [hv]; simp only [vals_cons, vals_nil, List.cons_append,
    List.nil_append]))

set_option hygiene false in
macro "vt_pre0" : tactic =>
  `(tactic| (refine ⟨Nat.zero_le _, ?_⟩; simp only [top_zero, vals_nil, List.nil_append]))

section
variable {P : Profile} {s : Store H} {f : Frame} {vs : List Val} {k : Nat} {c : Config H}

theorem tableGet?_sound {x : TableIdx} (h : tableGet? s f x vs = some (k, c)) :
    k ≤ vs.length ∧ TableStep P ⟨s, f, vals (top k vs) ++ [.plain (.tableGet x)]⟩ c := by
  simp only [tableGet?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, ⟨a, i⟩, hp, ⟨ta, ti⟩, ht, h⟩ := h
  obtain ⟨hl, hv⟩ := top1?_sound hv
  have ha := asAddr?_sound hp
  dsimp only at h ha
  split at h
  · rename_i r hr; vt_leaf; vt_pre; rw [ha]; exact .getVal ht hr
  · rename_i hr; vt_leaf; vt_pre; rw [ha]; exact .getOob ht (List.getElem?_eq_none_iff.mp hr)

theorem tableSet?_sound {x : TableIdx} (h : tableSet? s f x vs = some (k, c)) :
    k ≤ vs.length ∧ TableStep P ⟨s, f, vals (top k vs) ++ [.plain (.tableSet x)]⟩ c := by
  simp only [tableSet?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨v, w⟩, hq, ⟨a, i⟩, hp, r, hr, ⟨ta, ti⟩, ht, h⟩ := h
  obtain ⟨hl, hv⟩ := top2?_sound hq
  have ha := asAddr?_sound hp
  have hr' := asRef?_sound hr
  dsimp only at h ha hr' hv
  split at h
  · rename_i hi; vt_leaf; vt_pre; rw [ha, hr']; exact .setVal ht hi
  · rename_i hi; vt_leaf; vt_pre; rw [ha, hr']; exact .setOob ht (Nat.le_of_not_lt hi)

theorem tableSize?_sound {x : TableIdx} (h : tableSize? s f x = some (k, c)) :
    k ≤ vs.length ∧ TableStep P ⟨s, f, vals (top k vs) ++ [.plain (.tableSize x)]⟩ c := by
  simp only [tableSize?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ta, ti⟩, ht, h⟩ := h
  vt_leaf; vt_pre0; exact .size ht

theorem tableGrow?_sound {o : GrowOracle} {x : TableIdx} (h : tableGrow? o s f x vs = some (k, c)) :
    k ≤ vs.length ∧ TableStep (profile o) ⟨s, f, vals (top k vs) ++ [.plain (.tableGrow x)]⟩ c := by
  simp only [tableGrow?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨v, w⟩, hq, r, hr, ⟨a, n⟩, hp, ⟨ta, ti⟩, ht, h⟩ := h
  obtain ⟨hl, hv⟩ := top2?_sound hq
  have ha := asAddr?_sound hp
  have hr' := asRef?_sound hr
  dsimp only at h ha hr' hv
  split at h
  · rename_i hs
    split at h
    · rename_i ti' hg; vt_leaf; vt_pre; rw [ha, hr']; exact .growSucceed ht hg hs
    · rename_i hg; vt_leaf; vt_pre; rw [ha, hr']; exact .growFail ht (Or.inr hg)
  · rename_i hs
    vt_leaf; vt_pre; rw [ha, hr']
    refine .growFail ht (Or.inl ?_)
    simpa [Profile.growMaySucceed, Profile.growMayFail, profile, Profile.deterministic] using hs

theorem tableFill?_sound {x : TableIdx} (h : tableFill? s f x vs = some (k, c)) :
    k ≤ vs.length ∧ TableStep P ⟨s, f, vals (top k vs) ++ [.plain (.tableFill x)]⟩ c := by
  simp only [tableFill?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, v, w⟩, hq, ⟨a, i⟩, hp, n, hn, ⟨ta, ti⟩, ht, h⟩ := h
  obtain ⟨hl, hv⟩ := top3?_sound hq
  have ha := asAddr?_sound hp
  have hn' := asAddrOf?_sound hn
  dsimp only at h ha hn' hv n
  split at h
  · rename_i h1; vt_leaf; vt_pre; rw [ha, hn']; exact .fillOob ht h1
  · rename_i h1
    split at h
    · rename_i h2; subst h2; vt_leaf; vt_pre; rw [ha, hn']
      exact .fillZero ht (by simp at h1; omega)
    · rename_i h2; vt_leaf; vt_pre; rw [ha, hn']
      exact .fillSucc ht (Nat.le_of_not_lt h1) h2

theorem tableCopy?_sound {x₁ x₂ : TableIdx} (h : tableCopy? s f x₁ x₂ vs = some (k, c)) :
    k ≤ vs.length ∧ TableStep P ⟨s, f, vals (top k vs) ++ [.plain (.tableCopy x₁ x₂)]⟩ c := by
  simp only [tableCopy?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, v, w⟩, hq, ⟨a₁, i₁⟩, hp₁, ⟨a₂, i₂⟩, hp₂, ⟨a', n⟩, hp', ⟨ta₁, ti₁⟩, ht₁,
    ⟨ta₂, ti₂⟩, ht₂, h⟩ := h
  obtain ⟨hl, hv⟩ := top3?_sound hq
  have ha₁ := asAddr?_sound hp₁
  have ha₂ := asAddr?_sound hp₂
  have ha' := asAddr?_sound hp'
  dsimp only at h ha₁ ha₂ ha' hv
  split at h
  · rename_i h1; vt_leaf; vt_pre; rw [ha₁, ha₂, ha']; exact .copyOob ht₁ ht₂ h1
  · rename_i h1
    split at h
    · rename_i h2; replace h2 : n = 0 := h2; subst h2; vt_leaf; vt_pre; rw [ha₁, ha₂, ha']
      exact .copyZero ht₁ ht₂ (by simp at h1; omega)
    · rename_i h2
      split at h
      · rename_i h3; vt_leaf; vt_pre; rw [ha₁, ha₂, ha']
        exact .copyLe ht₁ ht₂ (by omega) h2 h3
      · rename_i h3; vt_leaf; vt_pre; rw [ha₁, ha₂, ha']
        exact .copyGt ht₁ ht₂ (by omega) h2 (by omega)

theorem tableInit?_sound {x : TableIdx} {y : ElemIdx} (h : tableInit? s f x y vs = some (k, c)) :
    k ≤ vs.length ∧ TableStep P ⟨s, f, vals (top k vs) ++ [.plain (.tableInit x y)]⟩ c := by
  simp only [tableInit?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, v, w⟩, hq, ⟨a, i⟩, hp, j, hj, n, hn, ⟨ta, ti⟩, ht, ⟨ea, ei⟩, he, h⟩ := h
  obtain ⟨hl, hv⟩ := top3?_sound hq
  have ha := asAddr?_sound hp
  have hj' := asI32?_sound hj
  have hn' := asI32?_sound hn
  dsimp only at h ha hv
  split at h
  · rename_i h1; vt_leaf; vt_pre; rw [ha, hj', hn']; exact .initOob ht he h1
  · rename_i h1
    split at h
    · rename_i h2; subst h2; vt_leaf; vt_pre; rw [ha, hj', hn']
      exact .initZero ht he (by simp at h1; omega)
    · rename_i h2
      split at h
      · rename_i r hr; vt_leaf; vt_pre; rw [ha, hj', hn']
        exact .initSucc ht he (by omega) h2 hr
      · cases h

theorem elemDrop?_sound {y : ElemIdx} (h : elemDrop? s f y = some (k, c)) :
    k ≤ vs.length ∧ TableStep P ⟨s, f, vals (top k vs) ++ [.plain (.elemDrop y)]⟩ c := by
  simp only [elemDrop?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ea, ei⟩, he, h⟩ := h
  vt_leaf; vt_pre0; exact .elemDrop he

end

end VarTab

open VarTab

/-! ## The step functions -/

/-- Head step of the variable family. -/
def variableStep? (_o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match e with
  | .plain (.localGet x) =>
    match f.local? x with
    | some (some v) => some (0, ⟨s, f, [v.toAdmin]⟩)
    | _ => none
  | .plain (.localSet x) => do
    let v ← top1? vs
    if x.toNat < f.locals.length then some (1, ⟨s, f.setLocal x v, []⟩) else none
  | .plain (.localTee x) => do
    let v ← top1? vs
    some (1, ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩)
  | .plain (.globalGet x) => do
    let g ← s.global? f x
    some (0, ⟨s, f, [g.2.value.toAdmin]⟩)
  | .plain (.globalSet x) => do
    let v ← top1? vs
    let g ← s.global? f x
    some (1, ⟨s.setGlobal g.1 v, f, []⟩)
  | _ => none

/-- Head step of the table family. -/
def tableStep? (o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match e with
  | .plain (.tableGet x) => tableGet? s f x vs
  | .plain (.tableSet x) => tableSet? s f x vs
  | .plain (.tableSize x) => tableSize? s f x
  | .plain (.tableGrow x) => tableGrow? o s f x vs
  | .plain (.tableFill x) => tableFill? s f x vs
  | .plain (.tableCopy x₁ x₂) => tableCopy? s f x₁ x₂ vs
  | .plain (.tableInit x y) => tableInit? s f x y vs
  | .plain (.elemDrop y) => elemDrop? s f y
  | _ => none

/-! ## Soundness -/

section
variable {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin} {k : Nat}
  {c : Config H}

theorem variableStep?_sound (h : variableStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  suffices k ≤ vs.length ∧ VariableStep ⟨s, f, vals (top k vs) ++ [e]⟩ c from
    ⟨this.1, .«variable» this.2⟩
  unfold variableStep? at h
  split at h
  · split at h
    · rename_i v hv; vt_leaf; vt_pre0; exact .localGet hv
    · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨hl, hv⟩ := top1?_sound hv
    split at h
    · rename_i hx; vt_leaf; vt_pre; exact .localSet hx
    · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨hl, hv⟩ := top1?_sound hv
    vt_leaf; vt_pre; exact .localTee
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, g⟩, hg, h⟩ := h
    vt_leaf; vt_pre0; exact .globalGet hg
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, ⟨a, g⟩, hg, h⟩ := h
    obtain ⟨hl, hv⟩ := top1?_sound hv
    vt_leaf; vt_pre; exact .globalSet hg
  · cases h

theorem tableStep?_sound (h : tableStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  suffices k ≤ vs.length ∧ TableStep (profile o) ⟨s, f, vals (top k vs) ++ [e]⟩ c from
    ⟨this.1, .table this.2⟩
  unfold tableStep? at h
  split at h
  · exact tableGet?_sound h
  · exact tableSet?_sound h
  · exact tableSize?_sound h
  · exact tableGrow?_sound h
  · exact tableFill?_sound h
  · exact tableCopy?_sound h
  · exact tableInit?_sound h
  · exact elemDrop?_sound h
  · cases h

/-! ## Completeness -/

set_option hygiene false in
/-- From `hl : vals args ++ [e] = <rule left-hand side>`, determine `args` and `e`. -/
macro "vt_args" : tactic =>
  `(tactic| (
    have hlen := congrArg List.length hl
    simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hlen
    rcases args with _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, _ | ⟨v₄, rest⟩⟩⟩⟩ <;>
      (try simp only [List.length_cons, List.length_nil] at hlen) <;> (try omega)
    all_goals
      simp only [vals_cons, vals_nil, List.cons_append, List.nil_append, List.cons.injEq,
        and_true, toAdmin_eq_iff, val?_intConst, val?_constI32, val?_ref, Admin.val?_toAdmin,
        Option.some.injEq, aconst] at hl
      repeat (first | (obtain ⟨h1, hl⟩ := hl; subst h1) | subst hl)))

theorem variableStep?_complete {args : List Val} (h : Head (profile o) s f args e c)
    (hf : famOf e = .variable) (hq : ∃ q, vs = q ++ args) :
    variableStep? o s f vs e = some (args.length, c) := by
  obtain ⟨q, rfl⟩ := hq
  have h' := h.fam_inv (by rw [hf]; decide)
  rw [hf] at h'
  simp only [FamRel] at h'
  clear h hf
  generalize hl : vals args ++ [e] = l at h'
  cases h' <;> vt_args <;> simp [variableStep?, *]

theorem tableStep?_complete {args : List Val} (h : Head (profile o) s f args e c)
    (hf : famOf e = .table) (hq : ∃ q, vs = q ++ args) :
    tableStep? o s f vs e = some (args.length, c) := by
  obtain ⟨q, rfl⟩ := hq
  have h' := h.fam_inv (by rw [hf]; decide)
  rw [hf] at h'
  simp only [FamRel] at h'
  clear h hf
  generalize hl : vals args ++ [e] = l at h'
  cases h' <;> vt_args
  all_goals simp [tableStep?, tableGet?, tableSet?, tableSize?, tableGrow?, tableFill?,
    tableCopy?, tableInit?, elemDrop?, *]
  all_goals first
    | (split_ifs <;> first | rfl | (exfalso; omega) | simp_all)
    | (intro hs; rcases ‹_ ∨ _› with hp | hp <;>
        simp_all [profile, Profile.deterministic, Profile.growMayFail, Profile.growMaySucceed])

end

end Silmaril.Wasm.SingleThreaded.Exec
