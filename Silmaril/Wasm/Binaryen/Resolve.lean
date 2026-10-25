module

public import Silmaril.Wasm.Binaryen.Named
public import Silmaril.Wasm.Binaryen.Lower
import Std.Data.String.ToNat

@[expose] public section

/-! # Resolution: layer N to layer D

`resolve` maps names to indices once:

* labels to de Bruijn depths through a break stack, innermost label winning, as
  `BinaryInstWriter::getBreakIndex` (`src/wasm/wasm-stack.cpp:3576`, version_133);
  `loop` and `if` push a scope even when unnamed (an `if` scope can never be
  named, so branches cannot target it from layer N);
* implicit (unnamed) blocks splice into the enclosing list, as
  `BinaryenIRWriter::visitBlock` does for blocks without a name
  (`src/wasm-stack.h:359`);
* an unreachable-typed named block, loop or if is written with the empty block
  type followed by `unreachable`, mirroring `afterChildren`
  (`src/wasm-stack.h:396`);
* function and global names to absolute indices (imports first).

BinaryenIRWriter's skip-after-unreachable (`visitPossibleBlockContents`,
`src/wasm-stack.h:293`) is **not** done here: it is the DCE pass
(`Binaryen/Pass/DCE.lean`), proved sound there.

The meaning of a layer-N module is the meaning of `lower (resolve m)`
(`NModule.beh`, `Binaryen/Behaviour.lean`).
-/

namespace Silmaril.Wasm.Binaryen

/-- Resolution failures. -/
inductive ResolveErr where
  | unboundLabel (l : Name)
  | unboundFunc (f : Name)
  | unboundGlobal (g : Name)
  | indexOverflow (n : Nat)
  deriving DecidableEq, Repr

/-- Function and global name spaces (absolute indices, imports first). -/
structure NameEnv where
  funcs : List Name
  globals : List Name
  deriving Repr

namespace NameEnv

def func (E : NameEnv) (f : Name) : Except ResolveErr FuncIdx :=
  match E.funcs.findIdx? (· == f) with
  | some n => match Idx.ofNat? n with
    | some i => .ok i
    | none => .error (.indexOverflow n)
  | none => .error (.unboundFunc f)

def global (E : NameEnv) (g : Name) : Except ResolveErr GlobalIdx :=
  match E.globals.findIdx? (· == g) with
  | some n => match Idx.ofNat? n with
    | some i => .ok i
    | none => .error (.indexOverflow n)
  | none => .error (.unboundGlobal g)

end NameEnv

/-- An index from a natural number, failing on overflow. -/
def toIdx {k : IndexKind} (n : Nat) : Except ResolveErr (Idx k) :=
  match Idx.ofNat? n with
  | some i => .ok i
  | none => .error (.indexOverflow n)

/-- The de Bruijn depth of label `l` in the break stack `L` (innermost first);
unnamed scopes are `none`. Innermost binding wins (`getBreakIndex`). -/
def labelDepth (L : List (Option Name)) (l : Name) : Except ResolveErr LabelIdx :=
  match L.findIdx? (· == some l) with
  | some n => toIdx n
  | none => .error (.unboundLabel l)

/-- The trailing `unreachable` written after an unreachable-typed scope. -/
def NTy.tail : NTy → List BExpr
  | .unreachable => [.op .unreachable []]
  | _ => []

mutual
/-- Resolve one expression to a list of folded trees (implicit blocks splice). -/
def resolveE (E : NameEnv) (L : List (Option Name)) : NExpr → Except ResolveErr (List BExpr)
  | .block none body _ => resolveL E L body
  | .block (some l) body ty => do
      let b ← resolveL E (some l :: L) body
      pure (.block ty.blockType b :: ty.tail)
  | .loop l body ty => do
      let b ← resolveE E (l :: L) body
      pure (.loop ty.blockType b :: ty.tail)
  | .if_ c t e ty => do
      let c' ← resolveE E L c
      let t' ← resolveE E (none :: L) t
      let e' ← resolveO E (none :: L) e
      pure (.if_ ty.blockType c' t' e' :: ty.tail)
  | .br l v c => do
      let d ← labelDepth L l
      let v' ← resolveO E L v
      let c' ← resolveO E L c
      pure [.op (if c.isSome then .brIf d else .br d) (v' ++ c')]
  | .switch ls d v c => do
      let ds ← ls.mapM (labelDepth L)
      let dd ← labelDepth L d
      let v' ← resolveO E L v
      let c' ← resolveE E L c
      pure [.op (.brTable ds dd) (v' ++ c')]
  | .call f args => do
      let fi ← E.func f
      let as ← resolveL E L args
      pure [.op (.call fi) as]
  | .localGet i => do pure [.op (.localGet (← toIdx i)) []]
  | .localSet i v tee => do
      let x ← toIdx i
      let v' ← resolveE E L v
      pure [.op (if tee then .localTee x else .localSet x) v']
  | .globalGet g => do pure [.op (.globalGet (← E.global g)) []]
  | .globalSet g v => do
      let x ← E.global g
      let v' ← resolveE E L v
      pure [.op (.globalSet x) v']
  | .const c => pure [.op c.instr []]
  | .unary op e => do pure [.op op.instr (← resolveE E L e)]
  | .binary op a b => do
      let a' ← resolveE E L a
      let b' ← resolveE E L b
      pure [.op op.instr (a' ++ b')]
  | .select a b c => do
      let a' ← resolveE E L a
      let b' ← resolveE E L b
      let c' ← resolveE E L c
      pure [.op (.select none) (a' ++ b' ++ c')]
  | .drop e => do pure [.op .drop (← resolveE E L e)]
  | .return_ v => do pure [.op .return_ (← resolveO E L v)]
  | .nop => pure [.op .nop []]
  | .unreachable => pure [.op .unreachable []]
/-- Resolve a list (concatenation). -/
def resolveL (E : NameEnv) (L : List (Option Name)) : List NExpr → Except ResolveErr (List BExpr)
  | [] => pure []
  | e :: es => do
      let a ← resolveE E L e
      let b ← resolveL E L es
      pure (a ++ b)
/-- Resolve an optional child (absent is the empty list). -/
def resolveO (E : NameEnv) (L : List (Option Name)) : Option NExpr → Except ResolveErr (List BExpr)
  | none => pure []
  | some e => resolveE E L e
end

namespace NModule

/-- The name environment of a module: imports, then defined functions; globals. -/
def env (m : NModule) : NameEnv :=
  ⟨m.imports.map Prod.fst ++ m.funcs.map Prod.fst, m.globals.map Prod.fst⟩

/-- **Resolution of a module.** Function bodies resolve under an empty break
stack: the function's own label is reached by `return` (layer N has no name for
it). Global initialisers lower to Core constant expressions. -/
def resolve (m : NModule) : Except ResolveErr BModule := do
  let E := m.env
  let funcs ← m.funcs.mapM fun (_, f) => do
    let body ← resolveE E [] f.body
    pure (⟨f.type, f.vars, body⟩ : BFunc)
  let globals ← m.globals.mapM fun (_, g) => do
    let init ← resolveE E [] g.init
    pure (⟨g.type, BExpr.lowerList init⟩ : Global)
  let exports ← m.exports.mapM fun x => do
    match x.kind with
    | .func => pure (⟨x.name, .func (← E.func x.internal)⟩ : Export)
    | .global => pure (⟨x.name, .global (← E.global x.internal)⟩ : Export)
  let start ← match m.start with
    | some s => do pure (some (← E.func s))
    | none => pure none
  let imports := m.imports.map fun (_, i) => (⟨i.module, i.base, .func i.type⟩ : Import)
  pure ⟨{ types := m.types, imports := imports, globals := globals, exports := exports,
          start := start }, funcs⟩

end NModule

/-! ## Resolution theorems -/

section Lemmas

theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = Except.ok a := rfl

/-- Resolution of a concatenation. -/
theorem resolveL_append (E : NameEnv) (L : List (Option Name)) (as bs : List NExpr) :
    resolveL E L (as ++ bs) = (do
      let x ← resolveL E L as
      let y ← resolveL E L bs
      pure (x ++ y)) := by
  induction as with
  | nil =>
    simp only [List.nil_append, resolveL, except_pure, except_ok_bind]
    cases resolveL E L bs <;> rfl
  | cons a as ih =>
    simp only [List.cons_append, resolveL, ih]
    cases resolveE E L a <;> cases resolveL E L as <;> cases resolveL E L bs <;>
      simp [except_ok_bind, except_error_bind, except_pure, List.append_assoc]

theorem resolveL_cons_ok {E : NameEnv} {L : List (Option Name)} {a : NExpr} {as : List NExpr}
    {es : List BExpr} (h : resolveL E L (a :: as) = .ok es) :
    ∃ x y, resolveE E L a = .ok x ∧ resolveL E L as = .ok y ∧ es = x ++ y := by
  simp only [resolveL] at h
  cases ha : resolveE E L a with
  | error err => rw [ha] at h; cases h
  | ok x =>
    cases has : resolveL E L as with
    | error err => rw [ha, has] at h; cases h
    | ok y => rw [ha, has] at h; cases h; exact ⟨x, y, rfl, rfl, rfl⟩

theorem resolveL_nil_ok {E : NameEnv} {L : List (Option Name)} {es : List BExpr}
    (h : resolveL E L [] = .ok es) : es = [] := by
  simp only [resolveL] at h
  cases h
  rfl

theorem resolveL_one_ok {E : NameEnv} {L : List (Option Name)} {a : NExpr} {es : List BExpr}
    (h : resolveL E L [a] = .ok es) : resolveE E L a = .ok es := by
  obtain ⟨x, y, hx, hy, rfl⟩ := resolveL_cons_ok h
  obtain rfl := resolveL_nil_ok hy
  rw [List.append_nil]
  exact hx

theorem resolveL_one_ok' {E : NameEnv} {L : List (Option Name)} {a : NExpr} {es : List BExpr}
    (h : resolveL E L [a] = .ok es) : ∃ x, resolveE E L a = .ok x ∧ es = x ++ [] := by
  obtain ⟨x, y, hx, hy, rfl⟩ := resolveL_cons_ok h
  obtain rfl := resolveL_nil_ok hy
  exact ⟨x, hx, rfl⟩

theorem resolveL_two_ok {E : NameEnv} {L : List (Option Name)} {a b : NExpr} {es : List BExpr}
    (h : resolveL E L [a, b] = .ok es) :
    ∃ x y, resolveE E L a = .ok x ∧ resolveE E L b = .ok y ∧ es = x ++ y := by
  obtain ⟨x, y, hx, hy, rfl⟩ := resolveL_cons_ok h
  exact ⟨x, y, hx, resolveL_one_ok hy, rfl⟩

theorem resolveL_three_ok {E : NameEnv} {L : List (Option Name)} {a b c : NExpr}
    {es : List BExpr} (h : resolveL E L [a, b, c] = .ok es) :
    ∃ x y z, resolveE E L a = .ok x ∧ resolveE E L b = .ok y ∧ resolveE E L c = .ok z ∧
      es = x ++ y ++ z := by
  obtain ⟨x, yz, hx, hyz, rfl⟩ := resolveL_cons_ok h
  obtain ⟨y, z, hy, hz, rfl⟩ := resolveL_two_ok hyz
  exact ⟨x, y, z, hx, hy, hz, (List.append_assoc _ _ _).symm⟩

/-- Free labels of a scope body are bound in the extended stack. -/
theorem mem_cons_of_mem_filter_ne {l : Option Name} {L : List (Option Name)} {xs : List Name}
    (h : ∀ x ∈ xs.filter (fun n => some n != l), some x ∈ L) : ∀ x ∈ xs, some x ∈ l :: L := by
  intro x hx
  by_cases hxl : some x = l
  · subst hxl
    simp
  · exact List.mem_cons_of_mem _ (h x (List.mem_filter.2 ⟨hx, by simp [hxl]⟩))

/-- Equal first-occurrence indices give equal depths. -/
theorem labelDepth_congr {L L' : List (Option Name)} {l l' : Name}
    (h1 : L'.findIdx? (· == some l') = L.findIdx? (· == some l)) (hl : some l ∈ L) :
    labelDepth L' l' = labelDepth L l := by
  cases hk : L.findIdx? (· == some l) with
  | none =>
    rw [List.findIdx?_eq_none_iff] at hk
    simpa using hk _ hl
  | some k =>
    unfold labelDepth
    rw [h1, hk]

theorem findIdx_rename {σ : Name → Name} (hσ : Function.Injective σ) (L : List (Option Name))
    (l : Name) :
    (L.map (Option.map σ)).findIdx? (· == some (σ l)) = L.findIdx? (· == some l) := by
  rw [List.findIdx?_map]
  congr 1
  funext x
  cases x <;> simp [hσ.eq_iff]

theorem mapM_labelDepth_rename {σ : Name → Name} (hσ : Function.Injective σ)
    (L : List (Option Name)) (ls : List Name) (h : ∀ x ∈ ls, some x ∈ L) :
    (ls.map σ).mapM (labelDepth (L.map (Option.map σ))) = ls.mapM (labelDepth L) := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [labelDepth_congr (findIdx_rename hσ L x) (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]

theorem renameLabelsOpt_isSome (σ : Name → Name) (o : Option NExpr) :
    (NExpr.renameLabelsOpt σ o).isSome = o.isSome := by
  cases o <;> rfl

mutual
theorem resolveE_rename (E : NameEnv) {σ : Name → Name} (hσ : Function.Injective σ) :
    (L : List (Option Name)) → (e : NExpr) → (∀ l ∈ e.freeLabels, some l ∈ L) →
      resolveE E (L.map (Option.map σ)) (e.renameLabels σ) = resolveE E L e
  | L, .block none body ty, hf => by
    have ih := resolveL_rename E hσ L body
      (fun x hx => hf x (by simp only [NExpr.freeLabels]; exact List.mem_filter.2 ⟨hx, by simp⟩))
    simp only [NExpr.renameLabels, Option.map, resolveE]
    exact ih
  | L, .block (some l) body ty, hf => by
    have ih := resolveL_rename E hσ (some l :: L) body
      (mem_cons_of_mem_filter_ne (fun x hx => hf x (by simp only [NExpr.freeLabels]; exact hx)))
    simp only [List.map_cons, Option.map] at ih
    simp only [NExpr.renameLabels, Option.map, resolveE]
    rw [ih]
  | L, .loop l body ty, hf => by
    have ih := resolveE_rename E hσ (l :: L) body
      (mem_cons_of_mem_filter_ne (fun x hx => hf x (by simp only [NExpr.freeLabels]; exact hx)))
    simp only [List.map_cons] at ih
    simp only [NExpr.renameLabels, resolveE]
    rw [ih]
  | L, .if_ c t e ty, hf => by
    have ihc := resolveE_rename E hσ L c (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have iht := resolveE_rename E hσ (none :: L) t
      (fun x hx => List.mem_cons_of_mem _ (hf x (by simp [NExpr.freeLabels, hx])))
    have ihe := resolveO_rename E hσ (none :: L) e
      (fun x hx => List.mem_cons_of_mem _ (hf x (by simp [NExpr.freeLabels, hx])))
    simp only [List.map_cons, Option.map] at iht ihe
    simp only [NExpr.renameLabels, resolveE]
    rw [ihc, iht, ihe]
  | L, .br l v c, hf => by
    have ihv := resolveO_rename E hσ L v (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have ihc := resolveO_rename E hσ L c (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have hd := labelDepth_congr (findIdx_rename hσ L l) (hf l (by simp [NExpr.freeLabels]))
    simp only [NExpr.renameLabels, resolveE]
    rw [hd, ihv, ihc, renameLabelsOpt_isSome]
  | L, .switch ls d v c, hf => by
    have ihv := resolveO_rename E hσ L v (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have ihc := resolveE_rename E hσ L c (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have hd := labelDepth_congr (findIdx_rename hσ L d) (hf d (by simp [NExpr.freeLabels]))
    have hls := mapM_labelDepth_rename hσ L ls
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [hls, hd, ihv, ihc]
  | L, .call f args, hf => by
    have ih := resolveL_rename E hσ L args (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [ih]
  | L, .localGet i, _ => by simp only [NExpr.renameLabels, resolveE]
  | L, .localSet i v tee, hf => by
    have ih := resolveE_rename E hσ L v (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [ih]
  | L, .globalGet g, _ => by simp only [NExpr.renameLabels, resolveE]
  | L, .globalSet g v, hf => by
    have ih := resolveE_rename E hσ L v (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [ih]
  | L, .const c, _ => by simp only [NExpr.renameLabels, resolveE]
  | L, .unary op v, hf => by
    have ih := resolveE_rename E hσ L v (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [ih]
  | L, .binary op a b, hf => by
    have iha := resolveE_rename E hσ L a (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have ihb := resolveE_rename E hσ L b (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [iha, ihb]
  | L, .select a b c, hf => by
    have iha := resolveE_rename E hσ L a (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have ihb := resolveE_rename E hσ L b (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have ihc := resolveE_rename E hσ L c (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [iha, ihb, ihc]
  | L, .drop v, hf => by
    have ih := resolveE_rename E hσ L v (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [ih]
  | L, .return_ v, hf => by
    have ih := resolveO_rename E hσ L v (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [NExpr.renameLabels, resolveE]
    rw [ih]
  | L, .nop, _ => by simp only [NExpr.renameLabels, resolveE]
  | L, .unreachable, _ => by simp only [NExpr.renameLabels, resolveE]

theorem resolveL_rename (E : NameEnv) {σ : Name → Name} (hσ : Function.Injective σ) :
    (L : List (Option Name)) → (es : List NExpr) →
      (∀ l ∈ NExpr.freeLabelsList es, some l ∈ L) →
      resolveL E (L.map (Option.map σ)) (NExpr.renameLabelsList σ es) = resolveL E L es
  | L, [], _ => by simp only [NExpr.renameLabelsList, resolveL]
  | L, e :: es, hf => by
    have ih1 := resolveE_rename E hσ L e
      (fun x hx => hf x (by simp [NExpr.freeLabelsList, hx]))
    have ih2 := resolveL_rename E hσ L es
      (fun x hx => hf x (by simp [NExpr.freeLabelsList, hx]))
    simp only [NExpr.renameLabelsList, resolveL]
    rw [ih1, ih2]

theorem resolveO_rename (E : NameEnv) {σ : Name → Name} (hσ : Function.Injective σ) :
    (L : List (Option Name)) → (o : Option NExpr) →
      (∀ l ∈ NExpr.freeLabelsOpt o, some l ∈ L) →
      resolveO E (L.map (Option.map σ)) (NExpr.renameLabelsOpt σ o) = resolveO E L o
  | L, none, _ => by simp only [NExpr.renameLabelsOpt, resolveO]
  | L, some e, hf => by
    simp only [NExpr.renameLabelsOpt, resolveO]
    exact resolveE_rename E hσ L e
      (fun x hx => hf x (by simp only [NExpr.freeLabelsOpt]; exact hx))
end

end Lemmas

/-- Compatible break stacks under a label renaming. -/
def StackRenamed (σ : Name → Name) (L L' : List (Option Name)) : Prop := L' = L.map (Option.map σ)

/-- **Alpha-invariance.** Renaming labels injectively (binders and uses together)
does not change the resolution, provided every free label of `e` is bound in the
break stack. Hence Binaryen's `UniqueNameMapper::uniquify` (`src/parsing.h:47`)
and `RemoveUnusedNames` renaming are free: their outputs lower to the same Core
code. -/
-- FLAG(statement-change): added `hfree` (every free label of `e` is bound in `L`).
-- Without it the statement is false: an unbound label `l` resolves to the error
-- `unboundLabel l` on one side and `unboundLabel (σ l)` on the other
-- (`resolve_rename_unbound_counterexample`).
theorem resolve_rename (E : NameEnv) (σ : Name → Name) (hσ : Function.Injective σ)
    (L L' : List (Option Name)) (hL : StackRenamed σ L L') (e : NExpr)
    (hfree : ∀ l ∈ e.freeLabels, some l ∈ L) :
    resolveE E L' (e.renameLabels σ) = resolveE E L e := by
  unfold StackRenamed at hL
  subst hL
  exact resolveE_rename E hσ L e hfree

/-- The original `resolve_rename` (without `hfree`) is false: renaming changes the
label reported in an `unboundLabel` error. -/
theorem resolve_rename_unbound_counterexample :
    ¬ ∀ (E : NameEnv) (σ : Name → Name) (_ : Function.Injective σ)
        (L L' : List (Option Name)) (_ : StackRenamed σ L L') (e : NExpr),
        resolveE E L' (e.renameLabels σ) = resolveE E L e := by
  intro h
  have := h ⟨[], []⟩ (fun s => "x" ++ s) (fun a b hab => (String.append_right_inj "x").1 hab)
    [] [] rfl (.br "a" none none)
  simp [NExpr.renameLabels, NExpr.renameLabelsOpt, resolveE, resolveO, labelDepth] at this

/-- Splicing nested implicit blocks (`MergeBlocks` on unnamed blocks,
`src/passes/MergeBlocks.cpp`) changes nothing after resolution. -/
theorem resolve_implicit_flatten (E : NameEnv) (L : List (Option Name))
    (pre inner post : List NExpr) (ty ty' : NTy) :
    resolveE E L (.block none (pre ++ [.block none inner ty'] ++ post) ty) =
      resolveE E L (.block none (pre ++ inner ++ post) ty) := by
  simp only [resolveE, resolveL_append, resolveL]
  cases resolveL E L pre <;> cases resolveL E L inner <;> cases resolveL E L post <;>
    simp [except_ok_bind, except_error_bind, except_pure, List.append_assoc]

/-! ## Naming: every layer-D tree has a layer-N view -/

/-- The generated label for the scope at depth `d` (`$l<d>`). -/
def genLabel (d : Nat) : Name := "l" ++ toString d

/-- Generated function and global names. -/
def genFunc (i : Nat) : Name := "f" ++ toString i
def genGlobal (i : Nat) : Name := "g" ++ toString i

/-- The `NTy` of a Core block type, if it is in the named fragment. -/
def tyOfBlockType : BlockType → Option NTy
  | .empty => some .none
  | .value t => some (.val t)
  | .typeIdx _ => none

/-- The name of the scope at de Bruijn depth `k`; fails for if scopes. -/
def scopeName (S : List (Option Nat)) (k : Nat) : Option Name :=
  match S[k]? with
  | some (some d) => some (genLabel d)
  | _ => none

mutual
/-- Name a folded tree in the profile fragment. `S` is the scope stack (innermost
first): `some d` for a block or loop named `$l<d>`, `none` for an if scope.
Fails outside the fragment, on stacky code, and on branches to if scopes. -/
def nameE (S : List (Option Nat)) : BExpr → Option NExpr
  | .op i args => do
      let as ← nameL S args
      match i, as with
      | .intConst .i32 b, [] => some (.const (.i32 b))
      | .intConst .i64 b, [] => some (.const (.i64 b))
      | .intUnOp t op, [a] => some (.unary (.int t op) a)
      | .intTestOp t _, [a] => some (.unary (.eqz t) a)
      | .intBinOp t op, [a, b] => some (.binary (.int t op) a b)
      | .intRelOp t op, [a, b] => some (.binary (.rel t op) a b)
      | .localGet x, [] => some (.localGet x.toNat)
      | .localSet x, [v] => some (.localSet x.toNat v false)
      | .localTee x, [v] => some (.localSet x.toNat v true)
      | .globalGet g, [] => some (.globalGet (genGlobal g.toNat))
      | .globalSet g, [v] => some (.globalSet (genGlobal g.toNat) v)
      | .call f, as => some (.call (genFunc f.toNat) as)
      | .drop, [e] => some (.drop e)
      | .select none, [a, b, c] => some (.select a b c)
      | .nop, [] => some .nop
      | .unreachable, [] => some .unreachable
      | .return_, [] => some (.return_ none)
      | .return_, [v] => some (.return_ (some v))
      | .br l, [] => do some (.br (← scopeName S l.toNat) none none)
      | .br l, [v] => do some (.br (← scopeName S l.toNat) (some v) none)
      | .brIf l, [c] => do some (.br (← scopeName S l.toNat) none (some c))
      | .brIf l, [v, c] => do some (.br (← scopeName S l.toNat) (some v) (some c))
      | .brTable ls d, [c] => do
          some (.switch (← ls.mapM (scopeName S ·.toNat)) (← scopeName S d.toNat) none c)
      | _, _ => none
  | .block bt body => do
      let ty ← tyOfBlockType bt
      let b ← nameL (some S.length :: S) body
      some (.block (some (genLabel S.length)) b ty)
  | .loop bt body => do
      let ty ← tyOfBlockType bt
      let b ← nameL (some S.length :: S) body
      some (.loop (some (genLabel S.length)) (.block none b ty) ty)
  | .if_ bt c t e => do
      let ty ← tyOfBlockType bt
      let cs ← nameL S c
      let c' ← match cs with | [c'] => some c' | _ => none
      let t' ← nameL (none :: S) t
      let e' ← nameL (none :: S) e
      some (.if_ c' (.block none t' ty) (some (.block none e' ty)) ty)
  | .tryTable .. => none
/-- `nameE` on a list. -/
def nameL (S : List (Option Nat)) : List BExpr → Option (List NExpr)
  | [] => some []
  | e :: es => do
      let a ← nameE S e
      let b ← nameL S es
      some (a :: b)
end

/-! ### Naming lemmas -/

section NamingLemmas

theorem natToString_inj {a b : Nat} (h : toString a = toString b) : a = b := by
  simpa using congrArg String.toNat? h

theorem genLabel_inj : Function.Injective genLabel := fun _ _ h =>
  natToString_inj ((String.append_right_inj "l").1 h)

theorem genFunc_inj : Function.Injective genFunc := fun _ _ h =>
  natToString_inj ((String.append_right_inj "f").1 h)

theorem genGlobal_inj : Function.Injective genGlobal := fun _ _ h =>
  natToString_inj ((String.append_right_inj "g").1 h)

/-- The first index satisfying `p` is `k`. -/
theorem findIdx?_eq_some_of {α : Type} (xs : List α) (p : α → Bool) (k : Nat)
    (hk : ∀ j x, j < k → xs[j]? = some x → p x = false)
    (hx : ∃ x, xs[k]? = some x ∧ p x = true) : xs.findIdx? p = some k := by
  induction xs generalizing k with
  | nil =>
    obtain ⟨x, hx, _⟩ := hx
    simp at hx
  | cons a xs ih =>
    rw [List.findIdx?_cons]
    cases k with
    | zero =>
      obtain ⟨x, hx, hp⟩ := hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      simp [hp]
    | succ k =>
      have ha : p a = false := hk 0 a (Nat.succ_pos _) (by simp)
      rw [ha]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih k (fun j x hj h => hk (j + 1) x (by omega) (by simpa using h)) (by simpa using hx)]
      try rfl

theorem toIdx_toNat {k : IndexKind} (i : Idx k) :
    (toIdx i.toNat : Except ResolveErr (Idx k)) = .ok i := by
  simp [toIdx, Idx.ofNat?_toNat]

/-- Scope stacks built by `nameE`: the scope at depth `k` is named `$l<d>` with
`d + k + 1` the stack height. -/
def GoodScopes (S : List (Option Nat)) : Prop :=
  ∀ k d, S[k]? = some (some d) → d + k + 1 = S.length

theorem GoodScopes.nil : GoodScopes [] := by
  intro k d h
  simp at h

theorem GoodScopes.push_some {S : List (Option Nat)} (h : GoodScopes S) :
    GoodScopes (some S.length :: S) := by
  intro k d hk
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp
  | succ k =>
    simp only [List.getElem?_cons_succ] at hk
    have := h k d hk
    simp only [List.length_cons]
    omega

theorem GoodScopes.push_none {S : List (Option Nat)} (h : GoodScopes S) :
    GoodScopes (none :: S) := by
  intro k d hk
  cases k with
  | zero => simp at hk
  | succ k =>
    simp only [List.getElem?_cons_succ] at hk
    have := h k d hk
    simp only [List.length_cons]
    omega

theorem labelDepth_scope {S : List (Option Nat)} (hS : GoodScopes S) {k : Nat} {nm : Name}
    (h : scopeName S k = some nm) :
    labelDepth (S.map (Option.map genLabel)) nm = toIdx k := by
  unfold scopeName at h
  split at h
  · rename_i d hd
    cases h
    have hf : (S.map (Option.map genLabel)).findIdx? (· == some (genLabel d)) = some k := by
      apply findIdx?_eq_some_of
      · intro j x hj hx
        rw [List.getElem?_map] at hx
        cases hj' : S[j]? with
        | none => rw [hj'] at hx; cases hx
        | some o =>
          rw [hj'] at hx
          simp at hx
          subst hx
          cases o with
          | none => simp
          | some d' =>
            have h1 := hS j d' hj'
            have h2 := hS k d hd
            have hne : d' ≠ d := by omega
            simp [genLabel_inj.eq_iff, hne]
      · exact ⟨some (genLabel d), by simp [List.getElem?_map, hd], by simp⟩
    unfold labelDepth
    rw [hf]
    try rfl
  · cases h

theorem mapM_scopeName {S : List (Option Nat)} (hS : GoodScopes S) :
    ∀ (ls : List LabelIdx) (ns : List Name),
      ls.mapM (fun x => scopeName S x.toNat) = some ns →
      ns.mapM (labelDepth (S.map (Option.map genLabel))) = .ok ls
  | [], ns, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, ns, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨n0, h0, ns0, h1, rfl⟩ := h
    simp only [List.mapM_cons, labelDepth_scope hS h0, toIdx_toNat, except_ok_bind, except_pure,
      mapM_scopeName hS xs ns0 h1]

theorem NameEnv.func_genFunc {E : NameEnv}
    (hE : ∀ i, i < 2 ^ 32 → E.funcs[i]? = some (genFunc i)) (f : FuncIdx) :
    E.func (genFunc f.toNat) = .ok f := by
  have hlt : f.toNat < 2 ^ 32 := f.value.isLt
  have hf : E.funcs.findIdx? (· == genFunc f.toNat) = some f.toNat := by
    apply findIdx?_eq_some_of
    · intro j x hj hx
      rw [hE j (by omega)] at hx
      cases hx
      simp only [beq_eq_false_iff_ne, ne_eq, genFunc_inj.eq_iff]
      omega
    · exact ⟨_, hE _ hlt, by simp⟩
  unfold NameEnv.func
  rw [hf]
  simp [Idx.ofNat?_toNat]

theorem NameEnv.global_genGlobal {E : NameEnv}
    (hG : ∀ i, i < 2 ^ 32 → E.globals[i]? = some (genGlobal i)) (g : GlobalIdx) :
    E.global (genGlobal g.toNat) = .ok g := by
  have hlt : g.toNat < 2 ^ 32 := g.value.isLt
  have hf : E.globals.findIdx? (· == genGlobal g.toNat) = some g.toNat := by
    apply findIdx?_eq_some_of
    · intro j x hj hx
      rw [hG j (by omega)] at hx
      cases hx
      simp only [beq_eq_false_iff_ne, ne_eq, genGlobal_inj.eq_iff]
      omega
    · exact ⟨_, hG _ hlt, by simp⟩
  unfold NameEnv.global
  rw [hf]
  simp [Idx.ofNat?_toNat]

theorem tyOfBlockType_some {bt : BlockType} {ty : NTy} (h : tyOfBlockType bt = some ty) :
    ty.blockType = bt ∧ ty.tail = [] := by
  cases bt <;> simp [tyOfBlockType] at h <;> subst h <;> simp [NTy.blockType, NTy.tail]

mutual
theorem nameE_resolve (E : NameEnv) (hE : ∀ i, i < 2 ^ 32 → E.funcs[i]? = some (genFunc i))
    (hG : ∀ i, i < 2 ^ 32 → E.globals[i]? = some (genGlobal i)) :
    (S : List (Option Nat)) → (e : BExpr) → (n : NExpr) → GoodScopes S → nameE S e = some n →
      ∃ es, resolveE E (S.map (Option.map genLabel)) n = .ok es ∧
        BExpr.lowerList es = e.lower
  | S, .op i args, n, hS, h => by
    have ihA := nameL_resolve E hE hG S args
    cases hA : nameL S args with
    | none =>
      rw [nameE, hA] at h
      cases h
    | some as =>
      obtain ⟨es', hr, hlow⟩ := ihA as hS hA
      rw [nameE, hA] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      refine ⟨[.op i es'], ?_, by simp [hlow]⟩
      split at h
      · -- i32.const
        cases h
        obtain rfl := resolveL_nil_ok hr
        rfl
      · -- i64.const
        cases h
        obtain rfl := resolveL_nil_ok hr
        rfl
      · -- integer unary operator
        cases h
        simp only [resolveE]
        rw [resolveL_one_ok hr]
        rfl
      · -- eqz
        rename_i op _
        cases op
        cases h
        simp only [resolveE]
        rw [resolveL_one_ok hr]
        rfl
      · -- integer binary operator
        cases h
        obtain ⟨x, y, hx, hy, rfl⟩ := resolveL_two_ok hr
        simp only [resolveE]
        rw [hx, hy]
        rfl
      · -- integer comparison
        cases h
        obtain ⟨x, y, hx, hy, rfl⟩ := resolveL_two_ok hr
        simp only [resolveE]
        rw [hx, hy]
        rfl
      · -- local.get
        cases h
        obtain rfl := resolveL_nil_ok hr
        simp only [resolveE]
        rw [toIdx_toNat]
        rfl
      · -- local.set
        cases h
        simp only [resolveE]
        rw [toIdx_toNat, resolveL_one_ok hr]
        rfl
      · -- local.tee
        cases h
        simp only [resolveE]
        rw [toIdx_toNat, resolveL_one_ok hr]
        rfl
      · -- global.get
        cases h
        obtain rfl := resolveL_nil_ok hr
        simp only [resolveE]
        rw [NameEnv.global_genGlobal hG]
        rfl
      · -- global.set
        cases h
        simp only [resolveE]
        rw [NameEnv.global_genGlobal hG, resolveL_one_ok hr]
        rfl
      · -- call
        cases h
        simp only [resolveE]
        rw [NameEnv.func_genFunc hE, hr]
        rfl
      · -- drop
        cases h
        simp only [resolveE]
        rw [resolveL_one_ok hr]
        rfl
      · -- select
        cases h
        obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := resolveL_three_ok hr
        simp only [resolveE]
        rw [hx, hy, hz]
        rfl
      · -- nop
        cases h
        obtain rfl := resolveL_nil_ok hr
        rfl
      · -- unreachable
        cases h
        obtain rfl := resolveL_nil_ok hr
        rfl
      · -- return
        cases h
        obtain rfl := resolveL_nil_ok hr
        rfl
      · -- return with a value
        cases h
        simp only [resolveE, resolveO]
        rw [resolveL_one_ok hr]
        rfl
      · -- br
        obtain ⟨nm, hs, h⟩ := Option.bind_eq_some_iff.1 h
        cases h
        obtain rfl := resolveL_nil_ok hr
        simp only [resolveE]
        rw [labelDepth_scope hS hs, toIdx_toNat]
        rfl
      · -- br with a value
        obtain ⟨nm, hs, h⟩ := Option.bind_eq_some_iff.1 h
        cases h
        obtain ⟨x, hx, rfl⟩ := resolveL_one_ok' hr
        simp only [resolveE, resolveO]
        rw [labelDepth_scope hS hs, toIdx_toNat, hx]
        rfl
      · -- br_if
        obtain ⟨nm, hs, h⟩ := Option.bind_eq_some_iff.1 h
        cases h
        simp only [resolveE, resolveO]
        rw [labelDepth_scope hS hs, toIdx_toNat, resolveL_one_ok hr]
        rfl
      · -- br_if with a value
        obtain ⟨nm, hs, h⟩ := Option.bind_eq_some_iff.1 h
        cases h
        obtain ⟨x, y, hx, hy, rfl⟩ := resolveL_two_ok hr
        simp only [resolveE, resolveO]
        rw [labelDepth_scope hS hs, toIdx_toNat, hx, hy]
        rfl
      · -- br_table
        obtain ⟨nms, hms, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨nm, hs, h⟩ := Option.bind_eq_some_iff.1 h
        cases h
        simp only [resolveE, resolveO]
        rw [mapM_scopeName hS _ _ hms, labelDepth_scope hS hs, toIdx_toNat, resolveL_one_ok hr]
        rfl
      · -- outside the fragment
        cases h
  | S, .block bt body, n, hS, h => by
    simp only [nameE, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, hty, b, hb, rfl⟩ := h
    obtain ⟨es', hr, hlow⟩ := nameL_resolve E hE hG (some S.length :: S) body b hS.push_some hb
    obtain ⟨hbt, htl⟩ := tyOfBlockType_some hty
    refine ⟨[.block bt es'], ?_, by simp [BExpr.lower, hlow]⟩
    simp only [List.map_cons, Option.map] at hr
    simp only [resolveE, hr, hbt, htl, except_ok_bind, except_pure]
  | S, .loop bt body, n, hS, h => by
    simp only [nameE, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, hty, b, hb, rfl⟩ := h
    obtain ⟨es', hr, hlow⟩ := nameL_resolve E hE hG (some S.length :: S) body b hS.push_some hb
    obtain ⟨hbt, htl⟩ := tyOfBlockType_some hty
    refine ⟨[.loop bt es'], ?_, by simp [BExpr.lower, hlow]⟩
    simp only [List.map_cons, Option.map] at hr
    simp only [resolveE, hr, hbt, htl, except_ok_bind, except_pure]
  | S, .if_ bt c t e, n, hS, h => by
    simp only [nameE, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ty, hty, cs, hcs, h⟩ := h
    rcases cs with _ | ⟨c0, _ | ⟨c1, cs⟩⟩
    · simp at h
    rotate_left
    · simp at h
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t', ht', e', he', rfl⟩ := h
    obtain ⟨cr, hcr, hclow⟩ := nameL_resolve E hE hG S c [c0] hS hcs
    obtain ⟨x, y, hx, hy, rfl⟩ := resolveL_cons_ok hcr
    obtain rfl := resolveL_nil_ok hy
    obtain ⟨tr, htr, htlow⟩ := nameL_resolve E hE hG (none :: S) t t' hS.push_none ht'
    obtain ⟨er, her, helow⟩ := nameL_resolve E hE hG (none :: S) e e' hS.push_none he'
    obtain ⟨hbt, htl⟩ := tyOfBlockType_some hty
    refine ⟨[.if_ bt x tr er], ?_, ?_⟩
    · simp only [List.map_cons, Option.map] at htr her
      simp only [resolveE, resolveO, hx, htr, her, hbt, htl, except_ok_bind, except_pure]
    · simp only [List.append_nil] at hclow
      simp [BExpr.lower, htlow, helow, hclow]
  | S, .tryTable bt cs body, n, hS, h => by
    simp [nameE] at h

theorem nameL_resolve (E : NameEnv) (hE : ∀ i, i < 2 ^ 32 → E.funcs[i]? = some (genFunc i))
    (hG : ∀ i, i < 2 ^ 32 → E.globals[i]? = some (genGlobal i)) :
    (S : List (Option Nat)) → (es : List BExpr) → (ns : List NExpr) → GoodScopes S →
      nameL S es = some ns →
      ∃ es', resolveL E (S.map (Option.map genLabel)) ns = .ok es' ∧
        BExpr.lowerList es' = BExpr.lowerList es
  | S, [], ns, _, h => by
    simp only [nameL, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | S, e :: es, ns, hS, h => by
    simp only [nameL, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨x, hx, hxl⟩ := nameE_resolve E hE hG S e a hS ha
    obtain ⟨y, hy, hyl⟩ := nameL_resolve E hE hG S es b hS hb
    refine ⟨x ++ y, ?_, by simp [hxl, hyl]⟩
    simp only [resolveL, hx, hy, except_ok_bind, except_pure]
end

end NamingLemmas

/-- **Naming round-trips through resolution, up to lowering.** -/
-- FLAG(statement-change): `hE`/`hG` were `∀ i, E.funcs[i]? = some (genFunc i)`
-- (resp. globals), which no finite list satisfies, so the theorem was vacuous.
-- They now range over the index space only (`i < 2 ^ 32`), which every index
-- `nameE` can produce lies in.
theorem resolve_nameE (E : NameEnv) (hE : ∀ i, i < 2 ^ 32 → E.funcs[i]? = some (genFunc i))
    (hG : ∀ i, i < 2 ^ 32 → E.globals[i]? = some (genGlobal i)) (e : BExpr) (n : NExpr)
    (h : nameE [] e = some n) :
    ∃ es, resolveE E [] n = .ok es ∧ BExpr.lowerList es = e.lower :=
  nameE_resolve E hE hG [] e n GoodScopes.nil h

/-- The original hypotheses of `resolve_nameE` are unsatisfiable. -/
theorem resolve_nameE_hyp_vacuous (E : NameEnv) : ¬ ∀ i, E.funcs[i]? = some (genFunc i) := by
  intro h
  have := h E.funcs.length
  simp at this

end Silmaril.Wasm.Binaryen
