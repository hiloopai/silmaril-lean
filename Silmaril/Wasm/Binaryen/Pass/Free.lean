module

public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Binaryen.Refinalize

@[expose] public section

/-! # P0: free passes (equivalence by equality of lowerings)

A pass that never changes the lowering is an equivalence in both directions, for
every profile and host, by `ExportRefines.of_lower_eq`: no semantics is needed.

* fold/unfold (`IRBuilder` tree reconstruction, `src/wasm/wasm-ir-builder.cpp`)
  — `foldPass_lower` from `lowerList_fold`;
* `MergeBlocks` on implicit (unnamed) blocks (`src/passes/MergeBlocks.cpp`) —
  `flattenImplicit_resolve`;
* `UniqueNameMapper::uniquify` (`src/parsing.h:47`) — `uniquify_resolve`, an
  instance of `resolve_rename` scope by scope.

`RemoveUnusedNames` (`src/passes/RemoveUnusedNames.cpp`) is **not** free here: a
block that loses its name is spliced by resolution, which removes a Core
`block` and shifts the de Bruijn indices of the body. Its soundness is the
`Joinable` lemma `block_unwrap` (`Pass/Vacuum.lean`).
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics

/-- **Free passes are equivalences.** -/
theorem free_pass_sound {pass : BModule → BModule} (h : ∀ m, (pass m).lower = m.lower)
    (m : BModule) (P : Profile) {H : Type} (host : HostSemantics H) :
    ExportRefines (· = ·) P host (pass m).lower m.lower ∧
      ExportRefines (· = ·) P host m.lower (pass m).lower := by
  rw [h m]
  exact ⟨ExportRefines.refl (fun _ => rfl) _, ExportRefines.refl (fun _ => rfl) _⟩

/-- Fold every function body with the given arities. -/
def foldPass (arity : Instr → Option Nat) (m : BModule) : BModule :=
  { m with funcs := m.funcs.map (Declaration.Func.mapBody (fold arity)) }

theorem foldPass_lower (arity : Instr → Option Nat) (m : BModule) :
    (foldPass arity m).lower = m.lower := by
  have h : (Declaration.Func.mapBody BExpr.lowerList ∘ Declaration.Func.mapBody (fold arity) :
      BFunc → Func) = Declaration.Func.mapBody BExpr.lowerList := by
    funext f
    simp [Declaration.Func.mapBody, lowerList_fold]
  simp only [foldPass, BModule.lower, List.map_map, h]

/-- Unfold completely: every instruction in a leaf. -/
def unfoldPass (m : BModule) : BModule := BModule.lift m.lower

theorem unfoldPass_lower (m : BModule) : (unfoldPass m).lower = m.lower := lower_lift _

/-! ## Layer N: implicit-block flattening -/

mutual
/-- Splice nested implicit blocks into their enclosing lists, everywhere. -/
def flatE : NExpr → NExpr
  | .block l body ty => .block l (flatL body) ty
  | .loop l body ty => .loop l (flatE body) ty
  | .if_ c t e ty => .if_ (flatE c) (flatE t) (flatO e) ty
  | .br l v c => .br l (flatO v) (flatO c)
  | .switch ls d v c => .switch ls d (flatO v) (flatE c)
  | .call f args => .call f (flatL args)
  | .localSet i v tee => .localSet i (flatE v) tee
  | .globalSet g v => .globalSet g (flatE v)
  | .unary op v => .unary op (flatE v)
  | .binary op a b => .binary op (flatE a) (flatE b)
  | .select a b c => .select (flatE a) (flatE b) (flatE c)
  | .drop v => .drop (flatE v)
  | .return_ v => .return_ (flatO v)
  | .localGet i => .localGet i
  | .globalGet g => .globalGet g
  | .const c => .const c
  | .nop => .nop
  | .unreachable => .unreachable
/-- A list (block body or call operands; resolution concatenates both): implicit
children are spliced. -/
def flatL : List NExpr → List NExpr
  | [] => []
  | .block none inner _ :: es => flatL inner ++ flatL es
  | e :: es => flatE e :: flatL es
/-- Optional child. -/
def flatO : Option NExpr → Option NExpr
  | none => none
  | some e => some (flatE e)
end

theorem flatL_cons_of (e : NExpr) (es : List NExpr)
    (h : ¬ ∃ inner ty, e = .block none inner ty) : flatL (e :: es) = flatE e :: flatL es := by
  cases e with
  | block l body ty =>
    cases l with
    | none => exact absurd ⟨body, ty, rfl⟩ h
    | some l => simp [flatL]
  | _ => simp [flatL]

theorem flatO_isSome (o : Option NExpr) : (flatO o).isSome = o.isSome := by
  cases o <;> simp [flatO]

mutual
theorem flatE_resolve (E : NameEnv) : (L : List (Option Name)) → (e : NExpr) →
    resolveE E L (flatE e) = resolveE E L e
  | L, .block l body ty => by
    have ih := flatL_resolve E (l :: L) body
    have ih' := flatL_resolve E L body
    cases l with
    | none =>
      simp only [flatE, resolveE]
      exact ih'
    | some l =>
      simp only [flatE, resolveE]
      rw [ih]
  | L, .loop l body ty => by
    have ih := flatE_resolve E (l :: L) body
    simp only [flatE, resolveE]
    rw [ih]
  | L, .if_ c t e ty => by
    have ihc := flatE_resolve E L c
    have iht := flatE_resolve E (none :: L) t
    have ihe := flatO_resolve E (none :: L) e
    simp only [flatE, resolveE]
    rw [ihc, iht, ihe]
  | L, .br l v c => by
    have ihv := flatO_resolve E L v
    have ihc := flatO_resolve E L c
    simp only [flatE, resolveE]
    rw [ihv, ihc, flatO_isSome]
  | L, .switch ls d v c => by
    have ihv := flatO_resolve E L v
    have ihc := flatE_resolve E L c
    simp only [flatE, resolveE]
    rw [ihv, ihc]
  | L, .call f args => by
    have ih := flatL_resolve E L args
    simp only [flatE, resolveE]
    rw [ih]
  | L, .localGet i => by simp only [flatE]
  | L, .localSet i v tee => by
    have ih := flatE_resolve E L v
    simp only [flatE, resolveE]
    rw [ih]
  | L, .globalGet g => by simp only [flatE]
  | L, .globalSet g v => by
    have ih := flatE_resolve E L v
    simp only [flatE, resolveE]
    rw [ih]
  | L, .const c => by simp only [flatE]
  | L, .unary op v => by
    have ih := flatE_resolve E L v
    simp only [flatE, resolveE]
    rw [ih]
  | L, .binary op a b => by
    have iha := flatE_resolve E L a
    have ihb := flatE_resolve E L b
    simp only [flatE, resolveE]
    rw [iha, ihb]
  | L, .select a b c => by
    have iha := flatE_resolve E L a
    have ihb := flatE_resolve E L b
    have ihc := flatE_resolve E L c
    simp only [flatE, resolveE]
    rw [iha, ihb, ihc]
  | L, .drop v => by
    have ih := flatE_resolve E L v
    simp only [flatE, resolveE]
    rw [ih]
  | L, .return_ v => by
    have ih := flatO_resolve E L v
    simp only [flatE, resolveE]
    rw [ih]
  | L, .nop => by simp only [flatE]
  | L, .unreachable => by simp only [flatE]

theorem flatL_resolve (E : NameEnv) : (L : List (Option Name)) → (es : List NExpr) →
    resolveL E L (flatL es) = resolveL E L es
  | L, [] => by simp only [flatL]
  | L, e :: es => by
    have he := flatE_resolve E L e
    have hes := flatL_resolve E L es
    by_cases h : ∃ inner ty, e = .block none inner ty
    · obtain ⟨inner, ty, rfl⟩ := h
      simp only [flatE, resolveE] at he
      simp only [flatL, resolveL_append, he, hes, resolveL, resolveE]
    · rw [flatL_cons_of e es h]
      simp only [resolveL]
      rw [he, hes]

theorem flatO_resolve (E : NameEnv) : (L : List (Option Name)) → (o : Option NExpr) →
    resolveO E L (flatO o) = resolveO E L o
  | L, none => by simp only [flatO]
  | L, some e => by
    simp only [flatO, resolveO]
    exact flatE_resolve E L e
end

/-- **Flattening implicit blocks is free.** -/
theorem flattenImplicit_resolve (E : NameEnv) (L : List (Option Name)) (e : NExpr) :
    resolveE E L (flatE e) = resolveE E L e :=
  flatE_resolve E L e

/-! ## Layer N: uniquify -/

/-- The fresh label number `n`. -/
def uniqName (n : Nat) : Name := "u" ++ toString n

/-- Rename a label use through the scope environment (innermost first). -/
def useName (env : List (Name × Name)) (l : Name) : Name := (env.lookup l).getD l

/-- Bind a scope label: fresh name `u<n>` if named. -/
def bindName (env : List (Name × Name)) (n : Nat) : Option Name →
    Option Name × List (Name × Name) × Nat
  | some l => (some (uniqName n), (l, uniqName n) :: env, n + 1)
  | none => (none, env, n)

mutual
/-- `UniqueNameMapper::uniquify`: give every scope label a distinct fresh name. -/
def uniqE (env : List (Name × Name)) (n : Nat) : NExpr → NExpr × Nat
  | .block l body ty =>
      let (l', env', n') := bindName env n l
      let (b, n'') := uniqL env' n' body
      (.block l' b ty, n'')
  | .loop l body ty =>
      let (l', env', n') := bindName env n l
      let (b, n'') := uniqE env' n' body
      (.loop l' b ty, n'')
  | .if_ c t e ty =>
      let (c', n₁) := uniqE env n c
      let (t', n₂) := uniqE env n₁ t
      let (e', n₃) := uniqO env n₂ e
      (.if_ c' t' e' ty, n₃)
  | .br l v c =>
      let (v', n₁) := uniqO env n v
      let (c', n₂) := uniqO env n₁ c
      (.br (useName env l) v' c', n₂)
  | .switch ls d v c =>
      let (v', n₁) := uniqO env n v
      let (c', n₂) := uniqE env n₁ c
      (.switch (ls.map (useName env)) (useName env d) v' c', n₂)
  | .call f args =>
      let (as, n₁) := uniqL env n args
      (.call f as, n₁)
  | .localSet i v tee => let (v', n₁) := uniqE env n v; (.localSet i v' tee, n₁)
  | .globalSet g v => let (v', n₁) := uniqE env n v; (.globalSet g v', n₁)
  | .unary op v => let (v', n₁) := uniqE env n v; (.unary op v', n₁)
  | .drop v => let (v', n₁) := uniqE env n v; (.drop v', n₁)
  | .binary op a b =>
      let (a', n₁) := uniqE env n a
      let (b', n₂) := uniqE env n₁ b
      (.binary op a' b', n₂)
  | .select a b c =>
      let (a', n₁) := uniqE env n a
      let (b', n₂) := uniqE env n₁ b
      let (c', n₃) := uniqE env n₂ c
      (.select a' b' c', n₃)
  | .return_ v => let (v', n₁) := uniqO env n v; (.return_ v', n₁)
  | .localGet i => (.localGet i, n)
  | .globalGet g => (.globalGet g, n)
  | .const c => (.const c, n)
  | .nop => (.nop, n)
  | .unreachable => (.unreachable, n)
/-- `uniqE` on a list, threading the counter. -/
def uniqL (env : List (Name × Name)) (n : Nat) : List NExpr → List NExpr × Nat
  | [] => ([], n)
  | e :: es =>
      let (e', n₁) := uniqE env n e
      let (es', n₂) := uniqL env n₁ es
      (e' :: es', n₂)
/-- `uniqE` on an optional child. -/
def uniqO (env : List (Name × Name)) (n : Nat) : Option NExpr → Option NExpr × Nat
  | none => (none, n)
  | some e => let (e', n₁) := uniqE env n e; (some e', n₁)
end

/-- Uniquify a closed function body. -/
def uniquify (e : NExpr) : NExpr := (uniqE [] 0 e).1

theorem uniqName_inj : Function.Injective uniqName := fun _ _ h =>
  natToString_inj ((String.append_right_inj "u").1 h)

/-! ### Counting: uniquify binds `u<n>`, `u<n+1>`, ... in order -/

theorem map_range'_append {f : Nat → Name} {n a m b : Nat} (h : m = n + a) :
    (List.range' n a).map f ++ (List.range' m b).map f = (List.range' n (a + b)).map f := by
  subst h
  rw [← List.map_append, List.range'_append_1]

mutual
theorem uniqE_count (env : List (Name × Name)) (n : Nat) : (e : NExpr) →
    ∃ k, (uniqE env n e).2 = n + k ∧
      (uniqE env n e).1.boundLabels = (List.range' n k).map uniqName
  | .block none body ty => by
    obtain ⟨k, hk, hb⟩ := uniqL_count env n body
    rcases h : uniqL env n body with ⟨b, n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, bindName, h]
    refine ⟨k, hk, ?_⟩
    simp only [NExpr.boundLabels, Option.toList, List.nil_append]
    exact hb
  | .block (some l) body ty => by
    obtain ⟨k, hk, hb⟩ := uniqL_count ((l, uniqName n) :: env) (n + 1) body
    rcases h : uniqL ((l, uniqName n) :: env) (n + 1) body with ⟨b, n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, bindName, h]
    refine ⟨k + 1, by omega, ?_⟩
    simp [NExpr.boundLabels, hb, List.range'_succ]
  | .loop none body ty => by
    obtain ⟨k, hk, hb⟩ := uniqE_count env n body
    rcases h : uniqE env n body with ⟨b, n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, bindName, h]
    refine ⟨k, hk, ?_⟩
    simp only [NExpr.boundLabels, Option.toList, List.nil_append]
    exact hb
  | .loop (some l) body ty => by
    obtain ⟨k, hk, hb⟩ := uniqE_count ((l, uniqName n) :: env) (n + 1) body
    rcases h : uniqE ((l, uniqName n) :: env) (n + 1) body with ⟨b, n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, bindName, h]
    refine ⟨k + 1, by omega, ?_⟩
    simp [NExpr.boundLabels, hb, List.range'_succ]
  | .if_ c t e ty => by
    obtain ⟨k₁, hk₁, hb₁⟩ := uniqE_count env n c
    rcases h₁ : uniqE env n c with ⟨c', n₁⟩
    rw [h₁] at hk₁ hb₁
    simp only at hk₁ hb₁
    obtain ⟨k₂, hk₂, hb₂⟩ := uniqE_count env n₁ t
    rcases h₂ : uniqE env n₁ t with ⟨t', n₂⟩
    rw [h₂] at hk₂ hb₂
    simp only at hk₂ hb₂
    obtain ⟨k₃, hk₃, hb₃⟩ := uniqO_count env n₂ e
    rcases h₃ : uniqO env n₂ e with ⟨e', n₃⟩
    rw [h₃] at hk₃ hb₃
    simp only at hk₃ hb₃
    simp only [uniqE, h₁, h₂, h₃]
    refine ⟨k₁ + k₂ + k₃, by omega, ?_⟩
    simp only [NExpr.boundLabels, hb₁, hb₂, hb₃]
    rw [map_range'_append hk₁, map_range'_append (by omega)]
  | .br l v c => by
    obtain ⟨k₁, hk₁, hb₁⟩ := uniqO_count env n v
    rcases h₁ : uniqO env n v with ⟨v', n₁⟩
    rw [h₁] at hk₁ hb₁
    simp only at hk₁ hb₁
    obtain ⟨k₂, hk₂, hb₂⟩ := uniqO_count env n₁ c
    rcases h₂ : uniqO env n₁ c with ⟨c', n₂⟩
    rw [h₂] at hk₂ hb₂
    simp only at hk₂ hb₂
    simp only [uniqE, h₁, h₂]
    refine ⟨k₁ + k₂, by omega, ?_⟩
    simp only [NExpr.boundLabels, hb₁, hb₂]
    rw [map_range'_append hk₁]
  | .switch ls d v c => by
    obtain ⟨k₁, hk₁, hb₁⟩ := uniqO_count env n v
    rcases h₁ : uniqO env n v with ⟨v', n₁⟩
    rw [h₁] at hk₁ hb₁
    simp only at hk₁ hb₁
    obtain ⟨k₂, hk₂, hb₂⟩ := uniqE_count env n₁ c
    rcases h₂ : uniqE env n₁ c with ⟨c', n₂⟩
    rw [h₂] at hk₂ hb₂
    simp only at hk₂ hb₂
    simp only [uniqE, h₁, h₂]
    refine ⟨k₁ + k₂, by omega, ?_⟩
    simp only [NExpr.boundLabels, hb₁, hb₂]
    rw [map_range'_append hk₁]
  | .call f args => by
    obtain ⟨k, hk, hb⟩ := uniqL_count env n args
    rcases h : uniqL env n args with ⟨as, n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, h]
    exact ⟨k, hk, by simp only [NExpr.boundLabels]; exact hb⟩
  | .localGet i => ⟨0, by simp [uniqE], by simp [uniqE, NExpr.boundLabels]⟩
  | .localSet i v tee => by
    obtain ⟨k, hk, hb⟩ := uniqE_count env n v
    rcases h : uniqE env n v with ⟨v', n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, h]
    exact ⟨k, hk, by simp only [NExpr.boundLabels]; exact hb⟩
  | .globalGet g => ⟨0, by simp [uniqE], by simp [uniqE, NExpr.boundLabels]⟩
  | .globalSet g v => by
    obtain ⟨k, hk, hb⟩ := uniqE_count env n v
    rcases h : uniqE env n v with ⟨v', n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, h]
    exact ⟨k, hk, by simp only [NExpr.boundLabels]; exact hb⟩
  | .const c => ⟨0, by simp [uniqE], by simp [uniqE, NExpr.boundLabels]⟩
  | .unary op v => by
    obtain ⟨k, hk, hb⟩ := uniqE_count env n v
    rcases h : uniqE env n v with ⟨v', n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, h]
    exact ⟨k, hk, by simp only [NExpr.boundLabels]; exact hb⟩
  | .binary op a b => by
    obtain ⟨k₁, hk₁, hb₁⟩ := uniqE_count env n a
    rcases h₁ : uniqE env n a with ⟨a', n₁⟩
    rw [h₁] at hk₁ hb₁
    simp only at hk₁ hb₁
    obtain ⟨k₂, hk₂, hb₂⟩ := uniqE_count env n₁ b
    rcases h₂ : uniqE env n₁ b with ⟨b', n₂⟩
    rw [h₂] at hk₂ hb₂
    simp only at hk₂ hb₂
    simp only [uniqE, h₁, h₂]
    refine ⟨k₁ + k₂, by omega, ?_⟩
    simp only [NExpr.boundLabels, hb₁, hb₂]
    rw [map_range'_append hk₁]
  | .select a b c => by
    obtain ⟨k₁, hk₁, hb₁⟩ := uniqE_count env n a
    rcases h₁ : uniqE env n a with ⟨a', n₁⟩
    rw [h₁] at hk₁ hb₁
    simp only at hk₁ hb₁
    obtain ⟨k₂, hk₂, hb₂⟩ := uniqE_count env n₁ b
    rcases h₂ : uniqE env n₁ b with ⟨b', n₂⟩
    rw [h₂] at hk₂ hb₂
    simp only at hk₂ hb₂
    obtain ⟨k₃, hk₃, hb₃⟩ := uniqE_count env n₂ c
    rcases h₃ : uniqE env n₂ c with ⟨c', n₃⟩
    rw [h₃] at hk₃ hb₃
    simp only at hk₃ hb₃
    simp only [uniqE, h₁, h₂, h₃]
    refine ⟨k₁ + k₂ + k₃, by omega, ?_⟩
    simp only [NExpr.boundLabels, hb₁, hb₂, hb₃]
    rw [map_range'_append hk₁, map_range'_append (by omega)]
  | .drop v => by
    obtain ⟨k, hk, hb⟩ := uniqE_count env n v
    rcases h : uniqE env n v with ⟨v', n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, h]
    exact ⟨k, hk, by simp only [NExpr.boundLabels]; exact hb⟩
  | .return_ v => by
    obtain ⟨k, hk, hb⟩ := uniqO_count env n v
    rcases h : uniqO env n v with ⟨v', n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqE, h]
    exact ⟨k, hk, by simp only [NExpr.boundLabels]; exact hb⟩
  | .nop => ⟨0, by simp [uniqE], by simp [uniqE, NExpr.boundLabels]⟩
  | .unreachable => ⟨0, by simp [uniqE], by simp [uniqE, NExpr.boundLabels]⟩

theorem uniqL_count (env : List (Name × Name)) (n : Nat) : (es : List NExpr) →
    ∃ k, (uniqL env n es).2 = n + k ∧
      NExpr.boundLabelsList (uniqL env n es).1 = (List.range' n k).map uniqName
  | [] => ⟨0, by simp [uniqL], by simp [uniqL, NExpr.boundLabelsList]⟩
  | e :: es => by
    obtain ⟨k₁, hk₁, hb₁⟩ := uniqE_count env n e
    rcases h₁ : uniqE env n e with ⟨e', n₁⟩
    rw [h₁] at hk₁ hb₁
    simp only at hk₁ hb₁
    obtain ⟨k₂, hk₂, hb₂⟩ := uniqL_count env n₁ es
    rcases h₂ : uniqL env n₁ es with ⟨es', n₂⟩
    rw [h₂] at hk₂ hb₂
    simp only at hk₂ hb₂
    simp only [uniqL, h₁, h₂]
    refine ⟨k₁ + k₂, by omega, ?_⟩
    simp only [NExpr.boundLabelsList, hb₁, hb₂]
    rw [map_range'_append hk₁]

theorem uniqO_count (env : List (Name × Name)) (n : Nat) : (o : Option NExpr) →
    ∃ k, (uniqO env n o).2 = n + k ∧
      NExpr.boundLabelsOpt (uniqO env n o).1 = (List.range' n k).map uniqName
  | none => ⟨0, by simp [uniqO], by simp [uniqO, NExpr.boundLabelsOpt]⟩
  | some e => by
    obtain ⟨k, hk, hb⟩ := uniqE_count env n e
    rcases h : uniqE env n e with ⟨e', n₁⟩
    rw [h] at hk hb
    simp only at hk hb
    simp only [uniqO, h]
    exact ⟨k, hk, by simp only [NExpr.boundLabelsOpt]; exact hb⟩
end

/-- After uniquify, bound labels are distinct. -/
theorem uniquify_nodup (e : NExpr) : (uniquify e).boundLabels.Nodup := by
  obtain ⟨k, -, hb⟩ := uniqE_count [] 0 e
  unfold uniquify
  rw [hb]
  exact List.pairwise_map.2
    ((List.nodup_range' (s := 0) (n := k)).imp fun h he => h (uniqName_inj he))

/-! ### Resolution: uniquify preserves the meaning of closed bodies -/

/-- The scope correspondence maintained by `uniqE`: original stack `L`, renamed
stack `L'`, and the environment mapping each named scope to its fresh name. -/
inductive UniqRel : List (Name × Name) → List (Option Name) → List (Option Name) → Prop
  | nil : UniqRel [] [] []
  | unnamed {env : List (Name × Name)} {L L' : List (Option Name)} :
      UniqRel env L L' → UniqRel env (none :: L) (none :: L')
  | named {env : List (Name × Name)} {L L' : List (Option Name)} (l u : Name) :
      UniqRel env L L' → UniqRel ((l, u) :: env) (some l :: L) (some u :: L')

/-- Every name on the renamed stack is `u<k>` for some `k < n`. -/
def UniqFresh (n : Nat) (L' : List (Option Name)) : Prop :=
  ∀ u ∈ L'.filterMap id, ∃ k < n, u = uniqName k

theorem UniqFresh.mono {n m : Nat} {L' : List (Option Name)} (h : UniqFresh n L') (hnm : n ≤ m) :
    UniqFresh m L' := by
  intro u hu
  obtain ⟨k, hk, rfl⟩ := h u hu
  exact ⟨k, by omega, rfl⟩

theorem UniqFresh.push {n : Nat} {L' : List (Option Name)} (h : UniqFresh n L')
    (hnd : (L'.filterMap id).Nodup) :
    ((some (uniqName n) :: L').filterMap id).Nodup ∧
      UniqFresh (n + 1) (some (uniqName n) :: L') := by
  have hc : (some (uniqName n) :: L').filterMap id = uniqName n :: L'.filterMap id := rfl
  refine ⟨?_, ?_⟩
  · rw [hc]
    refine List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩
    obtain ⟨k, hk, he⟩ := h _ hm
    have := uniqName_inj he
    omega
  · intro u hu
    rw [hc] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨n, by omega, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := h u hu
      exact ⟨k, by omega, rfl⟩

theorem UniqRel.lookup {env : List (Name × Name)} {L L' : List (Option Name)}
    (h : UniqRel env L L') :
    ∀ {l : Name}, (L'.filterMap id).Nodup → some l ∈ L →
      L'.findIdx? (· == some (useName env l)) = L.findIdx? (· == some l) ∧
        some (useName env l) ∈ L' := by
  induction h with
  | nil => intro l _ hl; simp at hl
  | @unnamed env L L' _ ih =>
    intro l hnd hl
    have hnd' : (L'.filterMap id).Nodup := hnd
    have hl' : some l ∈ L := by simpa using hl
    obtain ⟨h1, h2⟩ := ih hnd' hl'
    refine ⟨?_, List.mem_cons_of_mem _ h2⟩
    rw [List.findIdx?_cons, List.findIdx?_cons, h1]
    simp
  | @named env L L' l0 u _ ih =>
    intro l hnd hl
    have hc : (some u :: L').filterMap id = u :: L'.filterMap id := rfl
    rw [hc] at hnd
    obtain ⟨hnu, hnd'⟩ := List.nodup_cons.1 hnd
    by_cases hll : l = l0
    · subst hll
      have hu : useName ((l, u) :: env) l = u := by simp [useName]
      rw [hu]
      refine ⟨?_, by simp⟩
      rw [List.findIdx?_cons, List.findIdx?_cons]
      simp
    · have hb : (l == l0) = false := by simp [hll]
      have hu : useName ((l0, u) :: env) l = useName env l := by
        simp only [useName, List.lookup_cons, hb]
      rw [hu]
      have hl' : some l ∈ L := by
        rcases List.mem_cons.1 hl with h | h
        · exact absurd (Option.some.inj h) hll
        · exact h
      obtain ⟨h1, h2⟩ := ih hnd' hl'
      have hne : u ≠ useName env l := by
        rintro heq
        exact hnu (List.mem_filterMap.2 ⟨_, h2, by simp [heq]⟩)
      refine ⟨?_, List.mem_cons_of_mem _ h2⟩
      rw [List.findIdx?_cons, List.findIdx?_cons, h1]
      have hll' : l0 ≠ l := fun h => hll h.symm
      simp [hne, hll']

theorem mapM_labelDepth_uniq {env : List (Name × Name)} {L L' : List (Option Name)}
    (hR : UniqRel env L L') (hnd : (L'.filterMap id).Nodup) (ls : List Name)
    (h : ∀ x ∈ ls, some x ∈ L) :
    (ls.map (useName env)).mapM (labelDepth L') = ls.mapM (labelDepth L) := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons]
    have hx : some x ∈ L := h x (by simp)
    rw [labelDepth_congr (hR.lookup hnd hx).1 hx, ih (fun y hy => h y (by simp [hy]))]

theorem uniqO_isSome (env : List (Name × Name)) (n : Nat) (o : Option NExpr) :
    (uniqO env n o).1.isSome = o.isSome := by
  cases o with
  | none => rfl
  | some e =>
    rcases h : uniqE env n e with ⟨e', n₁⟩
    simp [uniqO, h]

mutual
theorem uniqE_resolve (E : NameEnv) : (env : List (Name × Name)) → (n : Nat) →
    (L L' : List (Option Name)) → (e : NExpr) → UniqRel env L L' → (L'.filterMap id).Nodup →
    UniqFresh n L' → (∀ l ∈ e.freeLabels, some l ∈ L) →
    resolveE E L' (uniqE env n e).1 = resolveE E L e
  | env, n, L, L', .block none body ty, hR, hnd, hfr, hf => by
    have ih := uniqL_resolve E env n L L' body hR hnd hfr
      (fun x hx => hf x (by simp only [NExpr.freeLabels]; exact List.mem_filter.2 ⟨hx, by simp⟩))
    rcases h : uniqL env n body with ⟨b, n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, bindName, h, resolveE]
    exact ih
  | env, n, L, L', .block (some l) body ty, hR, hnd, hfr, hf => by
    obtain ⟨hnd', hfr'⟩ := hfr.push hnd
    have ih := uniqL_resolve E ((l, uniqName n) :: env) (n + 1) (some l :: L)
      (some (uniqName n) :: L') body (.named l (uniqName n) hR) hnd' hfr'
      (mem_cons_of_mem_filter_ne (fun x hx => hf x (by simp only [NExpr.freeLabels]; exact hx)))
    rcases h : uniqL ((l, uniqName n) :: env) (n + 1) body with ⟨b, n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, bindName, h, resolveE]
    rw [ih]
  | env, n, L, L', .loop none body ty, hR, hnd, hfr, hf => by
    have ih := uniqE_resolve E env n (none :: L) (none :: L') body (.unnamed hR) hnd hfr
      (mem_cons_of_mem_filter_ne (fun x hx => hf x (by simp only [NExpr.freeLabels]; exact hx)))
    rcases h : uniqE env n body with ⟨b, n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, bindName, h, resolveE]
    rw [ih]
  | env, n, L, L', .loop (some l) body ty, hR, hnd, hfr, hf => by
    obtain ⟨hnd', hfr'⟩ := hfr.push hnd
    have ih := uniqE_resolve E ((l, uniqName n) :: env) (n + 1) (some l :: L)
      (some (uniqName n) :: L') body (.named l (uniqName n) hR) hnd' hfr'
      (mem_cons_of_mem_filter_ne (fun x hx => hf x (by simp only [NExpr.freeLabels]; exact hx)))
    rcases h : uniqE ((l, uniqName n) :: env) (n + 1) body with ⟨b, n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, bindName, h, resolveE]
    rw [ih]
  | env, n, L, L', .if_ c t e ty, hR, hnd, hfr, hf => by
    have ihc := uniqE_resolve E env n L L' c hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    obtain ⟨k₁, hk₁, -⟩ := uniqE_count env n c
    rcases h₁ : uniqE env n c with ⟨c', n₁⟩
    rw [h₁] at ihc hk₁
    simp only at ihc hk₁
    have iht := uniqE_resolve E env n₁ (none :: L) (none :: L') t (.unnamed hR) hnd
      (hfr.mono (by omega))
      (fun x hx => List.mem_cons_of_mem _ (hf x (by simp [NExpr.freeLabels, hx])))
    obtain ⟨k₂, hk₂, -⟩ := uniqE_count env n₁ t
    rcases h₂ : uniqE env n₁ t with ⟨t', n₂⟩
    rw [h₂] at iht hk₂
    simp only at iht hk₂
    have ihe := uniqO_resolve E env n₂ (none :: L) (none :: L') e (.unnamed hR) hnd
      (hfr.mono (by omega))
      (fun x hx => List.mem_cons_of_mem _ (hf x (by simp [NExpr.freeLabels, hx])))
    rcases h₃ : uniqO env n₂ e with ⟨e', n₃⟩
    rw [h₃] at ihe
    simp only at ihe
    simp only [uniqE, h₁, h₂, h₃, resolveE]
    rw [ihc, iht, ihe]
  | env, n, L, L', .br l v c, hR, hnd, hfr, hf => by
    have ihv := uniqO_resolve E env n L L' v hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    obtain ⟨k₁, hk₁, -⟩ := uniqO_count env n v
    rcases h₁ : uniqO env n v with ⟨v', n₁⟩
    rw [h₁] at ihv hk₁
    simp only at ihv hk₁
    have ihc := uniqO_resolve E env n₁ L L' c hR hnd (hfr.mono (by omega))
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    have hcs := uniqO_isSome env n₁ c
    rcases h₂ : uniqO env n₁ c with ⟨c', n₂⟩
    rw [h₂] at ihc hcs
    simp only at ihc hcs
    have hl : some l ∈ L := hf l (by simp [NExpr.freeLabels])
    have hd := labelDepth_congr (hR.lookup hnd hl).1 hl
    simp only [uniqE, h₁, h₂, resolveE]
    rw [hd, ihv, ihc, hcs]
  | env, n, L, L', .switch ls d v c, hR, hnd, hfr, hf => by
    have ihv := uniqO_resolve E env n L L' v hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    obtain ⟨k₁, hk₁, -⟩ := uniqO_count env n v
    rcases h₁ : uniqO env n v with ⟨v', n₁⟩
    rw [h₁] at ihv hk₁
    simp only at ihv hk₁
    have ihc := uniqE_resolve E env n₁ L L' c hR hnd (hfr.mono (by omega))
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h₂ : uniqE env n₁ c with ⟨c', n₂⟩
    rw [h₂] at ihc
    simp only at ihc
    have hdm : some d ∈ L := hf d (by simp [NExpr.freeLabels])
    have hd := labelDepth_congr (hR.lookup hnd hdm).1 hdm
    have hls := mapM_labelDepth_uniq hR hnd ls (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    simp only [uniqE, h₁, h₂, resolveE]
    rw [hls, hd, ihv, ihc]
  | env, n, L, L', .call f args, hR, hnd, hfr, hf => by
    have ih := uniqL_resolve E env n L L' args hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h : uniqL env n args with ⟨as, n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, h, resolveE]
    rw [ih]
  | env, n, L, L', .localGet i, _, _, _, _ => by simp only [uniqE, resolveE]
  | env, n, L, L', .localSet i v tee, hR, hnd, hfr, hf => by
    have ih := uniqE_resolve E env n L L' v hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h : uniqE env n v with ⟨v', n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, h, resolveE]
    rw [ih]
  | env, n, L, L', .globalGet g, _, _, _, _ => by simp only [uniqE, resolveE]
  | env, n, L, L', .globalSet g v, hR, hnd, hfr, hf => by
    have ih := uniqE_resolve E env n L L' v hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h : uniqE env n v with ⟨v', n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, h, resolveE]
    rw [ih]
  | env, n, L, L', .const c, _, _, _, _ => by simp only [uniqE, resolveE]
  | env, n, L, L', .unary op v, hR, hnd, hfr, hf => by
    have ih := uniqE_resolve E env n L L' v hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h : uniqE env n v with ⟨v', n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, h, resolveE]
    rw [ih]
  | env, n, L, L', .binary op a b, hR, hnd, hfr, hf => by
    have iha := uniqE_resolve E env n L L' a hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    obtain ⟨k₁, hk₁, -⟩ := uniqE_count env n a
    rcases h₁ : uniqE env n a with ⟨a', n₁⟩
    rw [h₁] at iha hk₁
    simp only at iha hk₁
    have ihb := uniqE_resolve E env n₁ L L' b hR hnd (hfr.mono (by omega))
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h₂ : uniqE env n₁ b with ⟨b', n₂⟩
    rw [h₂] at ihb
    simp only at ihb
    simp only [uniqE, h₁, h₂, resolveE]
    rw [iha, ihb]
  | env, n, L, L', .select a b c, hR, hnd, hfr, hf => by
    have iha := uniqE_resolve E env n L L' a hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    obtain ⟨k₁, hk₁, -⟩ := uniqE_count env n a
    rcases h₁ : uniqE env n a with ⟨a', n₁⟩
    rw [h₁] at iha hk₁
    simp only at iha hk₁
    have ihb := uniqE_resolve E env n₁ L L' b hR hnd (hfr.mono (by omega))
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    obtain ⟨k₂, hk₂, -⟩ := uniqE_count env n₁ b
    rcases h₂ : uniqE env n₁ b with ⟨b', n₂⟩
    rw [h₂] at ihb hk₂
    simp only at ihb hk₂
    have ihc := uniqE_resolve E env n₂ L L' c hR hnd (hfr.mono (by omega))
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h₃ : uniqE env n₂ c with ⟨c', n₃⟩
    rw [h₃] at ihc
    simp only at ihc
    simp only [uniqE, h₁, h₂, h₃, resolveE]
    rw [iha, ihb, ihc]
  | env, n, L, L', .drop v, hR, hnd, hfr, hf => by
    have ih := uniqE_resolve E env n L L' v hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h : uniqE env n v with ⟨v', n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, h, resolveE]
    rw [ih]
  | env, n, L, L', .return_ v, hR, hnd, hfr, hf => by
    have ih := uniqO_resolve E env n L L' v hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabels, hx]))
    rcases h : uniqO env n v with ⟨v', n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqE, h, resolveE]
    rw [ih]
  | env, n, L, L', .nop, _, _, _, _ => by simp only [uniqE, resolveE]
  | env, n, L, L', .unreachable, _, _, _, _ => by simp only [uniqE, resolveE]

theorem uniqL_resolve (E : NameEnv) : (env : List (Name × Name)) → (n : Nat) →
    (L L' : List (Option Name)) → (es : List NExpr) → UniqRel env L L' →
    (L'.filterMap id).Nodup → UniqFresh n L' → (∀ l ∈ NExpr.freeLabelsList es, some l ∈ L) →
    resolveL E L' (uniqL env n es).1 = resolveL E L es
  | env, n, L, L', [], _, _, _, _ => by simp only [uniqL, resolveL]
  | env, n, L, L', e :: es, hR, hnd, hfr, hf => by
    have ih1 := uniqE_resolve E env n L L' e hR hnd hfr
      (fun x hx => hf x (by simp [NExpr.freeLabelsList, hx]))
    obtain ⟨k₁, hk₁, -⟩ := uniqE_count env n e
    rcases h₁ : uniqE env n e with ⟨e', n₁⟩
    rw [h₁] at ih1 hk₁
    simp only at ih1 hk₁
    have ih2 := uniqL_resolve E env n₁ L L' es hR hnd (hfr.mono (by omega))
      (fun x hx => hf x (by simp [NExpr.freeLabelsList, hx]))
    rcases h₂ : uniqL env n₁ es with ⟨es', n₂⟩
    rw [h₂] at ih2
    simp only at ih2
    simp only [uniqL, h₁, h₂, resolveL]
    rw [ih1, ih2]

theorem uniqO_resolve (E : NameEnv) : (env : List (Name × Name)) → (n : Nat) →
    (L L' : List (Option Name)) → (o : Option NExpr) → UniqRel env L L' →
    (L'.filterMap id).Nodup → UniqFresh n L' → (∀ l ∈ NExpr.freeLabelsOpt o, some l ∈ L) →
    resolveO E L' (uniqO env n o).1 = resolveO E L o
  | env, n, L, L', none, _, _, _, _ => by simp only [uniqO, resolveO]
  | env, n, L, L', some e, hR, hnd, hfr, hf => by
    have ih := uniqE_resolve E env n L L' e hR hnd hfr
      (fun x hx => hf x (by simp only [NExpr.freeLabelsOpt]; exact hx))
    rcases h : uniqE env n e with ⟨e', n₁⟩
    rw [h] at ih
    simp only at ih
    simp only [uniqO, h, resolveO]
    exact ih
end

/-- **Uniquify is free**: same resolution, for a closed body. -/
-- FLAG(statement-change): added `hclosed : e.freeLabels = []`. Without it the
-- statement is false: a free use of a label spelled like a fresh name (`u0`) is
-- captured by the renamed binder (`uniquify_resolve_capture_counterexample`).
-- Function bodies resolve under the empty break stack, so a body that resolves
-- at all is closed.
theorem uniquify_resolve (E : NameEnv) (e : NExpr) (hclosed : e.freeLabels = []) :
    resolveE E [] (uniquify e) = resolveE E [] e := by
  unfold uniquify
  exact uniqE_resolve E [] 0 [] [] e .nil List.nodup_nil (by intro u hu; simp at hu)
    (by simp [hclosed])

/-- The original `uniquify_resolve` (for open bodies) is false: the free label
`u0` becomes bound by the renamed scope. -/
theorem uniquify_resolve_capture_counterexample :
    ¬ ∀ (E : NameEnv) (e : NExpr), resolveE E [] (uniquify e) = resolveE E [] e := by
  intro h
  have hb : (uniqName 0 == "a") = false := by decide
  have hu : uniquify (.block (some "a") [.br (uniqName 0) none none] .none) =
      .block (some (uniqName 0)) [.br (uniqName 0) none none] .none := by
    simp only [uniquify, uniqE, uniqL, uniqO, bindName, useName, List.lookup_cons, hb,
      List.lookup_nil, Option.getD]
  have h1 := h ⟨[], []⟩ (.block (some "a") [.br (uniqName 0) none none] .none)
  have hne : "a" ≠ uniqName 0 := by decide
  rw [hu] at h1
  simp [resolveE, resolveL, resolveO, labelDepth, toIdx, Idx.ofNat?, hne] at h1

end Silmaril.Wasm.Binaryen
