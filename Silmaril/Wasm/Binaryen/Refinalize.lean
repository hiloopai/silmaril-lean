module

public import Silmaril.Wasm.Binaryen.NTyping

@[expose] public section

/-! # ReFinalize

Binaryen's `ReFinalize` (`src/ir/ReFinalize.cpp`, version_133) recomputes every
`type` annotation bottom-up after a pass: a block's type is the least upper
bound of its last child's type and of the values branched to it (unreachable
when its body is unreachable and nothing branches to it); an `if` with an
unreachable condition is unreachable; any expression with an unreachable
operand is unreachable.

`refinalize` is that computation on layer N. The three properties a pass
author relies on are stated: it is **sound** (the result is well typed at the
type it computes, in Binaryen's validator typing `HasTypeB`, which adds the
unreachable-operand rules to `HasType`; in `HasType` itself soundness fails,
`refinalize_sound_false`), **principal** (that type is below every type the
input has), and **idempotent**; it also preserves free labels.
-/

namespace Silmaril.Wasm.Binaryen

/-- Free branches of an expression: target label and carried type. -/
abbrev Brs := List (Name × NTy)

/-- Least upper bound of a list, ignoring incompatible elements. -/
def lubAll (init : NTy) (ts : List NTy) : NTy :=
  ts.foldl (fun acc t => (NTy.lub acc t).getD acc) init

/-- `unreachable` if any operand type is, otherwise `t`. -/
def unlessUnreachable (ops : List NTy) (t : NTy) : NTy :=
  if ops.contains .unreachable then .unreachable else t

/-- Close a scope named `l`: the types carried to it, and the remaining branches. -/
def closeScope (l : Option Name) (brs : Brs) : List NTy × Brs :=
  match l with
  | some n => ((brs.filter (·.1 == n)).map (·.2), brs.filter (·.1 != n))
  | none => ([], brs)

mutual
/-- Recompute the type annotations of an expression; returns the new expression,
its type and its free branches. -/
def refinE (Γ : NEnv) : NExpr → NExpr × NTy × Brs
  | .block l body _ =>
      let r := refinL Γ body
      let last := (r.2.1.getLast?).getD .none
      let (mine, rest) := closeScope l r.2.2
      let t := if mine.isEmpty then last else lubAll last mine
      (.block l r.1 t, t, rest)
  | .loop l body _ =>
      let r := refinE Γ body
      (.loop l r.1 r.2.1, r.2.1, (closeScope l r.2.2).2)
  | .if_ c t e _ =>
      let rc := refinE Γ c
      let rt := refinE Γ t
      let re := refinO Γ e
      let ty := match re with
        | none => .none
        | some r => (NTy.lub rt.2.1 r.2.1).getD .none
      let ty := unlessUnreachable [rc.2.1] ty
      (.if_ rc.1 rt.1 (re.map (·.1)) ty, ty, rc.2.2 ++ rt.2.2 ++ ((re.map (·.2.2)).getD []))
  | .br l v c =>
      let rv := refinO Γ v
      let rc := refinO Γ c
      let vt := (rv.map (·.2.1)).getD .none
      let ops := (rv.map (·.2.1)).toList ++ (rc.map (·.2.1)).toList
      let ty := if c.isSome then unlessUnreachable ops vt else .unreachable
      (.br l (rv.map (·.1)) (rc.map (·.1)), ty,
        (l, vt) :: (((rv.map (·.2.2)).getD []) ++ ((rc.map (·.2.2)).getD [])))
  | .switch ls d v c =>
      let rv := refinO Γ v
      let rc := refinE Γ c
      let vt := (rv.map (·.2.1)).getD .none
      (.switch ls d (rv.map (·.1)) rc.1, .unreachable,
        (d :: ls).map (fun n => (n, vt)) ++ ((rv.map (·.2.2)).getD []) ++ rc.2.2)
  | .call f args =>
      let r := refinL Γ args
      let rs := ((Γ.funcs.lookup f).map (·.2)).getD []
      (.call f r.1, unlessUnreachable r.2.1 (resultTy rs), r.2.2)
  | .localGet i => (.localGet i, ((Γ.locals[i]?).map NTy.val).getD .none, [])
  | .localSet i v tee =>
      let r := refinE Γ v
      let t := if tee then ((Γ.locals[i]?).map NTy.val).getD .none else .none
      (.localSet i r.1 tee, unlessUnreachable [r.2.1] t, r.2.2)
  | .globalGet g => (.globalGet g, ((Γ.globals.lookup g).map NTy.val).getD .none, [])
  | .globalSet g v =>
      let r := refinE Γ v
      (.globalSet g r.1, unlessUnreachable [r.2.1] .none, r.2.2)
  | .const c => (.const c, .val c.ty, [])
  | .unary op e =>
      let r := refinE Γ e
      (.unary op r.1, unlessUnreachable [r.2.1] (.val op.resTy), r.2.2)
  | .binary op a b =>
      let ra := refinE Γ a
      let rb := refinE Γ b
      (.binary op ra.1 rb.1, unlessUnreachable [ra.2.1, rb.2.1] (.val op.resTy), ra.2.2 ++ rb.2.2)
  | .select a b c =>
      let ra := refinE Γ a
      let rb := refinE Γ b
      let rc := refinE Γ c
      (.select ra.1 rb.1 rc.1, unlessUnreachable [ra.2.1, rb.2.1, rc.2.1] ra.2.1,
        ra.2.2 ++ rb.2.2 ++ rc.2.2)
  | .drop e =>
      let r := refinE Γ e
      (.drop r.1, unlessUnreachable [r.2.1] .none, r.2.2)
  | .return_ v =>
      let r := refinO Γ v
      (.return_ (r.map (·.1)), .unreachable, (r.map (·.2.2)).getD [])
  | .nop => (.nop, .none, [])
  | .unreachable => (.unreachable, .unreachable, [])
/-- `refinE` on a list: new elements, their types, their free branches. -/
def refinL (Γ : NEnv) : List NExpr → List NExpr × List NTy × Brs
  | [] => ([], [], [])
  | e :: es =>
      let r := refinE Γ e
      let rs := refinL Γ es
      (r.1 :: rs.1, r.2.1 :: rs.2.1, r.2.2 ++ rs.2.2)
/-- `refinE` on an optional child. -/
def refinO (Γ : NEnv) : Option NExpr → Option (NExpr × NTy × Brs)
  | none => none
  | some e => some (refinE Γ e)
end

/-- `ReFinalize`: recompute every type annotation. -/
def refinalize (Γ : NEnv) (e : NExpr) : NExpr := (refinE Γ e).1

/-- The type `refinalize` computes. -/
def refinType (Γ : NEnv) (e : NExpr) : NTy := (refinE Γ e).2.1

/-! ## Binaryen's validator typing

`HasType` (`Binaryen/NTyping.lean`) has no rule typing a node with an
unreachable operand at `unreachable`, which is exactly what `ReFinalize` does
(and what Binaryen's validator, `src/wasm/wasm-validator.cpp`, accepts): e.g.
`(drop (unreachable))` is refinalized to type `unreachable`, which `HasType`
cannot derive (`refinalize_sound_false`). `HasTypeB` is `HasType` plus those
rules:

* a node with an unreachable-typed operand may be typed `unreachable` (`…U`
  rules); an `if` with an unreachable condition is annotated `unreachable`
  whatever its arms;
* a branch value may be unreachable whatever the label carries, and branch
  targets only need a label type *above* the carried type (`br`, `switch`), so
  that `br_table` targets need not agree when the value is unreachable.
-/

mutual
/-- Binaryen's validator typing of layer N (with unreachable propagation). -/
inductive HasTypeB (Γ : NEnv) : List (Name × NTy) → NExpr → NTy → Prop where
  | sub {Λ e a b} : HasTypeB Γ Λ e a → NTy.Sub a b → HasTypeB Γ Λ e b
  | const {Λ} (c : Lit) : HasTypeB Γ Λ (.const c) (.val c.ty)
  | localGet {Λ i t} : Γ.locals[i]? = some t → HasTypeB Γ Λ (.localGet i) (.val t)
  | localSet {Λ i v t} : Γ.locals[i]? = some t → HasTypeB Γ Λ v (.val t) →
      HasTypeB Γ Λ (.localSet i v false) .none
  | localTee {Λ i v t} : Γ.locals[i]? = some t → HasTypeB Γ Λ v (.val t) →
      HasTypeB Γ Λ (.localSet i v true) (.val t)
  | localSetU {Λ i v tee t} : Γ.locals[i]? = some t → HasTypeB Γ Λ v .unreachable →
      HasTypeB Γ Λ (.localSet i v tee) .unreachable
  | globalGet {Λ g t} : Γ.globals.lookup g = some t → HasTypeB Γ Λ (.globalGet g) (.val t)
  | globalSet {Λ g v t} : Γ.globals.lookup g = some t → HasTypeB Γ Λ v (.val t) →
      HasTypeB Γ Λ (.globalSet g v) .none
  | globalSetU {Λ g v t} : Γ.globals.lookup g = some t → HasTypeB Γ Λ v .unreachable →
      HasTypeB Γ Λ (.globalSet g v) .unreachable
  | unary {Λ op e} : HasTypeB Γ Λ e (.val op.argTy) →
      HasTypeB Γ Λ (.unary op e) (.val op.resTy)
  | unaryU {Λ op e} : HasTypeB Γ Λ e .unreachable → HasTypeB Γ Λ (.unary op e) .unreachable
  | binary {Λ op a b} : HasTypeB Γ Λ a (.val op.argTy) → HasTypeB Γ Λ b (.val op.argTy) →
      HasTypeB Γ Λ (.binary op a b) (.val op.resTy)
  | binaryUL {Λ op a b} : HasTypeB Γ Λ a .unreachable → HasTypeB Γ Λ b (.val op.argTy) →
      HasTypeB Γ Λ (.binary op a b) .unreachable
  | binaryUR {Λ op a b} : HasTypeB Γ Λ a (.val op.argTy) → HasTypeB Γ Λ b .unreachable →
      HasTypeB Γ Λ (.binary op a b) .unreachable
  | select {Λ a b c t} : HasTypeB Γ Λ a (.val t) → HasTypeB Γ Λ b (.val t) →
      HasTypeB Γ Λ c (.val .i32) → HasTypeB Γ Λ (.select a b c) (.val t)
  | selectUA {Λ a b c t} : HasTypeB Γ Λ a .unreachable → HasTypeB Γ Λ b (.val t) →
      HasTypeB Γ Λ c (.val .i32) → HasTypeB Γ Λ (.select a b c) .unreachable
  | selectUB {Λ a b c t} : HasTypeB Γ Λ a (.val t) → HasTypeB Γ Λ b .unreachable →
      HasTypeB Γ Λ c (.val .i32) → HasTypeB Γ Λ (.select a b c) .unreachable
  | selectUC {Λ a b c t} : HasTypeB Γ Λ a (.val t) → HasTypeB Γ Λ b (.val t) →
      HasTypeB Γ Λ c .unreachable → HasTypeB Γ Λ (.select a b c) .unreachable
  | drop {Λ e t} : HasTypeB Γ Λ e (.val t) → HasTypeB Γ Λ (.drop e) .none
  | dropU {Λ e} : HasTypeB Γ Λ e .unreachable → HasTypeB Γ Λ (.drop e) .unreachable
  | nop {Λ} : HasTypeB Γ Λ .nop .none
  | unreachable {Λ} : HasTypeB Γ Λ .unreachable .unreachable
  | returnNone {Λ} : Γ.results = [] → HasTypeB Γ Λ (.return_ none) .unreachable
  | returnSome {Λ v t} : Γ.results = [t] → HasTypeB Γ Λ v (.val t) →
      HasTypeB Γ Λ (.return_ (some v)) .unreachable
  | br {Λ l v vt τ} : Λ.lookup l = some τ → NTy.Sub vt τ → HasTypeOptB Γ Λ v vt →
      HasTypeB Γ Λ (.br l v none) .unreachable
  | brIf {Λ l v c vt} : Λ.lookup l = some vt → HasTypeOptB Γ Λ v vt →
      HasTypeB Γ Λ c (.val .i32) → HasTypeB Γ Λ (.br l v (some c)) vt
  | brIfUV {Λ l v c τ} : Λ.lookup l = some τ → HasTypeOptB Γ Λ v .unreachable →
      HasTypeB Γ Λ c (.val .i32) → HasTypeB Γ Λ (.br l v (some c)) .unreachable
  | brIfUC {Λ l v c vt τ} : Λ.lookup l = some τ → NTy.Sub vt τ → HasTypeOptB Γ Λ v vt →
      HasTypeB Γ Λ c .unreachable → HasTypeB Γ Λ (.br l v (some c)) .unreachable
  | switch {Λ ls d v c vt} : (∀ l ∈ d :: ls, ∃ τ, Λ.lookup l = some τ ∧ NTy.Sub vt τ) →
      HasTypeOptB Γ Λ v vt → HasTypeB Γ Λ c (.val .i32) →
      HasTypeB Γ Λ (.switch ls d v c) .unreachable
  | call {Λ f args ps rs} : Γ.funcs.lookup f = some (ps, rs) → HasTypesB Γ Λ args ps →
      HasTypeB Γ Λ (.call f args) (resultTy rs)
  | callU {Λ f args a ps rs} : Γ.funcs.lookup f = some (ps, rs) → HasTypesB Γ Λ args ps →
      a ∈ args → HasTypeB Γ Λ a .unreachable → HasTypeB Γ Λ (.call f args) .unreachable
  | block {Λ l body ty} : HasTypeSeqB Γ (pushLabel l ty Λ) body ty →
      HasTypeB Γ Λ (.block l body ty) ty
  | loop {Λ l body ty} : HasTypeB Γ (pushLabel l .none Λ) body ty →
      HasTypeB Γ Λ (.loop l body ty) ty
  | ifElse {Λ c t e ty} : HasTypeB Γ Λ c (.val .i32) → HasTypeB Γ Λ t ty →
      HasTypeB Γ Λ e ty → HasTypeB Γ Λ (.if_ c t (some e) ty) ty
  | ifNoElse {Λ c t} : HasTypeB Γ Λ c (.val .i32) → HasTypeB Γ Λ t .none →
      HasTypeB Γ Λ (.if_ c t none .none) .none
  | ifU {Λ c t e a b} : HasTypeB Γ Λ c .unreachable → HasTypeB Γ Λ t a → HasTypeB Γ Λ e b →
      HasTypeB Γ Λ (.if_ c t (some e) .unreachable) .unreachable
  | ifUNoElse {Λ c t a} : HasTypeB Γ Λ c .unreachable → HasTypeB Γ Λ t a →
      HasTypeB Γ Λ (.if_ c t none .unreachable) .unreachable
/-- An optional branch value of type `vt`: absent (`none`), a value, or unreachable. -/
inductive HasTypeOptB (Γ : NEnv) : List (Name × NTy) → Option NExpr → NTy → Prop where
  | absent {Λ} : HasTypeOptB Γ Λ none .none
  | present {Λ e t} : HasTypeB Γ Λ e (.val t) → HasTypeOptB Γ Λ (some e) (.val t)
  | unreach {Λ e} : HasTypeB Γ Λ e .unreachable → HasTypeOptB Γ Λ (some e) .unreachable
/-- Call operands of the parameter types. -/
inductive HasTypesB (Γ : NEnv) : List (Name × NTy) → List NExpr → List ValType → Prop where
  | nil {Λ} : HasTypesB Γ Λ [] []
  | cons {Λ e es t ts} : HasTypeB Γ Λ e (.val t) → HasTypesB Γ Λ es ts →
      HasTypesB Γ Λ (e :: es) (t :: ts)
/-- A block body, as `HasTypeSeq`. -/
inductive HasTypeSeqB (Γ : NEnv) : List (Name × NTy) → List NExpr → NTy → Prop where
  | nil {Λ ty} : NTy.Sub .none ty → HasTypeSeqB Γ Λ [] ty
  | last {Λ e ty} : HasTypeB Γ Λ e ty → HasTypeSeqB Γ Λ [e] ty
  | cons {Λ e e' es ty} : HasTypeB Γ Λ e .none → HasTypeSeqB Γ Λ (e' :: es) ty →
      HasTypeSeqB Γ Λ (e :: e' :: es) ty
end

/-! ## Proof infrastructure -/

namespace Refin

/-! ### The subtype order -/

theorem sub_refl (a : NTy) : NTy.Sub a a := by cases a <;> simp [NTy.Sub]

theorem sub_unreachable (b : NTy) : NTy.Sub .unreachable b := by simp [NTy.Sub]

theorem eq_of_sub {a b : NTy} (h : NTy.Sub a b) (ha : a ≠ .unreachable) : a = b := by
  cases a <;> simp_all [NTy.Sub]

theorem sub_trans {a b c : NTy} (h₁ : NTy.Sub a b) (h₂ : NTy.Sub b c) : NTy.Sub a c := by
  by_cases ha : a = .unreachable
  · subst ha; exact sub_unreachable c
  · rw [eq_of_sub h₁ ha]; exact h₂

theorem eq_unreachable_of_sub {a : NTy} (h : NTy.Sub a .unreachable) : a = .unreachable := by
  cases a <;> simp_all [NTy.Sub]

theorem lub_bound {a b τ : NTy} (ha : NTy.Sub a τ) (hb : NTy.Sub b τ) :
    ∃ c, NTy.lub a b = some c ∧ NTy.Sub a c ∧ NTy.Sub b c ∧ NTy.Sub c τ := by
  by_cases hau : a = .unreachable
  · subst hau; exact ⟨b, by simp [NTy.lub], sub_unreachable b, sub_refl b, hb⟩
  by_cases hbu : b = .unreachable
  · subst hbu
    refine ⟨a, ?_, sub_refl a, sub_unreachable a, ha⟩
    cases a <;> simp_all [NTy.lub]
  have e1 := eq_of_sub ha hau
  have e2 := eq_of_sub hb hbu
  have e : b = a := e2.trans e1.symm
  rw [e]
  refine ⟨a, ?_, sub_refl a, sub_refl a, ha⟩
  cases a <;> simp_all [NTy.lub]

theorem lubAll_bound {τ : NTy} : ∀ (init : NTy) (xs : List NTy), NTy.Sub init τ →
    (∀ x ∈ xs, NTy.Sub x τ) →
    NTy.Sub (lubAll init xs) τ ∧ NTy.Sub init (lubAll init xs) ∧
      ∀ x ∈ xs, NTy.Sub x (lubAll init xs)
  | init, [], h, _ => ⟨by simpa [lubAll] using h, by simpa [lubAll] using sub_refl init,
      by simp⟩
  | init, x :: xs, h, hxs => by
    obtain ⟨c, hc, h1, h2, h3⟩ := lub_bound h (hxs x (by simp))
    have ih := lubAll_bound c xs h3 (fun y hy => hxs y (by simp [hy]))
    have e : lubAll init (x :: xs) = lubAll c xs := by simp [lubAll, hc]
    rw [e]
    refine ⟨ih.1, sub_trans h1 ih.2.1, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact sub_trans h2 ih.2.1
    · exact ih.2.2 y hy

/-- The block type `refinE` computes from the last child's type and the types
carried to the label. -/
def blockTy (last : NTy) (mine : List NTy) : NTy :=
  if mine.isEmpty then last else lubAll last mine

theorem blockTy_bound {last τ : NTy} {mine : List NTy} (hl : NTy.Sub last τ)
    (hm : ∀ x ∈ mine, NTy.Sub x τ) :
    NTy.Sub (blockTy last mine) τ ∧ NTy.Sub last (blockTy last mine) ∧
      ∀ x ∈ mine, NTy.Sub x (blockTy last mine) := by
  unfold blockTy
  split
  · rename_i he
    have : mine = [] := List.isEmpty_iff.1 he
    subst this
    exact ⟨hl, sub_refl _, by simp⟩
  · exact lubAll_bound last mine hl hm

theorem unless_sub (ops : List NTy) (t : NTy) : NTy.Sub (unlessUnreachable ops t) t := by
  unfold unlessUnreachable
  split
  · exact sub_unreachable t
  · exact sub_refl t

theorem unless_of_mem {ops : List NTy} {t : NTy} (h : NTy.unreachable ∈ ops) :
    unlessUnreachable ops t = .unreachable := by
  simp [unlessUnreachable, h]

theorem unless_of_not_mem {ops : List NTy} {t : NTy} (h : NTy.unreachable ∉ ops) :
    unlessUnreachable ops t = t := by
  simp [unlessUnreachable, h]

/-! ### Free branches -/

/-- Every free branch targets a label of `Λ` whose type is above the carried type. -/
def BrsOk (Λ : List (Name × NTy)) (brs : Brs) : Prop :=
  ∀ p ∈ brs, ∃ τ, Λ.lookup p.1 = some τ ∧ NTy.Sub p.2 τ

theorem brsOk_nil (Λ : List (Name × NTy)) : BrsOk Λ [] := by simp [BrsOk]

theorem brsOk_append {Λ : List (Name × NTy)} {a b : Brs} :
    BrsOk Λ (a ++ b) ↔ BrsOk Λ a ∧ BrsOk Λ b := by
  simp only [BrsOk, List.mem_append]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h₁, h₂⟩ p (hp | hp)
    · exact h₁ p hp
    · exact h₂ p hp

theorem brsOk_cons {Λ : List (Name × NTy)} {p : Name × NTy} {b : Brs} :
    BrsOk Λ (p :: b) ↔ (∃ τ, Λ.lookup p.1 = some τ ∧ NTy.Sub p.2 τ) ∧ BrsOk Λ b := by
  simp [BrsOk]

theorem lookup_push_self (n : Name) (τ : NTy) (Λ : List (Name × NTy)) :
    (pushLabel (some n) τ Λ).lookup n = some τ := by
  simp [pushLabel]

theorem lookup_push_ne {n m : Name} (h : m ≠ n) (τ : NTy) (Λ : List (Name × NTy)) :
    (pushLabel (some n) τ Λ).lookup m = Λ.lookup m := by
  have hb : (m == n) = false := by simpa using h
  simp [pushLabel, List.lookup_cons, hb]

theorem closeScope_split {l : Option Name} {τ : NTy} {Λ : List (Name × NTy)} {brs : Brs}
    (h : BrsOk (pushLabel l τ Λ) brs) :
    (∀ m ∈ (closeScope l brs).1, NTy.Sub m τ) ∧ BrsOk Λ (closeScope l brs).2 := by
  cases l with
  | none => exact ⟨by simp [closeScope], by simpa [closeScope, pushLabel] using h⟩
  | some n =>
    constructor
    · intro m hm
      simp only [closeScope, List.mem_map, List.mem_filter] at hm
      obtain ⟨p, ⟨hp, hpn⟩, rfl⟩ := hm
      obtain ⟨τ', hl, hs⟩ := h p hp
      have hpn' : p.1 = n := by simpa using hpn
      rw [hpn', lookup_push_self] at hl
      cases hl
      exact hs
    · intro p hp
      simp only [closeScope, List.mem_filter] at hp
      obtain ⟨hp, hpn⟩ := hp
      obtain ⟨τ', hl, hs⟩ := h p hp
      have hpn' : p.1 ≠ n := by simpa using hpn
      rw [lookup_push_ne hpn'] at hl
      exact ⟨τ', hl, hs⟩

theorem closeScope_join {l : Option Name} {τ : NTy} {Λ : List (Name × NTy)} {brs : Brs}
    (hm : ∀ m ∈ (closeScope l brs).1, NTy.Sub m τ) (hr : BrsOk Λ (closeScope l brs).2) :
    BrsOk (pushLabel l τ Λ) brs := by
  cases l with
  | none => simpa [closeScope, pushLabel] using hr
  | some n =>
    intro p hp
    by_cases hpn : p.1 = n
    · refine ⟨τ, by rw [hpn, lookup_push_self], hm p.2 ?_⟩
      simp only [closeScope, List.mem_map, List.mem_filter]
      exact ⟨p, ⟨hp, by simp [hpn]⟩, rfl⟩
    · obtain ⟨τ', hl, hs⟩ := hr p (by simp [closeScope, hp, hpn])
      exact ⟨τ', by rw [lookup_push_ne hpn]; exact hl, hs⟩

/-! ### Equations of `refinE` -/

theorem refinL_nil (Γ : NEnv) : refinL Γ [] = ([], [], []) := by simp [refinL]

theorem refinL_cons (Γ : NEnv) (e : NExpr) (es : List NExpr) :
    refinL Γ (e :: es) = ((refinE Γ e).1 :: (refinL Γ es).1,
      (refinE Γ e).2.1 :: (refinL Γ es).2.1, (refinE Γ e).2.2 ++ (refinL Γ es).2.2) := by
  simp [refinL]

theorem refinO_none (Γ : NEnv) : refinO Γ none = none := by simp [refinO]

theorem refinO_some (Γ : NEnv) (e : NExpr) : refinO Γ (some e) = some (refinE Γ e) := by
  simp [refinO]

theorem refinE_block (Γ : NEnv) (l : Option Name) (body : List NExpr) (ty : NTy) :
    refinE Γ (.block l body ty) =
      (.block l (refinL Γ body).1
        (blockTy (((refinL Γ body).2.1.getLast?).getD .none) (closeScope l (refinL Γ body).2.2).1),
        blockTy (((refinL Γ body).2.1.getLast?).getD .none) (closeScope l (refinL Γ body).2.2).1,
        (closeScope l (refinL Γ body).2.2).2) := by
  simp only [refinE, blockTy]

/-! ### Annotation erasure -/

mutual
/-- Erase every annotation. -/
def stripAnn : NExpr → NExpr
  | .block l body _ => .block l (stripAnnL body) .none
  | .loop l body _ => .loop l (stripAnn body) .none
  | .if_ c t e _ => .if_ (stripAnn c) (stripAnn t) (stripAnnO e) .none
  | .br l v c => .br l (stripAnnO v) (stripAnnO c)
  | .switch ls d v c => .switch ls d (stripAnnO v) (stripAnn c)
  | .call f args => .call f (stripAnnL args)
  | .localGet i => .localGet i
  | .localSet i v tee => .localSet i (stripAnn v) tee
  | .globalGet g => .globalGet g
  | .globalSet g v => .globalSet g (stripAnn v)
  | .const c => .const c
  | .unary op e => .unary op (stripAnn e)
  | .binary op a b => .binary op (stripAnn a) (stripAnn b)
  | .select a b c => .select (stripAnn a) (stripAnn b) (stripAnn c)
  | .drop e => .drop (stripAnn e)
  | .return_ v => .return_ (stripAnnO v)
  | .nop => .nop
  | .unreachable => .unreachable
/-- `stripAnn` on a list. -/
def stripAnnL : List NExpr → List NExpr
  | [] => []
  | e :: es => stripAnn e :: stripAnnL es
/-- `stripAnn` on an optional child. -/
def stripAnnO : Option NExpr → Option NExpr
  | none => none
  | some e => some (stripAnn e)
end

theorem stripAnnO_isSome (v : Option NExpr) : (stripAnnO v).isSome = v.isSome := by
  cases v <;> rfl

mutual
theorem refinE_stripAnn (Γ : NEnv) : ∀ e : NExpr, refinE Γ (stripAnn e) = refinE Γ e
  | .block l body _ => by simp only [stripAnn, refinE, refinL_stripAnnL Γ body]
  | .loop l body _ => by simp only [stripAnn, refinE, refinE_stripAnn Γ body]
  | .if_ c t e _ => by
    simp only [stripAnn, refinE, refinE_stripAnn Γ c, refinE_stripAnn Γ t, refinO_stripAnnO Γ e]
  | .br l v c => by
    simp only [stripAnn, refinE, refinO_stripAnnO Γ v, refinO_stripAnnO Γ c, stripAnnO_isSome]
  | .switch ls d v c => by
    simp only [stripAnn, refinE, refinO_stripAnnO Γ v, refinE_stripAnn Γ c]
  | .call f args => by simp only [stripAnn, refinE, refinL_stripAnnL Γ args]
  | .localGet i => by simp only [stripAnn]
  | .localSet i v tee => by simp only [stripAnn, refinE, refinE_stripAnn Γ v]
  | .globalGet g => by simp only [stripAnn]
  | .globalSet g v => by simp only [stripAnn, refinE, refinE_stripAnn Γ v]
  | .const c => by simp only [stripAnn]
  | .unary op e => by simp only [stripAnn, refinE, refinE_stripAnn Γ e]
  | .binary op a b => by simp only [stripAnn, refinE, refinE_stripAnn Γ a, refinE_stripAnn Γ b]
  | .select a b c => by
    simp only [stripAnn, refinE, refinE_stripAnn Γ a, refinE_stripAnn Γ b, refinE_stripAnn Γ c]
  | .drop e => by simp only [stripAnn, refinE, refinE_stripAnn Γ e]
  | .return_ v => by simp only [stripAnn, refinE, refinO_stripAnnO Γ v]
  | .nop => by simp only [stripAnn]
  | .unreachable => by simp only [stripAnn]
theorem refinL_stripAnnL (Γ : NEnv) : ∀ es : List NExpr, refinL Γ (stripAnnL es) = refinL Γ es
  | [] => by simp only [stripAnnL]
  | e :: es => by simp only [stripAnnL, refinL, refinE_stripAnn Γ e, refinL_stripAnnL Γ es]
theorem refinO_stripAnnO (Γ : NEnv) : ∀ v : Option NExpr, refinO Γ (stripAnnO v) = refinO Γ v
  | none => by simp only [stripAnnO]
  | some e => by simp only [stripAnnO, refinO, refinE_stripAnn Γ e]
end

mutual
theorem stripAnn_refinE (Γ : NEnv) : ∀ e : NExpr, stripAnn (refinE Γ e).1 = stripAnn e
  | .block l body _ => by simp only [refinE, stripAnn, stripAnnL_refinL Γ body]
  | .loop l body _ => by simp only [refinE, stripAnn, stripAnn_refinE Γ body]
  | .if_ c t e _ => by
    simp only [refinE, stripAnn, stripAnn_refinE Γ c, stripAnn_refinE Γ t, stripAnnO_refinO Γ e]
  | .br l v c => by simp only [refinE, stripAnn, stripAnnO_refinO Γ v, stripAnnO_refinO Γ c]
  | .switch ls d v c => by
    simp only [refinE, stripAnn, stripAnnO_refinO Γ v, stripAnn_refinE Γ c]
  | .call f args => by simp only [refinE, stripAnn, stripAnnL_refinL Γ args]
  | .localGet i => by simp only [refinE, stripAnn]
  | .localSet i v tee => by simp only [refinE, stripAnn, stripAnn_refinE Γ v]
  | .globalGet g => by simp only [refinE, stripAnn]
  | .globalSet g v => by simp only [refinE, stripAnn, stripAnn_refinE Γ v]
  | .const c => by simp only [refinE, stripAnn]
  | .unary op e => by simp only [refinE, stripAnn, stripAnn_refinE Γ e]
  | .binary op a b => by simp only [refinE, stripAnn, stripAnn_refinE Γ a, stripAnn_refinE Γ b]
  | .select a b c => by
    simp only [refinE, stripAnn, stripAnn_refinE Γ a, stripAnn_refinE Γ b, stripAnn_refinE Γ c]
  | .drop e => by simp only [refinE, stripAnn, stripAnn_refinE Γ e]
  | .return_ v => by simp only [refinE, stripAnn, stripAnnO_refinO Γ v]
  | .nop => by simp only [refinE, stripAnn]
  | .unreachable => by simp only [refinE, stripAnn]
theorem stripAnnL_refinL (Γ : NEnv) :
    ∀ es : List NExpr, stripAnnL (refinL Γ es).1 = stripAnnL es
  | [] => by simp only [refinL, stripAnnL]
  | e :: es => by simp only [refinL, stripAnnL, stripAnn_refinE Γ e, stripAnnL_refinL Γ es]
theorem stripAnnO_refinO (Γ : NEnv) :
    ∀ v : Option NExpr, stripAnnO ((refinO Γ v).map (·.1)) = stripAnnO v
  | none => by simp only [refinO, Option.map, stripAnnO]
  | some e => by simp only [refinO, Option.map, stripAnnO, stripAnn_refinE Γ e]
end

mutual
theorem freeLabels_stripAnn : ∀ e : NExpr, (stripAnn e).freeLabels = e.freeLabels
  | .block l body _ => by simp only [stripAnn, NExpr.freeLabels, freeLabelsList_stripAnnL body]
  | .loop l body _ => by simp only [stripAnn, NExpr.freeLabels, freeLabels_stripAnn body]
  | .if_ c t e _ => by
    simp only [stripAnn, NExpr.freeLabels, freeLabels_stripAnn c, freeLabels_stripAnn t,
      freeLabelsOpt_stripAnnO e]
  | .br l v c => by
    simp only [stripAnn, NExpr.freeLabels, freeLabelsOpt_stripAnnO v, freeLabelsOpt_stripAnnO c]
  | .switch ls d v c => by
    simp only [stripAnn, NExpr.freeLabels, freeLabelsOpt_stripAnnO v, freeLabels_stripAnn c]
  | .call f args => by simp only [stripAnn, NExpr.freeLabels, freeLabelsList_stripAnnL args]
  | .localGet i => by simp only [stripAnn]
  | .localSet i v tee => by simp only [stripAnn, NExpr.freeLabels, freeLabels_stripAnn v]
  | .globalGet g => by simp only [stripAnn]
  | .globalSet g v => by simp only [stripAnn, NExpr.freeLabels, freeLabels_stripAnn v]
  | .const c => by simp only [stripAnn]
  | .unary op e => by simp only [stripAnn, NExpr.freeLabels, freeLabels_stripAnn e]
  | .binary op a b => by
    simp only [stripAnn, NExpr.freeLabels, freeLabels_stripAnn a, freeLabels_stripAnn b]
  | .select a b c => by
    simp only [stripAnn, NExpr.freeLabels, freeLabels_stripAnn a, freeLabels_stripAnn b,
      freeLabels_stripAnn c]
  | .drop e => by simp only [stripAnn, NExpr.freeLabels, freeLabels_stripAnn e]
  | .return_ v => by simp only [stripAnn, NExpr.freeLabels, freeLabelsOpt_stripAnnO v]
  | .nop => by simp only [stripAnn]
  | .unreachable => by simp only [stripAnn]
theorem freeLabelsList_stripAnnL :
    ∀ es : List NExpr, NExpr.freeLabelsList (stripAnnL es) = NExpr.freeLabelsList es
  | [] => by simp only [stripAnnL]
  | e :: es => by
    simp only [stripAnnL, NExpr.freeLabelsList, freeLabels_stripAnn e,
      freeLabelsList_stripAnnL es]
theorem freeLabelsOpt_stripAnnO :
    ∀ v : Option NExpr, NExpr.freeLabelsOpt (stripAnnO v) = NExpr.freeLabelsOpt v
  | none => by simp only [stripAnnO]
  | some e => by simp only [stripAnnO, NExpr.freeLabelsOpt, freeLabels_stripAnn e]
end

/-! ### Operand lists of `unlessUnreachable` -/

theorem unless_cons_u (l : List NTy) (t : NTy) :
    unlessUnreachable (.unreachable :: l) t = .unreachable := by
  simp [unlessUnreachable]

theorem unless_cons_ne {a : NTy} (ha : a ≠ .unreachable) (l : List NTy) (t : NTy) :
    unlessUnreachable (a :: l) t = unlessUnreachable l t := by
  simp [unlessUnreachable, Ne.symm ha]

theorem unless_nil (t : NTy) : unlessUnreachable [] t = t := by
  simp [unlessUnreachable]

/-! ### Principality -/

mutual
theorem principal_E {Γ : NEnv} {Λ : List (Name × NTy)} {e : NExpr} {t : NTy}
    (h : HasType Γ Λ e t) : NTy.Sub (refinE Γ e).2.1 t ∧ BrsOk Λ (refinE Γ e).2.2 :=
  match h with
  | .sub h hs => ⟨sub_trans (principal_E h).1 hs, (principal_E h).2⟩
  | .const _ => ⟨sub_refl _, brsOk_nil _⟩
  | .localGet (i := i) hi => by
    refine ⟨?_, brsOk_nil _⟩
    show NTy.Sub (((Γ.locals[i]?).map NTy.val).getD .none) _
    rw [hi]; exact sub_refl _
  | .localSet _ hv => ⟨unless_sub _ _, (principal_E hv).2⟩
  | .localTee (i := i) (v := v) (t := t) hi hv => by
    refine ⟨?_, (principal_E hv).2⟩
    show NTy.Sub (unlessUnreachable [(refinE Γ v).2.1] (((Γ.locals[i]?).map NTy.val).getD .none))
      (.val t)
    rw [hi]; exact unless_sub _ _
  | .globalGet (g := g) hg => by
    refine ⟨?_, brsOk_nil _⟩
    show NTy.Sub (((Γ.globals.lookup g).map NTy.val).getD .none) _
    rw [hg]; exact sub_refl _
  | .globalSet _ hv => ⟨unless_sub _ _, (principal_E hv).2⟩
  | .unary hv => ⟨unless_sub _ _, (principal_E hv).2⟩
  | .binary ha hb => ⟨unless_sub _ _, brsOk_append.2 ⟨(principal_E ha).2, (principal_E hb).2⟩⟩
  | .select ha hb hc => ⟨sub_trans (unless_sub _ _) (principal_E ha).1,
      brsOk_append.2 ⟨brsOk_append.2 ⟨(principal_E ha).2, (principal_E hb).2⟩,
        (principal_E hc).2⟩⟩
  | .drop hv => ⟨unless_sub _ _, (principal_E hv).2⟩
  | .nop => ⟨sub_refl _, brsOk_nil _⟩
  | .unreachable => ⟨sub_refl _, brsOk_nil _⟩
  | .returnNone _ => ⟨sub_refl _, brsOk_nil _⟩
  | .returnSome _ hv => ⟨sub_refl _, (principal_E hv).2⟩
  | .br hl hv =>
    ⟨sub_refl _, brsOk_cons.2 ⟨⟨_, hl, (principal_O hv).1⟩,
      brsOk_append.2 ⟨(principal_O hv).2, brsOk_nil _⟩⟩⟩
  | .brIf hl hv hc =>
    ⟨sub_trans (unless_sub _ _) (principal_O hv).1, brsOk_cons.2 ⟨⟨_, hl, (principal_O hv).1⟩,
      brsOk_append.2 ⟨(principal_O hv).2, (principal_E hc).2⟩⟩⟩
  | .switch hls hv hc => by
    refine ⟨sub_refl _, brsOk_append.2 ⟨brsOk_append.2 ⟨?_, (principal_O hv).2⟩,
      (principal_E hc).2⟩⟩
    intro p hp
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hp
    exact ⟨_, hls n hn, (principal_O hv).1⟩
  | .call (f := f) (args := args) (rs := rs) hf hargs => by
    refine ⟨?_, (principal_L hargs).2⟩
    show NTy.Sub (unlessUnreachable (refinL Γ args).2.1
      (resultTy (((Γ.funcs.lookup f).map (·.2)).getD []))) _
    rw [hf]; exact unless_sub _ _
  | .block hs => by
    obtain ⟨h1, h2⟩ := principal_S hs
    obtain ⟨hm, hr⟩ := closeScope_split h2
    rw [refinE_block]
    exact ⟨(blockTy_bound h1 hm).1, hr⟩
  | .loop hb => ⟨(principal_E hb).1, (closeScope_split (principal_E hb).2).2⟩
  | .ifElse (c := c) (t := t) (e := e) hc ht he => by
    obtain ⟨u, hu, -, -, hu'⟩ := lub_bound (principal_E ht).1 (principal_E he).1
    refine ⟨?_, brsOk_append.2 ⟨brsOk_append.2 ⟨(principal_E hc).2, (principal_E ht).2⟩,
      (principal_E he).2⟩⟩
    show NTy.Sub (unlessUnreachable [(refinE Γ c).2.1]
      ((NTy.lub (refinE Γ t).2.1 (refinE Γ e).2.1).getD .none)) _
    rw [hu]; exact sub_trans (unless_sub _ _) hu'
  | .ifNoElse hc ht => ⟨unless_sub _ _,
      brsOk_append.2 ⟨brsOk_append.2 ⟨(principal_E hc).2, (principal_E ht).2⟩, brsOk_nil _⟩⟩
theorem principal_O {Γ : NEnv} {Λ : List (Name × NTy)} {v : Option NExpr} {vt : NTy}
    (h : HasTypeOpt Γ Λ v vt) :
    NTy.Sub (((refinO Γ v).map (·.2.1)).getD .none) vt ∧
      BrsOk Λ (((refinO Γ v).map (·.2.2)).getD []) :=
  match h with
  | .absent => ⟨sub_refl _, brsOk_nil _⟩
  | .present h => principal_E h
theorem principal_L {Γ : NEnv} {Λ : List (Name × NTy)} {args : List NExpr} {ps : List ValType}
    (h : HasTypes Γ Λ args ps) :
    List.Forall₂ (fun a p => NTy.Sub a (.val p)) (refinL Γ args).2.1 ps ∧
      BrsOk Λ (refinL Γ args).2.2 :=
  match h with
  | .nil => ⟨.nil, brsOk_nil _⟩
  | .cons he hes =>
    ⟨.cons (principal_E he).1 (principal_L hes).1,
      brsOk_append.2 ⟨(principal_E he).2, (principal_L hes).2⟩⟩
theorem principal_S {Γ : NEnv} {Λ : List (Name × NTy)} {body : List NExpr} {ty : NTy}
    (h : HasTypeSeq Γ Λ body ty) :
    NTy.Sub (((refinL Γ body).2.1.getLast?).getD .none) ty ∧ BrsOk Λ (refinL Γ body).2.2 :=
  match h with
  | .nil hs => ⟨hs, brsOk_nil _⟩
  | .last he => ⟨(principal_E he).1, brsOk_append.2 ⟨(principal_E he).2, brsOk_nil _⟩⟩
  | .cons he hrest => by
    obtain ⟨h1, h2⟩ := principal_S hrest
    refine ⟨?_, brsOk_append.2 ⟨(principal_E he).2, h2⟩⟩
    simp only [refinL_cons, List.getLast?_cons_cons] at h1 ⊢
    exact h1
end

/-! ### Soundness against `HasTypeB` -/

mutual
theorem sound_E {Γ : NEnv} {Λ : List (Name × NTy)} {e : NExpr} {t : NTy}
    (h : HasType Γ Λ e t) : ∀ Λ', BrsOk Λ' (refinE Γ e).2.2 →
      HasTypeB Γ Λ' (refinE Γ e).1 (refinE Γ e).2.1 :=
  match h with
  | .sub h _ => sound_E h
  | .const c => fun _ _ => .const c
  | .localGet (i := i) hi => fun Λ' _ => by
    show HasTypeB Γ Λ' (.localGet i) (((Γ.locals[i]?).map NTy.val).getD .none)
    rw [hi]; exact .localGet hi
  | .localSet (i := i) (v := v) hi hv => fun Λ' hB => by
    have ih := sound_E hv Λ' hB
    have hs := (principal_E hv).1
    show HasTypeB Γ Λ' (.localSet i (refinE Γ v).1 false)
      (unlessUnreachable [(refinE Γ v).2.1] .none)
    by_cases hu : (refinE Γ v).2.1 = .unreachable
    · rw [hu, unless_cons_u]; rw [hu] at ih; exact .localSetU hi ih
    · rw [unless_cons_ne hu, unless_nil]; rw [eq_of_sub hs hu] at ih; exact .localSet hi ih
  | .localTee (i := i) (v := v) hi hv => fun Λ' hB => by
    have ih := sound_E hv Λ' hB
    have hs := (principal_E hv).1
    show HasTypeB Γ Λ' (.localSet i (refinE Γ v).1 true)
      (unlessUnreachable [(refinE Γ v).2.1] (((Γ.locals[i]?).map NTy.val).getD .none))
    rw [hi]
    by_cases hu : (refinE Γ v).2.1 = .unreachable
    · rw [hu, unless_cons_u]; rw [hu] at ih; exact .localSetU hi ih
    · rw [unless_cons_ne hu, unless_nil]; rw [eq_of_sub hs hu] at ih; exact .localTee hi ih
  | .globalGet (g := g) hg => fun Λ' _ => by
    show HasTypeB Γ Λ' (.globalGet g) (((Γ.globals.lookup g).map NTy.val).getD .none)
    rw [hg]; exact .globalGet hg
  | .globalSet (g := g) (v := v) hg hv => fun Λ' hB => by
    have ih := sound_E hv Λ' hB
    have hs := (principal_E hv).1
    show HasTypeB Γ Λ' (.globalSet g (refinE Γ v).1) (unlessUnreachable [(refinE Γ v).2.1] .none)
    by_cases hu : (refinE Γ v).2.1 = .unreachable
    · rw [hu, unless_cons_u]; rw [hu] at ih; exact .globalSetU hg ih
    · rw [unless_cons_ne hu, unless_nil]; rw [eq_of_sub hs hu] at ih; exact .globalSet hg ih
  | .unary (op := op) (e := e) hv => fun Λ' hB => by
    have ih := sound_E hv Λ' hB
    have hs := (principal_E hv).1
    show HasTypeB Γ Λ' (.unary op (refinE Γ e).1)
      (unlessUnreachable [(refinE Γ e).2.1] (.val op.resTy))
    by_cases hu : (refinE Γ e).2.1 = .unreachable
    · rw [hu, unless_cons_u]; rw [hu] at ih; exact .unaryU ih
    · rw [unless_cons_ne hu, unless_nil]; rw [eq_of_sub hs hu] at ih; exact .unary ih
  | .binary (op := op) (a := a) (b := b) ha hb => fun Λ' hB => by
    have hB' := brsOk_append.1 hB
    have iha := sound_E ha Λ' hB'.1
    have ihb := sound_E hb Λ' hB'.2
    have hsa := (principal_E ha).1
    have hsb := (principal_E hb).1
    show HasTypeB Γ Λ' (.binary op (refinE Γ a).1 (refinE Γ b).1)
      (unlessUnreachable [(refinE Γ a).2.1, (refinE Γ b).2.1] (.val op.resTy))
    by_cases hua : (refinE Γ a).2.1 = .unreachable
    · rw [hua, unless_cons_u]; rw [hua] at iha; exact .binaryUL iha (.sub ihb hsb)
    · rw [unless_cons_ne hua]
      by_cases hub : (refinE Γ b).2.1 = .unreachable
      · rw [hub, unless_cons_u]; rw [hub] at ihb; exact .binaryUR (.sub iha hsa) ihb
      · rw [unless_cons_ne hub, unless_nil]; exact .binary (.sub iha hsa) (.sub ihb hsb)
  | .select (a := a) (b := b) (c := c) ha hb hc => fun Λ' hB => by
    have hB' := brsOk_append.1 hB
    have hB'' := brsOk_append.1 hB'.1
    have iha := sound_E ha Λ' hB''.1
    have ihb := sound_E hb Λ' hB''.2
    have ihc := sound_E hc Λ' hB'.2
    have hsa := (principal_E ha).1
    have hsb := (principal_E hb).1
    have hsc := (principal_E hc).1
    show HasTypeB Γ Λ' (.select (refinE Γ a).1 (refinE Γ b).1 (refinE Γ c).1)
      (unlessUnreachable [(refinE Γ a).2.1, (refinE Γ b).2.1, (refinE Γ c).2.1] (refinE Γ a).2.1)
    by_cases hua : (refinE Γ a).2.1 = .unreachable
    · rw [hua, unless_cons_u]; rw [hua] at iha; exact .selectUA iha (.sub ihb hsb) (.sub ihc hsc)
    · rw [unless_cons_ne hua]
      rw [eq_of_sub hsa hua] at iha ⊢
      by_cases hub : (refinE Γ b).2.1 = .unreachable
      · rw [hub, unless_cons_u]; rw [hub] at ihb; exact .selectUB iha ihb (.sub ihc hsc)
      · rw [unless_cons_ne hub]
        by_cases huc : (refinE Γ c).2.1 = .unreachable
        · rw [huc, unless_cons_u]; rw [huc] at ihc; exact .selectUC iha (.sub ihb hsb) ihc
        · rw [unless_cons_ne huc, unless_nil]; exact .select iha (.sub ihb hsb) (.sub ihc hsc)
  | .drop (e := e) hv => fun Λ' hB => by
    have ih := sound_E hv Λ' hB
    have hs := (principal_E hv).1
    show HasTypeB Γ Λ' (.drop (refinE Γ e).1) (unlessUnreachable [(refinE Γ e).2.1] .none)
    by_cases hu : (refinE Γ e).2.1 = .unreachable
    · rw [hu, unless_cons_u]; rw [hu] at ih; exact .dropU ih
    · rw [unless_cons_ne hu, unless_nil]; rw [eq_of_sub hs hu] at ih; exact .drop ih
  | .nop => fun _ _ => .nop
  | .unreachable => fun _ _ => .unreachable
  | .returnNone hr => fun _ _ => .returnNone hr
  | .returnSome hr hv => fun Λ' hB => .returnSome hr (.sub (sound_E hv Λ' hB) (principal_E hv).1)
  | .br hl hv => fun Λ' hB => by
    obtain ⟨⟨τ, hτ, hsub⟩, hB2⟩ := brsOk_cons.1 hB
    exact .br hτ hsub (sound_O hv Λ' (brsOk_append.1 hB2).1)
  | .brIf (l := l) (c := c) _ hv hc => fun Λ' hB => by
    obtain ⟨⟨τ, hτ, hsub⟩, hB2⟩ := brsOk_cons.1 hB
    have hB3 := brsOk_append.1 hB2
    have ihv := sound_O hv Λ' hB3.1
    have ihc := sound_E hc Λ' hB3.2
    have hsc := (principal_E hc).1
    have hsv := (principal_O hv).1
    cases hv with
    | absent =>
      show HasTypeB Γ Λ' (.br l none (some (refinE Γ c).1))
        (unlessUnreachable [(refinE Γ c).2.1] .none)
      by_cases huc : (refinE Γ c).2.1 = .unreachable
      · rw [huc, unless_cons_u]; rw [huc] at ihc; exact .brIfUC hτ hsub ihv ihc
      · rw [unless_cons_ne huc, unless_nil]
        have hsub' : NTy.Sub .none τ := hsub
        have e : τ = .none := (eq_of_sub hsub' (by simp)).symm
        rw [e] at hτ
        exact .brIf hτ .absent (.sub ihc hsc)
    | @present _ e _ he =>
      show HasTypeB Γ Λ' (.br l (some (refinE Γ e).1) (some (refinE Γ c).1))
        (unlessUnreachable [(refinE Γ e).2.1, (refinE Γ c).2.1] (refinE Γ e).2.1)
      by_cases hue : (refinE Γ e).2.1 = .unreachable
      · have ihv' : HasTypeOptB Γ Λ' (some (refinE Γ e).1) (refinE Γ e).2.1 := ihv
        rw [hue] at ihv' ⊢
        rw [unless_cons_u]
        exact .brIfUV hτ ihv' (.sub ihc hsc)
      · rw [unless_cons_ne hue]
        by_cases huc : (refinE Γ c).2.1 = .unreachable
        · rw [huc, unless_cons_u]; rw [huc] at ihc; exact .brIfUC hτ hsub ihv ihc
        · rw [unless_cons_ne huc, unless_nil]
          have e' : (refinE Γ e).2.1 = τ := eq_of_sub hsub hue
          rw [← e'] at hτ
          exact .brIf hτ ihv (.sub ihc hsc)
  | .switch hls hv hc => fun Λ' hB => by
    have hB1 := brsOk_append.1 hB
    have hB2 := brsOk_append.1 hB1.1
    refine .switch ?_ (sound_O hv Λ' hB2.2) (.sub (sound_E hc Λ' hB1.2) (principal_E hc).1)
    intro n hn
    exact hB2.1 (n, _) (List.mem_map.2 ⟨n, hn, rfl⟩)
  | .call (f := f) (args := args) hf hargs => fun Λ' hB => by
    obtain ⟨hA, hU⟩ := sound_L hargs Λ' hB
    show HasTypeB Γ Λ' (.call f (refinL Γ args).1)
      (unlessUnreachable (refinL Γ args).2.1 (resultTy (((Γ.funcs.lookup f).map (·.2)).getD [])))
    rw [hf]
    by_cases hu : NTy.unreachable ∈ (refinL Γ args).2.1
    · rw [unless_of_mem hu]
      obtain ⟨a, ha, hta⟩ := hU hu
      exact .callU hf hA ha hta
    · rw [unless_of_not_mem hu]; exact .call hf hA
  | .block hs => fun Λ' hB => by
    obtain ⟨h1, h2⟩ := principal_S hs
    obtain ⟨hm, -⟩ := closeScope_split h2
    have hbt := blockTy_bound h1 hm
    rw [refinE_block] at hB ⊢
    exact .block (sound_S hs _ _ (closeScope_join hbt.2.2 hB) hbt.2.1)
  | .loop hb => fun Λ' hB =>
    .loop (sound_E hb _ (closeScope_join (closeScope_split (principal_E hb).2).1 hB))
  | .ifElse (c := c) (t := t) (e := e) hc ht he => fun Λ' hB => by
    have hB1 := brsOk_append.1 hB
    have hB2 := brsOk_append.1 hB1.1
    have ihc := sound_E hc Λ' hB2.1
    have iht := sound_E ht Λ' hB2.2
    have ihe := sound_E he Λ' hB1.2
    have hsc := (principal_E hc).1
    obtain ⟨u, hu, htu, heu, -⟩ := lub_bound (principal_E ht).1 (principal_E he).1
    show HasTypeB Γ Λ' (.if_ (refinE Γ c).1 (refinE Γ t).1 (some (refinE Γ e).1)
      (unlessUnreachable [(refinE Γ c).2.1]
        ((NTy.lub (refinE Γ t).2.1 (refinE Γ e).2.1).getD .none)))
      (unlessUnreachable [(refinE Γ c).2.1]
        ((NTy.lub (refinE Γ t).2.1 (refinE Γ e).2.1).getD .none))
    rw [hu]
    by_cases huc : (refinE Γ c).2.1 = .unreachable
    · rw [huc, unless_cons_u]; rw [huc] at ihc; exact .ifU ihc iht ihe
    · rw [unless_cons_ne huc, unless_nil]
      exact .ifElse (.sub ihc hsc) (.sub iht htu) (.sub ihe heu)
  | .ifNoElse (c := c) (t := t) hc ht => fun Λ' hB => by
    have hB1 := brsOk_append.1 hB
    have hB2 := brsOk_append.1 hB1.1
    have ihc := sound_E hc Λ' hB2.1
    have iht := sound_E ht Λ' hB2.2
    have hsc := (principal_E hc).1
    have hst := (principal_E ht).1
    show HasTypeB Γ Λ' (.if_ (refinE Γ c).1 (refinE Γ t).1 none
      (unlessUnreachable [(refinE Γ c).2.1] .none))
      (unlessUnreachable [(refinE Γ c).2.1] .none)
    by_cases huc : (refinE Γ c).2.1 = .unreachable
    · rw [huc, unless_cons_u]; rw [huc] at ihc; exact .ifUNoElse ihc iht
    · rw [unless_cons_ne huc, unless_nil]; exact .ifNoElse (.sub ihc hsc) (.sub iht hst)
theorem sound_O {Γ : NEnv} {Λ : List (Name × NTy)} {v : Option NExpr} {vt : NTy}
    (h : HasTypeOpt Γ Λ v vt) : ∀ Λ', BrsOk Λ' (((refinO Γ v).map (·.2.2)).getD []) →
      HasTypeOptB Γ Λ' ((refinO Γ v).map (·.1)) (((refinO Γ v).map (·.2.1)).getD .none) :=
  match h with
  | .absent => fun _ _ => .absent
  | .present (e := e) he => fun Λ' hB => by
    have ih := sound_E he Λ' hB
    have hs := (principal_E he).1
    show HasTypeOptB Γ Λ' (some (refinE Γ e).1) (refinE Γ e).2.1
    by_cases hu : (refinE Γ e).2.1 = .unreachable
    · rw [hu] at ih ⊢; exact .unreach ih
    · rw [eq_of_sub hs hu] at ih ⊢; exact .present ih
theorem sound_L {Γ : NEnv} {Λ : List (Name × NTy)} {args : List NExpr} {ps : List ValType}
    (h : HasTypes Γ Λ args ps) : ∀ Λ', BrsOk Λ' (refinL Γ args).2.2 →
      HasTypesB Γ Λ' (refinL Γ args).1 ps ∧
        (NTy.unreachable ∈ (refinL Γ args).2.1 →
          ∃ a ∈ (refinL Γ args).1, HasTypeB Γ Λ' a .unreachable) :=
  match h with
  | .nil => fun _ _ => ⟨.nil, fun hm => absurd hm (by simp [refinL])⟩
  | .cons (e := e) (es := es) he hes => fun Λ' hB => by
    have hB' := brsOk_append.1 hB
    have ih := sound_E he Λ' hB'.1
    have ihs := sound_L hes Λ' hB'.2
    refine ⟨.cons (.sub ih (principal_E he).1) ihs.1, ?_⟩
    intro hm
    rw [refinL_cons] at hm ⊢
    rcases List.mem_cons.1 hm with h | h
    · exact ⟨(refinE Γ e).1, List.mem_cons_self, h ▸ ih⟩
    · obtain ⟨a, ha, hta⟩ := ihs.2 h
      exact ⟨a, List.mem_cons_of_mem _ ha, hta⟩
theorem sound_S {Γ : NEnv} {Λ : List (Name × NTy)} {body : List NExpr} {ty : NTy}
    (h : HasTypeSeq Γ Λ body ty) : ∀ Λ' τ, BrsOk Λ' (refinL Γ body).2.2 →
      NTy.Sub (((refinL Γ body).2.1.getLast?).getD .none) τ →
      HasTypeSeqB Γ Λ' (refinL Γ body).1 τ :=
  match h with
  | .nil _ => fun _ _ _ hτ => .nil hτ
  | .last he => fun Λ' _ hB hτ => .last (.sub (sound_E he Λ' (brsOk_append.1 hB).1) hτ)
  | .cons (e' := e') (es := es) he hrest => fun Λ' τ hB hτ => by
    have hB' := brsOk_append.1 hB
    have hτ' : NTy.Sub (((refinL Γ (e' :: es)).2.1.getLast?).getD .none) τ := by
      simp only [refinL_cons, List.getLast?_cons_cons] at hτ ⊢
      exact hτ
    exact .cons (.sub (sound_E he Λ' hB'.1) (principal_E he).1) (sound_S hrest Λ' τ hB'.2 hτ')
end

/-! ### `drop` is never typed `unreachable` by `HasType` -/

theorem hasType_drop {Γ : NEnv} {Λ : List (Name × NTy)} {e : NExpr} {t : NTy}
    (h : HasType Γ Λ e t) : ∀ x, e = .drop x → t = .none :=
  match h with
  | .sub h hs => fun x he => by
    have := hasType_drop h x he
    subst this
    exact (eq_of_sub hs (by simp)).symm
  | .drop _ => fun _ _ => rfl
  | .const _ => fun _ he => nomatch he
  | .localGet _ => fun _ he => nomatch he
  | .localSet _ _ => fun _ he => nomatch he
  | .localTee _ _ => fun _ he => nomatch he
  | .globalGet _ => fun _ he => nomatch he
  | .globalSet _ _ => fun _ he => nomatch he
  | .unary _ => fun _ he => nomatch he
  | .binary _ _ => fun _ he => nomatch he
  | .select _ _ _ => fun _ he => nomatch he
  | .nop => fun _ he => nomatch he
  | .unreachable => fun _ he => nomatch he
  | .returnNone _ => fun _ he => nomatch he
  | .returnSome _ _ => fun _ he => nomatch he
  | .br _ _ => fun _ he => nomatch he
  | .brIf _ _ _ => fun _ he => nomatch he
  | .switch _ _ _ => fun _ he => nomatch he
  | .call _ _ => fun _ he => nomatch he
  | .block _ => fun _ he => nomatch he
  | .loop _ => fun _ he => nomatch he
  | .ifElse _ _ _ => fun _ he => nomatch he
  | .ifNoElse _ _ => fun _ he => nomatch he

end Refin

/-! ## `HasTypeB` extends `HasType` -/

mutual
/-- Every `HasType` derivation is a `HasTypeB` derivation. -/
theorem HasType.toB {Γ : NEnv} {Λ : List (Name × NTy)} {e : NExpr} {t : NTy}
    (h : HasType Γ Λ e t) : HasTypeB Γ Λ e t :=
  match h with
  | .sub h hs => .sub (HasType.toB h) hs
  | .const c => .const c
  | .localGet hi => .localGet hi
  | .localSet hi hv => .localSet hi (HasType.toB hv)
  | .localTee hi hv => .localTee hi (HasType.toB hv)
  | .globalGet hg => .globalGet hg
  | .globalSet hg hv => .globalSet hg (HasType.toB hv)
  | .unary hv => .unary (HasType.toB hv)
  | .binary ha hb => .binary (HasType.toB ha) (HasType.toB hb)
  | .select ha hb hc => .select (HasType.toB ha) (HasType.toB hb) (HasType.toB hc)
  | .drop hv => .drop (HasType.toB hv)
  | .nop => .nop
  | .unreachable => .unreachable
  | .returnNone hr => .returnNone hr
  | .returnSome hr hv => .returnSome hr (HasType.toB hv)
  | .br hl hv => .br hl (Refin.sub_refl _) (HasTypeOpt.toB hv)
  | .brIf hl hv hc => .brIf hl (HasTypeOpt.toB hv) (HasType.toB hc)
  | .switch hls hv hc =>
    .switch (fun l hl => ⟨_, hls l hl, Refin.sub_refl _⟩) (HasTypeOpt.toB hv) (HasType.toB hc)
  | .call hf ha => .call hf (HasTypes.toB ha)
  | .block hs => .block (HasTypeSeq.toB hs)
  | .loop hb => .loop (HasType.toB hb)
  | .ifElse hc ht he => .ifElse (HasType.toB hc) (HasType.toB ht) (HasType.toB he)
  | .ifNoElse hc ht => .ifNoElse (HasType.toB hc) (HasType.toB ht)
/-- `HasType.toB` on optional branch values. -/
theorem HasTypeOpt.toB {Γ : NEnv} {Λ : List (Name × NTy)} {v : Option NExpr} {vt : NTy}
    (h : HasTypeOpt Γ Λ v vt) : HasTypeOptB Γ Λ v vt :=
  match h with
  | .absent => .absent
  | .present he => .present (HasType.toB he)
/-- `HasType.toB` on call operands. -/
theorem HasTypes.toB {Γ : NEnv} {Λ : List (Name × NTy)} {args : List NExpr}
    {ps : List ValType} (h : HasTypes Γ Λ args ps) : HasTypesB Γ Λ args ps :=
  match h with
  | .nil => .nil
  | .cons he hes => .cons (HasType.toB he) (HasTypes.toB hes)
/-- `HasType.toB` on block bodies. -/
theorem HasTypeSeq.toB {Γ : NEnv} {Λ : List (Name × NTy)} {body : List NExpr} {ty : NTy}
    (h : HasTypeSeq Γ Λ body ty) : HasTypeSeqB Γ Λ body ty :=
  match h with
  | .nil hs => .nil hs
  | .last he => .last (HasType.toB he)
  | .cons he hrest => .cons (HasType.toB he) (HasTypeSeq.toB hrest)
end

/-- The original soundness statement (conclusion in `HasType`) is **false**:
`(drop (unreachable))` is typed `none`, refinalizes to type `unreachable`, and
`HasType` never types a `drop` at `unreachable`. -/
theorem refinalize_sound_false :
    ¬ ∀ (Γ : NEnv) (Λ : List (Name × NTy)) (e : NExpr) (t : NTy),
      HasType Γ Λ e t → HasType Γ Λ (refinalize Γ e) (refinType Γ e) := by
  intro H
  have h := H ⟨[], [], [], []⟩ [] (.drop .unreachable) .none
    (.drop (t := .i32) (.sub .unreachable (Refin.sub_unreachable _)))
  have h2 : NTy.unreachable = NTy.none := Refin.hasType_drop h .unreachable rfl
  cases h2

/-- **Soundness.** A typable expression is typed, after refinalization, at the
computed type, in Binaryen's validator typing `HasTypeB` (which adds the
unreachable-operand rules `ReFinalize` relies on). -/
-- FLAG(statement-change): conclusion `HasType` → `HasTypeB`. The `HasType` version is
-- false (`refinalize_sound_false`): `HasType` lacks Binaryen's "unreachable operand ⇒
-- unreachable" rules, which `refinE` uses (`(drop (unreachable)) : unreachable`).
theorem refinalize_sound {Γ : NEnv} {Λ : List (Name × NTy)} {e : NExpr} {t : NTy}
    (h : HasType Γ Λ e t) : HasTypeB Γ Λ (refinalize Γ e) (refinType Γ e) :=
  Refin.sound_E h Λ (Refin.principal_E h).2

/-- **Principality.** The computed type is below every type of the input. -/
theorem refinalize_principal {Γ : NEnv} {Λ : List (Name × NTy)} {e : NExpr} {t : NTy}
    (h : HasType Γ Λ e t) : NTy.Sub (refinType Γ e) t :=
  (Refin.principal_E h).1

/-- **Idempotence.** -/
theorem refinalize_idem (Γ : NEnv) (e : NExpr) :
    refinalize Γ (refinalize Γ e) = refinalize Γ e := by
  unfold refinalize
  rw [← Refin.refinE_stripAnn Γ (refinE Γ e).1, Refin.stripAnn_refinE, Refin.refinE_stripAnn]

/-- Refinalization changes only annotations, hence nothing after resolution except
the block types and trailing `unreachable`s that annotations determine; on a
well-typed expression the lowering is equivalent (`Binaryen/Pass/Free.lean`). -/
theorem refinalize_labels (Γ : NEnv) (e : NExpr) :
    (refinalize Γ e).freeLabels = e.freeLabels := by
  unfold refinalize
  rw [← Refin.freeLabels_stripAnn, Refin.stripAnn_refinE, Refin.freeLabels_stripAnn]

end Silmaril.Wasm.Binaryen
