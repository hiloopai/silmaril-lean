module

public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Typing preservation for local rewrites

A local rewrite replaces a sequence `A` of Core instructions by `B` inside some
surrounding code. This file proves that typing is preserved, for **every**
context, well-formed or not (`SeqOk` quantifies over all contexts, and the
splitting lemmas of `Validation/Instructions/Properties.lean` need `Context.Wf`).

The redexes `A` consist of *simple* instructions (integer numeric instructions
and `local.get`), each with a fixed stack effect (`ieff`). A typing derivation of
`L ++ A ++ R` may split `A` across `seq` nodes and wrap parts of it in
subsumption and framing; we summarise a typed simple sequence by `Eff`: its
stack effect, up to framing and *chains* of subtyping steps through valid types
(`SubStar`; transitivity of `Sub` needs `TypeCtx.Ok`, so it is never used).
`split_right`/`split_left` cut a simple suffix/prefix off a derivation exactly
(same instruction type), and `repl` replaces `A` by any `B` typable at every
`Eff`-typing of `A`.
-/

namespace Silmaril.Wasm.Binaryen

open Validation

namespace RTy

/-! ## `Forall₂` helpers -/

theorem f2_length {α β : Type _} {R : α → β → Prop} {a : List α} {b : List β}
    (h : List.Forall₂ R a b) : a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem f2_append {α β : Type _} {R : α → β → Prop} {a a' : List α} {b b' : List β}
    (h : List.Forall₂ R a b) (h' : List.Forall₂ R a' b') :
    List.Forall₂ R (a ++ a') (b ++ b') := by
  induction h with
  | nil => simpa using h'
  | cons hx _ ih => exact List.Forall₂.cons hx ih

theorem f2_split {α β : Type _} {R : α → β → Prop} : ∀ {a a' : List α} {b b' : List β},
    a.length = b.length → List.Forall₂ R (a ++ a') (b ++ b') →
    List.Forall₂ R a b ∧ List.Forall₂ R a' b'
  | [], _, [], _, _, h => ⟨List.Forall₂.nil, by simpa using h⟩
  | [], _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, hl, _ => by simp at hl
  | _ :: a, _, _ :: b, _, hl, h => by
    cases h with
    | cons hxy h =>
      have := f2_split (a := a) (b := b) (by simpa using hl) h
      exact ⟨List.Forall₂.cons hxy this.1, this.2⟩

theorem f2_trans {α : Type _} {R : α → α → Prop} (ht : ∀ x y z, R x y → R y z → R x z) :
    ∀ {a b c : List α}, List.Forall₂ R a b → List.Forall₂ R b c → List.Forall₂ R a c
  | _, _, _, .nil, .nil => List.Forall₂.nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => List.Forall₂.cons (ht _ _ _ h₁ h₂) (f2_trans ht t₁ t₂)

theorem f2_refl {α : Type _} {R : α → α → Prop} (hr : ∀ x, R x x) :
    ∀ (a : List α), List.Forall₂ R a a
  | [] => List.Forall₂.nil
  | x :: a => List.Forall₂.cons (hr x) (f2_refl hr a)

theorem f2_getElem? {α β : Type _} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → ∀ {k : Nat} {y : β}, b[k]? = some y →
      ∃ x, a[k]? = some x ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hxy t, 0, _, h => by simp at h; subst h; exact ⟨_, rfl, hxy⟩
  | _, _, .cons _ t, k + 1, _, h => by simpa using f2_getElem? t (k := k) (by simpa using h)

/-! ## Stack effects -/

/-- A stack effect: the types popped (bottom first) and the types pushed. -/
abbrev StackEff := List CValType × List CValType

/-- Sequential composition of stack effects (type mismatches are ignored: the
typing facts are carried by `Eff`). -/
def comp (a b : StackEff) : StackEff :=
  if b.1.length ≤ a.2.length then (a.1, a.2.take (a.2.length - b.1.length) ++ b.2)
  else (b.1.take (b.1.length - a.2.length) ++ a.1, b.2)

theorem comp_pos {a b : StackEff} (h : b.1.length ≤ a.2.length) :
    comp a b = (a.1, a.2.take (a.2.length - b.1.length) ++ b.2) := by simp [comp, h]

theorem comp_neg {a b : StackEff} (h : ¬ b.1.length ≤ a.2.length) :
    comp a b = (b.1.take (b.1.length - a.2.length) ++ a.1, b.2) := by simp [comp, h]

@[simp] theorem comp_nil_left (a : StackEff) : comp ([], []) a = a := by
  obtain ⟨i, o⟩ := a
  by_cases h : i = []
  · subst h; simp [comp]
  · rw [comp_neg (a := ([], [])) (b := (i, o))
      (by simp only [List.length_nil, Nat.le_zero, List.length_eq_zero_iff]; exact h)]
    simp

@[simp] theorem comp_nil_right (a : StackEff) : comp a ([], []) = a := by
  obtain ⟨i, o⟩ := a
  rw [comp_pos (a := (i, o)) (b := ([], [])) (by simp)]
  simp

theorem comp_assoc (a b c : StackEff) : comp (comp a b) c = comp a (comp b c) := by
  obtain ⟨ia, oa⟩ := a
  obtain ⟨ib, ob⟩ := b
  obtain ⟨ic, oc⟩ := c
  by_cases h1 : ib.length ≤ oa.length
  · have L1 : comp (ia, oa) (ib, ob) = (ia, oa.take (oa.length - ib.length) ++ ob) := comp_pos h1
    rw [L1]
    by_cases h2 : ic.length ≤ ob.length
    · have R1 : comp (ib, ob) (ic, oc) = (ib, ob.take (ob.length - ic.length) ++ oc) :=
        comp_pos h2
      rw [R1]
      have L2 : comp (ia, oa.take (oa.length - ib.length) ++ ob) (ic, oc) =
          (ia, (oa.take (oa.length - ib.length) ++ ob).take
            ((oa.take (oa.length - ib.length) ++ ob).length - ic.length) ++ oc) :=
        comp_pos (by simp only [List.length_append, List.length_take]; omega)
      have R2 : comp (ia, oa) (ib, ob.take (ob.length - ic.length) ++ oc) =
          (ia, oa.take (oa.length - ib.length) ++ (ob.take (ob.length - ic.length) ++ oc)) :=
        comp_pos h1
      rw [L2, R2, ← List.append_assoc]
      congr 2
      rw [List.take_append, List.take_take]
      congr 1
      · congr 1; simp only [List.length_append, List.length_take]; omega
      · congr 1; simp only [List.length_append, List.length_take]; omega
    · have R1 : comp (ib, ob) (ic, oc) = (ic.take (ic.length - ob.length) ++ ib, oc) :=
        comp_neg h2
      rw [R1]
      by_cases h3 : ic.length ≤ (oa.length - ib.length) + ob.length
      · have L2 : comp (ia, oa.take (oa.length - ib.length) ++ ob) (ic, oc) =
            (ia, (oa.take (oa.length - ib.length) ++ ob).take
              ((oa.take (oa.length - ib.length) ++ ob).length - ic.length) ++ oc) :=
          comp_pos (by simp only [List.length_append, List.length_take]; omega)
        have R2 : comp (ia, oa) (ic.take (ic.length - ob.length) ++ ib, oc) =
            (ia, oa.take (oa.length - (ic.take (ic.length - ob.length) ++ ib).length) ++ oc) :=
          comp_pos (by simp only [List.length_append, List.length_take]; omega)
        rw [L2, R2]
        congr 2
        rw [List.take_append_of_le_length (l₁ := oa.take (oa.length - ib.length)) (l₂ := ob)
          (i := (oa.take (oa.length - ib.length) ++ ob).length - ic.length)
          (by simp only [List.length_append, List.length_take]; omega), List.take_take]
        congr 1
        simp only [List.length_append, List.length_take]; omega
      · have L2 : comp (ia, oa.take (oa.length - ib.length) ++ ob) (ic, oc) =
            (ic.take (ic.length - (oa.take (oa.length - ib.length) ++ ob).length) ++ ia, oc) :=
          comp_neg (by simp only [List.length_append, List.length_take]; omega)
        have R2 : comp (ia, oa) (ic.take (ic.length - ob.length) ++ ib, oc) =
            ((ic.take (ic.length - ob.length) ++ ib).take
              ((ic.take (ic.length - ob.length) ++ ib).length - oa.length) ++ ia, oc) :=
          comp_neg (by simp only [List.length_append, List.length_take]; omega)
        rw [L2, R2]
        congr 2
        rw [List.take_append_of_le_length (l₁ := ic.take (ic.length - ob.length)) (l₂ := ib)
          (i := (ic.take (ic.length - ob.length) ++ ib).length - oa.length)
          (by simp only [List.length_append, List.length_take]; omega), List.take_take]
        congr 1
        simp only [List.length_append, List.length_take]; omega
  · have L1 : comp (ia, oa) (ib, ob) = (ib.take (ib.length - oa.length) ++ ia, ob) := comp_neg h1
    rw [L1]
    by_cases h2 : ic.length ≤ ob.length
    · have R1 : comp (ib, ob) (ic, oc) = (ib, ob.take (ob.length - ic.length) ++ oc) :=
        comp_pos h2
      rw [R1]
      have L2 : comp (ib.take (ib.length - oa.length) ++ ia, ob) (ic, oc) =
          (ib.take (ib.length - oa.length) ++ ia, ob.take (ob.length - ic.length) ++ oc) :=
        comp_pos h2
      have R2 : comp (ia, oa) (ib, ob.take (ob.length - ic.length) ++ oc) =
          (ib.take (ib.length - oa.length) ++ ia, ob.take (ob.length - ic.length) ++ oc) :=
        comp_neg h1
      rw [L2, R2]
    · have R1 : comp (ib, ob) (ic, oc) = (ic.take (ic.length - ob.length) ++ ib, oc) :=
        comp_neg h2
      rw [R1]
      have L2 : comp (ib.take (ib.length - oa.length) ++ ia, ob) (ic, oc) =
          (ic.take (ic.length - ob.length) ++ (ib.take (ib.length - oa.length) ++ ia), oc) :=
        comp_neg h2
      have R2 : comp (ia, oa) (ic.take (ic.length - ob.length) ++ ib, oc) =
          ((ic.take (ic.length - ob.length) ++ ib).take
            ((ic.take (ic.length - ob.length) ++ ib).length - oa.length) ++ ia, oc) :=
        comp_neg (by simp only [List.length_append, List.length_take]; omega)
      rw [L2, R2, ← List.append_assoc]
      congr 2
      rw [List.take_append]
      congr 1
      · exact (List.take_of_length_le
          (by simp only [List.length_append, List.length_take]; omega)).symm
      · congr 1; simp only [List.length_append, List.length_take]; omega

/-- The stack effect of a simple instruction; `lts` are the types of the locals. -/
def ieff (lts : List CValType) : Instr → Option StackEff
  | .intConst t _ => some ([], [.num (.int t)])
  | .intUnOp t _ => some ([.num (.int t)], [.num (.int t)])
  | .intBinOp t _ => some ([.num (.int t), .num (.int t)], [.num (.int t)])
  | .intTestOp t _ => some ([.num (.int t)], [Ty.i32])
  | .intRelOp t _ => some ([.num (.int t), .num (.int t)], [Ty.i32])
  | .localGet x => some ([], [(lts[x.toNat]?).getD .botv])
  | _ => none

/-- The stack effect of a sequence of simple instructions. -/
def effList (lts : List CValType) : List Instr → Option StackEff
  | [] => some ([], [])
  | i :: is =>
    match ieff lts i, effList lts is with
    | some a, some b => some (comp a b)
    | _, _ => none

theorem effList_cons {lts : List CValType} {i : Instr} {is : List Instr} {e : StackEff}
    (h : effList lts (i :: is) = some e) :
    ∃ a b, ieff lts i = some a ∧ effList lts is = some b ∧ e = comp a b := by
  simp only [effList] at h
  split at h
  · rename_i a b ha hb
    exact ⟨a, b, ha, hb, (Option.some.inj h).symm⟩
  · cases h

theorem effList_cons' {lts : List CValType} {i : Instr} {is : List Instr} {a b : StackEff}
    (ha : ieff lts i = some a) (hb : effList lts is = some b) :
    effList lts (i :: is) = some (comp a b) := by
  simp [effList, ha, hb]

theorem effList_append_of {lts : List CValType} :
    ∀ {a b : List Instr} {x y : StackEff}, effList lts a = some x → effList lts b = some y →
      effList lts (a ++ b) = some (comp x y)
  | [], _, x, y, ha, hb => by
    simp only [effList, Option.some.injEq] at ha; subst ha; simpa using hb
  | i :: a, b, x, y, ha, hb => by
    obtain ⟨u, v, hu, hv, rfl⟩ := effList_cons ha
    rw [List.cons_append, effList_cons' hu (effList_append_of hv hb), comp_assoc]

theorem effList_append {lts : List CValType} :
    ∀ {a b : List Instr} {e : StackEff}, effList lts (a ++ b) = some e →
      ∃ x y, effList lts a = some x ∧ effList lts b = some y ∧ e = comp x y
  | [], _, e, h => ⟨([], []), e, rfl, by simpa using h, by simp⟩
  | i :: a, b, e, h => by
    rw [List.cons_append] at h
    obtain ⟨u, v, hu, hv, rfl⟩ := effList_cons h
    obtain ⟨x, y, hx, hy, rfl⟩ := effList_append hv
    exact ⟨comp u x, y, effList_cons' hu hx, hy, (comp_assoc _ _ _).symm⟩

theorem effList_single {lts : List CValType} {i : Instr} {e : StackEff}
    (h : effList lts [i] = some e) : ieff lts i = some e := by
  obtain ⟨a, b, ha, hb, rfl⟩ := effList_cons h
  simp only [effList, Option.some.injEq] at hb
  subst hb; simpa using ha

/-! ## Subtyping chains -/

/-- One subtyping step into a valid type. -/
abbrev SubStep (Δ : TypeCtx) (a b : CValType) : Prop := Sub Δ a b ∧ TyOk Δ b

/-- Chains of subtyping steps through valid types. -/
abbrev SubStar (Δ : TypeCtx) : CValType → CValType → Prop := Relation.ReflTransGen (SubStep Δ)

/-- Pointwise chains. -/
abbrev PW (Δ : TypeCtx) : List CValType → List CValType → Prop := List.Forall₂ (SubStar Δ)

theorem PW.refl (Δ : TypeCtx) (a : List CValType) : PW Δ a a :=
  f2_refl (fun _ => Relation.ReflTransGen.refl) a

theorem PW.trans {Δ : TypeCtx} {a b c : List CValType} (h₁ : PW Δ a b) (h₂ : PW Δ b c) :
    PW Δ a c :=
  f2_trans (R := SubStar Δ) (fun _ _ _ h h' => Relation.ReflTransGen.trans h h') h₁ h₂

theorem PW.of_sub {Δ : TypeCtx} : ∀ {a b : List CValType}, List.Forall₂ (Sub Δ) a b →
    ResultOk Δ b → PW Δ a b
  | _, _, .nil, _ => List.Forall₂.nil
  | _, _, .cons h t, hb =>
    List.Forall₂.cons (Relation.ReflTransGen.single ⟨h, hb _ (by simp)⟩)
      (PW.of_sub t (fun x hx => hb x (by simp [hx])))

theorem SubStar.ok {Δ : TypeCtx} {a b : CValType} (h : SubStar Δ a b) (ha : TyOk Δ a) :
    TyOk Δ b := by
  induction h with
  | refl => exact ha
  | tail _ hs _ => exact hs.2

theorem PW.ok {Δ : TypeCtx} : ∀ {a b : List CValType}, PW Δ a b → ResultOk Δ a → ResultOk Δ b
  | _, _, .nil, _ => fun _ h => by simp at h
  | _, _, .cons h t, ha => by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact SubStar.ok h (ha _ (by simp))
    · exact PW.ok t (fun y hy => ha y (by simp [hy])) x hx

/-- List-level chains of `ResultSub` steps into valid result types. -/
abbrev LChain (Δ : TypeCtx) : List CValType → List CValType → Prop :=
  Relation.ReflTransGen (fun a b => ResultSub Δ a b ∧ ResultOk Δ b)

theorem LChain.cons_left {Δ : TypeCtx} {x : CValType} {a b : List CValType} (hx : TyOk Δ x)
    (h : LChain Δ a b) : LChain Δ (x :: a) (x :: b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    refine Relation.ReflTransGen.tail ih
      ⟨List.Forall₂.cons (Sub.refl Δ (k := .val) trivial x) hs.1, ?_⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hx
    · exact hs.2 t ht

theorem LChain.head_lift {Δ : TypeCtx} {x y : CValType} {b : List CValType}
    (hxy : SubStar Δ x y) (hb : ResultOk Δ b) : LChain Δ (x :: b) (y :: b) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    refine Relation.ReflTransGen.tail ih ⟨List.Forall₂.cons hs.1 (ResultSub.refl Δ b), ?_⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hs.2
    · exact hb t ht

theorem LChain.of_pw {Δ : TypeCtx} {a b : List CValType} (h : PW Δ a b) (ha : ResultOk Δ a) :
    LChain Δ a b := by
  revert ha
  induction h with
  | nil => intro _; exact Relation.ReflTransGen.refl
  | @cons x y a b hxy t ih =>
    intro ha
    have hx : TyOk Δ x := ha x (by simp)
    have ha' : ResultOk Δ a := fun z hz => ha z (by simp [hz])
    exact Relation.ReflTransGen.trans (LChain.cons_left hx (ih ha'))
      (LChain.head_lift hxy (PW.ok t ha'))

/-! ## Realising a typing by stacked subsumptions -/

theorem realize_res {C : Context} {is : List Instr} {p r r' : List CValType}
    (h : InstrsOk C is ⟨p, [], r⟩) (hp : ResultOk C.toTypeCtx p) (hc : LChain C.toTypeCtx r r') :
    InstrsOk C is ⟨p, [], r'⟩ := by
  induction hc with
  | refl => exact h
  | tail _ hs ih =>
    exact InstrsOk.sub ih ⟨ResultSub.refl _ _, hs.1, fun _ hx => by simp at hx⟩
      ⟨hp, hs.2, fun _ hx => by simp at hx⟩

theorem realize_par {C : Context} {is : List Instr} {p p' r : List CValType}
    (h : InstrsOk C is ⟨p, [], r⟩) (hr : ResultOk C.toTypeCtx r) (hc : LChain C.toTypeCtx p' p)
    (hp' : ResultOk C.toTypeCtx p') : InstrsOk C is ⟨p', [], r⟩ := by
  revert hp'
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact h
  | head hst _ ih =>
    intro hp'
    exact InstrsOk.sub (ih hst.2) ⟨hst.1, ResultSub.refl _ _, fun _ hx => by simp at hx⟩
      ⟨hp', hr, fun _ hx => by simp at hx⟩

theorem realize {C : Context} {is : List Instr} {p r p' r' : List CValType} {xs : List Nat}
    (h : InstrsOk C is ⟨p, [], r⟩) (hp : ResultOk C.toTypeCtx p) (hr : ResultOk C.toTypeCtx r)
    (hp' : ResultOk C.toTypeCtx p') (hpp : PW C.toTypeCtx p' p) (hrr : PW C.toTypeCtx r r')
    (hxs : ∀ x ∈ xs, ∃ t, C.locals[x]? = some ⟨.set, t⟩) : InstrsOk C is ⟨p', xs, r'⟩ := by
  have hr' : ResultOk C.toTypeCtx r' := PW.ok hrr hr
  have h₁ := realize_res h hp (LChain.of_pw hrr hr)
  have h₂ := realize_par h₁ hr' (LChain.of_pw hpp hp') hp'
  exact InstrsOk.sub h₂ ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun x hx _ => hxs x hx⟩
    ⟨hp', hr', fun x hx => let ⟨_, ht⟩ := hxs x hx; ⟨_, ht⟩⟩

/-! ## Effect summaries -/

/-- `it` is a typing (in `C`) of code with stack effect `e`, up to framing and
chains of subsumption. -/
structure Eff (C : Context) (e : StackEff) (it : InstrType) : Prop where
  pok : ResultOk C.toTypeCtx it.params
  inits : ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩
  stk : ∃ ts, ResultOk C.toTypeCtx ts ∧ PW C.toTypeCtx it.params (ts ++ e.1) ∧
    PW C.toTypeCtx (ts ++ e.2) it.results

theorem Eff.base {C : Context} {e : StackEff} (h : ResultOk C.toTypeCtx e.1) :
    Eff C e ⟨e.1, [], e.2⟩ :=
  ⟨h, fun _ hx => by simp at hx, ⟨[], by simp, PW.refl _ _, PW.refl _ _⟩⟩

theorem Eff.frame {C : Context} {e : StackEff} {p r us : List CValType} {xs : List Nat}
    (h : Eff C e ⟨p, xs, r⟩) (hus : ResultOk C.toTypeCtx us) : Eff C e ⟨us ++ p, xs, us ++ r⟩ := by
  obtain ⟨hp, hi, ts, hts, h₁, h₂⟩ := h
  refine ⟨ResultOk.append hus hp, hi, us ++ ts, ResultOk.append hus hts, ?_, ?_⟩
  · simpa [List.append_assoc] using f2_append (PW.refl _ us) h₁
  · simpa [List.append_assoc] using f2_append (PW.refl _ us) h₂

theorem Eff.sub {C : Context} {e : StackEff} {it it' : InstrType} (h : Eff C e it)
    (hs : InstrTypeSub C it it') (hok : InstrTypeOk C it') : Eff C e it' := by
  obtain ⟨hp, hi, ts, hts, h₁, h₂⟩ := h
  refine ⟨hok.1, ?_, ts, hts, PW.trans (PW.of_sub hs.1 hp) h₁,
    PW.trans h₂ (PW.of_sub hs.2.1 hok.2.1)⟩
  intro x hx
  by_cases hx' : x ∈ it.inits
  · exact hi x hx'
  · exact hs.2.2 x hx hx'

/-- Change the context (same types), dropping the initialised locals, and extend
the results by a subsumption. -/
theorem Eff.weaken {C C' : Context} {e : StackEff} {p r r' : List CValType} {xs : List Nat}
    (h : Eff C e ⟨p, xs, r⟩) (hT : C'.toTypeCtx = C.toTypeCtx)
    (hrr : ResultSub C.toTypeCtx r r') (hr' : ResultOk C.toTypeCtx r') : Eff C' e ⟨p, [], r'⟩ := by
  obtain ⟨hp, -, ts, hts, h₁, h₂⟩ := h
  refine ⟨by rw [hT]; exact hp, fun _ hx => by simp at hx, ts, by rw [hT]; exact hts,
    by rw [hT]; exact h₁, by rw [hT]; exact PW.trans h₂ (PW.of_sub hrr hr')⟩

/-- Extend the parameters by a subsumption, dropping the initialised locals. -/
theorem Eff.params {C : Context} {e : StackEff} {p p' r : List CValType} {xs : List Nat}
    (h : Eff C e ⟨p, xs, r⟩) (hpp : ResultSub C.toTypeCtx p' p) (hp' : ResultOk C.toTypeCtx p') :
    Eff C e ⟨p', [], r⟩ := by
  obtain ⟨hp, -, ts, hts, h₁, h₂⟩ := h
  exact ⟨hp', fun _ hx => by simp at hx, ts, hts, PW.trans (PW.of_sub hpp hp) h₁, h₂⟩

theorem Eff.results_ok {C : Context} {e : StackEff} {it : InstrType} (h : Eff C e it)
    (he : ResultOk C.toTypeCtx e.2) : ResultOk C.toTypeCtx it.results := by
  obtain ⟨-, -, ts, hts, -, h₂⟩ := h
  exact PW.ok h₂ (ResultOk.append hts he)

theorem Eff.seq {C : Context} {e₁ e₂ : StackEff} {p m r : List CValType} {x₁ x₂ : List Nat}
    (h₁ : Eff C e₁ ⟨p, x₁, m⟩) (h₂ : Eff (C.initLocals x₁) e₂ ⟨m, x₂, r⟩) :
    Eff C (comp e₁ e₂) ⟨p, x₁ ++ x₂, r⟩ := by
  obtain ⟨hp, hi₁, ts₁, hts₁, hp₁, hm₁⟩ := h₁
  obtain ⟨-, hi₂, ts₂, hts₂, hm₂, hr₂⟩ := h₂
  simp only [Context.initLocals_toTypeCtx] at hts₂ hm₂ hr₂
  refine ⟨hp, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hi₁ x hx
    · obtain ⟨t, ht⟩ := hi₂ x hx
      rcases Context.initLocals_set ht with hx' | ht'
      · exact hi₁ x hx'
      · exact ⟨t, ht'⟩
  · have hmid : PW C.toTypeCtx (ts₁ ++ e₁.2) (ts₂ ++ e₂.1) := PW.trans hm₁ hm₂
    have hlen := f2_length hmid
    simp only [List.length_append] at hlen
    unfold RTy.comp
    split
    · rename_i hle
      refine ⟨ts₁, hts₁, hp₁, ?_⟩
      have hsplit : PW C.toTypeCtx (ts₁ ++ e₁.2.take (e₁.2.length - e₂.1.length)) ts₂ ∧
          PW C.toTypeCtx (e₁.2.drop (e₁.2.length - e₂.1.length)) e₂.1 := by
        refine f2_split ?_ ?_
        · simp only [List.length_append, List.length_take]; omega
        · rw [List.append_assoc, List.take_append_drop]
          exact hmid
      have := f2_append hsplit.1 (PW.refl C.toTypeCtx e₂.2)
      rw [List.append_assoc] at this
      exact PW.trans this hr₂
    · rename_i hle
      refine ⟨ts₂, hts₂, ?_, hr₂⟩
      have hsplit : PW C.toTypeCtx ts₁ (ts₂ ++ e₂.1.take (e₂.1.length - e₁.2.length)) ∧
          PW C.toTypeCtx e₁.2 (e₂.1.drop (e₂.1.length - e₁.2.length)) := by
        refine f2_split ?_ ?_
        · simp only [List.length_append, List.length_take]; omega
        · rw [List.append_assoc, List.take_append_drop]
          exact hmid
      have := f2_append hsplit.1 (PW.refl C.toTypeCtx e₁.1)
      rw [List.append_assoc] at this
      exact PW.trans hp₁ this

/-! ## Simple instructions -/

theorem initLocals_types (C : Context) (xs : List Nat) :
    (C.initLocals xs).locals.map (·.type) = C.locals.map (·.type) := by
  obtain ⟨L, hL, hy⟩ := C.initLocals_spec xs
  rw [hL]
  apply List.ext_getElem?
  intro y
  simp only [List.getElem?_map, hy y]
  split <;> simp [Option.map_map, Function.comp_def]

theorem ieff_ins_ok {lts : List CValType} {i : Instr} {e : StackEff} (h : ieff lts i = some e)
    (Δ : TypeCtx) : ResultOk Δ e.1 := by
  unfold ieff at h
  split at h <;> first
    | (simp only [Option.some.injEq] at h; subst h; simp)
    | cases h

/-- Inversion for simple instructions. -/
theorem simple_inv {C : Context} {i : Instr} {it : InstrType} {e : StackEff}
    (h : InstrOk C i it) (he : ieff (C.locals.map (·.type)) i = some e) :
    it = ⟨e.1, [], e.2⟩ := by
  cases h with
  | numeric h => cases h <;> simp [ieff] at he <;> subst he <;> rfl
  | «variable» h =>
    cases h with
    | localGet hx => simp [ieff, hx] at he; subst he; rfl
    | _ => simp [ieff] at he
  | parametric h => cases h <;> simp [ieff] at he
  | vector h => cases h <;> simp [ieff] at he
  | memory h => cases h <;> simp [ieff] at he
  | table h => cases h <;> simp [ieff] at he
  | reference h => cases h <;> simp [ieff] at he
  | _ => simp [ieff] at he

/-- A typed sequence of simple instructions is summarised by its stack effect. -/
theorem eff_of_ok {lts : List CValType} {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) :
    ∀ {e : StackEff}, effList lts is = some e → C.locals.map (·.type) = lts → Eff C e it := by
  induction h using InstrsOk.ind with
  | nil =>
    intro e he _
    simp only [effList, Option.some.injEq] at he; subst he
    exact Eff.base (by simp)
  | @instr C i it₀ hi =>
    intro e he hl
    have he' := effList_single he
    rw [← hl] at he'
    rw [simple_inv hi he']
    exact Eff.base (ieff_ins_ok he' _)
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
    intro e he hl
    obtain ⟨x, y, hx₁, hy, rfl⟩ := effList_append he
    exact Eff.seq (ih₁ hx₁ hl) (ih₂ hy (by rw [initLocals_types, hl]))
  | @cons C i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
    intro e he hl
    obtain ⟨a, b, ha, hb, rfl⟩ := effList_cons he
    rw [← hl] at ha
    have hit := simple_inv hi ha
    simp only [InstrType.mk.injEq] at hit
    obtain ⟨rfl, rfl, rfl⟩ := hit
    have hb' := ih hb (by rw [initLocals_types, hl])
    exact Eff.seq (Eff.base (C := C) (ieff_ins_ok ha _)) hb'
  | sub h hs hok ih =>
    intro e he hl
    exact (ih he hl).sub hs hok
  | frame h hok ih =>
    intro e he hl
    exact (ih he hl).frame hok

/-- Outputs of every non-empty suffix are numeric (hence valid in every context). -/
def GoodOuts (lts : List CValType) (N : List Instr) : Prop :=
  ∀ S e, S ≠ [] → S <:+ N → effList lts S = some e → ∀ t ∈ e.2, ∃ n, t = .num n

theorem GoodOuts.suffix {lts : List CValType} {N N' : List Instr} (h : GoodOuts lts N)
    (hs : N' <:+ N) : GoodOuts lts N' :=
  fun S e hS hS' he => h S e hS (hS'.trans hs) he

theorem GoodOuts.ok {lts : List CValType} {N : List Instr} {e : StackEff} (h : GoodOuts lts N)
    (hN : N ≠ []) (he : effList lts N = some e) (Δ : TypeCtx) : ResultOk Δ e.2 := by
  intro t ht
  obtain ⟨n, rfl⟩ := h N e hN (List.suffix_refl N) he t ht
  exact TyOk.num n

theorem effList_outs {lts : List CValType} : ∀ {S : List Instr} {e : StackEff},
    effList lts S = some e → ∀ t ∈ e.2, ∃ i ∈ S, ∃ e', ieff lts i = some e' ∧ t ∈ e'.2
  | [], e, h => by
    simp only [effList, Option.some.injEq] at h
    subst h
    simp
  | i :: S, e, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := effList_cons h
    intro t ht
    unfold comp at ht
    split at ht
    · simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · exact ⟨i, by simp, a, ha, List.mem_of_mem_take ht⟩
      · obtain ⟨j, hj, e', he', ht'⟩ := effList_outs hb t ht
        exact ⟨j, by simp [hj], e', he', ht'⟩
    · obtain ⟨j, hj, e', he', ht'⟩ := effList_outs hb t ht
      exact ⟨j, by simp [hj], e', he', ht'⟩

theorem ieff_outs_num {lts : List CValType} {i : Instr} {e : StackEff} (h : ieff lts i = some e)
    (hi : ∀ x, i ≠ .localGet x) : ∀ t ∈ e.2, ∃ n, t = .num n := by
  unfold ieff at h
  split at h
  · cases h; intro t ht; simp at ht; exact ⟨_, ht⟩
  · cases h; intro t ht; simp at ht; exact ⟨_, ht⟩
  · cases h; intro t ht; simp at ht; exact ⟨_, ht⟩
  · cases h; intro t ht; simp at ht; exact ⟨_, ht⟩
  · cases h; intro t ht; simp at ht; exact ⟨_, ht⟩
  · exact absurd rfl (hi _)
  · cases h

theorem goodOuts_of_noLocal {lts : List CValType} {A : List Instr}
    (h : ∀ i ∈ A, ∀ x, i ≠ .localGet x) : GoodOuts lts A := by
  intro S e _ hS he t ht
  obtain ⟨i, hi, e', he', ht'⟩ := effList_outs he t ht
  exact ieff_outs_num he' (h i (hS.subset hi)) t ht'

/-! ## Exact splitting -/

/-- Cut a non-empty simple suffix off a typing derivation. -/
theorem split_right {lts : List CValType} {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) :
    ∀ {L N : List Instr} {e : StackEff}, is = L ++ N → N ≠ [] → effList lts N = some e →
      C.locals.map (·.type) = lts →
      ∃ m xa yN, InstrsOk C L ⟨it.params, xa, m⟩ ∧ Eff (C.initLocals xa) e ⟨m, yN, it.results⟩ ∧
        it.inits = xa ++ yN := by
  induction h using InstrsOk.ind with
  | nil =>
    intro L N e heq hN _ _
    exact absurd (List.append_eq_nil_iff.mp heq.symm).2 hN
  | @instr C i it₀ hi =>
    intro L N e heq hN he hl
    rcases List.append_eq_singleton_iff.mp heq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have he' := effList_single he
      rw [← hl] at he'
      have hit := simple_inv hi he'
      subst hit
      exact ⟨e.1, [], [], InstrsOk.id (ieff_ins_ok he' _), Eff.base (ieff_ins_ok he' _), rfl⟩
    · exact absurd rfl hN
  | @cons C i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
    intro L N e heq hN he hl
    rcases List.cons_eq_append_iff.mp heq with ⟨rfl, rfl⟩ | ⟨L', rfl, rfl⟩
    · have hE := eff_of_ok (InstrsOk.cons hi hx hs) he hl
      exact ⟨t₁, [], xs₁ ++ xs₂, InstrsOk.id hE.pok, hE, rfl⟩
    · obtain ⟨m, xa, yN, hL, hE, hin⟩ := ih rfl hN he (by rw [initLocals_types, hl])
      have hin' : xs₂ = xa ++ yN := hin
      subst hin'
      refine ⟨m, xs₁ ++ xa, yN, InstrsOk.cons hi hx hL, ?_, by simp⟩
      rw [Context.initLocals_append]; exact hE
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
    intro L N e heq hN he hl
    rcases List.append_eq_append_iff.mp heq with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · obtain ⟨m, xa, yN, ha, hE, hin⟩ := ih₂ rfl hN he (by rw [initLocals_types, hl])
      have hin' : xs₂ = xa ++ yN := hin
      subst hin'
      refine ⟨m, xs₁ ++ xa, yN, InstrsOk.seq h₁ hx ha, ?_, by simp⟩
      rw [Context.initLocals_append]; exact hE
    · by_cases hc : c' = []
      · subst hc
        rw [List.append_nil] at h₁
        simp only [List.nil_append] at he hN
        exact ⟨t₂, xs₁, xs₂, h₁, eff_of_ok h₂ he (by rw [initLocals_types, hl]), rfl⟩
      · obtain ⟨ec, e2, hec, he2, rfl⟩ := effList_append he
        obtain ⟨m, xa, yc, hL, hEc, hin⟩ := ih₁ rfl hc hec hl
        have hin' : xs₁ = xa ++ yc := hin
        subst hin'
        have hE2 := eff_of_ok h₂ he2 (by rw [initLocals_types, hl])
        rw [Context.initLocals_append] at hE2
        exact ⟨m, xa, yc ++ xs₂, hL, Eff.seq hEc hE2, by simp⟩
  | @sub C is it₀ it' h hs hok ih =>
    intro L N e heq hN he hl
    obtain ⟨m, xa, yN, hL, hE, hin⟩ := ih heq hN he hl
    have hm : ResultOk C.toTypeCtx m := by simpa using hE.pok
    refine ⟨m, it'.inits, [], ?_, ?_, by simp⟩
    · refine InstrsOk.sub hL ⟨hs.1, ResultSub.refl _ _, ?_⟩ ⟨hok.1, hm, hok.2.2⟩
      intro x hx hxa
      by_cases hx' : x ∈ it₀.inits
      · rw [hin] at hx'
        simp only [List.mem_append] at hx'
        rcases hx' with hx' | hx'
        · exact absurd hx' hxa
        · obtain ⟨t, ht⟩ := hE.inits x hx'
          rcases Context.initLocals_set ht with h' | h'
          · exact absurd h' hxa
          · exact ⟨t, h'⟩
      · exact hs.2.2 x hx hx'
    · exact hE.weaken (by simp) (by simpa using hs.2.1) (by simpa using hok.2.1)
  | @frame C is ts t₁ t₂ xs h hok ih =>
    intro L N e heq hN he hl
    obtain ⟨m, xa, yN, hL, hE, hin⟩ := ih heq hN he hl
    exact ⟨ts ++ m, xa, yN, InstrsOk.frame hL hok, hE.frame (by simpa using hok), hin⟩

/-- Cut a non-empty simple prefix with numeric outputs off a typing derivation. -/
theorem split_left {lts : List CValType} {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) :
    ∀ {N Q : List Instr} {e : StackEff}, is = N ++ Q → N ≠ [] → effList lts N = some e →
      GoodOuts lts N → C.locals.map (·.type) = lts →
      ∃ m yN yQ, Eff C e ⟨it.params, yN, m⟩ ∧ InstrsOk (C.initLocals yN) Q ⟨m, yQ, it.results⟩ ∧
        it.inits = yN ++ yQ := by
  induction h using InstrsOk.ind with
  | nil =>
    intro N Q e heq hN _ _ _
    exact absurd (List.append_eq_nil_iff.mp heq.symm).1 hN
  | @instr C i it₀ hi =>
    intro N Q e heq hN he hg hl
    rcases List.append_eq_singleton_iff.mp heq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hN
    · have he' := effList_single he
      rw [← hl] at he'
      have hit := simple_inv hi he'
      subst hit
      exact ⟨e.2, [], [], Eff.base (ieff_ins_ok he' _), InstrsOk.id (hg.ok hN he _), rfl⟩
  | @cons C i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
    intro N Q e heq hN he hg hl
    rcases List.cons_eq_append_iff.mp heq with ⟨rfl, -⟩ | ⟨N', rfl, rfl⟩
    · exact absurd rfl hN
    · obtain ⟨a, b, ha, hb, rfl⟩ := effList_cons he
      rw [← hl] at ha
      have hit := simple_inv hi ha
      simp only [InstrType.mk.injEq] at hit
      obtain ⟨rfl, rfl, rfl⟩ := hit
      by_cases hN' : N' = []
      · subst hN'
        simp only [effList, Option.some.injEq] at hb; subst hb
        refine ⟨a.2, [], xs₂, ?_, ?_, rfl⟩
        · rw [comp_nil_right]; exact Eff.base (ieff_ins_ok ha _)
        · simpa using hs
      · obtain ⟨m, yN, yQ, hE, hQ, hin⟩ := ih rfl hN' hb
          (hg.suffix (List.suffix_cons _ _)) (by rw [initLocals_types, hl])
        have hin' : xs₂ = yN ++ yQ := hin
        subst hin'
        refine ⟨m, [] ++ yN, yQ, Eff.seq (Eff.base (C := C) (ieff_ins_ok ha _)) hE, ?_, rfl⟩
        exact hQ
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
    intro N Q e heq hN he hg hl
    rcases List.append_eq_append_iff.mp heq with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · obtain ⟨e₁, e₂, he₁, he₂, rfl⟩ := effList_append he
      have hE₁ := eff_of_ok h₁ he₁ hl
      by_cases ha' : a' = []
      · subst ha'
        simp only [effList, Option.some.injEq] at he₂; subst he₂
        refine ⟨t₂, xs₁, xs₂, ?_, ?_, rfl⟩
        · rw [comp_nil_right]; exact hE₁
        · simpa using h₂
      · obtain ⟨m, yA, yQ, hE₂, hQ, hin⟩ := ih₂ rfl ha' he₂
          (hg.suffix (List.suffix_append _ _)) (by rw [initLocals_types, hl])
        have hin' : xs₂ = yA ++ yQ := hin
        subst hin'
        refine ⟨m, xs₁ ++ yA, yQ, Eff.seq hE₁ hE₂, ?_, by simp⟩
        rw [Context.initLocals_append]; exact hQ
    · obtain ⟨m, yN, yc, hE, hc, hin⟩ := ih₁ rfl hN he hg hl
      have hin' : xs₁ = yN ++ yc := hin
      subst hin'
      have h₂' : InstrsOk ((C.initLocals yN).initLocals yc) is₂ ⟨t₂, xs₂, t₃⟩ := by
        rw [← Context.initLocals_append]; exact h₂
      have hx' : ∀ x ∈ yc, ∃ lt, (C.initLocals yN).locals[x]? = some lt := by
        intro x hxm
        exact Context.initLocals_exists.mpr (hx x (by simp [hxm]))
      exact ⟨m, yN, yc ++ xs₂, hE, InstrsOk.seq hc hx' h₂', by simp⟩
  | @sub C is it₀ it' h hs hok ih =>
    intro N Q e heq hN he hg hl
    obtain ⟨m, yN, yQ, hE, hQ, hin⟩ := ih heq hN he hg hl
    have hm : ResultOk C.toTypeCtx m := hE.results_ok (hg.ok hN he _)
    have hC : C.initLocals yN = C := Context.initLocals_of_set (xs := yN) hE.inits
    rw [hC] at hQ
    refine ⟨m, [], it'.inits, hE.params hs.1 hok.1, ?_, by simp⟩
    refine InstrsOk.sub hQ ⟨ResultSub.refl _ _, hs.2.1, ?_⟩ ⟨hm, hok.2.1, hok.2.2⟩
    intro x hx hxq
    by_cases hx' : x ∈ it₀.inits
    · rw [hin] at hx'
      simp only [List.mem_append] at hx'
      rcases hx' with hx' | hx'
      · exact hE.inits x hx'
      · exact absurd hx' hxq
    · exact hs.2.2 x hx hx'
  | @frame C is ts t₁ t₂ xs h hok ih =>
    intro N Q e heq hN he hg hl
    obtain ⟨m, yN, yQ, hE, hQ, hin⟩ := ih heq hN he hg hl
    exact ⟨ts ++ m, yN, yQ, hE.frame hok, InstrsOk.frame hQ (by simpa using hok), hin⟩

/-! ## Replacement -/

/-- A redex: a non-empty simple sequence with numeric outputs on every suffix,
and a replacement typable at every typing of its stack effect. -/
structure Redex (lts : List CValType) (A B : List Instr) : Prop where
  ne : A ≠ []
  eff : ∃ e, effList lts A = some e ∧
    ∀ C it, C.locals.map (·.type) = lts → Eff C e it → InstrsOk C B it
  good : GoodOuts lts A

theorem straddle {lts : List CValType} {A B : List Instr} (hR : Redex lts A B) {C : Context}
    {L A₁ A₂ R : List Instr} {t₁ t₂ t₃ : List CValType} {x₁ x₂ : List Nat}
    (h₁ : InstrsOk C (L ++ A₁) ⟨t₁, x₁, t₂⟩) (hx : ∀ x ∈ x₁, ∃ lt, C.locals[x]? = some lt)
    (h₂ : InstrsOk (C.initLocals x₁) (A₂ ++ R) ⟨t₂, x₂, t₃⟩) (hA : A = A₁ ++ A₂)
    (h1 : A₁ ≠ []) (h2 : A₂ ≠ []) (hl : C.locals.map (·.type) = lts) :
    InstrsOk C (L ++ B ++ R) ⟨t₁, x₁ ++ x₂, t₃⟩ := by
  obtain ⟨-, ⟨eA, heA, hB⟩, hg⟩ := hR
  subst hA
  obtain ⟨e₁, e₂, he₁, he₂, rfl⟩ := effList_append heA
  obtain ⟨m, xa, yA₁, hL, hE₁, hin₁⟩ := split_right h₁ rfl h1 he₁ hl
  obtain ⟨n, yA₂, yR, hE₂, hR', hin₂⟩ := split_left h₂ rfl h2 he₂
    (hg.suffix (List.suffix_append _ _)) (by rw [initLocals_types, hl])
  have hin₁' : x₁ = xa ++ yA₁ := hin₁
  have hin₂' : x₂ = yA₂ ++ yR := hin₂
  subst hin₁' hin₂'
  rw [Context.initLocals_append] at hE₂ hR'
  have hEA := Eff.seq hE₁ hE₂
  have hBt := hB _ _ (by rw [initLocals_types, hl]) hEA
  have hR'' : InstrsOk ((C.initLocals xa).initLocals (yA₁ ++ yA₂)) R ⟨n, yR, t₃⟩ := by
    rw [Context.initLocals_append]; exact hR'
  have hBR := InstrsOk.seq hBt (fun x hx' => let ⟨_, ht⟩ := hEA.inits x hx'; ⟨_, ht⟩) hR''
  have hxa : ∀ x ∈ xa, ∃ lt, C.locals[x]? = some lt := fun x hx' => hx x (by simp [hx'])
  have := InstrsOk.seq hL hxa hBR
  simpa [List.append_assoc] using this

theorem repl_aux {lts : List CValType} {A B : List Instr} (hR : Redex lts A B) {C : Context}
    {is : List Instr} {it : InstrType} (h : InstrsOk C is it) :
    ∀ {L R : List Instr}, is = L ++ A ++ R → C.locals.map (·.type) = lts →
      InstrsOk C (L ++ B ++ R) it := by
  have hAne := hR.ne
  obtain ⟨eA, heA, hB⟩ := hR.eff
  induction h using InstrsOk.ind with
  | nil =>
    intro L R heq _
    simp only [List.append_assoc] at heq
    exact absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp heq.symm).2).1 hAne
  | @instr C i it₀ hi =>
    intro L R heq hl
    simp only [List.append_assoc] at heq
    rcases List.append_eq_singleton_iff.mp heq.symm with ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    · rcases List.append_eq_singleton_iff.mp h' with ⟨hA, -⟩ | ⟨hA, rfl⟩
      · exact absurd hA hAne
      · subst hA
        simpa using hB C it₀ hl (eff_of_ok (InstrsOk.instr hi) heA hl)
    · exact absurd (List.append_eq_nil_iff.mp h').1 hAne
  | @cons C i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
    intro L R heq hl
    simp only [List.append_assoc] at heq
    rcases List.cons_eq_append_iff.mp heq with ⟨rfl, h'⟩ | ⟨L', rfl, h'⟩
    · rcases List.cons_eq_append_iff.mp h'.symm with ⟨hA, -⟩ | ⟨A₂, hA, rfl⟩
      · exact absurd hA hAne
      · subst hA
        by_cases hA₂ : A₂ = []
        · subst hA₂
          have hBt := hB C ⟨t₁, xs₁, t₂⟩ hl (eff_of_ok (InstrsOk.instr hi) heA hl)
          simpa using InstrsOk.seq hBt hx hs
        · have h₁ : InstrsOk C ([] ++ [i]) ⟨t₁, xs₁, t₂⟩ := InstrsOk.instr hi
          exact straddle hR h₁ hx hs rfl (by simp) hA₂ hl
    · subst h'
      have := ih (L := L') (R := R) (by simp) (by rw [initLocals_types, hl])
      simpa using InstrsOk.cons hi hx this
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
    intro L R heq hl
    simp only [List.append_assoc] at heq
    rcases List.append_eq_append_iff.mp heq with ⟨a', rfl, h'⟩ | ⟨c', rfl, h'⟩
    · subst h'
      have := ih₂ (L := a') (R := R) (by simp) (by rw [initLocals_types, hl])
      simpa [List.append_assoc] using InstrsOk.seq h₁ hx this
    · rcases List.append_eq_append_iff.mp h' with ⟨a'', rfl, rfl⟩ | ⟨c'', hA, rfl⟩
      · have := ih₁ (L := L) (R := a'') (by simp) hl
        simpa [List.append_assoc] using InstrsOk.seq this hx h₂
      · by_cases hc' : c' = []
        · subst hc'
          rw [List.append_nil] at h₁
          simp only [List.nil_append] at hA
          subst hA
          have := ih₂ (L := []) (R := R) (by simp) (by rw [initLocals_types, hl])
          simpa [List.append_assoc] using InstrsOk.seq h₁ hx this
        · by_cases hc'' : c'' = []
          · subst hc''
            simp only [List.append_nil] at hA
            subst hA
            have := ih₁ (L := L) (R := []) (by simp) hl
            simpa [List.append_assoc] using InstrsOk.seq this hx h₂
          · exact straddle hR h₁ hx h₂ hA hc' hc'' hl
  | sub h hs hok ih =>
    intro L R heq hl
    exact InstrsOk.sub (ih heq hl) hs hok
  | frame h hok ih =>
    intro L R heq hl
    exact InstrsOk.frame (ih heq hl) hok

/-! ## Contextual typing implication -/

/-- Every typing of `xs` in any surrounding code is a typing of `ys` there. -/
def PresL (xs ys : List Instr) : Prop :=
  ∀ (C : Context) (L R : List Instr) (it : InstrType),
    InstrsOk C (L ++ xs ++ R) it → InstrsOk C (L ++ ys ++ R) it

theorem PresL.refl (xs : List Instr) : PresL xs xs := fun _ _ _ _ h => h

theorem PresL.trans {xs ys zs : List Instr} (h₁ : PresL xs ys) (h₂ : PresL ys zs) :
    PresL xs zs := fun C L R it h => h₂ C L R it (h₁ C L R it h)

theorem PresL.ctx {xs ys : List Instr} (h : PresL xs ys) (a b : List Instr) :
    PresL (a ++ xs ++ b) (a ++ ys ++ b) := by
  intro C L R it h'
  have := h C (L ++ a) (b ++ R) it (by simpa [List.append_assoc] using h')
  simpa [List.append_assoc] using this

theorem PresL.apply {xs ys : List Instr} (h : PresL xs ys) {C : Context} {it : InstrType}
    (h' : InstrsOk C xs it) : InstrsOk C ys it := by
  simpa using h C [] [] it (by simpa using h')

theorem PresL.append {xs ys xs' ys' : List Instr} (h : PresL xs ys) (h' : PresL xs' ys') :
    PresL (xs ++ xs') (ys ++ ys') := by
  have h₁ := h.ctx [] xs'
  have h₂ := h'.ctx ys []
  simp only [List.nil_append, List.append_nil] at h₁ h₂
  exact h₁.trans h₂

theorem PresL.of_redex {A B : List Instr} (h : ∀ lts, Redex lts A B) : PresL A B :=
  fun _ _ _ _ h' => repl_aux (h _) h' rfl rfl

theorem pres_instr_aux {i i' : Instr} (hi : ∀ C it, InstrOk C i it → InstrOk C i' it)
    {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it) :
    ∀ {L R : List Instr}, is = L ++ [i] ++ R → InstrsOk C (L ++ [i'] ++ R) it := by
  induction h using InstrsOk.ind with
  | nil =>
    intro L R heq
    simp at heq
  | @instr C j it₀ hj =>
    intro L R heq
    simp only [List.append_assoc, List.singleton_append] at heq
    rcases List.singleton_eq_append_iff.mp heq with ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    · simp only [List.cons.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact InstrsOk.instr (hi _ _ hj)
    · simp at h'
  | @cons C j is t₁ t₂ t₃ xs₁ xs₂ hj hx hs ih =>
    intro L R heq
    simp only [List.append_assoc, List.singleton_append] at heq
    rcases List.cons_eq_append_iff.mp heq with ⟨rfl, h'⟩ | ⟨L', rfl, h'⟩
    · simp only [List.cons.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      simpa using InstrsOk.cons (hi _ _ hj) hx hs
    · subst h'
      have := ih (L := L') (R := R) (by simp)
      simpa using InstrsOk.cons hj hx this
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
    intro L R heq
    simp only [List.append_assoc, List.singleton_append] at heq
    rcases List.append_eq_append_iff.mp heq with ⟨a', rfl, h'⟩ | ⟨c', rfl, h'⟩
    · subst h'
      have := ih₂ (L := a') (R := R) (by simp)
      simpa [List.append_assoc] using InstrsOk.seq h₁ hx this
    · rcases List.cons_eq_append_iff.mp h' with ⟨rfl, rfl⟩ | ⟨c'', rfl, rfl⟩
      · rw [List.append_nil] at h₁
        have := ih₂ (L := []) (R := R) (by simp)
        simpa [List.append_assoc] using InstrsOk.seq h₁ hx this
      · have := ih₁ (L := L) (R := c'') (by simp)
        simpa [List.append_assoc] using InstrsOk.seq this hx h₂
  | sub h hs hok ih =>
    intro L R heq
    exact InstrsOk.sub (ih heq) hs hok
  | frame h hok ih =>
    intro L R heq
    exact InstrsOk.frame (ih heq) hok

theorem PresL.instr {i i' : Instr} (hi : ∀ C it, InstrOk C i it → InstrOk C i' it) :
    PresL [i] [i'] :=
  fun _ _ _ _ h => pres_instr_aux hi h rfl

theorem instrOk_block {bt : BlockType} {b b' : List Instr}
    (hb : ∀ C it, InstrsOk C b it → InstrsOk C b' it) :
    ∀ C it, InstrOk C (.block bt b) it → InstrOk C (.block bt b') it := by
  intro C it h
  cases h with
  | block hbt hbody => exact InstrOk.block hbt (hb _ _ hbody)
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem instrOk_loop {bt : BlockType} {b b' : List Instr}
    (hb : ∀ C it, InstrsOk C b it → InstrsOk C b' it) :
    ∀ C it, InstrOk C (.loop bt b) it → InstrOk C (.loop bt b') it := by
  intro C it h
  cases h with
  | loop hbt hbody => exact InstrOk.loop hbt (hb _ _ hbody)
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem instrOk_if {bt : BlockType} {b₁ b₂ b₁' b₂' : List Instr}
    (hb₁ : ∀ C it, InstrsOk C b₁ it → InstrsOk C b₁' it)
    (hb₂ : ∀ C it, InstrsOk C b₂ it → InstrsOk C b₂' it) :
    ∀ C it, InstrOk C (.if_ bt b₁ b₂) it → InstrOk C (.if_ bt b₁' b₂') it := by
  intro C it h
  cases h with
  | if_ hbt h₁ h₂ => exact InstrOk.if_ hbt (hb₁ _ _ h₁) (hb₂ _ _ h₂)
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem instrOk_tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr}
    (hb : ∀ C it, InstrsOk C b it → InstrsOk C b' it) :
    ∀ C it, InstrOk C (.tryTable bt cs b) it → InstrOk C (.tryTable bt cs b') it := by
  intro C it h
  cases h with
  | tryTable hbt hbody hc => exact InstrOk.tryTable hbt (hb _ _ hbody) hc
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

end RTy

end Silmaril.Wasm.Binaryen
