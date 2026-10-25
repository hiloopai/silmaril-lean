module

public import Silmaril.Wasm.Execution.Core.Soundness.Parametric
public import Silmaril.Wasm.Execution.Core.Soundness.Numeric
public import Silmaril.Wasm.Execution.Core.Soundness.Vector
public import Silmaril.Wasm.Execution.Core.Soundness.Table
public import Silmaril.Wasm.Execution.Core.Soundness.Memory
public import Silmaril.Wasm.Execution.Core.Soundness.Reference
public import Silmaril.Wasm.Execution.Core.Soundness.Aggregate
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Auxiliary lemmas for progress

* list and value-sequence plumbing (`ValsTo`: values typed up to a chain of
  subtypings, which is what sequence typing provides without transitivity);
* `CtxOk`: the invariant relating the typing context of code (with labels,
  a return type and partially initialised locals) to the running frame;
* transport of the family typings from such a context to the frame context;
* store/module inversions (`call`, `global`, `tag`, block types).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Lists -/

theorem forall₂_split {α β : Type} {R : α → β → Prop} {l : List α} {m₁ m₂ : List β}
    (h : List.Forall₂ R l (m₁ ++ m₂)) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂ :=
  ⟨_, _, (List.take_append_drop _ _).symm, List.forall₂_take_append _ _ _ h,
    List.forall₂_drop_append _ _ _ h⟩

theorem vals_eq_nil {vs : List Val} : vals vs = [] ↔ vs = [] := by simp [vals]

/-- Split a list of values at a given length from the end. -/
theorem List.exists_split_right {α : Type} (l : List α) (n : Nat) (h : n ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₂.length = n :=
  ⟨l.take (l.length - n), l.drop (l.length - n), (List.take_append_drop _ _).symm,
    by simp; omega⟩

/-! ## Values up to a chain of subtypings -/

/-- A value of a type reachable by a chain of subtypings in `Δ`. -/
def ValTo (s : Store H) (Δ : TypeCtx) (v : Val) (t : CValType) : Prop :=
  ∃ t₀, ValOk s v t₀ ∧ Relation.ReflTransGen (Sub Δ) t₀ t

abbrev ValsTo (s : Store H) (Δ : TypeCtx) (vs : List Val) (ts : List CValType) : Prop :=
  List.Forall₂ (ValTo s Δ) vs ts

theorem ValsTo.of_sub {s : Store H} {Δ : TypeCtx} {vs : List Val} {tsv t₂ t₃ : List CValType}
    (hv : List.Forall₂ (ValOk s) vs tsv) (h₁ : ResultSub Δ tsv t₂) (h₂ : ResultSub Δ t₂ t₃) :
    ValsTo s Δ vs t₃ := by
  induction hv generalizing t₂ t₃ with
  | nil => cases h₁; cases h₂; exact .nil
  | cons hv _ ih =>
    cases h₁ with
    | cons ha h₁ =>
      cases h₂ with
      | cons hb h₂ => exact .cons ⟨_, hv, .tail (.single ha) hb⟩ (ih h₁ h₂)

theorem ValsTo.of_valOk {s : Store H} {Δ : TypeCtx} {vs : List Val} {ts : List CValType}
    (hv : List.Forall₂ (ValOk s) vs ts) : ValsTo s Δ vs ts :=
  hv.imp fun _ _ h => ⟨_, h, .refl⟩

theorem rtg_down {α : Type} {R : α → α → Prop} {S : α → Prop} (hS : ∀ a b, R a b → S b → S a)
    {a b : α} (h : Relation.ReflTransGen R a b) (hb : S b) : S a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | head hab _ ih => exact hS _ _ hab ih

theorem sub_num_inv {Δ : TypeCtx} {t : CValType} {n : NumType}
    (h : Relation.ReflTransGen (Sub Δ) t (.num n)) : t = .num n ∨ t = .botv :=
  rtg_down (S := fun t => t = .num n ∨ t = .botv) (fun a b hab hb => by
    rcases hb with rfl | rfl <;> cases hab <;> simp) h (.inl rfl)

theorem sub_vec_inv {Δ : TypeCtx} {t : CValType} {n : VecType}
    (h : Relation.ReflTransGen (Sub Δ) t (.vec n)) : t = .vec n ∨ t = .botv :=
  rtg_down (S := fun t => t = .vec n ∨ t = .botv) (fun a b hab hb => by
    rcases hb with rfl | rfl <;> cases hab <;> simp) h (.inl rfl)

theorem sub_ref_inv {Δ : TypeCtx} {t : CValType} {rt : CRefType}
    (h : Relation.ReflTransGen (Sub Δ) t (.refv rt)) : (∃ rt', t = .refv rt') ∨ t = .botv :=
  rtg_down (S := fun t => (∃ rt', t = .refv rt') ∨ t = .botv) (fun a b hab hb => by
    rcases hb with ⟨rt', rfl⟩ | rfl <;> cases hab <;> simp) h (.inl ⟨_, rfl⟩)

theorem ValTo.num {s : Store H} {Δ : TypeCtx} {v : Val} {n : NumType} (h : ValTo s Δ v (.num n)) :
    ∃ b, v = .num ⟨n, b⟩ := by
  obtain ⟨t₀, hv, hc⟩ := h
  rcases sub_num_inv hc with rfl | rfl
  · cases hv with
    | num v => exact ⟨v.bits, rfl⟩
  · cases hv

theorem ValTo.i32 {s : Store H} {Δ : TypeCtx} {v : Val} (h : ValTo s Δ v Ty.i32) :
    ∃ c, v = Val.i32 c :=
  ValTo.num (n := .int .i32) h

theorem ValTo.ref {s : Store H} {Δ : TypeCtx} {v : Val} {rt : CRefType} (h : ValTo s Δ v (.refv rt)) :
    ∃ r, v = .ref r := by
  obtain ⟨t₀, hv, hc⟩ := h
  rcases sub_ref_inv hc with ⟨rt', rfl⟩ | rfl
  · cases hv with
    | ref h => exact ⟨_, rfl⟩
  · cases hv

theorem ValTo.valOk {s : Store H} {Δ : TypeCtx} {v : Val} {t : CValType} (h : ValTo s Δ v t) :
    ∃ t₀, ValOk s v t₀ := ⟨_, h.choose_spec.1⟩

/-- Numeric and vector value types: subtyping chains into them are trivial. -/
def numVec : CValType → Bool
  | .num _ => true
  | .vec _ => true
  | _ => false

theorem ValTo.valOk_of_numVec {s : Store H} {Δ : TypeCtx} {v : Val} {t : CValType}
    (h : ValTo s Δ v t) (ht : numVec t = true) : ValOk s v t := by
  obtain ⟨t₀, hv, hc⟩ := h
  cases t with
  | num n =>
    rcases sub_num_inv hc with rfl | rfl
    · exact hv
    · cases hv
  | vec n =>
    rcases sub_vec_inv hc with rfl | rfl
    · exact hv
    · cases hv
  | _ => simp [numVec] at ht

theorem ValsTo.of_numVec {s : Store H} {Δ : TypeCtx} {vs : List Val} {ts : List CValType}
    (h : ValsTo s Δ vs ts) (hts : ∀ t ∈ ts, numVec t = true) : List.Forall₂ (ValOk s) vs ts := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih =>
    exact .cons (ha.valOk_of_numVec (hts _ (by simp)))
      (ih fun t ht => hts t (by simp [ht]))

/-! ## Stepping in a context -/

section Lift

variable {P : Profile} {host : HostSemantics H}

theorem Step.inCtx {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin} {c' : Config H}
    (h : Step P host ⟨s, f, is⟩ c') : ∃ c'', Step P host ⟨s, f, vals vs ++ is ++ rest⟩ c'' := by
  rcases c' with ⟨s', f', is'⟩
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact ⟨_, .ctxtInstrs h hne⟩
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    exact ⟨_, by simpa [vals] using h⟩

/-- Lift a step of `vals vs₂ ++ is` to `vals (vs₁ ++ vs₂) ++ is ++ rest`. -/
theorem Step.inCtx' {s : Store H} {f : Frame} {vs₁ vs₂ : List Val} {is rest : List Admin}
    (h : ∃ c', Step P host ⟨s, f, vals vs₂ ++ is⟩ c') :
    ∃ c'', Step P host ⟨s, f, vals (vs₁ ++ vs₂) ++ is ++ rest⟩ c'' := by
  obtain ⟨c', h⟩ := h
  obtain ⟨c'', h'⟩ := Step.inCtx (vs := vs₁) (rest := rest) h
  exact ⟨c'', by simpa [vals_append, List.append_assoc] using h'⟩

end Lift

/-! ## Decomposition of code -/

theorem decompose (is : List Admin) :
    (∃ vs, is = vals vs) ∨ ∃ vs a rest, is = vals vs ++ a :: rest ∧ a.val? = none := by
  induction is with
  | nil => exact .inl ⟨[], rfl⟩
  | cons a is ih =>
    cases ha : a.val? with
    | none => exact .inr ⟨[], a, is, rfl, ha⟩
    | some v =>
      obtain rfl := Admin.eq_of_val? ha
      rcases ih with ⟨vs, rfl⟩ | ⟨vs, b, rest, rfl, hb⟩
      · exact .inl ⟨v :: vs, rfl⟩
      · exact .inr ⟨v :: vs, b, rest, rfl, hb⟩

theorem sizeOf_lt_of_mid {a : Admin} {l₁ l₂ : List Admin} : sizeOf a < sizeOf (l₁ ++ a :: l₂) :=
  List.sizeOf_lt_of_mem (by simp)

/-! ## Contexts of running code -/

end Silmaril.Wasm.Execution.Core

namespace Silmaril.Wasm.Validation

/-- The context with the control fields and locals erased. -/
def Context.frameView (C : Context) : Context :=
  { C with labels := [], return_ := none, locals := [] }

theorem Context.eq_of_frameView {C C' : Context} (h : C.frameView = C'.frameView) :
    C = { C' with labels := C.labels, return_ := C.return_, locals := C.locals } := by
  cases C; cases C'
  simp only [Context.frameView, Context.mk.injEq] at h ⊢
  simp_all

@[simp] theorem Context.withLabel_frameView (C : Context) (ts : List CValType) :
    (C.withLabel ts).frameView = C.frameView := rfl

@[simp] theorem Context.withLabel_locals (C : Context) (ts : List CValType) :
    (C.withLabel ts).locals = C.locals := rfl

@[simp] theorem Context.withLabel_labels (C : Context) (ts : List CValType) :
    (C.withLabel ts).labels = ts :: C.labels := rfl

@[simp] theorem Context.withLabel_return (C : Context) (ts : List CValType) :
    (C.withLabel ts).return_ = C.return_ := rfl

@[simp] theorem Context.withLabel_toTypeCtx' (C : Context) (ts : List CValType) :
    (C.withLabel ts).toTypeCtx = C.toTypeCtx := rfl

theorem Context.withLocals_frameView :
    ∀ (C : Context) (xs : List Nat) (lts : List LocalType),
      (C.withLocals xs lts).frameView = C.frameView
  | C, x :: xs, lt :: lts => by
    rw [Context.withLocals, Context.withLocals_frameView]; rfl
  | _, [], _ => by simp [Context.withLocals]
  | _, _ :: _, [] => by simp [Context.withLocals]

theorem Context.withLocals_other :
    ∀ (C : Context) (xs : List Nat) (lts : List LocalType),
      (C.withLocals xs lts).labels = C.labels ∧ (C.withLocals xs lts).return_ = C.return_ ∧
        (C.withLocals xs lts).toTypeCtx = C.toTypeCtx ∧
        (C.withLocals xs lts).locals.length = C.locals.length
  | C, x :: xs, lt :: lts => by
    rw [Context.withLocals]
    have := Context.withLocals_other (C.setLocal x lt) xs lts
    simp only [this]
    simp [Context.setLocal]
  | _, [], _ => by simp [Context.withLocals]
  | _, _ :: _, [] => by simp [Context.withLocals]

theorem Context.withLocals_get :
    ∀ (C : Context) (xs : List Nat) (lts : List LocalType) (y : Nat), y ∉ xs →
      (C.withLocals xs lts).locals[y]? = C.locals[y]?
  | C, x :: xs, lt :: lts, y, hy => by
    rw [Context.withLocals, Context.withLocals_get _ xs lts y (fun h => hy (by simp [h]))]
    have hxy : x ≠ y := fun h => hy (by simp [h])
    simp [Context.setLocal, hxy]
  | _, [], _, _, _ => by simp [Context.withLocals]
  | _, _ :: _, [], _, _ => by simp [Context.withLocals]

@[simp] theorem Context.initLocals_frameView (C : Context) (xs : List Nat) :
    (C.initLocals xs).frameView = C.frameView := Context.withLocals_frameView _ _ _

@[simp] theorem Context.initLocals_locals_length (C : Context) (xs : List Nat) :
    (C.initLocals xs).locals.length = C.locals.length := (Context.withLocals_other _ _ _).2.2.2

end Silmaril.Wasm.Validation

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- The invariant relating the context `C` of running code to the frame `f`. -/
structure CtxOk (s : Store H) (f : Frame) (C : Context) : Prop where
  frame : ∃ Cf, FrameOk s f Cf ∧ C.frameView = Cf.frameView ∧ C.locals.length = Cf.locals.length
  len : C.locals.length = f.locals.length
  set : ∀ (x : Nat) t, C.locals[x]? = some ⟨.set, t⟩ → ∃ v, f.locals[x]? = some (some v)

theorem CtxOk.withLabel {s : Store H} {f : Frame} {C : Context} (h : CtxOk s f C)
    (ts : List CValType) : CtxOk s f (C.withLabel ts) :=
  ⟨h.frame, h.len, h.set⟩

theorem CtxOk.initLocals {s : Store H} {f : Frame} {C : Context} {xs : List Nat} (h : CtxOk s f C)
    (hxs : ∀ x ∈ xs, ∃ t, C.locals[x]? = some ⟨.set, t⟩) : CtxOk s f (C.initLocals xs) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨Cf, hf, hv, hl⟩ := h.frame
    exact ⟨Cf, hf, by simpa using hv, by simpa using hl⟩
  · simpa using h.len
  · intro y t hy
    by_cases hyx : y ∈ xs
    · obtain ⟨t', ht'⟩ := hxs y hyx
      exact h.set y t' ht'
    · rw [Context.initLocals, Context.withLocals_get _ _ _ _ hyx] at hy
      exact h.set y t hy

theorem ModuleInstOk.ctx_fields {s : Store H} {m : ModuleInst} {C : Context}
    (h : ModuleInstOk s m C) :
    C.locals = [] ∧ C.labels = [] ∧ C.return_ = none ∧ C.types = m.types := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem forall₂_getElem?_right {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) {x : Nat} {b : β} (hb : m[x]? = some b) :
    ∃ a, l[x]? = some a ∧ R a b := by
  induction h generalizing x with
  | nil => simp at hb
  | cons hab _ ih =>
    cases x with
    | zero => simp at hb; subst hb; exact ⟨_, rfl, hab⟩
    | succ x => simpa using ih (by simpa using hb)

theorem FrameOk.ctx_fields {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C) :
    C.labels = [] ∧ C.return_ = none ∧ C.locals.length = f.locals.length := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  obtain ⟨h0, h1, h2, -⟩ := hm.ctx_fields
  exact ⟨h1, h2, by simp [h0, hl.length_eq]⟩

theorem FrameOk.set {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C) :
    ∀ (x : Nat) t, C.locals[x]? = some ⟨.set, t⟩ → ∃ v, f.locals[x]? = some (some v) := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  obtain ⟨h0, -, -, -⟩ := hm.ctx_fields
  intro x t hx
  simp only [h0, List.nil_append] at hx
  obtain ⟨a, ha, hv⟩ := forall₂_getElem?_right hl hx
  cases hv with
  | set hv => exact ⟨_, ha⟩

theorem CtxOk.ofFrame {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C)
    (ts : List CValType) : CtxOk s f { C with return_ := some ts } :=
  ⟨⟨C, hf, rfl, rfl⟩, (FrameOk.ctx_fields hf).2.2, hf.set⟩

theorem CtxOk.ofFrame₀ {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C) :
    CtxOk s f C :=
  ⟨⟨C, hf, rfl, rfl⟩, (FrameOk.ctx_fields hf).2.2, hf.set⟩

theorem CtxOk.stateOk {s : Store H} {f : Frame} {C : Context} (hs : StoreOk s) (h : CtxOk s f C) :
    ∃ Cf, StateOk s f Cf ∧
      C = { Cf with labels := C.labels, return_ := C.return_, locals := C.locals } := by
  obtain ⟨Cf, hf, hv, -⟩ := h.frame
  exact ⟨Cf, ⟨hs, hf⟩, Context.eq_of_frameView hv⟩

theorem CtxOk.types {s : Store H} {f : Frame} {C : Context} (h : CtxOk s f C) :
    C.types = f.module.types := by
  obtain ⟨Cf, hf, hv, -⟩ := h.frame
  have h1 := Context.eq_of_frameView hv
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  rw [h1]
  exact hm.ctx_fields.2.2.2

/-! ## Transport of family typings to the frame context -/

section Transport

variable {C : Context} {L : List (List CValType)} {R : Option (List CValType)}
  {ls : List LocalType} {i : Instr} {it : InstrType}

theorem InstrTypeOk.plain_transport {t₁ t₂ : List CValType}
    (h : InstrTypeOk { C with labels := L, return_ := R, locals := ls } (.plain t₁ t₂)) :
    InstrTypeOk C (.plain t₁ t₂) :=
  ⟨h.1, h.2.1, by simp⟩

theorem ParametricInstrOk.transport
    (h : ParametricInstrOk { C with labels := L, return_ := R, locals := ls } i it) :
    ParametricInstrOk C i it := by
  cases h
  all_goals first
    | (constructor <;> assumption)
    | (constructor; exact InstrTypeOk.plain_transport ‹_›)

theorem NumericInstrOk.transport
    (h : NumericInstrOk { C with labels := L, return_ := R, locals := ls } i it) :
    NumericInstrOk C i it := by
  cases h <;> (constructor <;> assumption)

theorem VectorInstrOk.transport
    (h : VectorInstrOk { C with labels := L, return_ := R, locals := ls } i it) :
    VectorInstrOk C i it := by
  cases h <;> (constructor <;> assumption)

theorem MemoryInstrOk.transport
    (h : MemoryInstrOk { C with labels := L, return_ := R, locals := ls } i it) :
    MemoryInstrOk C i it := by
  cases h <;> (constructor <;> assumption)

theorem TableInstrOk.transport
    (h : TableInstrOk { C with labels := L, return_ := R, locals := ls } i it) :
    TableInstrOk C i it := by
  cases h <;> (constructor <;> assumption)

theorem RefInstrOk.transport
    (h : RefInstrOk { C with labels := L, return_ := R, locals := ls } i it) :
    RefInstrOk C i it := by
  cases h <;> (constructor <;> assumption)

end Transport

/-! ## Retyping family instructions at the types of their operands

Sequence typing only gives the operands up to a chain of subtypings in the
typing context; the family progress lemmas want them typed at the parameter
types of (some typing of) the instruction. -/

section Retype

variable {s : Store H} {f : Frame} {C : Context} {i : Instr} {t₁ t₂ : List CValType}
  {xs : List Nat} {vs : List Val}

theorem NumericInstrOk.retype (_hst : StateOk s f C) (hi : NumericInstrOk C i ⟨t₁, xs, t₂⟩)
    (hv : ValsTo s C.toTypeCtx vs t₁) :
    ∃ t₁' xs' t₂', NumericInstrOk C i ⟨t₁', xs', t₂'⟩ ∧ List.Forall₂ (ValOk s) vs t₁' := by
  refine ⟨_, _, _, hi, ValsTo.of_numVec hv ?_⟩
  cases hi <;> simp [numVec]

theorem VectorInstrOk.retype (_hst : StateOk s f C) (hi : VectorInstrOk C i ⟨t₁, xs, t₂⟩)
    (hv : ValsTo s C.toTypeCtx vs t₁) :
    ∃ t₁' xs' t₂', VectorInstrOk C i ⟨t₁', xs', t₂'⟩ ∧ List.Forall₂ (ValOk s) vs t₁' := by
  refine ⟨_, _, _, hi, ValsTo.of_numVec hv ?_⟩
  cases hi <;> simp [numVec, Ty.i32, Ty.v128]

theorem MemoryInstrOk.retype (_hst : StateOk s f C) (hi : MemoryInstrOk C i ⟨t₁, xs, t₂⟩)
    (hv : ValsTo s C.toTypeCtx vs t₁) :
    ∃ t₁' xs' t₂', MemoryInstrOk C i ⟨t₁', xs', t₂'⟩ ∧ List.Forall₂ (ValOk s) vs t₁' := by
  refine ⟨_, _, _, hi, ValsTo.of_numVec hv ?_⟩
  cases hi <;> simp [numVec, Ty.i32, Ty.v128, AddrType.valType]

-- `RefInstrOk.retype` is in `RefRetypeClosed.lean`.

end Retype

/-! ## Value sequences set no new locals -/

theorem AdminOk.inits_of_val {s : Store H} {C : Context} {a : Admin} {it : InstrType} {v : Val}
    (h : AdminOk s C a it) (hv : a.val? = some v) : it.inits = [] := by
  cases h with
  | plain hi =>
    cases hi with
    | parametric h => cases h <;> rfl
    | numeric h => cases h <;> rfl
    | vector h => cases h <;> rfl
    | «variable» h => cases h <;> first | rfl | simp [Admin.val?] at hv
    | memory h => cases h <;> rfl
    | table h => cases h <;> rfl
    | reference h => cases h <;> rfl
    | _ => rfl
  | ref => rfl
  | _ => first | rfl | simp [Admin.val?] at hv

@[simp] theorem Context.initLocals_nil (C : Context) : C.initLocals [] = C := rfl

theorem AdminsOk.vals_inits_aux {s : Store H} {C : Context} {code : List Admin} {it : InstrType}
    (h : AdminsOk s C code it) : ∀ vs, vals vs = code →
      ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩ := by
  refine AdminsOk.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun C code it _ => ∀ vs, vals vs = code →
      ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  iterate 9 (· intros; trivial)
  · intro C vs hc; simp
  · intro C a it ha _ vs hc x hx
    cases vs with
    | nil => simp [vals] at hc
    | cons v vs =>
      simp only [vals, List.map_cons, List.cons.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rw [AdminOk.inits_of_val ha (Admin.val?_toAdmin v)] at hx
      simp at hx
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ vs hc x hx'
    obtain ⟨l₁, l₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp hc
    rcases List.mem_append.mp hx' with h | h
    · exact ih₁ l₁ e₁ x h
    · by_cases hm : x ∈ xs₁
      · exact ih₁ l₁ e₁ x hm
      · obtain ⟨t, ht⟩ := ih₂ l₂ e₂ x h
        exact ⟨t, by rw [← ht, Context.initLocals, Context.withLocals_get _ _ _ _ hm]⟩
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha hx hs _ ih vs hc
    cases vs with
    | nil => simp [vals] at hc
    | cons v vs =>
      simp only [vals, List.map_cons, List.cons.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      have h0 := AdminOk.inits_of_val ha (Admin.val?_toAdmin v)
      simp only at h0
      subst h0
      intro x hx'
      simp only [List.nil_append] at hx'
      exact ih vs hc x hx'
  · intro C as it₀ it' h hs hok ih vs hc x hx
    by_cases hx' : x ∈ it₀.inits
    · exact ih vs hc x hx'
    · exact hs.2.2 x hx hx'
  · intro C as ts t₁ t₂ xs h hok ih vs hc
    exact ih vs hc

theorem AdminsOk.vals_inits {s : Store H} {C : Context} {vs : List Val} {it : InstrType}
    (h : AdminsOk s C (vals vs) it) : ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩ :=
  h.vals_inits_aux vs rfl

/-! ## The exception hierarchy is closed downwards -/

/-- Heap types below `exn`. -/
def exnDown : {k : TKind} → Ty k → Bool
  | _, .abs .exn => true
  | _, .abs .noexn => true
  | _, .bot => true
  | _, _ => false

def isExnT : {k : TKind} → Ty k → Bool
  | _, .abs .exn => true
  | _, _ => false

def isNoexnT : {k : TKind} → Ty k → Bool
  | _, .abs .noexn => true
  | _, _ => false

theorem exn_aux_bot_case {a top : AbsHeapType} (h' : CHeapType) (hb : h' ≠ .bot)
    (ih : (exnDown (Ty.abs top) = true → exnDown h' = true) ∧
      (isExnT h' = true → isExnT (Ty.abs top) = true) ∧
      (isNoexnT h' = true → isExnT (Ty.abs top) = true ∨ isNoexnT (Ty.abs top) = true))
    (ha1 : isExnT (Ty.abs a) = false) (ha2 : isNoexnT (Ty.abs a) = false)
    (ht1 : isExnT (Ty.abs top) = false) (ht2 : isNoexnT (Ty.abs top) = false) :
    (exnDown h' = true → exnDown (Ty.abs a) = true) ∧ (isExnT (Ty.abs a) = true → isExnT h' = true) ∧
      (isNoexnT (Ty.abs a) = true → isExnT h' = true ∨ isNoexnT h' = true) := by
  refine ⟨fun hd => ?_, by simp [ha1], by simp [ha2]⟩
  exfalso
  cases h' with
  | abs b =>
    cases b <;> simp [exnDown] at hd
    · have := ih.2.1 rfl; simp_all
    · have := ih.2.2 rfl; simp_all
  | bot => exact hb rfl
  | use u => simp [exnDown] at hd

theorem Sub.exn_aux {Δ : TypeCtx} {k : TKind} {a b : Ty k} (h : Sub Δ a b) :
    (exnDown b = true → exnDown a = true) ∧ (isExnT a = true → isExnT b = true) ∧
      (isNoexnT a = true → isExnT b = true ∨ isNoexnT b = true) := by
  apply Silmaril.Wasm.Validation.Sub.rec (motive_1 := fun _ _ _ _ => True) (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ a b _ => (exnDown b = true → exnDown a = true) ∧
      (isExnT a = true → isExnT b = true) ∧
      (isNoexnT a = true → isExnT b = true ∨ isNoexnT b = true)) (t := h)
  case heapTrans =>
    intro _ _ _ _ hok h1 h2 _ ih1 ih2
    exact ⟨fun hb => ih1.1 (ih2.1 hb), fun ha => ih2.2.1 (ih1.2.1 ha),
      fun ha => (ih1.2.2 ha).elim (fun he => .inl (ih2.2.1 he)) (fun hn => ih2.2.2 hn)⟩
  case none => intro _ _ hs hb ih; exact exn_aux_bot_case _ hb ih rfl rfl rfl rfl
  case nofunc => intro _ _ hs hb ih; exact exn_aux_bot_case _ hb ih rfl rfl rfl rfl
  case noextern => intro _ _ hs hb ih; exact exn_aux_bot_case _ hb ih rfl rfl rfl rfl
  case noexn =>
    intro _ h' hs hb ih
    refine ⟨by simp [exnDown], by simp [isExnT], fun _ => ?_⟩
    have := ih.1 (by simp [exnDown])
    cases h' with
    | abs a => cases a <;> simp_all [exnDown, isExnT, isNoexnT]
    | bot => exact absurd rfl hb
    | use u => simp [exnDown] at this
  case heapRefl => intro _ _; exact ⟨id, id, fun h => .inr h⟩
  all_goals intros
  all_goals first
    | trivial
    | simp [exnDown, isExnT, isNoexnT]

/-! ## Store and module inversions -/

section Inversions

variable {s : Store H} {f : Frame} {C : Context}

/-- Along declared supertypes of a valid defined type the fuel strictly decreases. -/
theorem reach_eq_or_fuel_lt {Δ : TypeCtx} (hΔ : Δ.Ok) {d e : DefType} (h : Δ.Reach d e) :
    TyOk Δ d → d = e ∨ Δ.fuel e < Δ.fuel d := by
  induction h with
  | refl => intro _; exact .inl rfl
  | step hu hr _ ih =>
    intro hd
    obtain ⟨hok, hlt, -⟩ := TypeCtx.super_step hΔ hd hu hr
    rcases ih hok with rfl | h
    · exact .inr hlt
    · exact .inr (by omega)

/-- Mutual subtyping of valid defined types in the empty context is equality. -/
theorem Sub.def_antisymm_empty {d₁ d₂ : DefType} (h₁ : TyOk {} d₁) (h₂ : TyOk {} d₂)
    (s₁ : Sub {} d₁ d₂) (s₂ : Sub {} d₂ d₁) : d₁ = d₂ := by
  have c₁ : ({} : TypeCtx).checkDef d₁ d₂ = true :=
    Sub.check_complete TypeCtx.ok_empty rfl s₁ h₁ h₂
  have c₂ : ({} : TypeCtx).checkDef d₂ d₁ = true :=
    Sub.check_complete TypeCtx.ok_empty rfl s₂ h₂ h₁
  obtain ⟨e₁, r₁, q₁⟩ := TypeCtx.checkDef_exists c₁
  obtain ⟨e₂, r₂, q₂⟩ := TypeCtx.checkDef_exists c₂
  simp only [Ty.clos_nil] at q₁ q₂
  subst q₁ q₂
  rcases reach_eq_or_fuel_lt TypeCtx.ok_empty r₁ h₁ with h | h
  · exact h
  · rcases reach_eq_or_fuel_lt TypeCtx.ok_empty r₂ h₂ with h' | h'
    · exact h'.symm
    · omega

/-- A tag address is typed exactly by its instance's type. -/
theorem ExternAddrOk.tag_inv (hs : StoreOk s) {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.tag a) xt) : ∃ ti, s.tags[a]? = some ti ∧ xt = .tag ti.type := by
  generalize hx : ExternAddr.tag a = xa at h
  induction h with
  | tag h => cases hx; exact ⟨_, h, rfl⟩
  | sub _ hok hsub ih =>
    obtain ⟨ti, hti, rfl⟩ := ih hx
    refine ⟨ti, hti, ?_⟩
    cases hsub with
    | tag ht =>
      cases hok with
      | tag hk =>
        have h₁ : TyOk {} ti.type := (hs.tags ti (List.mem_of_getElem? hti)).1
        rw [Sub.def_antisymm_empty h₁ hk.1 ht.1 ht.2]
  | _ => cases hx

/-- `throw`: the tag exists and its parameter count matches the operands. -/
theorem throw_inv {x : TagIdx} {d : DefType} {ts : Ty (.list .val)} {vs : List Val}
    (hst : StateOk s f C) (hx : C.tags[x.toNat]? = some d) (he : Expand d (.func ts .nil))
    (hv : ValsTo s C.toTypeCtx vs ts.toList) :
    ∃ ta ti ts', s.tag? f x = some (ta, ti) ∧ Expand ti.type (.func ts' .nil) ∧
      vs.length = ts'.length := by
  obtain ⟨hs, C₀, lts, hm, -, rfl⟩ := hst
  cases hm with
  | mk _ htags =>
    obtain ⟨a, ha, hxa⟩ := forall₂_getElem?_right htags hx
    obtain ⟨ti, hti, hte⟩ := ExternAddrOk.tag_inv hs hxa
    cases hte
    exact ⟨a, ti, _, by simp [Store.tag?, ha, hti], he, hv.length_eq⟩

theorem RefOk.exn_inv {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∀ n hh, rt = .ref n hh → exnDown hh = true → r = .null ∨ ∃ a, r = .exn a := by
  induction h with
  | null => intros; exact .inl rfl
  | exn _ => intros; exact .inr ⟨_, rfl⟩
  | sub h hok hs ih =>
    intro n hh e hd
    subst e
    cases hs with
    | refNonNull h' => exact ih _ _ rfl ((Sub.exn_aux h').1 hd)
    | refNull h' => exact ih _ _ rfl ((Sub.exn_aux h').1 hd)
  | _ => intro n hh e hd; cases e; simp [exnDown, Ty.defHeap] at hd

/-- `throw_ref` on a typed reference: null or an exception address. -/
theorem throwRef_inv {r : Ref} (_hst : StateOk s f C)
    (hv : ValTo s C.toTypeCtx (.ref r) (Ty.refT true (.abs .exn))) :
    r = .null ∨ ∃ a, r = .exn a := by
  obtain ⟨t₀, hv0, hc⟩ := hv
  have key := rtg_down (S := fun t : CValType => t = .botv ∨
      ∃ n h, t = .refv (.ref n h) ∧ exnDown h = true) (fun a b hab hb => by
      rcases hb with rfl | ⟨n, h, rfl, hd⟩
      · (cases hab; simp)
      · cases hab with
        | refv h' =>
          cases h' with
          | refNonNull hh => exact .inr ⟨_, _, rfl, (Sub.exn_aux hh).1 hd⟩
          | refNull hh => exact .inr ⟨_, _, rfl, (Sub.exn_aux hh).1 hd⟩
        | botv => exact .inl rfl) hc (.inr ⟨true, _, rfl, rfl⟩)
  rcases key with rfl | ⟨n, h, rfl, hd⟩
  · cases hv0
  · cases hv0 with
    | ref hr => exact RefOk.exn_inv hr _ _ rfl hd

theorem ExternAddrOk.func_inv {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.func a) xt) : ∃ fi, s.funcs[a]? = some fi := by
  generalize hx : ExternAddr.func a = xa at h
  induction h with
  | func h => cases hx; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih hx
  | _ => cases hx

theorem ExternAddrOk.global_inv {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.global a) xt) : ∃ gi, s.globals[a]? = some gi := by
  generalize hx : ExternAddr.global a = xa at h
  induction h with
  | global h => cases hx; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih hx
  | _ => cases hx

theorem StateOk.func? {x : FuncIdx} {d : DefType} (hst : StateOk s f C)
    (hx : C.funcs[x.toNat]? = some d) :
    ∃ a fi, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi := by
  obtain ⟨-, C₀, lts, hm, -, rfl⟩ := hst
  cases hm with
  | mk _ _ _ hfuncs =>
    obtain ⟨a, ha, hx⟩ := forall₂_getElem?_right hfuncs hx
    obtain ⟨fi, hfi⟩ := ExternAddrOk.func_inv hx
    exact ⟨a, fi, ha, hfi⟩

theorem ExternAddrOk.table_inv {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.table a) xt) : ∃ ti, s.tables[a]? = some ti := by
  generalize hx : ExternAddr.table a = xa at h
  induction h with
  | table h => cases hx; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih hx
  | _ => cases hx

theorem StateOk.table? {x : TableIdx} {tt : CTableType} (hst : StateOk s f C)
    (hx : C.tables[x.toNat]? = some tt) : ∃ a ti, s.table? f x = some (a, ti) := by
  obtain ⟨-, C₀, lts, hm, -, rfl⟩ := hst
  cases hm with
  | mk _ _ _ _ _ htables =>
    obtain ⟨a, ha, hx⟩ := forall₂_getElem?_right htables hx
    obtain ⟨ti, hti⟩ := ExternAddrOk.table_inv hx
    exact ⟨a, ti, by simp [Store.table?, ha, hti]⟩

theorem StateOk.global? {x : GlobalIdx} {g : CGlobalType} (hst : StateOk s f C)
    (hx : C.globals[x.toNat]? = some g) : ∃ a gi, s.global? f x = some (a, gi) := by
  obtain ⟨-, C₀, lts, hm, -, rfl⟩ := hst
  cases hm with
  | mk _ _ hglobals =>
    obtain ⟨a, ha, hx⟩ := forall₂_getElem?_right hglobals hx
    obtain ⟨gi, hgi⟩ := ExternAddrOk.global_inv hx
    exact ⟨a, gi, by simp [Store.global?, ha, hgi]⟩

theorem StateOk.types (hst : StateOk s f C) : C.types = f.module.types := by
  obtain ⟨-, C₀, lts, hm, -, rfl⟩ := hst
  exact hm.ctx_fields.2.2.2

theorem blockType_of_types {bt : BlockType} {t₁ t₂ : List CValType}
    (ht : C.types = f.module.types) (h : BlockTypeOk C bt t₁ t₂) :
    ∃ t₁' t₂', f.module.blockType? bt = some (t₁', t₂') ∧ t₁'.length = t₁.length ∧
      t₂'.length = t₂.length := by
  cases h with
  | empty => exact ⟨[], [], rfl, rfl, rfl⟩
  | value _ => exact ⟨[], _, rfl, rfl, rfl⟩
  | typeIdx hd he =>
    rename_i x d ps rs
    refine ⟨ps.toList, rs.toList, ?_, rfl, rfl⟩
    have hd' : f.module.types[x.toNat]? = some d := by
      rw [← ht]; exact hd
    have he' := Expand.iff.1 he
    simp [ModuleInst.blockType?, hd', DefType.funcType?, he']

end Inversions

end Silmaril.Wasm.Execution.Core
