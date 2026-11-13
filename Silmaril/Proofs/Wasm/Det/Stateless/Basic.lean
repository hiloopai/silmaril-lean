module

public import Silmaril.Wasm.Det.Stateless.Defs

/-!
# Stateless code: basic lemmas (proofs)

Sequence lemmas for the run-time invariant (`okL`, `PairedFrom`, `lastOr`, `Blk`) and the
store relations (`Agree`, `Eff.app`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Stateless

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Det.Stateless

variable {H : Type} {A R W : Nat → Bool} {m : ModuleInst}

/-! ## `okL` -/

@[simp] theorem okL_nil : okL A R W m [] := trivial

@[simp] theorem okL_cons {x : Admin} {l : List Admin} :
    okL A R W m (x :: l) ↔ okA A R W m x ∧ okL A R W m l := Iff.rfl

@[simp] theorem okL_append {l₁ l₂ : List Admin} :
    okL A R W m (l₁ ++ l₂) ↔ okL A R W m l₁ ∧ okL A R W m l₂ := by
  induction l₁ with
  | nil => simp
  | cons x l ih => simp [ih, and_assoc]

@[simp] theorem okA_plain {i : Instr} :
    okA A R W m (.plain i) ↔ slInstr A R W m i = true ∨ rtPlain i = true := Iff.rfl

@[simp] theorem okA_ref {r : Ref} : okA A R W m (.ref r) := trivial

@[simp] theorem okA_callRefType {d : Validation.DefType} : okA A R W m (.callRefType d) := trivial

@[simp] theorem okA_returnCallRefType {d : Validation.DefType} :
    ¬ okA A R W m (.returnCallRefType d) := id

@[simp] theorem okA_label {n : Nat} {cont : List Instr} {body : List Admin} :
    okA A R W m (.label n cont body) ↔
      slInstrs A R W m cont = true ∧ okL A R W m body ∧ PairedFrom A none body := Iff.rfl

@[simp] theorem okA_handler {n : Nat} {cs : List Catch} {body : List Admin} :
    ¬ okA A R W m (.handler n cs body) := id

@[simp] theorem okA_frame {n : Nat} {fr : Frame} {body : List Admin} :
    okA A R W m (.frame n fr body) ↔ okL A R W fr.module body ∧ PairedFrom A none body :=
  Iff.rfl

@[simp] theorem okA_trap : okA A R W m .trap := trivial

@[simp] theorem okA_toAdmin (v : Val) : okA A R W m v.toAdmin := by
  cases v with
  | num nv =>
    obtain ⟨ty, b⟩ := nv
    cases ty with
    | int t => exact Or.inl rfl
    | float t => exact Or.inr rfl
  | vec b => exact Or.inr rfl
  | ref r => trivial

@[simp] theorem okL_vals (vs : List Val) : okL A R W m (vals vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨okA_toAdmin v, ih⟩

theorem okL_expression {is : List Instr} (h : slInstrs A R W m is = true) :
    okL A R W m (expression is) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    have h' : slInstr A R W m i = true ∧ slInstrs A R W m is = true := by
      simpa only [slInstrs, Bool.and_eq_true] using h
    exact ⟨Or.inl h'.1, ih h'.2⟩

@[simp] theorem okL_throwing (a : Nat) : okL A R W m (throwing a) :=
  ⟨trivial, Or.inr rfl, trivial⟩

@[simp] theorem okL_toAdmin (r : Result) : okL A R W m r.toAdmin := by
  cases r with
  | values vs => exact okL_vals vs
  | throw a => exact okL_throwing a
  | trap => exact ⟨trivial, trivial⟩

theorem okL_mono_module {m' : ModuleInst} {l : List Admin} (hm : m' = m)
    (h : okL A R W m l) : okL A R W m' l := hm ▸ h

/-! ## `lastOr` -/

@[simp] theorem lastOr_nil (p : Option Admin) : lastOr p [] = p := rfl

theorem lastOr_cons (p : Option Admin) (x : Admin) (l : List Admin) :
    lastOr p (x :: l) = lastOr (some x) l := by
  cases l with
  | nil => rfl
  | cons y l =>
    show ((x :: y :: l).getLast?).or p = ((y :: l).getLast?).or (some x)
    rw [List.getLast?_cons_cons]
    cases h : (y :: l).getLast? with
    | none => simp at h
    | some z => rfl

theorem lastOr_append (p : Option Admin) (l₁ l₂ : List Admin) :
    lastOr p (l₁ ++ l₂) = lastOr (lastOr p l₁) l₂ := by
  induction l₁ generalizing p with
  | nil => rfl
  | cons x l ih => rw [List.cons_append, lastOr_cons, lastOr_cons, ih]

@[simp] theorem lastOr_concat (p : Option Admin) (l : List Admin) (x : Admin) :
    lastOr p (l ++ [x]) = some x := by
  simp [lastOr]

@[simp] theorem lastOr_singleton (p : Option Admin) (x : Admin) : lastOr p [x] = some x := rfl

theorem blk_lastOr_mono {p p' : Option Admin} (l : List Admin) (hp : Blk A p → Blk A p')
    (h : Blk A (lastOr p l)) : Blk A (lastOr p' l) := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', x, rfl⟩
  · exact hp h
  · simpa using h

/-! ## `PairedFrom` -/

@[simp] theorem pairedFrom_nil (p : Option Admin) : PairedFrom A p [] := trivial

@[simp] theorem pairedFrom_cons {p : Option Admin} {x : Admin} {l : List Admin} :
    PairedFrom A p (x :: l) ↔ (isCRT x = true → Blk A p) ∧ PairedFrom A (some x) l := Iff.rfl

theorem pairedFrom_append {p : Option Admin} {l₁ l₂ : List Admin} :
    PairedFrom A p (l₁ ++ l₂) ↔ PairedFrom A p l₁ ∧ PairedFrom A (lastOr p l₁) l₂ := by
  induction l₁ generalizing p with
  | nil => simp
  | cons x l ih => rw [List.cons_append, pairedFrom_cons, pairedFrom_cons, ih, lastOr_cons,
      and_assoc]

theorem pairedFrom_mono {p p' : Option Admin} {l : List Admin} (h : PairedFrom A p l)
    (hp : Blk A p → Blk A p') : PairedFrom A p' l := by
  cases l with
  | nil => trivial
  | cons x l => exact ⟨fun hx => hp (h.1 hx), h.2⟩

@[simp] theorem isCRT_plain (i : Instr) : isCRT (.plain i) = false := rfl
@[simp] theorem isCRT_ref (r : Ref) : isCRT (.ref r) = false := rfl
@[simp] theorem isCRT_callRefType (d : Validation.DefType) : isCRT (.callRefType d) = true := rfl
@[simp] theorem isCRT_label (n : Nat) (cont : List Instr) (b : List Admin) :
    isCRT (.label n cont b) = false := rfl
@[simp] theorem isCRT_frame (n : Nat) (f : Frame) (b : List Admin) :
    isCRT (.frame n f b) = false := rfl
@[simp] theorem isCRT_trap : isCRT .trap = false := rfl

@[simp] theorem isCRT_toAdmin (v : Val) : isCRT v.toAdmin = false := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem pairedFrom_vals (p : Option Admin) (vs : List Val) : PairedFrom A p (vals vs) := by
  induction vs generalizing p with
  | nil => trivial
  | cons v vs ih => exact ⟨fun h => absurd h (by simp), ih _⟩

@[simp] theorem pairedFrom_expression (p : Option Admin) (is : List Instr) :
    PairedFrom A p (expression is) := by
  induction is generalizing p with
  | nil => trivial
  | cons i is ih => exact ⟨fun h => absurd h (by simp [isCRT]), ih _⟩

@[simp] theorem pairedFrom_vals_expression (p : Option Admin) (vs : List Val) (is : List Instr) :
    PairedFrom A p (vals vs ++ expression is) :=
  pairedFrom_append.mpr ⟨pairedFrom_vals _ _, pairedFrom_expression _ _⟩

@[simp] theorem pairedFrom_vals_plain (p : Option Admin) (vs : List Val) (i : Instr)
    (l : List Admin) :
    PairedFrom A p (vals vs ++ .plain i :: l) ↔ PairedFrom A (some (.plain i)) l := by
  rw [pairedFrom_append, pairedFrom_cons]
  simp

@[simp] theorem pairedFrom_throwing (p : Option Admin) (a : Nat) :
    PairedFrom A p (throwing a) :=
  ⟨fun h => absurd h (by simp [isCRT]), fun h => absurd h (by simp [isCRT]), trivial⟩

@[simp] theorem pairedFrom_toAdmin (p : Option Admin) (r : Result) :
    PairedFrom A p r.toAdmin := by
  cases r with
  | values vs => exact pairedFrom_vals p vs
  | throw a => exact pairedFrom_throwing p a
  | trap => exact ⟨fun h => absurd h (by simp [isCRT]), trivial⟩

/-- A sequence not starting with `CALL_REF dt` does not depend on its predecessor. -/
theorem pairedFrom_head {p p' : Option Admin} {l : List Admin} (h : PairedFrom A p l)
    (hn : ¬ Blk A p) : PairedFrom A p' l := by
  cases l with
  | nil => trivial
  | cons x l =>
    refine ⟨fun hx => absurd (h.1 hx) hn, h.2⟩

/-! ## Stores -/

theorem Agree.refl (R : Nat → Bool) (s : Store H) : Agree R s s :=
  ⟨rfl, fun _ _ => rfl⟩

theorem Agree.symm {t s : Store H} (h : Agree R t s) : Agree R s t :=
  ⟨h.1.symm, fun a ha => (h.2 a ha).symm⟩

theorem Agree.trans {t u s : Store H} (h₁ : Agree R t u) (h₂ : Agree R u s) : Agree R t s :=
  ⟨h₁.1.trans h₂.1, fun a ha => (h₁.2 a ha).trans (h₂.2 a ha)⟩

theorem Agree.anti {R' : Nat → Bool} {t s : Store H} (h : Agree R t s)
    (hR : ∀ a, R' a = true → R a = true) : Agree R' t s :=
  ⟨h.1, fun a ha => h.2 a (hR a ha)⟩

@[simp] theorem setGlobal_funcs (s : Store H) (a : Nat) (v : Val) :
    (s.setGlobal a v).funcs = s.funcs := rfl

theorem setGlobal_globals (s : Store H) (a : Nat) (v : Val) (b : Nat) :
    (s.setGlobal a v).globals[b]? =
      if a = b then (s.globals[b]?).map fun g => { g with value := v } else s.globals[b]? := by
  by_cases h : a = b <;> simp [Store.setGlobal, h]

@[simp] theorem Eff.app_funcs (e : Eff) (s : Store H) : (e.app s).funcs = s.funcs := by
  cases e <;> rfl

theorem Agree.app {t s : Store H} (e : Eff) (h : Agree R t s) : Agree R (e.app t) (e.app s) := by
  cases e with
  | keep => exact h
  | set a v =>
    refine ⟨h.1, fun b hb => ?_⟩
    show (t.setGlobal a v).globals[b]? = (s.setGlobal a v).globals[b]?
    rw [setGlobal_globals, setGlobal_globals, h.2 b hb]

/-- An effect writing only globals of `W` keeps everything else. -/
theorem Eff.outside {e : Eff} (he : e.Ok W) (s : Store H) : Outside W (e.app s) s := by
  cases e with
  | keep => exact Agree.refl _ s
  | set a v =>
    have hW : W a = true := he
    refine ⟨rfl, fun b hb => ?_⟩
    have hab : a ≠ b := fun h => by subst h; simp [hW] at hb
    show (s.setGlobal a v).globals[b]? = s.globals[b]?
    simp [setGlobal_globals, hab]

end Silmaril.Proofs.Wasm.Det.Stateless
