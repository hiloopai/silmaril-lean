module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegRunDet

/-!
# Runs through `Good` instructions are forced

* `GTo P c d`: a run from `c` to `d` each of whose configurations before `d` has a `Good` first
  non-value (`GoodHead`); it is a forced run (`GTo.detTo`), and lifts under a value prefix and a
  suffix (`GTo.lift`).
* `Inv code`: the code consists of values and `Good` or constant instructions (`OkAdmin`). A
  host-free step from such code is at a `Good` head, keeps the frame, and leaves code of the
  same kind or code whose first non-value is `TRAP` (`step_shape`).

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Proofs.Wasm.Game.Choice

/-- The first non-value of the configuration is a `Good` instruction. -/
def GoodHead (c : Config Nat) : Prop :=
  ∃ W i R, c.code = vals W ++ .plain i :: R ∧ Good i

/-- A run through configurations with `Good` first non-values. -/
inductive GTo (P : Profile) : Config Nat → Config Nat → Prop where
  | refl (c : Config Nat) : GTo P c c
  | step {c c' d : Config Nat} (h : Step P noHost c c') (hg : GoodHead c) (rest : GTo P c' d) :
      GTo P c d

theorem good_val_none {i : Instr} (hg : Good i) : (Admin.plain i).val? = none := by
  cases i <;> first | exact hg.elim | rfl

theorem good_not_callRef {i : Instr} (hg : Good i) : (Admin.plain i).isCallRef = false := by
  cases i <;> first | exact hg.elim | rfl

theorem goodHead_decompose {c : Config Nat} (h : GoodHead c) : decompose? c.store c.code = none := by
  obtain ⟨W, i, R, hc, hg⟩ := h
  rw [hc]
  refine decompose?_vals_cons_none (good_val_none hg) fun vs rest => ?_
  have hcr := good_not_callRef hg
  simp only [decompHead, hcr, Bool.false_eq_true, ite_false]

theorem goodHead_not_result {c : Config Nat} (h : GoodHead c) (r : Result) :
    c.code ≠ r.toAdmin := by
  obtain ⟨W, i, R, hc, hg⟩ := h
  intro e
  have hf : fnv c.code = (W, .plain i :: R) := by
    rw [hc]
    simp [fnv_cons_of_none (good_val_none hg)]
  rw [e] at hf
  cases r with
  | values vs =>
    have hv : fnv (vals vs) = (vs, []) := by simp
    rw [show (Result.values vs).toAdmin = vals vs from rfl, hv] at hf
    simp at hf
  | trap => simp [Result.toAdmin, fnv_cons_of_none (a := .trap) rfl] at hf
  | throw a =>
    have hi : i = .throwRef := by
      simp [Result.toAdmin, fnv, Admin.val?] at hf
      exact hf.2.1.symm
    rw [hi] at hg
    exact hg

theorem goodHead_uniq {P : Profile} {c c₁ c₂ : Config Nat} (h : GoodHead c)
    (h₁ : Step P noHost c c₁) (h₂ : Step P noHost c c₂) : c₂ = c₁ := by
  obtain ⟨W, i, R, hc, hg⟩ := h
  obtain ⟨s, f, code⟩ := c
  simp only at hc
  subst hc
  exact good_step_uniq hg h₂ h₁

/-- A run through `Good` heads is a forced run. -/
theorem GTo.detTo {P : Profile} {c d : Config Nat} (h : GTo P c d) : DetTo P c d := by
  induction h with
  | refl c => exact .refl c
  | step hs hg _ ih =>
    exact .step hs (fun e he => goodHead_uniq hg hs he) (goodHead_decompose hg)
      (goodHead_not_result hg) ih

theorem GTo.trans {P : Profile} {c d e : Config Nat} (h₁ : GTo P c d) (h₂ : GTo P d e) :
    GTo P c e := by
  induction h₁ with
  | refl => exact h₂
  | step hs hg _ ih => exact .step hs hg (ih h₂)

theorem GTo.single {P : Profile} {c c' : Config Nat} (h : Step P noHost c c') (hg : GoodHead c) :
    GTo P c c' := .step h hg (.refl _)

/-- Put a configuration under a value prefix and before a suffix. -/
def wrap (V : List Val) (js : List Admin) (c : Config Nat) : Config Nat :=
  ⟨c.store, c.frame, vals V ++ c.code ++ js⟩

theorem GoodHead.wrap {c : Config Nat} (h : GoodHead c) (V : List Val) (js : List Admin) :
    GoodHead (wrap V js c) := by
  obtain ⟨W, i, R, hc, hg⟩ := h
  refine ⟨V ++ W, i, R ++ js, ?_, hg⟩
  simp only [SpecGlobals.wrap, hc, vals_append, List.append_assoc, List.cons_append]

/-- Runs through `Good` heads lift under a value prefix and a suffix. -/
theorem GTo.lift {P : Profile} {c d : Config Nat} (h : GTo P c d) (V : List Val) (js : List Admin) :
    GTo P (wrap V js c) (wrap V js d) := by
  induction h with
  | refl c => exact .refl _
  | step hs hg _ ih => exact .step (lift_instrs V js _ _ hs) (hg.wrap V js) ih

theorem wrap_nil (c : Config Nat) : wrap [] [] c = c := by
  simp only [wrap, List.append_nil]
  rfl

/-! ## Code of values and `Good` or constant instructions -/

/-- A value or a `Good` or constant instruction. -/
def OkAdmin : Admin → Prop
  | .plain i => i.IsConstI ∨ Good i
  | .ref _ => True
  | _ => False

/-- Code made of values and `Good` or constant instructions. -/
def Inv (code : List Admin) : Prop := ∀ a ∈ code, OkAdmin a

@[simp] theorem inv_nil : Inv [] := fun _ h => (List.not_mem_nil h).elim

@[simp] theorem inv_cons (a : Admin) (l : List Admin) : Inv (a :: l) ↔ OkAdmin a ∧ Inv l := by
  simp only [Inv, List.mem_cons, forall_eq_or_imp]

@[simp] theorem inv_append (l₁ l₂ : List Admin) : Inv (l₁ ++ l₂) ↔ Inv l₁ ∧ Inv l₂ := by
  simp only [Inv, List.mem_append, or_imp, forall_and]

@[simp] theorem okAdmin_toAdmin (v : Val) : OkAdmin v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, OkAdmin, Instr.IsConstI]

@[simp] theorem inv_vals (vs : List Val) : Inv (vals vs) := by
  intro a ha
  simp only [vals, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  exact okAdmin_toAdmin v

theorem okAdmin_plain {i : Instr} : OkAdmin (.plain i) ↔ i.IsConstI ∨ Good i := Iff.rfl

@[simp] theorem okAdmin_intConst (t : IntType) (b : BitVec t.width) :
    OkAdmin (.plain (.intConst t b)) := .inl trivial
@[simp] theorem okAdmin_ref (r : Ref) : OkAdmin (.ref r) := trivial
@[simp] theorem okAdmin_tableSet (x : TableIdx) : OkAdmin (.plain (.tableSet x)) := .inr trivial
@[simp] theorem okAdmin_tableInit (x : TableIdx) (y : ElemIdx) :
    OkAdmin (.plain (.tableInit x y)) := .inr trivial
@[simp] theorem okAdmin_intStore (t : IntType) (p : Option PackSize) (x : MemIdx) (a : MemArg) :
    OkAdmin (.plain (.intStore t p x a)) := .inr trivial
@[simp] theorem okAdmin_memoryInit (x : MemIdx) (y : DataIdx) :
    OkAdmin (.plain (.memoryInit x y)) := .inr trivial
@[simp] theorem okAdmin_structNew (x : TypeIdx) : OkAdmin (.plain (.structNew x)) := .inr trivial
@[simp] theorem okAdmin_arrayNewFixed (x : TypeIdx) (n : Fin (2 ^ 32)) :
    OkAdmin (.plain (.arrayNewFixed x n)) := .inr trivial

/-! ## The results of `Good` heads -/

/-- The result of a `Good` head: the frame is kept, the code is again of values and `Good` or
constant instructions, or a trap. -/
def OutOk (f : Frame) (c : Config Nat) : Prop := c.frame = f ∧ (Inv c.code ∨ c.code = [.trap])

section Out

variable {P : Profile} {s : Store Nat} {f : Frame} {l : List Admin} {c : Config Nat} {i : Instr}

set_option hygiene false in
macro "out_close" : tactic => `(tactic| (
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, List.getLast?_append,
    Option.some_or, Option.some.injEq, Admin.plain.injEq] at hl
  first
    | (subst hl; exact False.elim hg)
    | (subst hl; simp [OutOk, constI32, arrRef, store8]; done)))

theorem numeric_out {out : List Admin} (h : NumericStep P l out) (hl : l.getLast? = some (.plain i))
    (hg : Good i) : Inv out ∨ out = [.trap] := by
  cases h <;> (
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq,
      Admin.plain.injEq] at hl
    first
      | (subst hl; exact False.elim hg)
      | (subst hl; simp [OkAdmin, Instr.IsConstI]))

theorem variable_out (h : VariableStep ⟨s, f, l⟩ c) (hl : l.getLast? = some (.plain i))
    (hg : Good i) : OutOk f c := by
  cases h <;> out_close

theorem reference_out (h : RefStep ⟨s, f, l⟩ c) (hl : l.getLast? = some (.plain i))
    (hg : Good i) : OutOk f c := by
  cases h <;> out_close

theorem aggregate_out (h : AggregateStep ⟨s, f, l⟩ c) (hl : l.getLast? = some (.plain i))
    (hg : Good i) : OutOk f c := by
  cases h <;> out_close

theorem table_out (h : TableStep P ⟨s, f, l⟩ c) (hl : l.getLast? = some (.plain i))
    (hg : Good i) : OutOk f c := by
  cases h <;> out_close

theorem memory_out (h : MemoryStep P ⟨s, f, l⟩ c) (hl : l.getLast? = some (.plain i))
    (hg : Good i) : OutOk f c := by
  cases h <;> out_close

end Out

theorem parametric_bad {l out : List Admin} {i : Instr} (h : ParametricStep l out)
    (hl : l.getLast? = some (.plain i)) (hg : Good i) : False := by
  cases h <;> (
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq,
      Admin.plain.injEq] at hl
    subst hl
    exact hg)

theorem vector_bad {P : Profile} {l out : List Admin} {i : Instr} (h : VectorStep P l out)
    (hl : l.getLast? = some (.plain i)) (hg : Good i) : False := by
  cases h <;> (
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq,
      Admin.plain.injEq] at hl
    subst hl
    exact hg)

/-- The result of a head at a `Good` instruction. -/
theorem head_out {P : Profile} {s : Store Nat} {f : Frame} {args : List Val} {i : Instr}
    {c₀ : Config Nat} (hg : Good i) (hh : Head P s f args (.plain i) c₀) : OutOk f c₀ := by
  have hl := getLast_args args (.plain i)
  cases hh with
  | parametric h => exact (parametric_bad h hl hg).elim
  | numeric h => exact ⟨rfl, numeric_out h hl hg⟩
  | vector h => exact (vector_bad h hl hg).elim
  | «variable» h => exact variable_out h hl hg
  | table h => exact table_out h hl hg
  | memory h => exact memory_out h hl hg
  | reference h => exact reference_out h hl hg
  | aggregate h => exact aggregate_out h hl hg
  | _ => first
    | exact False.elim hg
    | exact absurd (IsCallRef.famOf ‹_›) (good_fam hg)

/-- Code is values, or values before a non-value. -/
theorem split_first : ∀ code : List Admin,
    (∃ W, code = vals W) ∨ ∃ W a R, code = vals W ++ a :: R ∧ a.val? = none
  | [] => .inl ⟨[], rfl⟩
  | a :: R => by
    cases ha : a.val? with
    | none => exact .inr ⟨[], a, R, rfl, ha⟩
    | some v =>
      have hv : a = v.toAdmin := Admin.eq_toAdmin_of_val? ha
      rcases split_first R with ⟨W, hW⟩ | ⟨W, b, R', hR, hb⟩
      · exact .inl ⟨v :: W, by rw [hv, hW]; rfl⟩
      · exact .inr ⟨v :: W, b, R', by rw [hv, hR]; rfl, hb⟩

/-- A constant or `Good` non-value instruction is `Good`. -/
theorem okAdmin_good {a : Admin} (ha : OkAdmin a) (hv : a.val? = none) :
    ∃ i, a = .plain i ∧ Good i := by
  cases a with
  | plain i =>
    refine ⟨i, rfl, ?_⟩
    rcases ha with hc | hg
    · cases i <;> first | exact hc.elim | trivial
    · exact hg
  | ref r => exact absurd hv (by simp [Admin.val?])
  | _ => exact ha.elim

/-- **A step from code of values and `Good` or constant instructions** is at a `Good` head, keeps
the frame, and leaves code of the same kind, or code whose first non-value is a trap. -/
theorem step_shape {P : Profile} {s : Store Nat} {f : Frame} {code : List Admin} {c : Config Nat}
    (hinv : Inv code) (h : Step P noHost ⟨s, f, code⟩ c) :
    GoodHead ⟨s, f, code⟩ ∧ c.frame = f ∧
      (Inv c.code ∨ ∃ W R, c.code = vals W ++ .trap :: R ∧ Inv R) := by
  rcases split_first code with ⟨W, hW⟩ | ⟨W, a, R, hc, hv⟩
  · exact absurd (hW ▸ h) not_step_vals
  have hR : Inv R := by
    have h' : Inv (vals W ++ a :: R) := hc ▸ hinv
    simp only [inv_append, inv_cons] at h'
    exact h'.2.2
  have ha : OkAdmin a := hinv a (by rw [hc]; simp)
  obtain ⟨i, rfl, hg⟩ := okAdmin_good ha hv
  have hh : Step P noHost ⟨s, f, vals W ++ .plain i :: R⟩ c := hc ▸ h
  obtain ⟨vs, args, c₀, -, hd, rfl⟩ := good_headDec hg hh
  obtain ⟨hf, hout⟩ := head_out hg hd
  refine ⟨⟨W, i, R, hc, hg⟩, hf, ?_⟩
  rcases hout with hi | ht
  · exact .inl (by simp only [inv_append, inv_vals, hi, hR, and_self])
  · exact .inr ⟨vs, R, by simp only [ht, List.append_assoc, List.singleton_append], hR⟩

end Silmaril.Proofs.Wasm.Game.SpecGlobals
