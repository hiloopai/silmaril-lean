module

public import Silmaril.Proofs.Wasm.Models.FXLower.HandlerInv

/-!
# The first non-value of FX code

An FX analogue of silmaril's `Det.fnv`:

* `cval?`: recognise a Core value instruction in FX code; `fnvX`: split FX code at its first
  non-value;
* `fnvX_cvals_append`, `fnvX_cons_none`: the computation rules;
* `cvals_append_cons_inj`: the decomposition `cvals W ++ e :: T` at a non-value `e` is unique;
* `fnvX_cases`: every FX code is values, or values followed by a non-value;
* `seq_split`: a `ctxt-instrs` decomposition `cvals vs ++ es ++ rest` of `cvals W ++ e :: T`
  either puts only values in `es`, or puts `e` in `es` after the values of `W` that `vs` leaves;
* `no_step_cvals` (no host calls): FX values do not step.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Proofs.Wasm.Models.FX (isCore map_core_inj)
open Silmaril.Wasm.SingleThreaded.Det (noHost not_step_vals val?_eq_some)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- A Core value instruction in FX code. -/
def cval? : AdminFX → Option Val
  | .core a => a.val?
  | _ => none

/-- The first non-value decomposition of FX code. -/
def fnvX : List AdminFX → List Val × List AdminFX
  | [] => ([], [])
  | a :: as =>
    match cval? a with
    | some v => (v :: (fnvX as).1, (fnvX as).2)
    | none => ([], a :: as)

@[simp] theorem fnvX_nil : fnvX [] = ([], []) := rfl

theorem fnvX_cons_none {a : AdminFX} (h : cval? a = none) (l : List AdminFX) :
    fnvX (a :: l) = ([], a :: l) := by
  simp [fnvX, h]

theorem fnvX_cons_some {a : AdminFX} {v : Val} (h : cval? a = some v) (l : List AdminFX) :
    fnvX (a :: l) = (v :: (fnvX l).1, (fnvX l).2) := by
  simp [fnvX, h]

@[simp] theorem cval?_core (a : Admin) : cval? (.core a) = a.val? := rfl
@[simp] theorem cval?_fx (i : FXInstr) : cval? (.fx i) = none := rfl
@[simp] theorem cval?_block (bt : BlockType) (b : List InstrFX) : cval? (.block bt b) = none := rfl
@[simp] theorem cval?_loop (bt : BlockType) (b : List InstrFX) : cval? (.loop bt b) = none := rfl
@[simp] theorem cval?_if (bt : BlockType) (b₁ b₂ : List InstrFX) :
    cval? (.if_ bt b₁ b₂) = none := rfl
@[simp] theorem cval?_label (n : Nat) (k : List InstrFX) (b : List AdminFX) :
    cval? (.label n k b) = none := rfl
@[simp] theorem cval?_frame (n : Nat) (f : Frame) (b : List AdminFX) :
    cval? (.frame n f b) = none := rfl
@[simp] theorem cval?_handler (hs : List HClause) (b : List AdminFX) :
    cval? (.handler hs b) = none := rfl
@[simp] theorem cval?_contRef (k : Nat) : cval? (.contRef k) = none := rfl

@[simp] theorem fnvX_cons_fx (i : FXInstr) (l : List AdminFX) :
    fnvX (.fx i :: l) = ([], .fx i :: l) := rfl
@[simp] theorem fnvX_cons_block (bt : BlockType) (b : List InstrFX) (l : List AdminFX) :
    fnvX (.block bt b :: l) = ([], .block bt b :: l) := rfl
@[simp] theorem fnvX_cons_loop (bt : BlockType) (b : List InstrFX) (l : List AdminFX) :
    fnvX (.loop bt b :: l) = ([], .loop bt b :: l) := rfl
@[simp] theorem fnvX_cons_if (bt : BlockType) (b₁ b₂ : List InstrFX) (l : List AdminFX) :
    fnvX (.if_ bt b₁ b₂ :: l) = ([], .if_ bt b₁ b₂ :: l) := rfl
@[simp] theorem fnvX_cons_label (n : Nat) (k : List InstrFX) (b l : List AdminFX) :
    fnvX (.label n k b :: l) = ([], .label n k b :: l) := rfl
@[simp] theorem fnvX_cons_frame (n : Nat) (f : Frame) (b l : List AdminFX) :
    fnvX (.frame n f b :: l) = ([], .frame n f b :: l) := rfl
@[simp] theorem fnvX_cons_handler (hs : List HClause) (b l : List AdminFX) :
    fnvX (.handler hs b :: l) = ([], .handler hs b :: l) := rfl
@[simp] theorem fnvX_cons_contRef (k : Nat) (l : List AdminFX) :
    fnvX (.contRef k :: l) = ([], .contRef k :: l) := rfl
@[simp] theorem fnvX_cons_ref (r : Ref) (l : List AdminFX) :
    fnvX (.core (.ref r) :: l) = (.ref r :: (fnvX l).1, (fnvX l).2) := rfl
@[simp] theorem fnvX_cons_trap (l : List AdminFX) :
    fnvX (.core .trap :: l) = ([], .core .trap :: l) := rfl

theorem fnvX_cons_core_none {a : Admin} (h : a.val? = none) (l : List AdminFX) :
    fnvX (.core a :: l) = ([], .core a :: l) := fnvX_cons_none (a := .core a) h l

/-- The plain instructions that are not values, for `simp`. -/
@[simp] theorem fnvX_cons_plain_br (l₀ : LabelIdx) (l : List AdminFX) :
    fnvX (.core (.plain (.br l₀)) :: l) = ([], .core (.plain (.br l₀)) :: l) := rfl
@[simp] theorem fnvX_cons_plain_return (l : List AdminFX) :
    fnvX (.core (.plain .return_) :: l) = ([], .core (.plain .return_) :: l) := rfl
@[simp] theorem fnvX_cons_plain_throwRef (l : List AdminFX) :
    fnvX (.core (.plain .throwRef) :: l) = ([], .core (.plain .throwRef) :: l) := rfl

@[simp] theorem cvals_cons (v : Val) (vs : List Val) :
    cvals (v :: vs) = .core v.toAdmin :: cvals vs := rfl
@[simp] theorem cvals_nil : cvals [] = [] := rfl
@[simp] theorem cvals_append (xs ys : List Val) : cvals (xs ++ ys) = cvals xs ++ cvals ys := by
  simp [cvals]

@[simp] theorem fnvX_cons_toAdmin (v : Val) (l : List AdminFX) :
    fnvX (.core v.toAdmin :: l) = (v :: (fnvX l).1, (fnvX l).2) :=
  fnvX_cons_some (a := .core v.toAdmin) (Admin.val?_toAdmin v) l

@[simp] theorem fnvX_cons_constI32 (c : BitVec 32) (l : List AdminFX) :
    fnvX (.core (constI32 c) :: l) = (Val.i32 c :: (fnvX l).1, (fnvX l).2) :=
  fnvX_cons_toAdmin _ l

@[simp] theorem fnvX_cvals_append (W : List Val) (l : List AdminFX) :
    fnvX (cvals W ++ l) = (W ++ (fnvX l).1, (fnvX l).2) := by
  induction W with
  | nil => rfl
  | cons v W ih =>
    rw [cvals_cons, List.cons_append, fnvX_cons_some (a := .core v.toAdmin) (Admin.val?_toAdmin v),
      ih]
    rfl

@[simp] theorem fnvX_cvals (W : List Val) : fnvX (cvals W) = (W, []) := by
  simpa using fnvX_cvals_append W []

/-- A Core value instruction is a value. -/
theorem eq_of_cval? {a : AdminFX} {v : Val} (h : cval? a = some v) : a = .core v.toAdmin := by
  cases a with
  | core a => exact congrArg AdminFX.core (val?_eq_some.mp h)
  | _ => exact absurd h (by simp)

/-- **Uniqueness of the first non-value.** -/
theorem cvals_append_cons_inj {W₁ W₂ : List Val} {e₁ e₂ : AdminFX} {T₁ T₂ : List AdminFX}
    (h : cvals W₁ ++ e₁ :: T₁ = cvals W₂ ++ e₂ :: T₂) (h₁ : cval? e₁ = none)
    (h₂ : cval? e₂ = none) : W₁ = W₂ ∧ e₁ = e₂ ∧ T₁ = T₂ := by
  have h' : fnvX (cvals W₁ ++ e₁ :: T₁) = fnvX (cvals W₂ ++ e₂ :: T₂) := congrArg fnvX h
  have h'' : (W₁, e₁ :: T₁) = (W₂, e₂ :: T₂) := by
    simpa only [fnvX_cvals_append, fnvX_cons_none h₁, fnvX_cons_none h₂, List.append_nil]
      using h'
  simp only [Prod.mk.injEq, List.cons.injEq] at h''
  exact h''

/-- **Every FX code is values, or values followed by a non-value.** -/
theorem fnvX_cases (l : List AdminFX) :
    (∃ V, l = cvals V) ∨ ∃ V e T, l = cvals V ++ e :: T ∧ cval? e = none := by
  induction l with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons a l ih =>
    cases hv : cval? a with
    | none => exact Or.inr ⟨[], a, l, rfl, hv⟩
    | some v =>
      have ha : a = .core v.toAdmin := eq_of_cval? hv
      rcases ih with ⟨V, rfl⟩ | ⟨V, e, T, rfl, he⟩
      · exact Or.inl ⟨v :: V, by rw [ha]; rfl⟩
      · exact Or.inr ⟨v :: V, e, T, by rw [ha]; rfl, he⟩

/-- **Splitting a `ctxt-instrs` decomposition at the first non-value.** -/
theorem seq_split {vs W : List Val} {es rest T : List AdminFX} {e : AdminFX}
    (he : cval? e = none) (h : cvals vs ++ es ++ rest = cvals W ++ e :: T) :
    (∃ V, es = cvals V) ∨ ∃ W₂ T₁, W = vs ++ W₂ ∧ es = cvals W₂ ++ e :: T₁ ∧ T = T₁ ++ rest := by
  rcases fnvX_cases es with hV | ⟨V, e', T', rfl, he'⟩
  · exact Or.inl hV
  · have h' : cvals (vs ++ V) ++ e' :: (T' ++ rest) = cvals W ++ e :: T := by
      rw [← h, cvals_append]
      simp only [List.append_assoc, List.cons_append]
    obtain ⟨hW, he, hT⟩ := cvals_append_cons_inj h' he' he
    exact Or.inr ⟨V, T', hW.symm, by rw [he], hT.symm⟩

/-- `cvals` of a split. -/
theorem cvals_eq_append {W : List Val} {A B : List AdminFX} (h : cvals W = A ++ B) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ A = cvals W₁ ∧ B = cvals W₂ := by
  obtain ⟨A', B', hW, hA, hB⟩ :=
    List.map_eq_append_iff.mp (show (vals W).map AdminFX.core = A ++ B from h)
  obtain ⟨W₁, W₂, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hW
  exact ⟨W₁, W₂, rfl, hA.symm, hB.symm⟩

/-- A call instruction is not a value. -/
theorem IsCallRef.val?_none {c : Admin} (hc : c.IsCallRef) : c.val? = none := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsCallRef] at hc
  · cases i <;> simp at hc; rfl
  · rfl

/-- The left-hand sides of most rules are not values. -/
macro "fnvX_absurd" hx:ident : tactic => `(tactic| (
  exfalso
  first
  | (have h1 := congrArg fnvX $hx:ident
     simp [cthrowing, throwing] at h1; done)
  | (simp [cthrowing, throwing, List.cons_eq_append_iff] at $hx:ident)))

/-- The `core` case of `no_step_cvals`. -/
theorem no_core_cvals {fx : H → Option FuncFX} {s s' : Store H} {f f' : Frame}
    {cs cs' : List Admin} {V : List Val}
    (h : Step P (blockFX noHost fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) (hc : cs.map .core = cvals V) :
    False := by
  have hcs : cs = vals V := map_core_inj hc
  have h' : Step P noHost ⟨s, f, vals V⟩ ⟨s', f', cs'⟩ := by
    rw [← blockFX_noHost fx, ← hcs]
    exact h
  exact not_step_vals h'

/-- **FX values do not step** (no host calls). -/
theorem no_step_cvals {fx : H → Option FuncFX} {x y : ConfigFX H}
    (h : StepFX P noHost fx x y) : ∀ V, x.code ≠ cvals V := by
  induction h with
  | core h => exact fun V hc => no_core_cvals h hc
  | @seq _ _ _ _ _ _ vs es _ rest _ _ ih =>
    intro V hc
    obtain ⟨W₁, W₂, -, -, hB⟩ := cvals_eq_append (hc.symm.trans (List.append_assoc _ _ _))
    obtain ⟨W₃, -, -, hes, -⟩ := cvals_eq_append hB.symm
    exact ih W₃ hes
  | @invoke _ _ _ c _ _ _ _ _ hc =>
    intro V hx
    have h1 := congrArg fnvX hx
    simp [fnvX_cons_core_none (IsCallRef.val?_none hc)] at h1
  | _ => intro V hx; fnvX_absurd hx

end Silmaril.Proofs.Wasm.Models.FXLower
