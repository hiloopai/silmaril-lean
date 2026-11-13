module

public import Silmaril.Wasm.Models.FXV.Thms

/-!
# The first non-value of FX code, with FX values

`Silmaril.Proofs.Wasm.Models.FXLower.fnvX` splits FX code at its first non-Core-value. Under
`StepFX'` a continuation reference is a value too, so the inversions of `StepFX'` split at the
first instruction that is neither a Core value nor a continuation reference:

* `fval?`: recognise an FX value; `fnvF`: split FX code at its first non-FX-value;
* `fnvF_fvals_append`, `fnvF_cons_none`: the computation rules; `fvals_inj`;
* `fvals_append_cons_inj`: the decomposition `fvals V ++ e :: T` at a non-value `e` is unique;
* `fnvF_cases`, `seq_splitF`: every code is FX values, or FX values then a non-value; a
  `ctxt-instrs` decomposition puts only values in the stepping part, or the first non-value
  after the values it skips;
* `fvals_eq_core`: FX values that are Core code are Core values;
* **`no_step_nil'`**, **`no_step_fvals'`** (no host calls): empty code and FX values do not
  step under `StepFX'`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXVRuns

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXLower (cval? blockFX_noHost)
open Silmaril.Wasm.SingleThreaded.Det (noHost not_step_vals val?_eq_some)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- An FX value instruction: a Core value or a continuation reference. -/
def fval? : AdminFX → Option FVal
  | .core a => a.val?.map .val
  | .contRef k => some (.cont k)
  | _ => none

/-- The first non-FX-value decomposition of FX code. -/
def fnvF : List AdminFX → List FVal × List AdminFX
  | [] => ([], [])
  | a :: as =>
    match fval? a with
    | some v => (v :: (fnvF as).1, (fnvF as).2)
    | none => ([], a :: as)

@[simp] theorem fnvF_nil : fnvF [] = ([], []) := rfl

theorem fnvF_cons_none {a : AdminFX} (h : fval? a = none) (l : List AdminFX) :
    fnvF (a :: l) = ([], a :: l) := by
  simp [fnvF, h]

theorem fnvF_cons_some {a : AdminFX} {v : FVal} (h : fval? a = some v) (l : List AdminFX) :
    fnvF (a :: l) = (v :: (fnvF l).1, (fnvF l).2) := by
  simp [fnvF, h]

@[simp] theorem fval?_toAdmin (v : FVal) : fval? v.toAdmin = some v := by
  cases v with
  | val v => simp [fval?, FVal.toAdmin]
  | cont k => rfl

@[simp] theorem fval?_core (a : Admin) : fval? (.core a) = a.val?.map .val := rfl
@[simp] theorem fval?_fx (i : FXInstr) : fval? (.fx i) = none := rfl
@[simp] theorem fval?_block (bt : BlockType) (b : List InstrFX) : fval? (.block bt b) = none := rfl
@[simp] theorem fval?_loop (bt : BlockType) (b : List InstrFX) : fval? (.loop bt b) = none := rfl
@[simp] theorem fval?_if (bt : BlockType) (b₁ b₂ : List InstrFX) :
    fval? (.if_ bt b₁ b₂) = none := rfl
@[simp] theorem fval?_label (n : Nat) (k : List InstrFX) (b : List AdminFX) :
    fval? (.label n k b) = none := rfl
@[simp] theorem fval?_frame (n : Nat) (f : Frame) (b : List AdminFX) :
    fval? (.frame n f b) = none := rfl
@[simp] theorem fval?_handler (hs : List HClause) (b : List AdminFX) :
    fval? (.handler hs b) = none := rfl
@[simp] theorem fval?_contRef (k : Nat) : fval? (.contRef k) = some (.cont k) := rfl

@[simp] theorem fnvF_cons_fx (i : FXInstr) (l : List AdminFX) :
    fnvF (.fx i :: l) = ([], .fx i :: l) := rfl
@[simp] theorem fnvF_cons_block (bt : BlockType) (b : List InstrFX) (l : List AdminFX) :
    fnvF (.block bt b :: l) = ([], .block bt b :: l) := rfl
@[simp] theorem fnvF_cons_loop (bt : BlockType) (b : List InstrFX) (l : List AdminFX) :
    fnvF (.loop bt b :: l) = ([], .loop bt b :: l) := rfl
@[simp] theorem fnvF_cons_if (bt : BlockType) (b₁ b₂ : List InstrFX) (l : List AdminFX) :
    fnvF (.if_ bt b₁ b₂ :: l) = ([], .if_ bt b₁ b₂ :: l) := rfl
@[simp] theorem fnvF_cons_label (n : Nat) (k : List InstrFX) (b l : List AdminFX) :
    fnvF (.label n k b :: l) = ([], .label n k b :: l) := rfl
@[simp] theorem fnvF_cons_frame (n : Nat) (f : Frame) (b l : List AdminFX) :
    fnvF (.frame n f b :: l) = ([], .frame n f b :: l) := rfl
@[simp] theorem fnvF_cons_handler (hs : List HClause) (b l : List AdminFX) :
    fnvF (.handler hs b :: l) = ([], .handler hs b :: l) := rfl
@[simp] theorem fnvF_cons_contRef (k : Nat) (l : List AdminFX) :
    fnvF (.contRef k :: l) = (.cont k :: (fnvF l).1, (fnvF l).2) := rfl

theorem fnvF_cons_core_none {a : Admin} (h : a.val? = none) (l : List AdminFX) :
    fnvF (.core a :: l) = ([], .core a :: l) :=
  fnvF_cons_none (by simp [h]) l

@[simp] theorem fnvF_cons_core_plain_none {i : Instr}
    (h : (Admin.plain i).val? = none) (l : List AdminFX) :
    fnvF (.core (.plain i) :: l) = ([], .core (.plain i) :: l) :=
  fnvF_cons_core_none h l

@[simp] theorem fnvF_cons_trap (l : List AdminFX) :
    fnvF (.core .trap :: l) = ([], .core .trap :: l) := fnvF_cons_core_none rfl l

@[simp] theorem fnvF_cons_core_ref (r : Ref) (l : List AdminFX) :
    fnvF (.core (.ref r) :: l) = (.val (.ref r) :: (fnvF l).1, (fnvF l).2) := rfl

theorem fnvF_fvals_append (V : List FVal) (T : List AdminFX) :
    fnvF (fvals V ++ T) = (V ++ (fnvF T).1, (fnvF T).2) := by
  induction V with
  | nil => rfl
  | cons v V ih =>
    show fnvF (v.toAdmin :: (fvals V ++ T)) = _
    rw [fnvF_cons_some (fval?_toAdmin v), ih]
    rfl

@[simp] theorem fnvF_fvals (V : List FVal) : fnvF (fvals V) = (V, []) := by
  simpa using fnvF_fvals_append V []

@[simp] theorem fvals_nil : fvals [] = [] := rfl

@[simp] theorem fvals_append (A B : List FVal) : fvals (A ++ B) = fvals A ++ fvals B :=
  List.map_append

@[simp] theorem fvals_cons (v : FVal) (V : List FVal) : fvals (v :: V) = v.toAdmin :: fvals V :=
  rfl

@[simp] theorem fvals_length (V : List FVal) : (fvals V).length = V.length := List.length_map _

theorem fvals_inj {V V' : List FVal} (h : fvals V = fvals V') : V = V' := by
  have h' := congrArg (fun l => (fnvF l).1) h
  simpa using h'

/-- A recognised FX value is that value. -/
theorem eq_of_fval? {a : AdminFX} {v : FVal} (h : fval? a = some v) : a = v.toAdmin := by
  cases a with
  | core a =>
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact congrArg AdminFX.core (val?_eq_some.mp hw)
  | contRef k =>
    cases h
    rfl
  | _ => exact absurd h (by simp)

/-- **Uniqueness of the first non-value.** -/
theorem fvals_append_cons_inj {V₁ V₂ : List FVal} {e₁ e₂ : AdminFX} {T₁ T₂ : List AdminFX}
    (h : fvals V₁ ++ e₁ :: T₁ = fvals V₂ ++ e₂ :: T₂) (h₁ : fval? e₁ = none)
    (h₂ : fval? e₂ = none) : V₁ = V₂ ∧ e₁ = e₂ ∧ T₁ = T₂ := by
  have h' : fnvF (fvals V₁ ++ e₁ :: T₁) = fnvF (fvals V₂ ++ e₂ :: T₂) := congrArg fnvF h
  have h'' : (V₁, e₁ :: T₁) = (V₂, e₂ :: T₂) := by
    simpa only [fnvF_fvals_append, fnvF_cons_none h₁, fnvF_cons_none h₂, List.append_nil]
      using h'
  simp only [Prod.mk.injEq, List.cons.injEq] at h''
  exact h''

/-- **Every FX code is FX values, or FX values followed by a non-value.** -/
theorem fnvF_cases (l : List AdminFX) :
    (∃ V, l = fvals V) ∨ ∃ V e T, l = fvals V ++ e :: T ∧ fval? e = none := by
  induction l with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons a l ih =>
    cases hv : fval? a with
    | none => exact Or.inr ⟨[], a, l, rfl, hv⟩
    | some v =>
      have ha : a = v.toAdmin := eq_of_fval? hv
      rcases ih with ⟨V, rfl⟩ | ⟨V, e, T, rfl, he⟩
      · exact Or.inl ⟨v :: V, by rw [ha]; rfl⟩
      · exact Or.inr ⟨v :: V, e, T, by rw [ha]; rfl, he⟩

/-- **Splitting a `ctxt-instrs` decomposition at the first non-value.** -/
theorem seq_splitF {vs V : List FVal} {es rest T : List AdminFX} {e : AdminFX}
    (he : fval? e = none) (h : fvals vs ++ es ++ rest = fvals V ++ e :: T) :
    (∃ U, es = fvals U) ∨ ∃ V₂ T₁, V = vs ++ V₂ ∧ es = fvals V₂ ++ e :: T₁ ∧ T = T₁ ++ rest := by
  rcases fnvF_cases es with hV | ⟨U, e', T', rfl, he'⟩
  · exact Or.inl hV
  · have h' : fvals (vs ++ U) ++ e' :: (T' ++ rest) = fvals V ++ e :: T := by
      rw [← h, fvals_append]
      simp only [List.append_assoc, List.cons_append]
    obtain ⟨hV, he, hT⟩ := fvals_append_cons_inj h' he' he
    exact Or.inr ⟨U, T', hV.symm, by rw [he], hT.symm⟩

/-- `fvals` of a split. -/
theorem fvals_eq_append {V : List FVal} {A B : List AdminFX} (h : fvals V = A ++ B) :
    ∃ V₁ V₂, V = V₁ ++ V₂ ∧ A = fvals V₁ ∧ B = fvals V₂ := by
  obtain ⟨V₁, V₂, rfl, hA, hB⟩ := List.map_eq_append_iff.mp h
  exact ⟨V₁, V₂, rfl, hA.symm, hB.symm⟩

/-- FX values that are Core code are Core values. -/
theorem fvals_eq_core {V : List FVal} {cs : List Admin} (h : fvals V = cs.map .core) :
    V = liftV (V.filterMap fun | .val v => some v | .cont _ => none) ∧
      cs = vals (V.filterMap fun | .val v => some v | .cont _ => none) := by
  induction V generalizing cs with
  | nil =>
    have hcs : cs = [] := List.map_eq_nil_iff.mp h.symm
    exact ⟨rfl, hcs⟩
  | cons v V ih =>
    obtain ⟨c, cs', rfl, hc, hcs⟩ := List.map_eq_cons_iff.mp h.symm
    obtain ⟨ih₁, ih₂⟩ := ih hcs.symm
    cases v with
    | val w =>
      have hc' : c = w.toAdmin := AdminFX.core.inj hc
      refine ⟨congrArg (FVal.val w :: ·) ih₁, ?_⟩
      simp only [List.filterMap_cons, vals, List.map_cons, hc']
      exact congrArg (w.toAdmin :: ·) ih₂
    | cont k => cases hc

/-- FX values that are Core code are Core values (existential form). -/
theorem fvals_eq_core' {V : List FVal} {cs : List Admin} (h : fvals V = cs.map .core) :
    ∃ W, V = liftV W ∧ cs = vals W :=
  ⟨_, (fvals_eq_core h).1, (fvals_eq_core h).2⟩

theorem fvals_liftV' (W : List Val) : fvals (liftV W) = cvals W := by
  simp [fvals, liftV, cvals, vals, FVal.toAdmin]

@[simp] theorem fnvF_cvals_append (W : List Val) (T : List AdminFX) :
    fnvF (cvals W ++ T) = (liftV W ++ (fnvF T).1, (fnvF T).2) := by
  rw [← fvals_liftV', fnvF_fvals_append]

@[simp] theorem fnvF_cvals (W : List Val) : fnvF (cvals W) = (liftV W, []) := by
  simpa using fnvF_cvals_append W []

/-- The left-hand sides of most rules are not FX values, or are split elsewhere. -/
macro "fnvF_absurd" hx:ident : tactic => `(tactic| (
  exfalso
  first
  | (have h1 := congrArg (fun l => (fnvF l).2) $hx:ident
     simp [fnvF_fvals_append, fnvF_cvals_append, fnvF, fval?, Admin.val?, constI32, Val.i32,
       Val.toAdmin, FVal.toAdmin, cthrowing, throwing] at h1; done)
  | (have h1 := congrArg fnvF $hx:ident
     simp [fnvF_fvals_append, fnvF_cvals_append, fnvF, fval?, Admin.val?, constI32, Val.i32,
       Val.toAdmin, FVal.toAdmin, cthrowing, throwing] at h1; done)
  | (simp [cthrowing, throwing, List.cons_eq_append_iff] at $hx:ident)))

/-- **Empty FX code does not step under `StepFX'`.** -/
theorem no_step_nil' {fx : H → Option FuncFX} {x y : ConfigFX H}
    (h : StepFX' P noHost fx x y) : x.code ≠ [] := by
  induction h with
  | @core s s' K f f' cs cs' h =>
    intro hc
    have hcs : cs = [] := List.map_eq_nil_iff.mp hc
    have h' : Step P noHost ⟨s, f, vals []⟩ ⟨s', f', cs'⟩ := by
      rw [← blockFX_noHost fx]
      rw [hcs] at h
      exact h
    exact not_step_vals h'
  | seq _ _ ih =>
    intro hc
    exact ih (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hc).1).2
  | _ => simp [cvals, cthrowing, fvals]

/-- The `core` case of `no_step_fvals'`. -/
theorem no_core_fvals {fx : H → Option FuncFX} {s s' : Store H} {f f' : Frame}
    {cs cs' : List Admin} {V : List FVal}
    (h : Step P (blockFX noHost fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) (hc : cs.map .core = fvals V) :
    False := by
  obtain ⟨W, -, hcs⟩ := fvals_eq_core' hc.symm
  have h' : Step P noHost ⟨s, f, vals W⟩ ⟨s', f', cs'⟩ := by
    rw [← blockFX_noHost fx, ← hcs]
    exact h
  exact not_step_vals h'

/-- **FX values do not step under `StepFX'`** (no host calls). -/
theorem no_step_fvals' {fx : H → Option FuncFX} {x y : ConfigFX H}
    (h : StepFX' P noHost fx x y) : ∀ V, x.code ≠ fvals V := by
  induction h with
  | core h => exact fun V hc => no_core_fvals h hc
  | @seq _ _ _ _ _ _ vs es _ rest _ _ ih =>
    intro V hc
    obtain ⟨W₁, W₂, -, -, hB⟩ := fvals_eq_append (hc.symm.trans (List.append_assoc _ _ _))
    obtain ⟨W₃, -, -, hes, -⟩ := fvals_eq_append hB.symm
    exact ih W₃ hes
  | @invoke _ _ _ c _ _ _ _ _ hc =>
    intro V hx
    have h1 := congrArg fnvF hx
    simp [fnvF_cons_core_none (Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc)] at h1
  | _ => intro V hx; fnvF_absurd hx

/-- The left-hand side of `invoke`, split at its call. -/
theorem invoke_eq (vs : List Val) (a : Nat) (c : Admin) :
    cvals vs ++ [.core (.ref (.func a)), .core c] =
      fvals (liftV vs ++ [.val (.ref (.func a))]) ++ AdminFX.core c :: [] := by
  simp [fvals, liftV, cvals, vals, FVal.toAdmin, Val.toAdmin]

end Silmaril.Proofs.Wasm.Models.FXVRuns
