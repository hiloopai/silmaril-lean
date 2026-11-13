module

public import Silmaril.Wasm.SpecTec.Sim20.StoreRun.Thms
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# Code with scalar stores at the administrative level, and its typing in `simEnv20T`

Round 3's covered fragment (`Whole.adminOk`) excludes stores. Here a scalar store may also stand
as an administrative instruction: at the top of the code, in a label body or in a frame body, at
any depth. It may not stand inside an instruction tree (a block body, a label continuation, a
function body), so the state stays typed in the original `simEnv20`.

* `storeOkI`: the scalar stores that 2.0 validation admits (a pack size below the width);
  `adminOkS`: `adminOk` with such stores allowed at the administrative level.
* `eraseA`, `eraseL`: replace every administrative scalar store by `nop`. Erased covered code is
  plain `adminOk` code (`adminOk_eraseA`), and code that is already `adminOk` is unchanged
  (`eraseA_of_adminOk`).
* **`typedT_of_eraseL`**: if the erased image is a typed `admininstr*` of the original script,
  the image itself is a typed `admininstr*` of `simEnv20T`. Labels and frames are taken apart in
  `simEnv20` (`Whole.typedV_adminLabel20_iff`) and put back in `simEnv20T`
  (`typedV_adminLabel20T_mk`, `typedV_adminFrame20T_mk`); stores are typed by the erratum
  (`StoreAgree.typedV_intStore20T`, `typedV_floatStore20T`).
* `typedV_instr_of_admin20T`: in `simEnv20T`, as in `simEnv20`, a plain instruction typed as an
  `admininstr` is typed as an `instr` (the case list of `admininstr` is that of `instr` followed
  by six administrative cases).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreGood

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT storeT frameT nT instrsT)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase recCases)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T fixCase adminCasesT findTyp_admininstr20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk ctrlOkL adminOk)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d133 Original.d295)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins}

/-! ## Scalar stores, erasure, and covered code with stores -/

/-- **The scalar stores 2.0 validation admits**: integer and float stores, a pack size below the
integer width. -/
def storeOkI : V2.Instr → Bool
  | .intStore _ none _ => true
  | .intStore t (some sz) _ => decide (sz.width < t.width)
  | .floatStore _ _ => true
  | _ => false

/-- A scalar store becomes `nop`; every other instruction is kept. Block bodies are not entered. -/
def eraseI : V2.Instr → V2.Instr
  | .intStore .. => .nop
  | .floatStore .. => .nop
  | i => i

mutual
/-- **Erase the administrative scalar stores** of an administrative instruction: in itself, and in
label and frame bodies (not in label continuations). -/
def eraseA : Admin → Admin
  | .plain i => .plain (eraseI i)
  | .label n cont body => .label n cont (eraseL body)
  | .frame n fi body => .frame n fi (eraseL body)
  | .trap => .trap
  | .callAddr a => .callAddr a
  | .refFuncAddr a => .refFuncAddr a
  | .refHostAddr a => .refHostAddr a

/-- `eraseA` on a sequence. -/
def eraseL : List Admin → List Admin
  | [] => []
  | a :: l => eraseA a :: eraseL l
end

mutual
/-- **Covered code with administrative stores**: `Whole.adminOk`, where a plain administrative
instruction may also be a scalar store (`storeOkI`). Label continuations stay `ctrlOk`. -/
def adminOkS : Admin → Bool
  | .plain i => ctrlOk i || storeOkI i
  | .label _ cont body => ctrlOkL cont && adminOkSL body
  | .frame _ _ body => adminOkSL body
  | .trap | .callAddr _ | .refFuncAddr _ | .refHostAddr _ => true

/-- `adminOkS` on a sequence. -/
def adminOkSL : List Admin → Bool
  | [] => true
  | a :: rest => adminOkS a && adminOkSL rest
end

@[simp] theorem eraseL_eq (l : List Admin) : eraseL l = l.map eraseA := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [eraseL, ih]

@[simp] theorem adminOkSL_eq (l : List Admin) : adminOkSL l = l.all adminOkS := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [adminOkSL, ih]

@[simp] theorem eraseA_plain (i : V2.Instr) : eraseA (.plain i) = .plain (eraseI i) := rfl

@[simp] theorem eraseA_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    eraseA (.label n cont body) = .label n cont (body.map eraseA) := by simp [eraseA]

@[simp] theorem eraseA_frame (n : Nat) (fi : Frame) (body : List Admin) :
    eraseA (.frame n fi body) = .frame n fi (body.map eraseA) := by simp [eraseA]

@[simp] theorem eraseA_trap : eraseA .trap = .trap := rfl
@[simp] theorem eraseA_callAddr (a : FuncAddr) : eraseA (.callAddr a) = .callAddr a := rfl

@[simp] theorem adminOkS_plain (i : V2.Instr) : adminOkS (.plain i) = (ctrlOk i || storeOkI i) :=
  rfl

@[simp] theorem adminOkS_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    adminOkS (.label n cont body) = (cont.all ctrlOk && body.all adminOkS) := by simp [adminOkS]

@[simp] theorem adminOkS_frame (n : Nat) (fi : Frame) (body : List Admin) :
    adminOkS (.frame n fi body) = body.all adminOkS := by simp [adminOkS]

@[simp] theorem adminOkS_trap : adminOkS .trap = true := rfl
@[simp] theorem adminOkS_callAddr (a : FuncAddr) : adminOkS (.callAddr a) = true := rfl

/-- A covered instruction is not erased. -/
theorem eraseI_of_ctrlOk {i : V2.Instr} (h : ctrlOk i = true) : eraseI i = i := by
  cases i <;> first | rfl | simp [ctrlOk] at h

/-- A store is not covered. -/
theorem ctrlOk_of_storeOkI {i : V2.Instr} (h : storeOkI i = true) : ctrlOk i = false := by
  cases i <;> simp_all [storeOkI, ctrlOk]

/-- An erased store is `nop`. -/
theorem eraseI_of_storeOkI {i : V2.Instr} (h : storeOkI i = true) : eraseI i = .nop := by
  cases i <;> simp_all [storeOkI, eraseI]

mutual
/-- **Code that is already covered is not erased.** -/
theorem eraseA_of_adminOk : ∀ a : Admin, adminOk a = true → eraseA a = a
  | .plain i, h => by rw [eraseA_plain, eraseI_of_ctrlOk h]
  | .label n cont body, h => by
    have hb : body.all adminOk = true := by simp_all
    rw [eraseA_label, ← eraseL_eq, eraseL_of_adminOk body hb]
  | .frame n fi body, h => by
    have hb : body.all adminOk = true := by simp_all
    rw [eraseA_frame, ← eraseL_eq, eraseL_of_adminOk body hb]
  | .trap, _ => rfl
  | .callAddr _, _ => rfl
  | .refFuncAddr _, _ => rfl
  | .refHostAddr _, _ => rfl

/-- `eraseA_of_adminOk` on a sequence. -/
theorem eraseL_of_adminOk : ∀ l : List Admin, l.all adminOk = true → eraseL l = l
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show eraseA a :: eraseL l = a :: l
    rw [eraseA_of_adminOk a h.1, eraseL_of_adminOk l h.2]
end

theorem map_eraseA_of_adminOk {l : List Admin} (h : l.all adminOk = true) : l.map eraseA = l := by
  rw [← eraseL_eq]; exact eraseL_of_adminOk l h

mutual
/-- **Covered code is covered with stores.** -/
theorem adminOkS_of_adminOk : ∀ a : Admin, adminOk a = true → adminOkS a = true
  | .plain i, h => by simp_all
  | .label n cont body, h => by
    have hb : cont.all ctrlOk = true ∧ body.all adminOk = true := by simpa using h
    rw [adminOkS_label, hb.1, ← adminOkSL_eq, adminOkSL_of_adminOk body hb.2]
    rfl
  | .frame n fi body, h => by
    have hb : body.all adminOk = true := by simpa using h
    rw [adminOkS_frame, ← adminOkSL_eq, adminOkSL_of_adminOk body hb]
  | .trap, _ => rfl
  | .callAddr _, _ => rfl
  | .refFuncAddr _, _ => rfl
  | .refHostAddr _, _ => rfl

/-- `adminOkS_of_adminOk` on a sequence. -/
theorem adminOkSL_of_adminOk : ∀ l : List Admin, l.all adminOk = true → adminOkSL l = true
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show (adminOkS a && adminOkSL l) = true
    rw [adminOkS_of_adminOk a h.1, adminOkSL_of_adminOk l h.2]
    rfl
end

theorem all_adminOkS_of_adminOk {l : List Admin} (h : l.all adminOk = true) :
    l.all adminOkS = true := by
  rw [← adminOkSL_eq]; exact adminOkSL_of_adminOk l h

mutual
/-- **Erased covered code is covered** (without stores). -/
theorem adminOk_eraseA : ∀ a : Admin, adminOkS a = true → adminOk (eraseA a) = true
  | .plain i, h => by
    rw [eraseA_plain, Whole.adminOk_plain]
    rcases Bool.or_eq_true_iff.1 (by simpa using h) with h | h
    · rw [eraseI_of_ctrlOk h, h]
    · rw [eraseI_of_storeOkI h]; rfl
  | .label n cont body, h => by
    have hb : cont.all ctrlOk = true ∧ body.all adminOkS = true := by simpa using h
    rw [eraseA_label, Whole.adminOk_label, hb.1, ← eraseL_eq]
    exact (Bool.true_and _).trans (all_adminOk_eraseL body hb.2)
  | .frame n fi body, h => by
    rw [eraseA_frame, Whole.adminOk_frame, ← eraseL_eq]
    exact all_adminOk_eraseL body (by simpa using h)
  | .trap, _ => rfl
  | .callAddr _, _ => rfl
  | .refFuncAddr _, _ => rfl
  | .refHostAddr _, _ => rfl

/-- `adminOk_eraseA` on a sequence. -/
theorem all_adminOk_eraseL : ∀ l : List Admin, l.all adminOkS = true → (eraseL l).all adminOk = true
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show (adminOk (eraseA a) && (eraseL l).all adminOk) = true
    rw [adminOk_eraseA a h.1, all_adminOk_eraseL l h.2]
    rfl
end

@[simp] theorem eraseA_toAdmin (v : Val) : eraseA v.toAdmin = v.toAdmin :=
  eraseA_of_adminOk _ (Whole.adminOk_toAdmin v)

@[simp] theorem map_eraseA_vals (vs : List Val) : (vals vs).map eraseA = vals vs :=
  map_eraseA_of_adminOk (Whole.all_adminOk_vals vs)

@[simp] theorem adminOkS_toAdmin (v : Val) : adminOkS v.toAdmin = true :=
  adminOkS_of_adminOk _ (Whole.adminOk_toAdmin v)

@[simp] theorem all_adminOkS_vals (vs : List Val) : (vals vs).all adminOkS = true :=
  all_adminOkS_of_adminOk (Whole.all_adminOk_vals vs)

@[simp] theorem all_adminOkS_expression (is : List V2.Instr) :
    (expression is).all adminOkS = is.all (fun i => ctrlOk i || storeOkI i) := by
  simp [expression, Function.comp_def]

/-! ## Typing in `simEnv20T` from the erased typing -/

/-- A closed type name of the safe kind moves from `simEnv20` to `simEnv20T`. -/
abbrev Safe (x : IL.Id) : Prop :=
  (Sim.Round7.Script.evTyp (.varT x [])).all (RelFree.rfEvB RelFree.bad20) = true

theorem findCase_label20T : findCase adminCasesT "LABEL_%{%}%" =
    some (.tupT [.mk "n" nT, .mk "instr*" instrsT, .mk "admininstr*" adminsTy], []) := by
  with_unfolding_all rfl

theorem findCase_frame20T : findCase adminCasesT "FRAME_%{%}%" =
    some (.tupT [.mk "n" nT, .mk "frame" frameT, .mk "admininstr*" adminsTy], []) := by
  with_unfolding_all rfl

/-- **A label is a typed `admininstr` of `simEnv20T`** when its parts are typed there. -/
theorem typedV_adminLabel20T_mk {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h₁ : TypedV (simEnv20T B) nT (.num (.natN n)))
    (h₂ : TypedV (simEnv20T B) instrsT (.list (instrsToV cont)))
    (h₃ : TypedV (simEnv20T B) adminsTy (.list (adminsToV body))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.label n cont body)) :=
  Pure.typedV_closedCase20 (findTyp_admininstr20T B) findCase_label20T
    (Whole.hasTyp_tup3_mk20 h₁ h₂ h₃)

/-- **A frame is a typed `admininstr` of `simEnv20T`** when its parts are typed there. -/
theorem typedV_adminFrame20T_mk {n : Nat} {fr : Frame} {body : List Admin}
    (h₁ : TypedV (simEnv20T B) nT (.num (.natN n)))
    (h₂ : TypedV (simEnv20T B) frameT (frameV fr))
    (h₃ : TypedV (simEnv20T B) adminsTy (.list (adminsToV body))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.frame n fr body)) :=
  Pure.typedV_closedCase20 (findTyp_admininstr20T B) findCase_frame20T
    (Whole.hasTyp_tup3_mk20 h₁ h₂ h₃)

/-- A scalar store admitted by `storeOkI` is a typed `admininstr` of `simEnv20T`. -/
theorem typedV_storeOk20T {i : V2.Instr} (h : storeOkI i = true) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.plain i)) := by
  cases i with
  | intStore t p a =>
    refine StoreAgree.typedV_intStore20T t p a fun sz hp => ?_
    subst hp
    simpa [storeOkI] using h
  | floatStore t a => exact StoreAgree.typedV_floatStore20T t a
  | _ => simp [storeOkI] at h

/-- A list typed in `simEnv20`, elementwise moved to `simEnv20T`. -/
theorem typedV_admins_to20T {l : List Admin}
    (h : TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) adminsTy (.list (adminsToV l))) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l)) :=
  StoreAgree.typedV_list_to20T (by decide) h

mutual
/-- **An erased covered instruction typed in `simEnv20` is typed in `simEnv20T`** before
erasure. -/
theorem typedT_of_eraseA : ∀ a : Admin, adminOkS a = true →
    TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) (.varT "admininstr" []) (adminToV (eraseA a)) →
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV a)
  | .plain i, hok, h => by
    rcases Bool.or_eq_true_iff.1 (by simpa using hok) with hc | hs
    · rw [eraseA_plain, eraseI_of_ctrlOk hc] at h
      exact StoreAgree.typedV_to20T (by decide) h
    · exact typedV_storeOk20T hs
  | .label n cont body, hok, h => by
    have hb : cont.all ctrlOk = true ∧ body.all adminOkS = true := by simpa using hok
    rw [eraseA_label, ← eraseL_eq] at h
    obtain ⟨h₁, h₂, h₃⟩ := Whole.typedV_adminLabel20_iff.1 h
    exact typedV_adminLabel20T_mk (StoreAgree.typedV_to20T (by decide) h₁)
      (StoreAgree.typedV_list_to20T (by decide) h₂) (typedT_of_eraseL body (by simpa using hb.2) h₃)
  | .frame n fi body, hok, h => by
    rw [eraseA_frame, ← eraseL_eq] at h
    obtain ⟨h₁, h₂, h₃⟩ := Whole.typedV_adminFrame20_iff.1 h
    exact typedV_adminFrame20T_mk (StoreAgree.typedV_to20T (by decide) h₁)
      (StoreAgree.typedV_to20T (by decide) h₂) (typedT_of_eraseL body (by simpa using hok) h₃)
  | .trap, _, h => StoreAgree.typedV_to20T (by decide) h
  | .callAddr _, _, h => StoreAgree.typedV_to20T (by decide) h
  | .refFuncAddr _, _, h => StoreAgree.typedV_to20T (by decide) h
  | .refHostAddr _, _, h => StoreAgree.typedV_to20T (by decide) h

/-- **Erased covered code typed in `simEnv20` is typed in `simEnv20T`** before erasure. -/
theorem typedT_of_eraseL : ∀ l : List Admin, adminOkSL l = true →
    TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) adminsTy (.list (adminsToV (eraseL l))) →
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l))
  | [], _, _ => Sim.typedV_list_iff.2 (by simp [adminsToV])
  | a :: l, hok, h => by
    simp only [adminOkSL, Bool.and_eq_true] at hok
    have h' : TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) adminsTy
        (.list (adminToV (eraseA a) :: adminsToV (eraseL l))) := h
    have hl := typedT_of_eraseL l hok.2 (Sim.typedV_list_iff.2 fun u hu =>
      Sim.typedV_list_iff.1 h' u (List.mem_cons_of_mem _ hu))
    have ha := typedT_of_eraseA a hok.1 (Sim.typedV_list_iff.1 h' _ List.mem_cons_self)
    refine Sim.typedV_list_iff.2 fun u hu => ?_
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ha
    · exact Sim.typedV_list_iff.1 hl u hu
end

/-- `typedT_of_eraseL`, with the `List.all` form of the hypothesis. -/
theorem typedT_of_erase {l : List Admin} (hok : l.all adminOkS = true)
    (h : TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) adminsTy (.list (adminsToV (l.map eraseA)))) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l)) :=
  typedT_of_eraseL l (by simpa using hok) (by simpa using h)

/-! ## `instr` and `admininstr` in `simEnv20T` -/

/-- The cases of the corrected `instr`. -/
noncomputable def instrCasesT : List TypCase := Whole.instrCases20.map fixCase

set_option maxRecDepth 8000000 in
theorem findTyp_instr20T : (simEnv20T B).findTyp? "instr" =
    some ([], [.instD [] [] (.variantT instrCasesT)]) := by
  with_unfolding_all rfl

theorem adminCasesT_eq : adminCasesT = instrCasesT ++ Whole.adminCases20.map fixCase := by
  rw [instrCasesT, ← List.map_append, ← Whole.recCases_admininstr20]
  rfl

theorem adminCasesT_heads : (Whole.adminCases20.map fixCase).map Whole.caseHead =
    Whole.adminHeads20 := by
  with_unfolding_all rfl

/-- **In `simEnv20T`, a plain instruction typed as an `admininstr` is typed as an `instr`.** -/
theorem typedV_instr_of_admin20T (i : V2.Instr)
    (h : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i)) :
    TypedV (simEnv20T B) (.varT "instr" []) (instrToV i) := by
  obtain ⟨op, w, he, hop⟩ := Whole.instrToV_notAdmin20 i
  rw [he] at h ⊢
  have hd : op ∉ (Whole.adminCases20.map fixCase).map Whole.caseHead := adminCasesT_heads ▸ hop
  obtain ⟨op', w', he', hc⟩ := hasTypDef_variantT_iff.1
    (Whole.hasTypDef_of_closed (findTyp_admininstr20T B) (h _ Whole.valsOnly_empty20))
  obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he'
  rw [adminCasesT_eq, Whole.hasTypCase_append_iff hd] at hc
  exact Whole.typedV_of_empty20 (hasTyp_varT_case rfl (findTyp_instr20T (B := B))
    Equiv.evalArgs_nil matchArgs_nil hc)

/-- **A plain code sequence typed as `admininstr*` in `simEnv20T` is a typed `instr*`.** -/
theorem typedV_instrs_of_admins20T {is : List V2.Instr}
    (h : TypedV (simEnv20T B) adminsTy (.list (adminsToV (expression is)))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV (expression is))) := by
  rw [Pure.adminsToV_expression] at h ⊢
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 (Whole.instrsToV_map20 is ▸ hu)
  exact typedV_instr_of_admin20T i (Sim.typedV_list_iff.1 h _ hu)

end Silmaril.Wasm.SpecTec.Sim20.StoreGood
