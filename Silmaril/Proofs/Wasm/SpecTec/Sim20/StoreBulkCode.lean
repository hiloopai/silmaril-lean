module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFn.Thms

/-!
# Covered code with the memory bulk instructions, typed in `simEnv20T` from its erasure

Round 5's `StoreFn.Good20F` covers code `StoreDeep.okD`, which admits no bulk instruction. Here
`memory.fill`, `memory.copy` and `memory.init` are admitted at every depth, in the code and in the
store's functions.

* `bulkOkI`: the instructions admitted beyond `okD`: `memory.fill`, `memory.copy`,
  `memory.init`, `table.fill`, `table.set`, and `table.copy`, `table.init`,
  `elem.drop` and `data.drop`.
* `ctrlOkB m`: `StoreDeep.ctrlOkD m` with `bulkOkI` admitted at every depth of `block`, `loop`
  and `if`; `okB m`: administrative code over it. `okD` code is `okB` (`okB_of_okD`).
* The deep erasure `StoreDeep.eD` keeps them (`eD_of_bulkOkI`), so the typing part
  `StoreFn.TypF` is unchanged.
* **`typedT_of_eBL`**: `okB` code whose deep erasure is typed in `simEnv20` is typed in
  `simEnv20T`. Blocks, loops, `if`s, labels and frames are taken apart as in
  `StoreDeep.typedT_of_eDL`; a bulk instruction is its own erasure and moves to `simEnv20T` as a
  closed `admininstr` (`StoreAgree.typedV_to20T`).
* `StoreOkB s`: every function of `s` is a Wasm function with an `okB` body.
  **`typedT_state_of_erasedB`**: over a `StoreOkB` store, a state whose erasure is typed in
  `simEnv20` is typed in `simEnv20T`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (TypedI)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (storeOkI)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eD eDA eDL eDAL ctrlOkD okD BodyT typedT_instrs_of
  typedT_block_of typedT_loop_of typedT_if_of typedT_labelD typedT_frameD)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (eraseS eraseFI eraseFI_code)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The covered code -/

/-- **The instructions admitted beyond `okD`**: `memory.fill`, `memory.copy`, `memory.init`,
`table.fill`, `table.set` (which `table.fill`, `table.copy` and `table.init` rewrite to),
`table.copy`, `table.init`, `elem.drop` and `data.drop`. -/
def bulkOkI : V2.Instr → Bool
  | .memoryFill | .memoryCopy | .memoryInit _ | .tableFill _ | .tableSet _ | .tableCopy _ _
  | .tableInit _ _ | .elemDrop _ | .dataDrop _ => true
  | _ => false

mutual
/-- **Covered instructions with stores and the memory bulk instructions at every depth**, in the module `m`. -/
def ctrlOkB (m : ModuleInst) : V2.Instr → Bool
  | .block _ body | .loop _ body => ctrlOkBL m body
  | .if_ _ l r => ctrlOkBL m l && ctrlOkBL m r
  | i => ctrlOkD m i || bulkOkI i

/-- `ctrlOkB` on a sequence. -/
def ctrlOkBL (m : ModuleInst) : List V2.Instr → Bool
  | [] => true
  | i :: is => ctrlOkB m i && ctrlOkBL m is
end

@[simp] theorem ctrlOkBL_eq (m : ModuleInst) (l : List V2.Instr) :
    ctrlOkBL m l = l.all (ctrlOkB m) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ctrlOkBL, ih]

@[simp] theorem ctrlOkB_block (m : ModuleInst) (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOkB m (.block bt b) = b.all (ctrlOkB m) := by simp [ctrlOkB]

@[simp] theorem ctrlOkB_loop (m : ModuleInst) (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOkB m (.loop bt b) = b.all (ctrlOkB m) := by simp [ctrlOkB]

@[simp] theorem ctrlOkB_if (m : ModuleInst) (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) :
    ctrlOkB m (.if_ bt b₁ b₂) = (b₁.all (ctrlOkB m) && b₂.all (ctrlOkB m)) := by simp [ctrlOkB]

@[simp] theorem ctrlOkB_memoryFill (m : ModuleInst) : ctrlOkB m .memoryFill = true := by
  simp [ctrlOkB, bulkOkI]

@[simp] theorem ctrlOkB_memoryCopy (m : ModuleInst) : ctrlOkB m .memoryCopy = true := by
  simp [ctrlOkB, bulkOkI]

@[simp] theorem ctrlOkB_memoryInit (m : ModuleInst) (x : DataIdx) :
    ctrlOkB m (.memoryInit x) = true := by
  simp [ctrlOkB, bulkOkI]

mutual
/-- **Covered administrative code with stores and the memory bulk instructions at every depth**, in the module
`m`. -/
def okB (m : ModuleInst) : Admin → Bool
  | .plain i => ctrlOkB m i
  | .label _ cont body => ctrlOkBL m cont && okBL m body
  | .frame _ fi body => okBL fi.module body
  | .trap | .callAddr _ | .refFuncAddr _ | .refHostAddr _ => true

/-- `okB` on a sequence. -/
def okBL (m : ModuleInst) : List Admin → Bool
  | [] => true
  | a :: rest => okB m a && okBL m rest
end

@[simp] theorem okBL_eq (m : ModuleInst) (l : List Admin) : okBL m l = l.all (okB m) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [okBL, ih]

@[simp] theorem okB_plain (m : ModuleInst) (i : V2.Instr) : okB m (.plain i) = ctrlOkB m i := rfl

@[simp] theorem okB_label (m : ModuleInst) (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    okB m (.label n cont body) = (cont.all (ctrlOkB m) && body.all (okB m)) := by simp [okB]

@[simp] theorem okB_frame (m : ModuleInst) (n : Nat) (fi : Frame) (body : List Admin) :
    okB m (.frame n fi body) = body.all (okB fi.module) := by simp [okB]

@[simp] theorem okB_trap (m : ModuleInst) : okB m .trap = true := rfl
@[simp] theorem okB_callAddr (m : ModuleInst) (a : FuncAddr) : okB m (.callAddr a) = true := rfl
@[simp] theorem okB_refFuncAddr (m : ModuleInst) (a : FuncAddr) :
    okB m (.refFuncAddr a) = true := rfl
@[simp] theorem okB_refHostAddr (m : ModuleInst) (a : HostAddr) :
    okB m (.refHostAddr a) = true := rfl

/-! ## `okD` code is `okB` -/

/-- `ctrlOkD` instructions are `ctrlOkB`, below a size bound. -/
theorem ctrlOkB_of_ctrlOkD_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOkD m i = true → ctrlOkB m i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi h
    have hb : ∀ b : List V2.Instr, sizeOf b < n → b.all (ctrlOkD m) = true →
        b.all (ctrlOkB m) = true :=
      fun b hs hb => List.all_eq_true.2 fun x hx =>
        ih x (by have := List.sizeOf_lt_of_mem hx; omega) (List.all_eq_true.1 hb x hx)
    cases i with
    | block bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | loop bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | if_ bt l r =>
      have hlr : l.all (ctrlOkD m) = true ∧ r.all (ctrlOkD m) = true := by simpa using h
      simp only [ctrlOkB_if, Bool.and_eq_true]
      exact ⟨hb l (by simp at hi; omega) hlr.1, hb r (by simp at hi; omega) hlr.2⟩
    | _ => simp [ctrlOkB, h]

/-- **`ctrlOkD` instructions are `ctrlOkB`.** -/
theorem ctrlOkB_of_ctrlOkD {m : ModuleInst} {i : V2.Instr} (h : ctrlOkD m i = true) :
    ctrlOkB m i = true :=
  ctrlOkB_of_ctrlOkD_lt m _ i (Nat.lt_succ_self _) h

theorem all_ctrlOkB_of_ctrlOkD {m : ModuleInst} {l : List V2.Instr}
    (h : l.all (ctrlOkD m) = true) : l.all (ctrlOkB m) = true :=
  List.all_eq_true.2 fun x hx => ctrlOkB_of_ctrlOkD (List.all_eq_true.1 h x hx)

mutual
/-- **`okD` code is `okB`.** -/
theorem okB_of_okD : ∀ (m : ModuleInst) (a : Admin), okD m a = true → okB m a = true
  | m, .plain i, h => ctrlOkB_of_ctrlOkD (m := m) (by simpa using h)
  | m, .label n cont body, h => by
    have hb : cont.all (ctrlOkD m) = true ∧ body.all (okD m) = true := by simpa using h
    rw [okB_label, all_ctrlOkB_of_ctrlOkD hb.1, ← okBL_eq,
      okBL_of_okDL m body (by simpa using hb.2)]
    rfl
  | _, .frame n fi body, h => by
    rw [okB_frame, ← okBL_eq]
    exact okBL_of_okDL fi.module body (by simpa using h)
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `okB_of_okD` on a sequence. -/
theorem okBL_of_okDL : ∀ (m : ModuleInst) (l : List Admin), StoreDeep.okDL m l = true →
    okBL m l = true
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [StoreDeep.okDL, Bool.and_eq_true] at h
    show (okB m a && okBL m l) = true
    rw [okB_of_okD m a h.1, okBL_of_okDL m l h.2]
    rfl
end

theorem all_okB_of_okD {m : ModuleInst} {l : List Admin} (h : l.all (okD m) = true) :
    l.all (okB m) = true := by
  rw [← okBL_eq]; exact okBL_of_okDL m l (by simpa using h)

@[simp] theorem okB_toAdmin (m : ModuleInst) (v : Val) : okB m v.toAdmin = true :=
  okB_of_okD m _ (StoreDeep.okD_toAdmin m v)

@[simp] theorem all_okB_vals (m : ModuleInst) (vs : List Val) : (vals vs).all (okB m) = true :=
  all_okB_of_okD (StoreDeep.all_okD_vals m vs)

@[simp] theorem all_okB_expression (m : ModuleInst) (is : List V2.Instr) :
    (expression is).all (okB m) = is.all (ctrlOkB m) := by
  simp [expression, Function.comp_def]

/-! ## The erasure keeps the bulk instructions -/

theorem eD_of_bulkOkI {i : V2.Instr} (h : bulkOkI i = true) : eD i = i := by
  cases i <;> simp_all [bulkOkI, eD]

/-! ## Typing in `simEnv20T` from the deep erasure -/

/-- An instruction without nested code, from its erased typing. -/
theorem typedT_flatB {m : ModuleInst} {i : V2.Instr}
    (hok : (ctrlOkD m i || bulkOkI i) = true) (h : TypedI B (eD i))
    (hnb : ∀ bt b, i ≠ .block bt b) (hnl : ∀ bt b, i ≠ .loop bt b)
    (hni : ∀ bt l r, i ≠ .if_ bt l r) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i) := by
  rcases Bool.or_eq_true_iff.1 hok with hd | hb
  · have hflat : (GoodMerge.ctrlOkM m i || storeOkI i) = true := by
      cases i <;> first
        | exact absurd rfl (hnb _ _) | exact absurd rfl (hnl _ _) | exact absurd rfl (hni _ _ _)
        | simpa [StoreDeep.ctrlOkD] using hd
    exact StoreDeep.typedT_flat hflat h
  · rw [eD_of_bulkOkI hb] at h
    exact StoreAgree.typedV_to20T (by decide) h

/-- **An instruction whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`**, below a
size bound. -/
theorem typedT_of_eBI_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOkB m i = true → TypedI B (eD i) →
      TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi hok h
    have hb : ∀ b : List V2.Instr, sizeOf b < n → b.all (ctrlOkB m) = true → BodyT B b :=
      fun b hs hb => typedT_instrs_of fun j hj =>
        ih j (by have := List.sizeOf_lt_of_mem hj; omega) (List.all_eq_true.1 hb j hj)
    cases i with
    | block bt b => exact typedT_block_of h (hb b (by simp at hi; omega) (by simpa using hok))
    | loop bt b => exact typedT_loop_of h (hb b (by simp at hi; omega) (by simpa using hok))
    | if_ bt l r =>
      have hlr : l.all (ctrlOkB m) = true ∧ r.all (ctrlOkB m) = true := by simpa using hok
      exact typedT_if_of h (hb l (by simp at hi; omega) hlr.1) (hb r (by simp at hi; omega) hlr.2)
    | _ => exact typedT_flatB (by simpa [ctrlOkB] using hok) h (by simp) (by simp) (by simp)

/-- **An instruction whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`.** -/
theorem typedT_of_eBI {m : ModuleInst} {i : V2.Instr} (hok : ctrlOkB m i = true)
    (h : TypedI B (eD i)) : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i) :=
  typedT_of_eBI_lt m _ i (Nat.lt_succ_self _) hok h

/-- **An `instr*` whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`.** -/
theorem typedT_instrs_of_eB {m : ModuleInst} {b : List V2.Instr} (hok : b.all (ctrlOkB m) = true)
    (h : TypedV (E20 B) Pure.instrsT (.list (instrsToV (b.map eD)))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b)) :=
  typedT_instrs_of (fun j hj => typedT_of_eBI (List.all_eq_true.1 hok j hj)) h

theorem okBL_of_label {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h : okB m (.label n cont body) = true) :
    cont.all (ctrlOkB m) = true ∧ okBL m body = true := by
  have hb : cont.all (ctrlOkB m) = true ∧ body.all (okB m) = true := by simpa using h
  exact ⟨hb.1, by simpa using hb.2⟩

/-- A label, from its erased typing and the typing of its body. -/
theorem typedT_labelB {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (hc : cont.all (ctrlOkB m) = true)
    (h : TypedV (E20 B) (.varT "admininstr" []) (adminToV (eDA (.label n cont body))))
    (ih : TypedV (E20 B) adminsTy (.list (adminsToV (eDAL body))) →
      TypedV (simEnv20T B) adminsTy (.list (adminsToV body))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.label n cont body)) := by
  have h' : TypedV (E20 B) (.varT "admininstr" [])
      (adminToV (.label n (cont.map eD) (eDAL body))) := by
    rwa [StoreDeep.eDA_label, ← StoreDeep.eDAL_eq] at h
  obtain ⟨h₁, h₂, h₃⟩ := Whole.typedV_adminLabel20_iff.1 h'
  exact StoreGood.typedV_adminLabel20T_mk (StoreAgree.typedV_to20T (by decide) h₁)
    (typedT_instrs_of_eB hc h₂) (ih h₃)

mutual
/-- **`okB` code whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`.** -/
theorem typedT_of_eBAM : ∀ (m : ModuleInst) (a : Admin), okB m a = true →
    TypedV (E20 B) (.varT "admininstr" []) (adminToV (eDA a)) →
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV a)
  | m, .plain i, hok, h => typedT_of_eBI (m := m) hok h
  | m, .label n cont body, hok, h =>
    typedT_labelB (okBL_of_label hok).1 h fun h₃ =>
      typedT_of_eBLM m body (okBL_of_label hok).2 h₃
  | _, .frame n fi body, hok, h =>
    typedT_frameD h fun h₃ => typedT_of_eBLM fi.module body (by simpa using hok) h₃
  | _, .trap, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .callAddr _, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .refFuncAddr _, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .refHostAddr _, _, h => StoreAgree.typedV_to20T (by decide) h

/-- `typedT_of_eBAM` on a sequence. -/
theorem typedT_of_eBLM : ∀ (m : ModuleInst) (l : List Admin), okBL m l = true →
    TypedV (E20 B) adminsTy (.list (adminsToV (eDAL l))) →
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l))
  | _, [], _, _ => Sim.typedV_list_iff.2 (by simp [adminsToV])
  | m, a :: l, hok, h => by
    simp only [okBL, Bool.and_eq_true] at hok
    have h' : TypedV (E20 B) adminsTy (.list (adminToV (eDA a) :: adminsToV (eDAL l))) := h
    have hl := typedT_of_eBLM m l hok.2 (Sim.typedV_list_iff.2 fun u hu =>
      Sim.typedV_list_iff.1 h' u (List.mem_cons_of_mem _ hu))
    have ha := typedT_of_eBAM m a hok.1 (Sim.typedV_list_iff.1 h' _ List.mem_cons_self)
    refine Sim.typedV_list_iff.2 fun u hu => ?_
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ha
    · exact Sim.typedV_list_iff.1 hl u hu
end

/-- **Covered code whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`.** -/
theorem typedT_of_eBL {m : ModuleInst} {l : List Admin} (hok : l.all (okB m) = true)
    (h : TypedV (E20 B) adminsTy (.list (adminsToV (l.map eDA)))) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l)) :=
  typedT_of_eBLM m l (by simpa using hok) (by simpa using h)

/-! ## The store -/

/-- **Every function of the store is a Wasm function whose body is covered, stores and
the memory bulk instructions at every depth included, in its own module.** -/
def StoreOkB (s : Store H) : Prop :=
  ∀ a fi, s.funcInst? a = some fi → ∃ fn, fi.code = .wasm fn ∧ fn.body.all (ctrlOkB fi.module) = true

theorem StoreOkB.not_host {s : Store H} (hs : StoreOkB s) {a : FuncAddr} {fi : FuncInst H} {h : H}
    (hf : s.funcInst? a = some fi) (hc : fi.code = .host h) : False := by
  obtain ⟨fn, hc', -⟩ := hs a fi hf
  rw [hc] at hc'
  cases hc'

theorem storeOkB_of_funcs {s s' : Store H} (h : StoreOkB s) (e : s'.funcs = s.funcs) :
    StoreOkB s' := fun a fi hf => h a fi (by simpa [Store.funcInst?, e] using hf)

/-- **`StoreOkD` stores are `StoreOkB`.** -/
theorem storeOkB_of_storeOkD {s : Store H} (h : StoreFn.StoreOkD s) : StoreOkB s := by
  intro a fi hf
  obtain ⟨fn, hc, hb⟩ := h a fi hf
  exact ⟨fn, hc, all_ctrlOkB_of_ctrlOkD hb⟩

/-- A function instance whose erasure is typed in `simEnv20`, with an `okB` body, is typed in
`simEnv20T`. -/
theorem typedT_funcInst_of_erasedB {fi : FuncInst H} {fn : V2.Func} (hc : fi.code = .wasm fn)
    (hb : fn.body.all (ctrlOkB fi.module) = true)
    (h : TypedV (E20 B) (.varT "funcinst" []) (funcInstV hn (eraseFI fi))) :
    TypedV (simEnv20T B) (.varT "funcinst" []) (funcInstV hn fi) := by
  have hc' := eraseFI_code hc
  rw [Whole.funcInstV_wasm hc'] at h
  have h₀ := Whole.hasTypFields_of_closed Whole.findTyp_funcinst20 h
  obtain ⟨hty, h₀⟩ := Whole.hasTypFields_cons_nil_iff.1 h₀
  obtain ⟨hmo, h₀⟩ := Whole.hasTypFields_cons_nil_iff.1 h₀
  obtain ⟨hco, -⟩ := Whole.hasTypFields_cons_nil_iff.1 h₀
  obtain ⟨p₁, p₂, p₃⟩ := StoreFn.func_parts Whole.findTyp_func20 Whole.findTyp_expr20
    (Whole.typedV_of_empty20 hco)
  have hbody : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV fn.body)) :=
    typedT_instrs_of_eB hb (by simpa using p₃)
  have hfunc : TypedV (simEnv20T B) (.varT "func" []) (Whole.codeV20 fn) :=
    StoreFn.func_mk StoreFn.findTyp_funcT StoreFn.findTyp_exprT
      (StoreAgree.typedV_to20T (by decide) p₁)
      (StoreAgree.typedV_list_to20T (x := "local") (by decide) p₂) hbody
  rw [Whole.funcInstV_wasm hc]
  exact Whole.typedV_structG StoreFn.findTyp_funcinstT (Whole.hasTypFields_consG
    (StoreAgree.typedV_to20T (x := "functype") (by decide) (Whole.typedV_of_empty20 hty))
    (Whole.hasTypFields_consG (StoreAgree.typedV_to20T (x := "moduleinst") (by decide)
      (Whole.typedV_of_empty20 hmo)) (Whole.hasTypFields_oneG hfunc)))

/-- **A state whose erasure is typed in `simEnv20`, over a `StoreOkB` store, is typed in
`simEnv20T`.** -/
theorem typedT_state_of_erasedB {s : Store H} {f : Frame} (hs : StoreOkB s)
    (h : TypedV (E20 B) stateT (stateV hn (eraseS s) f)) :
    TypedV (simEnv20T B) stateT (stateV hn s f) := by
  obtain ⟨hst, hfr⟩ := Whole.typedV_stateV_iff.1 h
  have S := Whole.typedV_storeV_iff.1 hst
  refine StoreFn.typedT_stateV_iff.2 ⟨StoreFn.typedT_storeV_iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    StoreAgree.typedV_to20T (x := "frame") (by decide) hfr⟩
  · refine Sim.typedV_list_iff.2 fun u hu => ?_
    obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hu
    obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
    obtain ⟨fn, hc, hb⟩ := hs a fi (by simpa [Store.funcInst?] using ha)
    refine typedT_funcInst_of_erasedB hc hb (Sim.typedV_list_iff.1 S.funcs _ ?_)
    exact List.mem_map_of_mem (List.mem_map_of_mem hfi)
  · exact StoreAgree.typedV_list_to20T (x := "globalinst") (by decide) S.globals
  · exact StoreAgree.typedV_list_to20T (x := "tableinst") (by decide) S.tables
  · exact StoreAgree.typedV_list_to20T (x := "meminst") (by decide) S.mems
  · exact StoreAgree.typedV_list_to20T (x := "eleminst") (by decide) S.elems
  · exact StoreAgree.typedV_list_to20T (x := "datainst") (by decide) S.datas

/-- The state of a `TypF` configuration over a `StoreOkB` store is typed in `simEnv20T`. -/
theorem typF_stateB {c : Config H} (h : StoreFn.TypF B hn c) (hs : StoreOkB c.store) :
    TypedV (simEnv20T B) stateT (stateV hn c.store c.frame) :=
  typedT_state_of_erasedB hs h.state

/-- The code of a `TypF` configuration, `okB` in some module, is typed in `simEnv20T`. -/
theorem typF_codeB {m : ModuleInst} {c : Config H} (h : StoreFn.TypF B hn c)
    (hok : c.code.all (okB m) = true) : TypedV (simEnv20T B) adminsTy (.list (adminsToV c.code)) :=
  typedT_of_eBL hok h.code

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
