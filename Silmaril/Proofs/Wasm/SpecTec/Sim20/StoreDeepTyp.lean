module

public import Silmaril.Wasm.SpecTec.Sim20.GoodMerge.Thms

/-!
# Stores inside instruction trees: the covered code, the deep erasure, and typing in `simEnv20T`

Round 5's `Good20M` admits scalar stores only at the administrative level. Here a store may also
stand inside a block body, an `if` branch or a label continuation, at any depth. The store's
functions stay store-free (`GoodMerge.StoreOkM`), so the state stays typed in `simEnv20`.

* `ctrlOkD m`: `GoodMerge.ctrlOkM m` with scalar stores (`StoreGood.storeOkI`) admitted at every
  depth of `block`, `loop` and `if`. `okD m`: administrative code over it; a label continuation is
  `ctrlOkD`, and a frame body is read in its frame's module.
* `eD`, `eDA`: the **deep erasure**, every store replaced by `nop`, inside block bodies, branches
  and label continuations as well.
  * Store-free covered code (`GoodMerge.okA false`) is unchanged (`eDA_of_okA_false`).
  * Erased covered code is store-free covered code (`okA_false_eDA`).
  * On `Good20M`'s code the deep and the shallow erasures agree (`eDA_eq_eraseA`).
* **`typedT_of_eDI`**: an instruction whose deep erasure is typed in `simEnv20` is typed in
  `simEnv20T`. Blocks, loops and `if`s are taken apart in `simEnv20`
  (`Whole.typed_block_inv20`, `typed_loop_inv20`, `typed_if20`) and rebuilt in `simEnv20T`
  (`typedT_block`, `typedT_loop`, `typedT_if`, cases found by `findCase` on the corrected list).
* **`typedT_of_eDL`**: the same for administrative code (`typedT_of_eDAM`), and `typedT_instrs_of_eD`
  for an `instr*` (a label continuation or a branch).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreDeep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T adminCasesT findTyp_admininstr20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk TypedI)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (storeOkI eraseA eraseI)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (ctrlOkI)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (ctrlOkM okA StoreOkM)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The covered code -/

mutual
/-- **Covered instructions with stores at every depth**, in the module `m`. -/
def ctrlOkD (m : ModuleInst) : V2.Instr → Bool
  | .block _ body | .loop _ body => ctrlOkDL m body
  | .if_ _ l r => ctrlOkDL m l && ctrlOkDL m r
  | i => ctrlOkM m i || storeOkI i

/-- `ctrlOkD` on a sequence. -/
def ctrlOkDL (m : ModuleInst) : List V2.Instr → Bool
  | [] => true
  | i :: is => ctrlOkD m i && ctrlOkDL m is
end

@[simp] theorem ctrlOkDL_eq (m : ModuleInst) (l : List V2.Instr) :
    ctrlOkDL m l = l.all (ctrlOkD m) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ctrlOkDL, ih]

@[simp] theorem ctrlOkD_block (m : ModuleInst) (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOkD m (.block bt b) = b.all (ctrlOkD m) := by simp [ctrlOkD]

@[simp] theorem ctrlOkD_loop (m : ModuleInst) (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOkD m (.loop bt b) = b.all (ctrlOkD m) := by simp [ctrlOkD]

@[simp] theorem ctrlOkD_if (m : ModuleInst) (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) :
    ctrlOkD m (.if_ bt b₁ b₂) = (b₁.all (ctrlOkD m) && b₂.all (ctrlOkD m)) := by simp [ctrlOkD]

mutual
/-- **Covered administrative code with stores at every depth**, in the module `m`. -/
def okD (m : ModuleInst) : Admin → Bool
  | .plain i => ctrlOkD m i
  | .label _ cont body => ctrlOkDL m cont && okDL m body
  | .frame _ fi body => okDL fi.module body
  | .trap | .callAddr _ | .refFuncAddr _ | .refHostAddr _ => true

/-- `okD` on a sequence. -/
def okDL (m : ModuleInst) : List Admin → Bool
  | [] => true
  | a :: rest => okD m a && okDL m rest
end

@[simp] theorem okDL_eq (m : ModuleInst) (l : List Admin) : okDL m l = l.all (okD m) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [okDL, ih]

@[simp] theorem okD_plain (m : ModuleInst) (i : V2.Instr) : okD m (.plain i) = ctrlOkD m i := rfl

@[simp] theorem okD_label (m : ModuleInst) (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    okD m (.label n cont body) = (cont.all (ctrlOkD m) && body.all (okD m)) := by simp [okD]

@[simp] theorem okD_frame (m : ModuleInst) (n : Nat) (fi : Frame) (body : List Admin) :
    okD m (.frame n fi body) = body.all (okD fi.module) := by simp [okD]

@[simp] theorem okD_trap (m : ModuleInst) : okD m .trap = true := rfl
@[simp] theorem okD_callAddr (m : ModuleInst) (a : FuncAddr) : okD m (.callAddr a) = true := rfl
@[simp] theorem okD_refFuncAddr (m : ModuleInst) (a : FuncAddr) :
    okD m (.refFuncAddr a) = true := rfl
@[simp] theorem okD_refHostAddr (m : ModuleInst) (a : HostAddr) :
    okD m (.refHostAddr a) = true := rfl

@[simp] theorem okD_toAdmin (m : ModuleInst) (v : Val) : okD m v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;>
    simp [Val.toAdmin, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk]

@[simp] theorem all_okD_vals (m : ModuleInst) (vs : List Val) : (vals vs).all (okD m) = true := by
  simp [vals]

@[simp] theorem all_okD_expression (m : ModuleInst) (is : List V2.Instr) :
    (expression is).all (okD m) = is.all (ctrlOkD m) := by
  simp [expression, Function.comp_def]

/-! ## The deep erasure -/

mutual
/-- **Erase every scalar store of an instruction**, at every depth. -/
def eD : V2.Instr → V2.Instr
  | .intStore .. => .nop
  | .floatStore .. => .nop
  | .block bt body => .block bt (eDL body)
  | .loop bt body => .loop bt (eDL body)
  | .if_ bt l r => .if_ bt (eDL l) (eDL r)
  | i => i

/-- `eD` on a sequence. -/
def eDL : List V2.Instr → List V2.Instr
  | [] => []
  | i :: is => eD i :: eDL is
end

@[simp] theorem eDL_eq (l : List V2.Instr) : eDL l = l.map eD := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [eDL, ih]

@[simp] theorem eD_block (bt : V2.BlockType) (b : List V2.Instr) :
    eD (.block bt b) = .block bt (b.map eD) := by simp [eD]

@[simp] theorem eD_loop (bt : V2.BlockType) (b : List V2.Instr) :
    eD (.loop bt b) = .loop bt (b.map eD) := by simp [eD]

@[simp] theorem eD_if (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) :
    eD (.if_ bt b₁ b₂) = .if_ bt (b₁.map eD) (b₂.map eD) := by simp [eD]

mutual
/-- **Erase every scalar store of administrative code**, in label continuations as well. -/
def eDA : Admin → Admin
  | .plain i => .plain (eD i)
  | .label n cont body => .label n (eDL cont) (eDAL body)
  | .frame n fi body => .frame n fi (eDAL body)
  | .trap => .trap
  | .callAddr a => .callAddr a
  | .refFuncAddr a => .refFuncAddr a
  | .refHostAddr a => .refHostAddr a

/-- `eDA` on a sequence. -/
def eDAL : List Admin → List Admin
  | [] => []
  | a :: l => eDA a :: eDAL l
end

@[simp] theorem eDAL_eq (l : List Admin) : eDAL l = l.map eDA := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [eDAL, ih]

@[simp] theorem eDA_plain (i : V2.Instr) : eDA (.plain i) = .plain (eD i) := rfl

@[simp] theorem eDA_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    eDA (.label n cont body) = .label n (cont.map eD) (body.map eDA) := by simp [eDA]

@[simp] theorem eDA_frame (n : Nat) (fi : Frame) (body : List Admin) :
    eDA (.frame n fi body) = .frame n fi (body.map eDA) := by simp [eDA]

@[simp] theorem eDA_trap : eDA .trap = .trap := rfl
@[simp] theorem eDA_callAddr (a : FuncAddr) : eDA (.callAddr a) = .callAddr a := rfl

/-- A store-free covered instruction is not erased, below a size bound. -/
theorem eD_of_ctrlOkM_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOkM m i = true → eD i = i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi h
    have hb : ∀ b : List V2.Instr, sizeOf b < n → b.all (ctrlOkM m) = true → b.map eD = b :=
      fun b hs hb => (List.map_congr_left (g := id) fun x hx =>
        ih x (by have := List.sizeOf_lt_of_mem hx; omega) (List.all_eq_true.1 hb x hx)).trans
          (List.map_id b)
    cases i with
    | block bt b => rw [eD_block, hb b (by simp at hi; omega) (by simpa using h)]
    | loop bt b => rw [eD_loop, hb b (by simp at hi; omega) (by simpa using h)]
    | if_ bt l r =>
      have hlr : l.all (ctrlOkM m) = true ∧ r.all (ctrlOkM m) = true := by simpa using h
      rw [eD_if, hb l (by simp at hi; omega) hlr.1, hb r (by simp at hi; omega) hlr.2]
    | _ => first | rfl | simp [GoodMerge.ctrlOkM, ctrlOkI, ctrlOk] at h

/-- **A store-free covered instruction is not erased.** -/
theorem eD_of_ctrlOkM {m : ModuleInst} {i : V2.Instr} (h : ctrlOkM m i = true) : eD i = i :=
  eD_of_ctrlOkM_lt m _ i (Nat.lt_succ_self _) h

theorem map_eD_of_ctrlOkM {m : ModuleInst} {l : List V2.Instr} (h : l.all (ctrlOkM m) = true) :
    l.map eD = l :=
  (List.map_congr_left (g := id) fun x hx => eD_of_ctrlOkM (List.all_eq_true.1 h x hx)).trans
    (List.map_id l)

/-- An erased covered instruction is store-free covered, below a size bound. -/
theorem ctrlOkM_eD_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOkD m i = true → ctrlOkM m (eD i) = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi h
    have hb : ∀ b : List V2.Instr, sizeOf b < n → b.all (ctrlOkD m) = true →
        (b.map eD).all (ctrlOkM m) = true :=
      fun b hs hb => by
        simp only [List.all_map, List.all_eq_true, Function.comp_apply]
        exact fun x hx => ih x (by have := List.sizeOf_lt_of_mem hx; omega) (List.all_eq_true.1 hb x hx)
    cases i with
    | block bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | loop bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | if_ bt l r =>
      have hlr : l.all (ctrlOkD m) = true ∧ r.all (ctrlOkD m) = true := by simpa using h
      simp only [eD_if, GoodMerge.ctrlOkM_if, Bool.and_eq_true]
      exact ⟨hb l (by simp at hi; omega) hlr.1, hb r (by simp at hi; omega) hlr.2⟩
    | intStore => simp [eD, GoodMerge.ctrlOkM, ctrlOkI, ctrlOk]
    | floatStore => simp [eD, GoodMerge.ctrlOkM, ctrlOkI, ctrlOk]
    | _ => revert h; simp [ctrlOkD, eD, storeOkI]

/-- **An erased covered instruction is store-free covered.** -/
theorem ctrlOkM_eD {m : ModuleInst} {i : V2.Instr} (h : ctrlOkD m i = true) :
    ctrlOkM m (eD i) = true :=
  ctrlOkM_eD_lt m _ i (Nat.lt_succ_self _) h

theorem all_ctrlOkM_eD {m : ModuleInst} {l : List V2.Instr} (h : l.all (ctrlOkD m) = true) :
    (l.map eD).all (ctrlOkM m) = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp_apply]
  exact fun x hx => ctrlOkM_eD (List.all_eq_true.1 h x hx)

/-- Store-free covered instructions are covered, below a size bound. -/
theorem ctrlOkD_of_ctrlOkM_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOkM m i = true → ctrlOkD m i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi h
    have hb : ∀ b : List V2.Instr, sizeOf b < n → b.all (ctrlOkM m) = true →
        b.all (ctrlOkD m) = true :=
      fun b hs hb => List.all_eq_true.2 fun x hx =>
        ih x (by have := List.sizeOf_lt_of_mem hx; omega) (List.all_eq_true.1 hb x hx)
    cases i with
    | block bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | loop bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | if_ bt l r =>
      have hlr : l.all (ctrlOkM m) = true ∧ r.all (ctrlOkM m) = true := by simpa using h
      simp only [ctrlOkD_if, Bool.and_eq_true]
      exact ⟨hb l (by simp at hi; omega) hlr.1, hb r (by simp at hi; omega) hlr.2⟩
    | _ => simp [ctrlOkD, h]

/-- **Store-free covered instructions are covered.** -/
theorem ctrlOkD_of_ctrlOkM {m : ModuleInst} {i : V2.Instr} (h : ctrlOkM m i = true) :
    ctrlOkD m i = true :=
  ctrlOkD_of_ctrlOkM_lt m _ i (Nat.lt_succ_self _) h

theorem all_ctrlOkD_of_ctrlOkM {m : ModuleInst} {l : List V2.Instr}
    (h : l.all (ctrlOkM m) = true) : l.all (ctrlOkD m) = true :=
  List.all_eq_true.2 fun x hx => ctrlOkD_of_ctrlOkM (List.all_eq_true.1 h x hx)

/-- A store is covered. -/
theorem ctrlOkD_of_storeOkI {m : ModuleInst} {i : V2.Instr} (h : storeOkI i = true) :
    ctrlOkD m i = true := by
  cases i <;> simp_all [ctrlOkD, storeOkI]

mutual
/-- **Store-free covered code is not erased.** -/
theorem eDA_of_okA_false : ∀ (m : ModuleInst) (a : Admin), okA false m a = true → eDA a = a
  | m, .plain i, h => by rw [eDA_plain, eD_of_ctrlOkM (m := m) (by simpa using h)]
  | m, .label n cont body, h => by
    have hb : cont.all (ctrlOkM m) = true ∧ body.all (okA false m) = true := by simpa using h
    rw [eDA_label, map_eD_of_ctrlOkM hb.1, ← eDAL_eq, eDAL_of_okA_false m body hb.2]
  | _, .frame n fi body, h => by
    rw [eDA_frame, ← eDAL_eq, eDAL_of_okA_false fi.module body (by simpa using h)]
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `eDA_of_okA_false` on a sequence. -/
theorem eDAL_of_okA_false : ∀ (m : ModuleInst) (l : List Admin), l.all (okA false m) = true →
    eDAL l = l
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show eDA a :: eDAL l = a :: l
    rw [eDA_of_okA_false m a h.1, eDAL_of_okA_false m l h.2]
end

theorem map_eDA_of_okA_false {m : ModuleInst} {l : List Admin} (h : l.all (okA false m) = true) :
    l.map eDA = l := by
  rw [← eDAL_eq]; exact eDAL_of_okA_false m l h

mutual
/-- **Erased covered code is store-free covered code.** -/
theorem okA_false_eDA : ∀ (m : ModuleInst) (a : Admin), okD m a = true → okA false m (eDA a) = true
  | m, .plain i, h => by simpa using ctrlOkM_eD (m := m) (i := i) (by simpa using h)
  | m, .label n cont body, h => by
    have hb : cont.all (ctrlOkD m) = true ∧ body.all (okD m) = true := by simpa using h
    rw [eDA_label, GoodMerge.okA_label, all_ctrlOkM_eD hb.1, ← eDAL_eq, ← GoodMerge.okAL_eq,
      okAL_false_eDAL m body (by simpa using hb.2)]
    rfl
  | _, .frame n fi body, h => by
    rw [eDA_frame, GoodMerge.okA_frame, ← eDAL_eq, ← GoodMerge.okAL_eq]
    exact okAL_false_eDAL fi.module body (by simpa using h)
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `okA_false_eDA` on a sequence. -/
theorem okAL_false_eDAL : ∀ (m : ModuleInst) (l : List Admin), okDL m l = true →
    GoodMerge.okAL false m (eDAL l) = true
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [okDL, Bool.and_eq_true] at h
    show (okA false m (eDA a) && GoodMerge.okAL false m (eDAL l)) = true
    rw [okA_false_eDA m a h.1, okAL_false_eDAL m l h.2]
    rfl
end

theorem all_okA_false_eDA {m : ModuleInst} {l : List Admin} (h : l.all (okD m) = true) :
    (l.map eDA).all (okA false m) = true := by
  rw [← eDAL_eq, ← GoodMerge.okAL_eq]; exact okAL_false_eDAL m l (by simpa using h)

mutual
/-- **`Good20M`'s covered code is covered here.** -/
theorem okD_of_okA : ∀ (m : ModuleInst) (a : Admin), okA true m a = true → okD m a = true
  | m, .plain i, h => by
    rcases Bool.or_eq_true_iff.1 (by simpa using h) with h | h
    · exact ctrlOkD_of_ctrlOkM h
    · exact ctrlOkD_of_storeOkI (by simpa using h)
  | m, .label n cont body, h => by
    have hb : cont.all (ctrlOkM m) = true ∧ body.all (okA true m) = true := by simpa using h
    rw [okD_label, all_ctrlOkD_of_ctrlOkM hb.1, ← okDL_eq, okDL_of_okA m body hb.2]
    rfl
  | _, .frame n fi body, h => by
    rw [okD_frame, ← okDL_eq]
    exact okDL_of_okA fi.module body (by simpa using h)
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `okD_of_okA` on a sequence. -/
theorem okDL_of_okA : ∀ (m : ModuleInst) (l : List Admin), l.all (okA true m) = true →
    okDL m l = true
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show (okD m a && okDL m l) = true
    rw [okD_of_okA m a h.1, okDL_of_okA m l h.2]
    rfl
end

theorem all_okD_of_okA {m : ModuleInst} {l : List Admin} (h : l.all (okA true m) = true) :
    l.all (okD m) = true := by
  rw [← okDL_eq]; exact okDL_of_okA m l h

/-- On a store, the deep and the shallow erasures agree. -/
theorem eD_eq_eraseI {m : ModuleInst} {i : V2.Instr} (h : (ctrlOkM m i || storeOkI i) = true) :
    eD i = eraseI i := by
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [eD_of_ctrlOkM h, GoodMerge.eraseI_of_ctrlOkM h]
  · cases i <;> simp_all [storeOkI, eD, eraseI]

mutual
/-- **On `Good20M`'s code the deep and the shallow erasures agree.** -/
theorem eDA_eq_eraseA : ∀ (m : ModuleInst) (a : Admin), okA true m a = true → eDA a = eraseA a
  | m, .plain i, h => by
    rw [eDA_plain, StoreGood.eraseA_plain, eD_eq_eraseI (m := m) (by simpa using h)]
  | m, .label n cont body, h => by
    have hb : cont.all (ctrlOkM m) = true ∧ body.all (okA true m) = true := by simpa using h
    rw [eDA_label, StoreGood.eraseA_label, map_eD_of_ctrlOkM hb.1, ← eDAL_eq,
      ← StoreGood.eraseL_eq, eDAL_eq_eraseL m body hb.2]
  | _, .frame n fi body, h => by
    rw [eDA_frame, StoreGood.eraseA_frame, ← eDAL_eq, ← StoreGood.eraseL_eq,
      eDAL_eq_eraseL fi.module body (by simpa using h)]
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `eDA_eq_eraseA` on a sequence. -/
theorem eDAL_eq_eraseL : ∀ (m : ModuleInst) (l : List Admin), l.all (okA true m) = true →
    eDAL l = StoreGood.eraseL l
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show eDA a :: eDAL l = eraseA a :: StoreGood.eraseL l
    rw [eDA_eq_eraseA m a h.1, eDAL_eq_eraseL m l h.2]
end

theorem map_eDA_eq_eraseA {m : ModuleInst} {l : List Admin} (h : l.all (okA true m) = true) :
    l.map eDA = l.map eraseA := by
  rw [← eDAL_eq, ← StoreGood.eraseL_eq]; exact eDAL_eq_eraseL m l h

@[simp] theorem map_eDA_vals (vs : List Val) : (vals vs).map eDA = vals vs :=
  map_eDA_of_okA_false (m := {}) (GoodMerge.all_okA_vals false {} vs)

@[simp] theorem map_eDA_expression (is : List V2.Instr) :
    (expression is).map eDA = expression (is.map eD) := by
  simp [expression, Function.comp_def]

/-! ## Blocks, loops and `if`s in `simEnv20T` -/

/-- **A block is a typed `admininstr` of `simEnv20T`** when its parts are typed there. -/
theorem typedT_block {bt : V2.BlockType} {b : List V2.Instr}
    (h₁ : TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt))
    (h₂ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.block bt b)) :=
  Pure.typedV_closedCase20 (findTyp_admininstr20T B) (by with_unfolding_all rfl)
    (Whole.hasTyp_tup2G h₁ h₂)

/-- **A loop is a typed `admininstr` of `simEnv20T`** when its parts are typed there. -/
theorem typedT_loop {bt : V2.BlockType} {b : List V2.Instr}
    (h₁ : TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt))
    (h₂ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.loop bt b)) :=
  Pure.typedV_closedCase20 (findTyp_admininstr20T B) (by with_unfolding_all rfl)
    (Whole.hasTyp_tup2G h₁ h₂)

/-- **An `if` is a typed `admininstr` of `simEnv20T`** when its parts are typed there. -/
theorem typedT_if {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (h₁ : TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt))
    (h₂ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₁)))
    (h₃ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₂))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.if_ bt b₁ b₂)) :=
  Pure.typedV_closedCase20 (findTyp_admininstr20T B) (by with_unfolding_all rfl)
    (Whole.hasTyp_tup3_mk20 h₁ h₂ h₃)

/-- A typed `admininstr` loop of `simEnv20` has a typed block type and body. -/
theorem typed_loop_inv {bt : V2.BlockType} {b : List V2.Instr} (h : TypedI B (.loop bt b)) :
    TypedV (E20 B) Pure.blocktypeT (blockTypeV bt) ∧ TypedV (E20 B) Pure.instrsT (.list (instrsToV b)) :=
  Whole.typed_loop_inv20 h

/-! ## Typing in `simEnv20T` from the deep erasure -/

/-- An `instr*` of `simEnv20`, after erasure, is an `instr*` of `simEnv20T` before, when each of
its instructions is. -/
theorem typedT_instrs_of {b : List V2.Instr}
    (ih : ∀ j ∈ b, TypedI B (eD j) → TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV j))
    (h : TypedV (E20 B) Pure.instrsT (.list (instrsToV (b.map eD)))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b)) := by
  rw [Whole.instrsToV_map20] at h ⊢
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hu
  have hj' : TypedV (E20 B) (.varT "instr" []) (instrToV (eD j)) :=
    Sim.typedV_list_iff.1 h _ (List.mem_map.2 ⟨eD j, List.mem_map_of_mem hj, rfl⟩)
  exact StoreGood.typedV_instr_of_admin20T j (ih j hj ((Whole.typedV_plain20_iff (eD j)).2 hj'))

/-- An instruction without nested code, from its erased typing. -/
theorem typedT_flat {m : ModuleInst} {i : V2.Instr} (hok : (ctrlOkM m i || storeOkI i) = true)
    (h : TypedI B (eD i)) : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i) := by
  by_cases hs : storeOkI i = true
  · exact StoreGood.typedV_storeOk20T hs
  · have hc : ctrlOkM m i = true := by simpa [hs] using hok
    have h' : TypedI B i := by rwa [eD_of_ctrlOkM hc] at h
    exact StoreAgree.typedV_to20T (by decide) h'

/-- The induction hypothesis on a body: its erased typing gives its typing in `simEnv20T`. -/
abbrev BodyT (B : Builtins) (b : List V2.Instr) : Prop :=
  TypedV (E20 B) Pure.instrsT (.list (instrsToV (b.map eD))) →
    TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b))

theorem typedT_block_of {bt : V2.BlockType} {b : List V2.Instr} (h : TypedI B (eD (.block bt b)))
    (hb : BodyT B b) : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.block bt b)) := by
  have hp := Whole.typed_block_inv20 (by simpa using h)
  exact typedT_block (StoreAgree.typedV_to20T (by decide) hp.1) (hb hp.2)

theorem typedT_loop_of {bt : V2.BlockType} {b : List V2.Instr} (h : TypedI B (eD (.loop bt b)))
    (hb : BodyT B b) : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.loop bt b)) := by
  have hp := Whole.typed_loop_inv20 (by simpa using h)
  exact typedT_loop (StoreAgree.typedV_to20T (by decide) hp.1) (hb hp.2)

theorem typedT_if_of {bt : V2.BlockType} {l r : List V2.Instr} (h : TypedI B (eD (.if_ bt l r)))
    (hl : BodyT B l) (hr : BodyT B r) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.if_ bt l r)) := by
  have hp := Whole.typed_if20 (by simpa using h)
  exact typedT_if (StoreAgree.typedV_to20T (by decide) hp.1) (hl hp.2.1) (hr hp.2.2)

/-- **An instruction whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`**, below a
size bound. -/
theorem typedT_of_eDI_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOkD m i = true → TypedI B (eD i) →
      TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi hok h
    have hb : ∀ b : List V2.Instr, sizeOf b < n → b.all (ctrlOkD m) = true → BodyT B b :=
      fun b hs hb => typedT_instrs_of fun j hj =>
        ih j (by have := List.sizeOf_lt_of_mem hj; omega) (List.all_eq_true.1 hb j hj)
    cases i with
    | block bt b => exact typedT_block_of h (hb b (by simp at hi; omega) (by simpa using hok))
    | loop bt b => exact typedT_loop_of h (hb b (by simp at hi; omega) (by simpa using hok))
    | if_ bt l r =>
      have hlr : l.all (ctrlOkD m) = true ∧ r.all (ctrlOkD m) = true := by simpa using hok
      exact typedT_if_of h (hb l (by simp at hi; omega) hlr.1) (hb r (by simp at hi; omega) hlr.2)
    | _ => exact typedT_flat (by simpa [ctrlOkD] using hok) h

/-- **An instruction whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`.** -/
theorem typedT_of_eDI {m : ModuleInst} {i : V2.Instr} (hok : ctrlOkD m i = true)
    (h : TypedI B (eD i)) : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i) :=
  typedT_of_eDI_lt m _ i (Nat.lt_succ_self _) hok h

/-- **An `instr*` whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`.** -/
theorem typedT_instrs_of_eD {m : ModuleInst} {b : List V2.Instr} (hok : b.all (ctrlOkD m) = true)
    (h : TypedV (E20 B) Pure.instrsT (.list (instrsToV (b.map eD)))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b)) :=
  typedT_instrs_of (fun j hj => typedT_of_eDI (List.all_eq_true.1 hok j hj)) h

/-- A label, from its erased typing and the typing of its body. -/
theorem typedT_labelD {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (hc : cont.all (ctrlOkD m) = true)
    (h : TypedV (E20 B) (.varT "admininstr" []) (adminToV (eDA (.label n cont body))))
    (ih : TypedV (E20 B) adminsTy (.list (adminsToV (eDAL body))) →
      TypedV (simEnv20T B) adminsTy (.list (adminsToV body))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.label n cont body)) := by
  have h' : TypedV (E20 B) (.varT "admininstr" [])
      (adminToV (.label n (cont.map eD) (eDAL body))) := by
    rwa [eDA_label, ← eDAL_eq] at h
  obtain ⟨h₁, h₂, h₃⟩ := Whole.typedV_adminLabel20_iff.1 h'
  exact StoreGood.typedV_adminLabel20T_mk (StoreAgree.typedV_to20T (by decide) h₁)
    (typedT_instrs_of_eD hc h₂) (ih h₃)

/-- A frame, from its erased typing and the typing of its body. -/
theorem typedT_frameD {n : Nat} {fi : Frame} {body : List Admin}
    (h : TypedV (E20 B) (.varT "admininstr" []) (adminToV (eDA (.frame n fi body))))
    (ih : TypedV (E20 B) adminsTy (.list (adminsToV (eDAL body))) →
      TypedV (simEnv20T B) adminsTy (.list (adminsToV body))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.frame n fi body)) := by
  have h' : TypedV (E20 B) (.varT "admininstr" []) (adminToV (.frame n fi (eDAL body))) := by
    rwa [eDA_frame, ← eDAL_eq] at h
  obtain ⟨h₁, h₂, h₃⟩ := Whole.typedV_adminFrame20_iff.1 h'
  exact StoreGood.typedV_adminFrame20T_mk (StoreAgree.typedV_to20T (by decide) h₁)
    (StoreAgree.typedV_to20T (by decide) h₂) (ih h₃)

theorem okDL_of_label {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h : okD m (.label n cont body) = true) : cont.all (ctrlOkD m) = true ∧ okDL m body = true := by
  have hb : cont.all (ctrlOkD m) = true ∧ body.all (okD m) = true := by simpa using h
  exact ⟨hb.1, by simpa using hb.2⟩

mutual
/-- **Administrative code whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`.** -/
theorem typedT_of_eDAM : ∀ (m : ModuleInst) (a : Admin), okD m a = true →
    TypedV (E20 B) (.varT "admininstr" []) (adminToV (eDA a)) →
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV a)
  | m, .plain i, hok, h => typedT_of_eDI (m := m) hok h
  | m, .label n cont body, hok, h =>
    typedT_labelD (okDL_of_label hok).1 h fun h₃ =>
      typedT_of_eDLM m body (okDL_of_label hok).2 h₃
  | _, .frame n fi body, hok, h =>
    typedT_frameD h fun h₃ => typedT_of_eDLM fi.module body (by simpa using hok) h₃
  | _, .trap, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .callAddr _, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .refFuncAddr _, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .refHostAddr _, _, h => StoreAgree.typedV_to20T (by decide) h

/-- `typedT_of_eDAM` on a sequence. -/
theorem typedT_of_eDLM : ∀ (m : ModuleInst) (l : List Admin), okDL m l = true →
    TypedV (E20 B) adminsTy (.list (adminsToV (eDAL l))) →
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l))
  | _, [], _, _ => Sim.typedV_list_iff.2 (by simp [adminsToV])
  | m, a :: l, hok, h => by
    simp only [okDL, Bool.and_eq_true] at hok
    have h' : TypedV (E20 B) adminsTy (.list (adminToV (eDA a) :: adminsToV (eDAL l))) := h
    have hl := typedT_of_eDLM m l hok.2 (Sim.typedV_list_iff.2 fun u hu =>
      Sim.typedV_list_iff.1 h' u (List.mem_cons_of_mem _ hu))
    have ha := typedT_of_eDAM m a hok.1 (Sim.typedV_list_iff.1 h' _ List.mem_cons_self)
    refine Sim.typedV_list_iff.2 fun u hu => ?_
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ha
    · exact Sim.typedV_list_iff.1 hl u hu
end

/-- **Covered code whose deep erasure is typed in `simEnv20` is typed in `simEnv20T`.** -/
theorem typedT_of_eDL {m : ModuleInst} {l : List Admin} (hok : l.all (okD m) = true)
    (h : TypedV (E20 B) adminsTy (.list (adminsToV (l.map eDA)))) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l)) :=
  typedT_of_eDLM m l (by simpa using hok) (by simpa using h)

end Silmaril.Wasm.SpecTec.Sim20.StoreDeep
