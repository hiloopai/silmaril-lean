module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.GoodMergeLoad
public import Silmaril.Wasm.SpecTec.Sim20.StoreGood.Thms
public import Silmaril.Wasm.SpecTec.Sim20.CallIndGood.Thms

/-!
# One covered code for stores, `call_indirect`, the size and `table.get` reads and packed loads

An earlier step has two invariants: `StoreGood.Good20CS` admits administrative scalar stores,
and `CallIndGood.Good20CI` admits `call_indirect` (read in a module), `table.size`,
`memory.size` and `table.get`. Here one predicate admits all of them, and packed loads as well.

* `ctrlOkM m`: `CallIndGood.ctrlOkI m` with packed loads, recursively in block bodies.
* `okA b m`: administrative code; a plain administrative instruction may also be a scalar store
  (`StoreGood.storeOkI`) when `b` holds. A frame body is read in its own frame's module. `okA
  true` is the merged covered code; `okA false` is its store-free part, which `StoreGood.eraseA`
  leaves unchanged (`eraseA_of_okA_false`) and into which it maps covered code
  (`okA_false_eraseA`).
* `StoreOkM s`: every function is a Wasm function whose body is `ctrlOkM` in its own module.
* **`typedT_of_eraseM`**: covered code whose erasure is typed in `simEnv20` is typed in
  `simEnv20T`.
* **`cover20M`**: every V2 step from plain-tail covered code over a `StoreOkM` store is a step of
  `Nest20 (BaseM P)`: round 3's fragment widened by `CallIndGood.FwdStep20G` on store-free
  windows, the packed loads (`LoadPackFwd20`), the second pure fragment whose tail may hold a
  store, and the six store steps.
* **`okA_step`**: such a step keeps the code covered (with or without stores), the store's
  functions, whole pages and the frame's module.
* Inclusions: `ctrlOkM_of_ctrlOkI`, `okA_of_adminOkS`, `okA_of_adminOkI`, `storeOkM_of_storeOkI`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.GoodMerge

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk adminOk Nest20 FwdStep20D PureFwd20B PureFrag20
  PureFrag20B StoreTop20 StoreOk Tail20 WholePages)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (storeOkI eraseA eraseI adminOkS)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (ctrlOkI adminOkI StoreOkI FwdStep20G fwdF_of_D)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins}

/-! ## The predicates -/

mutual
/-- **Covered instructions**: `ctrlOkI m`, with packed loads, recursively in block bodies. -/
def ctrlOkM (m : ModuleInst) : V2.Instr → Bool
  | .block _ body | .loop _ body => ctrlOkML m body
  | .if_ _ l r => ctrlOkML m l && ctrlOkML m r
  | .intLoad _ _ _ => true
  | i => ctrlOkI m i

/-- `ctrlOkM` on a sequence. -/
def ctrlOkML (m : ModuleInst) : List V2.Instr → Bool
  | [] => true
  | i :: is => ctrlOkM m i && ctrlOkML m is
end

@[simp] theorem ctrlOkML_eq (m : ModuleInst) (l : List V2.Instr) :
    ctrlOkML m l = l.all (ctrlOkM m) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ctrlOkML, ih]

@[simp] theorem ctrlOkM_block (m : ModuleInst) (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOkM m (.block bt b) = b.all (ctrlOkM m) := by simp [ctrlOkM]

@[simp] theorem ctrlOkM_loop (m : ModuleInst) (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOkM m (.loop bt b) = b.all (ctrlOkM m) := by simp [ctrlOkM]

@[simp] theorem ctrlOkM_if (m : ModuleInst) (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) :
    ctrlOkM m (.if_ bt b₁ b₂) = (b₁.all (ctrlOkM m) && b₂.all (ctrlOkM m)) := by simp [ctrlOkM]

mutual
/-- **Covered administrative code**, in the module `m`; scalar stores are admitted at the
administrative level when `b` holds. -/
def okA (b : Bool) (m : ModuleInst) : Admin → Bool
  | .plain i => ctrlOkM m i || (b && storeOkI i)
  | .label _ cont body => ctrlOkML m cont && okAL b m body
  | .frame _ fi body => okAL b fi.module body
  | .trap | .callAddr _ | .refFuncAddr _ | .refHostAddr _ => true

/-- `okA` on a sequence. -/
def okAL (b : Bool) (m : ModuleInst) : List Admin → Bool
  | [] => true
  | a :: rest => okA b m a && okAL b m rest
end

@[simp] theorem okAL_eq (b : Bool) (m : ModuleInst) (l : List Admin) :
    okAL b m l = l.all (okA b m) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [okAL, ih]

@[simp] theorem okA_plain (b : Bool) (m : ModuleInst) (i : V2.Instr) :
    okA b m (.plain i) = (ctrlOkM m i || (b && storeOkI i)) := rfl

@[simp] theorem okA_label (b : Bool) (m : ModuleInst) (n : Nat) (cont : List V2.Instr)
    (body : List Admin) :
    okA b m (.label n cont body) = (cont.all (ctrlOkM m) && body.all (okA b m)) := by
  simp [okA]

@[simp] theorem okA_frame (b : Bool) (m : ModuleInst) (n : Nat) (fi : Frame) (body : List Admin) :
    okA b m (.frame n fi body) = body.all (okA b fi.module) := by simp [okA]

@[simp] theorem okA_trap (b : Bool) (m : ModuleInst) : okA b m .trap = true := rfl
@[simp] theorem okA_callAddr (b : Bool) (m : ModuleInst) (a : FuncAddr) :
    okA b m (.callAddr a) = true := rfl
@[simp] theorem okA_refFuncAddr (b : Bool) (m : ModuleInst) (a : FuncAddr) :
    okA b m (.refFuncAddr a) = true := rfl
@[simp] theorem okA_refHostAddr (b : Bool) (m : ModuleInst) (a : HostAddr) :
    okA b m (.refHostAddr a) = true := rfl

@[simp] theorem okA_toAdmin (b : Bool) (m : ModuleInst) (v : Val) : okA b m v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> simp [Val.toAdmin, ctrlOkM, ctrlOkI, ctrlOk]

@[simp] theorem all_okA_vals (b : Bool) (m : ModuleInst) (vs : List Val) :
    (vals vs).all (okA b m) = true := by
  simp [vals]

@[simp] theorem all_okA_expression (b : Bool) (m : ModuleInst) (is : List V2.Instr) :
    (expression is).all (okA b m) = is.all (fun i => ctrlOkM m i || (b && storeOkI i)) := by
  simp [expression, Function.comp_def]

/-- **Every function of the store is a Wasm function whose body is covered in its module.** -/
def StoreOkM (s : Store H) : Prop :=
  ∀ a fi, s.funcInst? a = some fi → ∃ fn, fi.code = .wasm fn ∧ fn.body.all (ctrlOkM fi.module) = true

theorem storeOkM_of_funcs {s s' : Store H} (h : StoreOkM s) (e : s'.funcs = s.funcs) :
    StoreOkM s' := by
  intro a fi hf
  exact h a fi (by simpa [Store.funcInst?, e] using hf)

theorem StoreOkM.not_host {s : Store H} (hs : StoreOkM s) {a : FuncAddr} {fi : FuncInst H} {h : H}
    (hf : s.funcInst? a = some fi) (hcode : fi.code = .host h) : False := by
  obtain ⟨fn, hc, -⟩ := hs a fi hf
  rw [hcode] at hc
  cases hc

/-! ## Inclusions -/

/-- `ctrlOkI` gives `ctrlOkM`, below a size bound. -/
theorem ctrlOkM_of_ctrlOkI_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOkI m i = true → ctrlOkM m i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi h
    have hb : ∀ b : List V2.Instr, sizeOf b < n → b.all (ctrlOkI m) = true →
        b.all (ctrlOkM m) = true :=
      fun b hs hb => List.all_eq_true.2 fun x hx =>
        ih x (by have := List.sizeOf_lt_of_mem hx; omega) (List.all_eq_true.1 hb x hx)
    cases i with
    | block bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | loop bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | if_ bt l r =>
      have hlr : l.all (ctrlOkI m) = true ∧ r.all (ctrlOkI m) = true := by simpa using h
      simp only [ctrlOkM_if, Bool.and_eq_true]
      exact ⟨hb l (by simp at hi; omega) hlr.1, hb r (by simp at hi; omega) hlr.2⟩
    | _ => revert h; simp [ctrlOkM]

/-- **`ctrlOkI` gives `ctrlOkM`.** -/
theorem ctrlOkM_of_ctrlOkI (m : ModuleInst) (i : V2.Instr) (h : ctrlOkI m i = true) :
    ctrlOkM m i = true :=
  ctrlOkM_of_ctrlOkI_lt m _ i (Nat.lt_succ_self _) h

theorem all_ctrlOkM_of_ctrlOkI (m : ModuleInst) {l : List V2.Instr}
    (h : l.all (ctrlOkI m) = true) : l.all (ctrlOkM m) = true :=
  List.all_eq_true.2 fun x hx => ctrlOkM_of_ctrlOkI m x (List.all_eq_true.1 h x hx)

theorem all_ctrlOkM_of_ctrlOk (m : ModuleInst) {l : List V2.Instr} (h : l.all ctrlOk = true) :
    l.all (ctrlOkM m) = true :=
  List.all_eq_true.2 fun x hx =>
    ctrlOkM_of_ctrlOkI m x (CallIndGood.ctrlOkI_of_ctrlOk m x (List.all_eq_true.1 h x hx))

mutual
/-- **`adminOkI` code is covered**, without stores. -/
theorem okA_of_adminOkI (b : Bool) : ∀ (m : ModuleInst) (a : Admin), adminOkI m a = true →
    okA b m a = true
  | m, .plain i, h => by simp [ctrlOkM_of_ctrlOkI m i h]
  | m, .label _ cont body, h => by
    have hb : cont.all (ctrlOkI m) = true ∧ body.all (adminOkI m) = true := by simpa using h
    rw [okA_label, all_ctrlOkM_of_ctrlOkI m hb.1, ← okAL_eq, okAL_of_adminOkI b m body hb.2]
    rfl
  | _, .frame _ fi body, h => by
    rw [okA_frame, ← okAL_eq]
    exact okAL_of_adminOkI b fi.module body (by simpa using h)
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `okA_of_adminOkI` on a sequence. -/
theorem okAL_of_adminOkI (b : Bool) : ∀ (m : ModuleInst) (l : List Admin),
    l.all (adminOkI m) = true → okAL b m l = true
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show (okA b m a && okAL b m l) = true
    rw [okA_of_adminOkI b m a h.1, okAL_of_adminOkI b m l h.2]
    rfl
end

theorem all_okA_of_adminOkI (b : Bool) {m : ModuleInst} {l : List Admin}
    (h : l.all (adminOkI m) = true) : l.all (okA b m) = true := by
  rw [← okAL_eq]; exact okAL_of_adminOkI b m l h

mutual
/-- **Covered code with stores is covered here**, in every module. -/
theorem okA_of_adminOkS : ∀ (m : ModuleInst) (a : Admin), adminOkS a = true → okA true m a = true
  | m, .plain i, h => by
    rcases Bool.or_eq_true_iff.1 (by simpa using h) with h | h
    · simp [ctrlOkM_of_ctrlOkI m i (CallIndGood.ctrlOkI_of_ctrlOk m i h)]
    · simp [h]
  | m, .label _ cont body, h => by
    have hb : cont.all ctrlOk = true ∧ body.all adminOkS = true := by simpa using h
    rw [okA_label, all_ctrlOkM_of_ctrlOk m hb.1, ← okAL_eq, okAL_of_adminOkS m body hb.2]
    rfl
  | _, .frame _ fi body, h => by
    rw [okA_frame, ← okAL_eq]
    exact okAL_of_adminOkS fi.module body (by simpa using h)
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `okA_of_adminOkS` on a sequence. -/
theorem okAL_of_adminOkS : ∀ (m : ModuleInst) (l : List Admin), l.all adminOkS = true →
    okAL true m l = true
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show (okA true m a && okAL true m l) = true
    rw [okA_of_adminOkS m a h.1, okAL_of_adminOkS m l h.2]
    rfl
end

theorem all_okA_of_adminOkS (m : ModuleInst) {l : List Admin} (h : l.all adminOkS = true) :
    l.all (okA true m) = true := by
  rw [← okAL_eq]; exact okAL_of_adminOkS m l h

mutual
/-- Store-free covered code is covered. -/
theorem okA_true_of_false : ∀ (m : ModuleInst) (a : Admin), okA false m a = true →
    okA true m a = true
  | m, .plain i, h => by simp_all
  | m, .label _ cont body, h => by
    have hb : cont.all (ctrlOkM m) = true ∧ body.all (okA false m) = true := by simpa using h
    rw [okA_label, hb.1, ← okAL_eq, okAL_true_of_false m body hb.2]
    rfl
  | _, .frame _ fi body, h => by
    rw [okA_frame, ← okAL_eq]
    exact okAL_true_of_false fi.module body (by simpa using h)
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `okA_true_of_false` on a sequence. -/
theorem okAL_true_of_false : ∀ (m : ModuleInst) (l : List Admin), l.all (okA false m) = true →
    okAL true m l = true
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show (okA true m a && okAL true m l) = true
    rw [okA_true_of_false m a h.1, okAL_true_of_false m l h.2]
    rfl
end

theorem all_okA_true_of_false {m : ModuleInst} {l : List Admin} (h : l.all (okA false m) = true) :
    l.all (okA true m) = true := by
  rw [← okAL_eq]; exact okAL_true_of_false m l h

theorem storeOkM_of_storeOkI {s : Store H} (h : StoreOkI s) : StoreOkM s := by
  intro a fi hf
  obtain ⟨fn, hc, hb⟩ := h a fi hf
  exact ⟨fn, hc, all_ctrlOkM_of_ctrlOkI _ hb⟩

theorem storeOkM_of_storeOk {s : Store H} (h : StoreOk s) : StoreOkM s :=
  storeOkM_of_storeOkI (CallIndGood.storeOkI_of_storeOk h)

/-! ## Erasure -/

/-- A covered instruction is not erased. -/
theorem eraseI_of_ctrlOkM {m : ModuleInst} {i : V2.Instr} (h : ctrlOkM m i = true) :
    eraseI i = i := by
  cases i <;> first | rfl | simp [ctrlOkM, ctrlOkI, ctrlOk] at h

mutual
/-- **Store-free covered code is not erased.** -/
theorem eraseA_of_okA_false : ∀ (m : ModuleInst) (a : Admin), okA false m a = true → eraseA a = a
  | m, .plain i, h => by
    rw [StoreGood.eraseA_plain, eraseI_of_ctrlOkM (m := m) (by simpa using h)]
  | m, .label n cont body, h => by
    have hb : body.all (okA false m) = true := by simp_all
    rw [StoreGood.eraseA_label, ← StoreGood.eraseL_eq, eraseL_of_okA_false m body hb]
  | _, .frame n fi body, h => by
    rw [StoreGood.eraseA_frame, ← StoreGood.eraseL_eq,
      eraseL_of_okA_false fi.module body (by simpa using h)]
  | _, .trap, _ => rfl
  | _, .callAddr _, _ => rfl
  | _, .refFuncAddr _, _ => rfl
  | _, .refHostAddr _, _ => rfl

/-- `eraseA_of_okA_false` on a sequence. -/
theorem eraseL_of_okA_false : ∀ (m : ModuleInst) (l : List Admin), l.all (okA false m) = true →
    StoreGood.eraseL l = l
  | _, [], _ => rfl
  | m, a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show eraseA a :: StoreGood.eraseL l = a :: l
    rw [eraseA_of_okA_false m a h.1, eraseL_of_okA_false m l h.2]
end

theorem map_eraseA_of_okA_false {m : ModuleInst} {l : List Admin}
    (h : l.all (okA false m) = true) : l.map eraseA = l := by
  rw [← StoreGood.eraseL_eq]; exact eraseL_of_okA_false m l h

/-! ## Typing in `simEnv20T` from the erased typing -/

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

theorem okAL_of_label {b : Bool} {m : ModuleInst} {n : Nat} {cont : List V2.Instr}
    {body : List Admin} (h : okA b m (.label n cont body) = true) : okAL b m body = true := by
  have hb : cont.all (ctrlOkM m) = true ∧ body.all (okA b m) = true := by simpa using h
  simpa using hb.2

/-- A label, from its erased typing and the typing of its body. -/
theorem typedT_label_of {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h : TypedV (E20 B) (.varT "admininstr" []) (adminToV (eraseA (.label n cont body))))
    (ih : TypedV (E20 B) adminsTy (.list (adminsToV (StoreGood.eraseL body))) →
      TypedV (simEnv20T B) adminsTy (.list (adminsToV body))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.label n cont body)) := by
  have h' : TypedV (E20 B) (.varT "admininstr" [])
      (adminToV (.label n cont (StoreGood.eraseL body))) := by
    rwa [StoreGood.eraseA_label, ← StoreGood.eraseL_eq] at h
  obtain ⟨h₁, h₂, h₃⟩ := Whole.typedV_adminLabel20_iff.1 h'
  exact StoreGood.typedV_adminLabel20T_mk (StoreAgree.typedV_to20T (by decide) h₁)
    (StoreAgree.typedV_list_to20T (by decide) h₂) (ih h₃)

/-- A frame, from its erased typing and the typing of its body. -/
theorem typedT_frame_of {n : Nat} {fi : Frame} {body : List Admin}
    (h : TypedV (E20 B) (.varT "admininstr" []) (adminToV (eraseA (.frame n fi body))))
    (ih : TypedV (E20 B) adminsTy (.list (adminsToV (StoreGood.eraseL body))) →
      TypedV (simEnv20T B) adminsTy (.list (adminsToV body))) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.frame n fi body)) := by
  have h' : TypedV (E20 B) (.varT "admininstr" [])
      (adminToV (.frame n fi (StoreGood.eraseL body))) := by
    rwa [StoreGood.eraseA_frame, ← StoreGood.eraseL_eq] at h
  obtain ⟨h₁, h₂, h₃⟩ := Whole.typedV_adminFrame20_iff.1 h'
  exact StoreGood.typedV_adminFrame20T_mk (StoreAgree.typedV_to20T (by decide) h₁)
    (StoreAgree.typedV_to20T (by decide) h₂) (ih h₃)

mutual
/-- **An erased covered instruction typed in `simEnv20` is typed in `simEnv20T`** before
erasure. -/
theorem typedT_of_eraseAM : ∀ (m : ModuleInst) (a : Admin), okA true m a = true →
    TypedV (E20 B) (.varT "admininstr" []) (adminToV (eraseA a)) →
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV a)
  | m, .plain i, hok, h => by
    by_cases hs : storeOkI i = true
    · exact StoreGood.typedV_storeOk20T hs
    · show TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.plain i))
      have hc : ctrlOkM m i = true := by simpa [hs] using hok
      have h' : TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain i)) := by
        rwa [StoreGood.eraseA_plain, eraseI_of_ctrlOkM hc] at h
      exact StoreAgree.typedV_to20T (by decide) h'
  | m, .label n cont body, hok, h =>
    typedT_label_of h fun h₃ => typedT_of_eraseLM m body (okAL_of_label hok) h₃
  | _, .frame n fi body, hok, h =>
    typedT_frame_of h fun h₃ => typedT_of_eraseLM fi.module body (by simpa using hok) h₃
  | _, .trap, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .callAddr _, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .refFuncAddr _, _, h => StoreAgree.typedV_to20T (by decide) h
  | _, .refHostAddr _, _, h => StoreAgree.typedV_to20T (by decide) h

/-- `typedT_of_eraseAM` on a sequence. -/
theorem typedT_of_eraseLM : ∀ (m : ModuleInst) (l : List Admin), okAL true m l = true →
    TypedV (E20 B) adminsTy (.list (adminsToV (StoreGood.eraseL l))) →
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l))
  | _, [], _, _ => Sim.typedV_list_iff.2 (by simp [adminsToV])
  | m, a :: l, hok, h => by
    simp only [okAL, Bool.and_eq_true] at hok
    have h' : TypedV (E20 B) adminsTy
        (.list (adminToV (eraseA a) :: adminsToV (StoreGood.eraseL l))) := h
    have hl := typedT_of_eraseLM m l hok.2 (Sim.typedV_list_iff.2 fun u hu =>
      Sim.typedV_list_iff.1 h' u (List.mem_cons_of_mem _ hu))
    have ha := typedT_of_eraseAM m a hok.1 (Sim.typedV_list_iff.1 h' _ List.mem_cons_self)
    refine Sim.typedV_list_iff.2 fun u hu => ?_
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ha
    · exact Sim.typedV_list_iff.1 hl u hu
end

/-- `typedT_of_eraseLM`, with the `List.all` form of the hypothesis. -/
theorem typedT_of_eraseM {m : ModuleInst} {l : List Admin} (hok : l.all (okA true m) = true)
    (h : TypedV (E20 B) adminsTy (.list (adminsToV (l.map eraseA)))) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV l)) :=
  typedT_of_eraseLM m l (by simpa using hok) (by simpa using h)

/-! ## The base -/

/-- **The base steps of the merged fragment.** -/
inductive BaseM (P : Profile) : Config H → Config H → Prop where
  | old {c c' : Config H} (h : FwdStep20G P c c') (hok : c.code.all (okA false c.frame.module) = true) :
      BaseM P c c'
  | pack {c c' : Config H} (h : LoadPackFwd20 c c') : BaseM P c c'
  | pureB {c c' : Config H} (h : PureFwd20B P c c') : BaseM P c c'
  | store {c c' : Config H} (h : StoreTop20 c c') : BaseM P c c'

/-- Every base step is a V2 step. -/
theorem BaseM.step {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseM P c c') :
    Step P host c c' := by
  cases h with
  | old h _ => exact h.step
  | pack h => exact h.step
  | pureB h =>
    cases h with
    | mk h => exact .pure h.pureStep
  | store h => exact h.step

/-! ## Store-free windows -/

/-- The windows 's first pure fragment are store-free. -/
theorem okA_false_of_pureFrag20 {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20 P is is') (hok : is.all (okA true m) = true) :
    is.all (okA false m) = true := by
  cases h <;> simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

/-- The windows of the read steps are store-free. -/
theorem okA_false_of_readStep {s : Store H} {f : Frame} {m : ModuleInst} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all (okA true m) = true) :
    is.all (okA false m) = true := by
  cases h <;> simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI, List.all_append]

/-- `PureRest20N` has an instruction that is neither covered nor a store. -/
theorem not_pureRest20N_okA {m : ModuleInst} {is : List Admin} (h : Whole.PureRest20N is)
    (hok : is.all (okA true m) = true) : False := by
  cases h with
  | @vec is i hm hv =>
    have hi : okA true m (.plain i) = true := List.all_eq_true.1 hok _ hm
    have hs : storeOkI i = false := by
      cases i <;> simp_all [storeOkI, vecOp20]
    have hc : ctrlOkM m i = false := by
      cases i <;> simp_all [vecOp20, ctrlOkM, ctrlOkI, ctrlOk]
    simp [hs, hc] at hi
  | unOpInvalid h => simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI]
  | cvtUndefined h => simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

/-! ## The cover lemma -/

/-- The pure steps. -/
theorem cover20M_pure {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hp : PureStep P is is') (ht : Tail20 s f is) (hok : is.all (okA true f.module) = true) :
    BaseM P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rcases Whole.pureStep_cover_tail hp ht with h | h | h
  · exact .old (fwdF_of_D (Whole.fwdC_pure h)) (okA_false_of_pureFrag20 h hok)
  · exact .pureB (.mk h)
  · exact (not_pureRest20N_okA h hok).elim

/-- A packed load that reads a value is a base step. -/
theorem baseM_loadPackVal {P : Profile} {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {ao : V2.MemArg} {i : BitVec 32} {mi : MemInst} {c : BitVec sz.width}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hb : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat ao) (sz.width / 8) =
      some (ibytes sz.width c)) :
    BaseM P ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩
      ⟨s, f, [.plain (.intConst t (match sx with
        | .signed => c.signExtend t.width
        | .unsigned => c.setWidth t.width))]⟩ := by
  cases sx <;> exact .pack (.val hm hb)

/-- `call_indirect` traps where the frame's module defines the type index. -/
theorem fwdG_callIndirectTrap {P : Profile} {s : Store H} {f : Frame} {x : TableIdx}
    {y : TypeIdx} {i : BitVec 32} {ti : TableInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
      s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type)
    (hy : ctrlOkM f.module (.callIndirect x y) = true) :
    FwdStep20G P ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩ ⟨s, f, [.trap]⟩ := by
  have hy' : (f.module.type? y).isSome = true := by simpa [ctrlOkM, ctrlOkI] using hy
  obtain ⟨ft, hft⟩ : ∃ ft, f.module.type? y = some ft := Option.isSome_iff_exists.1 hy'
  exact .fwd (.callIndTrap (.mk ht (ft := ft) hft h))

/-- `global.get`, from V2's premise. -/
theorem fwdG_globalGet {P : Profile} {s : Store H} {f : Frame} {x : GlobalIdx} {gi : GlobalInst}
    (h : (⟨s, f⟩ : State H).global? x = some gi) :
    FwdStep20G P ⟨s, f, [.plain (.globalGet x)]⟩ ⟨s, f, [gi.value.toAdmin]⟩ := by
  obtain ⟨a, hga, hg⟩ := Whole.global?_some h
  exact fwdF_of_D (Whole.fwdC_read (.globalGet hga hg))

/-- **The read steps from covered code**: round 3's widened fragment on a store-free window, or a
packed load. -/
theorem cover20M_read {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') (hok : is.all (okA true f.module) = true) :
    BaseM P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have ha : is.all (okA false f.module) = true := okA_false_of_readStep hr hok
  cases hr with
  | block hbt hk => exact .old (fwdF_of_D (.fwd (.fwd (.block (.block hbt hk))))) ha
  | loop hbt hk => exact .old (fwdF_of_D (.fwd (.fwd (.block (.loop hbt hk))))) ha
  | call hx =>
    exact .old (fwdF_of_D (Whole.fwdC_call (.call (by simpa [ModuleInst.funcAddr?] using hx)))) ha
  | callAddr hf hcode hk => exact .old (fwdF_of_D (.fwd (.callAddr (.mk hf hcode hk)))) ha
  | loadIntTrap hm h => exact .old (fwdF_of_D (.load (.intTrap hm h))) ha
  | loadIntVal hm hb => exact .old (fwdF_of_D (.load (.intVal hm hb))) ha
  | loadFloatTrap hm h => exact .old (fwdF_of_D (.load (.floatTrap hm h))) ha
  | loadFloatVal hm hb => exact .old (fwdF_of_D (.load (.floatVal hm hb))) ha
  | loadPackTrap hm h => exact .pack (.trap hm h)
  | loadPackVal hm hb => exact baseM_loadPackVal hm hb
  | localGet h =>
    exact .old (fwdF_of_D (Whole.fwdC_read (.localGet (by simpa [State.local?, Frame.local?] using h))))
      ha
  | globalGet h => exact .old (fwdG_globalGet h) ha
  | refFunc hx =>
    exact .old (fwdF_of_D (Whole.fwdC_read (.refFunc (by simpa [ModuleInst.funcAddr?] using hx)))) ha
  | callIndirectCall ht hr hf hy => exact .old (.fwd (.fwd (.callInd (.mk ht hr hf hy)))) ha
  | tableSize ht hn => exact .old (.size (.table ht hn)) ha
  | memorySize hm hn => exact .old (.size (.memory hm hn)) ha
  | tableGetTrap ht h => exact .old (.tget (.trap ht h)) ha
  | tableGetVal ht hr => exact .old (.tget (.val ht hr)) ha
  | callIndirectTrap ht h => exact .old (fwdG_callIndirectTrap ht h (by
      simpa [storeOkI] using List.all_eq_true.1 hok (.plain (.callIndirect _ _)) (by simp))) ha
  | _ => simp [ctrlOkM, ctrlOkI, ctrlOk, storeOkI] at hok

theorem okA_ctx_inner {b : Bool} {m : ModuleInst} {vs : List Val} {is rest : List Admin}
    (h : (vals vs ++ is ++ rest).all (okA b m) = true) : is.all (okA b m) = true := by
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.1.2

theorem bodyOk_labelM {b : Bool} {m : ModuleInst} {n : Nat} {cont : List V2.Instr}
    {body : List Admin} (h : [Admin.label n cont body].all (okA b m) = true) :
    body.all (okA b m) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, okA_label, Bool.and_eq_true] at h
  exact h.2

theorem bodyOk_frameM {b : Bool} {m : ModuleInst} {n : Nat} {fr : Frame} {body : List Admin}
    (h : [Admin.frame n fr body].all (okA b m) = true) : body.all (okA b fr.module) = true := by
  simpa using h

/-- **Every V2 step from plain-tail covered code over a `StoreOkM` store is in the nested merged
fragment.** -/
theorem cover20M {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (ht : Tail20 c.store c.frame c.code) (hok : c.code.all (okA true c.frame.module) = true)
    (hs : StoreOkM c.store) : Nest20 (BaseM P) c c' := by
  induction h with
  | pure hp => exact .base (cover20M_pure hp ht hok)
  | read hr => exact .base (cover20M_read hr hok)
  | ctxtInstrs hstep hne ih =>
    exact .ctx (ih (Whole.tail20_ctx hstep.not_allVals ht) (okA_ctx_inner hok) hs) hne
  | ctxtLabel _ ih => exact .label (ih (Whole.tail20_label ht).tail (bodyOk_labelM hok) hs)
  | ctxtFrame _ ih => exact .frame (ih (Whole.tail20_frame ht).tail (bodyOk_frameM hok) hs)
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet hx =>
    exact .base (.old (fwdF_of_D (Whole.fwdC_top (.var (.localSet hx))))
      (by simp [ctrlOkM, ctrlOkI, ctrlOk]))
  | globalSet ha hg =>
    exact .base (.old (fwdF_of_D (Whole.fwdC_top (.var (.globalSet ha hg))))
      (by simp [ctrlOkM, ctrlOkI, ctrlOk]))
  | storeIntTrap ha hm h => exact .base (.store (.intTrap ha hm h))
  | storeIntVal ha hm hw => exact .base (.store (.intVal ha hm hw))
  | storeFloatTrap ha hm h => exact .base (.store (.floatTrap ha hm h))
  | storeFloatVal ha hm hw => exact .base (.store (.floatVal ha hm hw))
  | storePackTrap ha hm h => exact .base (.store (.packTrap ha hm h))
  | storePackVal ha hm hw => exact .base (.store (.packVal ha hm hw))
  | _ => exact absurd hok (by simp [ctrlOkM, ctrlOkI, ctrlOk, storeOkI])

/-! ## What a step keeps -/

/-- What a step from covered code keeps. -/
def KeepsM (b : Bool) (c c' : Config H) : Prop :=
  c'.code.all (okA b c'.frame.module) = true ∧ c'.store.funcs = c.store.funcs ∧
    (WholePages c.store → WholePages c'.store) ∧ c'.frame.module = c.frame.module

theorem keepsM_same {b : Bool} {s : Store H} {f f' : Frame} {is is' : List Admin}
    (h : is'.all (okA b f'.module) = true) (hm : f'.module = f.module) :
    KeepsM b ⟨s, f, is⟩ ⟨s, f', is'⟩ := ⟨h, rfl, id, hm⟩

/-- **Every pure step keeps covered code covered** in the same module. -/
theorem okA_pureStep {P : Profile} {b : Bool} {m : ModuleInst} {is is' : List Admin}
    (h : PureStep P is is') (hok : is.all (okA b m) = true) : is'.all (okA b m) = true := by
  cases h <;> simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI, List.all_append]

/-- **Every read step keeps covered code covered**, over a covered store. -/
theorem okA_readStep {b : Bool} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all (okA b f.module) = true) (hs : StoreOkM s) :
    is'.all (okA b f.module) = true := by
  cases h with
  | @callAddr a vs fi fn hf hcode hk =>
    obtain ⟨fn', hc', hb⟩ := hs a fi hf
    rw [hcode] at hc'
    cases hc'
    simp
    exact fun x hx => Or.inl (List.all_eq_true.1 hb x hx)
  | _ => simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI, List.all_append]

/-- The six store steps keep the functions and whole pages, and end in `trap` or nothing. -/
theorem keepsM_storeTop {b : Bool} {c c' : Config H} (h : StoreTop20 c c') : KeepsM b c c' := by
  cases h with
  | intTrap _ _ _ | floatTrap _ _ _ | packTrap _ _ _ => exact keepsM_same rfl rfl
  | intVal _ hm hw | floatVal _ hm hw | packVal _ hm hw =>
    exact ⟨rfl, rfl, fun hp => StoreGood.WholePages.setMemInst hp hm
      (StoreGood.writeBytes?_size hw), rfl⟩

/-- **Every V2 step from covered code over a covered store keeps the code covered (with stores
when `b` holds, store-free otherwise), the store's functions, whole pages and the frame's
module.** -/
theorem okA_step {P : Profile} {host : HostSemantics H} {b : Bool} {c c' : Config H}
    (h : Step P host c c') (hok : c.code.all (okA b c.frame.module) = true)
    (hs : StoreOkM c.store) : KeepsM b c c' := by
  induction h with
  | pure hp => exact keepsM_same (okA_pureStep hp hok) rfl
  | read hr => exact keepsM_same (okA_readStep hr hok hs) rfl
  | ctxtInstrs _ _ ih =>
    simp only [List.all_append, Bool.and_eq_true] at hok
    obtain ⟨hi, hm, hw, hmod⟩ := ih hok.1.2 hs
    have hi' : _ = true := hmod ▸ hi
    refine ⟨?_, hm, hw, hmod⟩
    rw [hmod]
    simp [List.all_append, hi', hok.2]
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    have hb : cont.all (ctrlOkM f.module) = true ∧ is.all (okA b f.module) = true := by
      simpa using hok
    obtain ⟨hi, hm, hw, hmod⟩ := ih hb.2 hs
    have hi' : _ = true := hmod ▸ hi
    refine ⟨?_, hm, hw, hmod⟩
    rw [hmod]
    simp [hb.1, hi']
  | ctxtFrame _ ih =>
    obtain ⟨hi, hm, hw, -⟩ := ih (by simpa using hok) hs
    exact ⟨by simpa using hi, hm, hw, rfl⟩
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet => exact ⟨rfl, rfl, id, rfl⟩
  | globalSet => exact ⟨rfl, rfl, fun hp => hp, rfl⟩
  | storeIntTrap ha hm h => exact keepsM_storeTop (.intTrap ha hm h)
  | storeIntVal ha hm hw => exact keepsM_storeTop (.intVal ha hm hw)
  | storeFloatTrap ha hm h => exact keepsM_storeTop (.floatTrap ha hm h)
  | storeFloatVal ha hm hw => exact keepsM_storeTop (.floatVal ha hm hw)
  | storePackTrap ha hm h => exact keepsM_storeTop (.packTrap ha hm h)
  | storePackVal ha hm hw => exact keepsM_storeTop (.packVal ha hm hw)
  | _ => simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

end Silmaril.Wasm.SpecTec.Sim20.GoodMerge
