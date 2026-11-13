module

public import Silmaril.Wasm.SpecTec.Sim20.BodyTyp.Thms
public import Silmaril.Wasm.V2.Validation.Modules

/-!
# V2 validation implies `packOkI`

Round 6 reduced the body-typing component of `StoreBulk.InvokeOk` to `packOkI`: every
packed load is below its type's width (`BodyTyp.InvokeOkS`). This file derives it from V2
validation.

* `packOkI_of_immediatesValid`: `Instr.immediatesValid` (the syntactic side conditions of the
  `syntax instr` productions) implies `packOkI`, at every depth. A strong induction on size;
  blocks, loops and conditionals recurse into their bodies.
* **`packOkI_of_instrOk`**, `packOkI_of_instrsOk`, `packOkI_of_exprOk`: so does V2 typing,
  through Silmaril's `InstrOk.immediatesValid`.
* **`packOkI_of_funcOk`**, **`packOkI_of_moduleOk`**: the body of a valid function, and of
  every function of a valid module.
* **`invokeOkS_of_valid`**: `BodyTyp.InvokeOkS` from its first three fields and a store whose
  Wasm functions are each valid in some context (`FuncsValid`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.PackValid

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.SpecTec.Sim20.BodyTyp (packOkI packOkIL packOkIL_eq InvokeOkS)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (FuncTypeSmall TypesSmall NamesTyped)

/-- A sequence each of whose members is `packOkI`. -/
theorem packOkIL_of_forall {b : List V2.Instr} (h : ∀ j ∈ b, packOkI j = true) :
    packOkIL b = true := by
  rw [packOkIL_eq, List.all_eq_true]
  exact h

/-- `immediatesValid` implies `packOkI`, below a size bound. -/
theorem packOkI_of_immediatesValid_lt (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → i.immediatesValid = true → packOkI i = true := by
  induction n with
  | zero => intro i hs; omega
  | succ n ih =>
    show ∀ i : V2.Instr, sizeOf i < n + 1 → i.immediatesValid = true → packOkI i = true
    intro i hs hv
    have hb : ∀ b : List V2.Instr, sizeOf b < n →
        (∀ x ∈ b.attach, (x.val).immediatesValid = true) → packOkIL b = true := fun b hb hj =>
      packOkIL_of_forall fun j hj' =>
        ih j (Nat.lt_trans (List.sizeOf_lt_of_mem hj') hb) (hj ⟨j, hj'⟩ (List.mem_attach _ _))
    cases i with
    | block bt b =>
      have hs' : sizeOf b < n := by simp only [V2.Instr.block.sizeOf_spec] at hs; omega
      simp only [V2.Instr.immediatesValid, List.all_eq_true] at hv
      simpa [packOkI] using hb b hs' hv
    | loop bt b =>
      have hs' : sizeOf b < n := by simp only [V2.Instr.loop.sizeOf_spec] at hs; omega
      simp only [V2.Instr.immediatesValid, List.all_eq_true] at hv
      simpa [packOkI] using hb b hs' hv
    | if_ bt b₁ b₂ =>
      have hs' : sizeOf b₁ < n ∧ sizeOf b₂ < n := by
        simp only [V2.Instr.if_.sizeOf_spec] at hs; omega
      simp only [V2.Instr.immediatesValid, List.all_eq_true, Bool.and_eq_true] at hv
      simp only [packOkI, Bool.and_eq_true]
      exact ⟨hb b₁ hs'.1 hv.1, hb b₂ hs'.2 hv.2⟩
    | intLoad t p a =>
      rcases p with _ | ⟨sz, sx⟩
      · rfl
      · simpa [packOkI, V2.Instr.immediatesValid] using hv
    | _ => rfl

/-- **`immediatesValid` implies `packOkI`.** -/
theorem packOkI_of_immediatesValid {i : V2.Instr} (h : i.immediatesValid = true) :
    packOkI i = true :=
  packOkI_of_immediatesValid_lt _ i (Nat.lt_succ_self _) h

/-- On a sequence. -/
theorem all_packOkI_of_immediatesValid {b : List V2.Instr}
    (h : b.all V2.Instr.immediatesValid = true) : b.all packOkI = true :=
  List.all_eq_true.2 fun j hj => packOkI_of_immediatesValid (List.all_eq_true.1 h j hj)

/-- **A V2-typed instruction is `packOkI`.** -/
theorem packOkI_of_instrOk {C : Context} {i : V2.Instr} {it : InstrType} (h : InstrOk C i it) :
    packOkI i = true :=
  packOkI_of_immediatesValid h.immediatesValid

/-- A V2-typed sequence is `packOkI`. -/
theorem packOkI_of_instrsOk {C : Context} {is : List V2.Instr} {it : InstrType}
    (h : InstrsOk C is it) : is.all packOkI = true :=
  all_packOkI_of_immediatesValid h.immediatesValid

/-- A V2-typed expression is `packOkI`. -/
theorem packOkI_of_exprOk {C : Context} {e : V2.Expr} {ts : CResultType} (h : ExprOk C e ts) :
    e.all packOkI = true :=
  packOkI_of_instrsOk h

/-- **The body of a valid function is `packOkI`.** -/
theorem packOkI_of_funcOk {C : Context} {f : V2.Func} {ft : V2.FuncType} (h : FuncOk C f ft) :
    f.body.all packOkI = true := by
  cases h with
  | mk _ hbody => exact packOkI_of_exprOk hbody

/-- A member of the left list of `Forall₂` has a partner. -/
theorem forall₂_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b, R a b := by
  induction h with
  | nil => simp at ha
  | cons hr _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, hr⟩
    · exact ih ha

/-- **Every function body of a valid module is `packOkI`.** -/
theorem packOkI_of_moduleOk {m : V2.Module} {ixt xt : List V2.ExternType} (h : ModuleOk m ixt xt)
    {f : V2.Func} (hf : f ∈ m.funcs) : f.body.all packOkI = true := by
  cases h with
  | mk _ _ _ _ _ _ _ hfuncs =>
    obtain ⟨ft, hok⟩ := forall₂_left hfuncs hf
    exact packOkI_of_funcOk hok

variable {H : Type}

/-- Every Wasm function of the store is valid in some context. -/
def FuncsValid (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ fn, fi.code = .wasm fn → ∃ C ft, FuncOk C fn ft

/-- **`InvokeOkS` with its `packs` field derived from V2 validation.** -/
theorem invokeOkS_of_valid {B : Silmaril.SpecTec.Sem.Builtins} {s : Store H} {f : Frame}
    (hT : TypesSmall f.module) (hN : NamesTyped B f.module)
    (hF : ∀ fi ∈ s.funcs, FuncTypeSmall fi.type ∧ TypesSmall fi.module ∧ NamesTyped B fi.module)
    (hV : FuncsValid s) : InvokeOkS B s f where
  frameTypes := hT
  frameNames := hN
  funcs := hF
  packs fi hfi fn hc := by
    obtain ⟨C, ft, hok⟩ := hV fi hfi fn hc
    exact packOkI_of_funcOk hok

end Silmaril.Wasm.SpecTec.Sim20.PackValid
