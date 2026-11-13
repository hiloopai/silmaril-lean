module

public import Silmaril.Wasm.Wasmi.RoundFree.Defs
public import Silmaril.Wasm.Execution.Core.Sim.SetFuncs

@[expose] public section

/-!
# Core 3.0 steps keep code free of rounding operators

`step_free`: a Core 3.0 step from a `Free` configuration, under a host that keeps stores free
(`HostKeeps`), reaches a `Free` configuration. New code enters a configuration only from a
structured body already in the code (`block`, `loop`, `if`, `try_table`, a label's
continuation), from a function body of the store (`call_ref-func`) or as values and fixed
instructions (every other rule); the store's functions change only at a host call.

New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi.RoundFree

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Wasmi.Observed Silmaril.Wasm.Wasmi.RoundFree

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Structure -/

@[simp] theorem rfIs_nil : rfIs [] = true := by simp [rfIs]

@[simp] theorem rfIs_cons (i : Instr) (is : List Instr) : rfIs (i :: is) = (rfI i && rfIs is) := by
  simp [rfIs]

@[simp] theorem rfAs_nil : rfAs [] = true := by simp [rfAs]

@[simp] theorem rfAs_cons (a : Admin) (as : List Admin) : rfAs (a :: as) = (rfA a && rfAs as) := by
  simp [rfAs]

@[simp] theorem rfAs_append : ∀ (x y : List Admin), rfAs (x ++ y) = (rfAs x && rfAs y)
  | [], _ => by simp
  | a :: x, y => by simp [rfAs_append x y, Bool.and_assoc]

theorem rfAs_iff : ∀ l : List Admin, rfAs l = true ↔ ∀ a ∈ l, rfA a = true
  | [] => by simp
  | a :: l => by simp [rfAs_iff l]

@[simp] theorem rfA_toAdmin (v : Val) : rfA v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, rfA, rfI]

@[simp] theorem rfAs_vals : ∀ vs : List Val, rfAs (vals vs) = true
  | [] => by simp [vals]
  | v :: vs => by simpa [vals] using rfAs_vals vs

theorem rfAs_map_plain : ∀ b : List Instr, rfAs (b.map Admin.plain) = rfIs b
  | [] => by simp
  | i :: b => by simp [rfA, rfAs_map_plain b]

@[simp] theorem rfAs_expression (b : List Instr) : rfAs (expression b) = rfIs b :=
  rfAs_map_plain b

@[simp] theorem rfAs_result (r : Result) : rfAs r.toAdmin = true := by
  cases r <;> simp [Result.toAdmin, rfA, rfI]

@[simp] theorem rfA_constI32 (c : BitVec 32) : rfA (constI32 c) = true := by
  simp [constI32]

@[simp] theorem rfA_retToCallIn (m : ModuleInst) (a : Admin) :
    rfA (a.retToCallIn m) = rfA a := by
  rcases a with ⟨i⟩ | _ | _ | _ | _ | _ | _ | _
  · cases i <;> simp only [Admin.retToCallIn]
    split <;> simp [rfA, rfI]
  all_goals rfl

theorem StoreFree.addExn {s : Store H} (hs : StoreFree s) (e : ExnInst) : StoreFree (s.addExn e) :=
  hs

theorem StoreFree.of_funcs {s s' : Store H} (hs : StoreFree s) (he : s'.funcs = s.funcs) :
    StoreFree s' := by
  intro fi hfi
  exact hs fi (he ▸ hfi)

/-- The body of a Wasm function of a free store is free. -/
theorem StoreFree.body {s : Store H} (hs : StoreFree s) {a : Nat} {fi : FuncInst H} {code : Func}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) : rfIs code.body = true := by
  have := hs fi (List.mem_of_getElem? hf)
  simpa [rfF, hcode] using this

/-! ## The families -/

theorem parametric_rf {is is' : List Admin} (h : ParametricStep is is') : rfAs is' = true := by
  cases h <;> simp [rfA]

theorem numeric_rf {is is' : List Admin} (h : NumericStep P is is') : rfAs is' = true := by
  cases h <;> simp [rfA, rfI]

theorem vector_rf {is is' : List Admin} (h : VectorStep P is is') : rfAs is' = true := by
  cases h <;> simp [rfA, rfI]

theorem variable_rf {c c' : Config H} (h : VariableStep c c') : rfAs c'.code = true := by
  cases h <;> simp [rfA, rfI]

theorem table_rf {c c' : Config H} (h : TableStep P c c') : rfAs c'.code = true := by
  cases h <;> simp [rfA, rfI]

theorem memory_rf {c c' : Config H} (h : MemoryStep P c c') : rfAs c'.code = true := by
  cases h <;> simp [rfA, rfI, store8, load8u]

theorem reference_rf {c c' : Config H} (h : RefStep c c') : rfAs c'.code = true := by
  cases h <;> simp [rfA]

theorem aggregate_rf {c c' : Config H} (h : AggregateStep c c') : rfAs c'.code = true := by
  cases h <;> first
    | (simp [rfA, rfI]; done)
    | (rw [rfAs_iff]; intro a ha
       simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil] at ha
       rcases ha with ⟨r, -, rfl⟩ | ha <;> simp_all [rfA, rfI])

/-! ## Contexts -/

theorem rf_instrs_iff (vs : List Val) (is rest : List Admin) :
    rfAs (vals vs ++ is ++ rest) = true ↔ rfAs is = true ∧ rfAs rest = true := by
  simp

theorem rf_label_iff (n : Nat) (cont : List Instr) (b : List Admin) :
    rfAs [.label n cont b] = true ↔ rfIs cont = true ∧ rfAs b = true := by
  simp [rfA]

theorem rf_handler_iff (n : Nat) (cs : List Catch) (b : List Admin) :
    rfAs [.handler n cs b] = true ↔ rfAs b = true := by
  simp [rfA]

theorem rf_frame_iff (n : Nat) (fi : Frame) (b : List Admin) :
    rfAs [.frame n fi b] = true ↔ rfAs b = true := by
  simp [rfA]

/-! ## Core steps -/

/-- A Core 3.0 step keeps the code and the store free (the two parts of `Free`). -/
theorem step_free_aux (hh : HostKeeps host) {c c' : Config H}
    (h : Execution.Core.Step P host c c') (hcode : rfAs c.code = true) (hs : StoreFree c.store) :
    rfAs c'.code = true ∧ StoreFree c'.store := by
  induction h with
  | parametric h => exact ⟨parametric_rf h, hs⟩
  | numeric h => exact ⟨numeric_rf h, hs⟩
  | vector h => exact ⟨vector_rf h, hs⟩
  | «variable» h => exact ⟨variable_rf h, StoreFree.of_funcs hs h.funcs_eq⟩
  | table h => exact ⟨table_rf h, StoreFree.of_funcs hs h.funcs_eq⟩
  | memory h => exact ⟨memory_rf h, StoreFree.of_funcs hs h.funcs_eq⟩
  | reference h => exact ⟨reference_rf h, StoreFree.of_funcs hs h.funcs_eq⟩
  | aggregate h => exact ⟨aggregate_rf h, StoreFree.of_funcs hs h.funcs_eq⟩
  | ctxtInstrs _ _ ih =>
    exact ⟨(rf_instrs_iff _ _ _).2 ⟨(ih ((rf_instrs_iff _ _ _).1 hcode).1 hs).1,
      ((rf_instrs_iff _ _ _).1 hcode).2⟩, (ih ((rf_instrs_iff _ _ _).1 hcode).1 hs).2⟩
  | ctxtLabel _ ih =>
    exact ⟨(rf_label_iff _ _ _).2 ⟨((rf_label_iff _ _ _).1 hcode).1,
      (ih ((rf_label_iff _ _ _).1 hcode).2 hs).1⟩, (ih ((rf_label_iff _ _ _).1 hcode).2 hs).2⟩
  | ctxtHandler _ ih =>
    exact ⟨(rf_handler_iff _ _ _).2 (ih ((rf_handler_iff _ _ _).1 hcode) hs).1,
      (ih ((rf_handler_iff _ _ _).1 hcode) hs).2⟩
  | ctxtFrame _ ih =>
    exact ⟨(rf_frame_iff _ _ _).2 (ih ((rf_frame_iff _ _ _).1 hcode) hs).1,
      (ih ((rf_frame_iff _ _ _).1 hcode) hs).2⟩
  | callRefFunc _ hf _ _ hcd => exact ⟨by simp [rfA, StoreFree.body hs hf hcd], hs⟩
  | callRefHost _ _ _ _ _ hhost => exact ⟨by simp, hh _ _ _ _ _ hhost hs⟩
  | throw => exact ⟨by simp [throwing, rfA, rfI], StoreFree.addExn hs _⟩
  | _ => exact ⟨by simp_all [rfA, rfI, throwing], hs⟩

/-- **A Core 3.0 step keeps a configuration free of rounding operators**, under a host that
keeps stores free. -/
theorem step_free (hh : HostKeeps host) {c c' : Config H} (h : Execution.Core.Step P host c c')
    (hc : Free c) : Free c' :=
  step_free_aux hh h hc.1 hc.2

end Silmaril.Proofs.Wasm.Wasmi.RoundFree
