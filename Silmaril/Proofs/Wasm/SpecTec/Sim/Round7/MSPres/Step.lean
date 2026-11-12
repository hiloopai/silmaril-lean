module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Defs
public import Silmaril.Wasm.SingleThreaded.Locality

/-!
# Round 7, memory SIMD: a Core step keeps `NoMemSimd`

* `adminsMS_append`, `adminsMS_vals`, `adminsMS_expression`: `AdminsMS` on the pieces Core's
  rules build code from;
* `step_funcs`: a Core step keeps the store's function instances, except a returning host call
  (silmaril-lean's `framesLocal` lemmas for the delegated families);
* `step_noMemSimd`: **a Core step keeps `NoMemSimd`**, at every profile, for a host that adds no
  memory SIMD code (`HostKeepsMS`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Round6.MemSimd (instrMS instrsMS AdminMS AdminsMS StoreMS NoMemSimd memSimd)
open Round7.MSPres (HostKeepsMS)

variable {H : Type}

/-! ## `AdminsMS` on the pieces of code -/

theorem adminsMS_append : ∀ {l m : List Admin}, AdminsMS (l ++ m) ↔ AdminsMS l ∧ AdminsMS m
  | [], _ => by simp [AdminsMS]
  | a :: l, m => by
    simp only [List.cons_append, AdminsMS]
    rw [adminsMS_append]
    tauto

theorem instrsMS_append : ∀ {l m : List Instr}, instrsMS (l ++ m) = (instrsMS l && instrsMS m)
  | [], _ => by simp [instrsMS]
  | i :: l, m => by
    simp only [List.cons_append, instrsMS]
    rw [instrsMS_append, Bool.and_assoc]

theorem adminMS_toAdmin (v : Val) : AdminMS v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, AdminMS, instrMS, memSimd]

theorem adminsMS_vals : ∀ vs : List Val, AdminsMS (vals vs)
  | [] => trivial
  | v :: vs => ⟨adminMS_toAdmin v, adminsMS_vals vs⟩

theorem adminsMS_expression : ∀ {b : List Instr}, AdminsMS (expression b) ↔ instrsMS b = true
  | [] => by simp [expression, AdminsMS, instrsMS]
  | i :: b => by
    have ih := adminsMS_expression (b := b)
    simp only [expression, List.map_cons] at ih ⊢
    simp only [AdminsMS, AdminMS, instrsMS, Bool.and_eq_true, ih]

theorem adminsMS_iff : ∀ {l : List Admin}, AdminsMS l ↔ ∀ a ∈ l, AdminMS a
  | [] => by simp [AdminsMS]
  | a :: l => by simp [AdminsMS, adminsMS_iff (l := l)]

theorem adminsMS_take_drop_refs (n i : Nat) (rs : List Ref) :
    AdminsMS (List.take n (List.drop i (List.map Admin.ref rs))) := by
  refine adminsMS_iff.2 fun a ha => ?_
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  trivial

theorem adminsMS_result (r : Result) : AdminsMS r.toAdmin := by
  cases r with
  | values vs => exact adminsMS_vals vs
  | throw a => simp [Result.toAdmin, AdminsMS, AdminMS, instrMS, memSimd]
  | trap => simp [Result.toAdmin, AdminsMS, AdminMS]

/-! ## The store's functions -/

/-- **A Core step keeps the function instances**, except a returning host call. -/
theorem step_funcs {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') :
    c'.store.funcs = c.store.funcs ∨
      ∃ hf vs r, host hf c.store vs (.returned c'.store r) := by
  induction h with
  | «variable» h => exact .inl (VariableStep.framesLocal h).1
  | table h => exact .inl (TableStep.framesLocal h).1
  | memory h => exact .inl (MemoryStep.framesLocal h).1
  | reference h => exact .inl (RefStep.framesLocal h).1
  | aggregate h => exact .inl (AggregateStep.framesLocal h).1
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | ctxtFrame _ ih => exact ih
  | callRefHost _ _ _ _ _ hhost => exact .inr ⟨_, _, _, hhost⟩
  | _ => exact .inl rfl

/-- The store half of `step_noMemSimd`. -/
theorem step_storeMS {P : Profile} {host : HostSemantics H} (hh : HostKeepsMS host)
    {c c' : Config H} (h : Step P host c c') (hs : StoreMS c.store) : StoreMS c'.store := by
  rcases step_funcs h with he | ⟨hf, vs, r, hr⟩
  · unfold StoreMS at hs ⊢
    rw [he]
    exact hs
  · exact hh hf c.store vs c'.store r hr hs

/-! ## The code -/

theorem adminMS_of_isRetCallRef {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    AdminMS (c.retToCallIn m) := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · simp only [Admin.retToCallIn]
    split <;> simp [AdminMS, instrMS, memSimd]
  · simp [Admin.retToCallIn, AdminMS]
  · exact hc.elim

theorem instrsMS_of_funcs {s : Store H} (hs : StoreMS s) {a : Nat} {fi : FuncInst H} {fn : Func}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) : instrsMS fn.body = true :=
  hs fi (List.mem_of_getElem? hf) fn hcode

-- The family arms share one simp set; not every rule uses every lemma of it.
set_option linter.unusedSimpArgs false in
/-- The code half of `step_noMemSimd`. -/
theorem step_adminsMS {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hs : StoreMS c.store) (hc : AdminsMS c.code) : AdminsMS c'.code := by
  induction h with
  | parametric h => cases h <;> simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]
  | numeric h => cases h <;> simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]
  | vector h => cases h <;> simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]
  | «variable» h => cases h <;> simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]
  | table h => cases h <;> simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]
  | memory h => cases h <;> simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]
  | reference h => cases h <;> simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]
  | aggregate h => cases h <;> simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]
  | @ctxtInstrs _ _ _ _ vs is is' rest _ _ ih =>
    have h₀ : (AdminsMS (vals vs) ∧ AdminsMS is) ∧ AdminsMS rest := by
      simpa only [adminsMS_append] using hc
    have h₁ : AdminsMS is' := ih hs h₀.1.2
    exact adminsMS_append.2 ⟨adminsMS_append.2 ⟨h₀.1.1, h₁⟩, h₀.2⟩
  | @ctxtLabel _ _ _ _ n cont is is' _ ih =>
    have h₀ : instrsMS cont = true ∧ AdminsMS is := hc.1
    exact ⟨⟨h₀.1, ih hs h₀.2⟩, trivial⟩
  | @ctxtHandler _ _ _ _ n cs is is' _ ih =>
    have h₀ : AdminsMS is := hc.1
    exact ⟨ih hs h₀, trivial⟩
  | @ctxtFrame _ _ _ _ _ n is is' _ ih =>
    have h₀ : AdminsMS is := hc.1
    exact ⟨ih hs h₀, trivial⟩
  | callRefFunc _ hf _ _ hcode =>
    simp [AdminsMS, AdminMS, adminsMS_expression, instrsMS, instrsMS_of_funcs hs hf hcode]
  | callRefHost => exact adminsMS_result _
  | returnCallRefFrameAddr hcr =>
    exact adminsMS_append.2 ⟨adminsMS_vals _, trivial, adminMS_of_isRetCallRef hcr _, trivial⟩
  | _ => simp_all [AdminsMS, AdminMS, instrMS, instrsMS, memSimd, constI32, adminMS_toAdmin,
      adminsMS_append, adminsMS_vals, adminsMS_expression, adminsMS_result, store8, load8u,
      adminsMS_take_drop_refs]

/-! ## The whole configuration -/

/-- **A Core step keeps `NoMemSimd`**, at every profile, for a host that adds no memory SIMD
code. -/
theorem step_noMemSimd {P : Profile} {host : HostSemantics H} (hh : HostKeepsMS host)
    {c c' : Config H} (h : Step P host c c') (hc : NoMemSimd c) : NoMemSimd c' :=
  ⟨step_storeMS hh h hc.store, step_adminsMS h hc.store hc.code⟩

/-- **Runs keep `NoMemSimd`.** -/
theorem steps_noMemSimd {P : Profile} {host : HostSemantics H} (hh : HostKeepsMS host)
    {c c' : Config H} (h : Steps P host c c') (hc : NoMemSimd c) : NoMemSimd c' := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact step_noMemSimd hh hs ih

end Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres
