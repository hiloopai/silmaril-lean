module

public import Silmaril.Wasm.Tools.Component.Wat.Defs
public import Silmaril.Wasm.Component.Wat.Thms

/-!
# Component WAT with every built-in: each built-in reads back

`item_canon : R.item (P.canon c) = some (.canons [c])` for every `BinaryP3.Canon`, and the
well-formedness of the printed atoms (`wf_canon`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Wat

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Wat (Sexp kw num num? nm nm? bytesS bytes? mapO num?_num
  canonOpts_rt valType_rt coreValType_rt wf_canonOpt wf_valType wf_coreValType)
open Silmaril.Wasm.Component.Wat.Sexp (WF WFL)
open Silmaril.Wasm.Component.Binary (CanonOpt CoreValType)
open Silmaril.Wasm.Component.BinaryP3 (Canon Section Ast)

/-- Each built-in's keyword names it. -/
theorem bkOf?_name (b : BK) : bkOf? b.name = some b := by
  cases b <;> decide +kernel

/-- A built-in item reads as its body. -/
theorem item_builtin (b : BK) (args : List Sexp) :
    R.item (P.builtin b args) = (R.builtinK b args).map fun c => .canons [c] := by
  simp only [P.builtin, kw, R.item, R.coreItem, R.builtin, bkOf?_name, Option.bind_some]

theorem opts_rt (os : List CanonOpt) :
    mapO _root_.Silmaril.Wasm.Component.Wat.R.canonOpt (P.opts os) = some os :=
  canonOpts_rt os

theorem asyncFlag_rt (a : Bool) : R.asyncFlag (P.asyncL a) = some a := by
  cases a <;> rfl

theorem sharedPre_rt (b : Bool) (r : List Sexp) (h : r.head? ≠ some (kw "shared")) :
    R.sharedPre (P.sharedL b ++ r) = (b, r) := by
  cases b
  · match r, h with
    | [], _ => rfl
    | .atom a :: r', h =>
      have ha : a ≠ "shared" := fun e => h (by rw [e]; rfl)
      simp [P.sharedL, R.sharedPre, ha]
    | .str _ :: _, _ => rfl
    | .list _ :: _, _ => rfl
  · rfl

theorem taskReturn_rt (r : Option Binary.ValType) (os : List CanonOpt) :
    R.taskReturn ((r.map fun t => .list [kw "result", Wat.P.valType t]).toList ++ P.opts os) =
      some (.taskReturn r os) := by
  cases r with
  | some t => simp [R.taskReturn, kw, valType_rt, opts_rt]
  | none =>
    cases os with
    | nil => rfl
    | cons o os =>
      cases o <;> simp [R.taskReturn, P.opts, _root_.Silmaril.Wasm.Component.Wat.P.canonOpt,
        mapO, _root_.Silmaril.Wasm.Component.Wat.R.canonOpt, canonOpts_rt]

/-- Items other than nested components and `core` items go through `Wat`'s reader. -/
theorem item_other (k : String) (ss : List Sexp) (h1 : k ≠ "component") (h2 : k ≠ "core") :
    R.item (.list (.atom k :: ss)) =
      (_root_.Silmaril.Wasm.Component.Wat.R.itemKw k ss).map Section.ofV0 := by
  rw [R.item.eq_def]
  split <;> simp_all

/-- The lift and lower built-ins read back (through `Wat`'s reader). -/
theorem item_lift (f : Nat) (os : List CanonOpt) (t : Nat) :
    R.item (P.canon (.lift f os t)) = some (.canons [.lift f os t]) := by
  have h := _root_.Silmaril.Wasm.Component.Wat.item_canon (.lift f os t)
  simp only [P.canon, _root_.Silmaril.Wasm.Component.Wat.P.canon] at h ⊢
  rw [_root_.Silmaril.Wasm.Component.Wat.item_kw _ _ (by decide)] at h
  rw [kw, item_other _ _ (by decide) (by decide), h]; rfl

theorem item_lower (f : Nat) (os : List CanonOpt) :
    R.item (P.canon (.lower f os)) = some (.canons [.lower f os]) := by
  have h := item_builtin .lower (.list [kw "func", num f] :: P.opts os)
  simp only [BK.name, P.builtin, P.opts] at h
  simp only [P.canon, _root_.Silmaril.Wasm.Component.Wat.P.canon]
  rw [h]
  simp [R.builtinK, canonOpts_rt]

/-- A number is not the keyword `shared`. -/
theorem num_ne_shared (n : Nat) : (num n :: ([] : List Sexp)).head? ≠ some (kw "shared") := by
  intro h
  have e : num n = kw "shared" := by simpa using h
  have h1 := num?_num n
  rw [e] at h1
  have h2 : num? (kw "shared") = none := by decide
  rw [h2] at h1
  cases h1

theorem num_ne_shared' (n : Nat) (r : List Sexp) : (num n :: r).head? ≠ some (kw "shared") := by
  have := num_ne_shared n
  simpa using this

theorem item_taskReturn (r : Option Binary.ValType) (os : List CanonOpt) :
    R.item (P.canon (.taskReturn r os)) = some (.canons [.taskReturn r os]) := by
  rw [P.canon, item_builtin]
  simp only [R.builtinK, taskReturn_rt, Option.map_some]

theorem item_spawnRef (sh : Bool) (ft : Nat) :
    R.item (P.canon (.threadSpawnRef sh ft)) = some (.canons [.threadSpawnRef sh ft]) := by
  rw [P.canon, item_builtin]
  simp only [R.builtinK, sharedPre_rt sh [num ft] (num_ne_shared' ft []), R.tOnly, num?_num,
    Option.map_some]

theorem item_spawnIndirect (sh : Bool) (ft tbl : Nat) :
    R.item (P.canon (.threadSpawnIndirect sh ft tbl)) =
      some (.canons [.threadSpawnIndirect sh ft tbl]) := by
  rw [P.canon, item_builtin]
  simp only [R.builtinK, sharedPre_rt sh [num ft, num tbl] (num_ne_shared' ft _), R.two,
    num?_num]
  rfl

theorem sharedPre_nil (sh : Bool) : R.sharedPre (P.sharedL sh) = (sh, []) := by
  cases sh <;> rfl

theorem item_parallelism (sh : Bool) :
    R.item (P.canon (.threadAvailableParallelism sh)) =
      some (.canons [.threadAvailableParallelism sh]) := by
  rw [P.canon, item_builtin]
  simp only [R.builtinK, sharedPre_nil, R.none0, Option.map_some]

/-- **Every built-in reads back.** -/
theorem item_canon (c : Canon) : R.item (P.canon c) = some (.canons [c]) := by
  cases c with
  | lift f os t => exact item_lift f os t
  | lower f os => exact item_lower f os
  | taskReturn r os => exact item_taskReturn r os
  | threadSpawnRef sh ft => exact item_spawnRef sh ft
  | threadSpawnIndirect sh ft tbl => exact item_spawnIndirect sh ft tbl
  | threadAvailableParallelism sh => exact item_parallelism sh
  | _ =>
    rw [P.canon, item_builtin]
    simp [R.builtinK, R.tOnly, R.tOpts, R.tAsync, R.none0, R.context, R.memory, R.two,
      asyncFlag_rt, opts_rt, coreValType_rt]

/-! ## Well-formedness -/

theorem wf_builtin (k : BK) (args : List Sexp) (hk : Wat.Sexp.AtomOk k.name) (h : WFL args) :
    WF (P.builtin k args) := by
  simp [P.builtin, kw, Wat.wf_atom, Wat.wf_list, Wat.wfl_cons, hk, h]
  decide

theorem wfl_opts (os : List CanonOpt) : WFL (P.opts os) := by
  simp [P.opts, Wat.wfl_map, wf_canonOpt]

theorem atomOk_async : Wat.Sexp.AtomOk "async" := by decide
theorem atomOk_shared : Wat.Sexp.AtomOk "shared" := by decide
theorem atomOk_result : Wat.Sexp.AtomOk "result" := by decide
theorem atomOk_memory : Wat.Sexp.AtomOk "memory" := by decide

theorem wfl_async (a : Bool) : WFL (P.asyncL a) := by
  cases a <;> simp [P.asyncL, kw, Wat.wfl_cons, Wat.wf_atom, atomOk_async]

theorem wfl_shared (a : Bool) : WFL (P.sharedL a) := by
  cases a <;> simp [P.sharedL, kw, Wat.wfl_cons, Wat.wf_atom, atomOk_shared]

theorem wf_canon (c : Canon) : WF (P.canon c) := by
  cases c with
  | lift f os t => exact _root_.Silmaril.Wasm.Component.Wat.wf_canon (.lift f os t)
  | lower f os => exact _root_.Silmaril.Wasm.Component.Wat.wf_canon (.lower f os)
  | taskReturn r os =>
    refine wf_builtin _ _ (by decide +kernel) ?_
    cases r <;> simp [kw, wfl_opts, wf_valType, Wat.wf_atom, atomOk_result]
  | _ =>
    refine wf_builtin _ _ (by decide +kernel) ?_
    simp [kw, wfl_opts, wfl_async, wfl_shared, wf_coreValType, Wat.wf_atom, atomOk_memory]

end Silmaril.Wasm.Tools.Component.Wat
