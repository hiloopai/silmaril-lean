module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Config
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs

/-!
# Round 7, encoder lemma: the converse, and `$hostcall` at export-free stores

* `storeNE_of_efB`: a store whose image passes `efB` is export-free, so `efB (storeV hn s)` and
  `Round5.Pos.StoreNE s` are equivalent (`efB_storeV_iff`).
* `hostcall_storeNE`: an export-blind host called in an export-free store returns export-free
  stores: by the second half of `HostExportBlind` with `stripStore s = s`, every outcome is
  `stripOutcome` of one.
* `efB_hostcallCall`: so round 4's `$hostcall` primitive (`Prims.hostcallCall`), called at
  arguments that pass `efB`, answers a value that passes `efB`. This is the `$hostcall` case of
  the determination ingredient of `Round7.Task.envAgreeNE`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (AdminNE AdminsNE StoreNE NoExports)

variable {H : Type}

@[simp] theorem isNilList_list (l : List Value) : isNilList (.list l) = l.isEmpty := by
  cases l <;> rfl

open TypAgree (ExpFree) in
theorem expFree_field {gs : List (IL.AtomS × Value)} {a : IL.AtomS} {v : Value}
    (h : ExpFree (.struct gs)) (hm : (a, v) ∈ gs) : ExpFree v := by
  cases h with
  | struct hf _ => exact hf _ hm

open TypAgree (ExpFree) in
theorem exports_nil_of_expFree {m : ModuleInst} (h : ExpFree (moduleInstToValue CT m)) :
    m.exports = [] := by
  cases h with
  | struct _ hE =>
    have := hE ("EXPORTS", .list (m.exports.map exportInstToValue)) (by simp) rfl
    simpa using this

open TypAgree (ExpFree) in
theorem module_exports_nil_of_expFree (hn : H → String) {fi : FuncInst H}
    (h : ExpFree (funcInstV hn fi)) : fi.module.exports = [] :=
  exports_nil_of_expFree (expFree_field h (a := "MODULE") (by simp))

/-- **The converse of `efB_storeV`.** -/
theorem storeNE_of_efB (hn : H → String) {s : Store H} (h : efB (storeV hn s) = true) :
    StoreNE s := by
  intro fi hfi
  have hF := expFree_field (expFree_of_efB _ h) (a := "FUNCS")
    (v := .list (s.funcs.map (funcInstV hn))) (by simp)
  cases hF with
  | list hl => exact module_exports_nil_of_expFree hn (hl _ (List.mem_map_of_mem hfi))

theorem efB_storeV_iff (hn : H → String) (s : Store H) :
    efB (storeV hn s) = true ↔ StoreNE s :=
  ⟨storeNE_of_efB hn, efB_storeV hn⟩

/-- An export-free store is its own stripped form. -/
theorem stripStore_of_storeNE {s : Store H} (h : StoreNE s) : Round7.stripStore s = s := by
  obtain ⟨tags, globals, mems, tables, funcs, datas, elems, structs, arrays, exns⟩ := s
  simp only [Round7.stripStore, Store.mk.injEq, and_true, true_and]
  conv => rhs; rw [← List.map_id funcs]
  refine List.map_congr_left fun fi hfi => ?_
  have he : fi.module.exports = [] := h fi hfi
  simp [Round7.stripModule, ← he]

/-- A stripped store is export-free. -/
theorem storeNE_stripStore (s : Store H) : StoreNE (Round7.stripStore s) := by
  intro fi hfi
  simp only [Round7.stripStore, List.mem_map] at hfi
  obtain ⟨fi₀, -, rfl⟩ := hfi
  rfl

/-- The stores of the outcomes of a host call. -/
def OutcomeNE : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result → Prop
  | .returned s _ => StoreNE s
  | .diverged => True

/-- **An export-blind host called in an export-free store returns export-free stores.** -/
theorem hostcall_storeNE {host : HostSemantics H} (hb : Round7.HostExportBlind host) {h : H}
    {s : Store H} {vs : List Val} {o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result}
    (hs : StoreNE s) (ho : host h s vs o) : OutcomeNE o := by
  rw [← stripStore_of_storeNE hs] at ho
  obtain ⟨o₀, -, rfl⟩ := hb.2 h s vs o ho
  cases o₀ with
  | returned s₀ r => exact storeNE_stripStore s₀
  | diverged => trivial

@[simp] theorem efB_resultV (r : Result) : efB (resultV r) = true := by
  cases r <;> simp [resultV]

theorem efB_outcomeV (hn : H → String) {o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result}
    (h : OutcomeNE o) : efB (outcomeV hn o) = true := by
  cases o with
  | returned s r => simp [outcomeV, efB_storeV hn h]
  | diverged => rfl

/-- **`$hostcall` preserves `efB`** for an export-blind host: at arguments whose values pass
`efB`, round 4's primitive answers a value that passes `efB`. -/
theorem efB_hostcallCall (hn : H → String) {host : HostSemantics H}
    (hb : Round7.HostExportBlind host) {ws : List ArgV} {v : Value}
    (hw : ∀ w, ArgV.val w ∈ ws → efB w = true) (h : Prims.hostcallCall hn host ws = some v) :
    efB v = true := by
  unfold Prims.hostcallCall at h
  split at h
  · rename_i hex
    cases h
    have hargs := hex.choose_spec.1
    have hos := hex.choose_spec.2.choose_spec
    have hst' : ∀ p : H × Store H × List Val, ws = Prims.hostArgs hn p.1 p.2.1 p.2.2 →
        efB (storeV hn p.2.1) = true := by
      rintro p rfl
      exact hw _ (by simp [Prims.hostArgs])
    have hst := hst' _ hargs
    have hne := storeNE_of_efB hn hst
    simp only [efB_list, efBs_map, List.all_eq_true]
    intro o ho
    exact efB_outcomeV hn (hostcall_storeNE hb hne ((hos o).2 ho))
  · cases h

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
