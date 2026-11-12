module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms

/-!
# Round 7, REH route 2: the primitives of `envBI` conform (unrefined)

Round 3's strictness lemmas (`EraseAll.oks_call`, `oks_utf8Call`) give export-free answers for
every primitive except `$hostcall`, `$blocktype_` and `$sx`. `$blocktype_` answers an instruction
type and `$sx` answers `ε`, both export-free. `$hostcall` answers `outcomeV` images, which
conform at `hostcallresult*` (`vtB_outcomeV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)
open Silmaril.SpecTec.Equiv.RuntimeBridge (moduleInstToValue)

variable {H : Type}

/-! ## Values whose fields are export-free -/

theorem unfN (n : String) (h : (sigX.aliases.lookup n).isNone = true := by decide) :
    unf sigX (.name n []) = .name n [] := by
  simp only [Option.isNone_iff_eq_none] at h
  simp [unf, unalias, h]

theorem vtF_of_nx (S : Sig) (n : String) : ∀ gs : List (AtomS × Value),
    (∀ g ∈ gs, nxB g.2 = true) → vtF S n gs = true
  | [], _ => rfl
  | (k, v) :: gs, h => by
    simp only [vtF, Bool.and_eq_true]
    exact ⟨vtB_of_nxB S _ v (h _ (List.mem_cons_self ..)),
      vtF_of_nx S n gs fun g hg => h g (List.mem_cons_of_mem _ hg)⟩

theorem vtF_iff (S : Sig) (n : String) : ∀ gs : List (AtomS × Value),
    vtF S n gs = true ↔ ∀ g ∈ gs, vtB S (fieldAT S n g.1) g.2 = true
  | [] => by simp [vtF]
  | (k, v) :: gs => by simp [vtF, vtF_iff S n gs]

theorem nxB_defType (t : Validation.DefType) : nxB (CT.defType t) = true := by
  simp [CT]

theorem vtB_moduleInst (m : ModuleInst) :
    vtB sigX (.name "moduleinst" []) (moduleInstToValue CT m) = true := by
  unfold moduleInstToValue
  rw [vtB_struct_name (by decide) (unfN "moduleinst")]
  refine vtF_of_nx _ _ _ fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [CT]

theorem vtB_funcInst (hn : H → String) (fi : FuncInst H) :
    vtB sigX (.name "funcinst" []) (Sim.funcInstV hn fi) = true := by
  unfold Sim.funcInstV
  rw [vtB_struct_name (by decide) (unfN "funcinst"), vtF_iff]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact vtB_of_nxB _ _ _ (nxB_defType _)
  · show vtB sigX (fieldAT sigX "funcinst" "MODULE") _ = true
    rw [show fieldAT sigX "funcinst" "MODULE" = .name "moduleinst" [] from
      (atEq_iff _ _).1 (by decide)]
    exact vtB_moduleInst fi.module
  · exact vtB_of_nxB _ _ _ (Swap.nxB_codeV hn fi)

theorem vtB_storeV (hn : H → String) (s : Store H) :
    vtB sigX (.name "store" []) (Sim.storeV hn s) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Swap.nxB_storeRest (H := H) s
  unfold Sim.storeV
  rw [vtB_struct_name (by decide) (unfN "store"), vtF_iff]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vtB_of_nxB _ _ _ h1
  · exact vtB_of_nxB _ _ _ h2
  · exact vtB_of_nxB _ _ _ h3
  · exact vtB_of_nxB _ _ _ h4
  · show vtB sigX (fieldAT sigX "store" "FUNCS") _ = true
    rw [show fieldAT sigX "store" "FUNCS" = .iter (.name "funcinst" []) from
      (atEq_iff _ _).1 (by decide), vtB_list_iter (b := .name "funcinst" []) (by decide)
      (show unf sigX (.iter (.name "funcinst" [])) = .iter (.name "funcinst" []) by
        simp [unf, unalias]), vtL_iff]
    intro w hw
    obtain ⟨fi, _, rfl⟩ := List.mem_map.1 hw
    exact vtB_funcInst hn fi
  · exact vtB_of_nxB _ _ _ h5
  · exact vtB_of_nxB _ _ _ h6
  · exact vtB_of_nxB _ _ _ h7
  · exact vtB_of_nxB _ _ _ h8
  · exact vtB_of_nxB _ _ _ h9

theorem nxB_resultV (r : Result) : nxB (Sim.resultV r) = true := by
  cases r <;> simp [Sim.resultV]

theorem vtB_outcomeV (hn : H → String)
    (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result) :
    vtB sigX (.name "hostcallresult" []) (Sim.outcomeV hn o) = true := by
  cases o with
  | returned s r =>
    rw [Sim.outcomeV, vtB_case_name (by decide) (unfN "hostcallresult")]
    rw [show caseAT sigX "hostcallresult" "RES" = .tup [.name "store" [], .name "result" []]
      from (atEq_iff _ _).1 (by decide), vtB_tup (xs := [.name "store" [], .name "result" []])
      (by decide) (by simp [unf, unalias])]
    simp only [vtT, Bool.and_eq_true, Bool.and_true]
    exact ⟨vtB_storeV hn s, vtB_of_nxB _ _ _ (nxB_resultV r)⟩
  | diverged =>
    exact vtB_of_nxB _ _ _ (by simp [Sim.outcomeV])

end Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims
