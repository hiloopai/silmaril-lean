module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# Round 5, pass 2, track read: the SIMD loads (42–51) do not fire on bounded code

Every `vload*` rule's left-hand side names a `VLOAD`/`VLOAD_LANE` instruction, which is the image
only of Core's `vecLoad`/`vecLoadLane`. Those are outside the bounded fragment
(`Round4.instrBnd`), so no rule of the ten fires from a configuration whose active code is
`Round4.AdminsBnd` (`ReadValidS.bnd`). The rules are discharged vacuously.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- An instruction image named `VLOAD` or `VLOAD_LANE` is a SIMD load. -/
theorem head_vload {a : Admin} (h : Typing.adminHead a = "VLOAD" ∨
    Typing.adminHead a = "VLOAD_LANE") :
    (∃ t x arg, a = .plain (.vecLoad t x arg)) ∨
      ∃ t x arg j, a = .plain (.vecLoadLane t x arg j) := by
  rcases h with h | h
  · left
    revert h
    admin_head_inv
  · right
    revert h
    admin_head_inv

/-- A SIMD load is not `Round4.AdminBnd`. -/
theorem not_adminBnd_vload {a : Admin} (h : Typing.adminHead a = "VLOAD" ∨
    Typing.adminHead a = "VLOAD_LANE") : ¬ Round4.AdminBnd a := by
  rcases head_vload h with ⟨t, x, arg, rfl⟩ | ⟨t, x, arg, j, rfl⟩ <;>
    simp [Round4.AdminBnd, Round4.instrBnd]

/-- `Round4.AdminsBnd` at a member. -/
theorem adminBnd_of_mem : ∀ {l : List Admin} {a : Admin}, Round4.AdminsBnd l → a ∈ l →
    Round4.AdminBnd a
  | _ :: _, _, h, .head _ => h.1
  | _ :: _, _, h, .tail _ hm => adminBnd_of_mem h.2 hm

/-- An evaluated list has a value at every position of its expressions. -/
theorem evalExps_getElem? {env : Env} {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value}, EvalExps env ρ es vs → ∀ {k : Nat} {e : Exp},
      es[k]? = some e → ∃ v, vs[k]? = some v ∧ EvalExp env ρ e v
  | [], _, _, _, _, he => by simp at he
  | e' :: es, vs, h, k, e, he => by
      obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 h
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          subst he
          exact ⟨w, rfl, hw⟩
      | succ k => exact evalExps_getElem? hws (by simpa using he)

/-- A position of an image list is the image of the instruction at that position. -/
theorem adminsToV_getElem? : ∀ {is : List Admin} {k : Nat} {v : Value},
    (adminsToV is)[k]? = some v → ∃ a ∈ is, adminToV a = v
  | [], _, _, h => by simp [adminsToV] at h
  | a :: is, 0, v, h => ⟨a, List.mem_cons_self, by simpa [adminsToV] using h⟩
  | _ :: is, k + 1, v, h => by
      obtain ⟨a, ha, e⟩ := adminsToV_getElem? (is := is) (k := k) (by simpa [adminsToV] using h)
      exact ⟨a, List.mem_cons_of_mem _ ha, e⟩

/-- **A rule whose left-hand side names a SIMD load does not fire on bounded code.** -/
theorem not_fires_vload {env : Env} {j : Nat} {nm : IL.Id} {qs : List Param} {L : List Exp}
    {rhs : Exp} {prems : List Prem} {k : Nat} {op : MixopS} {e : Exp}
    (hr : HasRuleAt env "Step_read" "%~>%" j
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE L]), rhs]) prems))
    (hk : L[k]? = some (.caseE op e)) (hop : op = "VLOAD" ∨ op = "VLOAD_LANE") {c : Config H}
    {w : Value} (hb : Round4.AdminsBnd c.code)
    (hf : Fires env "Step_read" j (.tuple [configV hn c, w])) : False := by
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body hr hf)
  obtain ⟨-, hl⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  obtain ⟨v, hv, ev⟩ := evalExps_getElem? (RefsGC.elems_of_list hl) hk
  obtain ⟨W, -, rfl⟩ := evalExp_caseE_iff.1 ev
  obtain ⟨a, ha, ea⟩ := adminsToV_getElem? hv
  have hh := Typing.adminToV_case ea
  exact not_adminBnd_vload (hh ▸ hop) (adminBnd_of_mem hb ha)

/-- **`Step_read` 42–51 (`vload*`), backward, under `ReadValidS`**: vacuous. -/
theorem bwdS_vload (i : Nat) (hi : i ∈ [42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) (c : Config H)
    (w : Value) (hv : ReadValidS c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) : False := by
  have RR := State.hasReadRules_simEnv (BI P hn host)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_fires_vload RR.vloadNumOob (k := 1) rfl (.inl rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadNumVal (k := 1) rfl (.inl rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadPackOob (k := 1) rfl (.inl rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadPackVal (k := 1) rfl (.inl rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadSplatOob (k := 1) rfl (.inl rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadSplatVal (k := 1) rfl (.inl rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadZeroOob (k := 1) rfl (.inl rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadZeroVal (k := 1) rfl (.inl rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadLaneOob (k := 2) rfl (.inr rfl) hv.bnd hf
  · exact not_fires_vload RR.vloadLaneVal (k := 2) rfl (.inr rfl) hv.bnd hf

end Silmaril.Wasm.SpecTec.Sim.Round5.Read

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- The pinned stream has 103 `Step_read` rules. -/
theorem readRules_length :
    (RefsGC.relRules (envOfScript Specs.wasm30) "Step_read").length = 103 := by
  rfl

/-- **No `Step_read` rule has an index beyond 102.** -/
theorem lt_of_fires_read {B : Builtins} {i : Nat} {v : Value}
    (hf : Fires (simEnv B) "Step_read" i v) : i < 103 := by
  obtain ⟨t, rules, r, hrel, hr, -⟩ := hf
  have hl : rules.length = 103 := by
    have h := readRules_length
    rw [← RefsGC.relRules_simEnv B] at h
    simpa [RefsGC.relRules, hrel] using h
  exact hl ▸ (List.getElem?_eq_some_iff.1 hr).1

end Silmaril.Wasm.SpecTec.Sim.Round5.Read
