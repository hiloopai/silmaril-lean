module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.TableFill

/-!
# Track r4-read: `Step_read/table.size` (27), `table.copy-oob` (31), `table.init-oob` (35),
backward, under validity

Round 3 found all three false without a hypothesis the target lacked:

* `table.size`: SpecTec's result `CONST at (% n)` carries the exact count, Core's
  `BitVec.ofNat _ n`. The store bounds (`ReadValid.store`) keep `n < 2 ^ 32`, so the two agree.
* `table.copy-oob`, `table.init-oob`: the premise `A \/ B` short-circuits, so when `A` holds the
  second table (resp. element segment) is never looked up, while Core's `copyOob`/`initOob` look
  up both. Index resolution (`ReadValid.idx`) gives both, so both disjuncts evaluate, and the
  premise is read back as Core's disjunction (`Memory.or_true`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv adminsToV_eq_quad decode_aconst decode_tableCopy decode_tableInit NoAcc)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_tableSize {a : Admin} (h : Typing.adminHead a = "TABLE.SIZE") :
    ∃ x, a = .plain (.tableSize x) := by
  revert h
  admin_head_inv

theorem decode_tableSize {a : Admin} {X : Value} (h : adminToV a = .case "TABLE.SIZE" X) :
    ∃ x : TableIdx, a = .plain (.tableSize x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_tableSize (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

variable (B : Builtins)

/-- `|$table(z, x).REFS|` for a resolved table, in a rule scope. -/
theorem evalExp_tableLen' {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : TableIdx}
    {ta : Nat} {ti : TableInst} {zx : IL.Id}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fx : (VarEnv.empty.bindVals σ).findVal? zx = some (idxV x.toNat))
    (ht : s.table? f x = some (ta, ti)) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE zx)]) "REFS"))
      (.num (.natN ti.refs.length)) := by
  have h := Memory.evalExp_tableRefsLen (State.stateDefs_simEnv B) (evalExp_var fz)
    (evalExp_var fx) (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti)
  rwa [List.length_map] at h

/-- `|$elem(z, y).REFS|` for a resolved element segment, in a rule scope. -/
theorem evalExp_elemLen' {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {y : ElemIdx}
    {ea : Nat} {ei : ElemInst} {zy : IL.Id}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fy : (VarEnv.empty.bindVals σ).findVal? zy = some (idxV y.toNat))
    (he : s.elem? f y = some (ea, ei)) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE zy)]) "REFS"))
      (.num (.natN ei.refs.length)) := by
  have h := RefsGC.evalExp_len (RefsGC.evalExp_dot (Memory.evalExp_elem_of
    (State.stateDefs_simEnv B) (evalExp_var fz) (evalExp_var fy) (Memory.elemAt_of_elem? hn he))
    (Memory.elemInstV_REFS ei))
  rwa [List.length_map] at h

variable (NA : NoAcc B)

include NA in

/-- **`Step_read` 27 (`table.size`), backward, under the store bounds.** -/
theorem bwdV_tableSize : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 27 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableSize hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨LIM, fl, -⟩ := hq "lim" (.varT "limits" []) (by simp)
  obtain ⟨RT, fr, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "TABLE.SIZE" X]]) ∧
      w = .list [.case "CONST" (.tuple [AT, .case "%" (.tuple [N])])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single hcode
  obtain ⟨x, rfl, rfl⟩ := decode_tableSize ha
  subst hZ
  have h₁ := ifPrem (hp _ List.mem_cons_self)
  obtain ⟨v₁, v₂, e₁, -, -⟩ := evalExp_cmpE_iff.1 h₁
  obtain ⟨ta, ti, ht, rfl⟩ := BwdRead.tableLen_inv B NA rfl fz fx e₁
  have eN : N = .num (.natN ti.refs.length) :=
    (RefsGC.eq_of_evalExp_eq h₁ e₁ (evalExp_var fn)).symm
  have h₂ := ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨T, -, eT, -, -⟩ := evalExp_cmpE_iff.1 h₂
  obtain ⟨T₀, hT₀, hTT⟩ := evalExp_dotE_iff.1 eT
  obtain ⟨ta', ti', ht', rfl⟩ := BwdRead.table_inv B NA rfl fz fx hT₀
  rw [ht] at ht'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ht')
  have eAT : AT = Encode.toValue ti.type.address := by
    have hR := RefsGC.eq_of_evalExp_eq h₂ eT (evalExp_case (evalExp_tup3 (evalExp_var fa)
      (evalExp_var fl) (evalExp_var fr)))
    have hT : T = .case "%%%" (.tuple [Encode.toValue ti.type.address,
        Encode.toValue ti.type.limits, Silmaril.SpecTec.Equiv.Validation.tyV ti.type.element]) := by
      simpa using hTT.symm
    rw [hT] at hR
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hR
    exact hR.1.symm
  have hlt := lt_width (a := ti.type.address) (table_lt32 hv.store ht)
  refine ⟨[aconst ti.type.address (BitVec.ofNat _ ti.refs.length)], ?_, .table (.size ht)⟩
  rw [hc.2, eAT, eN]
  simp only [adminsToV, State.adminToV_aconst, Memory.toNat_ofNat_of_lt hlt]

/-- **`Step_read` 31 (`table.copy-oob`), backward, under validity.** -/
theorem bwdV_tableCopyOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 31 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableCopyOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT₁, fa₁, hAT₁⟩ := hq "at_1" State.addrtypeT (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" (State.numAtT "at_1") (by simp)
  obtain ⟨AT₂, fa₂, hAT₂⟩ := hq "at_2" State.addrtypeT (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" (State.numAtT "at_2") (by simp)
  obtain ⟨AT', fa', -⟩ := hq "at'" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X₁, fx₁, -⟩ := hq "x_1" State.idxT (by simp)
  obtain ⟨X₂, fx₂, -⟩ := hq "x_2" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "TABLE.COPY" (.tuple [X₁, X₂])]])
      ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x₁, x₂, rfl, hX⟩ := decode_tableCopy h₄
  obtain ⟨rfl, rfl⟩ := Value.tuple.inj hX |> fun h => (List.cons.inj h).imp id
    (fun h => (List.cons.inj h).1)
  obtain ⟨t₁, b₁, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT₁
  obtain ⟨t₂, b₂, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₂ hAT₂
  obtain ⟨t', b', rfl, rfl, hN⟩ := decode_aconst h₃
  have eN : N = .num (.natN b'.toNat) := by simpa using hN
  subst eN hZ
  obtain ⟨ix₁, ix₂⟩ := idx_last4 hv (c := ⟨s, f, is⟩) his
  obtain ⟨ta₁, ti₁, ht₁⟩ := table_of_isSome ix₁
  obtain ⟨ta₂, ti₂, ht₂⟩ := table_of_isSome ix₂
  have hoob := Memory.or_true (ifPrem (hp _ List.mem_cons_self))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi₁)) (evalExp_var fn))
    (evalExp_tableLen' B fz fx₁ ht₁)
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi₂)) (evalExp_var fn))
    (evalExp_tableLen' B fz fx₂ ht₂)
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  rw [his]
  exact .table (.copyOob ht₁ ht₂ hoob)

/-- **`Step_read` 35 (`table.init-oob`), backward, under validity.** -/
theorem bwdV_tableInitOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 35 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableInitOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, hAT⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "TABLE.INIT" (.tuple [X, Y])]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x, y, rfl, hXY⟩ := decode_tableInit h₄
  obtain ⟨rfl, rfl⟩ := Value.tuple.inj hXY |> fun h => (List.cons.inj h).imp id
    (fun h => (List.cons.inj h).1)
  obtain ⟨t, b, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₃
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN hZ
  obtain ⟨ix, iy⟩ := idx_last4 hv (c := ⟨s, f, is⟩) his
  obtain ⟨ta, ti, ht⟩ := table_of_isSome ix
  obtain ⟨ea, ei, hei⟩ := elem_of_isSome iy
  have hoob := Memory.or_true (ifPrem (hp _ List.mem_cons_self))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi)) (evalExp_var fn))
    (evalExp_tableLen' B fz fx ht)
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fj)) (evalExp_var fn))
    (evalExp_elemLen' B fz fy hei)
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  rw [his]
  exact .table (.initOob (i := b) (j := j) (n := n) ht hei hoob)

end Silmaril.Wasm.SpecTec.Sim.Round4Read
