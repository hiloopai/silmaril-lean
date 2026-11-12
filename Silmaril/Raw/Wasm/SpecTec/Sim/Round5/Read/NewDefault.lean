module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Zero

/-!
# Round 5, pass 2, track read: `array.new_default` (72), backward, under `ReadValidS`

The rule's premises are `Expand($type(z, x), ARRAY mut? zt)` and `$default_($unpack(zt)) = ?(val)`.
`ReadValidS.seg` gives the type of `x` (validation: an array type with a defaultable element
type). `$type(z, x)` then evaluates to its image, and SpecTec's `Expand` on that image ends at
Core's expansion (`R4Fwd.expandInv_builtins`), which fixes the quantifier `zt`
(`R4Fwd.zt_of_expand`). `$default_` evaluates to Core's default value, which fixes `val`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open BwdRead (cfg_inv)
open Round4Read (decode_aconst_at)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_arrayNewDefault {a : Admin} (h : Typing.adminHead a = "ARRAY.NEW_DEFAULT") :
    ∃ x, a = .plain (.arrayNewDefault x) := by
  revert h
  admin_head_inv

/-- **`Step_read` 72 (`array.new_default`), backward, under `ReadValidS`.** -/
theorem bwdS_arrayNewDefault : ∀ (c : Config H) (w : Value), ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 72 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have XI := R4Fwd.expandInv_builtins (prof := P) hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayNewDefault hf)
  have hρ := valsOnly_bindVals σ
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨VAL, fval, -⟩ := hq "val" State.valT (by simp)
  obtain ⟨ZT, fzt, -⟩ := hq "zt" (.varT "storagetype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.NEW_DEFAULT" X]]) := by
    concl_inv hl
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₁
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, rfl⟩ := head_arrayNewDefault (Typing.adminToV_case h₂).symm
  have eX : X = Encode.toValue x := by
    injection h₂ with _ h
    exact h.symm
  subst eX hZ
  obtain ⟨d, m, zt, hd, hexp, hdef⟩ := hv.seg.2.1
  obtain ⟨v₀, hv₀⟩ := Option.isSome_iff_exists.1 hdef
  obtain ⟨w', hw', hD⟩ := RefsGC.premW_rule (hp _ List.mem_cons_self)
  have eZT : ZT = tyV zt := EvalExp.unique (evalExp_var fzt)
    (R4Fwd.zt_of_expand XI hρ hd hexp (evalExp_var fz) (evalExp_var fx) hw' hD)
  subst eZT
  have hdefv : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "default_" [.expA (.callE "unpack" [.expA (.varE "zt")])]) (.opt (some (valV v₀))) :=
    Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (Equiv.evalArgs_cons (Vec.evalExp_call (Aggregates.findDef_none hρ _)
        (Vec.evalArgs_var fzt Equiv.evalArgs_nil) (R4Fwd.applies_unpack_any zt)) Equiv.evalArgs_nil)
      (FwdSimdAgg.applies_default_closed zt.unpack hv₀)
  have eVAL : Value.opt (some (valV v₀)) = .opt (some VAL) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) hdefv
      (evalExp_optE_some_iff.2 ⟨_, evalExp_var fval, rfl⟩)
  obtain rfl : VAL = valV v₀ := by simpa using eVAL.symm
  have hw : w = .list (List.replicate n.toNat (valV v₀) ++ [.case "ARRAY.NEW_FIXED"
      (.tuple [Encode.toValue x, .case "%" (.tuple [.num (.natN n.toNat)])])]) :=
    EvalExp.unique (RefsGC.rhs_of_concl he) (evalExp_cat
      (Vec.evalExp_iterListN_nodom (evalExp_var fn) (RefsGC.evalExp_sub_of (evalExp_var fval)))
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_case
        (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var fn) evalExps_nil, rfl⟩))))))
  have hs : Step P host ⟨s, f, [constI32 n, .plain (.arrayNewDefault x)]⟩
      ⟨s, f, vals (List.replicate n.toNat v₀) ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩ :=
    .aggregate (.arrayNewDefault hd hexp hv₀)
  refine ⟨_, ?_, hs⟩
  rw [hw, adminsToV_append, adminsToV_vals, List.map_replicate]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Read
