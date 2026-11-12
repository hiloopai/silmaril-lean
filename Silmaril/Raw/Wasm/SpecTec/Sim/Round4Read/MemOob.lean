module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.MemFill

/-!
# Track r4-read: `Step_read/memory.size` (52), `memory.copy-oob` (56), `memory.init-oob` (60),
backward, under validity

Round 3 found all three false without a hypothesis the target lacked:

* `memory.size`: SpecTec's result `CONST at (% n)` carries the exact page count `n` with
  `n · 64 Ki = |BYTES|`, Core's `BitVec.ofNat _ (|bytes| / 64 Ki)`. The store bounds
  (`ReadValid.store`) keep `|bytes| < 2 ^ 32`, so the two agree.
* `memory.copy-oob`, `memory.init-oob`: the premise `A \/ B` short-circuits, so when `A` holds the
  second memory (resp. data segment) is never looked up, while Core's `copyOob`/`initOob` look
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
open BwdRead (cfg_inv adminsToV_eq_quad decode_aconst NoAcc)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

variable (B : Builtins)

/-- `p * q` on natural numerals, read back from its second operand. -/
theorem mul_nat_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {q : Nat} {v : Value}
    (h₂ : EvalExp env ρ e₂ (.num (.natN q)))
    (h : EvalExp env ρ (.binE .mulOp (.numT .natT) e₁ e₂) v) :
    ∃ p, EvalExp env ρ e₁ (.num (.natN p)) ∧ v = .num (.natN (p * q)) := by
  obtain ⟨v₁, h₁', hs | ⟨-, v₂, h₂', hb⟩⟩ := evalExp_binE_iff.1 h
  · simp [boolShort] at hs
  · have e₂ : v₂ = .num (.natN q) := EvalExp.unique h₂' h₂
    subst e₂
    cases v₁ with
    | num m =>
      cases m <;> simp [binValues, Num.bin, Res.ofOption] at hb
      exact ⟨_, h₁', hb.symm⟩
    | _ => simp [binValues] at hb

variable (NA : NoAcc B)

include NA in

/-- **`Step_read` 52 (`memory.size`), backward, under the store bounds.** -/
theorem bwdV_memorySize : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 52 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memorySize hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨LIM, fl, -⟩ := hq "lim" (.varT "limits" []) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "MEMORY.SIZE" X]]) ∧
      w = .list [.case "CONST" (.tuple [AT, .case "%" (.tuple [N])])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single hcode
  obtain ⟨x, rfl, rfl⟩ := decode_memorySize ha
  subst hZ
  have h₁ := ifPrem (hp _ List.mem_cons_self)
  obtain ⟨v₁, v₂, e₁, e₂, -⟩ := evalExp_cmpE_iff.1 h₁
  obtain ⟨ma, mi, hm, rfl⟩ := BwdRead.memLen_inv B NA rfl fz fx e₂
  obtain ⟨p, ep, rfl⟩ := mul_nat_inv (RefsGC.evalExp_mulNat RefsGC.evalExp_num'
    (Memory.kiOk_simEnv B σ)) e₁
  have hpv : p * (64 * 1024) = mi.bytes.size := by
    have := RefsGC.eq_of_evalExp_eq h₁ e₁ e₂
    simpa using this
  have eN : N = .num (.natN p) := EvalExp.unique (evalExp_var fn) ep
  have h₂ := ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨T, -, eT, -, -⟩ := evalExp_cmpE_iff.1 h₂
  obtain ⟨T₀, hT₀, hTT⟩ := evalExp_dotE_iff.1 eT
  obtain ⟨ma', mi', hm', rfl⟩ := BwdRead.mem_inv B NA rfl fz fx hT₀
  rw [hm] at hm'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
  have eAT : AT = Encode.toValue mi.type.address := by
    have hR := RefsGC.eq_of_evalExp_eq h₂ eT (evalExp_case (evalExp_tup2 (evalExp_var fa)
      (evalExp_var fl)))
    have hT : T = .case "%%PAGE" (.tuple [Encode.toValue mi.type.address,
        Encode.toValue mi.type.limits]) := by
      simpa using hTT.symm
    rw [hT] at hR
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hR
    exact hR.1.symm
  have hpages : mi.pages = p := by
    rw [MemInst.pages, ← hpv]
    exact Nat.mul_div_cancel _ (by decide)
  have hlt : p < 2 ^ mi.type.address.intType.width := by
    have := mem_lt32 hv.store hm
    exact lt_width (by omega)
  refine ⟨[aconst mi.type.address (BitVec.ofNat _ mi.pages)], ?_, .memory (.size hm)⟩
  rw [hc.2, eAT, eN]
  simp only [adminsToV, State.adminToV_aconst, hpages, Memory.toNat_ofNat_of_lt hlt]

/-- **`Step_read` 56 (`memory.copy-oob`), backward, under validity.** -/
theorem bwdV_memoryCopyOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 56 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memoryCopyOob hf)
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
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "MEMORY.COPY" (.tuple [X₁, X₂])]])
      ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x₁, x₂, rfl, hX⟩ := decode_memoryCopy h₄
  obtain ⟨rfl, rfl⟩ := Value.tuple.inj hX |> fun h => (List.cons.inj h).imp id
    (fun h => (List.cons.inj h).1)
  obtain ⟨t₁, b₁, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT₁
  obtain ⟨t₂, b₂, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₂ hAT₂
  obtain ⟨t', b', rfl, rfl, hN⟩ := decode_aconst h₃
  have eN : N = .num (.natN b'.toNat) := by simpa using hN
  subst eN hZ
  obtain ⟨ix₁, ix₂⟩ := idx_last4 hv (c := ⟨s, f, is⟩) his
  obtain ⟨ma₁, mi₁, ht₁⟩ := mem_of_isSome ix₁
  obtain ⟨ma₂, mi₂, ht₂⟩ := mem_of_isSome ix₂
  have hoob := Memory.or_true (ifPrem (hp _ List.mem_cons_self))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi₁)) (evalExp_var fn))
    (evalExp_memLen' B fz fx₁ ht₁)
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi₂)) (evalExp_var fn))
    (evalExp_memLen' B fz fx₂ ht₂)
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  rw [his]
  exact .memory (.copyOob ht₁ ht₂ hoob)

/-- **`Step_read` 60 (`memory.init-oob`), backward, under validity.** -/
theorem bwdV_memoryInitOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 60 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memoryInitOob hf)
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
      .case "MEMORY.INIT" (.tuple [X, Y])]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x, y, rfl, hXY⟩ := decode_memoryInit h₄
  obtain ⟨rfl, rfl⟩ := Value.tuple.inj hXY |> fun h => (List.cons.inj h).imp id
    (fun h => (List.cons.inj h).1)
  obtain ⟨t, b, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₃
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN hZ
  obtain ⟨ix, iy⟩ := idx_last4 hv (c := ⟨s, f, is⟩) his
  obtain ⟨ma, mi, ht⟩ := mem_of_isSome ix
  obtain ⟨da, di, hdi⟩ := data_of_isSome iy
  have hoob := Memory.or_true (ifPrem (hp _ List.mem_cons_self))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi)) (evalExp_var fn))
    (evalExp_memLen' B fz fx ht)
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fj)) (evalExp_var fn))
    (evalExp_dataLen' B fz fy hdi)
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  rw [his]
  exact .memory (.initOob (i := b) (j := j) (n := n) ht hdi hoob)

end Silmaril.Wasm.SpecTec.Sim.Round4Read
