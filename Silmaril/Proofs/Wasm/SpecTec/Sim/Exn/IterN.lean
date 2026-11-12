module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.Backward

/-!
# Family X: inverting counted iterations

`evalExp_iterN_inv`: an iteration `x^m` over one domain `y`, whose body reads `x` back,
evaluates only to the list `y` is bound to, with `m` bound to its length. `try_table` (`val^m`,
`t_1^m`, `t_2^n`) and `throw` (`val^n`, `t^n`) need it for the backward direction.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

variable {env : Env}

/-- A variable evaluated with explicit fuel. -/
theorem evalExp_varE_ok {n : Nat} {ρ : VarEnv} {y : IL.Id} {v : Value}
    (h : evalExp n env ρ (.varE y) = .ok v) : ρ.findVal? y = some v :=
  evalExp_varE_iff.1 ⟨n, h⟩

/-- One domain `x ← y`, evaluated. -/
theorem evalDoms_one {n : Nat} {ρ : VarEnv} {x y : IL.Id} {xvs : List (IL.Id × Value)}
    (h : evalDoms n env ρ [.mk x (.varE y)] = .ok xvs) :
    ∃ yv, ρ.findVal? y = some yv ∧ xvs = [(x, yv)] := by
  cases n with
  | zero => simp [evalDoms] at h
  | succ n =>
      simp only [evalDoms, List.mapM_cons, List.mapM_nil, domVar, domSrc] at h
      cases hy : evalExp n env ρ (.varE y) with
      | error e => simp [hy] at h
      | ok yv =>
          simp [hy] at h
          exact ⟨yv, evalExp_varE_ok hy, h.symm⟩

/-- Rounds of a body that reads `x` back return the domain. -/
theorem evalRounds_var_inv {n : Nat} {ρ : VarEnv} {b : Exp} {x : IL.Id}
    (hb : ∀ (σ : VarEnv) (w u : Value), σ.findVal? x = some w → EvalExp env σ b u → u = w)
    (hx : x ≠ "_") :
    ∀ (ws us : List Value), (ws.map fun w => [(x, w)]).mapM
      (fun r => evalExp n env (ρ.bindVals r) b) = .ok us → us = ws
  | [], us, h => (Except.ok.inj h).symm
  | w :: ws, us, h => by
      simp only [List.map_cons, List.mapM_cons, Res.bind_eq_ok] at h
      obtain ⟨u, hu, us', hus, hres⟩ := h
      have e₀ : us = u :: us' := (Except.ok.inj hres).symm
      have e₁ : u = w := hb _ w u
        (by simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx]) ⟨n, hu⟩
      rw [e₀, e₁, evalRounds_var_inv hb hx ws us' hus]

/-- A numeral read back. -/
theorem asNat?_eq_some {kv : Value} {k : Nat} (h : kv.asNat? = some k) : kv = .num (.natN k) := by
  cases kv with
  | num m => cases m <;> simp_all [Value.asNat?]
  | _ => simp [Value.asNat?] at h

/-- The counted body of an iteration over one domain whose body reads `x` back. -/
theorem evalIterList_one_inv {n k : Nat} {ρ : VarEnv} {b : Exp} {x : IL.Id} {yv v : Value}
    (hb : ∀ (σ : VarEnv) (w u : Value), σ.findVal? x = some w → EvalExp env σ b u → u = w)
    (hx : x ≠ "_") (h : evalIterList n env ρ b [(x, yv)] none k = .ok v) :
    ∃ l, yv = .list l ∧ l.length = k ∧ v = .list l := by
  cases n with
  | zero => simp [evalIterList] at h
  | succ n =>
      rw [evalIterList] at h
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_cons,
        List.mapM_nil] at h
      obtain ⟨ds, hds, hall, us, hus, hres⟩ := h
      obtain ⟨l, rfl⟩ : ∃ l, yv = .list l := by
        cases yv <;> simp [Value.asList?] at hds ⊢
      have hds' : ds = [(x, l)] := by simpa [Value.asList?] using hds.symm
      have hkl : l.length = k := by simpa [hds'] using hall
      have hrows : evalRounds n env ρ b (l.map fun w => [(x, w)]) = .ok us := by
        rw [← Equiv.Execution.iterRows_singleton, hkl, ← hds']
        exact hus
      have hul : us = l := by
        cases n with
        | zero => simp [evalRounds] at hrows
        | succ n => exact evalRounds_var_inv hb hx l us (by rw [evalRounds] at hrows; exact hrows)
      exact ⟨l, rfl, hkl, by rw [← hul]; exact (Except.ok.inj hres).symm⟩

/-- `x^m` over one domain `y`, inverted: `y` is bound to the result, `m` to its length. -/
theorem evalExp_iterN_inv {ρ : VarEnv} {b : Exp} {x y m : IL.Id} {v : Value}
    (hb : ∀ (σ : VarEnv) (w u : Value), σ.findVal? x = some w → EvalExp env σ b u → u = w)
    (hx : x ≠ "_")
    (h : EvalExp env ρ (.iterE b (.mk (.listN (.varE m) none) [.mk x (.varE y)])) v) :
    ∃ vs, ρ.findVal? y = some (.list vs) ∧ ρ.findVal? m = some (.num (.natN vs.length)) ∧
      v = .list vs := by
  obtain ⟨n, hn⟩ := evalExp_iterE_iff.1 h
  cases n with
  | zero => simp [evalIterE] at hn
  | succ n =>
      rw [evalIterE] at hn
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
      obtain ⟨xvs, hdoms, kv, hkv, k, hk, hlist⟩ := hn
      obtain ⟨yv, fy, rfl⟩ := evalDoms_one hdoms
      obtain ⟨l, rfl, rfl, rfl⟩ := evalIterList_one_inv hb hx hlist
      exact ⟨l, fy, by rw [← asNat?_eq_some hk]; exact evalExp_varE_ok hkv, rfl⟩

/-- `val^m` (`valsNPat`), inverted. -/
theorem evalExp_valsNPat_inv {ρ : VarEnv} {x y m : IL.Id} {v : Value} (hx : x ≠ "_")
    (h : EvalExp env ρ (Equiv.Execution.valsNPat x y m) v) :
    ∃ vs, ρ.findVal? y = some (.list vs) ∧ ρ.findVal? m = some (.num (.natN vs.length)) ∧
      v = .list vs :=
  evalExp_iterN_inv (fun _ w u hw hu => by
    rw [evalExp_subE_iff, evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm) hx h

/-- `x^m` with a plain variable body, inverted. -/
theorem evalExp_varN_inv {ρ : VarEnv} {x y m : IL.Id} {v : Value} (hx : x ≠ "_")
    (h : EvalExp env ρ (.iterE (.varE x) (.mk (.listN (.varE m) none) [.mk x (.varE y)])) v) :
    ∃ vs, ρ.findVal? y = some (.list vs) ∧ ρ.findVal? m = some (.num (.natN vs.length)) ∧
      v = .list vs :=
  evalExp_iterN_inv (fun _ w u hw hu => by
    rw [evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm) hx h

end Silmaril.Wasm.SpecTec.Sim.Exn
