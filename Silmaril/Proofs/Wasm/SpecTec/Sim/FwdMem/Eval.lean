module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.Typing
public import Silmaril.Wasm.SpecTec.Sim.State.Thms

/-!
# Evaluating `$with_mem` and slices

`$with_mem(z, x, i, j, b*) = $sof(z)[.MEMS[$fof(z).MODULE.MEMS[x!%.0]].BYTES[i : j] = b*]; $fof(z)`
(`Original.d611`): one premise-free clause, evaluated by `evalExp_withMem` through a slice update
(`pathSet_slice`). `WithMemDef` is the environment fact, proved for every `simEnv B`
(`withMemDef_simEnv`). `sliceAt_of_lt`/`sliceAt_of_total` give the slice and slice update the
load and store rules need, under the evaluator's strict bound or under `SliceTotal`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open State (HasClause1 iterVar modAddr idxV StateDefs)

/-- The body of `$with_mem`'s clause. -/
abbrev withMemBody : Exp :=
  .caseE "%;%" (.tupE [.updE (.callE "sof" [.expA (.varE "z")])
      (.sliceP (.dotP (.idxP (.dotP .rootP "MEMS") (modAddr "MEMS")) "BYTES") (.varE "i")
        (.varE "j"))
      (iterVar "b" "b*"),
    .callE "fof" [.expA (.varE "z")]])

/-- The argument patterns of `$with_mem`'s clause. -/
abbrev withMemPats : List Arg :=
  [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "i"), .expA (.varE "j"),
    .expA (iterVar "b" "b*")]

/-- `$with_mem` has one premise-free clause. -/
def WithMemDef (env : Env) : Prop := HasClause1 env "with_mem" withMemPats withMemBody

set_option maxRecDepth 100000 in
theorem withMemDef_baseEnv : WithMemDef baseEnv := ⟨_, _, _, rfl⟩

theorem withMemDef_simEnv (B : Builtins) : WithMemDef (simEnv B) :=
  withMemDef_baseEnv.withBuiltins B

/-- Writing a slice through a path. -/
theorem pathSet_slice {env : Env} {ρ : VarEnv} {v u u' w r : Value} {p : Path} {e₁ e₂ : Exp}
    {i k : Nat} (hg : PathGet env ρ v p u) (h₁ : EvalExp env ρ e₁ (.num (.natN i)))
    (h₂ : EvalExp env ρ e₂ (.num (.natN k))) (hs : u.setSlice i k w = some u')
    (hr : PathSet env ρ v p u' r) : PathSet env ρ v (.sliceP p e₁ e₂) w r := by
  obtain ⟨n₁, hg⟩ := hg
  obtain ⟨n₂, h₁⟩ := h₁
  obtain ⟨n₃, h₂⟩ := h₂
  obtain ⟨n₄, hr⟩ := hr
  refine ⟨max (max n₁ n₂) (max n₃ n₄) + 1, ?_⟩
  simp only [pathSet, pathGet_ok_of_le (show n₁ ≤ max (max n₁ n₂) (max n₃ n₄) by omega) hg,
    Bind.bind, Except.bind, evalExp_ok_of_le (show n₂ ≤ max (max n₁ n₂) (max n₃ n₄) by omega) h₁,
    evalExp_ok_of_le (show n₃ ≤ max (max n₁ n₂) (max n₃ n₄) by omega) h₂, Value.asNat?,
    Res.ofOption, hs, pathSet_ok_of_le (show n₄ ≤ max (max n₁ n₂) (max n₃ n₄) by omega) hr]

section WithMem

variable {env : Env} (D : StateDefs env) (W : WithMemDef env) {ρ : VarEnv} {S F : Value}
  {n : Nat}
include D W

/-- `$with_mem(z, x, i, j, b*)`: the slice `[i : j]` of the `BYTES` of the memory the module
lists at `n` becomes `b*`. -/
theorem evalExp_withMem {ez ex ei ej eb : Exp} {M m m' u S' : Value} {Ls As bs ws : List Value}
    {a i j : Nat} (hρ : ρ.findDef? "with_mem" = none) (hz : EvalExp env ρ ez (stV S F))
    (hx : EvalExp env ρ ex (idxV n)) (hi : EvalExp env ρ ei (.num (.natN i)))
    (hj : EvalExp env ρ ej (.num (.natN j))) (hb : EvalExp env ρ eb (.list ws))
    (hS : S.field? "MEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "MEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hm : Ls[a]? = some m) (hB : m.field? "BYTES" = some (.list bs))
    (hsl : Value.setSlice (.list bs) i j (.list ws) = some u)
    (hm' : m.setField "BYTES" u = some m')
    (hS' : S.setField "MEMS" (.list (Ls.set a m')) = some S') :
    EvalExp env ρ (.callE "with_mem" [.expA ez, .expA ex, .expA ei, .expA ej, .expA eb])
      (stV S' F) := by
  refine State.evalExp_call1 W hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hi (evalArgs_cons hj
      (evalArgs_cons hb evalArgs_nil)))))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA
          (State.matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil))))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (State.evalExp_fof D rfl (evalExp_var rfl)))
  let ρ₁ := ((((VarEnv.empty.bindVal "z" (stV S F)).bindVal "x" (idxV n)).bindVal "i"
    (.num (.natN i))).bindVal "j" (.num (.natN j))).bindVal "b*" (.list ws)
  have hidx : EvalExp env ρ₁ (modAddr "MEMS") (.num (.natN a)) :=
    State.evalExp_modAddr D rfl rfl rfl hM hA ha
  have ha' : a < Ls.length := (List.getElem?_eq_some_iff.1 hm).1
  have hg : PathGet env ρ₁ S (.idxP (.dotP .rootP "MEMS") (modAddr "MEMS")) m :=
    State.pathGet_idx (State.pathGet_dot State.pathGet_root hS) hidx hm
  refine evalExp_updE_iff.2 ⟨S, .list ws, State.evalExp_sof D rfl (evalExp_var rfl),
    Equiv.Execution.evalExp_iterPat (by decide) rfl, ?_⟩
  exact pathSet_slice (State.pathGet_dot hg hB) (evalExp_var rfl) (evalExp_var rfl) hsl
    (State.pathSet_dot hg hm' (State.pathSet_idx (State.pathGet_dot State.pathGet_root hS) hidx
      (by simp [Value.setIdx, ha']) (State.pathSet_dot State.pathGet_root hS'
        State.pathSet_root)))

end WithMem

/-! ## Slices -/

/-- The slice `vs[i : n]` the load rules read, as the evaluator computes it. -/
def SliceAt (vs : List Value) (i n : Nat) : Prop :=
  Value.slice? (.list vs) i n = some (.list ((vs.drop i).take n)) ∧
    ∀ ws : List Value, Value.setSlice (.list vs) i n (.list ws) =
      some (.list (vs.take i ++ ws ++ vs.drop (i + n)))

/-- Under the evaluator's strict bound. -/
theorem sliceAt_of_lt {vs : List Value} {i n : Nat} (h : i + n < vs.length) : SliceAt vs i n :=
  ⟨by simp [Value.slice?, h.le], fun _ => by simp [Value.setSlice, h.le]⟩

/-- Under `SliceTotal` (upstream item U2), up to the end of the list. -/
theorem sliceAt_of_total (hT : SliceTotal) {vs : List Value} {i n : Nat}
    (h : i + n ≤ vs.length) : SliceAt vs i n :=
  ⟨hT.1 vs i n h, fun ws => hT.2 vs ws i n h⟩

end Silmaril.Wasm.SpecTec.Sim.FwdMem
