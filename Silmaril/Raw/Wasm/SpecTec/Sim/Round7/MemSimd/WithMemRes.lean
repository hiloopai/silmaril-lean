module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.StateF
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.MemSimd.WithMem

/-!
# Round 7, memory SIMD: an evaluating `$with_mem` resolves its memory (unrefined)

`withMem_resolvesF`: if `$with_mem(z, x, i, j, b*)` evaluates at `z = stateVF F s f`, then the
frame resolves `x` to a memory of the store (`Store.mem?`). It is the first half of the inversion
chain of `withMem_bound'` (round 5's `BwdStep.withMem_bound`), which assumes the resolution
instead. The vector store rules of `Step` use it to recover the memory from a firing rule.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (idxV)

variable {B : Builtins} {H : Type} {F : Value}

/-- **An evaluating `$with_mem` call resolves its memory**, for any `B` that does not interpret
`$with_mem`. -/
theorem withMem_resolvesF (hwm : ∀ ws, B.call "with_mem" ws = none) {ρ : VarEnv} (hρ : ValsOnly ρ)
    {s : Store H} {f : Frame} {x : MemIdx} {ei ej eb : Exp} {W : Value} {i j : Nat}
    {ws : List Value}
    (fz : ρ.findVal? "z" = some (stateVF F s f)) (fx : ρ.findVal? "x" = some (idxV x.toNat))
    (hi : EvalExp (simEnv B) ρ ei (.num (.natN i)))
    (hj : EvalExp (simEnv B) ρ ej (.num (.natN j))) (hb : EvalExp (simEnv B) ρ eb (.list ws))
    (h : EvalExp (simEnv B) ρ
      (.callE "with_mem" [.expA (.varE "z"), .expA (.varE "x"), .expA ei, .expA ej, .expA eb]) W) :
    ∃ ma mi, s.mem? f x = some (ma, mi) := by
  have D := State.stateDefs_simEnv B
  have hbody := BwdPureStep.evalExp_call1_inv (FwdMem.withMemDef_simEnv _)
    (Prims.findDef_none_of_valsOnly hρ _) (hwm _)
    (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fx)
      (Equiv.evalArgs_cons hi (Equiv.evalArgs_cons hj (Equiv.evalArgs_cons hb
        Equiv.evalArgs_nil)))))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA
          (State.matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil))))) h
  obtain ⟨W₁, W₂, h₁, -, -⟩ := BwdPureStep.body_pair hbody
  obtain ⟨S, Wb, hS, -, hps⟩ := evalExp_updE_iff.1 h₁
  have eS : S = storeVF F s := EvalExp.unique hS (State.evalExp_sof D rfl (evalExp_var rfl))
  subst eS
  obtain ⟨u, v₁, v₂, i', k', u', hu, -, -, -, -, -, -⟩ := Round5.BwdStep.pathSet_slice_inv hps
  obtain ⟨u₀, hu₀, -⟩ := BwdPureStep.pathGet_dot_inv hu
  obtain ⟨L, iv, a, hL, hiv, ha, hLa⟩ := BwdPureStep.pathGet_idx_inv hu₀
  obtain ⟨R, hR, hRf⟩ := BwdPureStep.pathGet_dot_inv hL
  have eR := BwdPureStep.pathGet_root_inv hR
  subst eR
  rw [storeVF_MEMS, Option.some.injEq] at hRf
  subst hRf
  obtain ⟨ma, hma, rfl⟩ := moduleIdx_invF D rfl rfl rfl (State.moduleV_MEMS _) hiv
  simp only [Value.asNat?, Option.some.injEq] at ha
  subst ha
  simp only [Value.idx?, List.getElem?_map] at hLa
  obtain ⟨mi, hmi, -⟩ := Option.map_eq_some_iff.1 hLa
  exact ⟨ma, mi, by simp [Store.mem?, hma, hmi]⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
