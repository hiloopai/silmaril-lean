module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.VStore
public import Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.Thms

/-!
# Round 7, memory SIMD: `$with_mem` stays inside the memory (unrefined)

`withMem_bound'` is round 5's `BwdStep.withMem_bound` (in `Raw/…/Round5/BwdStep/Store.lean`),
copied and generalised from `simEnv (BI …)` to any `simEnv B` whose `B` does not interpret
`$with_mem`, so that it applies at `withVBytes (Prims.builtins …)`, and (pass 6) from `stateV`
to `stateVF F s f` (any `FUNCS` value), so that it applies at `stateVD`. The proof is the original
one, kept here because it is a long inversion chain.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (idxV)

variable {B : Builtins} {H : Type} {F : Value}

/-- **A `$with_mem` call that evaluates writes inside the memory** (round 5's
`BwdStep.withMem_bound`, for any `B` that does not interpret `$with_mem`). -/
theorem withMem_bound' (hwm : ∀ ws, B.call "with_mem" ws = none) {ρ : VarEnv} (hρ : ValsOnly ρ)
    {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst} {ei ej eb : Exp} {W : Value}
    {i j : Nat} {ws : List Value}
    (fz : ρ.findVal? "z" = some (stateVF F s f)) (fx : ρ.findVal? "x" = some (idxV x.toNat))
    (hm : s.mem? f x = some (ma, mi)) (hi : EvalExp (simEnv B) ρ ei (.num (.natN i)))
    (hj : EvalExp (simEnv B) ρ ej (.num (.natN j))) (hb : EvalExp (simEnv B) ρ eb (.list ws))
    (h : EvalExp (simEnv B) ρ
      (.callE "with_mem" [.expA (.varE "z"), .expA (.varE "x"), .expA ei, .expA ej, .expA eb]) W) :
    i + j ≤ mi.bytes.size := by
  have D := State.stateDefs_simEnv B
  obtain ⟨hma, hmi⟩ := Memory.Store.mem?_eq_some hm
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
  obtain ⟨u, v₁, v₂, i', k', u', hu, hv₁, hv₂, hi', hk', hsl, -⟩ :=
    Round5.BwdStep.pathSet_slice_inv hps
  have e₁ : v₁ = .num (.natN i) := EvalExp.unique hv₁ (evalExp_var rfl)
  have e₂ : v₂ = .num (.natN j) := EvalExp.unique hv₂ (evalExp_var rfl)
  subst e₁ e₂
  simp only [Value.asNat?, Option.some.injEq] at hi' hk'
  subst hi' hk'
  obtain ⟨u₀, hu₀, hB⟩ := BwdPureStep.pathGet_dot_inv hu
  obtain ⟨L, iv, a, hL, hiv, ha, hLa⟩ := BwdPureStep.pathGet_idx_inv hu₀
  obtain ⟨R, hR, hRf⟩ := BwdPureStep.pathGet_dot_inv hL
  have eR := BwdPureStep.pathGet_root_inv hR
  subst eR
  rw [show (storeVF F s).field? "MEMS" = some (.list (s.mems.map Silmaril.SpecTec.Equiv.RuntimeBridge.memInstToValue)) from rfl,
    Option.some.injEq] at hRf
  subst hRf
  have eiv : iv = .num (.natN ma) := EvalExp.unique hiv (State.evalExp_modAddr D rfl rfl rfl
    (State.frameV_MODULE f) (State.moduleV_MEMS _) (State.getElem?_map_natN hma))
  subst eiv
  simp only [Value.asNat?, Option.some.injEq] at ha
  subst ha
  simp only [Value.idx?, List.getElem?_map, hmi, Option.map_some, Option.some.injEq] at hLa
  subst hLa
  rw [FwdMem.memInstV_BYTES', Option.some.injEq] at hB
  subst hB
  have := Round5.BwdStep.le_of_setSlice hsl
  rwa [FwdMem.bytesV_length] at this

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
