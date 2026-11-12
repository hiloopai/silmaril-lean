module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Scripts

/-!
# #654 in reverse: a sentence the fixed theory entails and the original does not

`fixed_not_entails_original` separates the theories one way: the original wasm-3.0 theory
entails `Bi32 ⊢ FF 7E ↦ 16255`, the fixed theory does not. This module proves the other way.
The fixed `Bi32 = BiN(32)` reads the single byte `7F` as `i32.const -1`. Its value is
`$inv_signed_(32, -1) = 2^32 - 1`, the `iN(32)` bit pattern of `-1`. The original `Bi32 = BuN(32)`
reads `7F` only as `127` (`bi32_pinned_7F_unique`).

The new ingredient is a forward derivation through `BiN`'s production (`bin_of_sn`). It evaluates
`$inv_signed_` with `Equiv.callDef_invSigned`, which needs the script's numerics group
(`Equiv.NumEnv`). That group is checked against the fixed and main scripts by `rfl`.

So the errata are neither an extension nor a restriction of the original grammar theory: each
theory entails a sentence the other does not (`wasm30_errata_incomparable`).
-/

public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.Wasm.Binary
open Silmaril.Wasm.SpecTec.Scripts

/-! ## A forward derivation through `BiN` -/

/-- **`BiN(W)` derives what `BsN(W)` derives, with value `$inv_signed_(W, i)`.** The derivation
needs the same side condition as `bsn_of_sn` (#803), and the bound on `i` that
`$inv_signed_`'s clauses require. -/
theorem bin_of_sn {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env) (hn : NumEnv env)
    {W : Nat} {bs : Grammar.Bytes} {i : Int} (hsn : SN W bs i) (hW : 0 < W)
    (hc : 0 ≤ i ∨ bs.length = 1) (h₁ : -2 ^ (W - 1) ≤ i) (h₂ : i < 2 ^ (W - 1))
    (ρ : VarEnv) :
    SymDerives env ρ (.varG "BiN" [.expA (.numE (.natN W))]) bs
      [uNV (Wasm.Numerics.invSigned_ W i)] ρ := by
  rw [symDerives_varG hs.bin]
  refine ⟨rfl, _, List.mem_singleton.mpr rfl, ?_⟩
  -- The production's scope after binding `N := W` and matching `i` against the `BsN` value.
  let σ : VarEnv := (bunScope W).bindVal "i" (sNV i)
  have hσN : σ.findVal? "N" = some (.num (.natN W)) := rfl
  have hσi : σ.findVal? "i" = some (sNV i) := rfl
  refine ⟨[.val (.num (.natN W))], bunScope W, [sNV i], σ, σ,
    uNV (Wasm.Numerics.invSigned_ W i), evalArgs_expA (evalExp_numE_iff.mpr rfl), rfl,
    ?_, premsHold_nil .., ?_, rfl⟩
  · show SymDerives env (bunScope W) (.attrG (.varE "i") (.varG "BsN" [.expA (.varE "N")]))
      bs [sNV i] σ
    rw [symDerives_attrG]
    exact ⟨sNV i, bunScope W,
      bsn_of_sn hl hs hsn hW hc (bunScope W) _ (evalExp_varE_iff.mpr (findVal_bunScope_N W)),
      rfl, matchExp_varE_of_none rfl⟩
  · have hcall : EvalExp env σ (.callE "inv_signed_"
        [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i") "%") 0)])
        (natV (Wasm.Numerics.invSigned_ W i)) :=
      evalExp_callE_iff.mpr (callDef_invSigned hn rfl
        (evalArgs_cons (evalExp_varE_iff.mpr hσN)
          (evalArgs_cons (evalExp_bsnProj hσi) Equiv.evalArgs_nil)) hW h₁ h₂)
    exact evalExp_caseE_iff.mpr
      ⟨_, evalExp_tupE_iff.mpr ⟨_, evalExps_singleton hcall, rfl⟩, rfl⟩

/-- `7F` is the signed LEB128 encoding of `-1`. -/
theorem sn32_7F : SN 32 [0x7F] (-1) := by
  have h : SN 32 [0x7F] (((0x7F : UInt8).toNat : Int) - 2 ^ 7) :=
    .neg 0x7F (by decide) (by decide) (by decide)
  have e : (((0x7F : UInt8).toNat : Int) - 2 ^ 7) = -1 := by decide
  exact e ▸ h

/-- `$inv_signed_(32, -1)` is the bit pattern of `-1 : BitVec 32`. -/
theorem invSigned_32_minusOne :
    uNV (Wasm.Numerics.invSigned_ 32 (-1)) = iNV (-1 : BitVec 32) := by
  have h : Wasm.Numerics.invSigned_ 32 (-1) = (-1 : BitVec 32).toNat := by decide
  rw [h]
  rfl

/-- **A corrected `Bi32` reads `7F` as `i32.const -1`**, in any script with the pinned LEB128
grammars, the corrected `Bi32` and the pinned numerics. -/
theorem bi32_7F_corrected {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env)
    (hb : HasCorrectedBi env) (hn : NumEnv env) (ρ : VarEnv) :
    gramRelSup env ρ (.varG "Bi32" []) [0x7F] (iNV (-1 : BitVec 32)) := by
  rw [wrap_rel_iff hb.bi32 hs.bin ρ _ _, ← invSigned_32_minusOne]
  exact gramRelSup_iff.mpr ⟨VarEnv.empty, bin_of_sn hl hs hn sn32_7F (by decide)
    (Or.inr rfl) (by decide) (by decide) VarEnv.empty⟩

/-! ## The numerics group of the fixed and main scripts -/

set_option maxRecDepth 100000 in
/-- The fixed wasm-3.0 script has the pinned numerics group (it is `Sim.baseEnv`). -/
theorem numEnv_fixed : NumEnv Wasm30.envFixed :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- So has the main wasm-3.0 script (`WebAssembly/spec@e7a9df7c`). -/
theorem numEnv_main : NumEnv Versions.Main.Wasm30.env :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The reverse separation -/

/-- `iNV (-1)` is not the unsigned `127`. -/
theorem iNV_minusOne_ne : iNV (-1 : BitVec 32) ≠ uNV 127 := by
  intro h
  simp only [uNV, iNV, percentV, Sem.caseV, Value.case.injEq, Value.tuple.injEq,
    Encode.toValue, List.cons.injEq, Value.num.injEq, Num.natN.injEq] at h
  exact absurd h.2.1 (by decide)

/-- **#654 repaired, positively**: the fixed theory entails `Bi32 ⊢ 7F ↦ -1`. -/
theorem bi32_7F_entailed_fixed (ρ : VarEnv) :
    Entails (scriptAxioms Wasm30.envFixed) (derivesNT "Bi32" [] ρ [0x7F] (iNV (-1 : BitVec 32))) :=
  (gramRelSup_varG_iff_entails ..).mp
    (bi32_7F_corrected Broken.hasLeb_fixed Broken.hasSignedLeb_fixed Broken.hasCorrectedBi_fixed
      numEnv_fixed ρ)

/-- The same on main. -/
theorem bi32_7F_entailed_main (ρ : VarEnv) :
    Entails (scriptAxioms Versions.Main.Wasm30.env)
      (derivesNT "Bi32" [] ρ [0x7F] (iNV (-1 : BitVec 32))) :=
  (gramRelSup_varG_iff_entails ..).mp
    (bi32_7F_corrected Versions.hasLeb_main Versions.hasSignedLeb_main Versions.hasCorrectedBi_main
      numEnv_main ρ)

/-- **#654 in the original theory, read in reverse**: the unsigned `Bi32` does not read `7F` as
`-1`. -/
theorem bi32_7F_not_entailed_original (ρ : VarEnv) :
    ¬ Entails (scriptAxioms Wasm30.envOriginal)
      (derivesNT "Bi32" [] ρ [0x7F] (iNV (-1 : BitVec 32))) := fun h =>
  iNV_minusOne_ne (bi32_pinned_7F_unique Broken.hasLeb_original Broken.hasPinnedBi_original ρ _
    ((gramRelSup_varG_iff_entails ..).mpr h))

/-- **The original theory does not entail the fixed one**: the identity is not a theory morphism
fixed → original either. The witness is `Bi32 ⊢ 7F ↦ -1`. -/
theorem original_not_entails_fixed :
    ¬ ∀ ψ ∈ scriptAxioms Wasm30.envFixed, Entails (scriptAxioms Wasm30.envOriginal) ψ :=
  not_entailsAll_of_separates (bi32_7F_entailed_fixed VarEnv.empty)
    (bi32_7F_not_entailed_original VarEnv.empty)

/-- The same for the pin against main. -/
theorem original_not_entails_main :
    ¬ ∀ ψ ∈ scriptAxioms Versions.Main.Wasm30.env, Entails (scriptAxioms Wasm30.envOriginal) ψ :=
  not_entailsAll_of_separates (bi32_7F_entailed_main VarEnv.empty)
    (bi32_7F_not_entailed_original VarEnv.empty)

/-- **The wasm-3.0 errata give an incomparable theory**: neither the original nor the fixed
grammar theory entails the other. -/
theorem wasm30_errata_incomparable :
    (¬ ∀ ψ ∈ scriptAxioms Wasm30.envOriginal, Entails (scriptAxioms Wasm30.envFixed) ψ) ∧
      (¬ ∀ ψ ∈ scriptAxioms Wasm30.envFixed, Entails (scriptAxioms Wasm30.envOriginal) ψ) :=
  ⟨fixed_not_entails_original, original_not_entails_fixed⟩

end Silmaril.Wasm.SpecTec.GrammarInst
