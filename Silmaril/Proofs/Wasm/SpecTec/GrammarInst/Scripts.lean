module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Least
public import Silmaril.Wasm.SpecTec.Broken.Thms
public import Silmaril.Wasm.SpecTec.Versions.Thms

/-!
# SpecTec scripts in the institution of grammars

* `gramRelSup` is consequence in the script's grammar theory (`gramRelSup_iff_entails`), and the
  intended model `leastModel (gramOf env)` is the least model of that theory
  (`scriptLeastModel_sat`, `scriptLeastModel_le`).
* The grammar defects of `Silmaril.Wasm.SpecTec.Broken` and `…Versions`, recast as
  (non-)entailment: #803 (`BsN(32)` loses `FF 7E`) on the original, fixed and main wasm-3.0
  theories; #654 (`Bi32` unsigned) as a sentence the original theory entails and the fixed and
  main theories do not, so the erratum is not a theory morphism along the identity.
* silmaril-lean's hand-written LEB128 relations as theories interpreted in a script's theory:
  `UN` exactly (`entails_bun_iff_un`, `unInterp`), `SN` exactly on its non-negative and one-byte
  part (`entails_bsn_iff_sn`, `snInterp`), and not beyond (`not_interprets_sn`); and the
  framework's hand-written grammar `lebGram` has the same `BuN` consequences
  (`entails_lebGram_iff`).
-/

public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open CategoryTheory
open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.Wasm.Binary
open Silmaril.Wasm.SpecTec.Scripts

/-! ## `gramRelSup` is consequence; `gramOf` is the least model -/

/-- **`gramRelSup` is semantic consequence in the script's grammar theory.** -/
theorem gramRelSup_iff_entails (env : Env) (ρ : VarEnv) (g : IL.Sym) (bs : Bytes) (v : Value) :
    gramRelSup env ρ g bs v ↔ Entails (scriptAxioms env) (derivesSym env g ρ bs v) := by
  have h : Entails (scriptAxioms env) (derivesSym env g ρ bs v) ↔
      ∃ a, Grammar.denote (gramOf env) (transSym env g) bs a ∧ ∃ ρ', a ρ [v] ρ' :=
    entails_derives_iff actAlg (prodsOf env env) (transSym env g) bs _
  rw [h]
  constructor
  · rintro ⟨a, ρ', ha, hv⟩
    exact ⟨a, ha, ρ', hv⟩
  · rintro ⟨a, ha, ρ', hv⟩
    exact ⟨a, ρ', ha, hv⟩

/-- The same at a nonterminal, where the sentence does not depend on the script. -/
theorem gramRelSup_varG_iff_entails (env : Env) (ρ : VarEnv) (x : IL.Id) (args : List IL.Arg)
    (bs : Bytes) (v : Value) :
    gramRelSup env ρ (.varG x args) bs v ↔ Entails (scriptAxioms env) (derivesNT x args ρ bs v) :=
  gramRelSup_iff_entails env ρ (.varG x args) bs v

/-- The script's least model satisfies its grammar theory. -/
theorem scriptLeastModel_sat (env : Env) :
    ∀ φ ∈ scriptAxioms env, (room actAlg NT).Sat (leastModel (gramOf env)) φ :=
  leastModel_sat actAlg (prodsOf env env)

/-- …and lies below every model of it. -/
theorem scriptLeastModel_le (env : Env) (M : Model NT Act)
    (hM : ∀ φ ∈ scriptAxioms env, (room actAlg NT).Sat M φ) (n : NT) :
    (leastModel (gramOf env)).rel n ≤ M.rel n :=
  leastModel_le actAlg (prodsOf env env) M hM n

/-- `gramRelSup` at a nonterminal reads the least model. -/
theorem gramRelSup_varG_iff_leastModel (env : Env) (ρ : VarEnv) (x : IL.Id)
    (args : List IL.Arg) (bs : Bytes) (v : Value) :
    gramRelSup env ρ (.varG x args) bs v ↔
      ∃ a ρ', (leastModel (gramOf env)).rel (x, args) bs a ∧ a ρ [v] ρ' :=
  Iff.rfl

/-- Consequences of the binary (or any) fragment are consequences of the whole script. -/
theorem entails_of_binary {env : Env} {φ : Sen NT Act} (h : Entails (binaryAxioms env) φ) :
    Entails (scriptAxioms env) φ :=
  entails_mono (prodAxiomsWhere_subset _ _) h

/-- Consequences of the text fragment are consequences of the whole script. -/
theorem entails_of_text {env : Env} {φ : Sen NT Act} (h : Entails (textAxioms env) φ) :
    Entails (scriptAxioms env) φ :=
  entails_mono (prodAxiomsWhere_subset _ _) h

/-! ## Defects as (non-)entailment -/

/-- The argument list `(32)`. -/
abbrev arg32 : List IL.Arg := [.expA (.numE (.natN 32))]

/-- **#803 in the original wasm-3.0 theory**: `FF 7E ∉ BsN(32)`, as a non-consequence. -/
theorem bsn_FF7E_not_entailed_original (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "BsN" arg32 ρ [0xFF, 0x7E] v) :=
  fun h => Broken.bsnLosesFF7E_original ρ v ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **#803 in the fixed wasm-3.0 theory**: no erratum addresses it. -/
theorem bsn_FF7E_not_entailed_fixed (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Wasm30.envFixed) (derivesNT "BsN" arg32 ρ [0xFF, 0x7E] v) :=
  fun h => Broken.bsnLosesFF7E_fixed ρ v ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **#803 in the main wasm-3.0 theory** (`WebAssembly/spec@e7a9df7c`). -/
theorem bsn_FF7E_not_entailed_main (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Versions.Main.Wasm30.env) (derivesNT "BsN" arg32 ρ [0xFF, 0x7E] v) :=
  fun h => Versions.bsnLosesFF7E_main ρ v ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **#654 in the original theory**: the unsigned `Bi32` derives `FF 7E` as `16255`. -/
theorem bi32_FF7E_entailed_original (ρ : VarEnv) :
    Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "Bi32" [] ρ [0xFF, 0x7E] (uNV 16255)) :=
  (gramRelSup_varG_iff_entails ..).mp
    ((Broken.bi32Unsigned_original ρ _ _).mpr ⟨16255, Broken.u32_FF7E, rfl⟩)

/-- **#654 repaired**: the fixed `Bi32` derives nothing from `FF 7E` (that it derives nothing
at all is #803). -/
theorem bi32_FF7E_not_entailed_fixed (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Wasm30.envFixed) (derivesNT "Bi32" [] ρ [0xFF, 0x7E] v) :=
  fun h => Broken.not_bi32_FF7E Broken.hasLeb_fixed Broken.hasSignedLeb_fixed
    Broken.hasCorrectedBi_fixed ρ v ((gramRelSup_varG_iff_entails ..).mpr h)

/-- The same on main. -/
theorem bi32_FF7E_not_entailed_main (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Versions.Main.Wasm30.env) (derivesNT "Bi32" [] ρ [0xFF, 0x7E] v) :=
  fun h => Versions.not_bi32_FF7E_main ρ v ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **The errata are a patch, not an extension**: the fixed wasm-3.0 theory does not entail
every production of the original, so the identity renaming is not a theory morphism from the
original theory to the fixed one. The witness is #654's `Bi32 ⊢ FF 7E ↦ 16255`. -/
theorem fixed_not_entails_original :
    ¬ ∀ ψ ∈ scriptAxioms Wasm30.envOriginal, Entails (scriptAxioms Wasm30.envFixed) ψ :=
  not_entailsAll_of_separates (bi32_FF7E_entailed_original VarEnv.empty)
    (bi32_FF7E_not_entailed_fixed VarEnv.empty _)

/-- The same for main against the pin. -/
theorem main_not_entails_original :
    ¬ ∀ ψ ∈ scriptAxioms Wasm30.envOriginal, Entails (scriptAxioms Versions.Main.Wasm30.env) ψ :=
  not_entailsAll_of_separates (bi32_FF7E_entailed_original VarEnv.empty)
    (bi32_FF7E_not_entailed_main VarEnv.empty _)

/-! ## silmaril-lean's hand-written LEB128 relations as interpreted theories -/

/-- The argument list `(W)`. -/
abbrev argW (W : Nat) : List IL.Arg := [.expA (.numE (.natN W))]

/-- **`BuN(W)`'s consequences are exactly the hand-written `UN W`**, in every script with the
pinned LEB128 grammar. -/
theorem entails_bun_iff_un {env : Env} (hl : HasLeb env) (W : Nat) (ρ : VarEnv) (bs : Bytes)
    (v : Value) :
    Entails (scriptAxioms env) (derivesNT "BuN" (argW W) ρ bs v) ↔
      ∃ m, UN W bs m ∧ v = numCase m :=
  (gramRelSup_varG_iff_entails ..).symm.trans (bun_iff_un hl W bs v ρ)

/-- **`BsN(W)`'s consequences are the hand-written `SN W`, on non-negative values and single
bytes**, and only there (#803). -/
theorem entails_bsn_iff_sn {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env) (W : Nat)
    (hW : 0 < W) (ρ : VarEnv) (bs : Bytes) (v : Value) :
    Entails (scriptAxioms env) (derivesNT "BsN" (argW W) ρ bs v) ↔
      ∃ i, SN W bs i ∧ (0 ≤ i ∨ bs.length = 1) ∧ v = sNV i :=
  (gramRelSup_varG_iff_entails ..).symm.trans (bsn_iff_sn hl hs W hW bs v ρ)

/-- The theory of the hand-written unsigned LEB128 relation: every `UN` fact, as a `BuN`
derivability assertion. -/
def unTheory : Set (Sen NT Act) :=
  {φ | ∃ W bs m ρ, UN W bs m ∧ φ = derivesNT "BuN" (argW W) ρ bs (numCase m)}

/-- The theory of the hand-written signed LEB128 relation at width `W`, optionally restricted
to the part #803 leaves intact. -/
def snTheory (W : Nat) (restricted : Bool) : Set (Sen NT Act) :=
  {φ | ∃ bs i ρ, SN W bs i ∧ (restricted → 0 ≤ i ∨ bs.length = 1) ∧
    φ = derivesNT "BsN" (argW W) ρ bs (sNV i)}

/-- The script's theory entails all of `UN`'s theory. -/
theorem entails_unTheory {env : Env} (hl : HasLeb env) :
    ∀ φ ∈ unTheory, Entails (scriptAxioms env) φ := by
  rintro φ ⟨W, bs, m, ρ, hm, rfl⟩
  exact (entails_bun_iff_un hl W ρ bs _).mpr ⟨m, hm, rfl⟩

/-- The script's theory entails the restricted `SN` theory. -/
theorem entails_snTheory_restricted {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env)
    (W : Nat) (hW : 0 < W) : ∀ φ ∈ snTheory W true, Entails (scriptAxioms env) φ := by
  rintro φ ⟨bs, i, ρ, hi, hc, rfl⟩
  exact (entails_bsn_iff_sn hl hs W hW ρ bs _).mpr ⟨i, hi, hc rfl, rfl⟩

/-- **…but not the full `SN` theory**: `SN 32 (FF 7E) (-129)` is a hand-written fact that no
script with the pinned `BsN` entails (#803). -/
theorem not_interprets_sn {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env) :
    ¬ ∀ φ ∈ snTheory 32 false, Entails (scriptAxioms env) φ := by
  intro h
  have hφ : derivesNT "BsN" (argW 32) VarEnv.empty [0xFF, 0x7E] (sNV (-129)) ∈ snTheory 32 false :=
    ⟨[0xFF, 0x7E], -129, VarEnv.empty, sn32_FF7E, fun h => absurd h (by decide), rfl⟩
  have hd : gramRelSup env VarEnv.empty (.varG "BsN" (argW 32)) [0xFF, 0x7E] (sNV (-129)) :=
    (gramRelSup_varG_iff_entails ..).mpr (h _ hφ)
  exact not_bsn_FF7E hl hs VarEnv.empty _ hd

/-- A set of sentences entailed by a script's theory is a specification morphism along the
identity: a theory interpretation in the institution of grammars. -/
def interpOfEntails (env : Env) (Γ : Set (Sen NT Act))
    (h : ∀ φ ∈ Γ, Entails (scriptAxioms env) φ) :
    (⟨scriptSig env, Γ⟩ : Spec (functor actAlg Decl)) ⟶
      ⟨scriptSig env, scriptAxioms env⟩ where
  sig := 𝟙 _
  mapsTo φ hφ := by
    rw [(functor actAlg Decl).map_id]
    exact h φ hφ

/-- **silmaril-lean's `UN` is interpreted in every script with the pinned `BuN`.** -/
def unInterp {env : Env} (hl : HasLeb env) :
    (⟨scriptSig env, unTheory⟩ : Spec (functor actAlg Decl)) ⟶
      ⟨scriptSig env, scriptAxioms env⟩ :=
  interpOfEntails env unTheory (entails_unTheory hl)

/-- **silmaril-lean's `SN`, restricted to what #803 leaves, is interpreted likewise.** -/
def snInterp {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env) (W : Nat) (hW : 0 < W) :
    (⟨scriptSig env, snTheory W true⟩ : Spec (functor actAlg Decl)) ⟶
      ⟨scriptSig env, scriptAxioms env⟩ :=
  interpOfEntails env (snTheory W true) (entails_snTheory_restricted hl hs W hW)

/-- **The framework's hand-written `lebGram` and a script's `BuN` have the same consequences**,
across two instances of the institution (attributes `List Nat` and `Sem.Act`). -/
theorem entails_lebGram_iff {env : Env} (hl : HasLeb env) (W : Nat) (ρ : VarEnv) (bs : Bytes)
    (m : Nat) :
    (room Grammar.lebAlg Nat).Entails (prodAxioms Grammar.lebProds)
        (.derives (.nt W) bs (· = [m])) ↔
      Entails (scriptAxioms env) (derivesNT "BuN" (argW W) ρ bs (numCase m)) := by
  have hleb : (room Grammar.lebAlg Nat).Entails (prodAxioms Grammar.lebProds)
      (.derives (.nt W) bs (· = [m])) ↔ Grammar.denote Grammar.lebGram (.nt W) bs [m] := by
    rw [entails_derives_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro ha
      exact ⟨[m], ha, rfl⟩
  rw [hleb, ← gramRelSup_varG_iff_entails]
  exact (bun_iff_lebGram hl W bs m ρ).symm

/-! ## The LEB128 grammars across all versions

The wasm-1.0 and wasm-2.0 scripts, pinned, fixed and on main, carry the same `Bbyte`, `BuN`,
`BsN` and `BiN` as the pinned wasm-3.0 script (checked by `rfl` against the generated terms), so
the interpretations and #803 hold in every one of the nine grammar theories. -/

section Versions

set_option maxRecDepth 100000

theorem hasLeb_wasm10_original : HasLeb Wasm10.envOriginal := ⟨by rfl, by rfl⟩
theorem hasLeb_wasm10_fixed : HasLeb Wasm10.envFixed := ⟨by rfl, by rfl⟩
theorem hasLeb_wasm20_original : HasLeb Wasm20.envOriginal := ⟨by rfl, by rfl⟩
theorem hasLeb_wasm20_fixed : HasLeb Wasm20.envFixed := ⟨by rfl, by rfl⟩
theorem hasLeb_main10 : HasLeb Versions.Main.Wasm10.env := ⟨by rfl, by rfl⟩
theorem hasLeb_main20 : HasLeb Versions.Main.Wasm20.env := ⟨by rfl, by rfl⟩

theorem hasSignedLeb_wasm10_original : HasSignedLeb Wasm10.envOriginal := ⟨by rfl, by rfl⟩
theorem hasSignedLeb_wasm10_fixed : HasSignedLeb Wasm10.envFixed := ⟨by rfl, by rfl⟩
theorem hasSignedLeb_wasm20_original : HasSignedLeb Wasm20.envOriginal := ⟨by rfl, by rfl⟩
theorem hasSignedLeb_wasm20_fixed : HasSignedLeb Wasm20.envFixed := ⟨by rfl, by rfl⟩
theorem hasSignedLeb_main10 : HasSignedLeb Versions.Main.Wasm10.env := ⟨by rfl, by rfl⟩
theorem hasSignedLeb_main20 : HasSignedLeb Versions.Main.Wasm20.env := ⟨by rfl, by rfl⟩

end Versions

/-- The nine grammar theories: wasm-1.0, 2.0 and 3.0, each pinned, fixed and on main. -/
@[expose] def NineEnvs (env : Env) : Prop :=
  env = Wasm10.envOriginal ∨ env = Wasm10.envFixed ∨ env = Versions.Main.Wasm10.env ∨
    env = Wasm20.envOriginal ∨ env = Wasm20.envFixed ∨ env = Versions.Main.Wasm20.env ∨
    env = Wasm30.envOriginal ∨ env = Wasm30.envFixed ∨ env = Versions.Main.Wasm30.env

set_option maxRecDepth 100000 in
/-- All nine theories have the pinned LEB128 grammars. -/
theorem lebs_nineEnvs : ∀ env, NineEnvs env → HasLeb env ∧ HasSignedLeb env := by
  intro env h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hasLeb_wasm10_original, hasSignedLeb_wasm10_original⟩
  · exact ⟨hasLeb_wasm10_fixed, hasSignedLeb_wasm10_fixed⟩
  · exact ⟨hasLeb_main10, hasSignedLeb_main10⟩
  · exact ⟨hasLeb_wasm20_original, hasSignedLeb_wasm20_original⟩
  · exact ⟨hasLeb_wasm20_fixed, hasSignedLeb_wasm20_fixed⟩
  · exact ⟨hasLeb_main20, hasSignedLeb_main20⟩
  · exact ⟨Broken.hasLeb_original, Broken.hasSignedLeb_original⟩
  · exact ⟨Broken.hasLeb_fixed, Broken.hasSignedLeb_fixed⟩
  · exact ⟨Versions.hasLeb_main, Versions.hasSignedLeb_main⟩

/-- **In all nine theories**, `UN` and the restricted `SN 32` are interpreted, the full `SN 32`
is not, and `BsN(32)` derives nothing from `FF 7E` (#803). -/
theorem nineEnvs_leb :
    ∀ env, NineEnvs env →
      (∀ φ ∈ unTheory, Entails (scriptAxioms env) φ) ∧
      (∀ φ ∈ snTheory 32 true, Entails (scriptAxioms env) φ) ∧
      (¬ ∀ φ ∈ snTheory 32 false, Entails (scriptAxioms env) φ) ∧
      (∀ ρ v, ¬ Entails (scriptAxioms env) (derivesNT "BsN" arg32 ρ [0xFF, 0x7E] v)) := by
  intro env h
  obtain ⟨hl, hs⟩ := lebs_nineEnvs env h
  exact ⟨entails_unTheory hl, entails_snTheory_restricted hl hs 32 (by decide),
    not_interprets_sn hl hs,
    fun ρ v he => not_bsn_FF7E hl hs ρ v ((gramRelSup_varG_iff_entails ..).mpr he)⟩

end Silmaril.Wasm.SpecTec.GrammarInst
