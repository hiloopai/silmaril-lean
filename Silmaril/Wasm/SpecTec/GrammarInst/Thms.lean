module

public import Silmaril.Wasm.SpecTec.GrammarInst.Defs
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Least
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Scripts
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Reverse
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Hom
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.LebHom
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Fragment
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Closed
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Locality
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Errata
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Separate
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.SeparateBinary
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.TextEscape
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.TextReserved
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.TextTypeuse
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.BmoduleDead
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.SegmentsV2
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.BfuncBound
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.BfuncLarge

/-!
# The institution of SpecTec grammars: headline theorems

* `inst A D` is an institution (`Silmaril.Wasm.SpecTec.GrammarInst.Defs`); its satisfaction
  condition is `Sen.holds_rename`.
* The theory of a grammar has `Grammar.denote` as least model, so derivability is consequence
  (`entails_derives_iff`); for SpecTec scripts, `gramRelSup` is consequence in the script's
  grammar theory (`gramRelSup_iff_entails`).
* Errata and defects as (non-)entailment, and silmaril-lean's hand-written LEB128 relations as
  theory interpretations (`Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Scripts`).
* #654 in reverse: the fixed theory entails `Bi32 ⊢ 7F ↦ -1` and the original does not, so the
  original and fixed wasm-3.0 theories are incomparable (`wasm30_errata_incomparable`,
  `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Reverse`).
* Attribute-algebra homomorphisms translate grammars conservatively (`entails_map_iff`) and induce
  a comorphism of the sub-institutions of derivability assertions (`obsCoHom`,
  `obsCoHom_conservative`); `lebHom : lebAlg → actAlg` is an instance
  (`Silmaril.Proofs.Wasm.SpecTec.GrammarInst.{Hom,LebHom}`).
* The binary and text fragments of all nine scripts are closed, so each script is a
  conservative extension of each fragment (`nineEnvs_fragments_closed`, `entails_binary_iff`,
  `entails_text_iff`; `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.{Fragment,Closed}`).
* Errata locality: the wasm-3.0 errata change the production table only at their thirteen
  targets (`errata_locality`, `entails_local_iff`, `bsn_errata_local`;
  `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Locality`); the same for the text §6.x errata alone
  and the wasm-1.0 and 2.0 errata, together with the fact that each changes every one of its
  grammar targets (`errata_grammar_theories`, `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Errata`).
* Separating sentences for the text errata: the pinned `Tfloat`/`Thexfloat` derive only strings
  with an exponent marker (#662, `wasm30_float_exponent_mandatory`); the text-patched theory
  entails `Tfloat ⊢ 0 ↦ 0` and the pinned one entails `Talign_(4) ⊢ ε ↦ %(4)`, each not the
  other (`text6x_errata_incomparable`, `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Separate`).
* Separating sentences for the wasm-1.0 errata at `Binstr ⊢ BB` (#686,
  `wasm10_errata_incomparable`) and for the wasm-2.0 errata at `Binstr ⊢ FD 5C 00 00` and
  `Binstr ⊢ FD 5D 00 00` (#670, `wasm20_errata_incomparable`;
  `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.SeparateBinary`).
* The other text errata (pass 4): #661 separates (`tstringchar_E000_text6x`,
  `tstringchar_E000_not_pinned`); #665, #692 and #664 cannot, since their targets derive nothing
  over bytes before and after the patch (`blockcomment_dead_pinned`, `texporttabledots_dead`,
  `ttypeuse_dead_pinned`, from the arity and scope criteria of
  `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Dead`); #694 cannot, since the pinned and patched
  `Treserved` read the same bytes (`treserved_entails_iff`).
* The other wasm-1.0/2.0 grammar errata (pass 4): #690 separates at `Belem` and `Bdata`
  (`belem_80_fixed`, `bdata_80_fixed`) and #671 at `Belem` (`belem_kind6_fixed`); #687 and #672
  cannot, since `Bmodule` derives nothing in any of the four theories (`bmodule_not_entailed`,
  an unbound `func*`); for #688 the corrected `Bfunc` bounds its locals (`bfunc_fixed_bound`)
  and the pinned one derives `2^32` locals from `02 FF FF FF FF 0F 7F 01 7F 0B`
  (`bfunc688PinnedLarge`, which proves `Task.bfunc688PinnedLarge`), so #688 separates
  (`bfunc688_separates`).

See `docs/projects/spectec/README.md`.
-/

public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

/-- **Grammar defects as consequence in the wasm-3.0 grammar theories.** #803: `BsN(32)` derives
nothing from `FF 7E` in the original, fixed and main theories. #654: the original theory derives
`FF 7E` as the `Bi32` value `16255`, the fixed and main theories do not, so neither later
theory entails the original one. -/
theorem wasm30_grammar_defects :
    (∀ ρ v, ¬ Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "BsN" arg32 ρ [0xFF, 0x7E] v) ∧
      ¬ Entails (scriptAxioms Wasm30.envFixed) (derivesNT "BsN" arg32 ρ [0xFF, 0x7E] v) ∧
      ¬ Entails (scriptAxioms Versions.Main.Wasm30.env)
        (derivesNT "BsN" arg32 ρ [0xFF, 0x7E] v)) ∧
    (∀ ρ, Entails (scriptAxioms Wasm30.envOriginal)
      (derivesNT "Bi32" [] ρ [0xFF, 0x7E] (Equiv.uNV 16255))) ∧
    (∀ ρ v, ¬ Entails (scriptAxioms Wasm30.envFixed) (derivesNT "Bi32" [] ρ [0xFF, 0x7E] v) ∧
      ¬ Entails (scriptAxioms Versions.Main.Wasm30.env)
        (derivesNT "Bi32" [] ρ [0xFF, 0x7E] v)) ∧
    (¬ ∀ ψ ∈ scriptAxioms Wasm30.envOriginal, Entails (scriptAxioms Wasm30.envFixed) ψ) ∧
    (¬ ∀ ψ ∈ scriptAxioms Wasm30.envOriginal,
      Entails (scriptAxioms Versions.Main.Wasm30.env) ψ) :=
  ⟨fun ρ v => ⟨bsn_FF7E_not_entailed_original ρ v, bsn_FF7E_not_entailed_fixed ρ v,
      bsn_FF7E_not_entailed_main ρ v⟩,
    bi32_FF7E_entailed_original,
    fun ρ v => ⟨bi32_FF7E_not_entailed_fixed ρ v, bi32_FF7E_not_entailed_main ρ v⟩,
    fixed_not_entails_original, main_not_entails_original⟩

/-- A dead nonterminal of the pinned script, in the `Scripts` environment. -/
theorem not_entails_original_of_dead {x : IL.Id} {args : List IL.Arg}
    (h : ∀ {ρ ρ' : Silmaril.SpecTec.Sem.VarEnv} {bs : Grammar.Bytes} {l : List Value},
      ¬ SymDerives Equiv.Text.envPinned ρ (.varG x args) bs l ρ')
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    ¬ Entails (scriptAxioms Wasm30.envOriginal) (derivesNT x args ρ bs v) := by
  rw [envOriginal_eq_pinned]
  exact not_entails_of_dead h ρ bs v

/-- **The remaining text-format errata in the byte grammar institution** (pass 4). #661
separates the pinned and the text-patched wasm-3.0 theories. #665 (`Tblockcomment`,
`Tblockchar`), #692 (`Texporttabledots_`) and #664 (`Ttypeuse_`) cannot: neither theory entails
any sentence about those targets. #694 (`Treserved`) cannot either: the two theories entail the
same `Treserved` sentences as soon as their `Tstring`s read the same bytes. -/
theorem text6x_remaining_errata :
    (∀ ρ, Entails (scriptAxioms envText6x) (derivesNT "Tstringchar" [] ρ escE000 (numCase 57344)) ∧
      ¬ Entails (scriptAxioms Wasm30.envOriginal)
        (derivesNT "Tstringchar" [] ρ escE000 (numCase 57344))) ∧
    (∀ x ∈ ["Tblockcomment", "Tblockchar"], ∀ ρ bs v,
      ¬ Entails (scriptAxioms Wasm30.envOriginal) (derivesNT x [] ρ bs v) ∧
        ¬ Entails (scriptAxioms envText6x) (derivesNT x [] ρ bs v)) ∧
    (∀ x ∈ ["Texporttabledots_", "Ttypeuse_"], ∀ args ρ bs v,
      ¬ Entails (scriptAxioms Wasm30.envOriginal) (derivesNT x args ρ bs v) ∧
        ¬ Entails (scriptAxioms envText6x) (derivesNT x args ρ bs v)) ∧
    ((∀ bs, (∃ w, gramRelSup Equiv.Text.envPinned VarEnv.empty (.varG "Tstring" []) bs w) ↔
        ∃ w, gramRelSup envText6x VarEnv.empty (.varG "Tstring" []) bs w) →
      ∀ ρ bs v, (Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "Treserved" [] ρ bs v) ↔
        Entails (scriptAxioms envText6x) (derivesNT "Treserved" [] ρ bs v))) := by
  refine ⟨fun ρ => ⟨tstringchar_E000_text6x ρ, tstringchar_E000_not_pinned ρ⟩, ?_, ?_,
    fun hst => treserved_entails_iff hst⟩
  · intro x hx ρ bs v
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨not_entails_original_of_dead blockcomment_dead_pinned.1 ρ bs v,
        not_entails_of_dead blockcomment_dead_text6x.1 ρ bs v⟩
    · exact ⟨not_entails_original_of_dead blockcomment_dead_pinned.2 ρ bs v,
        not_entails_of_dead blockcomment_dead_text6x.2 ρ bs v⟩
  · intro x hx args ρ bs v
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨not_entails_original_of_dead texporttabledots_dead.1 ρ bs v,
        not_entails_of_dead texporttabledots_dead.2 ρ bs v⟩
    · exact ⟨not_entails_original_of_dead ttypeuse_dead_pinned ρ bs v,
        not_entails_of_dead ttypeuse_dead_text6x ρ bs v⟩

/-- **The remaining wasm-1.0 and wasm-2.0 grammar errata in the byte grammar institution**
(pass 4). #690 separates at `Belem` and `Bdata` (index `80 00`), #671 at `Belem` (kind 6 with
`externref`); for #687 and #672 neither theory entails anything about `Bmodule`. -/
theorem binary_remaining_errata :
    (∀ ρ, Entails (scriptAxioms Wasm10.envFixed)
        (derivesNT "Belem" [] ρ seg80 (.case "ELEM" (.tuple [.list [], .list []]))) ∧
      ∀ v, ¬ Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Belem" [] ρ seg80 v)) ∧
    (∀ ρ, Entails (scriptAxioms Wasm10.envFixed)
        (derivesNT "Bdata" [] ρ seg80 (.case "DATA" (.tuple [.list [], .list []]))) ∧
      ∀ v, ¬ Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Bdata" [] ρ seg80 v)) ∧
    (∀ ρ, Entails (scriptAxioms Wasm20.envFixed) (derivesNT "Belem" [] ρ kind6Bytes kind6Target) ∧
      ¬ Entails (scriptAxioms Wasm20.envOriginal) (derivesNT "Belem" [] ρ kind6Bytes kind6Target)) ∧
    (∀ ρ bs v,
      ¬ Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Bmodule" [] ρ bs v) ∧
      ¬ Entails (scriptAxioms Wasm10.envFixed) (derivesNT "Bmodule" [] ρ bs v) ∧
      ¬ Entails (scriptAxioms Wasm20.envOriginal) (derivesNT "Bmodule" [] ρ bs v) ∧
      ¬ Entails (scriptAxioms Wasm20.envFixed) (derivesNT "Bmodule" [] ρ bs v)) :=
  ⟨fun ρ => ⟨belem_80_fixed ρ, belem_80_not_original ρ⟩,
    fun ρ => ⟨bdata_80_fixed ρ, bdata_80_not_original ρ⟩,
    fun ρ => ⟨belem_kind6_fixed ρ, belem_kind6_not_original ρ⟩, bmodule_not_entailed⟩

end Silmaril.Wasm.SpecTec.GrammarInst

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.GrammarInst.text6x_remaining_errata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.SpecTec.GrammarInst.text6x_remaining_errata

/-- info: 'Silmaril.Wasm.SpecTec.GrammarInst.binary_remaining_errata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.SpecTec.GrammarInst.binary_remaining_errata

/-- info: 'Silmaril.Wasm.SpecTec.GrammarInst.bfunc688_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.SpecTec.GrammarInst.bfunc688_separates
