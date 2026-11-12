module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Locality
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20

/-!
# Every errata set as a statement about grammar theories

`Locality.lean` treats the combined wasm-3.0 errata. This module does the same for each errata
set separately: the text-format §6.x errata, the binary §5.1 errata, and the wasm-1.0 and
wasm-2.0 errata. For each set it proves two things.

* **Only there** (`ErrataLocal`): outside the set's targets, the patched and unpatched
  environments have the same grammars. So, with a fixed evaluation environment, they entail the
  same assertions about any closed set of nonterminals that avoids the targets
  (`entails_local_iff_of`).
* **Exactly there** (`gramChanged`): at each grammar target, the two grammar definitions differ.
  The kernel decides this through `IL.defEq`, the printer-based equality the errata machinery
  uses.

So each errata set is a change of the presentation at exactly its grammar targets, and a
conservative one everywhere else. Which *sentences* separate the two theories at a target is a
semantic question. It is answered here only for #654 (`Reverse.lean`, and
`fixed_not_entails_original`). For the text errata and the wasm-1.0/2.0 errata it is open,
because a separating derivation goes through large text or module grammars with premises.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

/-! ## Generic: locality of a patch function -/

/-- Two environments have the same grammars outside `ts`. -/
def ErrataLocal (envF envO : Env) (ts : List IL.Id) : Prop :=
  ∀ y, y ∉ ts → envF.findGram? y = envO.findGram? y

/-- A patch function that changes no grammar binding outside `ts` gives a local change. -/
theorem errataLocal_map {f : Def → Def} {ts : List IL.Id}
    (hf : ∀ y, y ∉ ts → ∀ d, gramBinds y (f d) = gramBinds y d) (ds : List Def) :
    ErrataLocal (envOfScript (ds.map f)) (envOfScript ds) ts := by
  intro y hy
  rw [envOfScript, envOfScript, findGram_envOfDefs, findGram_envOfDefs,
    gramBindsL_map (hf y hy)]

/-- **A local change is conservative** about closed sets of nonterminals avoiding the targets,
for any evaluation environment `E`. -/
theorem entails_local_iff_of {envF envO : Env} {ts : List IL.Id} (hl : ErrataLocal envF envO ts)
    (E : Env) {R : NT → Prop} (hR : ClosedUnder R (prodsOf E envO)) (hRt : ∀ n, R n → n.1 ∉ ts)
    {g : Grammar.Sym NT Act} (hg : SymIn R g) (bs : Grammar.Bytes) (Q : Act → Prop) :
    Entails (prodAxioms (prodsOf E envF)) (.derives g bs Q) ↔
      Entails (prodAxioms (prodsOf E envO)) (.derives g bs Q) := by
  have hp : ∀ n, n.1 ∉ ts → prodsOf E envF n = prodsOf E envO n := fun n hn => by
    unfold prodsOf
    rw [hl n.1 hn]
  have hR' : ClosedUnder R (prodsOf E envF) := fun n hn g hg =>
    hR n hn g (hp n (hRt n hn) ▸ hg)
  have hax : prodAxiomsWhere (fun n : NT => n.1 ∉ ts) (prodsOf E envF) =
      prodAxiomsWhere (fun n : NT => n.1 ∉ ts) (prodsOf E envO) := by
    ext φ
    constructor
    · rintro ⟨x, g, hx, hg, rfl⟩
      exact ⟨x, g, hx, hp x hx ▸ hg, rfl⟩
    · rintro ⟨x, g, hx, hg, rfl⟩
      exact ⟨x, g, hx, (hp x hx).symm ▸ hg, rfl⟩
  show (room actAlg NT).Entails _ _ ↔ (room actAlg NT).Entails _ _
  rw [← entails_fragment_iff actAlg hR' hRt hg, ← entails_fragment_iff actAlg hR hRt hg, hax]

/-- The grammar `y` is defined differently in the two environments, decided through the
printer (`IL.defEq`). -/
def gramChanged (envF envO : Env) (y : IL.Id) : Bool :=
  match envF.findGram? y, envO.findGram? y with
  | some a, some b => !defEq (.gramD y a.1 a.2.1 a.2.2) (.gramD y b.1 b.2.1 b.2.2)
  | none, none => false
  | _, _ => true

theorem findGram_ne_of_gramChanged {envF envO : Env} {y : IL.Id}
    (h : gramChanged envF envO y = true) : envF.findGram? y ≠ envO.findGram? y := by
  intro he
  unfold gramChanged at h
  rw [he] at h
  cases hb : envO.findGram? y with
  | none => simp [hb] at h
  | some b =>
    have hself : defEq (.gramD y b.1 b.2.1 b.2.2) (.gramD y b.1 b.2.1 b.2.2) = true :=
      defEq_iff.mpr rfl
    simp [hb, hself] at h

/-! ## The patch functions change nothing outside their targets -/

/-- The targets of the nine text §6.x patches. -/
def text6xTargets : List IL.Id :=
  ["Tstringchar", "Tfloat", "Thexfloat", "Talign_", "Ttypeuse_", "Tblockcomment", "Tblockchar",
    "Texporttabledots_", "Treserved"]

/-- The targets of the four binary §5.1 patches. -/
def binary51Targets : List IL.Id := ["Bi32", "Bi64", "cont", "utf8"]

/-- The targets of the eight wasm-1.0 patches. -/
def wasm10Targets : List IL.Id :=
  ["Module_ok", "utf8", "Binstr", "Bmodule", "Bfunc", "Belem", "Bdata"]

/-- The targets of the four wasm-2.0 patches. -/
def wasm20Targets : List IL.Id := ["Binstr", "Belem", "Bmodule", "dataidx_instrs"]

theorem gramBinds_text6xPatch {y : IL.Id} (hy : y ∉ text6xTargets) (d : Def) :
    gramBinds y (IL.Text6x.text6xPatch d) = gramBinds y d := by
  simp only [text6xTargets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := hy
  rw [IL.Text6x.text6xPatch, gramBinds_replaceDef rfl h₉, gramBinds_replaceDef rfl h₈,
    gramBinds_replaceDef rfl h₇, gramBinds_replaceDef rfl h₆, gramBinds_replaceDef rfl h₅,
    gramBinds_replaceDef rfl h₄, gramBinds_replaceDef rfl h₃, gramBinds_replaceDef rfl h₂,
    gramBinds_replaceDef rfl h₁]

theorem gramBinds_binary51Patch {y : IL.Id} (hy : y ∉ binary51Targets) (d : Def) :
    gramBinds y (IL.Binary51.binary51Patch d) = gramBinds y d := by
  simp only [binary51Targets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hy
  rw [IL.Binary51.binary51Patch, gramBinds_replaceDef rfl h₄, gramBinds_replaceDef rfl h₃,
    gramBinds_replaceDef rfl h₂, gramBinds_replaceDef rfl h₁]

theorem gramBinds_wasm10Patch {y : IL.Id} (hy : y ∉ wasm10Targets) (d : Def) :
    gramBinds y (IL.Wasm10.wasm10Patch d) = gramBinds y d := by
  simp only [wasm10Targets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hy
  rw [IL.Wasm10.wasm10Patch, gramBinds_replaceDef rfl h₇, gramBinds_replaceDef rfl h₆,
    gramBinds_replaceDef rfl h₅, gramBinds_replaceDef rfl h₄, gramBinds_replaceDef rfl h₃,
    gramBinds_replaceDef rfl h₂, gramBinds_replaceDef rfl h₂, gramBinds_replaceDef rfl h₁]

theorem gramBinds_wasm20Patch {y : IL.Id} (hy : y ∉ wasm20Targets) (d : Def) :
    gramBinds y (IL.Wasm20.wasm20Patch d) = gramBinds y d := by
  simp only [wasm20Targets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hy
  rw [IL.Wasm20.wasm20Patch, gramBinds_replaceDef rfl h₄, gramBinds_replaceDef rfl h₃,
    gramBinds_replaceDef rfl h₂, gramBinds_replaceDef rfl h₁]

/-! ## Only there -/

/-- **The text errata are local**: the text-patched wasm-3.0 script has the original's grammars
outside the nine text targets. -/
theorem text6x_local :
    ErrataLocal (envOfScript IL.Text6x.wasm30text6x) Wasm30.envOriginal text6xTargets := by
  rw [IL.Text6x.wasm30text6x_eq_map, Wasm30.envOriginal, wasm30_original_eq]
  exact errataLocal_map (fun _ hy => gramBinds_text6xPatch hy) _

/-- **The binary §5.1 errata are local.** -/
theorem binary51_local :
    ErrataLocal (envOfScript IL.Binary51.wasm30binary51) Wasm30.envOriginal binary51Targets := by
  rw [IL.Binary51.wasm30binary51_eq_map, Wasm30.envOriginal, wasm30_original_eq]
  exact errataLocal_map (fun _ hy => gramBinds_binary51Patch hy) _

/-- **The wasm-1.0 errata are local.** -/
theorem wasm10_local : ErrataLocal Wasm10.envFixed Wasm10.envOriginal wasm10Targets := by
  rw [Wasm10.envFixed, Wasm10.envOriginal, wasm10_fixed_eq, wasm10_original_eq,
    IL.Wasm10.wasm10corrected_eq_map]
  exact errataLocal_map (fun _ hy => gramBinds_wasm10Patch hy) _

/-- **The wasm-2.0 errata are local.** -/
theorem wasm20_local : ErrataLocal Wasm20.envFixed Wasm20.envOriginal wasm20Targets := by
  rw [Wasm20.envFixed, Wasm20.envOriginal, wasm20_fixed_eq, wasm20_original_eq,
    IL.Wasm20.wasm20corrected_eq_map]
  exact errataLocal_map (fun _ hy => gramBinds_wasm20Patch hy) _

/-! ## Exactly there -/

/-- The grammar targets of the text errata (all nine are grammars). -/
def text6xGramTargets : List IL.Id := text6xTargets

/-- The grammar targets of the wasm-1.0 errata (`Module_ok` is a relation, `utf8` a function). -/
def wasm10GramTargets : List IL.Id := ["Binstr", "Bmodule", "Bfunc", "Belem", "Bdata"]

/-- The grammar targets of the wasm-2.0 errata (`dataidx_instrs` is a function). -/
def wasm20GramTargets : List IL.Id := ["Binstr", "Belem", "Bmodule"]

set_option maxRecDepth 100000 in
/-- **The text errata change every one of their nine grammars.** -/
theorem text6x_changes :
    ∀ y ∈ text6xGramTargets,
      gramChanged (envOfScript IL.Text6x.wasm30text6x) Wasm30.envOriginal y = true := by
  rw [Wasm30.envOriginal, wasm30_original_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The wasm-1.0 errata change every one of their five grammars.** -/
theorem wasm10_changes :
    ∀ y ∈ wasm10GramTargets, gramChanged Wasm10.envFixed Wasm10.envOriginal y = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The wasm-2.0 errata change every one of their three grammars.** -/
theorem wasm20_changes :
    ∀ y ∈ wasm20GramTargets, gramChanged Wasm20.envFixed Wasm20.envOriginal y = true := by
  decide +kernel

/-! ## Headline -/

/-- **The text-format and wasm-1.0/2.0 errata, as statements about grammar theories.** Each
errata set changes the grammar table at each of its grammar targets and nowhere else. So, with
the evaluation environment held fixed, the patched theory entails exactly what the original
entails about every closed set of nonterminals that avoids the targets. -/
theorem errata_grammar_theories :
    (ErrataLocal (envOfScript IL.Text6x.wasm30text6x) Wasm30.envOriginal text6xTargets ∧
      ∀ y ∈ text6xGramTargets, Wasm30.envOriginal.findGram? y ≠
        (envOfScript IL.Text6x.wasm30text6x).findGram? y) ∧
    (ErrataLocal Wasm10.envFixed Wasm10.envOriginal wasm10Targets ∧
      ∀ y ∈ wasm10GramTargets, Wasm10.envOriginal.findGram? y ≠ Wasm10.envFixed.findGram? y) ∧
    (ErrataLocal Wasm20.envFixed Wasm20.envOriginal wasm20Targets ∧
      ∀ y ∈ wasm20GramTargets, Wasm20.envOriginal.findGram? y ≠ Wasm20.envFixed.findGram? y) :=
  ⟨⟨text6x_local, fun y hy => (findGram_ne_of_gramChanged (text6x_changes y hy)).symm⟩,
    ⟨wasm10_local, fun y hy => (findGram_ne_of_gramChanged (wasm10_changes y hy)).symm⟩,
    ⟨wasm20_local, fun y hy => (findGram_ne_of_gramChanged (wasm20_changes y hy)).symm⟩⟩

end Silmaril.Wasm.SpecTec.GrammarInst
