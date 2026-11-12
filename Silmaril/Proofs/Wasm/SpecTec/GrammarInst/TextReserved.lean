module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.TextErrata
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Text

/-!
# #694 in the byte grammar institution: `Treserved` is unchanged

The pinned `Treserved` is `(Tidchar | Tstring | "," | ";" | "[" | "]" | "{" | "}")+`; #694 moves
the six punctuation characters into productions of their own. As elaborated, the run is bound
by the singleton pattern `[x]` (`Equiv/Text.lean`, the singleton-list cast), so the pinned
grammar reads exactly **one** item, and that masks the longest-match defect #694 corrects.

Over bytes the two grammars derive the same thing: one `Tidchar`, one `Tstring` or one of the
six punctuation bytes, always with value `()` (`treserved_pinned_iff`, `treserved_patched_iff`,
both against `ResChar`). Hence `treserved_patch_invisible`: in any two scripts whose `Tidchar`
and `Tstring` derive the same byte strings, the pinned and the patched `Treserved` derive the
same byte strings with the same values. No sentence about `Treserved` separates the #694 patch
in the byte institution; a difference between the full text-patched and pinned theories at
`Treserved` can only come from `Tstring`, i.e. from #661 (`TextEscape.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts
open Silmaril.SpecTec.Equiv.BinaryModule (Rounds symDerives_iterG)
open Silmaril.SpecTec.Equiv (symDerives_seq1)
open Silmaril.SpecTec.Equiv.Text (envPinned envCorrected treservedProds treservedProdsC
  shortProd implicitId unitResult matchExp_listE_var_elim symDerives_textG)

/-! ## The productions -/

/-- The six punctuation alternatives. -/
def punctSyms : List IL.Sym :=
  [.seqG [.textG ","], .seqG [.textG ";"], .seqG [.textG "["], .seqG [.textG "]"],
    .seqG [.textG "{"], .seqG [.textG "}"]]

/-- `Tidchar | Tstring`. -/
def resAlt2 : IL.Sym := .altG [.seqG [.varG "Tidchar" []], .seqG [.varG "Tstring" []]]

/-- The pinned alternative, with the punctuation inside the run. -/
def resAlt8 : IL.Sym := .altG ([.seqG [.varG "Tidchar" []], .seqG [.varG "Tstring" []]] ++ punctSyms)

/-- `A+` bound by the singleton pattern `[x]`, with value `()`. -/
def listProd (A : IL.Sym) : IL.Prod :=
  .prodD [.expP implicitId (.tupT [])] (.attrG (.listE [.varE implicitId]) (.iterG A (.mk .list1 [])))
    unitResult []

/-- The six punctuation bytes. -/
def punctBytes : List Grammar.Bytes := [[0x2C], [0x3B], [0x5B], [0x5D], [0x7B], [0x7D]]

/-- A punctuation production `c => ()` of the patched `Treserved`. -/
def punctProd (c : Nat) : IL.Prod := shortProd (.numT .natT) (.numG c) []

theorem treservedProds_eq : treservedProds = [listProd resAlt8] := rfl

theorem treservedProdsC_eq : treservedProdsC = listProd resAlt2 ::
    [0x2C, 0x3B, 0x5B, 0x5D, 0x7B, 0x7D].map punctProd := rfl

/-- What either `Treserved` reads: one `Tidchar`, one `Tstring`, or one punctuation byte. -/
def ResChar (env : Env) (bs : Grammar.Bytes) : Prop :=
  (∃ w, gramRelSup env VarEnv.empty (.varG "Tidchar" []) bs w) ∨
    (∃ w, gramRelSup env VarEnv.empty (.varG "Tstring" []) bs w) ∨ bs ∈ punctBytes

/-! ## The unit value -/

/-- `unitResult` is `()`, whenever the implicit variable is bound. -/
theorem evalExp_unitResult {env : Env} {ρ : VarEnv} {w : Value}
    (h : ρ.findVal? implicitId = some w) : EvalExp env ρ unitResult (.tuple []) := by
  have ht : EvalExp env ρ (.tupE [.varE implicitId, .tupE []]) (.tuple [w, .tuple []]) :=
    evalExp_tupE_iff.mpr ⟨_, evalExps_cons_iff.mpr ⟨_, _, evalExp_varE_iff.mpr h,
      evalExps_cons_iff.mpr ⟨_, _, evalExp_tupE_iff.mpr ⟨[], evalExps_nil_iff.mpr rfl, rfl⟩,
        evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩
  exact evalExp_projE_iff.mpr ⟨_, ht, by decide, rfl⟩

/-- …and only `()`. -/
theorem evalExp_unitResult_elim {env : Env} {ρ : VarEnv} {v : Value}
    (h : EvalExp env ρ unitResult v) : v = .tuple [] := by
  obtain ⟨vs, ht, -, hv⟩ := evalExp_projE_iff.mp h
  obtain ⟨us, hus, hvs⟩ := evalExp_tupE_iff.mp ht
  obtain ⟨a, as₁, -, has, rfl⟩ := evalExps_cons_iff.mp hus
  obtain ⟨b, bs, hb, hbs, rfl⟩ := evalExps_cons_iff.mp has
  obtain rfl := evalExps_nil_iff.mp hbs
  obtain ⟨cs, hcs, rfl⟩ := evalExp_tupE_iff.mp hb
  obtain rfl := evalExps_nil_iff.mp hcs
  simp only [Value.tuple.injEq] at hvs
  subst hvs
  simpa using hv.symm

/-! ## The run production -/

/-- Matching `[x]` against a one-element list binds `x`. -/
theorem matchExp_listE_single {env : Env} {x : IL.Id} {w : Value}
    (hx : VarEnv.empty.findVal? x = none) :
    MatchExp env VarEnv.empty (.listE [.varE x]) (.list [w]) (VarEnv.empty.bindVal x w) :=
  ⟨3, by simp [matchExp, matchExps, Value.asList?, hx]⟩

/-- The empty scope binds nothing. -/
theorem findVal?_empty (x : IL.Id) : VarEnv.empty.findVal? x = none := rfl

/-- Reading one round of the run, forwards. -/
theorem listProd_of_round {env : Env} {ρ : VarEnv} {A : IL.Sym} {bs : Grammar.Bytes} {w : Value}
    {σ : VarEnv} (hd : SymDerives env VarEnv.empty (substSym [] A) bs [w] σ) :
    ProdDerives env ρ [] [] (listProd A) bs [.tuple []] := by
  have hr : Rounds env VarEnv.empty (substSym [] A) [] (bs ++ []) [(w, [])] := .cons hd rfl .nil
  have hit : SymDerives env VarEnv.empty (.iterG (substSym [] A) (.mk .list1 [])) bs
      [.list [w]] VarEnv.empty := by
    have hc : IterCount env VarEnv.empty .list1 [(w, ([] : List Value))].length := by
      simp [IterCount]
    have h := symDerives_iterG.mpr ⟨[(w, [])], hr, hc, rfl, rfl⟩
    simpa [iterValue] using h
  let σ₁ : VarEnv := VarEnv.empty.bindVal implicitId w
  have hat : SymDerives env VarEnv.empty (.attrG (.listE [.varE implicitId])
      (.iterG (substSym [] A) (.mk .list1 []))) bs [.list [w]] σ₁ :=
    symDerives_attrG.mpr ⟨_, _, hit, rfl, matchExp_listE_single (findVal?_empty _)⟩
  exact ⟨[], VarEnv.empty, _, σ₁, σ₁, _, evalArgs_nil env ρ, rfl, hat, premsHold_nil_iff.mpr rfl,
    evalExp_unitResult rfl, rfl⟩

/-- Reading the run production backwards: exactly one round, and the value `()`. -/
theorem round_of_listProd {env : Env} {ρ : VarEnv} {A : IL.Sym} {bs : Grammar.Bytes}
    {l : List Value} (h : ProdDerives env ρ [] [] (listProd A) bs l) :
    l = [.tuple []] ∧ ∃ w σ, SymDerives env VarEnv.empty (substSym [] A) bs [w] σ := by
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hws, hb, hs, -, hv, rfl⟩ := h
  obtain rfl := evalArgs_nil_iff.mp hws
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hb).symm
  obtain ⟨u, ρ₃, hit, -, hm⟩ := symDerives_attrG.mp hs
  obtain ⟨rows, hr, -, hu, -⟩ := symDerives_iterG.mp hit
  obtain rfl : u = .list (rows.map Prod.fst) := List.singleton_inj.mp hu
  obtain ⟨w, hw⟩ := matchExp_listE_var_elim hm
  refine ⟨by rw [evalExp_unitResult_elim hv], ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, rows = [r] := by
    match rows, hw with
    | [r], _ => exact ⟨r, rfl⟩
  cases hr with
  | cons hd _ ht =>
    cases ht
    exact ⟨_, _, by simpa using hd⟩

/-- **The run production**: it reads exactly what one round of `A` reads, with value `()`. -/
theorem listProd_iff {env : Env} {ρ : VarEnv} {A : IL.Sym} {bs : Grammar.Bytes}
    {l : List Value} :
    ProdDerives env ρ [] [] (listProd A) bs l ↔
      l = [.tuple []] ∧ ∃ w σ, SymDerives env VarEnv.empty (substSym [] A) bs [w] σ := by
  refine ⟨round_of_listProd, ?_⟩
  rintro ⟨rfl, w, σ, hd⟩
  exact listProd_of_round hd

/-- **A punctuation production** reads its byte, with value `()`. -/
theorem punctProd_iff {env : Env} {ρ : VarEnv} {c : Nat} (hc : c < 256) {bs : Grammar.Bytes}
    {l : List Value} :
    ProdDerives env ρ [] [] (punctProd c) bs l ↔ l = [.tuple []] ∧ bs = [UInt8.ofNat c] := by
  constructor
  · rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, hv, rfl⟩
    obtain ⟨u, σ, hn, -, -⟩ := symDerives_attrG.mp hs
    exact ⟨by rw [evalExp_unitResult_elim hv], ((symDerives_numG hc).mp hn).1⟩
  · rintro ⟨rfl, rfl⟩
    have hn : SymDerives env VarEnv.empty (.numG c) [UInt8.ofNat c]
        [.num (.natN (UInt8.ofNat c).toNat)] VarEnv.empty := (symDerives_numG hc).mpr
      ⟨rfl, rfl, rfl⟩
    let σ₁ : VarEnv := VarEnv.empty.bindVal implicitId (.num (.natN (UInt8.ofNat c).toNat))
    exact ⟨[], VarEnv.empty, _, σ₁, σ₁, _, evalArgs_nil env ρ, rfl,
      symDerives_attrG.mpr ⟨_, _, hn, rfl, matchExp_varE_of_none (findVal?_empty _)⟩,
      premsHold_nil_iff.mpr rfl, evalExp_unitResult rfl, rfl⟩

/-! ## The alternatives -/

/-- One value from `[x]`, as `gramRelSup`. -/
theorem exists_seq_varG_iff {env : Env} {x : IL.Id} {bs : Grammar.Bytes} :
    (∃ w σ, SymDerives env VarEnv.empty (.seqG [.varG x []]) bs [w] σ) ↔
      ∃ w, gramRelSup env VarEnv.empty (.varG x []) bs w := by
  simp only [symDerives_seq1, gramRelSup_iff]

/-- **`Tidchar | Tstring`**, with one value. -/
theorem alt2_iff {env : Env} {bs : Grammar.Bytes} :
    (∃ w σ, SymDerives env VarEnv.empty resAlt2 bs [w] σ) ↔
      (∃ w, gramRelSup env VarEnv.empty (.varG "Tidchar" []) bs w) ∨
        (∃ w, gramRelSup env VarEnv.empty (.varG "Tstring" []) bs w) := by
  rw [← exists_seq_varG_iff, ← exists_seq_varG_iff]
  constructor
  · rintro ⟨w, σ, h⟩
    obtain ⟨g, hg, hd⟩ := symDerives_altG.mp h
    rcases List.mem_pair.mp hg with rfl | rfl
    · exact .inl ⟨w, σ, hd⟩
    · exact .inr ⟨w, σ, hd⟩
  · rintro (⟨w, σ, hd⟩ | ⟨w, σ, hd⟩)
    · exact ⟨w, σ, symDerives_altG.mpr ⟨_, by simp, hd⟩⟩
    · exact ⟨w, σ, symDerives_altG.mpr ⟨_, by simp, hd⟩⟩

/-- A one-byte text alternative reads its byte, with one value. -/
theorem punct_mem {env : Env} {t : Text} {c : UInt8} (hg : IL.Sym.seqG [.textG t] ∈ punctSyms)
    (hc : Unicode.utf8 t = [c]) :
    ∃ g ∈ punctSyms, ∃ w σ, SymDerives env VarEnv.empty g [c] [w] σ := by
  have h := symDerives_seq1.mpr (symDerives_textG (env := env) (ρ := VarEnv.empty) (t := t))
  rw [hc] at h
  exact ⟨_, hg, _, _, h⟩

/-- The punctuation alternatives read exactly the six punctuation bytes, with one value. -/
theorem punct_iff {env : Env} {bs : Grammar.Bytes} :
    (∃ g ∈ punctSyms, ∃ w σ, SymDerives env VarEnv.empty g bs [w] σ) ↔ bs ∈ punctBytes := by
  constructor
  · rintro ⟨g, hg, w, σ, hd⟩
    simp only [punctSyms, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [symDerives_textG_bytes (symDerives_seq1.mp hd)]
        decide
  · intro hb
    simp only [punctBytes, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact punct_mem (t := ",") (by simp [punctSyms]) (by decide)
    · exact punct_mem (t := ";") (by simp [punctSyms]) (by decide)
    · exact punct_mem (t := "[") (by simp [punctSyms]) (by decide)
    · exact punct_mem (t := "]") (by simp [punctSyms]) (by decide)
    · exact punct_mem (t := "{") (by simp [punctSyms]) (by decide)
    · exact punct_mem (t := "}") (by simp [punctSyms]) (by decide)

/-- **The pinned alternative is the patched one plus the six punctuation bytes.** -/
theorem alt8_iff {env : Env} {bs : Grammar.Bytes} :
    (∃ w σ, SymDerives env VarEnv.empty resAlt8 bs [w] σ) ↔
      (∃ w σ, SymDerives env VarEnv.empty resAlt2 bs [w] σ) ∨ bs ∈ punctBytes := by
  rw [← punct_iff]
  constructor
  · rintro ⟨w, σ, h⟩
    obtain ⟨g, hg, hd⟩ := symDerives_altG.mp h
    rcases List.mem_append.mp hg with hg | hg
    · exact .inl ⟨w, σ, symDerives_altG.mpr ⟨g, hg, hd⟩⟩
    · exact .inr ⟨g, hg, w, σ, hd⟩
  · rintro (⟨w, σ, h⟩ | ⟨g, hg, w, σ, hd⟩)
    · obtain ⟨g, hg, hd⟩ := symDerives_altG.mp h
      exact ⟨w, σ, symDerives_altG.mpr ⟨g, List.mem_append_left _ hg, hd⟩⟩
    · exact ⟨w, σ, symDerives_altG.mpr ⟨g, List.mem_append_right _ hg, hd⟩⟩

/-! ## `Treserved`, pinned and patched -/

/-- **The pinned `Treserved` over bytes.** -/
theorem treserved_pinned_iff {env : Env}
    (hg : env.findGram? "Treserved" = some ([], .tupT [], treservedProds)) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Treserved" []) bs l ρ' ↔
      ρ' = ρ ∧ l = [.tuple []] ∧ ResChar env bs := by
  rw [symDerives_varG hg, treservedProds_eq]
  simp only [List.mem_singleton, exists_eq_left, listProd_iff]
  rw [show substSym [] resAlt8 = resAlt8 from rfl, alt8_iff, alt2_iff, ResChar, or_assoc]

/-- The six punctuation code points. -/
def punctCodes : List Nat := [0x2C, 0x3B, 0x5B, 0x5D, 0x7B, 0x7D]

/-- The punctuation bytes are the punctuation code points. -/
theorem mem_punctBytes_iff {bs : Grammar.Bytes} :
    bs ∈ punctBytes ↔ ∃ c ∈ punctCodes, bs = [UInt8.ofNat c] := by
  simp only [punctBytes, punctCodes, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left]
  rfl

/-- The patched production list, read off. -/
theorem patched_prods_iff {env : Env} {ρ : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    (∃ p ∈ treservedProdsC, ProdDerives env ρ [] [] p bs l) ↔
      l = [.tuple []] ∧ ResChar env bs := by
  rw [treservedProdsC_eq, ResChar, ← or_assoc, ← alt2_iff, mem_punctBytes_iff]
  constructor
  · rintro ⟨p, hp, hd⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨hl, h⟩ := listProd_iff.mp hd
      exact ⟨hl, .inl h⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
      have hc' : c < 256 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; omega
      obtain ⟨hl, hb⟩ := (punctProd_iff hc').mp hd
      exact ⟨hl, .inr ⟨c, hc, hb⟩⟩
  · rintro ⟨rfl, h | ⟨c, hc, rfl⟩⟩
    · exact ⟨_, List.mem_cons_self .., listProd_iff.mpr ⟨rfl, h⟩⟩
    · have hc' : c < 256 := by
        simp only [punctCodes, List.mem_cons, List.not_mem_nil, or_false] at hc; omega
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_map_of_mem hc),
        (punctProd_iff hc').mpr ⟨rfl, rfl⟩⟩

/-- **The patched `Treserved` over bytes**: the same characterization. -/
theorem treserved_patched_iff {env : Env}
    (hg : env.findGram? "Treserved" = some ([], .tupT [], treservedProdsC)) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env ρ (.varG "Treserved" []) bs l ρ' ↔
      ρ' = ρ ∧ l = [.tuple []] ∧ ResChar env bs := by
  rw [symDerives_varG hg, patched_prods_iff]

/-- **#694 is invisible over bytes.** In any two scripts whose `Tidchar` and `Tstring` read the
same byte strings, the pinned `Treserved` of the first and the patched `Treserved` of the
second derive the same byte strings, with the same values and scopes. -/
theorem treserved_patch_invisible {env₁ env₂ : Env}
    (h₁ : env₁.findGram? "Treserved" = some ([], .tupT [], treservedProds))
    (h₂ : env₂.findGram? "Treserved" = some ([], .tupT [], treservedProdsC))
    (hid : ∀ bs, (∃ w, gramRelSup env₁ VarEnv.empty (.varG "Tidchar" []) bs w) ↔
      ∃ w, gramRelSup env₂ VarEnv.empty (.varG "Tidchar" []) bs w)
    (hst : ∀ bs, (∃ w, gramRelSup env₁ VarEnv.empty (.varG "Tstring" []) bs w) ↔
      ∃ w, gramRelSup env₂ VarEnv.empty (.varG "Tstring" []) bs w)
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    SymDerives env₁ ρ (.varG "Treserved" []) bs l ρ' ↔
      SymDerives env₂ ρ (.varG "Treserved" []) bs l ρ' := by
  rw [treserved_pinned_iff h₁, treserved_patched_iff h₂, ResChar, ResChar, hid, hst]

/-! ## At the pinned and the text-patched scripts -/

open Silmaril.SpecTec.Equiv.Text (IsIdChar textByteRel_iff textByteRel_tidchar_eq_gramRelSup_corrected
  tidchar_text6x_iff utf8Codes_singleton_ascii isAscii_of_isIdChar gramRelSup_tidchar_pinned_iff)

/-- The text-patched `Tidchar` in closed form, as `gramRelSup_tidchar_pinned_iff` has it for the
pinned one. -/
theorem gramRelSup_tidchar_text6x_iff {ρ : VarEnv} {bs : Grammar.Bytes} {v : Value} :
    gramRelSup envText6x ρ (.varG "Tidchar" []) bs v ↔
      ∃ n, IsIdChar n ∧ bs = [UInt8.ofNat n] ∧ v = numCase n := by
  rw [← textByteRel_tidchar_eq_gramRelSup_corrected, textByteRel_iff]
  constructor
  · rintro ⟨cs, rfl, ρ', hder⟩
    obtain ⟨-, n, hn, rfl, rfl⟩ := tidchar_text6x_iff.mp hder
    exact ⟨n, hn, utf8Codes_singleton_ascii (isAscii_of_isIdChar hn), rfl⟩
  · rintro ⟨n, hn, rfl, rfl⟩
    exact ⟨[n], utf8Codes_singleton_ascii (isAscii_of_isIdChar hn), ρ,
      tidchar_text6x_iff.mpr ⟨rfl, n, hn, rfl, rfl⟩⟩

/-- `Tidchar` reads the same byte strings in the pinned and the text-patched scripts. -/
theorem tidchar_pinned_text6x (bs : Grammar.Bytes) :
    (∃ w, gramRelSup envPinned VarEnv.empty (.varG "Tidchar" []) bs w) ↔
      ∃ w, gramRelSup envText6x VarEnv.empty (.varG "Tidchar" []) bs w := by
  simp only [gramRelSup_tidchar_pinned_iff, gramRelSup_tidchar_text6x_iff]

set_option maxRecDepth 100000 in
theorem findGram_treserved_pinned :
    envPinned.findGram? "Treserved" = some ([], .tupT [], treservedProds) := by
  rfl

set_option maxRecDepth 100000 in
theorem findGram_treserved_text6x :
    envText6x.findGram? "Treserved" = some ([], .tupT [], treservedProdsC) := by
  rfl

/-- **#694 in the grammar institution.** The pinned and the text-patched theories entail the
same sentences about `Treserved`, provided their `Tstring`s read the same byte strings — the
only part of `Treserved` another text erratum (#661, through `Tstringchar`) can reach. -/
theorem treserved_entails_iff
    (hst : ∀ bs, (∃ w, gramRelSup envPinned VarEnv.empty (.varG "Tstring" []) bs w) ↔
      ∃ w, gramRelSup envText6x VarEnv.empty (.varG "Tstring" []) bs w)
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "Treserved" [] ρ bs v) ↔
      Entails (scriptAxioms envText6x) (derivesNT "Treserved" [] ρ bs v) := by
  rw [envOriginal_eq_pinned, ← gramRelSup_varG_iff_entails, ← gramRelSup_varG_iff_entails,
    gramRelSup_iff, gramRelSup_iff]
  exact exists_congr fun ρ' => treserved_patch_invisible findGram_treserved_pinned
    findGram_treserved_text6x tidchar_pinned_text6x hst

end Silmaril.Wasm.SpecTec.GrammarInst
