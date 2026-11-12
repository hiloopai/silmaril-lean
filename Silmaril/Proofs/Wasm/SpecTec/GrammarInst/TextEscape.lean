module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.TextErrata
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Text

/-!
# #661 in the byte grammar institution: `\u{E000}`

The pinned `Tstringchar` (`6.1-text.values.spectec:98`) reads the escape `\u{n}` only when
`n < 0xD800 ∨ 0xE800 ≤ n < 0x110000`; #661 corrects the second bound to `0xE000`. The escape
production reads only ASCII bytes (`\u{`, hexadecimal digits, `}`), so the byte semantics
reaches it, unlike most of the text format.

* `tstringchar_E000_text6x`: the patched theory entails `Tstringchar ⊢ \u{E000} ↦ %(57344)`,
  through `Thexnum ⊢ E000 ↦ 57344` (`thexnum_E000`).
* `tstringchar_E000_not_pinned`: the pinned theory entails `Tstringchar ⊢ \u{E000} ↦ v` for no
  `v`. Its first production reads a `Tchar` (empty over bytes), the next six are two-byte
  escapes, and the escape production's value fixes `n = 57344`, where the pinned premise is
  false. No uniqueness of `Thexnum` is needed: the value of the sentence determines `n`.
* `text6x_incomparable_661`: so #661 alone already separates the two theories.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts
open Silmaril.SpecTec.Equiv.Text (envPinned envCorrected symDerives_textG)

/-! ## The escape production -/

/-- `n < 0xD800 ∨ B ≤ n < 0x110000`, the premise of the `\u{n}` production, with lower bound
`B` of the second range: `0xE800` pinned, `0xE000` patched. -/
def escCond (B : Nat) : Exp :=
  .binE .orOp .boolT (.cmpE .ltOp (.numT .natT) (.varE "n") (.numE (.natN 55296)))
    (.binE .andOp .boolT (.cmpE .leOp (.numT .natT) (.numE (.natN B)) (.varE "n"))
      (.cmpE .ltOp (.numT .natT) (.varE "n") (.numE (.natN 1114112))))

/-- The body of the `\u{n}` production. -/
def escBody : IL.Sym :=
  .seqG [.seqG [.textG "\\u{"], .seqG [.attrG (.varE "n") (.varG "Thexnum" [])],
    .seqG [.textG "}"]]

/-- The `\u{n}` production of `Tstringchar`. -/
def escProd (B : Nat) : IL.Prod :=
  .prodD [.expP "n" (.varT "n" [])] escBody (.caseE "%" (.tupE [.varE "n"])) [.ifPr (escCond B)]

/-- The shape of `Tstringchar`: a `Tchar` production, the six two-byte escapes, and the
`\u{n}` escape with bound `B`. Values and the first premise are left open. -/
def TstringcharShape (env : Env) (B : Nat) : Prop :=
  ∃ (q₁ : List Param) (e₁ : Exp) (pr₁ : List Prem) (e₂ e₃ e₄ e₅ e₆ e₇ : Exp),
    env.findGram? "Tstringchar" = some ([], .varT "char" [],
      [.prodD q₁ (.attrG (.varE "c") (.varG "Tchar" [])) e₁ pr₁,
        .prodD [] (.textG "\\t") e₂ [], .prodD [] (.textG "\\n") e₃ [],
        .prodD [] (.textG "\\r") e₄ [], .prodD [] (.textG "\\\"") e₅ [],
        .prodD [] (.textG "\\'") e₆ [], .prodD [] (.textG "\\\\") e₇ [], escProd B])

set_option maxRecDepth 100000 in
theorem tstringcharShape_pinned : TstringcharShape envPinned 59392 :=
  ⟨_, _, _, _, _, _, _, _, _, by rfl⟩

set_option maxRecDepth 100000 in
theorem tstringcharShape_text6x : TstringcharShape envText6x 57344 :=
  ⟨_, _, _, _, _, _, _, _, _, by rfl⟩

/-! ## The premise at `n = 57344` -/

/-- A variable bound to a numeral evaluates to it. -/
theorem evalExp_var_num {env : Env} {ρ : VarEnv} {x : IL.Id} {m : Nat}
    (h : ρ.findVal? x = some (.num (.natN m))) : EvalExp env ρ (.varE x) (.num (.natN m)) :=
  evalExp_varE_iff.mpr h

/-- A numeral evaluates to itself. -/
theorem evalExp_nat (env : Env) (ρ : VarEnv) (m : Nat) :
    EvalExp env ρ (.numE (.natN m)) (.num (.natN m)) :=
  evalExp_numE_iff.mpr rfl

/-- **The pinned premise is false at `57344`.** -/
theorem escCond_pinned_false {env : Env} {ρ : VarEnv}
    (h : ρ.findVal? "n" = some (.num (.natN 57344))) :
    EvalExp env ρ (escCond 59392) (.bool false) := by
  have h₁ : EvalExp env ρ (.cmpE .ltOp (.numT .natT) (.varE "n") (.numE (.natN 55296)))
      (.bool false) := evalExp_cmpE_num (evalExp_var_num h) (evalExp_nat env ρ _) rfl
  have h₂ : EvalExp env ρ (.cmpE .leOp (.numT .natT) (.numE (.natN 59392)) (.varE "n"))
      (.bool false) := evalExp_cmpE_num (evalExp_nat env ρ _) (evalExp_var_num h) rfl
  have h₃ : EvalExp env ρ (.binE .andOp .boolT
      (.cmpE .leOp (.numT .natT) (.numE (.natN 59392)) (.varE "n"))
      (.cmpE .ltOp (.numT .natT) (.varE "n") (.numE (.natN 1114112)))) (.bool false) :=
    evalExp_binE_iff.mpr ⟨_, h₂, .inl rfl⟩
  exact evalExp_binE_iff.mpr ⟨_, h₁, .inr ⟨rfl, _, h₃, rfl⟩⟩

/-- **The patched premise is true at `57344`.** -/
theorem escCond_text6x_true {env : Env} {ρ : VarEnv}
    (h : ρ.findVal? "n" = some (.num (.natN 57344))) :
    EvalExp env ρ (escCond 57344) (.bool true) := by
  have h₁ : EvalExp env ρ (.cmpE .ltOp (.numT .natT) (.varE "n") (.numE (.natN 55296)))
      (.bool false) := evalExp_cmpE_num (evalExp_var_num h) (evalExp_nat env ρ _) rfl
  have h₂ : EvalExp env ρ (.cmpE .leOp (.numT .natT) (.numE (.natN 57344)) (.varE "n"))
      (.bool true) := evalExp_cmpE_num (evalExp_nat env ρ _) (evalExp_var_num h) rfl
  have h₃ : EvalExp env ρ (.cmpE .ltOp (.numT .natT) (.varE "n") (.numE (.natN 1114112)))
      (.bool true) := evalExp_cmpE_num (evalExp_var_num h) (evalExp_nat env ρ _) rfl
  have h₄ : EvalExp env ρ (.binE .andOp .boolT
      (.cmpE .leOp (.numT .natT) (.numE (.natN 57344)) (.varE "n"))
      (.cmpE .ltOp (.numT .natT) (.varE "n") (.numE (.natN 1114112)))) (.bool true) :=
    evalExp_binE_iff.mpr ⟨_, h₂, .inr ⟨rfl, _, h₃, rfl⟩⟩
  exact evalExp_binE_iff.mpr ⟨_, h₁, .inr ⟨rfl, _, h₄, rfl⟩⟩

/-! ## `Thexnum ⊢ E000 ↦ 57344` in the patched script -/

/-- `d:Tdigit => d`, the first production of `Thexdigit`. -/
def hexDigitProd : IL.Prod :=
  .prodD [.expP "d" (.numT .natT)] (.attrG (.varE "d") (.varG "Tdigit" [])) (.varE "d") []

/-- A hexadecimal letter `b => v` of `Thexdigit`. -/
def hexLetterProd (b v : Nat) : IL.Prod := .prodD [] (.numG b) (.numE (.natN v)) []

/-- `h:Thexdigit => h`, the first production of `Thexnum`. -/
def hexnum1Prod : IL.Prod :=
  .prodD [.expP "h" (.numT .natT)] (.attrG (.varE "h") (.varG "Thexdigit" [])) (.varE "h") []

/-- The body of the second production of `Thexnum`, `n:Thexnum "_"? h:Thexdigit`. -/
def hexnum2Body : IL.Sym :=
  .seqG [.seqG [.attrG (.varE "n") (.varG "Thexnum" [])],
    .seqG [.iterG (.textG "_") (.mk .opt [])], .seqG [.attrG (.varE "h") (.varG "Thexdigit" [])]]

/-- `16 * n + h`, the value of the second production of `Thexnum`. -/
def hexnum2Value : Exp :=
  .binE .addOp (.numT .natT) (.binE .mulOp (.numT .natT) (.numE (.natN 16)) (.varE "n")) (.varE "h")

/-- The second production of `Thexnum`. -/
def hexnum2Prod : IL.Prod :=
  .prodD [.expP "n" (.varT "n" []), .expP "h" (.numT .natT)] hexnum2Body hexnum2Value []

/-- The grammars a derivation of `Thexnum ⊢ E000` goes through. -/
structure HasHexnum (env : Env) : Prop where
  thexdigit : ∃ r, env.findGram? "Thexdigit" = some ([], .numT .natT,
    hexDigitProd :: hexLetterProd 0x41 10 :: hexLetterProd 0x42 11 :: hexLetterProd 0x43 12 ::
      hexLetterProd 0x44 13 :: hexLetterProd 0x45 14 :: r)
  thexnum : env.findGram? "Thexnum" = some ([], .numT .natT, [hexnum1Prod, hexnum2Prod])

set_option maxRecDepth 100000 in
theorem hasHexnum_text6x : HasHexnum envText6x := ⟨⟨_, by rfl⟩, by rfl⟩

/-- `Thexdigit ⊢ 0 ↦ 0`. -/
theorem thexdigit_0 {env : Env} (hf : HasFloatZero env) (h : HasHexnum env) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Thexdigit" []) [0x30] [.num (.natN 0)] ρ := by
  obtain ⟨r, hg⟩ := h.thexdigit
  have hp : ProdDerives env ρ [] [] hexDigitProd [0x30] [.num (.natN 0)] :=
    ⟨[], VarEnv.empty, _, _, _, _, evalArgs_nil env ρ, rfl,
      symDerives_attrVar rfl (tdigit_0 hf VarEnv.empty), premsHold_nil_iff.mpr rfl,
      evalExp_varE_iff.mpr rfl, rfl⟩
  exact (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩

/-- `Thexdigit ⊢ E ↦ 14`. -/
theorem thexdigit_E {env : Env} (h : HasHexnum env) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Thexdigit" []) [0x45] [.num (.natN 14)] ρ := by
  obtain ⟨r, hg⟩ := h.thexdigit
  have hp : ProdDerives env ρ [] [] (hexLetterProd 0x45 14) [0x45] [.num (.natN 14)] :=
    ⟨[], VarEnv.empty, _, VarEnv.empty, VarEnv.empty, _, evalArgs_nil env ρ, rfl,
      (symDerives_numG (by decide)).mpr ⟨rfl, rfl, rfl⟩, premsHold_nil_iff.mpr rfl,
      evalExp_numE_iff.mpr rfl, rfl⟩
  exact (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩

/-- The value `16 * n + h`. -/
theorem evalExp_hexnum2Value {env : Env} {ρ : VarEnv} {a b : Nat}
    (hn : ρ.findVal? "n" = some (.num (.natN a))) (hh : ρ.findVal? "h" = some (.num (.natN b))) :
    EvalExp env ρ hexnum2Value (.num (.natN (16 * a + b))) := by
  have hm : EvalExp env ρ (.binE .mulOp (.numT .natT) (.numE (.natN 16)) (.varE "n"))
      (.num (.natN (16 * a))) :=
    evalExp_binE_iff.mpr ⟨_, evalExp_nat env ρ 16, .inr ⟨rfl, _, evalExp_var_num hn, rfl⟩⟩
  exact evalExp_binE_iff.mpr ⟨_, hm, .inr ⟨rfl, _, evalExp_var_num hh, rfl⟩⟩

/-- **One more hexadecimal digit**: `Thexnum ⊢ bs ↦ a` and `Thexdigit ⊢ cs ↦ b` give
`Thexnum ⊢ bs cs ↦ 16 a + b`, through the second production with no `_`. -/
theorem thexnum_step {env : Env} (h : HasHexnum env) {bs cs : Grammar.Bytes} {a b : Nat}
    (ha : SymDerives env VarEnv.empty (.varG "Thexnum" []) bs [.num (.natN a)] VarEnv.empty)
    (hb : ∀ ρ, SymDerives env ρ (.varG "Thexdigit" []) cs [.num (.natN b)] ρ) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Thexnum" []) (bs ++ cs) [.num (.natN (16 * a + b))] ρ := by
  let σ₁ : VarEnv := VarEnv.empty.bindVal "n" (.num (.natN a))
  let σ₂ : VarEnv := σ₁.bindVal "h" (.num (.natN b))
  have hbody : SymDerives env VarEnv.empty hexnum2Body (bs ++ [] ++ cs)
      ([.num (.natN a)] ++ [.opt none] ++ [.num (.natN b)]) σ₂ :=
    symDerives_seq3 (symDerives_seqG_single (symDerives_attrVar rfl ha))
      (symDerives_seqG_single symDerives_optNone)
      (symDerives_seqG_single (symDerives_attrVar rfl (hb σ₁)))
  have hbody' : SymDerives env VarEnv.empty hexnum2Body (bs ++ cs)
      [.num (.natN a), .opt none, .num (.natN b)] σ₂ := by simpa using hbody
  have hp : ProdDerives env ρ [] [] hexnum2Prod (bs ++ cs) [.num (.natN (16 * a + b))] :=
    ⟨[], VarEnv.empty, _, σ₂, σ₂, _, evalArgs_nil env ρ, rfl, hbody',
      premsHold_nil_iff.mpr rfl, evalExp_hexnum2Value rfl rfl, rfl⟩
  exact (symDerives_varG h.thexnum).mpr ⟨rfl, _, by simp, hp⟩

/-- A single hexadecimal digit is a `Thexnum`. -/
theorem thexnum_digit {env : Env} (h : HasHexnum env) {cs : Grammar.Bytes} {b : Nat}
    (hb : ∀ ρ, SymDerives env ρ (.varG "Thexdigit" []) cs [.num (.natN b)] ρ) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Thexnum" []) cs [.num (.natN b)] ρ := by
  have hp : ProdDerives env ρ [] [] hexnum1Prod cs [.num (.natN b)] :=
    ⟨[], VarEnv.empty, _, _, _, _, evalArgs_nil env ρ, rfl,
      symDerives_attrVar rfl (hb VarEnv.empty), premsHold_nil_iff.mpr rfl,
      evalExp_varE_iff.mpr rfl, rfl⟩
  exact (symDerives_varG h.thexnum).mpr ⟨rfl, _, by simp, hp⟩

/-- **`Thexnum ⊢ E000 ↦ 57344`.** -/
theorem thexnum_E000 {env : Env} (hf : HasFloatZero env) (h : HasHexnum env) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Thexnum" []) [0x45, 0x30, 0x30, 0x30] [.num (.natN 57344)] ρ := by
  have h₁ := thexnum_digit h (thexdigit_E h) VarEnv.empty
  have h₂ := thexnum_step h h₁ (thexdigit_0 hf h) VarEnv.empty
  have h₃ := thexnum_step h h₂ (thexdigit_0 hf h) VarEnv.empty
  exact thexnum_step h h₃ (thexdigit_0 hf h) ρ

/-! ## The separating sentence -/

/-- The bytes of `\u{E000}`. -/
def escE000 : Grammar.Bytes := Unicode.utf8 "\\u{E000}"

/-- **The patched `Tstringchar` reads `\u{E000}` as `%(57344)`.** -/
theorem tstringchar_E000 {env : Env} (hf : HasFloatZero env) (h : HasHexnum env)
    (hs : TstringcharShape env 57344) (ρ : VarEnv) :
    gramRelSup env ρ (.varG "Tstringchar" []) escE000 (numCase 57344) := by
  obtain ⟨q₁, e₁, pr₁, e₂, e₃, e₄, e₅, e₆, e₇, hg⟩ := hs
  let σ : VarEnv := VarEnv.empty.bindVal "n" (.num (.natN 57344))
  have hbody : SymDerives env VarEnv.empty escBody
      (Unicode.utf8 "\\u{" ++ [0x45, 0x30, 0x30, 0x30] ++ Unicode.utf8 "}") _ σ :=
    symDerives_seq3 (symDerives_seqG_single symDerives_textG)
      (symDerives_seqG_single (symDerives_attrVar rfl (thexnum_E000 hf h VarEnv.empty)))
      (symDerives_seqG_single symDerives_textG)
  have hp : ProdDerives env ρ [] [] (escProd 57344) escE000 [numCase 57344] :=
    ⟨[], VarEnv.empty, _, σ, σ, _, evalArgs_nil env ρ, rfl, hbody,
      premsHold_ifPr_iff.mpr ⟨escCond_text6x_true rfl, rfl⟩, evalExp_case_var rfl, rfl⟩
  exact gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩⟩

/-- The pinned escape production does not read `\u{E000}` as `%(57344)`: the value forces
`n = 57344`, where the pinned premise is false. -/
theorem not_escProd_pinned {env : Env} {ρ : VarEnv} {bs : Grammar.Bytes} :
    ¬ ProdDerives env ρ [] [] (escProd 59392) bs [numCase 57344] := by
  rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, w, -, -, -, hpr, hv, hl⟩
  obtain ⟨hc, rfl⟩ := premsHold_ifPr_iff.mp hpr
  have hw : w = numCase 57344 := (List.cons.inj hl).1.symm
  obtain ⟨u, hu, hcase⟩ := evalExp_caseE_iff.mp (hw ▸ hv)
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.mp hu
  obtain ⟨x, xs, hx, -, rfl⟩ := evalExps_cons_iff.mp hvs
  have hx' : x = .num (.natN 57344) := by
    simp only [numCase, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at hcase
    exact hcase.2.1.symm
  have hn : ρ₂.findVal? "n" = some (.num (.natN 57344)) := hx' ▸ evalExp_varE_iff.mp hx
  exact absurd (EvalExp.unique hc (escCond_pinned_false hn)) (by simp)

/-- A literal production `t => e` reads only the bytes of `t`. -/
theorem prodDerives_text_bytes {env : Env} {ρ : VarEnv} {t : Text} {e : Exp}
    {bs : Grammar.Bytes} {l : List Value}
    (h : ProdDerives env ρ [] [] (.prodD [] (.textG t) e []) bs l) : bs = Unicode.utf8 t := by
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, w, -, -, hs, -, -, -⟩ := h
  exact symDerives_textG_bytes hs

/-- **The pinned `Tstringchar` does not read `\u{E000}` as `%(57344)`.** -/
theorem not_tstringchar_E000 {env : Env} (hb : ∀ ρ, gramRelSup env ρ (.varG "Tchar" []) = ⊥)
    (hs : TstringcharShape env 59392) (ρ : VarEnv) :
    ¬ gramRelSup env ρ (.varG "Tstringchar" []) escE000 (numCase 57344) := by
  obtain ⟨q₁, e₁, pr₁, e₂, e₃, e₄, e₅, e₆, e₇, hg⟩ := hs
  intro h
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp h
  obtain ⟨-, p, hmem, hpd⟩ := (symDerives_varG hg).mp hd
  have hchar : ∀ {σ σ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      ¬ SymDerives env σ (substSym [] (.varG "Tchar" [])) bs l σ' :=
    fun hd => not_symDerives_tchar hb hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_prodDerives_attr_of_dead hchar hpd
  all_goals first
    | exact absurd (prodDerives_text_bytes hpd) (by decide)
    | exact not_escProd_pinned hpd

/-! ## In the grammar institution -/

/-- **#661 repaired**: the text-patched theory entails `Tstringchar ⊢ \u{E000} ↦ %(57344)`. -/
theorem tstringchar_E000_text6x (ρ : VarEnv) :
    Entails (scriptAxioms envText6x) (derivesNT "Tstringchar" [] ρ escE000 (numCase 57344)) :=
  (gramRelSup_varG_iff_entails ..).mp
    (tstringchar_E000 hasFloatZero_text6x hasHexnum_text6x tstringcharShape_text6x ρ)

/-- **#661 in the original theory**: it does not entail that sentence. -/
theorem tstringchar_E000_not_pinned (ρ : VarEnv) :
    ¬ Entails (scriptAxioms Wasm30.envOriginal)
      (derivesNT "Tstringchar" [] ρ escE000 (numCase 57344)) := by
  rw [envOriginal_eq_pinned]
  exact fun h => not_tstringchar_E000 tchar_bot_pinned tstringcharShape_pinned ρ
    ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **#661 alone separates the text-patched theory from the original**: the original does not
entail all of the patched theory. -/
theorem text6x_not_below_original_661 :
    ¬ ∀ ψ ∈ scriptAxioms envText6x, Entails (scriptAxioms Wasm30.envOriginal) ψ :=
  not_entailsAll_of_separates (tstringchar_E000_text6x VarEnv.empty)
    (tstringchar_E000_not_pinned VarEnv.empty)

end Silmaril.Wasm.SpecTec.GrammarInst
