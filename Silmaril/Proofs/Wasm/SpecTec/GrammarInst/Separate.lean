module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Errata
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.TextBridge
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryModule
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x

/-!
# Separating sentences for the text-format errata

`Errata.lean` shows that the text §6.x errata change the grammar theory at exactly their nine
targets. This module gives sentences that separate the two theories, as
`Reverse.lean` does for #654.

* **#662, the float exponent.** The original `Tfloat` has one production,
  `p:Tmant ("E" | "e") s:Tsign ee:Tnum`, so every byte string it derives contains `E` or `e`
  (`tfloat_exponent`), and `Thexfloat` likewise contains `P` or `p` (`thexfloat_exponent`).
  This is the float-exponent defect, stated in the grammar institution. It needs no evaluation
  of `$ieee_`: `Tfloat` and `Thexfloat` do not call it. The patched `Tfloat` derives `0` with
  value `0` (`tfloat_0_text6x`). So the text-patched theory entails `Tfloat ⊢ 0 ↦ 0` and the
  original does not. One level up, the pinned `TfN(N)` derives no `0` at all
  (`tfn_0_not_entailed_original`), whatever `$ieee_` does: the proof never evaluates it. In the
  patched theory `TfN(N) ⊢ 0` should still fail, because `$ieee_` has no clauses
  (`wasm30_ieee_undefined`); that is not proved here. So `TfN` is not where the two theories
  separate; `Tfloat` is.
* **#663, the default alignment.** The original `Talign_(4)` derives the empty string with value
  `%(4)` (its default branch `eps => N`). The patched default branch is
  `eps => n -- if N = 2^n`, and an `if` premise binds nothing, so `n` is unbound when the value
  `%(n)` is evaluated. Hence the patched `Talign_(4)` derives no value at all on the empty
  string (`talign_4_empty_text6x`). The original theory entails `Talign_(4) ⊢ ε ↦ %(4)` and the
  patched one does not. This also records a defect **of the patch**: under the IL evaluator the
  corrected default branch has no derivation.

Together they show that the text errata give a theory incomparable with the original
(`text6x_errata_incomparable`), as `wasm30_errata_incomparable` does for the combined errata.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts
open Silmaril.SpecTec.Equiv.BinaryModule (Rounds symDerives_iterG)

/-! ## Small derivation steps -/

/-- A one-element sequence derives what its element derives. -/
theorem symDerives_seqG_single {env : Env} {ρ ρ' : VarEnv} {g : IL.Sym} {bs : Grammar.Bytes}
    {l : List Value} (h : SymDerives env ρ g bs l ρ') : SymDerives env ρ (.seqG [g]) bs l ρ' :=
  symDerives_seqG_cons.mpr ⟨bs, l, ρ', [], [], h, symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩,
    (List.append_nil bs).symm, (List.append_nil l).symm⟩

/-- `x:g` with `x` fresh binds `x` to the value `g` derives. -/
theorem symDerives_attrVar {env : Env} {σ : VarEnv} {x : IL.Id} {g : IL.Sym} {bs : Grammar.Bytes}
    {v : Value} (hx : σ.findVal? x = none) (h : SymDerives env σ g bs [v] σ) :
    SymDerives env σ (.attrG (.varE x) g) bs [v] (σ.bindVal x v) :=
  symDerives_attrG.mpr ⟨v, σ, h, rfl, matchExp_varE_of_none hx⟩

/-- A literal text terminal derives exactly its UTF-8 bytes. -/
theorem symDerives_textG_bytes {env : Env} {ρ ρ' : VarEnv} {t : Text} {bs : Grammar.Bytes}
    {l : List Value} (h : SymDerives env ρ (.textG t) bs l ρ') : bs = Unicode.utf8 t := by
  obtain ⟨a, ha, -⟩ := h
  rw [symDen_textG] at ha
  exact ha.1

/-- A one-element sequence of a literal text terminal derives exactly its bytes. -/
theorem symDerives_seqText_bytes {env : Env} {ρ ρ' : VarEnv} {t : Text} {bs : Grammar.Bytes}
    {l : List Value} (h : SymDerives env ρ (.seqG [.textG t]) bs l ρ') :
    bs = Unicode.utf8 t := by
  obtain ⟨b₁, l₁, ρ₁, b₂, l₂, h₁, h₂, rfl, -⟩ := symDerives_seqG_cons.mp h
  obtain ⟨rfl, -, -⟩ := symDerives_seqG_nil.mp h₂
  rw [List.append_nil]
  exact symDerives_textG_bytes h₁

/-- An optional iteration with no rounds derives the empty string with value `none`. -/
theorem symDerives_optNone {env : Env} {ρ : VarEnv} {g : IL.Sym} :
    SymDerives env ρ (.iterG g (.mk .opt [])) [] [.opt none] ρ :=
  symDerives_iterG.mpr ⟨[], .nil, Nat.zero_le 1, rfl, rfl⟩

/-! ## #662: the original `Tfloat` and `Thexfloat` need an exponent -/

/-- The body of the pinned `Tfloat` production (`6.1-text.values.spectec:59-60`). -/
def tfloatBodyO : IL.Sym :=
  .seqG [.seqG [.attrG (.varE "p") (.varG "Tmant" [])],
    .altG [.seqG [.textG "E"], .seqG [.textG "e"]],
    .seqG [.attrG (.varE "s") (.varG "Tsign" [])], .seqG [.attrG (.varE "ee") (.varG "Tnum" [])]]

/-- The body of the pinned `Thexfloat` production (`6.1-text.values.spectec:62-63`). -/
def thexfloatBodyO : IL.Sym :=
  .seqG [.seqG [.textG "0x"], .seqG [.attrG (.varE "p") (.varG "Thexmant" [])],
    .altG [.seqG [.textG "P"], .seqG [.textG "p"]],
    .seqG [.attrG (.varE "s") (.varG "Tsign" [])], .seqG [.attrG (.varE "ee") (.varG "Tnum" [])]]

/-- An exponent marker: a derivation of `("E" | "e")`, or of `("P" | "p")`, is one of the two
letters. -/
theorem symDerives_marker {env : Env} {ρ ρ' : VarEnv} {s t : Text} {bs : Grammar.Bytes}
    {l : List Value} (h : SymDerives env ρ (.altG [.seqG [.textG s], .seqG [.textG t]]) bs l ρ') :
    bs = Unicode.utf8 s ∨ bs = Unicode.utf8 t := by
  obtain ⟨g, hg, hd⟩ := symDerives_altG.mp h
  rcases List.mem_pair.mp hg with rfl | rfl
  · exact Or.inl (symDerives_seqText_bytes hd)
  · exact Or.inr (symDerives_seqText_bytes hd)

/-- A sequence whose second factor is an exponent marker derives a string containing one of
the marker's letters. -/
theorem seq_marker_mem {env : Env} {ρ ρ' : VarEnv} {g : IL.Sym} {gs : List IL.Sym} {s t : Text}
    {a b : UInt8} (ha : Unicode.utf8 s = [a]) (hb : Unicode.utf8 t = [b]) {bs : Grammar.Bytes}
    {l : List Value}
    (h : SymDerives env ρ (.seqG (g :: .altG [.seqG [.textG s], .seqG [.textG t]] :: gs)) bs l ρ') :
    a ∈ bs ∨ b ∈ bs := by
  obtain ⟨b₁, l₁, ρ₁, b₂, l₂, -, h₂, rfl, -⟩ := symDerives_seqG_cons.mp h
  obtain ⟨c₁, k₁, ρ₂, c₂, k₂, hm, -, rfl, -⟩ := symDerives_seqG_cons.mp h₂
  rcases symDerives_marker hm with rfl | rfl
  · exact Or.inl (by simp [ha])
  · exact Or.inr (by simp [hb])

/-- A grammar with one production whose body is `bodyMem`-shaped contains a marker letter. -/
theorem single_prod_mem {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {ps : List Param} {ty : Typ}
    {q : List Param} {body : IL.Sym} {e : Exp} {prems : List Prem} {P : Grammar.Bytes → Prop}
    (hg : env.findGram? x = some (ps, ty, [.prodD q body e prems]))
    (hsub : substSym (gramArgSubst ps []) body = body)
    (hP : ∀ {σ σ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      SymDerives env σ body bs l σ' → P bs)
    {bs : Grammar.Bytes} {l : List Value} (h : SymDerives env ρ (.varG x []) bs l ρ') : P bs := by
  obtain ⟨-, p, hp, hd⟩ := (symDerives_varG hg).mp h
  rw [List.mem_singleton] at hp
  subst hp
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩ := hd
  rw [hsub] at hs
  exact hP hs

/-- **#662 as a grammar sentence**: every byte string the pinned `Tfloat` derives contains an
exponent marker `E` (`0x45`) or `e` (`0x65`). In particular no exponent-free literal such as `0`,
`1.5` or `12345` is a `Tfloat`. -/
theorem tfloat_exponent {env : Env} {q : List Param} {e : Exp} {prems : List Prem}
    (hg : env.findGram? "Tfloat" = some ([], .numT .ratT, [.prodD q tfloatBodyO e prems]))
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value}
    (h : SymDerives env ρ (.varG "Tfloat" []) bs l ρ') : (0x45 : UInt8) ∈ bs ∨ 0x65 ∈ bs :=
  single_prod_mem (P := fun bs => (0x45 : UInt8) ∈ bs ∨ 0x65 ∈ bs) hg rfl
    (fun hs => seq_marker_mem (s := "E") (t := "e") rfl rfl hs) h

/-- The same for `Thexfloat`: every byte string it derives contains `P` (`0x50`) or `p`
(`0x70`). -/
theorem thexfloat_exponent {env : Env} {q : List Param} {e : Exp} {prems : List Prem}
    (hg : env.findGram? "Thexfloat" = some ([], .numT .ratT, [.prodD q thexfloatBodyO e prems]))
    {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value}
    (h : SymDerives env ρ (.varG "Thexfloat" []) bs l ρ') : (0x50 : UInt8) ∈ bs ∨ 0x70 ∈ bs := by
  refine single_prod_mem (P := fun bs => (0x50 : UInt8) ∈ bs ∨ 0x70 ∈ bs) hg rfl ?_ h
  intro σ σ' cs k hs
  obtain ⟨b₁, l₁, ρ₁, b₂, l₂, -, h₂, rfl, -⟩ := symDerives_seqG_cons.mp hs
  have hm : (0x50 : UInt8) ∈ b₂ ∨ 0x70 ∈ b₂ := seq_marker_mem (s := "P") (t := "p") rfl rfl h₂
  rcases hm with hm | hm
  · exact Or.inl (List.mem_append_right _ hm)
  · exact Or.inr (List.mem_append_right _ hm)

/-! ## #662: the patched `Tfloat` derives `0` -/

/-- The digit `0` (`6.1-text.values.spectec`, first production of `Tdigit`). -/
def tdigit0Prod : IL.Prod := .prodD [] (.numG 48) (.numE (.natN 0)) []

/-- The first production of `Tnum`, `d:Tdigit => d`. -/
def tnum1Prod : IL.Prod :=
  .prodD [.expP "d" (.numT .natT)] (.attrG (.varE "d") (.varG "Tdigit" [])) (.varE "d") []

/-- The first production of `Tmant`, `p:Tnum "."? => p`. -/
def tmant1Prod : IL.Prod :=
  .prodD [.expP "p" (.numT .natT)]
    (.seqG [.seqG [.attrG (.varE "p") (.varG "Tnum" [])], .seqG [.iterG (.textG ".") (.mk .opt [])]])
    (.cvtE (.varE "p") .natT .ratT) []

/-- The production #662 adds to `Tfloat`, `p:Tmant => p`. -/
def tfloat1Prod : IL.Prod :=
  .prodD [.expP "p" (.numT .ratT)] (.attrG (.varE "p") (.varG "Tmant" [])) (.varE "p") []

/-- The grammars a derivation of `Tfloat ⊢ 0` goes through, each by its first production. -/
structure HasFloatZero (env : Env) : Prop where
  tdigit : ∃ r, env.findGram? "Tdigit" = some ([], .numT .natT, tdigit0Prod :: r)
  tnum : ∃ r, env.findGram? "Tnum" = some ([], .numT .natT, tnum1Prod :: r)
  tmant : ∃ r, env.findGram? "Tmant" = some ([], .numT .ratT, tmant1Prod :: r)
  tfloat : ∃ r, env.findGram? "Tfloat" = some ([], .numT .ratT, tfloat1Prod :: r)

/-- A grammar derives what its first production derives, leaving the caller's scope. -/
theorem symDerives_firstProd {env : Env} {ρ : VarEnv} {x : IL.Id} {ps : List Param} {ty : Typ}
    {p : IL.Prod} (h : ∃ r, env.findGram? x = some (ps, ty, p :: r)) {args : List IL.Arg}
    {bs : Grammar.Bytes} {l : List Value} (hp : ProdDerives env ρ ps args p bs l) :
    SymDerives env ρ (.varG x args) bs l ρ := by
  obtain ⟨r, hg⟩ := h
  exact (symDerives_varG hg).mpr ⟨rfl, p, List.mem_cons_self .., hp⟩

/-- `Tdigit ⊢ 0 ↦ 0`. -/
theorem tdigit_0 {env : Env} (h : HasFloatZero env) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Tdigit" []) [0x30] [.num (.natN 0)] ρ :=
  symDerives_firstProd h.tdigit ⟨[], VarEnv.empty, _, VarEnv.empty, VarEnv.empty, _,
    evalArgs_nil env ρ, rfl, (symDerives_numG (by decide)).mpr ⟨rfl, rfl, rfl⟩,
    premsHold_nil_iff.mpr rfl, evalExp_numE_iff.mpr rfl, rfl⟩

/-- `Tnum ⊢ 0 ↦ 0`. -/
theorem tnum_0 {env : Env} (h : HasFloatZero env) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Tnum" []) [0x30] [.num (.natN 0)] ρ :=
  symDerives_firstProd h.tnum ⟨[], VarEnv.empty, _, _, _, _, evalArgs_nil env ρ, rfl,
    symDerives_attrVar rfl (tdigit_0 h VarEnv.empty), premsHold_nil_iff.mpr rfl,
    evalExp_varE_iff.mpr rfl, rfl⟩

/-- `Tmant ⊢ 0 ↦ 0`, through `p:Tnum "."?` with no `.`. -/
theorem tmant_0 {env : Env} (h : HasFloatZero env) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Tmant" []) [0x30] [.num (.ratN 0)] ρ := by
  let σ : VarEnv := VarEnv.empty.bindVal "p" (.num (.natN 0))
  have hb : SymDerives env VarEnv.empty
      (.seqG [.seqG [.attrG (.varE "p") (.varG "Tnum" [])], .seqG [.iterG (.textG ".") (.mk .opt [])]])
      [0x30] [.num (.natN 0), .opt none] σ :=
    symDerives_seqG_cons.mpr ⟨[0x30], [.num (.natN 0)], σ, [], [.opt none],
      symDerives_seqG_single (symDerives_attrVar rfl (tnum_0 h VarEnv.empty)),
      symDerives_seqG_single (symDerives_seqG_single symDerives_optNone), rfl, rfl⟩
  have hv : EvalExp env σ (.cvtE (.varE "p") .natT .ratT) (.num (.ratN 0)) :=
    evalExp_cvtE_iff.mpr ⟨.natN 0, .ratN 0, evalExp_varE_iff.mpr rfl, by simp [Num.cvt], rfl⟩
  exact symDerives_firstProd h.tmant ⟨[], VarEnv.empty, _, σ, σ, _, evalArgs_nil env ρ, rfl, hb,
    premsHold_nil_iff.mpr rfl, hv, rfl⟩

/-- **The patched `Tfloat` derives `0` with value `0`**, through the production #662 adds. -/
theorem tfloat_0 {env : Env} (h : HasFloatZero env) (ρ : VarEnv) :
    gramRelSup env ρ (.varG "Tfloat" []) [0x30] (.num (.ratN 0)) :=
  gramRelSup_iff.mpr ⟨ρ, symDerives_firstProd h.tfloat ⟨[], VarEnv.empty, _, _, _, _,
    evalArgs_nil env ρ, rfl, symDerives_attrVar rfl (tmant_0 h VarEnv.empty),
    premsHold_nil_iff.mpr rfl, evalExp_varE_iff.mpr rfl, rfl⟩⟩

/-! ## #663: the default alignment -/

/-- The pinned default branch of `Talign_`, `eps => N` (`6.3-text.instructions.spectec:186`). -/
def talignDefaultO : IL.Prod := .prodD [] .epsG (.caseE "%" (.tupE [.varE "N"])) []

/-- The parameter list of `Talign_`. -/
def talignParams : List Param := [.expP "N" (.varT "N" [])]

/-- The argument `4`. -/
def arg4 : List IL.Arg := [.expA (.numE (.natN 4))]

/-- **The pinned `Talign_(4)` derives the empty string with value `%(4)`**, through its default
branch. -/
theorem talign_4 {env : Env} {p₁ : IL.Prod}
    (hg : env.findGram? "Talign_" = some (talignParams, .varT "u32" [], [p₁, talignDefaultO]))
    (ρ : VarEnv) : gramRelSup env ρ (.varG "Talign_" arg4) [] (numCase 4) := by
  let σ : VarEnv := VarEnv.empty.bindVal "N" (.num (.natN 4))
  have hv : EvalExp env σ (.caseE "%" (.tupE [.varE "N"])) (numCase 4) :=
    evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr
      ⟨_, evalExps_singleton (evalExp_varE_iff.mpr rfl), rfl⟩, rfl⟩
  have hp : ProdDerives env ρ talignParams arg4 talignDefaultO [] [numCase 4] :=
    ⟨_, σ, [], σ, σ, _, evalArgs_expA (evalExp_numE_iff.mpr rfl), rfl,
      symDerives_epsG.mpr ⟨rfl, rfl, rfl⟩, premsHold_nil_iff.mpr rfl, hv, rfl⟩
  exact gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩⟩

/-- The shape of the patched `Talign_`: an explicit branch beginning with `align=`, and the
default branch `eps => %(n) -- if e`, whose value mentions the variable `n`. -/
def TalignPatched (env : Env) : Prop :=
  ∃ (q₁ : List Param) (rest : List IL.Sym) (e₁ : Exp) (pr₁ : List Prem) (q₂ : List Param)
    (e₂ : Exp), env.findGram? "Talign_" = some (talignParams, .varT "u32" [],
      [.prodD q₁ (.seqG (.seqG [.textG "align="] :: rest)) e₁ pr₁,
        .prodD q₂ .epsG (.caseE "%" (.tupE [.varE "n"])) [.ifPr e₂]])

/-- The explicit branch derives a nonempty string. -/
theorem talign_explicit_ne {env : Env} {ρ ρ' : VarEnv} {rest : List IL.Sym}
    {bs : Grammar.Bytes} {l : List Value}
    (h : SymDerives env ρ (.seqG (.seqG [.textG "align="] :: rest)) bs l ρ') : bs ≠ [] := by
  obtain ⟨b₁, l₁, ρ₁, b₂, l₂, h₁, -, rfl, -⟩ := symDerives_seqG_cons.mp h
  have hb : b₁ = Unicode.utf8 "align=" := symDerives_seqText_bytes h₁
  rw [hb, show Unicode.utf8 "align=" = [0x61, 0x6C, 0x69, 0x67, 0x6E, 0x3D] from rfl]
  exact List.cons_ne_nil _ _

/-- The value `%(n)` cannot be evaluated where `n` is unbound. -/
theorem not_evalExp_case_unbound {env : Env} {σ : VarEnv} (hn : σ.findVal? "n" = none)
    {v : Value} : ¬ EvalExp env σ (.caseE "%" (.tupE [.varE "n"])) v := by
  intro h
  obtain ⟨w, hw, -⟩ := evalExp_caseE_iff.mp h
  obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.mp hw
  obtain ⟨u, us, hu, -, -⟩ := evalExps_cons_iff.mp hvs
  rw [evalExp_varE_iff, hn] at hu
  exact absurd hu (by simp)

/-- The patched default branch derives nothing: the `if` premise binds nothing, so `n` is
unbound when `%(n)` is evaluated. -/
theorem talign_default_patched_none {env : Env} {ρ : VarEnv} {q₂ : List Param} {e₂ : Exp}
    {bs : Grammar.Bytes} {l : List Value} :
    ¬ ProdDerives env ρ talignParams arg4 (.prodD q₂ .epsG (.caseE "%" (.tupE [.varE "n"]))
      [.ifPr e₂]) bs l := by
  rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hb, hs, hpr, hv, -⟩
  obtain ⟨u, hu, rfl⟩ := evalArgs_expA_iff.mp hw
  obtain rfl : u = .num (.natN 4) := evalExp_numE_iff.mp hu
  obtain rfl : ρ₀ = VarEnv.empty.bindVal "N" (.num (.natN 4)) := (Option.some.inj hb).symm
  obtain ⟨-, -, rfl⟩ := symDerives_epsG.mp hs
  obtain ⟨-, rfl⟩ := premsHold_ifPr_iff.mp hpr
  exact not_evalExp_case_unbound rfl hv

/-- **The patched `Talign_(4)` derives no value on the empty string.** -/
theorem talign_4_patched_none {env : Env} (hg : TalignPatched env) (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup env ρ (.varG "Talign_" arg4) [] v := by
  obtain ⟨q₁, rest, e₁, pr₁, q₂, e₂, hg⟩ := hg
  rintro ⟨a, ρ', ha, hv⟩
  obtain ⟨-, p, hp, hd⟩ := (symDerives_varG hg).mp ⟨a, ha, hv⟩
  rcases List.mem_pair.mp hp with rfl | rfl
  · obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, w, -, -, hs, -, -, -⟩ := hd
    exact talign_explicit_ne hs rfl
  · exact talign_default_patched_none hd

/-! ## At the pinned and the text-patched wasm-3.0 scripts -/

/-- The text-patched wasm-3.0 script. -/
noncomputable abbrev envText6x : Env := envOfScript IL.Text6x.wasm30text6x

set_option maxRecDepth 100000 in
theorem hasFloatZero_text6x : HasFloatZero envText6x :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

set_option maxRecDepth 100000 in
theorem talignPatched_text6x : TalignPatched envText6x :=
  ⟨_, _, _, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findGram_tfloat_original :
    ∃ q e prems, Wasm30.envOriginal.findGram? "Tfloat" =
      some ([], .numT .ratT, [.prodD q tfloatBodyO e prems]) := by
  rw [Wasm30.envOriginal, wasm30_original_eq]
  exact ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findGram_thexfloat_original :
    ∃ q e prems, Wasm30.envOriginal.findGram? "Thexfloat" =
      some ([], .numT .ratT, [.prodD q thexfloatBodyO e prems]) := by
  rw [Wasm30.envOriginal, wasm30_original_eq]
  exact ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findGram_talign_original :
    ∃ p₁, Wasm30.envOriginal.findGram? "Talign_" =
      some (talignParams, .varT "u32" [], [p₁, talignDefaultO]) := by
  rw [Wasm30.envOriginal, wasm30_original_eq]
  exact ⟨_, rfl⟩

/-- **The float-exponent defect (#662) in the pinned wasm-3.0 grammar theory.** Whatever the
original theory entails about `Tfloat` is a string with `E` or `e` in it, and about `Thexfloat`
a string with `P` or `p` in it. -/
theorem wasm30_float_exponent_mandatory (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    (Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "Tfloat" [] ρ bs v) →
      (0x45 : UInt8) ∈ bs ∨ 0x65 ∈ bs) ∧
    (Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "Thexfloat" [] ρ bs v) →
      (0x50 : UInt8) ∈ bs ∨ 0x70 ∈ bs) := by
  obtain ⟨q, e, prems, hf⟩ := findGram_tfloat_original
  obtain ⟨q', e', prems', hh⟩ := findGram_thexfloat_original
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp ((gramRelSup_varG_iff_entails ..).mpr h)
    exact tfloat_exponent hf hd
  · obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp ((gramRelSup_varG_iff_entails ..).mpr h)
    exact thexfloat_exponent hh hd

/-- **#662 repaired**: the text-patched theory entails `Tfloat ⊢ 0 ↦ 0`. -/
theorem tfloat_0_entailed_text6x (ρ : VarEnv) :
    Entails (scriptAxioms envText6x) (derivesNT "Tfloat" [] ρ [0x30] (.num (.ratN 0))) :=
  (gramRelSup_varG_iff_entails ..).mp (tfloat_0 hasFloatZero_text6x ρ)

/-- …and the original theory entails no `Tfloat` derivation of `0`, with any value. -/
theorem tfloat_0_not_entailed_original (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "Tfloat" [] ρ [0x30] v) := by
  intro h
  rcases (wasm30_float_exponent_mandatory ρ [0x30] v).1 h with h | h <;> simp at h

/-- **#663 in the original theory**: it entails `Talign_(4) ⊢ ε ↦ %(4)`. -/
theorem talign_4_entailed_original (ρ : VarEnv) :
    Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "Talign_" arg4 ρ [] (numCase 4)) := by
  obtain ⟨p₁, hg⟩ := findGram_talign_original
  exact (gramRelSup_varG_iff_entails ..).mp (talign_4 hg ρ)

/-- …and the text-patched theory entails no `Talign_(4)` derivation of the empty string. -/
theorem talign_4_not_entailed_text6x (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms envText6x) (derivesNT "Talign_" arg4 ρ [] v) := fun h =>
  talign_4_patched_none talignPatched_text6x ρ v ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **The text errata give an incomparable theory**: neither the pinned nor the text-patched
wasm-3.0 grammar theory entails the other. The witnesses are `Talign_(4) ⊢ ε ↦ %(4)` (#663) and
`Tfloat ⊢ 0 ↦ 0` (#662). -/
theorem text6x_errata_incomparable :
    (¬ ∀ ψ ∈ scriptAxioms Wasm30.envOriginal, Entails (scriptAxioms envText6x) ψ) ∧
      (¬ ∀ ψ ∈ scriptAxioms envText6x, Entails (scriptAxioms Wasm30.envOriginal) ψ) :=
  ⟨not_entailsAll_of_separates (talign_4_entailed_original VarEnv.empty)
      (talign_4_not_entailed_text6x VarEnv.empty _),
    not_entailsAll_of_separates (tfloat_0_entailed_text6x VarEnv.empty)
      (tfloat_0_not_entailed_original VarEnv.empty _)⟩

/-! ## #662 at `TfN`: no float literal `0`, whatever `$ieee_` does -/

/-- The productions of the pinned `TfNmag(N)` (`6.1-text.values.spectec:65-70`): a `Tfloat`, a
`Thexfloat`, `inf`, `nan` and `nan:0x` followed by a payload. Only the shapes of the bodies
matter; values and premises (which call `$ieee_`) are left open. -/
def TfNmagShape (env : Env) : Prop :=
  ∃ (q₁ : List Param) (e₁ : Exp) (pr₁ : List Prem) (q₂ : List Param) (e₂ : Exp)
    (pr₂ : List Prem) (e₃ e₄ : Exp) (q₅ : List Param) (g₅ : IL.Sym) (e₅ : Exp) (pr₅ : List Prem)
    (t : Typ), env.findGram? "TfNmag" = some ([.expP "N" (.varT "N" [])], t,
      [.prodD q₁ (.attrG (.varE "q") (.varG "Tfloat" [])) e₁ pr₁,
        .prodD q₂ (.attrG (.varE "q") (.varG "Thexfloat" [])) e₂ pr₂,
        .prodD [] (.textG "inf") e₃ [], .prodD [] (.textG "nan") e₄ [],
        .prodD q₅ (.seqG [.seqG [.textG "nan:0x"], g₅]) e₅ pr₅])

/-- An expression parameter contributes no grammar substitution. -/
theorem gramArgSubst_expP (x : IL.Id) (t : Typ) (args : List IL.Arg) :
    gramArgSubst [.expP x t] args = [] := by
  cases args <;> rfl

/-- `x:g` derives what `g` derives. -/
theorem symDerives_attr_inner {env : Env} {ρ ρ' : VarEnv} {e : Exp} {g : IL.Sym}
    {bs : Grammar.Bytes} {l : List Value} (h : SymDerives env ρ (.attrG e g) bs l ρ') :
    ∃ v ρ₁, SymDerives env ρ g bs [v] ρ₁ := by
  obtain ⟨v, ρ₁, hd, -, -⟩ := symDerives_attrG.mp h
  exact ⟨v, ρ₁, hd⟩

/-- **The pinned `TfNmag(N)` derives no `0`**, for any `N` and any evaluation of `$ieee_`: the
`Tfloat` and `Thexfloat` branches need an exponent marker, and the other three are literals that
do not match. -/
theorem not_tfnmag_0 {env : Env} (hm : TfNmagShape env)
    (hf : ∃ q e prems, env.findGram? "Tfloat" = some ([], .numT .ratT, [.prodD q tfloatBodyO e prems]))
    (hh : ∃ q e prems,
      env.findGram? "Thexfloat" = some ([], .numT .ratT, [.prodD q thexfloatBodyO e prems]))
    {ρ ρ' : VarEnv} {args : List IL.Arg} {l : List Value} :
    ¬ SymDerives env ρ (.varG "TfNmag" args) [0x30] l ρ' := by
  obtain ⟨q₁, e₁, pr₁, q₂, e₂, pr₂, e₃, e₄, q₅, g₅, e₅, pr₅, t, hg⟩ := hm
  obtain ⟨qf, ef, prf, hf⟩ := hf
  obtain ⟨qh, eh, prh, hh⟩ := hh
  intro h
  obtain ⟨-, p, hp, hd⟩ := (symDerives_varG hg).mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩ := hd <;>
    rw [gramArgSubst_expP] at hs
  · obtain ⟨w, σ, hw⟩ := symDerives_attr_inner hs
    rcases tfloat_exponent hf hw with h' | h' <;> simp at h'
  · obtain ⟨w, σ, hw⟩ := symDerives_attr_inner hs
    rcases thexfloat_exponent hh hw with h' | h' <;> simp at h'
  · exact absurd (symDerives_textG_bytes hs) (by decide)
  · exact absurd (symDerives_textG_bytes hs) (by decide)
  · obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, -, hb, -⟩ := symDerives_seqG_cons.mp hs
    have hb₁ : b₁ = Unicode.utf8 "nan:0x" := symDerives_seqText_bytes h₁
    rw [hb₁, show Unicode.utf8 "nan:0x" = [0x6E, 0x61, 0x6E, 0x3A, 0x30, 0x78] from rfl] at hb
    simp at hb

/-- The two productions of the pinned `TfN(N)`: a sign, then a `TfNmag(N)`. -/
def TfNShape (env : Env) : Prop :=
  ∃ (q₁ : List Param) (p₁ e₁ : Exp) (q₂ : List Param) (p₂ e₂ : Exp) (t : Typ),
    env.findGram? "TfN" = some ([.expP "N" (.varT "N" [])], t,
      [.prodD q₁ (.seqG [.seqG [.attrG p₁ (.varG "Tsign" [])],
          .seqG [.attrG (.varE "q") (.varG "TfNmag" [.expA (.varE "N")])]]) e₁ [],
        .prodD q₂ (.seqG [.seqG [.attrG p₂ (.varG "Tsign" [])],
          .seqG [.attrG (.varE "q") (.varG "TfNmag" [.expA (.varE "N")])]]) e₂ []])

/-- The pinned `Tsign` (`6.1-text.values.spectec:21-22`): empty, `+` or `-`. -/
def TsignShape (env : Env) : Prop :=
  ∃ (e₁ e₂ e₃ : Exp) (t : Typ), env.findGram? "Tsign" =
    some ([], t, [.prodD [] .epsG e₁ [], .prodD [] (.textG "+") e₂ [], .prodD [] (.textG "-") e₃ []])

/-- A sign is empty, `+` or `-`. -/
theorem tsign_bytes {env : Env} (hs : TsignShape env) {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} (h : SymDerives env ρ (.varG "Tsign" []) bs l ρ') :
    bs = [] ∨ bs = [0x2B] ∨ bs = [0x2D] := by
  obtain ⟨e₁, e₂, e₃, t, hg⟩ := hs
  obtain ⟨-, p, hp, hd⟩ := (symDerives_varG hg).mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩ := hd
  · exact Or.inl (symDerives_epsG.mp hs).1
  · exact Or.inr (Or.inl (symDerives_textG_bytes hs))
  · exact Or.inr (Or.inr (symDerives_textG_bytes hs))

/-- A signed `TfNmag` body derives no `0`. -/
theorem not_signed_0 {env : Env} (hs : TsignShape env)
    (hmag : ∀ {σ σ' : VarEnv} {args : List IL.Arg} {l : List Value},
      ¬ SymDerives env σ (.varG "TfNmag" args) [0x30] l σ')
    {ρ ρ' : VarEnv} {p : Exp} {a : List IL.Arg} {l : List Value} :
    ¬ SymDerives env ρ (.seqG [.seqG [.attrG p (.varG "Tsign" [])],
        .seqG [.attrG (.varE "q") (.varG "TfNmag" a)]]) [0x30] l ρ' := by
  intro h
  obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, hb, -⟩ := symDerives_seqG_cons.mp h
  obtain ⟨c₁, k₁, τ₁, c₂, k₂, hc₁, hc₂, rfl, -⟩ := symDerives_seqG_cons.mp h₁
  obtain ⟨rfl, -, -⟩ := symDerives_seqG_nil.mp hc₂
  obtain ⟨d₁, k₃, τ₂, d₂, k₄, hd₀, hd₂, rfl, -⟩ := symDerives_seqG_cons.mp h₂
  obtain ⟨rfl, -, -⟩ := symDerives_seqG_nil.mp hd₂
  obtain ⟨f₁, k₅, τ₅, f₂, k₆, hd₁, hf₂, rfl, -⟩ := symDerives_seqG_cons.mp hd₀
  obtain ⟨rfl, -, -⟩ := symDerives_seqG_nil.mp hf₂
  obtain ⟨u, τ₃, hu⟩ := symDerives_attr_inner hc₁
  obtain ⟨w, τ₄, hw⟩ := symDerives_attr_inner hd₁
  rcases tsign_bytes hs hu with rfl | rfl | rfl
  · simp only [List.append_nil, List.nil_append] at hb
    exact hmag (hb ▸ hw)
  · simp at hb
  · simp at hb

/-- **The float-literal defect at `TfN`**: the pinned `TfN(N)` derives no `0`, for any `N` and
any value, and for any evaluation of `$ieee_` — the proof never reaches it. -/
theorem not_tfn_0 {env : Env} (hn : TfNShape env) (hs : TsignShape env) (hm : TfNmagShape env)
    (hf : ∃ q e prems, env.findGram? "Tfloat" = some ([], .numT .ratT, [.prodD q tfloatBodyO e prems]))
    (hh : ∃ q e prems,
      env.findGram? "Thexfloat" = some ([], .numT .ratT, [.prodD q thexfloatBodyO e prems]))
    (ρ : VarEnv) (args : List IL.Arg) (v : Value) :
    ¬ gramRelSup env ρ (.varG "TfN" args) [0x30] v := by
  obtain ⟨q₁, p₁, e₁, q₂, p₂, e₂, t, hg⟩ := hn
  rintro ⟨a, ρ', ha, hv⟩
  obtain ⟨-, p, hp, hd⟩ := (symDerives_varG hg).mp ⟨a, ha, hv⟩
  have hmag := fun {σ σ' : VarEnv} {args : List IL.Arg} {l : List Value} =>
    not_tfnmag_0 (ρ := σ) (ρ' := σ') (args := args) (l := l) hm hf hh
  rcases List.mem_pair.mp hp with rfl | rfl <;>
    obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, w, -, -, hs', -, -, -⟩ := hd <;>
    rw [gramArgSubst_expP] at hs'
  · exact not_signed_0 hs hmag hs'
  · exact not_signed_0 hs hmag hs'

set_option maxRecDepth 100000 in
theorem tfNShape_original : TfNShape Wasm30.envOriginal := by
  rw [Wasm30.envOriginal, wasm30_original_eq]
  exact ⟨_, _, _, _, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem tsignShape_original : TsignShape Wasm30.envOriginal := by
  rw [Wasm30.envOriginal, wasm30_original_eq]
  exact ⟨_, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem tfNmagShape_original : TfNmagShape Wasm30.envOriginal := by
  rw [Wasm30.envOriginal, wasm30_original_eq]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **#662 as the doc's sentence**: the pinned wasm-3.0 theory entails no `TfN(N) ⊢ 0 ↦ v`, for
any `N` and `v`. Unlike `wasm30_ieee_undefined`, this does not depend on `$ieee_`: the proof
holds for every evaluation environment with the pinned `TfN`, `Tsign`, `TfNmag`, `Tfloat` and
`Thexfloat` grammars (`not_tfn_0`). -/
theorem tfn_0_not_entailed_original (ρ : VarEnv) (args : List IL.Arg) (v : Value) :
    ¬ Entails (scriptAxioms Wasm30.envOriginal) (derivesNT "TfN" args ρ [0x30] v) := fun h =>
  not_tfn_0 tfNShape_original tsignShape_original tfNmagShape_original findGram_tfloat_original
    findGram_thexfloat_original ρ args v ((gramRelSup_varG_iff_entails ..).mpr h)

end Silmaril.Wasm.SpecTec.GrammarInst
