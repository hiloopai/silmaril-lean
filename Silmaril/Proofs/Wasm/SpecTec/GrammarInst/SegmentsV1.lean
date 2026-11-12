module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Dead
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.V1Binary
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10

/-!
# #690 in the byte grammar institution: `Belem` and `Bdata` of wasm-1.0

The pinned `Belem` and `Bdata` (`A-binary.spectec:492`, `:518`) begin with the byte terminal
`0x00`; #690 replaces it by `0:Bu32`, a LEB128 index whose value is 0, which also admits the
non-minimal spelling `80 00` (`test/core/binary-leb128.wast:1029-1037`, `:24-31`).

* `belem_80_fixed`, `bdata_80_fixed`: the corrected theory entails
  `Belem ⊢ 80 00 0B 00 ↦ ELEM [] []` and `Bdata ⊢ 80 00 0B 00 ↦ DATA [] []`: index `80 00`,
  the empty expression `0B`, and the empty vector `00`. The derivations go through `Bu32`
  (`symDerives_bu32_v1`), `Bexpr` with no instruction (`bexpr_end`) and `Blist` with count 0
  (`blist_empty`, proved directly: `Equiv/BinaryModule.lean`'s `blist_iff_vec` needs a `Bs33`
  that wasm-1.0 does not have).
* `belem_80_not_original`, `bdata_80_not_original`: the pinned theory entails nothing at all
  about a byte string starting with `80`, for either grammar.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts
open Silmaril.Wasm.Binary (U32 UN)
open Silmaril.SpecTec.Equiv (blistParams blistProds)
open Silmaril.SpecTec.Equiv.BinaryModule (Rounds symDerives_iterG blistScope blistScope_n
  blistScope_els evalArgs_typA_gramA_iff evalExp_blistResult matchExp_iterList_var
  evalExp_iterList_var)
open Silmaril.SpecTec.Equiv.V1Binary (HasV1Types symDerives_bu32_v1)

/-! ## `Blist` with count 0 -/

/-- `Blist`'s body, with the grammar argument `y` substituted. -/
abbrev blistBodyOf (y : IL.Id) : IL.Sym := Silmaril.SpecTec.Equiv.BinaryModule.blistBody y

/-- The body of `Blist` reads the count `00` and no element. -/
theorem blistBody_empty {env : Env} {σ : VarEnv} (hn : σ.findVal? "n" = none)
    (hels : σ.findVal? "el*" = none)
    (hu : SymDerives env σ (.varG "Bu32" []) [0x00] [numCase 0] σ) (y : IL.Id) :
    SymDerives env σ (blistBodyOf y) [0x00] [numCase 0, .list []]
      ((σ.bindVal "n" (.num (.natN 0))).bindVal "el*" (.list [])) := by
  let σ₁ : VarEnv := σ.bindVal "n" (.num (.natN 0))
  have hA : SymDerives env σ (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])) [0x00]
      [numCase 0] σ₁ := symDerives_attrG.mpr ⟨_, _, hu, rfl, matchExp_case_var hn⟩
  have hn₁ : σ₁.findVal? "n" = some (.num (.natN 0)) := by
    simp [σ₁, VarEnv.findVal?, VarEnv.bindVal, Map.bind]
  have hels₁ : σ₁.findVal? "el*" = none := by
    simpa [σ₁, VarEnv.findVal?, VarEnv.bindVal, Map.bind, Map.find?] using hels
  have hc : IterCount env σ₁ (.listN (.varE "n") none) ([] : List (Value × List Value)).length :=
    ⟨rfl, _, evalExp_varE_iff.mpr hn₁, rfl⟩
  have hI : SymDerives env σ₁ (.iterG (.attrG (.varE "el") (.varG y []))
      (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])) [] [.list []]
      (σ₁.bindVal "el*" (.list [])) :=
    symDerives_iterG.mpr ⟨[], .nil, hc, rfl, ⟨_, matchExp_varE_of_none hels₁, rfl⟩⟩
  exact symDerives_seqG_cons.mpr ⟨[0x00], [numCase 0], σ₁, [], [.list []],
    symDerives_seqG_single hA, symDerives_seqG_single (symDerives_seqG_single hI), rfl, rfl⟩

/-- **`Blist(BY)` reads `00` as the empty list**, given that `Bu32` reads `00` as `0`. -/
theorem blist_empty {env : Env}
    (hb : env.findGram? "Blist" = some (blistParams, .iterT (.varT "el" []) .list, blistProds))
    (hu : ∀ σ, SymDerives env σ (.varG "Bu32" []) [0x00] [numCase 0] σ) (t : Typ) (y : IL.Id)
    (ρ : VarEnv) :
    SymDerives env ρ (.varG "Blist" [.typA t, .gramA (.varG y [])]) [0x00] [.list []] ρ := by
  let σ := blistScope ρ t y
  let σ₂ : VarEnv := (σ.bindVal "n" (.num (.natN 0))).bindVal "el*" (.list [])
  have hbody := blistBody_empty (blistScope_n ρ t y) (blistScope_els ρ t y) (hu σ) y
  have hn : σ₂.findVal? "n" = some (.num (.natN 0)) := by
    simp [σ₂, VarEnv.findVal?, VarEnv.bindVal, Map.bind]
  have hel : σ₂.findVal? "el*" = some (.list []) := by
    simp [σ₂, VarEnv.findVal?, VarEnv.bindVal, Map.bind]
  have hp : ProdDerives env ρ blistParams [.typA t, .gramA (.varG y [])]
      (.prodD [.expP "n" (.varT "n" []), .expP "el*" (.iterT (.varT "el" []) .list)]
        (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
          .seqG [.iterG (.attrG (.varE "el") (.varG "BX" []))
            (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])]])
        (.iterE (.varE "el") (.mk (.listN (.varE "n") none) [.mk "el" (.varE "el*")])) [])
      [0x00] [.list []] :=
    ⟨_, σ, _, σ₂, σ₂, _, evalArgs_typA_gramA_iff.mpr rfl, rfl, hbody, premsHold_nil_iff.mpr rfl,
      evalExp_blistResult hn hel rfl, rfl⟩
  exact (symDerives_varG hb).mpr ⟨rfl, _, by simp [blistProds], hp⟩

/-! ## `Bexpr` with no instruction -/

/-- The body of `Bexpr`, `in*:Binstr* 0x0B`. -/
def bexprBody : IL.Sym :=
  .seqG [.seqG [.iterG (.attrG (.varE "in") (.varG "Binstr" [])) (.mk .list [.mk "in" (.varE "in*")])],
    .seqG [.numG 0x0B]]

/-- The value of `Bexpr`, `in*`. -/
def bexprValue : Exp := .iterE (.varE "in") (.mk .list [.mk "in" (.varE "in*")])

/-- **`Bexpr` reads `0B` as the empty expression.** -/
theorem bexpr_end {env : Env} {q : List Param} {t : Typ}
    (hg : env.findGram? "Bexpr" = some ([], t, [.prodD q bexprBody bexprValue []])) (ρ : VarEnv) :
    SymDerives env ρ (.varG "Bexpr" []) [0x0B] [.list []] ρ := by
  let σ : VarEnv := VarEnv.empty.bindVal "in*" (.list [])
  have hI : SymDerives env VarEnv.empty (.iterG (.attrG (.varE "in") (.varG "Binstr" []))
      (.mk .list [.mk "in" (.varE "in*")])) [] [.list []] σ :=
    symDerives_iterG.mpr ⟨[], .nil, trivial, rfl, ⟨_, matchExp_varE_of_none rfl, rfl⟩⟩
  have hB : SymDerives env σ (.numG 0x0B) [0x0B] [.num (.natN 11)] σ :=
    (symDerives_numG (by decide)).mpr ⟨rfl, rfl, rfl⟩
  have hbody : SymDerives env VarEnv.empty bexprBody [0x0B] [.list [], .num (.natN 11)] σ :=
    symDerives_seqG_cons.mpr ⟨[], [.list []], σ, [0x0B], [.num (.natN 11)],
      symDerives_seqG_single hI, symDerives_seqG_single (symDerives_seqG_single hB), rfl, rfl⟩
  have hp : ProdDerives env ρ [] [] (.prodD q bexprBody bexprValue []) [0x0B] [.list []] :=
    ⟨[], VarEnv.empty, _, σ, σ, _, evalArgs_nil env ρ, rfl, hbody, premsHold_nil_iff.mpr rfl,
      evalExp_iterList_var (by decide) rfl, rfl⟩
  exact (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩

/-! ## The corrected segments -/

/-- The body of the corrected `Belem`/`Bdata`: `0:Bu32 e:Bexpr a*:Blist(Y)`. -/
def segBody (a xs T Y : IL.Id) : IL.Sym :=
  .seqG [.seqG [.attrG (.caseE "%" (.tupE [.numE (.natN 0)])) (.varG "Bu32" [])],
    .seqG [.attrG (.varE "e") (.varG "Bexpr" [])],
    .seqG [.attrG (.iterE (.varE a) (.mk .list [.mk a (.varE xs)]))
      (.varG "Blist" [.typA (.varT T []), .gramA (.varG Y [])])]]

/-- The value `C e a*`. -/
def segValue (C a xs : IL.Id) : Exp :=
  .caseE C (.tupE [.varE "e", .iterE (.varE a) (.mk .list [.mk a (.varE xs)])])

/-- Matching the literal index pattern `%(0)` against `%(0)` binds nothing. -/
theorem matchExp_case_zero {env : Env} {σ : VarEnv} :
    MatchExp env σ (.caseE "%" (.tupE [.numE (.natN 0)])) (numCase 0) σ :=
  ⟨4, by simp [matchExp, matchExps, numCase, Value.asCase?, Value.asTuple?]⟩

/-- The value of a corrected segment with an empty expression and an empty vector. -/
theorem evalExp_segValue_empty {env : Env} {σ : VarEnv} {C a xs : IL.Id} (ha : a ≠ "_")
    (he : σ.findVal? "e" = some (.list [])) (has : σ.findVal? xs = some (.list [])) :
    EvalExp env σ (segValue C a xs) (.case C (.tuple [.list [], .list []])) :=
  evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_, evalExps_cons_iff.mpr ⟨_, _,
    evalExp_varE_iff.mpr he, evalExps_cons_iff.mpr ⟨_, _, evalExp_iterList_var ha has,
      evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- The grammars a corrected segment `80 00 0B 00` goes through. -/
structure HasSegment (env : Env) : Prop where
  bu32_80 : ∀ σ, SymDerives env σ (.varG "Bu32" []) [0x80, 0x00] [numCase 0] σ
  bu32_00 : ∀ σ, SymDerives env σ (.varG "Bu32" []) [0x00] [numCase 0] σ
  blist : env.findGram? "Blist" = some (blistParams, .iterT (.varT "el" []) .list, blistProds)
  bexpr : ∃ q t, env.findGram? "Bexpr" = some ([], t, [.prodD q bexprBody bexprValue []])

/-- **A corrected segment reads `80 00 0B 00`**: index `80 00` (a non-minimal `0`), the empty
expression, the empty vector. -/
theorem segment_80 {env : Env} (h : HasSegment env) {X C a xs T Y : IL.Id} {q : List Param}
    {t : Typ} (hg : env.findGram? X = some ([], t, [.prodD q (segBody a xs T Y) (segValue C a xs) []]))
    (ha : a ≠ "_") (hfa : (VarEnv.empty.bindVal "e" (.list [])).findVal? a = none)
    (hfas : (VarEnv.empty.bindVal "e" (.list [])).findVal? xs = none)
    (has : ((VarEnv.empty.bindVal "e" (.list [])).bindVal xs (.list [])).findVal? xs =
      some (.list []))
    (hase : ((VarEnv.empty.bindVal "e" (.list [])).bindVal xs (.list [])).findVal? "e" =
      some (.list [])) (ρ : VarEnv) :
    gramRelSup env ρ (.varG X []) [0x80, 0x00, 0x0B, 0x00] (.case C (.tuple [.list [], .list []])) := by
  obtain ⟨qe, te, hbe⟩ := h.bexpr
  let σ₁ : VarEnv := VarEnv.empty.bindVal "e" (.list [])
  let σ₂ : VarEnv := σ₁.bindVal xs (.list [])
  have h₁ : SymDerives env VarEnv.empty (.attrG (.caseE "%" (.tupE [.numE (.natN 0)]))
      (.varG "Bu32" [])) [0x80, 0x00] [numCase 0] VarEnv.empty :=
    symDerives_attrG.mpr ⟨_, _, h.bu32_80 _, rfl, matchExp_case_zero⟩
  have h₂ : SymDerives env VarEnv.empty (.attrG (.varE "e") (.varG "Bexpr" [])) [0x0B]
      [.list []] σ₁ := symDerives_attrVar rfl (bexpr_end hbe VarEnv.empty)
  have h₃ : SymDerives env σ₁ (.attrG (.iterE (.varE a) (.mk .list [.mk a (.varE xs)]))
      (.varG "Blist" [.typA (.varT T []), .gramA (.varG Y [])])) [0x00] [.list []] σ₂ :=
    symDerives_attrG.mpr ⟨_, _, blist_empty h.blist h.bu32_00 _ Y σ₁, rfl,
      matchExp_iterList_var ha hfa hfas []⟩
  have hbody := symDerives_seq3 (symDerives_seqG_single h₁) (symDerives_seqG_single h₂)
    (symDerives_seqG_single h₃)
  have hp : ProdDerives env ρ [] [] (.prodD q (segBody a xs T Y) (segValue C a xs) [])
      [0x80, 0x00, 0x0B, 0x00] [.case C (.tuple [.list [], .list []])] :=
    ⟨[], VarEnv.empty, _, σ₂, σ₂, _, evalArgs_nil env ρ, rfl, hbody, premsHold_nil_iff.mpr rfl,
      evalExp_segValue_empty ha hase has, rfl⟩
  exact gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩⟩

/-! ## The pinned segments start with `0x00` -/

/-- A pinned segment production: its body starts with the byte terminal `0x00`. -/
def OrigSegShape (env : Env) (X : IL.Id) : Prop :=
  ∃ (q : List Param) (t : Typ) (rest : List IL.Sym) (e : Exp) (prems : List Prem),
    env.findGram? X = some ([], t, [.prodD q (.seqG (.seqG [.numG 0] :: rest)) e prems])

/-- **A pinned segment reads nothing that starts with `80`.** -/
theorem not_orig_segment_80 {env : Env} {X : IL.Id} (hs : OrigSegShape env X) {ρ : VarEnv}
    {bs : Grammar.Bytes} {v : Value} : ¬ gramRelSup env ρ (.varG X []) (0x80 :: bs) v := by
  obtain ⟨q, t, rest, e, prems, hg⟩ := hs
  intro h
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp h
  obtain ⟨-, p, hp, hpd⟩ := (symDerives_varG hg).mp hd
  rw [List.mem_singleton] at hp
  subst hp
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, w, -, -, hsd, -, -, -⟩ := hpd
  rw [Silmaril.SpecTec.Equiv.substSym_seqG, Silmaril.SpecTec.Equiv.substSyms_cons] at hsd
  obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, -, hb, -⟩ := symDerives_seqG_cons.mp hsd
  have h₁' : SymDerives env ρ₀ (.seqG [.numG 0]) b₁ l₁ σ₁ := h₁
  obtain ⟨rfl, -, -⟩ := (Silmaril.SpecTec.Equiv.symDerives_byteFactor (by decide)).mp h₁'
  simp at hb

/-! ## At the wasm-1.0 scripts -/

open Silmaril.SpecTec.Equiv.V1Binary (hasV1Types_v1)

theorem hasV1Types_wasm10_fixed : HasV1Types Wasm10.envFixed := by
  rw [Wasm10.envFixed, wasm10_fixed_eq]; exact hasV1Types_v1

/-- `80 00` is a (non-minimal) LEB128 `u32` encoding of `0`. -/
theorem u32_80_00 : U32 [0x80, 0x00] 0 := by
  have h : U32 [0x80, 0x00] (2 ^ 7 * 0 + ((0x80 : UInt8).toNat - 2 ^ 7)) :=
    .cont 0x80 (by decide) (by decide) (.byte 0x00 (by decide) (by decide))
  simpa using h

set_option maxRecDepth 100000 in
theorem hasSegment_wasm10_fixed : HasSegment Wasm10.envFixed where
  bu32_80 σ := (symDerives_bu32_v1 hasV1Types_wasm10_fixed hasLeb_wasm10_fixed).mpr
    ⟨rfl, 0, u32_80_00, rfl⟩
  bu32_00 σ := (symDerives_bu32_v1 hasV1Types_wasm10_fixed hasLeb_wasm10_fixed).mpr
    ⟨rfl, 0, .byte 0x00 (by decide) (by decide), rfl⟩
  blist := by rfl
  bexpr := ⟨_, _, by rfl⟩

set_option maxRecDepth 100000 in
theorem belem_shape_wasm10_fixed : ∃ q t, Wasm10.envFixed.findGram? "Belem" =
    some ([], t, [.prodD q (segBody "x" "x*" "funcidx" "Bfuncidx") (segValue "ELEM" "x" "x*") []]) :=
  ⟨_, _, by rfl⟩

set_option maxRecDepth 100000 in
theorem bdata_shape_wasm10_fixed : ∃ q t, Wasm10.envFixed.findGram? "Bdata" =
    some ([], t, [.prodD q (segBody "b" "b*" "byte" "Bbyte") (segValue "DATA" "b" "b*") []]) :=
  ⟨_, _, by rfl⟩

set_option maxRecDepth 100000 in
theorem origSegShape_belem : OrigSegShape Wasm10.envOriginal "Belem" :=
  ⟨_, _, _, _, _, by rfl⟩

set_option maxRecDepth 100000 in
theorem origSegShape_bdata : OrigSegShape Wasm10.envOriginal "Bdata" :=
  ⟨_, _, _, _, _, by rfl⟩

/-- The bytes `80 00 0B 00`. -/
def seg80 : Grammar.Bytes := [0x80, 0x00, 0x0B, 0x00]

/-- **#690 repaired, `Belem`**: the corrected theory entails `Belem ⊢ 80 00 0B 00 ↦ ELEM [] []`. -/
theorem belem_80_fixed (ρ : VarEnv) : Entails (scriptAxioms Wasm10.envFixed)
    (derivesNT "Belem" [] ρ seg80 (.case "ELEM" (.tuple [.list [], .list []]))) := by
  obtain ⟨q, t, hg⟩ := belem_shape_wasm10_fixed
  exact (gramRelSup_varG_iff_entails ..).mp
    (segment_80 hasSegment_wasm10_fixed hg (by decide) rfl rfl rfl rfl ρ)

/-- **#690 repaired, `Bdata`**: the corrected theory entails `Bdata ⊢ 80 00 0B 00 ↦ DATA [] []`. -/
theorem bdata_80_fixed (ρ : VarEnv) : Entails (scriptAxioms Wasm10.envFixed)
    (derivesNT "Bdata" [] ρ seg80 (.case "DATA" (.tuple [.list [], .list []]))) := by
  obtain ⟨q, t, hg⟩ := bdata_shape_wasm10_fixed
  exact (gramRelSup_varG_iff_entails ..).mp
    (segment_80 hasSegment_wasm10_fixed hg (by decide) rfl rfl rfl rfl ρ)

/-- **#690 in the pinned theory, `Belem`**: it entails nothing about `80 00 0B 00`. -/
theorem belem_80_not_original (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Belem" [] ρ seg80 v) := fun h =>
  not_orig_segment_80 origSegShape_belem ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **#690 in the pinned theory, `Bdata`**: it entails nothing about `80 00 0B 00`. -/
theorem bdata_80_not_original (ρ : VarEnv) (v : Value) :
    ¬ Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Bdata" [] ρ seg80 v) := fun h =>
  not_orig_segment_80 origSegShape_bdata ((gramRelSup_varG_iff_entails ..).mpr h)

end Silmaril.Wasm.SpecTec.GrammarInst
