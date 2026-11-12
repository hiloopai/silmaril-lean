module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.SegmentsV1
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Wasm20
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20

/-!
# #671 in the byte grammar institution: element segment kind 6 of wasm-2.0

The pinned kind-6 `Belem` production (`A-binary.spectec:873-874`) reads
`6:Bu32 x:Btableidx expr:Bexpr e*:Blist(Bexpr)` and returns `ELEM FUNCREF e* (ACTIVE x expr)`;
#671 inserts `rt:Breftype` before the vector and returns `ELEM rt …`.

* `belem_kind6_fixed`: the corrected theory entails
  `Belem ⊢ 06 00 0B 6F 00 ↦ ELEM EXTERNREF [] (ACTIVE %(0) [])` — kind 6, table 0, the empty
  offset expression, `externref`, the empty vector.
* `belem_kind6_not_original`: the pinned theory does not. Every pinned production starts with
  `k:Bu32` for a literal `k`, and a `Bu32` read from bytes starting with `06` is `6`
  (`u32_head_06`), so only kind 6 applies, and its value begins `ELEM FUNCREF`.
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
open Silmaril.SpecTec.Equiv.BinaryModule (matchExp_iterList_var evalExp_iterList_var)
open Silmaril.SpecTec.Equiv.Wasm20 (HasV2Types symDerives_bu32_v2 symDerives_breftype_v2
  hasV2Types_pinned_v2 hasV2Types_v2)

/-! ## The leading `Bu32` -/

/-- A `u32` whose encoding starts with `06` is `6`. -/
theorem u32_head_06 {b c rest : Grammar.Bytes} {m : Nat} (h : U32 b m)
    (hb : b ++ c = 0x06 :: rest) : m = 6 := by
  cases h with
  | byte n h₁ h₂ =>
      have hn : n = 0x06 := (List.cons.inj hb).1
      rw [hn]
      rfl
  | cont n h₁ h₂ _ =>
      have hn : n = 0x06 := (List.cons.inj hb).1
      rw [hn] at h₁
      exact absurd h₁ (by decide)

/-- Matching the literal pattern `%(k)` against `%(m)` forces `k = m`. -/
theorem matchExp_case_num_elim {env : Env} {σ σ' : VarEnv} {k m : Nat}
    (h : MatchExp env σ (.caseE "%" (.tupE [.numE (.natN k)])) (numCase m) σ') : k = m := by
  obtain ⟨n, h⟩ := h
  have h4 : matchExp (n + 4) env σ (.caseE "%" (.tupE [.numE (.natN k)])) (numCase m) = .ok σ' :=
    matchExp_ok_of_le (by omega) h
  simp [matchExp, matchExps, numCase, Value.asCase?, Value.asTuple?] at h4
  omega

/-- A segment production `k:Bu32 …`. -/
def kindProd (q : List Param) (k : Nat) (rest : List IL.Sym) (e : Exp) (prems : List Prem) :
    IL.Prod :=
  .prodD q (.seqG (.seqG [.attrG (.caseE "%" (.tupE [.numE (.natN k)])) (.varG "Bu32" [])] :: rest))
    e prems

/-- **A production `k:Bu32 …` reading bytes that start with `06` has `k = 6`.** -/
theorem kind_eq_six {env : Env} (h : HasV2Types env) (hl : HasLeb env) {ρ : VarEnv}
    {q : List Param} {k : Nat} {rest : List IL.Sym} {e : Exp} {prems : List Prem}
    {bs : Grammar.Bytes} {l : List Value}
    (hd : ProdDerives env ρ [] [] (kindProd q k rest e prems) (0x06 :: bs) l) : k = 6 := by
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩ := hd
  rw [Silmaril.SpecTec.Equiv.substSym_seqG, Silmaril.SpecTec.Equiv.substSyms_cons] at hs
  obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, -, hb, -⟩ := symDerives_seqG_cons.mp hs
  have h₁' : SymDerives env ρ₀ (.seqG [.attrG (.caseE "%" (.tupE [.numE (.natN k)]))
      (.varG "Bu32" [])]) b₁ l₁ σ₁ := h₁
  obtain ⟨u, σ, hbu, -, hm⟩ := symDerives_attrG.mp (Silmaril.SpecTec.Equiv.symDerives_seq1.mp h₁')
  obtain ⟨-, m, hU, hu⟩ := (symDerives_bu32_v2 h hl).mp hbu
  have hm6 : m = 6 := u32_head_06 hU hb.symm
  rw [List.singleton_inj.mp hu, hm6] at hm
  exact matchExp_case_num_elim hm

/-! ## The pinned `Belem` -/

/-- The pinned kind-6 value, `ELEM FUNCREF e₂ e₃`. -/
def funcrefValue (e₂ e₃ : Exp) : Exp := .caseE "ELEM" (.tupE [.caseE "FUNCREF" (.tupE []), e₂, e₃])

/-- The pinned wasm-2.0 `Belem`: eight productions `k:Bu32 …`, `k = 0, …, 7`, the kind-6 one
with value `ELEM FUNCREF …`. -/
def OrigBelemV2Shape (env : Env) : Prop :=
  ∃ (t : Typ) (q₀ q₁ q₂ q₃ q₄ q₅ q₆ q₇ : List Param) (r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : List IL.Sym)
    (e₀ e₁ e₂ e₃ e₄ e₅ e₇ f₂ f₃ : Exp) (p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ : List Prem),
    env.findGram? "Belem" = some ([], t, [kindProd q₀ 0 r₀ e₀ p₀, kindProd q₁ 1 r₁ e₁ p₁,
      kindProd q₂ 2 r₂ e₂ p₂, kindProd q₃ 3 r₃ e₃ p₃, kindProd q₄ 4 r₄ e₄ p₄,
      kindProd q₅ 5 r₅ e₅ p₅, kindProd q₆ 6 r₆ (funcrefValue f₂ f₃) p₆, kindProd q₇ 7 r₇ e₇ p₇])

set_option maxRecDepth 100000 in
theorem origBelemV2Shape_original : OrigBelemV2Shape Wasm20.envOriginal :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, by rfl⟩

/-- The value `ELEM FUNCREF …` is not `ELEM EXTERNREF …`. -/
theorem not_evalExp_funcrefValue {env : Env} {σ : VarEnv} {e₂ e₃ : Exp} {w₂ w₃ : Value} :
    ¬ EvalExp env σ (funcrefValue e₂ e₃)
      (.case "ELEM" (.tuple [.case "EXTERNREF" (.tuple []), w₂, w₃])) := by
  intro h
  obtain ⟨u, hu, hc⟩ := evalExp_caseE_iff.mp h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.mp hu
  obtain ⟨a, as₁, ha, -, rfl⟩ := evalExps_cons_iff.mp hvs
  obtain ⟨b, hb, rfl⟩ := evalExp_caseE_iff.mp ha
  simp at hc

/-- The pinned kind-6 production yields no `ELEM EXTERNREF …`. -/
theorem not_kind6_funcref {env : Env} {ρ : VarEnv} {q : List Param} {r : List IL.Sym}
    {f₂ f₃ : Exp} {pr : List Prem} {bs : Grammar.Bytes} {w₂ w₃ : Value} :
    ¬ ProdDerives env ρ [] [] (kindProd q 6 r (funcrefValue f₂ f₃) pr) bs
      [.case "ELEM" (.tuple [.case "EXTERNREF" (.tuple []), w₂, w₃])] := by
  rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, -, -, hev, hl'⟩
  rw [← List.singleton_inj.mp hl'] at hev
  exact not_evalExp_funcrefValue hev

/-- **The pinned `Belem` reads no `06 …` as `ELEM EXTERNREF …`.** -/
theorem not_orig_belem_kind6 {env : Env} (hs : OrigBelemV2Shape env) (h : HasV2Types env)
    (hl : HasLeb env) {ρ : VarEnv} {bs : Grammar.Bytes} {w₂ w₃ : Value} :
    ¬ gramRelSup env ρ (.varG "Belem" []) (0x06 :: bs)
      (.case "ELEM" (.tuple [.case "EXTERNREF" (.tuple []), w₂, w₃])) := by
  obtain ⟨t, q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇, r₀, r₁, r₂, r₃, r₄, r₅, r₆, r₇, e₀, e₁, e₂, e₃,
    e₄, e₅, e₇, f₂, f₃, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, hg⟩ := hs
  intro hv
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hv
  obtain ⟨-, p, hp, hpd⟩ := (symDerives_varG hg).mp hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hk : ∀ {q : List Param} {k : Nat} {r : List IL.Sym} {e : Exp} {pr : List Prem}
      {l : List Value}, k ≠ 6 → ¬ ProdDerives env ρ [] [] (kindProd q k r e pr) (0x06 :: bs) l :=
    fun hk hd => hk (kind_eq_six h hl hd)
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hk (by decide) hpd
  · exact hk (by decide) hpd
  · exact hk (by decide) hpd
  · exact hk (by decide) hpd
  · exact hk (by decide) hpd
  · exact hk (by decide) hpd
  · exact not_kind6_funcref hpd
  · exact hk (by decide) hpd

/-! ## The corrected kind 6 -/

/-- The corrected kind-6 body `6:Bu32 x:Btableidx expr:Bexpr rt:Breftype e*:Blist(Bexpr)`. -/
def kind6Body : IL.Sym :=
  .seqG [.seqG [.attrG (.caseE "%" (.tupE [.numE (.natN 6)])) (.varG "Bu32" [])],
    .seqG [.attrG (.varE "x") (.varG "Btableidx" [])],
    .seqG [.attrG (.varE "expr") (.varG "Bexpr" [])],
    .seqG [.attrG (.varE "rt") (.varG "Breftype" [])],
    .seqG [.attrG (.iterE (.varE "e") (.mk .list [.mk "e" (.varE "e*")]))
      (.varG "Blist" [.typA (.varT "expr" []), .gramA (.varG "Bexpr" [])])]]

/-- The corrected kind-6 value `ELEM rt e* (ACTIVE x expr)`. -/
def kind6Value : Exp :=
  .caseE "ELEM" (.tupE [.varE "rt", .iterE (.varE "e") (.mk .list [.mk "e" (.varE "e*")]),
    .caseE "ACTIVE" (.tupE [.varE "x", .varE "expr"])])

/-- The corrected wasm-2.0 `Belem`: the kind-6 production is the seventh. -/
def FixedBelemV2Shape (env : Env) : Prop :=
  ∃ (t : Typ) (pre post : List IL.Prod) (q : List Param),
    env.findGram? "Belem" = some ([], t, pre ++ .prodD q kind6Body kind6Value [] :: post)

set_option maxRecDepth 100000 in
theorem fixedBelemV2Shape_fixed : FixedBelemV2Shape Wasm20.envFixed :=
  ⟨_, [_, _, _, _, _, _], _, _, by rfl⟩

theorem hasV2Types_fixed : HasV2Types Wasm20.envFixed := by
  rw [Wasm20.envFixed, wasm20_fixed_eq]; exact hasV2Types_v2

set_option maxRecDepth 100000 in
theorem btableidx_shape_fixed : ∃ q t, Wasm20.envFixed.findGram? "Btableidx" =
    some ([], t, [.prodD q (.attrG (.varE "x") (.varG "Bu32" [])) (.varE "x") []]) :=
  ⟨_, _, by rfl⟩

/-- The target value `ELEM EXTERNREF [] (ACTIVE %(0) [])`. -/
def kind6Target : Value :=
  .case "ELEM" (.tuple [.case "EXTERNREF" (.tuple []), .list [],
    .case "ACTIVE" (.tuple [numCase 0, .list []])])

/-- The bytes `06 00 0B 6F 00`. -/
def kind6Bytes : Grammar.Bytes := [0x06, 0x00, 0x0B, 0x6F, 0x00]

/-- The scope the corrected kind-6 body leaves. -/
def kind6Scope : VarEnv :=
  (((VarEnv.empty.bindVal "x" (numCase 0)).bindVal "expr" (.list [])).bindVal "rt"
    (.case "EXTERNREF" (.tuple []))).bindVal "e*" (.list [])

/-- The value, evaluated in that scope. -/
theorem evalExp_kind6Value {env : Env} : EvalExp env kind6Scope kind6Value kind6Target := by
  have hrt : EvalExp env kind6Scope (.varE "rt") (.case "EXTERNREF" (.tuple [])) :=
    evalExp_varE_iff.mpr rfl
  have he : EvalExp env kind6Scope (.iterE (.varE "e") (.mk .list [.mk "e" (.varE "e*")]))
      (.list []) := evalExp_iterList_var (by decide) rfl
  have ha : EvalExp env kind6Scope (.caseE "ACTIVE" (.tupE [.varE "x", .varE "expr"]))
      (.case "ACTIVE" (.tuple [numCase 0, .list []])) :=
    evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_, evalExps_cons_iff.mpr ⟨_, _,
      evalExp_varE_iff.mpr rfl, evalExps_cons_iff.mpr ⟨_, _, evalExp_varE_iff.mpr rfl,
        evalExps_nil_iff.mpr rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_, evalExps_cons_iff.mpr ⟨_, _, hrt,
    evalExps_cons_iff.mpr ⟨_, _, he, evalExps_cons_iff.mpr ⟨_, _, ha, evalExps_nil_iff.mpr rfl,
      rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- A five-factor sequence. -/
theorem symDerives_seq5 {env : Env} {ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ₅ : VarEnv} {g₁ g₂ g₃ g₄ g₅ : IL.Sym}
    {b₁ b₂ b₃ b₄ b₅ : Grammar.Bytes} {l₁ l₂ l₃ l₄ l₅ : List Value}
    (h₁ : SymDerives env ρ g₁ b₁ l₁ ρ₁) (h₂ : SymDerives env ρ₁ g₂ b₂ l₂ ρ₂)
    (h₃ : SymDerives env ρ₂ g₃ b₃ l₃ ρ₃) (h₄ : SymDerives env ρ₃ g₄ b₄ l₄ ρ₄)
    (h₅ : SymDerives env ρ₄ g₅ b₅ l₅ ρ₅) :
    SymDerives env ρ (.seqG [g₁, g₂, g₃, g₄, g₅]) (b₁ ++ (b₂ ++ (b₃ ++ (b₄ ++ b₅))))
      (l₁ ++ (l₂ ++ (l₃ ++ (l₄ ++ l₅)))) ρ₅ :=
  symDerives_seqG_cons.mpr ⟨_, _, _, _, _, h₁, symDerives_seqG_cons.mpr ⟨_, _, _, _, _, h₂,
    symDerives_seqG_cons.mpr ⟨_, _, _, _, _, h₃, symDerives_seqG_cons.mpr ⟨_, _, _, _, _, h₄,
      symDerives_seqG_single h₅, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩

/-- Matching the literal pattern `%(k)` against `%(k)` binds nothing. -/
theorem matchExp_case_lit {env : Env} {σ : VarEnv} (k : Nat) :
    MatchExp env σ (.caseE "%" (.tupE [.numE (.natN k)])) (numCase k) σ :=
  ⟨4, by simp [matchExp, matchExps, numCase, Value.asCase?, Value.asTuple?]⟩

/-- **The corrected kind-6 production reads `06 00 0B 6F 00` as
`ELEM EXTERNREF [] (ACTIVE %(0) [])`.** -/
theorem belem_kind6 {env : Env} (hs : FixedBelemV2Shape env) (h : HasV2Types env)
    (hl : HasLeb env) (hsg : HasSegment env)
    (hti : ∃ q t, env.findGram? "Btableidx" =
      some ([], t, [.prodD q (.attrG (.varE "x") (.varG "Bu32" [])) (.varE "x") []]))
    (ρ : VarEnv) : gramRelSup env ρ (.varG "Belem" []) kind6Bytes kind6Target := by
  obtain ⟨t, pre, post, q, hg⟩ := hs
  obtain ⟨qt, tt, hti⟩ := hti
  obtain ⟨qe, te, hbe⟩ := hsg.bexpr
  have hu6 : ∀ σ, SymDerives env σ (.varG "Bu32" []) [0x06] [numCase 6] σ := fun σ =>
    (symDerives_bu32_v2 h hl).mpr ⟨rfl, 6, .byte 0x06 (by decide) (by decide), rfl⟩
  have hidx : ∀ σ, SymDerives env σ (.varG "Btableidx" []) [0x00] [numCase 0] σ := fun σ => by
    have hp : ProdDerives env σ [] [] (.prodD qt (.attrG (.varE "x") (.varG "Bu32" [])) (.varE "x")
        []) [0x00] [numCase 0] :=
      ⟨[], VarEnv.empty, _, _, _, _, evalArgs_nil env σ, rfl,
        symDerives_attrVar rfl (hsg.bu32_00 _), premsHold_nil_iff.mpr rfl,
        evalExp_varE_iff.mpr rfl, rfl⟩
    exact (symDerives_varG hti).mpr ⟨rfl, _, by simp, hp⟩
  have hrt : ∀ σ, SymDerives env σ (.varG "Breftype" []) [0x6F]
      [.case "EXTERNREF" (.tuple [])] σ := fun σ =>
    (symDerives_breftype_v2 h).mpr ⟨rfl, .inr ⟨rfl, rfl⟩⟩
  let σ₁ : VarEnv := VarEnv.empty.bindVal "x" (numCase 0)
  let σ₂ : VarEnv := σ₁.bindVal "expr" (.list [])
  let σ₃ : VarEnv := σ₂.bindVal "rt" (.case "EXTERNREF" (.tuple []))
  have f₁ : SymDerives env VarEnv.empty (.attrG (.caseE "%" (.tupE [.numE (.natN 6)]))
      (.varG "Bu32" [])) [0x06] [numCase 6] VarEnv.empty :=
    symDerives_attrG.mpr ⟨_, _, hu6 VarEnv.empty, rfl, matchExp_case_lit 6⟩
  have f₂ : SymDerives env VarEnv.empty (.attrG (.varE "x") (.varG "Btableidx" [])) [0x00]
      [numCase 0] σ₁ := symDerives_attrVar rfl (hidx _)
  have f₃ : SymDerives env σ₁ (.attrG (.varE "expr") (.varG "Bexpr" [])) [0x0B] [.list []] σ₂ :=
    symDerives_attrVar rfl (bexpr_end hbe _)
  have f₄ : SymDerives env σ₂ (.attrG (.varE "rt") (.varG "Breftype" [])) [0x6F]
      [.case "EXTERNREF" (.tuple [])] σ₃ := symDerives_attrVar rfl (hrt _)
  have f₅ : SymDerives env σ₃ (.attrG (.iterE (.varE "e") (.mk .list [.mk "e" (.varE "e*")]))
      (.varG "Blist" [.typA (.varT "expr" []), .gramA (.varG "Bexpr" [])])) [0x00] [.list []]
      kind6Scope :=
    symDerives_attrG.mpr ⟨_, _, blist_empty hsg.blist hsg.bu32_00 (.varT "expr" []) "Bexpr" _,
      rfl, matchExp_iterList_var (by decide) rfl rfl []⟩
  have hbody := symDerives_seq5 (symDerives_seqG_single f₁) (symDerives_seqG_single f₂)
    (symDerives_seqG_single f₃) (symDerives_seqG_single f₄) (symDerives_seqG_single f₅)
  have hp : ProdDerives env ρ [] [] (.prodD q kind6Body kind6Value []) kind6Bytes [kind6Target] :=
    ⟨[], VarEnv.empty, _, kind6Scope, kind6Scope, _, evalArgs_nil env ρ, rfl, hbody,
      premsHold_nil_iff.mpr rfl, evalExp_kind6Value, rfl⟩
  exact gramRelSup_iff.mpr ⟨ρ, (symDerives_varG hg).mpr ⟨rfl, _, by simp, hp⟩⟩

/-! ## At the wasm-2.0 scripts -/

theorem hasV2Types_original : HasV2Types Wasm20.envOriginal := by
  rw [Wasm20.envOriginal, wasm20_original_eq]; exact hasV2Types_pinned_v2

set_option maxRecDepth 100000 in
theorem hasSegment_wasm20_fixed : HasSegment Wasm20.envFixed where
  bu32_80 σ := (symDerives_bu32_v2 hasV2Types_fixed hasLeb_wasm20_fixed).mpr
    ⟨rfl, 0, u32_80_00, rfl⟩
  bu32_00 σ := (symDerives_bu32_v2 hasV2Types_fixed hasLeb_wasm20_fixed).mpr
    ⟨rfl, 0, .byte 0x00 (by decide) (by decide), rfl⟩
  blist := by rfl
  bexpr := ⟨_, _, by rfl⟩

/-- **#671 repaired**: the corrected wasm-2.0 theory entails
`Belem ⊢ 06 00 0B 6F 00 ↦ ELEM EXTERNREF [] (ACTIVE %(0) [])`. -/
theorem belem_kind6_fixed (ρ : VarEnv) :
    Entails (scriptAxioms Wasm20.envFixed) (derivesNT "Belem" [] ρ kind6Bytes kind6Target) :=
  (gramRelSup_varG_iff_entails ..).mp (belem_kind6 fixedBelemV2Shape_fixed hasV2Types_fixed
    hasLeb_wasm20_fixed hasSegment_wasm20_fixed btableidx_shape_fixed ρ)

/-- **#671 in the pinned theory**: it does not entail that sentence. -/
theorem belem_kind6_not_original (ρ : VarEnv) :
    ¬ Entails (scriptAxioms Wasm20.envOriginal) (derivesNT "Belem" [] ρ kind6Bytes kind6Target) :=
  fun h => not_orig_belem_kind6 origBelemV2Shape_original hasV2Types_original
    hasLeb_wasm20_original ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **#671 separates the wasm-2.0 theories at `Belem`.** -/
theorem wasm20_fixed_not_below_original_671 :
    ¬ ∀ ψ ∈ scriptAxioms Wasm20.envFixed, Entails (scriptAxioms Wasm20.envOriginal) ψ :=
  not_entailsAll_of_separates (belem_kind6_fixed VarEnv.empty)
    (belem_kind6_not_original VarEnv.empty)

end Silmaril.Wasm.SpecTec.GrammarInst
