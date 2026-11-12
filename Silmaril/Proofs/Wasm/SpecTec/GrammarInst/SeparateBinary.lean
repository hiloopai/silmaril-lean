module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Separate
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryInstr
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Wasm20
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20

/-!
# Separating sentences for the wasm-1.0 and wasm-2.0 errata

`Errata.lean` shows that the wasm-1.0 and wasm-2.0 errata change the grammar theory at exactly
their grammar targets. This module gives, for each version, a pair of sentences that separate
the original and the fixed theories, both at `Binstr`.

* **wasm-1.0, #686.** The pinned `0xBB => CVTOP F32 F64 PROMOTE` is corrected to
  `CVTOP F64 F32 PROMOTE`. `0xBB` is the only `Binstr` production with leading byte `0xBB` in
  either script (`binstrOps`, computed by `rfl`), so each theory reads `[0xBB]` as exactly its
  own value (`binstr_BB_original_iff`, `binstr_BB_fixed_iff`).
* **wasm-2.0, #670.** The pinned `Binstr` gives `0xFD 92:Bu32` twice, for `VLOAD V128 (ZERO 32)`
  and `VLOAD V128 (ZERO 64)`; the fix moves the second to `0xFD 93`. The original theory entails
  `Binstr ⊢ FD 5C 00 00 ↦ VLOAD V128 (ZERO 64) {ALIGN 0, OFFSET 0}` and the fixed one does
  not; the fixed one entails the same at `FD 5D 00 00` and the original does not. The negative
  halves filter the `0xFD` productions by their value (`mayEval`, a sound over-approximation
  of evaluation, checked by `rfl` over all of them) and then read the `Bu32` opcode.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts
open Silmaril.Wasm.Binary (U32 UN)
open Silmaril.SpecTec.Equiv (HasBinstr binstrOps binstrProds prodLead symDerives_binstr_cons)

/-! ## A `Binstr` lead byte with a single literal production -/

/-- The value of a production. -/
def prodValue : IL.Prod → Exp
  | .prodD _ _ e _ => e

/-- A production that reads one byte `n` and has the literal value `lit v`. -/
def byteLitProd (n : Nat) (v : Value) : IL.Prod := .prodD [] (.numG n) (lit v) []

/-- **A lead byte with one literal production.** If the only `Binstr` production with leading
byte `c` is `c => v`, then `Binstr` reads `[c]` as `w` exactly when `w = v`. -/
theorem binstr_single_iff {env : Env} (hb : HasBinstr env) {c : UInt8} {v : Value}
    (hops : binstrOps env c = [byteLitProd c.toNat v]) (ρ : VarEnv) (w : Value) :
    gramRelSup env ρ (.varG "Binstr" []) [c] w ↔ w = v := by
  rw [gramRelSup_iff]
  constructor
  · rintro ⟨ρ', hd⟩
    obtain ⟨-, p, hp, hdd⟩ := (symDerives_binstr_cons hb).mp hd
    rw [hops, List.mem_singleton] at hp
    subst hp
    obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, u, -, -, -, -, hu, hl⟩ := hdd
    obtain rfl : w = u := List.singleton_inj.mp hl
    exact EvalExp.unique hu (evalExp_lit env ρ₂ v)
  · rintro rfl
    have hd : ProdDerives env ρ [] [] (byteLitProd c.toNat w) [c] [w] :=
      ⟨[], VarEnv.empty, _, VarEnv.empty, VarEnv.empty, w, evalArgs_nil env ρ, rfl,
        (symDerives_numG c.toNat_lt_size).mpr ⟨by simp, rfl, rfl⟩,
        premsHold_nil_iff.mpr rfl, evalExp_lit env _ w, rfl⟩
    exact ⟨ρ, (symDerives_binstr_cons hb).mpr ⟨rfl, _, by rw [hops]; simp, hd⟩⟩

/-! ## wasm-1.0, #686 -/

/-- A nullary constructor value. -/
def con (op : MixopS) : Value := .case op (.tuple [])

/-- `CVTOP t₁ t₂ PROMOTE`. -/
def cvtPromote (t₁ t₂ : MixopS) : Value :=
  .case "CVTOP" (.tuple [con t₁, con t₂, con "PROMOTE"])

/-- The pinned `0xBB` instruction, `CVTOP F32 F64 PROMOTE` (`A-binary.spectec:382`). -/
abbrev promoteO : Value := cvtPromote "F32" "F64"

/-- The corrected `0xBB` instruction, `CVTOP F64 F32 PROMOTE` (`f64.promote_f32`). -/
abbrev promoteF : Value := cvtPromote "F64" "F32"

set_option maxRecDepth 100000 in
theorem hasBinstr_wasm10_original : HasBinstr Wasm10.envOriginal := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hasBinstr_wasm10_fixed : HasBinstr Wasm10.envFixed := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem binstrOps_BB_wasm10_original :
    binstrOps Wasm10.envOriginal 0xBB = [byteLitProd 0xBB promoteO] := rfl

set_option maxRecDepth 100000 in
theorem binstrOps_BB_wasm10_fixed :
    binstrOps Wasm10.envFixed 0xBB = [byteLitProd 0xBB promoteF] := rfl

/-- **The pinned wasm-1.0 `Binstr` reads `0xBB` as `CVTOP F32 F64 PROMOTE` and nothing else.** -/
theorem binstr_BB_original_iff (ρ : VarEnv) (w : Value) :
    gramRelSup Wasm10.envOriginal ρ (.varG "Binstr" []) [0xBB] w ↔ w = promoteO :=
  binstr_single_iff hasBinstr_wasm10_original binstrOps_BB_wasm10_original ρ w

/-- **The fixed wasm-1.0 `Binstr` reads `0xBB` as `CVTOP F64 F32 PROMOTE` and nothing else.** -/
theorem binstr_BB_fixed_iff (ρ : VarEnv) (w : Value) :
    gramRelSup Wasm10.envFixed ρ (.varG "Binstr" []) [0xBB] w ↔ w = promoteF :=
  binstr_single_iff hasBinstr_wasm10_fixed binstrOps_BB_wasm10_fixed ρ w

theorem promoteO_ne_promoteF : promoteO ≠ promoteF := by
  simp [cvtPromote, con]

/-- **The wasm-1.0 errata give an incomparable theory**: the original entails
`Binstr ⊢ BB ↦ CVTOP F32 F64 PROMOTE` and the fixed one does not; the fixed one entails
`Binstr ⊢ BB ↦ CVTOP F64 F32 PROMOTE` and the original does not. -/
theorem wasm10_errata_incomparable :
    (¬ ∀ ψ ∈ scriptAxioms Wasm10.envOriginal, Entails (scriptAxioms Wasm10.envFixed) ψ) ∧
      (¬ ∀ ψ ∈ scriptAxioms Wasm10.envFixed, Entails (scriptAxioms Wasm10.envOriginal) ψ) := by
  let ρ := VarEnv.empty
  have hO : Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Binstr" [] ρ [0xBB] promoteO) :=
    (gramRelSup_varG_iff_entails ..).mp ((binstr_BB_original_iff ρ _).mpr rfl)
  have hF : Entails (scriptAxioms Wasm10.envFixed) (derivesNT "Binstr" [] ρ [0xBB] promoteF) :=
    (gramRelSup_varG_iff_entails ..).mp ((binstr_BB_fixed_iff ρ _).mpr rfl)
  have nF : ¬ Entails (scriptAxioms Wasm10.envFixed) (derivesNT "Binstr" [] ρ [0xBB] promoteO) :=
    fun h => promoteO_ne_promoteF ((binstr_BB_fixed_iff ρ _).mp
      ((gramRelSup_varG_iff_entails ..).mpr h))
  have nO : ¬ Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Binstr" [] ρ [0xBB] promoteF) :=
    fun h => promoteO_ne_promoteF ((binstr_BB_original_iff ρ _).mp
      ((gramRelSup_varG_iff_entails ..).mpr h)).symm
  exact ⟨not_entailsAll_of_separates hO nF, not_entailsAll_of_separates hF nO⟩

/-! ## A sound over-approximation of evaluation -/

/-- `mayEvalL f es vs`: the lists have the same length and `f` holds pointwise. -/
def mayEvalL (f : Exp → Value → Bool) : List Exp → List Value → Bool
  | [], [] => true
  | e :: es, w :: ws => f e w && mayEvalL f es ws
  | _, _ => false

/-- `mayEval k e v = false` means `e` cannot evaluate to `v`: the head constructors of tuples,
injections, options and numerals are compared down to depth `k`; everything else may evaluate
to anything. -/
def mayEval : Nat → Exp → Value → Bool
  | 0, _, _ => true
  | k + 1, .caseE op e, .case op' w => op == op' && mayEval k e w
  | _ + 1, .caseE _ _, _ => false
  | k + 1, .tupE es, .tuple ws => mayEvalL (mayEval k) es ws
  | _ + 1, .tupE _, _ => false
  | _ + 1, .optE none, .opt none => true
  | k + 1, .optE (some e), .opt (some w) => mayEval k e w
  | _ + 1, .optE _, _ => false
  | _ + 1, .numE m, .num m' => decide (m = m')
  | _ + 1, .numE _, _ => false
  | _ + 1, _, _ => true

/-- An empty expression list denotes only the empty list. -/
theorem evalExps_nil_inv {env : Env} {ρ : VarEnv} {vs : List Value}
    (h : EvalExps env ρ [] vs) : vs = [] := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [evalExps] at h
  | succ n => rw [evalExps_nil_eq] at h; exact (Except.ok.inj h).symm

/-- `optE (some e)` denotes `some` of what `e` denotes. -/
theorem evalExp_optSome_inv {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ (.optE (some e)) v) : ∃ w, EvalExp env ρ e w ∧ v = .opt (some w) := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [evalExp] at h
  | succ n =>
    simp only [evalExp, Res.map_eq_ok] at h
    obtain ⟨w, hw, rfl⟩ := h
    exact ⟨w, ⟨n, hw⟩, rfl⟩

/-- `optE none` denotes `none`. -/
theorem evalExp_optNone_inv {env : Env} {ρ : VarEnv} {v : Value}
    (h : EvalExp env ρ (.optE none) v) : v = .opt none := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [evalExp] at h
  | succ n => simp only [evalExp] at h; exact (Except.ok.inj h).symm

theorem mayEvalL_sound {env : Env} {ρ : VarEnv} {f : Exp → Value → Bool}
    (hf : ∀ e w, EvalExp env ρ e w → f e w = true) :
    ∀ (es : List Exp) (vs : List Value), EvalExps env ρ es vs → mayEvalL f es vs = true
  | [], vs, h => by rw [evalExps_nil_inv h]; rfl
  | e :: es, vs, h => by
    obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.mp h
    simp [mayEvalL, hf e w hw, mayEvalL_sound hf es ws hws]

theorem mayEval_caseE_sound {env : Env} {ρ : VarEnv} {k : Nat} {op : MixopS} {e : Exp}
    {v : Value} (ih : ∀ w, EvalExp env ρ e w → mayEval k e w = true)
    (h : EvalExp env ρ (.caseE op e) v) : mayEval (k + 1) (.caseE op e) v = true := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.mp h
  simp [mayEval, ih w hw]

theorem mayEval_optE_sound {env : Env} {ρ : VarEnv} {k : Nat} {o : Option Exp} {v : Value}
    (ih : ∀ e w, EvalExp env ρ e w → mayEval k e w = true)
    (h : EvalExp env ρ (.optE o) v) : mayEval (k + 1) (.optE o) v = true := by
  cases o with
  | none => rw [evalExp_optNone_inv h]; rfl
  | some e =>
    obtain ⟨w, hw, rfl⟩ := evalExp_optSome_inv h
    simp [mayEval, ih e w hw]

/-- **`mayEval` is sound**: what an expression evaluates to, it may evaluate to. -/
theorem mayEval_sound {env : Env} {ρ : VarEnv} :
    ∀ (k : Nat) (e : Exp) (v : Value), EvalExp env ρ e v → mayEval k e v = true
  | 0, _, _, _ => rfl
  | k + 1, e, v, h => by
    cases e <;> try rfl
    case caseE op e => exact mayEval_caseE_sound (mayEval_sound k e) h
    case optE o => exact mayEval_optE_sound (mayEval_sound k) h
    case numE m =>
      obtain rfl := evalExp_numE_iff.mp h
      simp [mayEval]
    case tupE es =>
      obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.mp h
      simpa [mayEval] using mayEvalL_sound (mayEval_sound k) es vs hvs

/-- A production derives a value its expression may evaluate to. -/
theorem mayEval_of_prodDerives {env : Env} {ρ : VarEnv} {ps : List Param} {args : List IL.Arg}
    {p : IL.Prod} {bs : Grammar.Bytes} {v : Value} (h : ProdDerives env ρ ps args p bs [v])
    (k : Nat) : mayEval k (prodValue p) v = true := by
  obtain ⟨q, g, e, prems⟩ := p
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, u, -, -, -, -, hu, hl⟩ := h
  obtain rfl : v = u := List.singleton_inj.mp hl
  exact mayEval_sound k e v hu

/-! ## Productions by printed equality -/

/-- Two `Binstr` productions are equal, decided through the printer (`IL.defEq`). -/
def prodEq (p q : IL.Prod) : Bool :=
  defEq (.gramD "Binstr" [] (.varT "instr" []) [p]) (.gramD "Binstr" [] (.varT "instr" []) [q])

theorem eq_of_prodEq {p q : IL.Prod} (h : prodEq p q = true) : p = q := by
  have h' := defEq_iff.mp h
  simp only [Def.gramD.injEq, List.cons.injEq, and_true, true_and] at h'
  exact h'

/-- **The value filter at a lead byte.** Every production with leading byte `c` either cannot
yield `v` or is `q`. -/
def onlyProdYields (env : Env) (c : UInt8) (v : Value) (q : IL.Prod) : Bool :=
  (binstrOps env c).all fun p => !mayEval 6 (prodValue p) v || prodEq p q

/-- So a derivation of `c :: r` with value `v` is a derivation by `q`. -/
theorem prodDerives_of_onlyProdYields {env : Env} (hb : HasBinstr env) {c : UInt8} {v : Value}
    {q : IL.Prod} (hq : onlyProdYields env c v q = true) {ρ : VarEnv} {r : Grammar.Bytes}
    (h : gramRelSup env ρ (.varG "Binstr" []) (c :: r) v) :
    ProdDerives env ρ [] [] q (c :: r) [v] := by
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp h
  obtain ⟨-, p, hp, hdd⟩ := (symDerives_binstr_cons hb).mp hd
  have hc : (!mayEval 6 (prodValue p) v || prodEq p q) = true := List.all_eq_true.mp hq p hp
  rw [mayEval_of_prodDerives hdd 6, Bool.not_true, Bool.false_or] at hc
  rw [← eq_of_prodEq hc]
  exact hdd

/-- `p` occurs among the productions with leading byte `c`, decided through the printer. -/
def hasOp (env : Env) (c : UInt8) (q : IL.Prod) : Bool :=
  (binstrOps env c).any fun p => prodEq p q

theorem mem_of_hasOp {env : Env} {c : UInt8} {q : IL.Prod} (h : hasOp env c q = true) :
    q ∈ binstrOps env c := by
  obtain ⟨p, hp, he⟩ := List.any_eq_true.mp h
  rw [← eq_of_prodEq he]
  exact hp

/-! ## wasm-2.0, #670 -/

/-- `0xFD k:Bu32 ao:Bmemarg => VLOAD V128 (ZERO z) ao` (`A-binary.spectec:471-472`). -/
def vloadZeroProd (k z : Nat) : IL.Prod :=
  .prodD [.expP "ao" (.varT "memarg" [])]
    (.seqG [.seqG [.numG 253], .seqG [.attrG (.caseE "%" (.tupE [.numE (.natN k)])) (.varG "Bu32" [])],
      .seqG [.attrG (.varE "ao") (.varG "Bmemarg" [])]])
    (.caseE "VLOAD" (.tupE [.caseE "V128" (.tupE []),
      .optE (some (.caseE "ZERO" (.numE (.natN z)))), .varE "ao"])) []

/-- The memory argument `{ALIGN 0, OFFSET 0}`. -/
def memarg0 : Value := .struct [("ALIGN", numCase 0), ("OFFSET", numCase 0)]

/-- `VLOAD V128 (ZERO 64) {ALIGN 0, OFFSET 0}`, `v128.load64_zero` with a zero memory
argument. -/
def vload64 : Value :=
  .case "VLOAD" (.tuple [con "V128", .opt (some (.case "ZERO" (.num (.natN 64)))), memarg0])

/-- Matching a numeral pattern `%(k)` against `%(m)` forces `k = m`. -/
theorem matchExp_caseNum_inv {env : Env} {ρ ρ' : VarEnv} {k m : Nat}
    (h : MatchExp env ρ (.caseE "%" (.tupE [.numE (.natN k)])) (numCase m) ρ') : k = m := by
  obtain ⟨n, h⟩ := h
  have h4 : matchExp (n + 4) env ρ (.caseE "%" (.tupE [.numE (.natN k)])) (numCase m) = .ok ρ' :=
    matchExp_ok_of_le (by omega) h
  have h5 : m = k ∧ ρ = ρ' := by
    simpa [matchExp, matchExps, numCase, Value.asCase?, Value.asTuple?, Res.bind_eq_ok,
      Res.assert_eq_ok] using h4
  exact h5.1.symm

/-- A one-byte prefix `b` of `c :: _` with `c < 128` is the whole `u32` encoding: its value
is `c`. -/
theorem u32_of_small_head {b r : Grammar.Bytes} {c : UInt8} {r' : Grammar.Bytes} {k : Nat}
    (hu : U32 b k) (hb : b ++ r = c :: r') (hc : c.toNat < 128) : k = c.toNat := by
  cases hu with
  | byte n h₁ h₂ => exact (List.cons.inj hb).1 ▸ rfl
  | cont n h₁ h₂ rest =>
    have hn : n = c := (List.cons.inj hb).1
    subst hn
    omega

/-- **The opcode of a `VLOAD … ZERO` derivation.** A derivation of `FD c …` by
`vloadZeroProd k z`, with `c < 128`, has `k = c`. -/
theorem vloadZero_opcode {env : Env} (h : Equiv.Wasm20.HasV2Types env) (hl : HasLeb env)
    {ρ : VarEnv} {k z : Nat} {c : UInt8} {r : Grammar.Bytes} {l : List Value}
    (hc : c.toNat < 128) (hd : ProdDerives env ρ [] [] (vloadZeroProd k z) (0xFD :: c :: r) l) :
    k = c.toNat := by
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩ := hd
  obtain ⟨b₁, l₁, σ₁, b₂, l₂, h₁, h₂, hb, -⟩ := symDerives_seqG_cons.mp hs
  obtain ⟨d₁, k₁, τ₁, d₂, k₂, hd₁, hd₂, rfl, -⟩ := symDerives_seqG_cons.mp h₁
  obtain ⟨rfl, -, -⟩ := (symDerives_numG (by decide)).mp hd₁
  obtain ⟨rfl, -, -⟩ := symDerives_seqG_nil.mp hd₂
  obtain ⟨e₁, m₁, τ₂, e₂, m₂, he₁, -, rfl, -⟩ := symDerives_seqG_cons.mp h₂
  obtain ⟨f₁, n₁, τ₃, f₂, n₂, hf₁, -, rfl, -⟩ := symDerives_seqG_cons.mp he₁
  obtain ⟨w, τ₄, hw, rfl, hm⟩ := symDerives_attrG.mp hf₁
  obtain ⟨-, m, hum, hwm⟩ := (Equiv.Wasm20.symDerives_bu32_v2 h hl).mp hw
  obtain rfl : w = numCase m := List.singleton_inj.mp hwm
  have hkm : k = m := matchExp_caseNum_inv hm
  have hb' : f₁ ++ (f₂ ++ e₂) = c :: r := by simpa using hb.symm
  rw [hkm]
  exact u32_of_small_head hum hb' hc

/-! ### Positive derivations -/

/-- A `u32` byte below `128` is its own encoding. -/
theorem u32_small {c : UInt8} (hc : c.toNat < 128) : U32 [c] c.toNat :=
  .byte c hc (by omega)

/-- Matching the numeral pattern `%(k)` against `%(k)` binds nothing. -/
theorem matchExp_caseNum {env : Env} {ρ : VarEnv} {k : Nat} :
    MatchExp env ρ (.caseE "%" (.tupE [.numE (.natN k)])) (numCase k) ρ :=
  ⟨4, by simp [matchExp, matchExps, numCase, Value.asCase?, Value.asTuple?]⟩

/-- A two-field record evaluates field by field. -/
theorem evalExpFields_pair {env : Env} {ρ : VarEnv} {a b : AtomS} {e₁ e₂ : Exp} {w₁ w₂ : Value}
    (h₁ : EvalExp env ρ e₁ w₁) (h₂ : EvalExp env ρ e₂ w₂) :
    EvalExpFields env ρ [.mk a e₁, .mk b e₂] [(a, w₁), (b, w₂)] := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp only [evalExpFields, List.mapM_cons, List.mapM_nil,
    evalExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁, evalExp_ok_of_le (Nat.le_max_right n₁ n₂) h₂]
  rfl

/-- `%(x)` evaluates to `%(k)` where `x` is bound to `k`. -/
theorem evalExp_caseVar {env : Env} {σ : VarEnv} {x : IL.Id} {k : Nat}
    (hx : σ.findVal? x = some (.num (.natN k))) :
    EvalExp env σ (.caseE "%" (.tupE [.varE x])) (numCase k) :=
  evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr
    ⟨_, evalExps_singleton (evalExp_varE_iff.mpr hx), rfl⟩, rfl⟩

/-- **`Bmemarg ⊢ 00 00 ↦ {ALIGN 0, OFFSET 0}`**, for the wasm-1.0/2.0 `Bmemarg`. -/
theorem bmemarg_00 {env : Env} (h : Equiv.Wasm20.HasV2Types env) (hl : HasLeb env)
    (hm : env.findGram? "Bmemarg" = some ([], .varT "memarg" [], Equiv.V1Binary.bmemargV1Prods))
    (ρ : VarEnv) : SymDerives env ρ (.varG "Bmemarg" []) [0, 0] [memarg0] ρ := by
  let σ₁ : VarEnv := VarEnv.empty.bindVal "n" (.num (.natN 0))
  let σ₂ : VarEnv := σ₁.bindVal "m" (.num (.natN 0))
  have u0 : U32 [0] 0 := u32_small (c := 0) (by decide)
  have hb : SymDerives env VarEnv.empty
      (.seqG [.seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bu32" [])],
        .seqG [.attrG (.caseE "%" (.tupE [.varE "m"])) (.varG "Bu32" [])]])
      [0, 0] [numCase 0, numCase 0] σ₂ :=
    symDerives_seqG_cons.mpr ⟨[0], [numCase 0], σ₁, [0], [numCase 0],
      (Equiv.Wasm20.symDerives_bu32Factor_v2 h hl rfl).mpr ⟨0, u0, rfl, rfl⟩,
      symDerives_seqG_single ((Equiv.Wasm20.symDerives_bu32Factor_v2 h hl rfl).mpr
        ⟨0, u0, rfl, rfl⟩), rfl, rfl⟩
  have hv : EvalExp env σ₂ (.strE [.mk "ALIGN" (.caseE "%" (.tupE [.varE "n"])),
      .mk "OFFSET" (.caseE "%" (.tupE [.varE "m"]))]) memarg0 :=
    evalExp_strE_iff.mpr ⟨_, evalExpFields_pair (evalExp_caseVar rfl) (evalExp_caseVar rfl), rfl⟩
  exact (symDerives_varG hm).mpr ⟨rfl, _, List.mem_singleton_self _,
    ⟨[], VarEnv.empty, _, σ₂, σ₂, _, evalArgs_nil env ρ, rfl, hb, premsHold_nil_iff.mpr rfl, hv,
      rfl⟩⟩

/-- The value of `VLOAD V128 (ZERO 64) ao` where `ao` is bound to `{ALIGN 0, OFFSET 0}`. -/
theorem evalExp_vload64 {env : Env} :
    EvalExp env (VarEnv.empty.bindVal "ao" memarg0)
      (.caseE "VLOAD" (.tupE [.caseE "V128" (.tupE []),
        .optE (some (.caseE "ZERO" (.numE (.natN 64)))), .varE "ao"])) vload64 := by
  let σ := VarEnv.empty.bindVal "ao" memarg0
  have h₁ : EvalExp env σ (lit (con "V128")) (con "V128") := evalExp_lit env σ _
  have h₂ : EvalExp env σ (lit (.opt (some (.case "ZERO" (.num (.natN 64))))))
      (.opt (some (.case "ZERO" (.num (.natN 64))))) := evalExp_lit env σ _
  have h₃ : EvalExp env σ (.varE "ao") memarg0 := evalExp_varE_iff.mpr rfl
  have hn : EvalExps env σ [] [] := ⟨1, evalExps_nil_eq env σ 0⟩
  have hs : EvalExps env σ [lit (con "V128"), lit (.opt (some (.case "ZERO" (.num (.natN 64))))),
      .varE "ao"] [con "V128", .opt (some (.case "ZERO" (.num (.natN 64)))), memarg0] :=
    evalExps_cons_iff.mpr ⟨_, _, h₁, evalExps_cons_iff.mpr ⟨_, _, h₂,
      evalExps_cons_iff.mpr ⟨_, _, h₃, hn, rfl⟩, rfl⟩, rfl⟩
  exact evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_, hs, rfl⟩, rfl⟩

/-- **`vloadZeroProd c 64` reads `FD c 00 00` as `v128.load64_zero` with a zero memory
argument**, for `c < 128`. -/
theorem vloadZero_derives {env : Env} (h : Equiv.Wasm20.HasV2Types env) (hl : HasLeb env)
    (hm : env.findGram? "Bmemarg" = some ([], .varT "memarg" [], Equiv.V1Binary.bmemargV1Prods))
    {c : UInt8} (hc : c.toNat < 128) (ρ : VarEnv) :
    ProdDerives env ρ [] [] (vloadZeroProd c.toNat 64) [0xFD, c, 0, 0] [vload64] := by
  let σ := VarEnv.empty.bindVal "ao" memarg0
  have hop : SymDerives env VarEnv.empty
      (.seqG [.attrG (.caseE "%" (.tupE [.numE (.natN c.toNat)])) (.varG "Bu32" [])])
      [c] [numCase c.toNat] VarEnv.empty :=
    symDerives_seqG_single (symDerives_attrG.mpr ⟨_, VarEnv.empty,
      (Equiv.Wasm20.symDerives_bu32_v2 h hl).mpr ⟨rfl, _, u32_small hc, rfl⟩, rfl,
      matchExp_caseNum⟩)
  have hma : SymDerives env VarEnv.empty (.seqG [.seqG [.attrG (.varE "ao") (.varG "Bmemarg" [])]])
      [0, 0] [memarg0] σ :=
    symDerives_seqG_single (symDerives_seqG_single (symDerives_attrVar rfl (bmemarg_00 h hl hm _)))
  have hb : SymDerives env VarEnv.empty (substSym (gramArgSubst [] [])
      (.seqG [.seqG [.numG 253],
        .seqG [.attrG (.caseE "%" (.tupE [.numE (.natN c.toNat)])) (.varG "Bu32" [])],
        .seqG [.attrG (.varE "ao") (.varG "Bmemarg" [])]])) [0xFD, c, 0, 0]
      [.num (.natN 253), numCase c.toNat, memarg0] σ :=
    symDerives_seqG_cons.mpr ⟨[0xFD], _, VarEnv.empty, [c, 0, 0], _,
      symDerives_seqG_single ((symDerives_numG (by decide)).mpr ⟨rfl, rfl, rfl⟩),
      symDerives_seqG_cons.mpr ⟨[c], _, VarEnv.empty, [0, 0], _, hop, hma, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨[], VarEnv.empty, _, σ, σ, _, evalArgs_nil env ρ, rfl, hb, premsHold_nil_iff.mpr rfl,
    evalExp_vload64, rfl⟩

/-! ### At the pinned and the fixed wasm-2.0 scripts -/

theorem hasV2Types_wasm20_original : Equiv.Wasm20.HasV2Types Wasm20.envOriginal := by
  rw [Wasm20.envOriginal, wasm20_original_eq]; exact Equiv.Wasm20.hasV2Types_pinned_v2

theorem hasV2Types_wasm20_fixed : Equiv.Wasm20.HasV2Types Wasm20.envFixed := by
  rw [Wasm20.envFixed, wasm20_fixed_eq]; exact Equiv.Wasm20.hasV2Types_v2

set_option maxRecDepth 100000 in
theorem bmemarg_wasm20_original : Wasm20.envOriginal.findGram? "Bmemarg" =
    some ([], .varT "memarg" [], Equiv.V1Binary.bmemargV1Prods) := rfl

set_option maxRecDepth 100000 in
theorem bmemarg_wasm20_fixed : Wasm20.envFixed.findGram? "Bmemarg" =
    some ([], .varT "memarg" [], Equiv.V1Binary.bmemargV1Prods) := rfl

set_option maxRecDepth 100000 in
theorem hasBinstr_wasm20_original : HasBinstr Wasm20.envOriginal := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hasBinstr_wasm20_fixed : HasBinstr Wasm20.envFixed := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The pinned `Binstr` has `0xFD 92 => VLOAD V128 (ZERO 64)`. -/
theorem hasOp_92_original : hasOp Wasm20.envOriginal 0xFD (vloadZeroProd 92 64) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The fixed `Binstr` has `0xFD 93 => VLOAD V128 (ZERO 64)`. -/
theorem hasOp_93_fixed : hasOp Wasm20.envFixed 0xFD (vloadZeroProd 93 64) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- In the pinned `Binstr`, the only `0xFD` production that can yield `v128.load64_zero` is the
one at `92`. -/
theorem only_92_original : onlyProdYields Wasm20.envOriginal 0xFD vload64 (vloadZeroProd 92 64) =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- In the fixed `Binstr`, it is the one at `93`. -/
theorem only_93_fixed : onlyProdYields Wasm20.envFixed 0xFD vload64 (vloadZeroProd 93 64) =
    true := by
  decide +kernel

/-- `FD 5C 00 00`: the pinned encoding of `v128.load64_zero`. -/
def bytesFD5C : Grammar.Bytes := [0xFD, 0x5C, 0, 0]

/-- `FD 5D 00 00`: the corrected encoding of `v128.load64_zero`. -/
def bytesFD5D : Grammar.Bytes := [0xFD, 0x5D, 0, 0]

/-- **The pinned wasm-2.0 theory reads `FD 5C 00 00` as `v128.load64_zero`.** -/
theorem binstr_FD5C_original (ρ : VarEnv) :
    gramRelSup Wasm20.envOriginal ρ (.varG "Binstr" []) bytesFD5C vload64 :=
  gramRelSup_iff.mpr ⟨ρ, (symDerives_binstr_cons hasBinstr_wasm20_original).mpr
    ⟨rfl, _, mem_of_hasOp hasOp_92_original, vloadZero_derives (c := 0x5C)
      hasV2Types_wasm20_original hasLeb_wasm20_original bmemarg_wasm20_original (by decide) ρ⟩⟩

/-- **The fixed wasm-2.0 theory reads `FD 5D 00 00` as `v128.load64_zero`.** -/
theorem binstr_FD5D_fixed (ρ : VarEnv) :
    gramRelSup Wasm20.envFixed ρ (.varG "Binstr" []) bytesFD5D vload64 :=
  gramRelSup_iff.mpr ⟨ρ, (symDerives_binstr_cons hasBinstr_wasm20_fixed).mpr
    ⟨rfl, _, mem_of_hasOp hasOp_93_fixed, vloadZero_derives (c := 0x5D)
      hasV2Types_wasm20_fixed hasLeb_wasm20_fixed bmemarg_wasm20_fixed (by decide) ρ⟩⟩

/-- **The fixed theory does not read `FD 5C 00 00` as `v128.load64_zero`**: the only `0xFD`
production that can yield it reads the opcode `93`. -/
theorem not_binstr_FD5C_fixed (ρ : VarEnv) :
    ¬ gramRelSup Wasm20.envFixed ρ (.varG "Binstr" []) bytesFD5C vload64 := fun h =>
  absurd (vloadZero_opcode hasV2Types_wasm20_fixed hasLeb_wasm20_fixed (c := 0x5C) (by decide)
    (prodDerives_of_onlyProdYields hasBinstr_wasm20_fixed only_93_fixed h)) (by decide)

/-- **The pinned theory does not read `FD 5D 00 00` as `v128.load64_zero`**: there the only
such production reads the opcode `92`. -/
theorem not_binstr_FD5D_original (ρ : VarEnv) :
    ¬ gramRelSup Wasm20.envOriginal ρ (.varG "Binstr" []) bytesFD5D vload64 := fun h =>
  absurd (vloadZero_opcode hasV2Types_wasm20_original hasLeb_wasm20_original (c := 0x5D)
    (by decide) (prodDerives_of_onlyProdYields hasBinstr_wasm20_original only_92_original h))
    (by decide)

/-- **The wasm-2.0 errata give an incomparable theory**: the original entails
`Binstr ⊢ FD 5C 00 00 ↦ v128.load64_zero` and the fixed one does not; the fixed one entails
`Binstr ⊢ FD 5D 00 00 ↦ v128.load64_zero` and the original does not (#670). -/
theorem wasm20_errata_incomparable :
    (¬ ∀ ψ ∈ scriptAxioms Wasm20.envOriginal, Entails (scriptAxioms Wasm20.envFixed) ψ) ∧
      (¬ ∀ ψ ∈ scriptAxioms Wasm20.envFixed, Entails (scriptAxioms Wasm20.envOriginal) ψ) :=
  ⟨not_entailsAll_of_separates
      ((gramRelSup_varG_iff_entails ..).mp (binstr_FD5C_original VarEnv.empty))
      (fun h => not_binstr_FD5C_fixed VarEnv.empty ((gramRelSup_varG_iff_entails ..).mpr h)),
    not_entailsAll_of_separates
      ((gramRelSup_varG_iff_entails ..).mp (binstr_FD5D_fixed VarEnv.empty))
      (fun h => not_binstr_FD5D_original VarEnv.empty ((gramRelSup_varG_iff_entails ..).mpr h))⟩

end Silmaril.Wasm.SpecTec.GrammarInst
