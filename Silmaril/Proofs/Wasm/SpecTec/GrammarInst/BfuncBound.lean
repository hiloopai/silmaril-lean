module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Dead
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10

/-!
# #688 in the byte grammar institution: the bound on locals (half of it)

#688 appends `-- if |$concat_(local, local**)| < 2^32` to wasm-1.0's `Bfunc`
(`A-binary.spectec:505-506`). The production's value is `($concat_(local, local**), expr)`,
and the premise reads the same expression in the same scope (an `if` binds nothing), so every
value the corrected `Bfunc` derives has fewer than `2^32` locals (`bfunc_fixed_bound`), for any
byte string — no evaluation of `$concat_` is needed.

The other half, a pinned derivation with at least `2^32` locals, is stated here as
`Task.bfunc688PinnedLarge`; under it, #688 separates (`bfunc688_separates_of_task`). It is proved
in `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.BfuncLarge` (`bfunc688PinnedLarge`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

/-- `2^32`, as the corrected premise writes it. -/
def pow32 : Exp := .binE .powOp (.numT .natT) (.numE (.natN 2)) (.numE (.natN 32))

/-- The corrected `Bfunc`: one production whose value is `(C, expr)` and whose premise is
`|C| < 2^32`, for the same expression `C`. -/
def BfuncFixedShape (env : Env) : Prop :=
  ∃ (t : Typ) (q : List Param) (g : IL.Sym) (C : Exp),
    env.findGram? "Bfunc" = some ([], t, [.prodD q g (.tupE [C, .varE "expr"])
      [.ifPr (.cmpE .ltOp (.numT .natT) (.lenE C) pow32)]])

set_option maxRecDepth 100000 in
theorem bfuncFixedShape_wasm10 : BfuncFixedShape Wasm10.envFixed := ⟨_, _, _, _, by rfl⟩

/-- `2^32` evaluates to `2^32`. -/
theorem evalExp_pow32 {env : Env} {ρ : VarEnv} : EvalExp env ρ pow32 (.num (.natN (2 ^ 32))) :=
  evalExp_binE_iff.mpr ⟨_, evalExp_numE_iff.mpr rfl, .inr ⟨rfl, _, evalExp_numE_iff.mpr rfl, rfl⟩⟩

/-- The premise, read back: the list `C` denotes has fewer than `2^32` elements. -/
theorem lt_of_premise {env : Env} {ρ : VarEnv} {C : Exp} {L : List Value}
    (hc : EvalExp env ρ C (.list L))
    (hp : EvalExp env ρ (.cmpE .ltOp (.numT .natT) (.lenE C) pow32) (.bool true)) :
    L.length < 2 ^ 32 := by
  obtain ⟨a, b, ha, hb, hab⟩ := evalExp_cmpE_iff.mp hp
  obtain ⟨vs, hvs, rfl⟩ := evalExp_lenE_iff.mp ha
  obtain rfl : b = .num (.natN (2 ^ 32)) := EvalExp.unique hb evalExp_pow32
  obtain ⟨⟩ : Value.list vs = .list L := EvalExp.unique hvs hc
  simpa [cmpValues, Num.cmp] using hab

/-- **The corrected `Bfunc` bounds its locals**: whatever it derives is a pair `(L, e)` with
`|L| < 2^32`. -/
theorem bfunc_fixed_bound {env : Env} (hs : BfuncFixedShape env) {ρ : VarEnv}
    {bs : Grammar.Bytes} {L : List Value} {e : Value}
    (h : gramRelSup env ρ (.varG "Bfunc" []) bs (.tuple [.list L, e])) : L.length < 2 ^ 32 := by
  obtain ⟨t, q, g, C, hg⟩ := hs
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp h
  obtain ⟨-, p, hp, hpd⟩ := (symDerives_varG hg).mp hd
  rw [List.mem_singleton] at hp
  subst hp
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, -, hpr, hv, hl⟩ := hpd
  obtain ⟨hc, rfl⟩ := premsHold_ifPr_iff.mp hpr
  rw [← List.singleton_inj.mp hl] at hv
  obtain ⟨vs, hvs, hvv⟩ := evalExp_tupE_iff.mp hv
  obtain ⟨a, as₁, ha, -, rfl⟩ := evalExps_cons_iff.mp hvs
  obtain ⟨rfl, -⟩ : Value.list L = a ∧ _ := by simpa using hvv
  exact lt_of_premise ha hc

/-- `bfunc_fixed_bound` at the corrected wasm-1.0 theory, as a statement about entailment. -/
theorem bfunc_fixed_entails_bound (ρ : VarEnv) (bs : Grammar.Bytes) (L : List Value) (e : Value)
    (h : Entails (scriptAxioms Wasm10.envFixed) (derivesNT "Bfunc" [] ρ bs (.tuple [.list L, e]))) :
    L.length < 2 ^ 32 :=
  bfunc_fixed_bound bfuncFixedShape_wasm10 ((gramRelSup_varG_iff_entails ..).mpr h)

/-- **Target (#688)**, proved by `bfunc688PinnedLarge` (`BfuncLarge`). The pinned wasm-1.0 theory entails a `Bfunc` sentence with at
least `2^32` locals. -/
def Task.bfunc688PinnedLarge : Prop :=
  ∃ (bs : Grammar.Bytes) (L : List Value) (e : Value), 2 ^ 32 ≤ L.length ∧
    Entails (scriptAxioms Wasm10.envOriginal)
      (derivesNT "Bfunc" [] VarEnv.empty bs (.tuple [.list L, e]))

/-- **#688 separates, conditionally**: under `Task.bfunc688PinnedLarge`, the corrected theory does
not entail all of the pinned one. -/
theorem bfunc688_separates_of_task (h : Task.bfunc688PinnedLarge) :
    ¬ ∀ ψ ∈ scriptAxioms Wasm10.envOriginal, Entails (scriptAxioms Wasm10.envFixed) ψ := by
  obtain ⟨bs, L, e, hL, hO⟩ := h
  refine not_entailsAll_of_separates hO fun hF => ?_
  have := bfunc_fixed_entails_bound VarEnv.empty bs L e hF
  omega

end Silmaril.Wasm.SpecTec.GrammarInst
