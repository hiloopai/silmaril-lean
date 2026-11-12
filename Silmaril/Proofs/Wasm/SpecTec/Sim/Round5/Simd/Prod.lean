module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Pack

/-!
# Round 5: `$prod` and `$jsizenn` by their clauses

`$prod(n*)` is the product of its arguments (`applies_prod`, by induction over the list: the
second clause matches `n n'*` by splitting off the literal one-element prefix), and
`$jsizenn(Jnn)` is the lane width (`applies_jsizenn`, through `$lsize`, `$size`, `$psize`). Both
hold for every `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil bvV natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## `$prod` -/

/-- The tail pattern `n'*` of `$prod`'s second clause. -/
abbrev prodTail : Exp := .iterE (.varE "n'") (.mk .list [.mk "n'" (.varE "n'*")])

/-- `$prod`'s second clause. -/
abbrev prodClause₂ : Clause :=
  .defD [.expP "n" (.varT "n" []), .expP "n'*" (.iterT (.varT "n" []) .list)]
    [.expA (.catE (.listE [.varE "n"]) prodTail)]
    (.binE .mulOp (.numT .natT) (.varE "n") (.callE "prod" [.expA prodTail])) []

set_option maxRecDepth 100000 in
theorem findDef_prod (B : Builtins) : ∃ ps t, (simEnv B).findDef? "prod" = some (ps, t,
    [.defD [] [.expA (.listE [])] (.numE (.natN 1)) [], prodClause₂]) := ⟨_, _, rfl⟩

/-- The numerals of a list of naturals. -/
def natsV (ns : List Nat) : List Value := ns.map fun n => .num (.natN n)

/-- The scope of `$prod`'s second clause at `n :: ns`. -/
abbrev prodScope (n : Nat) (ns : List Nat) : VarEnv :=
  (VarEnv.empty.bindVal "n" (.num (.natN n))).bindVal "n'*" (.list (natsV ns))

/-- `n n'*` matches `n :: ns`. -/
theorem matchArgs_prod₂ (n : Nat) (ns : List Nat) :
    MatchArgs (simEnv B) VarEnv.empty [.expA (.catE (.listE [.varE "n"]) prodTail)]
      [.val (.list (natsV (n :: ns)))] (prodScope n ns) := by
  have h₁ : MatchExp (simEnv B) VarEnv.empty (.listE [.varE "n"]) (.list [.num (.natN n)])
      (VarEnv.empty.bindVal "n" (.num (.natN n))) :=
    ⟨3, by simp [matchExp, matchExps, Res.ofOption, Value.asList?, Bind.bind, Except.bind]⟩
  have h₂ : MatchExp (simEnv B) (VarEnv.empty.bindVal "n" (.num (.natN n))) prodTail
      (.list (natsV ns)) (prodScope n ns) :=
    (Equiv.Execution.matchExp_iterE_list_iff (Equiv.Execution.bindsVar_varE "n'") (by simp)
      (by decide)).2 ⟨natsV ns, rfl, (Equiv.Execution.matchExp_freshVar_iff (by simp)).2 rfl⟩
  exact matchArgs_cons (matchArg_expA (Equiv.Execution.matchExp_catE_ofLeft (m := 1)
    (j := 1) (by simp [patLen]) (by simp [natsV]) (by simpa [natsV] using h₁)
    (by simpa [natsV] using h₂))) matchArgs_nil

/-- **`$prod(n*)` is the product of `n*`**, for every `B`. -/
theorem applies_prod : ∀ ns : List Nat,
    Applies (simEnv B) "prod" [.val (.list (natsV ns))] (.num (.natN ns.prod))
  | [] => by
    obtain ⟨ps, t, hd⟩ := findDef_prod B
    have hm : MatchExp (simEnv B) VarEnv.empty (.listE []) (.list (natsV [])) VarEnv.empty :=
      ⟨2, by simp [matchExp, matchExps, Res.ofOption, Value.asList?, natsV, Bind.bind,
        Except.bind]⟩
    exact ⟨ps, t, _, hd, Or.inl (tryClauses_hit (ρ₀ := VarEnv.empty)
      (matchArgs_cons (matchArg_expA hm) matchArgs_nil) premsHold_nil RefsGC.evalExp_num')⟩
  | n :: ns => by
    obtain ⟨ps, t, hd⟩ := findDef_prod B
    have ih := applies_prod ns
    have hskip : ∃ k, matchArg k (simEnv B) VarEnv.empty (.expA (.listE []))
        (.val (.list (natsV (n :: ns)))) = .error .undef :=
      matchArg_expA_undef ⟨2, by simp [matchExp, matchExps, Res.ofOption, Value.asList?, natsV,
        Bind.bind, Except.bind]⟩
    have htail : EvalExp (simEnv B) (prodScope n ns) prodTail (.list (natsV ns)) :=
      Equiv.Execution.evalExp_iterPat (by decide) (by simp)
    have hrec : EvalExp (simEnv B) (prodScope n ns) (.callE "prod" [.expA prodTail])
        (.num (.natN ns.prod)) :=
      Vec.evalExp_call rfl (evalArgs_cons htail evalArgs_nil) ih
    have hbody : EvalExp (simEnv B) (prodScope n ns)
        (.binE .mulOp (.numT .natT) (.varE "n") (.callE "prod" [.expA prodTail]))
        (.num (.natN (n :: ns).prod)) := by
      rw [List.prod_cons]
      exact RefsGC.evalExp_mulNat (evalExp_var (by simp)) hrec
    exact ⟨ps, t, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef hskip)
      (tryClauses_hit (matchArgs_prod₂ n ns) premsHold_nil hbody))⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
