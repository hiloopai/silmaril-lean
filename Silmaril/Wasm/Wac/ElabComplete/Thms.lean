module

public import Silmaril.Wasm.Wac.Elab.Thms

/-!
# WAC elaboration: completeness

Every derivation of the relations of `Silmaril.Wasm.Wac.ElabSpec` is computed by the
elaborator: `elabExpr_complete`, `elabArgs_complete`, `elabSpreads_complete`,
`elabStmt_complete`, `elabDoc_complete`. With soundness,
`elabDoc_iff : elabDoc env d = .ok g ↔ ElabDoc env d g`: the elaborator decides the
relational specification, and the specification is functional.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Syntax

/-! ## Small steps -/

theorem ESt.lookup_of {st : ESt} {x : String} {i : Nat} (h : st.scope.lookup x = some i) :
    st.lookup x = .ok i := by
  simp [ESt.lookup, h]

theorem insertArg_of {acc : List (String × Nat)} {n : String} {i : Nat} (h : n ∉ acc.map (·.1)) :
    insertArg acc n i = .ok (acc ++ [(n, i)]) := by
  have hn : acc.any (·.1 == n) = false :=
    List.any_eq_false.2 fun a ha e => h (List.mem_map.2 ⟨a, ha, by simpa using e⟩)
  simp [insertArg, hn]

theorem ESt.exportsOf_of {st : ESt} {i : Nat} {w : String} {es : Externs}
    (h : (st.g.kindOf i).exports? = some es) : st.exportsOf i w = .ok es := by
  simp [ESt.exportsOf, h]

theorem ESt.aliasExport_of {st : ESt} {i : Nat} {n w : String} {es : Externs} {k : Kind}
    (he : (st.g.kindOf i).exports? = some es) (hk : es.find n = some k) :
    st.aliasExport i n w = .ok (some (st.aliasAt i n k)) := by
  unfold ESt.aliasExport
  rw [ESt.exportsOf_of he]
  show Except.ok ((es.find n).map _) = _
  rw [hk]
  rfl

theorem checkArgs_of {pkg : String} {imps : Externs} {g : CGraph} :
    ∀ {acc : List (String × Nat)}, ArgsTyped imps g acc → checkArgs pkg imps g acc = .ok ()
  | [], _ => rfl
  | (n, j) :: rest, h => by
    obtain ⟨k, hk, hs⟩ := h (n, j) (by simp)
    have ih := checkArgs_of (pkg := pkg) (acc := rest) fun a ha => h a (by simp [ha])
    simp [checkArgs, hk, (sub_iff _ _).2 hs, ih]

theorem checkAll_of {pkg : String} {imps : Externs} {acc : List (String × Nat)}
    (h : AllGiven imps acc) : checkAll pkg imps acc = .ok () := by
  have hn : imps.find? (fun q => !(acc.any (·.1 == q.1))) = none := by
    refine List.find?_eq_none.2 fun q hq => ?_
    obtain ⟨a, ha, e⟩ := List.mem_map.1 (h q hq)
    have hany : acc.any (·.1 == q.1) = true := List.any_eq_true.2 ⟨a, ha, by rw [e]; exact beq_self_eq_true _⟩
    simp [hany]
  simp [checkAll, hn]

theorem ECtx.package_of {cx : ECtx} {key : String} {pk : PkgType} (h : cx.env.lookup key = some pk) :
    cx.package key = .ok pk := by
  simp [ECtx.package, h]

/-! ## Spreads -/

theorem PickExport.unique {exps : List String} {n e e' : String} (h : PickExport exps n e)
    (h' : PickExport exps n e') : e = e' :=
  Option.some.inj ((pickExport_iff.2 h).symm.trans (pickExport_iff.2 h'))

theorem SpreadPlan.eq {exps sup ns : List String} {pl : List (String × String)}
    (h : SpreadPlan exps sup ns pl) : spreadPlan exps ns sup = pl := by
  induction h with
  | nil => rfl
  | supplied hs _ ih => simp [spreadPlan, hs] at ih ⊢; exact ih
  | @unmatched n ns pl hs hn _ ih =>
    have hp : pickExport exps n = none := by
      cases e : pickExport exps _ with
      | none => rfl
      | some x => exact absurd (pickExport_iff.1 e) (hn x)
    simp [spreadPlan, hs, hp] at ih ⊢; exact ih
  | pick hs hp _ ih =>
    simp [spreadPlan, hs, pickExport_iff.2 hp] at ih ⊢; exact ih

theorem elabSpreads_complete {imps : List String} {st : ESt} {acc : List (String × Nat)}
    {xs : List String} {r : ESt × List (String × Nat)} (h : ElabSpreads imps st acc xs r) :
    elabSpreads imps st acc xs = .ok r := by
  induction h with
  | nil => rfl
  | @cons st acc x xs i es plan r hx he hp hne _ ih =>
    have hne' : plan.isEmpty = false := by cases plan <;> simp_all
    rw [elabSpreads, ESt.lookup_of hx]
    simp only [bind, Except.bind, ESt.exportsOf_of he, hp.eq, hne']
    exact ih

/-! ## Expressions and arguments -/

mutual
/-- **Every derivation of an expression is computed.** -/
theorem elabExpr_complete {cx : ECtx} :
    ∀ {st : ESt} {e : Expr} {r : ESt × Nat}, ElabExpr cx st e r → elabExpr cx st e = .ok r
  | _, _, _, .ident hx => by rw [elabExpr, ESt.lookup_of hx]; rfl
  | _, _, _, .paren h => by rw [elabExpr]; exact elabExpr_complete h
  | _, _, _, .access h he ht hk => by
    rw [elabExpr]
    simp only [bind, Except.bind, elabExpr_complete h, ESt.exportsOf_of he, tailOrSelf_iff.2 ht,
      ESt.aliasExport_of he hk]
    rfl
  | _, _, _, .namedAccess h he hk => by
    rw [elabExpr]
    simp only [bind, Except.bind, elabExpr_complete h, ESt.aliasExport_of he hk]
    rfl
  | _, _, _, @ElabExpr.new _ _ _ _ _ _ _ _ _ fill hne hpk ha hs ht hall => by
    rw [elabExpr, Implicit.ite_no hne]
    simp only [bind, Except.bind, ECtx.package_of hpk, elabArgs_complete ha, elabSpreads_complete hs,
      checkArgs_of ht]
    cases fill with
    | true => rfl
    | false => simp only [checkAll_of (hall rfl), Bool.false_eq_true, ite_false]; rfl

/-- **Every derivation of the arguments is computed.** -/
theorem elabArgs_complete {cx : ECtx} :
    ∀ {imps : List String} {st : ESt} {acc : List (String × Nat)} {args : List Arg}
      {r : ESt × List (String × Nat) × Bool}, ElabArgs cx imps st acc args r →
      elabArgs cx imps st acc args = .ok r
  | _, _, _, _, _, .nil => by rw [elabArgs]
  | _, _, _, _, _, .fill => by rw [elabArgs]
  | _, _, _, _, _, .spread h => by rw [elabArgs]; exact elabArgs_complete h
  | _, _, _, _, _, .inferred hx hi hn h => by
    rw [elabArgs]
    simp only [bind, Except.bind, ESt.lookup_of hx, inferArg_iff.2 hi, insertArg_of hn]
    exact elabArgs_complete h
  | _, _, _, _, _, .named he hn hnot h => by
    rw [elabArgs]
    simp only [bind, Except.bind, elabExpr_complete he, namedArg_iff.2 hn, insertArg_of hnot]
    exact elabArgs_complete h
end

/-! ## Statements -/

theorem ESt.bind_of {st st' : ESt} {x : String} {i : Nat} (h : Binds st x i st') :
    st.bind x i = .ok st' := by
  cases h with
  | mk hn => simp [ESt.bind, hn]

theorem ESt.exportAs_of {st st' : ESt} {i : Nat} {n : String} (h : ExportAs st i n st') :
    st.exportAs i n = .ok st' := by
  cases h with
  | mk hd he =>
    have hd' : (st.scope.lookup n).any st.isDefn = false := by
      cases e : st.scope.lookup n with
      | none => rfl
      | some j => simpa using hd j e
    simp [ESt.exportAs, hd', he]

theorem spreadExports_complete {es : Externs} {i : Nat} {st : ESt} {xs : Externs} {r : ESt × Bool}
    (h : SpreadExports es i st xs r) : spreadExports es i st xs = .ok r := by
  induction h with
  | nil => rfl
  | skip hx _ ih => rw [spreadExports, Implicit.ite_yes hx]; exact ih
  | emit hx hex _ ih =>
    rw [spreadExports, Implicit.ite_no (by simpa using hx)]
    simp only [bind, Except.bind, ESt.exportAs_of hex, ih]
    rfl

/-- **Every derivation of a statement is computed.** -/
theorem elabStmt_complete {cx : ECtx} {st st' : ESt} {s : Stmt} (h : ElabStmt cx st s st') :
    elabStmt cx st s = .ok st' := by
  cases h with
  | «import» hk hn hb =>
    rw [elabStmt]
    simp only [bind, Except.bind, hk, Implicit.ite_no hn]
    exact ESt.bind_of hb
  | type hk hx hb =>
    rw [elabStmt]
    simp only [bind, Except.bind, hk, hx, Bool.false_eq_true, ite_false]
    exact ESt.bind_of hb
  | «let» he hb =>
    rw [elabStmt]
    simp only [bind, Except.bind, elabExpr_complete he]
    exact ESt.bind_of hb
  | exportNone he hn hx =>
    rw [elabStmt]
    simp only [bind, Except.bind, elabExpr_complete he, exportName?_iff.2 hn]
    exact ESt.exportAs_of hx
  | exportRename he hx =>
    rw [elabStmt]
    simp only [bind, Except.bind, elabExpr_complete he]
    exact ESt.exportAs_of hx
  | exportSpread he hes hx =>
    rw [elabStmt]
    simp only [bind, Except.bind, elabExpr_complete he, ESt.exportsOf_of hes, spreadExports_complete hx]
    rfl

theorem elabStmts_complete {cx : ECtx} {st st' : ESt} {ss : List Stmt} (h : ElabStmts cx st ss st') :
    elabStmts cx st ss = .ok st' := by
  induction h with
  | nil => rfl
  | cons h1 _ ih =>
    rw [elabStmts]
    simp only [bind, Except.bind, elabStmt_complete h1]
    exact ih

/-! ## Documents -/

theorem checkTargetImports_of {wi : Externs} :
    ∀ {xs : Externs}, (∀ p ∈ xs, ∃ k, wi.find p.1 = some k ∧ Sub k.promote p.2) →
      checkTargetImports wi xs = .ok ()
  | [], _ => rfl
  | (n, k) :: rest, h => by
    obtain ⟨k', hk', hs⟩ := h (n, k) (by simp)
    have ih := checkTargetImports_of (wi := wi) (xs := rest) fun p hp => h p (by simp [hp])
    simp [checkTargetImports, hk', (sub_iff _ _).2 hs, ih]

theorem checkTargetExports_of {g : CGraph} :
    ∀ {xs : Externs}, (∀ p ∈ xs, ∃ j, g.exports.lookup p.1 = some j ∧ Sub (g.kindOf j) p.2.promote) →
      checkTargetExports g xs = .ok ()
  | [], _ => rfl
  | (n, k) :: rest, h => by
    obtain ⟨j, hj, hs⟩ := h (n, k) (by simp)
    have ih := checkTargetExports_of (g := g) (xs := rest) fun p hp => h p (by simp [hp])
    simp [checkTargetExports, hj, (sub_iff _ _).2 hs, ih]

theorem checkTargets_of {cx : ECtx} {st : ESt} {g : CGraph} {t : Option PkgPath}
    (h : ∀ p, t = some p → ∃ i wi we, resolvePath cx st p = .ok (.type (.comp i wi we)) ∧ TargetOk g wi we) :
    checkTargets cx st g t = .ok () := by
  cases t with
  | none => rfl
  | some p =>
    obtain ⟨i, wi, we, hr, hi, he⟩ := h p rfl
    rw [checkTargets]
    simp only [bind, Except.bind, hr, checkTarget, checkTargetImports_of hi, checkTargetExports_of he]

/-- **Every derivation of a document is computed.** -/
theorem elabDoc_complete {env : PkgEnv} {d : Document} {g : CGraph} (h : ElabDoc env d g) :
    elabDoc env d = .ok g := by
  cases h with
  | mk hs hr ht =>
    rw [elabDoc]
    simp only [bind, Except.bind, elabStmts_complete hs, hr, checkTargets_of ht]
    rfl

/-- **The elaborator decides the relational specification.** -/
theorem elabDoc_iff {env : PkgEnv} {d : Document} {g : CGraph} :
    elabDoc env d = .ok g ↔ ElabDoc env d g :=
  ⟨elabDoc_sound, elabDoc_complete⟩

/-- **The specification is functional.** -/
theorem ElabDoc.unique {env : PkgEnv} {d : Document} {g g' : CGraph} (h : ElabDoc env d g)
    (h' : ElabDoc env d g') : g = g' :=
  Except.ok.inj ((elabDoc_complete h).symm.trans (elabDoc_complete h'))

end Silmaril.Wasm.Wac
