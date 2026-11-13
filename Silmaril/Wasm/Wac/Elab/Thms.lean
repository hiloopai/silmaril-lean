module

public import Silmaril.Wasm.Wac.ElabSpec.Defs
public import Silmaril.Wasm.Wac.Infer.Thms
public import Silmaril.Wasm.Wac.Implicit.Thms

/-!
# WAC elaboration: soundness

* `elabExpr_sound`, `elabArgs_sound`, `elabSpreads_sound`, `elabStmt_sound`,
  `elabDoc_sound`: whatever the elaborator computes is derivable in the relations of
  `Silmaril.Wasm.Wac.ElabSpec` (name inference by the precedence rules, spread and
  implicit-import resolution, WIT subtyping of arguments, target checking).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Syntax

/-! ## The error monad -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Small steps -/

theorem ESt.lookup_ok {st : ESt} {x : String} {i : Nat} (h : st.lookup x = .ok i) :
    st.scope.lookup x = some i := by
  unfold ESt.lookup at h
  split at h
  · rename_i j hj; cases h; exact hj
  · cases h

theorem insertArg_ok {acc acc' : List (String × Nat)} {n : String} {i : Nat}
    (h : insertArg acc n i = .ok acc') : n ∉ acc.map (·.1) ∧ acc' = acc ++ [(n, i)] := by
  unfold insertArg at h
  split at h
  · cases h
  · rename_i hn
    refine ⟨fun hm => hn ?_, (Except.ok.inj h).symm⟩
    obtain ⟨a, ha, e⟩ := List.mem_map.1 hm
    exact List.any_eq_true.2 ⟨a, ha, by simp [e]⟩

theorem ESt.exportsOf_ok {st : ESt} {i : Nat} {w : String} {es : Externs}
    (h : st.exportsOf i w = .ok es) : (st.g.kindOf i).exports? = some es := by
  unfold ESt.exportsOf at h
  split at h
  · rename_i es' he; cases h; exact he
  · cases h

theorem ESt.aliasExport_ok {st : ESt} {i : Nat} {n w : String} {r : ESt × Nat}
    (h : st.aliasExport i n w = .ok (some r)) :
    ∃ es k, (st.g.kindOf i).exports? = some es ∧ es.find n = some k ∧ r = st.aliasAt i n k := by
  obtain ⟨es, h1, h2⟩ := bind_ok h
  have h2' : (es.find n).map (fun k => st.aliasAt i n k) = some r := Except.ok.inj h2
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h2'
  exact ⟨es, k, ESt.exportsOf_ok h1, hk, rfl⟩

theorem checkArgs_ok {pkg : String} {imps : Externs} {g : CGraph} :
    ∀ {acc : List (String × Nat)}, checkArgs pkg imps g acc = .ok () → ArgsTyped imps g acc
  | [], _ => fun _ h => nomatch h
  | (n, j) :: rest, h => by
    unfold checkArgs at h
    split at h
    · cases h
    · rename_i k hk
      split at h
      · rename_i hs
        have ih : ArgsTyped imps g rest := checkArgs_ok h
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact ⟨k, hk, (sub_iff _ _).1 hs⟩
        · exact ih a ha
      · cases h

theorem checkAll_ok {pkg : String} {imps : Externs} {acc : List (String × Nat)}
    (h : checkAll pkg imps acc = .ok ()) : AllGiven imps acc := by
  unfold checkAll at h
  split at h
  · cases h
  · rename_i hn
    intro q hq
    have hq' : ∃ x, (q.1, x) ∈ acc := by
      have := List.find?_eq_none.1 hn q hq; simpa using this
    obtain ⟨x, hx⟩ := hq'
    exact List.mem_map.2 ⟨(q.1, x), hx, rfl⟩

/-! ## Spread arguments -/

theorem spreadPlan_spec (exps sup : List String) :
    ∀ ns, SpreadPlan exps sup ns (spreadPlan exps ns sup)
  | [] => .nil
  | n :: ns => by
    have ih := spreadPlan_spec exps sup ns
    by_cases hs : n ∈ sup
    · have e : spreadPlan exps (n :: ns) sup = spreadPlan exps ns sup := by
        simp [spreadPlan, hs]
      exact e ▸ .supplied hs ih
    · cases hp : pickExport exps n with
      | none =>
        have e : spreadPlan exps (n :: ns) sup = spreadPlan exps ns sup := by
          simp [spreadPlan, hs, hp]
        exact e ▸ .unmatched hs (fun x hx => by rw [pickExport_iff.2 hx] at hp; cases hp) ih
      | some x =>
        have e : spreadPlan exps (n :: ns) sup = (n, x) :: spreadPlan exps ns sup := by
          simp [spreadPlan, hs, hp]
        exact e ▸ .pick hs (pickExport_iff.1 hp) ih

theorem elabSpreads_sound {imps : List String} :
    ∀ {xs : List String} {st : ESt} {acc : List (String × Nat)} {r : ESt × List (String × Nat)},
      elabSpreads imps st acc xs = .ok r → ElabSpreads imps st acc xs r
  | [], st, acc, r, h => by
    have e : r = (st, acc) := (Except.ok.inj h).symm
    exact e ▸ .nil
  | x :: xs, st, acc, r, h => by
    obtain ⟨i, hi, h⟩ := bind_ok h
    obtain ⟨es, hes, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · rename_i hne
      have h' : elabSpreads imps (aliasPlan es i st acc (spreadPlan es.names imps (acc.map (·.1)))).1
          (aliasPlan es i st acc (spreadPlan es.names imps (acc.map (·.1)))).2 xs = .ok r := by
        revert h; cases aliasPlan es i st acc (spreadPlan es.names imps (acc.map (·.1))); exact id
      exact .cons (ESt.lookup_ok hi) (ESt.exportsOf_ok hes) (spreadPlan_spec _ _ _)
        (by simpa using hne) (elabSpreads_sound h')

/-! ## Expressions and arguments -/

theorem ECtx.package_ok {cx : ECtx} {key : String} {pk : PkgType} (h : cx.package key = .ok pk) :
    cx.env.lookup key = some pk := by
  unfold ECtx.package at h
  split at h
  · rename_i p hp; cases h; exact hp
  · cases h

theorem access_spec {st : ESt} {i : Nat} {es : Externs} {n w : String} {r : ESt × Nat}
    (hes : st.exportsOf i w = .ok es) (ho : st.aliasExport i n w = .ok (some r)) :
    ∃ k, (st.g.kindOf i).exports? = some es ∧ es.find n = some k ∧ r = st.aliasAt i n k := by
  obtain ⟨es', k, hes', hk, rfl⟩ := ESt.aliasExport_ok ho
  have e : es' = es := Option.some.inj (hes'.symm.trans (ESt.exportsOf_ok hes))
  exact ⟨k, ESt.exportsOf_ok hes, e ▸ hk, rfl⟩

mutual
/-- **Expressions elaborate soundly.** -/
theorem elabExpr_sound {cx : ECtx} :
    ∀ {e : Silmaril.Wasm.Wac.Syntax.Expr} {st : ESt} {r : ESt × Nat}, elabExpr cx st e = .ok r → ElabExpr cx st e r
  | .ident x, st, r, h => by
    rw [elabExpr] at h
    obtain ⟨i, hi, h⟩ := bind_ok h
    cases h
    exact .ident (ESt.lookup_ok hi)
  | .paren e, st, r, h => by
    rw [elabExpr] at h
    exact .paren (elabExpr_sound h)
  | .access e x, st, r, h => by
    rw [elabExpr] at h
    obtain ⟨⟨st1, i⟩, h1, h⟩ := bind_ok h
    obtain ⟨es, hes, h⟩ := bind_ok h
    obtain ⟨o, ho, h⟩ := bind_ok h
    cases o with
    | none => cases h
    | some r' =>
      cases h
      obtain ⟨k, hes', hk, rfl⟩ := access_spec hes ho
      exact .access (elabExpr_sound h1) hes' (tailOrSelf_iff.1 rfl) hk
  | .namedAccess e n, st, r, h => by
    rw [elabExpr] at h
    obtain ⟨⟨st1, i⟩, h1, h⟩ := bind_ok h
    obtain ⟨o, ho, h⟩ := bind_ok h
    cases o with
    | none => cases h
    | some r' =>
      cases h
      obtain ⟨es, k, hes, hk, rfl⟩ := ESt.aliasExport_ok ho
      exact .namedAccess (elabExpr_sound h1) hes hk
  | .new p args, st, r, h => by
    rw [elabExpr] at h
    split at h
    · cases h
    · rename_i hne
      obtain ⟨pk, hpk, h⟩ := bind_ok h
      obtain ⟨⟨st1, acc, fill⟩, h1, h⟩ := bind_ok h
      obtain ⟨⟨st2, acc2⟩, h2, h⟩ := bind_ok h
      obtain ⟨u, h3, h⟩ := bind_ok h
      cases u
      have hs := elabSpreads_sound h2
      have ha := elabArgs_sound h1
      cases fill with
      | true =>
        cases h
        exact .new hne (ECtx.package_ok hpk) ha hs (checkArgs_ok h3) (fun hf => nomatch hf)
      | false =>
        obtain ⟨u', h4, h⟩ := bind_ok h
        cases u'
        cases h
        exact .new hne (ECtx.package_ok hpk) ha hs (checkArgs_ok h3) (fun _ => checkAll_ok h4)

/-- **Inferred and named arguments elaborate soundly.** -/
theorem elabArgs_sound {cx : ECtx} :
    ∀ {args : List Arg} {imps : List String} {st : ESt} {acc : List (String × Nat)}
      {r : ESt × List (String × Nat) × Bool},
      elabArgs cx imps st acc args = .ok r → ElabArgs cx imps st acc args r
  | [], imps, st, acc, r, h => by
    rw [elabArgs] at h
    cases h
    exact .nil
  | .inferred x :: rest, imps, st, acc, r, h => by
    rw [elabArgs] at h
    obtain ⟨i, hi, h⟩ := bind_ok h
    obtain ⟨acc', ha, h⟩ := bind_ok h
    obtain ⟨hn, rfl⟩ := insertArg_ok ha
    exact .inferred (ESt.lookup_ok hi) (inferArg_spec _ _ _ _) hn (elabArgs_sound h)
  | .named a e :: rest, imps, st, acc, r, h => by
    rw [elabArgs] at h
    obtain ⟨⟨st1, i⟩, h1, h⟩ := bind_ok h
    obtain ⟨acc', ha, h⟩ := bind_ok h
    obtain ⟨hn, rfl⟩ := insertArg_ok ha
    exact .named (elabExpr_sound h1) (namedArg_iff.1 rfl) hn (elabArgs_sound h)
  | .spread x :: rest, imps, st, acc, r, h => by
    rw [elabArgs] at h
    exact .spread (elabArgs_sound h)
  | [.fill], imps, st, acc, r, h => by
    rw [elabArgs] at h
    cases h
    exact .fill
  | .fill :: _ :: _, imps, st, acc, r, h => by
    rw [elabArgs] at h
    cases h
end

/-! ## Statements -/

theorem ESt.bind_sound {st st' : ESt} {x : String} {i : Nat} (h : st.bind x i = .ok st') :
    Binds st x i st' := by
  unfold ESt.bind at h
  split at h
  · cases h
  · rename_i hn
    cases h
    have hl : st.scope.lookup x = none := by
      cases e : st.scope.lookup x with
      | none => rfl
      | some _ => rw [e] at hn; exact absurd rfl hn
    exact .mk hl

theorem ESt.exportAs_sound {st st' : ESt} {i : Nat} {n : String} (h : st.exportAs i n = .ok st') :
    ExportAs st i n st' := by
  unfold ESt.exportAs at h
  split at h
  · cases h
  · rename_i hd
    split at h
    · cases h
    · rename_i he
      cases h
      refine .mk (fun j hj => ?_) (by simpa using he)
      simpa [hj] using hd

theorem spreadExports_sound {es : Externs} {i : Nat} :
    ∀ {xs : Externs} {st : ESt} {r : ESt × Bool}, spreadExports es i st xs = .ok r →
      SpreadExports es i st xs r
  | [], st, r, h => by
    rw [spreadExports] at h
    cases h
    exact .nil
  | (n, k) :: rest, st, r, h => by
    rw [spreadExports] at h
    split at h
    · rename_i hx
      exact .skip hx (spreadExports_sound h)
    · rename_i hx
      obtain ⟨st2, h2, h⟩ := bind_ok (h : ((st.aliasAt i n k).1.exportAs (st.aliasAt i n k).2 n >>= _) = _)
      obtain ⟨⟨st3, b⟩, h3, h⟩ := bind_ok h
      cases h
      exact .emit (by simpa using hx) (ESt.exportAs_sound h2) (spreadExports_sound h3)

/-- **Statements elaborate soundly.** -/
theorem elabStmt_sound {cx : ECtx} {st st' : ESt} :
    ∀ {s : Stmt}, elabStmt cx st s = .ok st' → ElabStmt cx st s st'
  | .import i, h => by
    rw [elabStmt] at h
    obtain ⟨k, hk, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · rename_i hn
      exact .import hk hn (ESt.bind_sound h)
  | .type t, h => by
    rw [elabStmt] at h
    obtain ⟨⟨n, k⟩, hk, h⟩ := bind_ok h
    cases hx : st.g.hasExport n with
    | true => simp [hx] at h
    | false =>
      simp only [hx, Bool.false_eq_true, ite_false] at h
      exact .type hk hx (ESt.bind_sound h)
  | .let x e, h => by
    rw [elabStmt] at h
    obtain ⟨⟨st1, i⟩, h1, h⟩ := bind_ok h
    exact .let (elabExpr_sound h1) (ESt.bind_sound h)
  | .export e opts, h => by
    rw [elabStmt] at h
    obtain ⟨⟨st1, i⟩, h1, h⟩ := bind_ok h
    have he := elabExpr_sound h1
    cases opts with
    | none =>
      dsimp only at h
      split at h
      · rename_i n hn
        exact .exportNone he (exportName?_iff.1 hn) (ESt.exportAs_sound h)
      · cases h
    | rename n => exact .exportRename he (ESt.exportAs_sound h)
    | spread =>
      dsimp only at h
      obtain ⟨es, hes, h⟩ := bind_ok h
      obtain ⟨⟨st2, done⟩, h2, h⟩ := bind_ok h
      cases done with
      | false => cases h
      | true =>
        cases h
        exact .exportSpread he (ESt.exportsOf_ok hes) (spreadExports_sound h2)

theorem elabStmts_sound {cx : ECtx} :
    ∀ {ss : List Stmt} {st st' : ESt}, elabStmts cx st ss = .ok st' → ElabStmts cx st ss st'
  | [], st, st', h => by
    rw [elabStmts] at h
    cases h
    exact .nil
  | s :: ss, st, st', h => by
    rw [elabStmts] at h
    obtain ⟨st1, h1, h⟩ := bind_ok h
    exact .cons (elabStmt_sound h1) (elabStmts_sound h)

/-! ## Targets and documents -/

theorem checkTargetImports_ok {wi : Externs} :
    ∀ {xs : Externs}, checkTargetImports wi xs = .ok () → ∀ p ∈ xs, ∃ k, wi.find p.1 = some k ∧ Sub k.promote p.2
  | [], _ => fun _ hp => nomatch hp
  | (n, k) :: rest, h => by
    rw [checkTargetImports] at h
    split at h
    · cases h
    · rename_i k' hk'
      split at h
      · rename_i hs
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨k', hk', (sub_iff _ _).1 hs⟩
        · exact checkTargetImports_ok h p hp
      · cases h

theorem checkTargetExports_ok {g : CGraph} :
    ∀ {xs : Externs}, checkTargetExports g xs = .ok () →
      ∀ p ∈ xs, ∃ j, g.exports.lookup p.1 = some j ∧ Sub (g.kindOf j) p.2.promote
  | [], _ => fun _ hp => nomatch hp
  | (n, k) :: rest, h => by
    rw [checkTargetExports] at h
    split at h
    · cases h
    · rename_i j hj
      split at h
      · rename_i hs
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨j, hj, (sub_iff _ _).1 hs⟩
        · exact checkTargetExports_ok h p hp
      · cases h

theorem checkTarget_ok {g : CGraph} {wi we : Externs} (h : checkTarget g wi we = .ok ()) :
    TargetOk g wi we := by
  obtain ⟨u, h1, h2⟩ := bind_ok h
  cases u
  exact ⟨checkTargetImports_ok h1, checkTargetExports_ok h2⟩

theorem checkTargets_ok {cx : ECtx} {st : ESt} {g : CGraph} {t : Option PkgPath}
    (h : checkTargets cx st g t = .ok ()) :
    ∀ p, t = some p → ∃ i wi we, resolvePath cx st p = .ok (.type (.comp i wi we)) ∧ TargetOk g wi we := by
  intro p hp
  subst hp
  rw [checkTargets] at h
  obtain ⟨k, hk, h⟩ := bind_ok h
  split at h
  · rename_i i wi we
    exact ⟨i, wi, we, hk, checkTarget_ok h⟩
  · cases h

/-- **The elaborator is sound**: a document it elaborates to `g` elaborates to `g` in
the relational specification. -/
theorem elabDoc_sound {env : PkgEnv} {d : Document} {g : CGraph} (h : elabDoc env d = .ok g) :
    ElabDoc env d g := by
  rw [elabDoc] at h
  obtain ⟨st, h1, h⟩ := bind_ok h
  obtain ⟨g1, h2, h⟩ := bind_ok h
  obtain ⟨u, h3, h⟩ := bind_ok h
  cases u
  cases h
  exact .mk (elabStmts_sound h1) h2 (checkTargets_ok h3)

end Silmaril.Wasm.Wac
