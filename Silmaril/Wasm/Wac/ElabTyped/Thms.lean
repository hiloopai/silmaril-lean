module

public import Silmaril.Wasm.Wac.Elab.Thms

/-!
# WAC elaboration: the composition is well typed and fully explicit

`elabDoc_typed`: when every package of the registry has WIT-shaped imports
(`EnvWit`: instances of WIT interfaces, functions, types), the graph of an elaborated
document

* passes every import of every instantiated package as a named argument
  (`CGraph.Complete`: the IR is fully explicit), and
* type-checks: every argument is an import of its package, at a subtype (`CGraph.Typed`),
  for explicit arguments (checked by the elaborator) and implicit ones (merged imports,
  `Implicit.resolve_typed`).

The proof is an induction on the relational derivation of `Silmaril.Wasm.Wac.ElabSpec`
(via `elabDoc_sound`): every state reached has its local names bound to existing
nodes, and every instantiation node created refers to earlier nodes and type-checks.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Syntax

/-- Every package of the registry has WIT-shaped imports. -/
def EnvWit (env : PkgEnv) : Prop := ∀ key pk, env.lookup key = some pk → Implicit.WitEx pk.imports

/-- A node is well formed in `g`: an instantiation has WIT-shaped imports and arguments
that refer to nodes of `g` and type-check. -/
def NodeOk (g : CGraph) (nd : CNode) : Prop :=
  ∀ p imps args, nd.op = .inst p imps args →
    Implicit.WitEx imps ∧ ∀ a ∈ args, a.2 < g.nodes.length ∧ ∃ k, imps.find a.1 = some k ∧ Sub (g.kindOf a.2) k

/-- The invariant of elaboration states. -/
structure ESt.Inv (st : ESt) : Prop where
  scope : ∀ p ∈ st.scope, p.2 < st.g.nodes.length
  nodes : ∀ nd ∈ st.g.nodes, NodeOk st.g nd

/-- `st'` extends the nodes of `st`. -/
def ESt.Ext (st st' : ESt) : Prop := ∃ l, st'.g.nodes = st.g.nodes ++ l

theorem ESt.Ext.refl (st : ESt) : st.Ext st := ⟨[], by simp⟩

theorem ESt.Ext.trans {a b c : ESt} (h1 : a.Ext b) (h2 : b.Ext c) : a.Ext c := by
  obtain ⟨l1, e1⟩ := h1
  obtain ⟨l2, e2⟩ := h2
  exact ⟨l1 ++ l2, by rw [e2, e1, List.append_assoc]⟩

theorem ESt.Ext.le {a b : ESt} (h : a.Ext b) : a.g.nodes.length ≤ b.g.nodes.length := by
  obtain ⟨l, e⟩ := h
  rw [e, List.length_append]; omega

theorem kindOf_ext {g g' : CGraph} {l : List CNode} (e : g'.nodes = g.nodes ++ l) {j : Nat}
    (hj : j < g.nodes.length) : g'.kindOf j = g.kindOf j := by
  simp only [CGraph.kindOf, e, List.getElem?_append_left hj]

theorem NodeOk.mono {g g' : CGraph} {l : List CNode} (e : g'.nodes = g.nodes ++ l) {nd : CNode}
    (h : NodeOk g nd) : NodeOk g' nd := fun p imps args hop => by
  obtain ⟨hw, ha⟩ := h p imps args hop
  refine ⟨hw, fun a hm => ?_⟩
  obtain ⟨hlt, k, hk, hs⟩ := ha a hm
  have hlen : g.nodes.length ≤ g'.nodes.length := by rw [e, List.length_append]; omega
  exact ⟨Nat.lt_of_lt_of_le hlt hlen, k, hk, by rw [kindOf_ext e hlt]; exact hs⟩

/-! ## Basic steps -/

theorem ESt.add_inv {st : ESt} {nd : CNode} (hi : st.Inv) (hn : NodeOk st.g nd) :
    (st.add nd).1.Inv ∧ (st.add nd).2 < (st.add nd).1.g.nodes.length ∧ st.Ext (st.add nd).1 := by
  have e : (st.add nd).1.g.nodes = st.g.nodes ++ [nd] := rfl
  refine ⟨⟨fun p hp => ?_, fun x hx => ?_⟩, by simp [ESt.add, CGraph.add], ⟨[nd], e⟩⟩
  · have := hi.scope p hp; rw [e, List.length_append]; omega
  · rcases List.mem_append.1 (e ▸ hx) with h | h
    · exact (hi.nodes x h).mono e
    · rw [List.mem_singleton.1 h]; exact hn.mono e

theorem nodeOk_of_not_inst {g : CGraph} {nd : CNode} (h : ∀ p imps args, nd.op ≠ .inst p imps args) :
    NodeOk g nd := fun p imps args hop => absurd hop (h p imps args)

theorem nodeOk_imp (g : CGraph) (n : String) (k : Kind) : NodeOk g ⟨.imp n, k⟩ :=
  fun _ _ _ h => nomatch h

theorem nodeOk_defn (g : CGraph) (n : String) (k : Kind) : NodeOk g ⟨.defn n, k⟩ :=
  fun _ _ _ h => nomatch h

theorem findAlias_lt {g : CGraph} {i : Nat} {n : String} {j : Nat} (h : g.findAlias i n = some j) :
    j < g.nodes.length := by
  unfold CGraph.findAlias at h
  exact (List.findIdx?_eq_some_iff_getElem.1 h).1

theorem ESt.aliasAt_inv {st : ESt} {i : Nat} {n : String} {k : Kind} (hi : st.Inv) :
    (st.aliasAt i n k).1.Inv ∧ (st.aliasAt i n k).2 < (st.aliasAt i n k).1.g.nodes.length ∧
      st.Ext (st.aliasAt i n k).1 := by
  unfold ESt.aliasAt
  split
  · rename_i j hj
    exact ⟨hi, findAlias_lt hj, ESt.Ext.refl st⟩
  · exact ESt.add_inv hi (fun _ _ _ h => nomatch h)

theorem Binds.inv {st st' : ESt} {x : String} {i : Nat} (h : Binds st x i st') (hi : st.Inv)
    (hlt : i < st.g.nodes.length) : st'.Inv ∧ st.Ext st' := by
  cases h with
  | mk _ =>
    refine ⟨⟨fun p hp => ?_, hi.nodes⟩, ESt.Ext.refl _⟩
    rcases List.mem_append.1 hp with h | h
    · exact hi.scope p h
    · rw [List.mem_singleton.1 h]; exact hlt

theorem mem_of_lookup {l : List (String × Nat)} {x : String} {i : Nat} (h : l.lookup x = some i) :
    (x, i) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨y, v⟩ := p
    by_cases hx : x = y
    · subst hx
      have e : v = i := by simpa [List.lookup] using h
      simp [e]
    · have h' : l.lookup x = some i := by simpa [List.lookup, beq_false_of_ne hx] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem lookup_lt {st : ESt} (hi : st.Inv) {x : String} {i : Nat} (h : st.scope.lookup x = some i) :
    i < st.g.nodes.length := hi.scope _ (mem_of_lookup h)

/-! ## Arguments and expressions -/

/-- Every argument refers to a node of `st`. -/
def AccLt (st : ESt) (acc : List (String × Nat)) : Prop := ∀ a ∈ acc, a.2 < st.g.nodes.length

theorem AccLt.mono {st st' : ESt} {acc : List (String × Nat)} (h : AccLt st acc) (he : st.Ext st') :
    AccLt st' acc := fun a ha => Nat.lt_of_lt_of_le (h a ha) he.le

theorem AccLt.snoc {st : ESt} {acc : List (String × Nat)} {n : String} {i : Nat} (h : AccLt st acc)
    (hi : i < st.g.nodes.length) : AccLt st (acc ++ [(n, i)]) := fun a ha => by
  rcases List.mem_append.1 ha with h1 | h1
  · exact h a h1
  · rw [List.mem_singleton.1 h1]; exact hi

/-- What an elaboration step from `st` to `st'` preserves. -/
structure Step (st st' : ESt) : Prop where
  inv : st'.Inv
  ext : st.Ext st'

theorem Step.trans {a b c : ESt} (h1 : Step a b) (h2 : Step b c) : Step a c := ⟨h2.inv, h1.ext.trans h2.ext⟩

theorem aliasPlan_inv {es : Externs} {i : Nat} :
    ∀ (plan : List (String × String)) (st : ESt) (acc : List (String × Nat)), st.Inv → AccLt st acc →
      Step st (aliasPlan es i st acc plan).1 ∧ AccLt (aliasPlan es i st acc plan).1 (aliasPlan es i st acc plan).2
  | [], st, acc, hi, ha => ⟨⟨hi, ESt.Ext.refl st⟩, ha⟩
  | (n, e) :: rest, st, acc, hi, ha => by
    obtain ⟨hi1, hlt, he1⟩ := ESt.aliasAt_inv (st := st) (i := i) (n := e) (k := (es.find e).getD default) hi
    have ha1 : AccLt (st.aliasAt i e _).1 (acc ++ [(n, (st.aliasAt i e _).2)]) := (ha.mono he1).snoc hlt
    obtain ⟨hs, ha2⟩ := aliasPlan_inv rest _ _ hi1 ha1
    exact ⟨Step.trans ⟨hi1, he1⟩ hs, ha2⟩

theorem ElabSpreads.inv {imps : List String} {st : ESt} {acc : List (String × Nat)} {xs : List String}
    {r : ESt × List (String × Nat)} (h : ElabSpreads imps st acc xs r) (hi : st.Inv) (ha : AccLt st acc) :
    Step st r.1 ∧ AccLt r.1 r.2 := by
  induction h with
  | nil => exact ⟨⟨hi, ESt.Ext.refl _⟩, ha⟩
  | cons _ _ _ _ _ ih =>
    obtain ⟨hs1, ha1⟩ := aliasPlan_inv _ _ _ hi ha
    obtain ⟨hs2, ha2⟩ := ih hs1.inv ha1
    exact ⟨hs1.trans hs2, ha2⟩

/-- The instantiation node of a `new`. -/
theorem new_nodeOk {env : PkgEnv} (hE : EnvWit env) {key : String} {pk : PkgType} (hpk : env.lookup key = some pk)
    {st : ESt} {acc : List (String × Nat)} (ha : AccLt st acc) (ht : ArgsTyped pk.imports st.g acc) (ex : Externs) :
    NodeOk st.g ⟨.inst key pk.imports acc, .inst none ex⟩ := fun p imps args hop => by
  cases hop
  exact ⟨hE key pk hpk, fun a hm => ⟨ha a hm, ht a hm⟩⟩

mutual
theorem ElabExpr.inv {cx : ECtx} (hE : EnvWit cx.env) :
    ∀ {st : ESt} {e : Expr} {r : ESt × Nat}, ElabExpr cx st e r → st.Inv →
      Step st r.1 ∧ r.2 < r.1.g.nodes.length
  | _, _, _, .ident hx, hi => ⟨⟨hi, ESt.Ext.refl _⟩, lookup_lt hi hx⟩
  | _, _, _, .paren h, hi => ElabExpr.inv hE h hi
  | _, _, _, .access h _ _ _, hi | _, _, _, .namedAccess h _ _, hi => by
    obtain ⟨hs, _⟩ := ElabExpr.inv hE h hi
    obtain ⟨hi2, hlt, he2⟩ := ESt.aliasAt_inv hs.inv
    exact ⟨hs.trans ⟨hi2, he2⟩, hlt⟩
  | _, _, _, .new _ hpk ha hsp ht _, hi => by
    obtain ⟨hs1, ha1⟩ := ElabArgs.inv hE ha hi (fun _ hm => nomatch hm)
    obtain ⟨hs2, ha2⟩ := hsp.inv hs1.inv ha1
    obtain ⟨hi3, hlt, he3⟩ := ESt.add_inv hs2.inv (new_nodeOk hE hpk ha2 ht _)
    exact ⟨(hs1.trans hs2).trans ⟨hi3, he3⟩, hlt⟩

theorem ElabArgs.inv {cx : ECtx} (hE : EnvWit cx.env) :
    ∀ {imps : List String} {st : ESt} {acc : List (String × Nat)} {args : List Arg}
      {r : ESt × List (String × Nat) × Bool}, ElabArgs cx imps st acc args r → st.Inv → AccLt st acc →
      Step st r.1 ∧ AccLt r.1 r.2.1
  | _, _, _, _, _, .nil, hi, ha => ⟨⟨hi, ESt.Ext.refl _⟩, ha⟩
  | _, _, _, _, _, .fill, hi, ha => ⟨⟨hi, ESt.Ext.refl _⟩, ha⟩
  | _, _, _, _, _, .spread h, hi, ha => ElabArgs.inv hE h hi ha
  | _, _, _, _, _, .inferred hx _ _ h, hi, ha => ElabArgs.inv hE h hi (ha.snoc (lookup_lt hi hx))
  | _, _, _, _, _, .named he _ _ h, hi, ha => by
    obtain ⟨hs1, hlt⟩ := ElabExpr.inv hE he hi
    obtain ⟨hs2, ha2⟩ := ElabArgs.inv hE h hs1.inv ((ha.mono hs1.ext).snoc hlt)
    exact ⟨hs1.trans hs2, ha2⟩
end

/-! ## Statements -/

/-- Changing the exports keeps the invariant. -/
theorem ESt.Inv.exports {st : ESt} (hi : st.Inv) (ex : List (String × Nat)) :
    ESt.Inv { st with g := { st.g with exports := ex } } := ⟨hi.scope, hi.nodes⟩

theorem ExportAs.step {st st' : ESt} {i : Nat} {n : String} (h : ExportAs st i n st') (hi : st.Inv) :
    Step st st' := by
  cases h with
  | mk _ _ => exact ⟨hi.exports _, ⟨[], by simp⟩⟩

theorem SpreadExports.step {es : Externs} {i : Nat} {st : ESt} {xs : Externs} {r : ESt × Bool}
    (h : SpreadExports es i st xs r) (hi : st.Inv) : Step st r.1 := by
  induction h with
  | nil => exact ⟨hi, ESt.Ext.refl _⟩
  | skip _ _ ih => exact ih hi
  | emit _ hx _ ih =>
    obtain ⟨hi1, _, he1⟩ := ESt.aliasAt_inv hi
    have hs : Step _ _ := hx.step hi1
    exact (Step.trans ⟨hi1, he1⟩ hs).trans (ih hs.inv)

theorem ElabStmt.step {cx : ECtx} (hE : EnvWit cx.env) {st st' : ESt} {s : Stmt}
    (h : ElabStmt cx st s st') (hi : st.Inv) : Step st st' := by
  cases h with
  | «import» _ _ hb =>
    obtain ⟨hi1, hlt, he1⟩ := ESt.add_inv hi (nodeOk_imp _ _ _)
    obtain ⟨hi2, he2⟩ := hb.inv hi1 hlt
    exact ⟨hi2, he1.trans he2⟩
  | type _ _ hb =>
    obtain ⟨hi1, hlt, he1⟩ := ESt.add_inv hi (nodeOk_defn _ _ _)
    obtain ⟨hi2, he2⟩ := hb.inv (hi1.exports _) hlt
    exact ⟨hi2, he1.trans (ESt.Ext.trans ⟨[], by simp⟩ he2)⟩
  | «let» he hb =>
    obtain ⟨hs, hlt⟩ := ElabExpr.inv hE he hi
    obtain ⟨hi2, he2⟩ := hb.inv hs.inv hlt
    exact ⟨hi2, hs.ext.trans he2⟩
  | exportNone he _ hx | exportRename he hx =>
    obtain ⟨hs, _⟩ := ElabExpr.inv hE he hi
    exact hs.trans (hx.step hs.inv)
  | exportSpread he _ hx =>
    obtain ⟨hs, _⟩ := ElabExpr.inv hE he hi
    exact hs.trans (hx.step hs.inv)

theorem ElabStmts.step {cx : ECtx} (hE : EnvWit cx.env) {st st' : ESt} {ss : List Stmt}
    (h : ElabStmts cx st ss st') (hi : st.Inv) : Step st st' := by
  induction h with
  | nil => exact ⟨hi, ESt.Ext.refl _⟩
  | cons h1 _ ih =>
    have hs : Step _ _ := h1.step hE hi
    exact hs.trans (ih hs.inv)

/-! ## Documents -/

theorem ESt.Inv.explicit {st : ESt} (hi : st.Inv) : Implicit.ExplicitTyped st.g :=
  fun nd hnd p imps args hop => (hi.nodes nd hnd p imps args hop).2

theorem ESt.Inv.wit {st : ESt} (hi : st.Inv) : Implicit.ImportsWit st.g :=
  fun nd hnd p imps args hop => (hi.nodes nd hnd p imps args hop).1

/-- **The elaborated composition is fully explicit and well typed** (for registries of
WIT-shaped packages). -/
theorem ElabDoc.typed {env : PkgEnv} (hE : EnvWit env) {d : Document} {g : CGraph}
    (h : ElabDoc env d g) : g.Complete ∧ g.Typed := by
  cases h with
  | mk hs hr _ =>
    have hi : ESt.Inv {} := ⟨(fun _ hp => nomatch hp), (fun _ hn => nomatch hn)⟩
    have hst : Step _ _ := hs.step hE hi
    exact ⟨Implicit.resolve_complete hr, Implicit.resolve_typed hr hst.inv.explicit hst.inv.wit⟩

/-- **The elaborator's output is fully explicit and well typed.** -/
theorem elabDoc_typed {env : PkgEnv} (hE : EnvWit env) {d : Document} {g : CGraph}
    (h : elabDoc env d = .ok g) : g.Complete ∧ g.Typed :=
  (elabDoc_sound h).typed hE

end Silmaril.Wasm.Wac
