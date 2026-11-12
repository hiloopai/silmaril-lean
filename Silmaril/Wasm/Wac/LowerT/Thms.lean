module

public import Silmaril.Wasm.Wac.LowerT.Defs

/-!
# WAC: the typed lowering meets its specification

* `graph_spec`: if `LowerT.graph S c` succeeds with `g`, the items `l` of `c` specify
  `g` (`Spec S l g`): declared imports (`Decls`), exports (`Exps`), and every node
  (`NodeAt`), with as many nodes as instantiations;
* `runT_inv`: the invariant behind it (`Inv`): the instance and function index spaces of
  the state have exactly `count` entries, and each entry is what `Den` says the index
  denotes; the type space is `typesOf`, the component count `count .comp`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.LowerT

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wac.Lower (Loc qual suffix?)

variable {S : Nat → PkgSig}

/-! ## Counting -/

theorem typesOf_snoc (l : List Item) (x : Item) : typesOf (l ++ [x]) = tyStep (typesOf l) x := by
  simp [typesOf, List.foldl_append]

theorem count_snoc (s : Sp) (l : List Item) (x : Item) :
    count s (l ++ [x]) = count s l + (if x.sp == some s then 1 else 0) := by
  simp [count, List.countP_append]

theorem nodeCount_snoc (l : List Item) (x : Item) :
    nodeCount (l ++ [x]) = nodeCount l + (if x.isNode then 1 else 0) := by
  simp [nodeCount, List.countP_append]

theorem count_snoc_self {s : Sp} {l : List Item} {x : Item} (h : x.sp = some s) :
    count s (l ++ [x]) = count s l + 1 := by
  simp [count_snoc, h]

theorem count_snoc_other {s : Sp} {l : List Item} {x : Item} (h : x.sp ≠ some s) :
    count s (l ++ [x]) = count s l := by
  simp [count_snoc, h]

theorem getElem?_snoc {α : Type} {xs : List α} {a b : α} {j : Nat}
    (h : (xs ++ [a])[j]? = some b) : xs[j]? = some b ∨ (j = xs.length ∧ b = a) := by
  rcases Nat.lt_or_ge j xs.length with hj | hj
  · left
    rwa [List.getElem?_append_left hj] at h
  · right
    rw [List.getElem?_append_right hj] at h
    cases hk : j - xs.length with
    | zero =>
      rw [hk] at h
      have hb : a = b := by simpa using h
      exact ⟨by omega, hb.symm⟩
    | succ k =>
      rw [hk] at h
      simp at h

/-! ## The invariant -/

/-- The state after the items `l`. -/
structure Inv (S : Nat → PkgSig) (l : List Item) (st : TSt) : Prop where
  types : st.types = typesOf l
  comps : st.comps = count .comp l
  insts_len : st.insts.length = count .inst l
  funcs_len : st.funcs.length = count .func l
  nodes_len : st.nodes.length = nodeCount l
  insts : ∀ j e, st.insts[j]? = some e → Den S l .inst j (.inl e)
  funcs : ∀ j e, st.funcs[j]? = some e → Den S l .func j (.inr e)
  nodes : ∀ k n, st.nodes[k]? = some n → NodeAt S l k n
  decls : Decls S l st.imports
  exps : Exps S l st.exports

theorem inv_nil : Inv S [] {} :=
  ⟨rfl, rfl, rfl, rfl, rfl, by simp, by simp, by simp, .nil, .nil⟩

/-- An index space after one more item: unchanged, or one more entry. -/
def Grows {α : Type} (old new : List α) (here : Bool) (P : α → Prop) : Prop :=
  (new = old ∧ here = false) ∨ (∃ e, new = old ++ [e] ∧ here = true ∧ P e)

theorem grows_len {α : Type} {old new : List α} {here : Bool} {P : α → Prop} {n : Nat}
    (h : Grows old new here P) (hl : old.length = n) :
    new.length = n + (if here then 1 else 0) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨e, rfl, rfl, _⟩
  · simpa using hl
  · simp [hl]

theorem grows_get {α : Type} {old new : List α} {here : Bool} {P : α → Prop} {Q : Nat → α → Prop}
    (h : Grows old new here P) (hold : ∀ j e, old[j]? = some e → Q j e)
    (hnew : ∀ e, P e → Q old.length e) : ∀ j e, new[j]? = some e → Q j e := by
  rcases h with ⟨rfl, _⟩ | ⟨e₀, rfl, _, hp⟩
  · exact hold
  · intro j e hj
    rcases getElem?_snoc hj with h1 | ⟨rfl, rfl⟩
    · exact hold j e h1
    · exact hnew e hp

/-- The invariant after one more item, from how each part of the state changed. -/
theorem Inv.snoc {l : List Item} {st st' : TSt} {x : Item} (h : Inv S l st)
    (htypes : st'.types = tyStep st.types x)
    (hcomps : st'.comps = st.comps + (if x.sp == some .comp then 1 else 0))
    (hinsts : Grows st.insts st'.insts (x.sp == some .inst)
      fun e => Den S (l ++ [x]) .inst (count .inst l) (.inl e))
    (hfuncs : Grows st.funcs st'.funcs (x.sp == some .func)
      fun e => Den S (l ++ [x]) .func (count .func l) (.inr e))
    (hnodes : Grows st.nodes st'.nodes x.isNode fun n => NodeAt S (l ++ [x]) (nodeCount l) n)
    (hdecls : Decls S (l ++ [x]) st'.imports) (hexps : Exps S (l ++ [x]) st'.exports) :
    Inv S (l ++ [x]) st' where
  types := by rw [htypes, h.types, typesOf_snoc]
  comps := by rw [hcomps, h.comps, count_snoc]
  insts_len := by rw [grows_len hinsts h.insts_len, count_snoc]
  funcs_len := by rw [grows_len hfuncs h.funcs_len, count_snoc]
  nodes_len := by rw [grows_len hnodes h.nodes_len, nodeCount_snoc]
  insts := grows_get hinsts (fun j e hj => .there (h.insts j e hj)) fun e he => h.insts_len ▸ he
  funcs := grows_get hfuncs (fun j e hj => .there (h.funcs j e hj)) fun e he => h.funcs_len ▸ he
  nodes := grows_get hnodes (fun k n hk => .there (h.nodes k n hk)) fun n hn => h.nodes_len ▸ hn
  decls := hdecls
  exps := hexps

theorem grows_same {α : Type} {old : List α} {P : α → Prop} : Grows old old false P :=
  .inl ⟨rfl, rfl⟩

theorem grows_one {α : Type} {old : List α} {P : α → Prop} {e : α} (he : P e) :
    Grows old (old ++ [e]) true P :=
  .inr ⟨e, rfl, rfl, he⟩

/-! ## Arguments -/

theorem argT_func {l : List Item} {st : TSt} (h : Inv S l st) {c : Nat} {n : String} {j : Nat}
    {as : List (String × Src)} (ha : argT S st c (n, ⟨.func, j⟩) = .ok as) :
    ArgDen S l c (n, ⟨.func, j⟩) as := by
  simp only [argT] at ha
  split at ha
  · rename_i src ft hj
    split at ha
    · rename_i ht
      obtain rfl := (Except.ok.inj ha).symm
      exact .func (h.funcs j _ hj) ht
    · simp at ha
  · simp at ha

theorem argT_inst {l : List Item} {st : TSt} (h : Inv S l st) {c : Nat} {n : String} {j : Nat}
    {as : List (String × Src)} (ha : argT S st c (n, ⟨.instance, j⟩) = .ok as) :
    ArgDen S l c (n, ⟨.instance, j⟩) as := by
  simp only [argT] at ha
  split at ha
  · rename_i loc tab hj
    split at ha
    · rename_i hall
      obtain rfl := (Except.ok.inj ha).symm
      refine .inst (h.insts j _ hj) fun q f ty hm => ?_
      have hq : decide (tab.lookup f = some ty) = true := List.all_eq_true.1 hall (q, f, ty) hm
      simpa using hq
    · simp at ha
  · simp at ha

theorem argT_den {l : List Item} {st : TSt} (h : Inv S l st) {c : Nat} {a : String × SortIdx}
    {as : List (String × Src)} (ha : argT S st c a = .ok as) : ArgDen S l c a as := by
  obtain ⟨n, ⟨srt, j⟩⟩ := a
  cases srt with
  | func => exact argT_func h ha
  | «instance» => exact argT_inst h ha
  | type => obtain rfl := (Except.ok.inj ha).symm; exact .type
  | component => obtain rfl := (Except.ok.inj ha).symm; exact .comp
  | value | core _ => simp [argT] at ha

theorem argsT_den {l : List Item} {st : TSt} (h : Inv S l st) {c : Nat} :
    ∀ {args : List (String × SortIdx)} {as : List (String × Src)},
      argsT S st c args = .ok as → ArgsDen S l c args as
  | [], as, ha => by
    obtain rfl := (Except.ok.inj ha).symm
    exact .nil
  | a :: args, as, ha => by
    cases h1 : argT S st c a with
    | error e => simp [argsT, h1, Except.bind] at ha
    | ok x =>
      cases h2 : argsT S st c args with
      | error e => simp [argsT, h1, h2, Except.bind, Except.map] at ha
      | ok xs =>
        have e : as = x ++ xs := by
          simpa [argsT, h1, h2, Except.bind, Except.map] using ha.symm
        rw [e]
        exact .cons (argT_den h h1) (argsT_den h h2)

/-! ## One item -/

/-- How the state changes on the item `x`, apart from types and components. -/
structure StepOk (S : Nat → PkgSig) (l : List Item) (st : TSt) (x : Item) (st₁ : TSt) : Prop where
  insts : Grows st.insts st₁.insts (x.sp == some .inst)
    fun e => Den S (l ++ [x]) .inst (count .inst l) (.inl e)
  funcs : Grows st.funcs st₁.funcs (x.sp == some .func)
    fun e => Den S (l ++ [x]) .func (count .func l) (.inr e)
  nodes : Grows st.nodes st₁.nodes x.isNode fun n => NodeAt S (l ++ [x]) (nodeCount l) n
  decls : Decls S (l ++ [x]) st₁.imports
  exps : Exps S (l ++ [x]) st₁.exports

/-- An item that changes nothing but the type space or the component count. -/
theorem stepOk_same {l : List Item} {st : TSt} {x : Item}
    (hi : x.sp ≠ some .inst) (hf : x.sp ≠ some .func) (hn : x.isNode = false)
    (hd : Decls S (l ++ [x]) st.imports) (he : Exps S (l ++ [x]) st.exports) :
    StepOk S l st x st := by
  have hi' : (x.sp == some .inst) = false := by simpa using hi
  have hf' : (x.sp == some .func) = false := by simpa using hf
  exact ⟨hi' ▸ grows_same, hf' ▸ grows_same, hn ▸ grows_same, hd, he⟩

theorem importT_func {l : List Item} {st st₁ : TSt} {i : Import} {t : Nat} (h : Inv S l st)
    (hd : i.desc = .func t) (hs : importT st i = .ok st₁) : StepOk S l st (.imp i) st₁ := by
  simp only [importT, hd] at hs
  split at hs
  · rename_i ft ht
    obtain rfl := (Except.ok.inj hs).symm
    have ht' : (typesOf l)[t]? = some (.func ft) := h.types ▸ ht
    have hden := Den.impFunc (S := S) (l := l) hd ht'
    have hsp : (Item.imp i).sp = some .func := by simp [Item.sp, hd, descSp]
    refine ⟨?_, ?_, grows_same, .impFunc h.decls hden, .other (by simp) h.exps⟩
    · simp only [hsp]
      exact grows_same
    · simp only [hsp]
      exact grows_one hden
  · simp at hs

theorem importT_inst {l : List Item} {st st₁ : TSt} {i : Import} {t : Nat} (h : Inv S l st)
    (hd : i.desc = .instance t) (hs : importT st i = .ok st₁) : StepOk S l st (.imp i) st₁ := by
  simp only [importT, hd] at hs
  split at hs
  · rename_i ds ht
    split at hs
    · rename_i tab htab
      obtain rfl := (Except.ok.inj hs).symm
      have ht' : (typesOf l)[t]? = some (.inst ds) := h.types ▸ ht
      have hden := Den.impInst (S := S) (l := l) hd ht' (h.types ▸ htab)
      have hsp : (Item.imp i).sp = some .inst := by simp [Item.sp, hd, descSp]
      refine ⟨?_, ?_, grows_same, .impInst h.decls hden, .other (by simp) h.exps⟩
      · simp only [hsp]
        exact grows_one hden
      · simp only [hsp]
        exact grows_same
    · simp at hs
  · simp at hs

theorem importT_other {l : List Item} {st st₁ : TSt} {i : Import} (h : Inv S l st)
    (hd : descSp i.desc = some .comp ∨ descSp i.desc = some .type) (hs : importT st i = .ok st₁) :
    StepOk S l st (.imp i) st₁ := by
  have e : st₁ = st := by
    unfold importT at hs
    rcases hd with hd | hd <;> (split at hs <;> simp_all [descSp])
  subst e
  have hsp : (Item.imp i).sp = descSp i.desc := rfl
  refine stepOk_same ?_ ?_ rfl (.impOther hd h.decls) (.other (by simp) h.exps) <;>
    rcases hd with hd | hd <;> simp [hsp, hd]

theorem importT_ok {l : List Item} {st st₁ : TSt} {i : Import} (h : Inv S l st)
    (hs : importT st i = .ok st₁) : StepOk S l st (.imp i) st₁ := by
  cases hd : i.desc with
  | func t => exact importT_func h hd hs
  | «instance» t => exact importT_inst h hd hs
  | component t => exact importT_other h (.inl (by simp [hd, descSp])) hs
  | type t => exact importT_other h (.inr (by simp [hd, descSp])) hs
  | coreModule t | value t => simp [importT, hd] at hs

theorem instT_instantiate {st st₁ : TSt} {c : Nat} {args : List (String × SortIdx)}
    (hs : instT S st (.instantiate c args) = .ok st₁) :
    ∃ as, c < st.comps ∧ argsT S st c args = .ok as ∧ explicitArgs (S c) as = true ∧
      st₁ = { st with
        insts := st.insts ++ [(.node st.nodes.length none, (S c).exports)]
        nodes := st.nodes ++ [⟨c, as⟩] } := by
  simp only [instT] at hs
  split at hs
  · rename_i hc
    split at hs
    · rename_i as has
      split at hs
      · rename_i hex
        exact ⟨as, hc, has, hex, (Except.ok.inj hs).symm⟩
      · simp at hs
    · simp at hs
  · simp at hs

theorem instT_ok {l : List Item} {st st₁ : TSt} {e : InstanceExpr} (h : Inv S l st)
    (hs : instT S st e = .ok st₁) : StepOk S l st (.inst e) st₁ := by
  cases e with
  | exports _ => simp [instT] at hs
  | instantiate c args =>
    obtain ⟨as, hc, has, hex, rfl⟩ := instT_instantiate hs
    have hc' : c < count .comp l := h.comps ▸ hc
    have hargs : ArgsDen S l c args as := argsT_den h has
    have hnode : NodeAt S (l ++ [.inst (.instantiate c args)]) (nodeCount l) ⟨c, as⟩ :=
      .here hargs hex hc'
    have hden := Den.node hargs hex hc'
    rw [← h.nodes_len] at hden
    exact ⟨grows_one hden, grows_same, grows_one hnode,
      .other (by simp) h.decls, .other (by simp) h.exps⟩

theorem aliasT_func {l : List Item} {st st₁ : TSt} {i : Nat} {n : String}
    {loc : Loc} {tab : Table} (h : Inv S l st) (hi : st.insts[i]? = some (loc, tab))
    (hs : aliasT st ⟨.func, .«export» i n⟩ = .ok st₁) :
    StepOk S l st (.«alias» ⟨.func, .«export» i n⟩) st₁ := by
  have hdi := h.insts i _ hi
  simp only [aliasT, hi] at hs
  split at hs
  · rename_i ft hft
    obtain rfl := (Except.ok.inj hs).symm
    exact ⟨grows_same, grows_one (Den.aliasFunc hdi hft), grows_same,
      .other (by simp) h.decls, .other (by simp) h.exps⟩
  · simp at hs

theorem aliasT_export {l : List Item} {st st₁ : TSt} {srt : ItemSort} {i : Nat} {n : String}
    {loc : Loc} {tab : Table} (h : Inv S l st) (hi : st.insts[i]? = some (loc, tab))
    (hs : aliasT st ⟨srt, .«export» i n⟩ = .ok st₁) :
    StepOk S l st (.«alias» ⟨srt, .«export» i n⟩) st₁ := by
  cases srt with
  | func => exact aliasT_func h hi hs
  | «instance» =>
    obtain rfl := (Except.ok.inj (by simpa only [aliasT, hi] using hs)).symm
    exact ⟨grows_one (Den.aliasInst (h.insts i _ hi)), grows_same, grows_same,
      .other (by simp) h.decls, .other (by simp) h.exps⟩
  | type | component =>
    obtain rfl := (Except.ok.inj (by simpa only [aliasT, hi] using hs)).symm
    exact stepOk_same (by simp [Item.sp, spOfSort]) (by simp [Item.sp, spOfSort]) rfl
      (.other (by simp) h.decls) (.other (by simp) h.exps)
  | value | core _ => simp [aliasT, hi] at hs

theorem aliasT_ok {l : List Item} {st st₁ : TSt} {a : Alias} (h : Inv S l st)
    (hs : aliasT st a = .ok st₁) : StepOk S l st (.«alias» a) st₁ := by
  obtain ⟨srt, tgt⟩ := a
  cases tgt with
  | coreExport _ _ | outer _ _ => simp [aliasT] at hs
  | «export» i n =>
    cases hi : st.insts[i]? with
    | none => simp [aliasT, hi] at hs
    | some p => exact aliasT_export h hi hs

theorem exportT_func {l : List Item} {st st₁ : TSt} {nm : ExternName} {j : Nat}
    {d : Option ExternDesc} (h : Inv S l st) (hs : exportT st ⟨nm, ⟨.func, j⟩, d⟩ = .ok st₁) :
    StepOk S l st (.exp ⟨nm, ⟨.func, j⟩, d⟩) st₁ := by
  simp only [exportT] at hs
  split at hs
  · rename_i src ft hj
    obtain rfl := (Except.ok.inj hs).symm
    have hdj := h.funcs j _ hj
    exact ⟨grows_same, grows_one (Den.expFunc rfl hdj), grows_same,
      .other (by simp) h.decls, .func h.exps rfl hdj⟩
  · simp at hs

theorem exportT_inst {l : List Item} {st st₁ : TSt} {nm : ExternName} {j : Nat}
    {d : Option ExternDesc} (h : Inv S l st) (hs : exportT st ⟨nm, ⟨.instance, j⟩, d⟩ = .ok st₁) :
    StepOk S l st (.exp ⟨nm, ⟨.instance, j⟩, d⟩) st₁ := by
  simp only [exportT] at hs
  split at hs
  · rename_i loc tab hj
    obtain rfl := (Except.ok.inj hs).symm
    have hdj := h.insts j _ hj
    exact ⟨grows_one (Den.expInst rfl hdj), grows_same, grows_same,
      .other (by simp) h.decls, .inst h.exps rfl hdj⟩
  · simp at hs

theorem exportT_ok {l : List Item} {st st₁ : TSt} {e : Binary.Export} (h : Inv S l st)
    (hs : exportT st e = .ok st₁) : StepOk S l st (.exp e) st₁ := by
  obtain ⟨nm, ⟨srt, j⟩, d⟩ := e
  cases srt with
  | func => exact exportT_func h hs
  | «instance» => exact exportT_inst h hs
  | type | component =>
    obtain rfl := (Except.ok.inj hs).symm
    exact stepOk_same (by simp [Item.sp, spOfSort]) (by simp [Item.sp, spOfSort]) rfl
      (.other (by simp) h.decls) (.otherSort (by simp [spOfSort]) h.exps)
  | value | core _ => simp [exportT] at hs

theorem stepO_ok {l : List Item} {st st₁ : TSt} {x : Item} (h : Inv S l st)
    (hs : stepO S st x = .ok st₁) : StepOk S l st x st₁ := by
  cases x with
  | type t =>
    obtain rfl := (Except.ok.inj hs).symm
    exact stepOk_same (by simp [Item.sp]) (by simp [Item.sp]) rfl
      (.other (by simp) h.decls) (.other (by simp) h.exps)
  | comp =>
    obtain rfl := (Except.ok.inj hs).symm
    exact stepOk_same (by simp [Item.sp]) (by simp [Item.sp]) rfl
      (.other (by simp) h.decls) (.other (by simp) h.exps)
  | imp i => exact importT_ok h hs
  | inst e => exact instT_ok h hs
  | «alias» a => exact aliasT_ok h hs
  | exp e => exact exportT_ok h hs

theorem stepT_inv {l : List Item} {st st' : TSt} {x : Item} (h : Inv S l st)
    (hs : stepT S st x = .ok st') : Inv S (l ++ [x]) st' := by
  cases h1 : stepO S st x with
  | error e => simp [stepT, h1, Except.map] at hs
  | ok st₁ =>
    have e : st' = { st₁ with
        types := tyStep st.types x
        comps := st.comps + (if x.sp == some .comp then 1 else 0) } := by
      simpa [stepT, h1, Except.map] using hs.symm
    subst e
    have k := stepO_ok h h1
    exact h.snoc rfl rfl k.insts k.funcs k.nodes k.decls k.exps

/-- **The invariant of the lowering.** -/
theorem runT_inv {l : List Item} {st : TSt} (h : Inv S l st) :
    ∀ {xs : List Item} {st' : TSt}, runT S st xs = .ok st' → Inv S (l ++ xs) st'
  | [], st', hs => by
    obtain rfl := (Except.ok.inj hs).symm
    simpa using h
  | x :: xs, st', hs => by
    cases h1 : stepT S st x with
    | error e => simp [runT, h1, Except.bind] at hs
    | ok st₁ =>
      have h2 : runT S st₁ xs = .ok st' := by simpa [runT, h1, Except.bind] using hs
      have r := runT_inv (stepT_inv h h1) h2
      simpa using r

/-- **The typed lowering is sound for its specification**: the graph is the one the
items of the component specify, and the index spaces have the sizes the items give. -/
theorem graph_spec {c : Ast} {g : Graph} (hg : graph S c = .ok g) :
    ∃ l st, items c = some l ∧ Spec S l g ∧ Inv S l st := by
  unfold graph at hg
  split at hg
  · split at hg
    · rename_i l hl
      cases hr : runT S {} l with
      | error e => simp [hr, Except.map] at hg
      | ok st =>
        have e : g = ⟨st.imports, st.nodes, st.exports⟩ := by simpa [hr, Except.map] using hg.symm
        subst e
        have hi : Inv S l st := by simpa using runT_inv inv_nil hr
        exact ⟨l, st, hl, ⟨hi.decls, hi.exps, hi.nodes_len, hi.nodes⟩, hi⟩
    · simp at hg
  · simp at hg

end Silmaril.Wasm.Wac.LowerT
