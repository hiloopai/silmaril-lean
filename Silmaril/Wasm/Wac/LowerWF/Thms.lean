module

public import Silmaril.Wasm.Wac.LowerT.Thms
public import Silmaril.Wasm.Wac.Graph.Thms

/-!
# WAC: the typed lowering gives well-formed, fully typed graphs

* `graph_wf`: the graph of `LowerT.graph` is well formed (`Graph.WF`): every argument of
  an instance refers to a declared import or to an export of an *earlier* instance, and
  every export to a declared import or an export of some instance;
* `graph_iface`: every import of the composition (`Graph.iface`, which `Graph.toComp`
  uses) is a declared import, with the function type the WAT gives it. So the
  placeholder `anyTy` of `Lower.graph` never occurs, and the imports of
  `LowerT.toComp P c` are the WAT's typed imports, merged.

The proof keeps a resolution invariant (`RInv`) of the lowering state: every entry of
the instance and function index spaces, every argument of every node and every export
resolves in the state.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.LowerT

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wac.Lower (Loc qual suffix?)

variable {S : Nat → PkgSig}

/-! ## Names -/

theorem eq_qual_of_sfx {n q f : String} (h : sfx? n q = some f) : q = qual n f := by
  unfold sfx? at h
  split at h
  · rename_i hs
    have hp : (n.toList ++ ['#']) <+: q.toList := List.isPrefixOf_iff_prefix.1 hs
    obtain ⟨r, hr⟩ := hp
    have hf : f = String.ofList (q.toList.drop (n.length + 1)) := (Option.some.inj h).symm
    have hl : (n.toList ++ ['#']).length = n.length + 1 := by simp [String.length_toList]
    have hd : q.toList.drop (n.length + 1) = r := by rw [← hr, ← hl, List.drop_left]
    apply String.toList_inj.1
    rw [hf, hd, ← hr]
    simp [qual]
  · simp at h

/-- `sfx?` is `Lower.suffix?`. -/
theorem sfx_eq_suffix (n q : String) : sfx? n q = suffix? n q := by
  have he : (n ++ "#").toList = n.toList ++ ['#'] := by simp
  have hb : ((n.toList ++ ['#']).isPrefixOf q.toList = true) ↔ q.startsWith (n ++ "#") = true := by
    rw [List.isPrefixOf_iff_prefix, String.startsWith_string_iff, he]
  unfold sfx? suffix?
  by_cases h : (n.toList ++ ['#']).isPrefixOf q.toList = true
  · simp [h, hb.1 h]
  · have h' : ¬ q.startsWith (n ++ "#") = true := fun h' => h (hb.2 h')
    simp [h, h']

theorem func_inst (loc : Loc) (n f : String) : (loc.inst n).func f = loc.func (qual n f) := by
  cases loc with
  | imp q => simp [Loc.inst, Loc.func, qual, String.append_assoc]
  | node k p => cases p <;> simp [Loc.inst, Loc.func, qual, String.append_assoc]

theorem mem_names_subTable {n f : String} {tab : Table} (h : f ∈ names (subTable n tab)) :
    qual n f ∈ names tab := by
  obtain ⟨⟨f', ty⟩, hm, rfl⟩ := List.mem_map.1 h
  obtain ⟨⟨q, ty'⟩, hq, hs⟩ := List.mem_filterMap.1 hm
  obtain ⟨f'', hsuf, he⟩ := Option.map_eq_some_iff.1 hs
  have he' : f'' = f' := by simpa using congrArg Prod.fst he
  have hq' : q = qual n f' := he' ▸ eq_qual_of_sfx hsuf
  exact List.mem_map.2 ⟨(q, ty'), hq, hq'⟩

/-! ## The resolution invariant -/

/-- A reference resolves in the state: a declared import, or an export of a node. -/
def SrcRes (S : Nat → PkgSig) (st : TSt) : Src → Prop
  | .imp x => x ∈ names st.imports
  | .out k q => ∃ n, st.nodes[k]? = some n ∧ q ∈ names (S n.pkg).exports

/-- The state only grows: imports and nodes are extended at the end. -/
def Ext (st st' : TSt) : Prop := (∃ I, st'.imports = st.imports ++ I) ∧ ∃ N, st'.nodes = st.nodes ++ N

theorem Ext.refl (st : TSt) : Ext st st := ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem getElem?_append_some {α : Type} {xs ys : List α} {k : Nat} {a : α}
    (h : xs[k]? = some a) : (xs ++ ys)[k]? = some a := by
  have hk : k < xs.length := by
    by_contra hc
    have hn : xs[k]? = none := List.getElem?_eq_none (by omega)
    simp [hn] at h
  rw [List.getElem?_append_left hk, h]

theorem SrcRes.mono {st st' : TSt} (he : Ext st st') : ∀ {s : Src}, SrcRes S st s → SrcRes S st' s
  | .imp x, h => by
    obtain ⟨I, hI⟩ := he.1
    have h' : x ∈ names (st.imports ++ I) := by simp only [names, List.map_append]; exact List.mem_append_left _ h
    simpa [SrcRes, hI] using h'
  | .out k q, h => by
    obtain ⟨N, hN⟩ := he.2
    obtain ⟨n, hn, hq⟩ := h
    exact ⟨n, hN ▸ getElem?_append_some hn, hq⟩

/-- The resolution invariant. -/
structure RInv (S : Nat → PkgSig) (st : TSt) : Prop where
  insts : ∀ (j : Nat) (loc : Loc) (tab : Table), st.insts[j]? = some (loc, tab) → ∀ f ∈ names tab, SrcRes S st (loc.func f)
  funcs : ∀ (j : Nat) (src : Src) (ft : FuncTy), st.funcs[j]? = some (src, ft) → SrcRes S st src
  nodes : ∀ (k : Nat) (n : Inst), st.nodes[k]? = some n → ∀ p ∈ (S n.pkg).imports,
    SrcRes S { st with nodes := st.nodes.take k } (n.src p.1)
  exps : ∀ p ∈ st.exports, SrcRes S st p.2

theorem mem_names_of_lookup {α : Type} {l : List (String × α)} {n : String} {a : α}
    (h : l.lookup n = some a) : n ∈ l.map Prod.fst := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨m, b⟩ := p
    by_cases hm : n = m
    · simp [hm]
    · have h' : l.lookup n = some a := by simpa [List.lookup, beq_false_of_ne hm] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem mem_of_lookup' {α : Type} {l : List (String × α)} {n : String} {a : α}
    (h : l.lookup n = some a) : (n, a) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨m, b⟩ := p
    by_cases hm : n = m
    · have hb : b = a := by simpa [hm] using h
      simp [hm, hb]
    · have h' : l.lookup n = some a := by simpa [List.lookup, beq_false_of_ne hm] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem getElem?_append_cases {α : Type} {xs ys : List α} {j : Nat} {a : α}
    (h : (xs ++ ys)[j]? = some a) : xs[j]? = some a ∨ (xs.length ≤ j ∧ a ∈ ys) := by
  rcases Nat.lt_or_ge j xs.length with hj | hj
  · left
    rwa [List.getElem?_append_left hj] at h
  · right
    rw [List.getElem?_append_right hj] at h
    exact ⟨hj, List.mem_of_getElem? h⟩

theorem Ext.trans_eq {st st' : TSt} (he : Ext st st') {st'' : TSt} (hi : st''.imports = st'.imports)
    (hn : st''.nodes = st'.nodes) : Ext st st'' := by
  obtain ⟨⟨I, hI⟩, ⟨N, hN⟩⟩ := he
  exact ⟨⟨I, hi.trans hI⟩, ⟨N, hn.trans hN⟩⟩

/-- How one item changes the state, as far as resolution is concerned. -/
structure RStep (S : Nat → PkgSig) (st st₁ : TSt) : Prop where
  ext : Ext st st₁
  insts : ∃ I, st₁.insts = st.insts ++ I ∧ ∀ e ∈ I, ∀ f ∈ names e.2, SrcRes S st₁ (e.1.func f)
  funcs : ∃ F, st₁.funcs = st.funcs ++ F ∧ ∀ e ∈ F, SrcRes S st₁ e.1
  nodes : st₁.nodes = st.nodes ∨
    ∃ n, st₁.nodes = st.nodes ++ [n] ∧ st₁.imports = st.imports ∧
      ∀ p ∈ (S n.pkg).imports, SrcRes S st (n.src p.1)
  exps : ∃ X, st₁.exports = st.exports ++ X ∧ ∀ p ∈ X, SrcRes S st₁ p.2

theorem RStep.same (st : TSt) : RStep S st st :=
  ⟨Ext.refl st, ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩, .inl rfl, ⟨[], by simp, by simp⟩⟩

theorem rinv_insts {st st₁ : TSt} (h : RInv S st) (r : RStep S st st₁) :
    ∀ (j : Nat) (loc : Loc) (tab : Table), st₁.insts[j]? = some (loc, tab) →
      ∀ f ∈ names tab, SrcRes S st₁ (loc.func f) := by
  obtain ⟨I, hI, hnew⟩ := r.insts
  intro j loc tab hj f hf
  rw [hI] at hj
  rcases getElem?_append_cases hj with hold | ⟨_, hm⟩
  · exact SrcRes.mono r.ext (h.insts j loc tab hold f hf)
  · exact hnew (loc, tab) hm f hf

theorem rinv_funcs {st st₁ : TSt} (h : RInv S st) (r : RStep S st st₁) :
    ∀ (j : Nat) (src : Src) (ft : FuncTy), st₁.funcs[j]? = some (src, ft) → SrcRes S st₁ src := by
  obtain ⟨F, hF, hnew⟩ := r.funcs
  intro j src ft hj
  rw [hF] at hj
  rcases getElem?_append_cases hj with hold | ⟨_, hm⟩
  · exact SrcRes.mono r.ext (h.funcs j src ft hold)
  · exact hnew (src, ft) hm

theorem rinv_exps {st st₁ : TSt} (h : RInv S st) (r : RStep S st st₁) :
    ∀ p ∈ st₁.exports, SrcRes S st₁ p.2 := by
  obtain ⟨X, hX, hnew⟩ := r.exps
  intro p hp
  rw [hX] at hp
  rcases List.mem_append.1 hp with hold | hm
  · exact SrcRes.mono r.ext (h.exps p hold)
  · exact hnew p hm

theorem take_append_of_lt {α : Type} {xs ys : List α} {k : Nat} (hk : k < xs.length) :
    (xs ++ ys).take k = xs.take k := by
  rw [List.take_append_of_le_length (by omega)]

theorem rinv_old_node {st st₁ : TSt} (h : RInv S st) (r : RStep S st st₁) {k : Nat} {n : Inst}
    (hold : st.nodes[k]? = some n) (N : List Inst) (hN : st₁.nodes = st.nodes ++ N) :
    ∀ p ∈ (S n.pkg).imports, SrcRes S { st₁ with nodes := st₁.nodes.take k } (n.src p.1) := by
  have hk : k < st.nodes.length := (List.getElem?_eq_some_iff.1 hold).1
  have he : Ext { st with nodes := st.nodes.take k } { st₁ with nodes := st₁.nodes.take k } :=
    ⟨r.ext.1, ⟨[], by simp [hN, take_append_of_lt hk]⟩⟩
  exact fun p hp => SrcRes.mono he (h.nodes k n hold p hp)

theorem rinv_nodes {st st₁ : TSt} (h : RInv S st) (r : RStep S st st₁) :
    ∀ (k : Nat) (n : Inst), st₁.nodes[k]? = some n → ∀ p ∈ (S n.pkg).imports,
      SrcRes S { st₁ with nodes := st₁.nodes.take k } (n.src p.1) := by
  intro k n hk
  rcases r.nodes with hs | ⟨n₀, hN, hI, hres⟩
  · rw [hs] at hk
    exact rinv_old_node h r hk [] (by simp [hs])
  · rw [hN] at hk
    rcases getElem?_append_cases hk with hold | ⟨hle, hm⟩
    · exact rinv_old_node h r hold [n₀] hN
    · have hn : n = n₀ := by simpa using hm
      have hkl : k = st.nodes.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1
        simp at this
        omega
      have he : Ext st { st₁ with nodes := st₁.nodes.take k } :=
        ⟨⟨[], by simp [hI]⟩, ⟨[], by simp [hN, hkl]⟩⟩
      exact fun p hp => SrcRes.mono he (hn ▸ hres p (hn ▸ hp))

theorem RInv.step {st st₁ : TSt} (h : RInv S st) (r : RStep S st st₁) : RInv S st₁ :=
  ⟨rinv_insts h r, rinv_funcs h r, rinv_nodes h r, rinv_exps h r⟩

/-! ## Each item -/

theorem SrcRes.congr {st st' : TSt} (hi : st'.imports = st.imports) (hn : st'.nodes = st.nodes)
    {s : Src} (h : SrcRes S st s) : SrcRes S st' s :=
  SrcRes.mono ((Ext.refl st).trans_eq hi hn) h

theorem argT_res {st : TSt} (h : RInv S st) {c : Nat} {a : String × SortIdx}
    {as : List (String × Src)} (ha : argT S st c a = .ok as) : ∀ q ∈ as, SrcRes S st q.2 := by
  obtain ⟨n, ⟨srt, j⟩⟩ := a
  cases srt with
  | func => exact argT_func_res h ha
  | «instance» => exact argT_inst_res h ha
  | type | component =>
    obtain rfl := (Except.ok.inj ha).symm
    simp
  | value | core _ => simp [argT] at ha
where
  argT_func_res {st : TSt} (h : RInv S st) {c : Nat} {n : String} {j : Nat}
      {as : List (String × Src)} (ha : argT S st c (n, ⟨.func, j⟩) = .ok as) :
      ∀ q ∈ as, SrcRes S st q.2 := by
    simp only [argT] at ha
    split at ha
    · rename_i src ft hj
      split at ha
      · obtain rfl := (Except.ok.inj ha).symm
        simpa using h.funcs j src ft hj
      · simp at ha
    · simp at ha
  argT_inst_res {st : TSt} (h : RInv S st) {c : Nat} {n : String} {j : Nat}
      {as : List (String × Src)} (ha : argT S st c (n, ⟨.instance, j⟩) = .ok as) :
      ∀ q ∈ as, SrcRes S st q.2 := by
    simp only [argT] at ha
    split at ha
    · rename_i loc tab hj
      split at ha
      · rename_i hall
        obtain rfl := (Except.ok.inj ha).symm
        intro q hq
        obtain ⟨⟨q', f, ty⟩, hm, rfl⟩ := List.mem_map.1 hq
        have hl : decide (tab.lookup f = some ty) = true := List.all_eq_true.1 hall _ hm
        exact h.insts j loc tab hj f (mem_names_of_lookup (of_decide_eq_true hl))
      · simp at ha
    · simp at ha

theorem argsT_res {st : TSt} (h : RInv S st) {c : Nat} :
    ∀ {args : List (String × SortIdx)} {as : List (String × Src)},
      argsT S st c args = .ok as → ∀ q ∈ as, SrcRes S st q.2
  | [], as, ha => by
    obtain rfl := (Except.ok.inj ha).symm
    simp
  | a :: args, as, ha => by
    cases h1 : argT S st c a with
    | error e => simp [argsT, h1, Except.bind] at ha
    | ok x =>
      cases h2 : argsT S st c args with
      | error e => simp [argsT, h1, h2, Except.bind, Except.map] at ha
      | ok xs =>
        have e : as = x ++ xs := by simpa [argsT, h1, h2, Except.bind, Except.map] using ha.symm
        intro q hq
        rw [e] at hq
        rcases List.mem_append.1 hq with hx | hx
        · exact argT_res h h1 q hx
        · exact argsT_res h h2 q hx

/-- With every import given, the source of each import is one of the arguments. -/
theorem src_mem_of_explicit {s : PkgSig} {n : Inst} (hex : explicitArgs s n.args = true)
    {p : String × FuncTy} (hp : p ∈ s.imports) : ∃ q ∈ n.args, n.src p.1 = q.2 := by
  have hs : (n.args.lookup p.1).isSome = true := List.all_eq_true.1 hex p hp
  obtain ⟨src, hsrc⟩ := Option.isSome_iff_exists.1 hs
  have hm : (p.1, src) ∈ n.args := Silmaril.Wasm.Wac.LowerT.mem_of_lookup' hsrc
  exact ⟨(p.1, src), hm, by simp [Inst.src, hsrc]⟩

theorem importT_res {st st₁ : TSt} {i : Silmaril.Wasm.Component.Binary.Import} (hs : importT st i = .ok st₁) : RStep S st st₁ := by
  cases hd : i.desc with
  | func t =>
    simp only [importT, hd] at hs
    split at hs
    · rename_i ft _
      obtain rfl := (Except.ok.inj hs).symm
      refine ⟨⟨⟨[_], rfl⟩, ⟨[], by simp⟩⟩, ⟨[], by simp, by simp⟩, ⟨[_], rfl, ?_⟩, .inl rfl,
        ⟨[], by simp, by simp⟩⟩
      simp [SrcRes, names]
    · simp at hs
  | «instance» t => exact importT_inst_res hd hs
  | component t | type t =>
    obtain rfl := (Except.ok.inj (by simpa only [importT, hd] using hs)).symm
    exact RStep.same _
  | coreModule t | value t => simp [importT, hd] at hs
where
  importT_inst_res {st st₁ : TSt} {i : Silmaril.Wasm.Component.Binary.Import} {t : Nat} (hd : i.desc = .instance t)
      (hs : importT st i = .ok st₁) : RStep S st st₁ := by
    simp only [importT, hd] at hs
    split at hs
    · split at hs
      · rename_i tab _
        obtain rfl := (Except.ok.inj hs).symm
        refine ⟨⟨⟨_, rfl⟩, ⟨[], by simp⟩⟩, ⟨[_], rfl, ?_⟩, ⟨[], by simp, by simp⟩, .inl rfl,
          ⟨[], by simp, by simp⟩⟩
        intro e he f hf
        have he' : e = (.imp i.name.name, tab) := by simpa using he
        subst he'
        obtain ⟨⟨f', ty⟩, hm, rfl⟩ := List.mem_map.1 hf
        show qual i.name.name f' ∈ names (st.imports ++ tab.map fun p => (qual i.name.name p.1, p.2))
        simp only [names, List.map_append, List.map_map]
        exact List.mem_append_right _ (List.mem_map.2 ⟨(f', ty), hm, rfl⟩)
      · simp at hs
    · simp at hs

theorem instT_res {st st₁ : TSt} (h : RInv S st) {e : InstanceExpr} (hs : instT S st e = .ok st₁) :
    RStep S st st₁ := by
  cases e with
  | exports _ => simp [instT] at hs
  | instantiate c args =>
    obtain ⟨as, _, has, hex, rfl⟩ := instT_instantiate hs
    have hargs : ∀ q ∈ as, SrcRes S st q.2 := argsT_res h has
    have hnode : ∀ p ∈ (S c).imports, SrcRes S st ((⟨c, as⟩ : Inst).src p.1) := by
      intro p hp
      obtain ⟨q, hq, he⟩ := src_mem_of_explicit (n := ⟨c, as⟩) hex hp
      exact he ▸ hargs q hq
    refine ⟨⟨⟨[], by simp⟩, ⟨[_], rfl⟩⟩, ⟨[_], rfl, ?_⟩, ⟨[], by simp, by simp⟩,
      .inr ⟨_, rfl, rfl, hnode⟩, ⟨[], by simp, by simp⟩⟩
    intro e he f hf
    have he' : e = (.node st.nodes.length none, (S c).exports) := by simpa using he
    subst he'
    exact ⟨⟨c, as⟩, by simp, hf⟩

theorem aliasT_res {st st₁ : TSt} (h : RInv S st) {a : Alias} (hs : aliasT st a = .ok st₁) :
    RStep S st st₁ := by
  obtain ⟨srt, tgt⟩ := a
  cases tgt with
  | coreExport _ _ | outer _ _ => simp [aliasT] at hs
  | «export» i n =>
    cases hi : st.insts[i]? with
    | none => simp [aliasT, hi] at hs
    | some p =>
      obtain ⟨loc, tab⟩ := p
      have hres : ∀ f ∈ names tab, SrcRes S st (loc.func f) := h.insts i loc tab hi
      cases srt with
      | func => exact aliasT_func_res hi hres hs
      | «instance» => exact aliasT_inst_res hi hres hs
      | type | component =>
        obtain rfl := (Except.ok.inj (by simpa only [aliasT, hi] using hs)).symm
        exact RStep.same _
      | value | core _ => simp [aliasT, hi] at hs
where
  aliasT_inst_res {st st₁ : TSt} {i : Nat} {n : String} {loc : Loc} {tab : Table}
      (hi : st.insts[i]? = some (loc, tab)) (hres : ∀ f ∈ names tab, SrcRes S st (loc.func f))
      (hs : aliasT st ⟨.instance, .«export» i n⟩ = .ok st₁) : RStep S st st₁ := by
    obtain rfl := (Except.ok.inj (by simpa only [aliasT, hi] using hs)).symm
    refine ⟨Ext.refl st, ⟨[_], rfl, ?_⟩, ⟨[], by simp, by simp⟩, .inl rfl, ⟨[], by simp, by simp⟩⟩
    intro e he f hf
    have he' : e = (loc.inst n, subTable n tab) := by simpa using he
    subst he'
    exact (func_inst loc n f) ▸ hres _ (mem_names_subTable hf)
  aliasT_func_res {st st₁ : TSt} {i : Nat} {n : String} {loc : Loc} {tab : Table}
      (hi : st.insts[i]? = some (loc, tab)) (hres : ∀ f ∈ names tab, SrcRes S st (loc.func f))
      (hs : aliasT st ⟨.func, .«export» i n⟩ = .ok st₁) : RStep S st st₁ := by
    simp only [aliasT, hi] at hs
    split at hs
    · rename_i ft hft
      obtain rfl := (Except.ok.inj hs).symm
      refine ⟨Ext.refl st, ⟨[], by simp, by simp⟩, ⟨[_], rfl, ?_⟩, .inl rfl, ⟨[], by simp, by simp⟩⟩
      intro e he
      have he' : e = (loc.func n, ft) := by simpa using he
      subst he'
      exact hres n (mem_names_of_lookup hft)
    · simp at hs

theorem exportT_res {st st₁ : TSt} (h : RInv S st) {e : Binary.Export} (hs : exportT st e = .ok st₁) :
    RStep S st st₁ := by
  obtain ⟨nm, ⟨srt, j⟩, d⟩ := e
  cases srt with
  | func =>
    simp only [exportT] at hs
    split at hs
    · rename_i src ft hj
      obtain rfl := (Except.ok.inj hs).symm
      have hr : SrcRes S st src := h.funcs j src ft hj
      have hr' := SrcRes.congr (st' := { st with
        funcs := st.funcs ++ [(src, ft)], exports := st.exports ++ [(nm.name, src)] }) rfl rfl hr
      exact ⟨Ext.refl _, ⟨[], by simp, by simp⟩, ⟨[_], rfl, by simpa using hr'⟩, .inl rfl,
        ⟨[_], rfl, by simpa using hr'⟩⟩
    · simp at hs
  | «instance» => exact exportT_inst_res h hs
  | type | component =>
    obtain rfl := (Except.ok.inj hs).symm
    exact RStep.same _
  | value | core _ => simp [exportT] at hs
where
  exportT_inst_res {st st₁ : TSt} (h : RInv S st) {nm : ExternName} {j : Nat} {d : Option ExternDesc}
      (hs : exportT st ⟨nm, ⟨.instance, j⟩, d⟩ = .ok st₁) : RStep S st st₁ := by
    simp only [exportT] at hs
    split at hs
    · rename_i loc tab hj
      obtain rfl := (Except.ok.inj hs).symm
      have hr : ∀ f ∈ names tab, SrcRes S st (loc.func f) := h.insts j loc tab hj
      refine ⟨Ext.refl _, ⟨[_], rfl, ?_⟩, ⟨[], by simp, by simp⟩, .inl rfl, ⟨_, rfl, ?_⟩⟩
      · intro e he
        have he' : e = (loc, tab) := by simpa using he
        subst he'
        exact fun f hf => SrcRes.congr rfl rfl (hr f hf)
      · intro p hp
        obtain ⟨⟨f, ty⟩, hm, rfl⟩ := List.mem_map.1 hp
        exact SrcRes.congr rfl rfl (hr f (List.mem_map.2 ⟨(f, ty), hm, rfl⟩))
    · simp at hs

theorem stepO_res {st st₁ : TSt} (h : RInv S st) {x : Item} (hs : stepO S st x = .ok st₁) :
    RStep S st st₁ := by
  cases x with
  | type _ | comp =>
    obtain rfl := (Except.ok.inj hs).symm
    exact RStep.same _
  | imp i => exact importT_res hs
  | inst e => exact instT_res h hs
  | «alias» a => exact aliasT_res h hs
  | exp e => exact exportT_res h hs

/-- Changing the type space and the component count does not matter for resolution. -/
theorem RStep.retype {st st₁ : TSt} (r : RStep S st st₁) (ts : List TypeEntry) (k : Nat) :
    RStep S st { st₁ with types := ts, comps := k } :=
  ⟨r.ext.trans_eq rfl rfl,
    r.insts.imp fun _ h => ⟨h.1, fun e he f hf => SrcRes.congr rfl rfl (h.2 e he f hf)⟩,
    r.funcs.imp fun _ h => ⟨h.1, fun e he => SrcRes.congr rfl rfl (h.2 e he)⟩,
    r.nodes,
    r.exps.imp fun _ h => ⟨h.1, fun p hp => SrcRes.congr rfl rfl (h.2 p hp)⟩⟩

theorem stepT_res {st st' : TSt} (h : RInv S st) {x : Item} (hs : stepT S st x = .ok st') :
    RInv S st' := by
  cases h1 : stepO S st x with
  | error e => simp [stepT, h1, Except.map] at hs
  | ok st₁ =>
    have e : st' = { st₁ with
        types := tyStep st.types x
        comps := st.comps + (if x.sp == some .comp then 1 else 0) } := by
      simpa [stepT, h1, Except.map] using hs.symm
    rw [e]
    exact h.step ((stepO_res h h1).retype _ _)

theorem runT_res {st : TSt} (h : RInv S st) :
    ∀ {xs : List Item} {st' : TSt}, runT S st xs = .ok st' → RInv S st'
  | [], st', hs => by
    obtain rfl := (Except.ok.inj hs).symm
    exact h
  | x :: xs, st', hs => by
    cases h1 : stepT S st x with
    | error e => simp [runT, h1, Except.bind] at hs
    | ok st₁ =>
      have h2 : runT S st₁ xs = .ok st' := by simpa [runT, h1, Except.bind] using hs
      exact runT_res (stepT_res h h1) h2

theorem rinv_empty : RInv S {} := ⟨by simp, by simp, by simp, by simp⟩

/-! ## Well-formedness and the imports of the composition -/

theorem graph_state {c : Ast} {g : Graph} (hg : graph S c = .ok g) :
    ∃ st, RInv S st ∧ g = ⟨st.imports, st.nodes, st.exports⟩ := by
  unfold graph at hg
  split at hg
  · split at hg
    · rename_i l _
      cases hr : runT S {} l with
      | error e => simp [hr, Except.map] at hg
      | ok st =>
        have e : g = ⟨st.imports, st.nodes, st.exports⟩ := by simpa [hr, Except.map] using hg.symm
        exact ⟨st, runT_res rinv_empty hr, e⟩
    · simp at hg
  · simp at hg

theorem resolves_of_res {st : TSt} {k : Nat} {s : Src}
    (h : SrcRes S { st with nodes := st.nodes.take k } s) :
    Graph.Resolves S ⟨st.imports, st.nodes, st.exports⟩
      (Graph.iface S ⟨st.imports, st.nodes, st.exports⟩) k s := by
  cases s with
  | imp x => exact mem_iface_of_declared S _ h
  | out k' q =>
    obtain ⟨n, hn, hq⟩ := h
    have hk : k' < (st.nodes.take k).length := (List.getElem?_eq_some_iff.1 hn).1
    have hn' : st.nodes[k']? = some n := by
      rw [List.getElem?_take] at hn
      simpa [show k' < k by simp at hk; omega] using hn
    exact ⟨n, hn', by simp at hk; omega, hq⟩

/-- **The typed lowering gives well-formed graphs.** -/
theorem graph_wf {c : Ast} {g : Graph} (hg : graph S c = .ok g) : g.WF S := by
  obtain ⟨st, h, rfl⟩ := graph_state hg
  refine ⟨fun k n hk p hp => resolves_of_res (h.nodes k n hk p hp), fun p hp => ?_⟩
  have hr : SrcRes S st p.2 := h.exps p hp
  refine resolves_of_res (k := st.nodes.length) ?_
  simpa using hr

theorem lookup_of_mem_dedup : ∀ {L : Iface} {p : String × FuncTy}, p ∈ dedup L → L.lookup p.1 = some p.2
  | [], _, h => by simp [dedup] at h
  | q :: L, p, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · simp [List.lookup]
    · obtain ⟨hm, hne⟩ := List.mem_filter.1 h'
      have hne' : p.1 ≠ q.1 := by simpa using hne
      simpa [List.lookup, beq_false_of_ne hne'] using lookup_of_mem_dedup hm

theorem lookup_append_left {l m : Iface} {x : String} (hx : x ∈ names l) :
    (l ++ m).lookup x = l.lookup x := by
  induction l with
  | nil => simp at hx
  | cons q l ih =>
    by_cases hq : x = q.1
    · simp [List.lookup, hq]
    · have hx' : x ∈ names l := by simpa [names, hq] using hx
      simp [List.lookup, beq_false_of_ne hq, ih hx']

/-- Every import an instance or an export uses is declared. -/
theorem used_declared {st : TSt} (h : RInv S st) :
    ∀ x ∈ names ((Graph.mk st.imports st.nodes st.exports).nodes.flatMap (Inst.uses S) ++
      (Graph.mk st.imports st.nodes st.exports).exportUses), x ∈ names st.imports := by
  intro x hx
  simp only [names, List.map_append, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨⟨y, ty⟩, hy, rfl⟩ | ⟨⟨y, ty⟩, hy, rfl⟩
  · obtain ⟨n, hn, hu⟩ := List.mem_flatMap.1 hy
    obtain ⟨p, hp, hpx⟩ := List.mem_filterMap.1 hu
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hn
    have hr := h.nodes k n hk p hp
    revert hpx hr
    cases n.src p.1 with
    | imp z => intro hpx hr; simp at hpx; exact hpx.1 ▸ hr
    | out _ _ => intro hpx; simp at hpx
  · obtain ⟨q, hq, hqx⟩ := List.mem_filterMap.1 hy
    have hr := h.exps q hq
    revert hqx hr
    cases q.2 with
    | imp z => intro hqx hr; simp at hqx; exact hqx.1 ▸ hr
    | out _ _ => intro hqx; simp at hqx

/-- **The imports of the composition are the declared, typed imports**: no import of
`Graph.iface` (and so of `Graph.toComp`) carries the placeholder type of an undeclared
import. -/
theorem graph_iface {c : Ast} {g : Graph} (hg : graph S c = .ok g) :
    ∀ p ∈ g.iface S, p ∈ g.imports := by
  obtain ⟨st, h, rfl⟩ := graph_state hg
  intro p hp
  have hl : (st.imports ++ ((Graph.mk st.imports st.nodes st.exports).nodes.flatMap (Inst.uses S) ++
      (Graph.mk st.imports st.nodes st.exports).exportUses)).lookup p.1 = some p.2 := by
    simpa [Graph.iface, List.append_assoc] using lookup_of_mem_dedup hp
  have hn : p.1 ∈ names st.imports := by
    have hm : p.1 ∈ names (Graph.iface S ⟨st.imports, st.nodes, st.exports⟩) :=
      List.mem_map.2 ⟨p, hp, rfl⟩
    rw [Graph.iface, mem_dedup] at hm
    simp only [names, List.map_append, List.mem_append] at hm
    rcases hm with (h1 | h1) | h1
    · exact h1
    · exact used_declared h _ (by simp only [names, List.map_append, List.mem_append]; exact .inl h1)
    · exact used_declared h _ (by simp only [names, List.map_append, List.mem_append]; exact .inr h1)
  rw [lookup_append_left hn] at hl
  exact mem_of_lookup' hl

end Silmaril.Wasm.Wac.LowerT
