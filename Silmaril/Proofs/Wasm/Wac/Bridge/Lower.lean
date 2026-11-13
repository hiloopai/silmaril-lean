module

public import Silmaril.Proofs.Wasm.Wac.Bridge.Scope
public import Silmaril.Wasm.Wac.Bridge.Text.Thms
public import Silmaril.Wasm.Wac.Bridge.Encode.Thms

/-!
# WAC bridge: lowering the encoding of a graph is its direct translation

A lock-step simulation (`Sim`) of three computations on an elaborated graph: the encoder
(`encode`, state `ESt`), the direct translation (`toGraph`, state `DS`) and `Lower.graph`
on the items the encoder has emitted so far (state `Lower.St`). It relates the index
spaces: the type count, the component count and package indices, and, for every node,
its item (sort and index) in the encoding, its meaning in the direct translation and
the lowering's function or instance at that index (`VRel`); the imports, graph nodes
and exports of the lowering and of the direct translation are equal.

Each kind of step keeps it: imports (`sim_import`, using `externDesc_inst` for the
function exports of an imported instance's type), packages (`sim_package`),
definitions (`sim_defn`), instantiations (`sim_inst`: the arguments, deduplicated by
name on both sides, `argRel_first`, lower to the direct translation's arguments,
`mapM_withArg`), aliases (`sim_alias`) and exports (`sim_export`). `lower_encode`
chains them.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Lower (Loc qual suffix?)

/-- Lowering a list of items. -/
def lowerItems (S : Nat → PkgSig) (its : List Item) (L : Lower.St) : Except String Lower.St :=
  (((its.map Item.toSection).forM (Lower.section_ S)).run L).map (·.2)

theorem lowerItems_nil (S : Nat → PkgSig) (L : Lower.St) : lowerItems S [] L = .ok L := rfl

theorem forM_app {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (f : α → m PUnit) :
    ∀ a b : List α, List.forM (a ++ b) f = (do List.forM a f; List.forM b f)
  | [], b => by
    show List.forM b f = (pure PUnit.unit >>= fun _ => List.forM b f)
    rw [pure_bind]
  | x :: a, b => by
    show (f x >>= fun _ => List.forM (a ++ b) f) = ((f x >>= fun _ => List.forM a f) >>= fun _ => List.forM b f)
    rw [forM_app f a b, bind_assoc]

theorem lowerItems_append (S : Nat → PkgSig) (a b : List Item) (L : Lower.St) :
    lowerItems S (a ++ b) L = (lowerItems S a L).bind (lowerItems S b) := by
  unfold lowerItems
  rw [List.map_append, forM_app, StateT.run_bind]
  cases ((a.map Item.toSection).forM (Lower.section_ S)).run L with
  | error e => rfl
  | ok p => rfl

theorem lowerItems_type (S : Nat → PkgSig) (d : DefType) (L : Lower.St) :
    lowerItems S [.type d] L = .ok { L with types := L.types ++ #[some d] } := rfl

theorem lowerItems_func (S : Nat → PkgSig) (n : String) (t : Nat) (L : Lower.St) :
    lowerItems S [.imp n (.func t)] L =
      .ok { L with funcs := L.funcs.push (.imp n), imports := L.imports.push (n, anyTy) } := rfl

theorem lowerItems_instImp (S : Nat → PkgSig) (n : String) (t : Nat) (L : Lower.St) :
    lowerItems S [.imp n (.instance t)] L =
      .ok { L with insts := L.insts.push (.imp n),
                   imports := L.imports ++ ((Lower.instTypeFuncs L.types t).map fun f => (qual n f, anyTy)).toArray } := rfl

theorem lowerItems_types (S : Nat → PkgSig) : ∀ (ts : List DefType) (L : Lower.St),
    ∃ tys, lowerItems S (ts.map Item.type) L = .ok { L with types := tys } ∧ tys.size = L.types.size + ts.length
  | [], L => ⟨L.types, rfl, rfl⟩
  | t :: ts, L => by
    obtain ⟨tys, h, hs⟩ := lowerItems_types S ts { L with types := L.types ++ #[some t] }
    refine ⟨tys, ?_, ?_⟩
    · rw [List.map_cons, show Item.type t :: ts.map Item.type = [Item.type t] ++ ts.map Item.type from rfl,
        lowerItems_append, lowerItems_type]
      exact h
    · rw [hs, Array.size_append, List.length_cons]; simp only [List.size_toArray, List.length_cons,
        List.length_nil]; omega

/-! ## The simulation -/

/-- The item of a node and its meaning, in a lowering state. -/
def VRel (L : Lower.St) : Option SortIdx → Option V → Prop
  | none, none => True
  | some x, some v =>
    match x.sort, v with
    | .func, .src s => L.funcs[x.idx]? = some s
    | .instance, .loc l => L.insts[x.idx]? = some l
    | .type, .type => True
    | .component, .comp => True
    | _, _ => False
  | _, _ => False

/-- The lowering state `L` extends `L₀` in the function and instance index spaces. -/
def Ext (L₀ L : Lower.St) : Prop :=
  (∀ (x : Nat) (s : Src), L₀.funcs[x]? = some s → L.funcs[x]? = some s) ∧
    (∀ (x : Nat) (l : Loc), L₀.insts[x]? = some l → L.insts[x]? = some l)

theorem Ext.refl (L : Lower.St) : Ext L L := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem VRel.mono {L₀ L : Lower.St} (he : Ext L₀ L) :
    ∀ {a : Option SortIdx} {b : Option V}, VRel L₀ a b → VRel L a b
  | none, none, _ => trivial
  | some ⟨.func, x⟩, some (.src s), h => he.1 x s h
  | some ⟨.instance, x⟩, some (.loc l), h => he.2 x l h
  | some ⟨.type, _⟩, some .type, _ | some ⟨.component, _⟩, some .comp, _ => trivial
  | none, some _, h | some _, none, h => h.elim
  | some ⟨.func, _⟩, some (.loc _), h | some ⟨.func, _⟩, some .comp, h
  | some ⟨.func, _⟩, some .type, h | some ⟨.func, _⟩, some .none, h => h.elim
  | some ⟨.instance, _⟩, some (.src _), h | some ⟨.instance, _⟩, some .comp, h
  | some ⟨.instance, _⟩, some .type, h | some ⟨.instance, _⟩, some .none, h => h.elim
  | some ⟨.type, _⟩, some (.src _), h | some ⟨.type, _⟩, some (.loc _), h
  | some ⟨.type, _⟩, some .comp, h | some ⟨.type, _⟩, some .none, h => h.elim
  | some ⟨.component, _⟩, some (.src _), h | some ⟨.component, _⟩, some (.loc _), h
  | some ⟨.component, _⟩, some .type, h | some ⟨.component, _⟩, some .none, h => h.elim
  | some ⟨.value, _⟩, some _, h | some ⟨.core _, _⟩, some _, h => h.elim

theorem lookup_snoc {κ β : Type} [DecidableEq κ] (l : List (κ × β)) (i j : κ) (x : β) :
    (l ++ [(i, x)]).lookup j = match l.lookup j with
      | some y => some y
      | none => if j = i then some x else none := by
  induction l with
  | nil =>
    by_cases h : j = i
    · simp [List.lookup, h]
    · have hb : (j == i) = false := by simp [h]
      simp only [List.nil_append, List.lookup, hb, h, ite_false]
  | cons p l ih =>
    by_cases h : j = p.1
    · simp [List.lookup, h]
    · have hb : (j == p.1) = false := by simp [h]
      simp only [List.cons_append, List.lookup, hb]
      exact ih

/-- The simulation: the encoder's state, the direct translation's state and the state of
`Lower.graph` on the items emitted so far. -/
structure Sim (es : ESt) (ds : DS) (L : Lower.St) : Prop where
  types : L.types.size = es.sc.ntypes
  comps : L.comps = es.comps
  dcomps : ds.comps = es.comps
  pkgs : ds.pkgs = es.pkgs
  pkgs_lt : ∀ k c, es.pkgs.lookup k = some c → c < es.comps
  funcs : L.funcs.size = es.funcs
  insts : L.insts.size = es.insts
  vals : ∀ j, VRel L (es.idx.lookup j) (ds.vals.lookup j)
  imports : L.imports = ds.imports
  nodes : L.nodes = ds.nodes
  exports : L.exports = ds.exports
  share : es.sc.share = false

/-- Recording a node in lock step keeps the correspondence of meanings. -/
theorem vals_snoc {es : ESt} {ds : DS} {L L' : Lower.St} {i : Nat} {x : SortIdx} {v : V}
    (hv : ∀ j, VRel L (es.idx.lookup j) (ds.vals.lookup j)) (he : Ext L L') (hn : VRel L' (some x) (some v)) :
    ∀ j, VRel L' ((es.setIdx i x).idx.lookup j) ((ds.setVal i v).vals.lookup j) := by
  intro j
  show VRel L' ((es.idx ++ [(i, x)]).lookup j) ((ds.vals ++ [(i, v)]).lookup j)
  rw [lookup_snoc, lookup_snoc]
  have hj := hv j
  revert hj
  cases es.idx.lookup j <;> cases ds.vals.lookup j <;> intro hj
  · by_cases h : j = i
    · simpa [h] using hn
    · simp [h, VRel]
  · exact hj.elim
  · exact hj.elim
  · exact VRel.mono he hj

theorem runT_ok {α : Type} {m : TM α} {es es₁ : ESt} {a : α} (h : runT m es = .ok (a, es₁)) :
    ∃ sc, m.run { es.sc with decls := [] } = .ok (a, sc) ∧
      es₁ = { es with items := es.items ++ tyItems sc.decls, sc := { sc with decls := [] } } := by
  unfold runT at h
  split at h
  · rename_i a' sc hr
    have e : a = a' ∧ es₁ = { es with items := es.items ++ tyItems sc.decls, sc := { sc with decls := [] } } := by
      cases h; exact ⟨rfl, rfl⟩
    rw [e.1]; exact ⟨sc, hr, e.2⟩
  · cases h

theorem tyItems_types (ts : List DefType) :
    tyItems ([] ++ ts.map fun d => .inst (.type d)) = ts.map Item.type := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact congrArg (Item.type t :: ·) ih

/-- A type computation at the top level emits type items, and keeps the simulation. -/
theorem sim_runT (S : Nat → PkgSig) {α : Type} {m : TM α} {es es₁ : ESt} {ds : DS} {L : Lower.St} {a : α}
    (hm : Pres m) (hS : Sim es ds L) (h : runT m es = .ok (a, es₁)) :
    ∃ (ts : List DefType) (L₁ : Lower.St) (sc : Scope), m.run { es.sc with decls := [] } = .ok (a, sc) ∧
      sc.decls = ts.map (fun d => .inst (.type d)) ∧
      es₁ = { es with items := es.items ++ ts.map Item.type, sc := { sc with decls := [] } } ∧
      lowerItems S (ts.map Item.type) L = .ok L₁ ∧ Sim es₁ ds L₁ ∧ Ext L L₁ := by
  obtain ⟨sc, hr, he⟩ := runT_ok h
  obtain ⟨ts, hd, hn, hsh⟩ := hm _ a sc hr
  have hd' : sc.decls = ts.map (fun d => .inst (.type d)) := by simpa using hd
  obtain ⟨tys, hl, hsz⟩ := lowerItems_types S ts L
  have hit : tyItems sc.decls = ts.map Item.type := by rw [hd]; exact tyItems_types ts
  refine ⟨ts, { L with types := tys }, sc, hr, hd', by rw [he, hit], hl, ?_, Ext.refl L⟩
  rw [he]
  exact { types := by rw [hsz, hS.types, hn]
          comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
          funcs := hS.funcs, insts := hS.insts, vals := hS.vals
          imports := hS.imports, nodes := hS.nodes, exports := hS.exports
          share := by rw [← hS.share]; exact hsh }

theorem getElem?_push_old {β : Type} {xs : Array β} {x : Nat} {b c : β} (h : xs[x]? = some b) :
    (xs.push c)[x]? = some b := by
  have hx : x < xs.size := by
    rcases Nat.lt_or_ge x xs.size with hx | hx
    · exact hx
    · rw [Array.getElem?_eq_none hx] at h; cases h
  rw [Array.getElem?_push]; simp only [Nat.ne_of_lt hx, ite_false]; exact h

theorem Ext.pushFunc (L : Lower.St) (s : Src) : Ext L { L with funcs := L.funcs.push s } :=
  ⟨fun _ _ h => getElem?_push_old h, fun _ _ h => h⟩

theorem Ext.pushInst (L : Lower.St) (l : Loc) : Ext L { L with insts := L.insts.push l } :=
  ⟨fun _ _ h => h, fun _ _ h => getElem?_push_old h⟩

theorem Ext.trans {L₁ L₂ L₃ : Lower.St} (h₁ : Ext L₁ L₂) (h₂ : Ext L₂ L₃) : Ext L₁ L₃ :=
  ⟨fun x s h => h₂.1 x s (h₁.1 x s h), fun x l h => h₂.2 x l (h₁.2 x l h)⟩

theorem Ext.of_eq {L L' : Lower.St} (hf : L'.funcs = L.funcs) (hi : L'.insts = L.insts) : Ext L L' :=
  ⟨fun _ _ h => hf ▸ h, fun _ _ h => hi ▸ h⟩

theorem ebind_ok {ε α β : Type} {e : Except ε α} {f : α → Except ε β} {b : β} (h : e >>= f = .ok b) :
    ∃ a, e = .ok a ∧ f a = .ok b := by
  cases he : e with
  | error x => rw [he] at h; cases h
  | ok a => rw [he] at h; exact ⟨a, rfl, h⟩

/-- The rest of an import, after its type. -/
def impFinish (es : ESt) (i : Nat) (n : String) (d : ExternDesc) : ESt :=
  let st := es.emit (.imp n d)
  let (j, st) := st.alloc (descSort d)
  (st.nameDesc n j d).setIdx i ⟨descSort d, j⟩

theorem impFinish_items (es : ESt) (i : Nat) (n : String) (d : ExternDesc) :
    (impFinish es i n d).items = es.items ++ [.imp n d] := by
  cases d <;> rfl

theorem encImport_eq (i : Nat) (n : String) (k : Kind) (es : ESt) :
    encImport i n k es = (runT (externDesc k) es >>= fun p => .ok (impFinish p.2 i n p.1)) := rfl

theorem sim_imp_func (S : Nat → PkgSig) {es : ESt} {ds : DS} {L : Lower.St} (hS : Sim es ds L)
    (i : Nat) (n : String) (t : Nat) (s : Wit.Binary.Sig) :
    ∃ L', lowerItems S [.imp n (.func t)] L = .ok L' ∧ Ext L L' ∧
      Sim (impFinish es i n (.func t)) (dImport i n (.func s) ds) L' := by
  refine ⟨_, lowerItems_func S n t L, Ext.pushFunc L _, ?_⟩
  have hnew : VRel { L with funcs := L.funcs.push (.imp n), imports := L.imports.push (n, anyTy) }
      (some ⟨.func, es.funcs⟩) (some (.src (.imp n))) := by
    show (L.funcs.push (.imp n))[es.funcs]? = some (.imp n)
    rw [← hS.funcs]; exact Array.getElem?_push_size
  exact { types := hS.types, comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
          funcs := by show (L.funcs.push _).size = es.funcs + 1; rw [Array.size_push, hS.funcs]
          insts := hS.insts
          vals := vals_snoc hS.vals (Ext.pushFunc L _) hnew
          imports := by show L.imports.push _ = ds.imports.push _; rw [hS.imports]
          nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem sim_imp_inst (S : Nat → PkgSig) {es : ESt} {ds : DS} {L : Lower.St} (hS : Sim es ds L)
    (i : Nat) (n : String) (t : Nat) (id : Option String) (xs : Externs)
    (ht : Lower.instTypeFuncs L.types t = funcNames xs) :
    ∃ L', lowerItems S [.imp n (.instance t)] L = .ok L' ∧ Ext L L' ∧
      Sim (impFinish es i n (.instance t)) (dImport i n (.inst id xs) ds) L' := by
  refine ⟨_, lowerItems_instImp S n t L, Ext.pushInst L _, ?_⟩
  have hnew : VRel { L with insts := L.insts.push (.imp n), imports := L.imports ++ ((Lower.instTypeFuncs L.types t).map fun f => (qual n f, anyTy)).toArray } (some ⟨.instance, es.insts⟩) (some (.loc (.imp n))) := by
    show (L.insts.push (.imp n))[es.insts]? = some (.imp n)
    rw [← hS.insts]; exact Array.getElem?_push_size
  exact { types := hS.types, comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
          funcs := hS.funcs
          insts := by show (L.insts.push _).size = es.insts + 1; rw [Array.size_push, hS.insts]
          vals := vals_snoc hS.vals (Ext.pushInst L _) hnew
          imports := by show L.imports ++ _ = ds.imports ++ _; rw [hS.imports, ht]
          nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem sim_imp_comp (S : Nat → PkgSig) {es : ESt} {ds : DS} {L : Lower.St} (hS : Sim es ds L)
    (i : Nat) (n : String) (t : Nat) (id : Option String) (xs ys : Externs) :
    ∃ L', lowerItems S [.imp n (.component t)] L = .ok L' ∧ Ext L L' ∧
      Sim (impFinish es i n (.component t)) (dImport i n (.comp id xs ys) ds) L' := by
  refine ⟨{ L with comps := L.comps + 1 }, rfl, Ext.of_eq rfl rfl, ?_⟩
  exact { types := hS.types
          comps := by show L.comps + 1 = es.comps + 1; rw [hS.comps]
          dcomps := by show ds.comps + 1 = es.comps + 1; rw [hS.dcomps]
          pkgs := hS.pkgs
          pkgs_lt := fun k c hc => Nat.lt_succ_of_lt (hS.pkgs_lt k c hc)
          funcs := hS.funcs, insts := hS.insts
          vals := vals_snoc hS.vals (Ext.of_eq rfl rfl) trivial
          imports := hS.imports, nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem sim_imp_type (S : Nat → PkgSig) {es : ESt} {ds : DS} {L : Lower.St} (hS : Sim es ds L)
    (i : Nat) (n : String) (b : TypeBound) (k : Kind) (hk : kindSort k = .type) :
    ∃ L', lowerItems S [.imp n (.type b)] L = .ok L' ∧ Ext L L' ∧
      Sim (impFinish es i n (.type b)) (dImport i n k ds) L' := by
  refine ⟨{ L with types := L.types.push none }, rfl, Ext.of_eq rfl rfl, ?_⟩
  have hd : dImport i n k ds = ds.setVal i .type := by
    cases k <;> first | rfl | (simp [kindSort] at hk)
  rw [hd]
  exact { types := by show (L.types.push none).size = es.sc.ntypes + 1; rw [Array.size_push, hS.types]
          comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
          funcs := hS.funcs, insts := hS.insts
          vals := vals_snoc hS.vals (Ext.of_eq rfl rfl) trivial
          imports := hS.imports, nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem map_type_single {ts : List DefType} {x : DefType}
    (h : ts.map (fun d => ComponentDecl.inst (.type d)) = [.inst (.type x)]) : ts = [x] := by
  have h' : ts.map (fun d => ComponentDecl.inst (.type d)) = [x].map (fun d => ComponentDecl.inst (.type d)) := h
  exact List.map_injective_iff.mpr (fun a b e => by cases e; rfl) h'

theorem instTypeFuncs_last (tys : Array (Option DefType)) (ids : List InstanceDecl) :
    Lower.instTypeFuncs (tys ++ #[some (.instance ids)]) tys.size = ifuncs ids := by
  unfold Lower.instTypeFuncs
  rw [Array.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem desc_func {d : ExternDesc} (h : descSort d = .func) : ∃ t, d = .func t := by
  cases d <;> first | exact ⟨_, rfl⟩ | exact absurd h (by simp [descSort])

theorem desc_comp {d : ExternDesc} (h : descSort d = .component) : ∃ t, d = .component t := by
  cases d <;> first | exact ⟨_, rfl⟩ | exact absurd h (by simp [descSort])

theorem desc_type {d : ExternDesc} (h : descSort d = .type) : ∃ b, d = .type b := by
  cases d <;> first | exact ⟨_, rfl⟩ | exact absurd h (by simp [descSort])

/-- The type items of an imported instance: one instance type. -/
theorem sim_import_inst (S : Nat → PkgSig) {es es₁ : ESt} {ds : DS} {L L₁ : Lower.St} {i : Nat}
    {n : String} {id : Option String} {xs : Externs} {d : ExternDesc} {ts : List DefType} {sc : Scope}
    (hS : Sim es ds L) (hrun : (externDesc (.inst id xs)).run { es.sc with decls := [] } = .ok (d, sc))
    (hdecls : sc.decls = ts.map fun d => .inst (.type d)) (hl₁ : lowerItems S (ts.map Item.type) L = .ok L₁)
    (hS₁ : Sim es₁ ds L₁) :
    ∃ L', lowerItems S [.imp n d] L₁ = .ok L' ∧ Ext L₁ L' ∧ Sim (impFinish es₁ i n d) (dImport i n (.inst id xs) ds) L' := by
  have hsh : ({ es.sc with decls := [] } : Scope).share = false := hS.share
  obtain ⟨hd, ids, hsd, _, hfn⟩ := externDesc_inst hsh hrun
  have hts : ts = [.instance ids] := map_type_single (by rw [← hdecls, hsd]; rfl)
  have hl₁' : lowerItems S ([DefType.instance ids].map Item.type) L = .ok L₁ := hts ▸ hl₁
  have e₁ : (Except.ok L₁ : Except String Lower.St) = .ok { L with types := L.types ++ #[some (.instance ids)] } :=
    hl₁'.symm.trans (lowerItems_type S _ L)
  have hL₁ : L₁ = { L with types := L.types ++ #[some (.instance ids)] } := Except.ok.inj e₁
  have ht : Lower.instTypeFuncs L₁.types es.sc.ntypes = funcNames xs := by
    rw [hL₁, ← hS.types]; exact (instTypeFuncs_last _ ids).trans hfn
  rw [hd]
  exact sim_imp_inst S hS₁ i n _ id xs ht

/-- The import item, after the type items. -/
theorem sim_import_item (S : Nat → PkgSig) {es es₁ : ESt} {ds : DS} {L L₁ : Lower.St} {i : Nat}
    {n : String} {k : Kind} {d : ExternDesc} {ts : List DefType} {sc : Scope} (hS : Sim es ds L)
    (hv : kindSort k ≠ .value) (hrun : (externDesc k).run { es.sc with decls := [] } = .ok (d, sc))
    (hdecls : sc.decls = ts.map fun d => .inst (.type d)) (hl₁ : lowerItems S (ts.map Item.type) L = .ok L₁)
    (hS₁ : Sim es₁ ds L₁) :
    ∃ L', lowerItems S [.imp n d] L₁ = .ok L' ∧ Ext L₁ L' ∧ Sim (impFinish es₁ i n d) (dImport i n k ds) L' := by
  have hsort : descSort d = kindSort k := Ret.externDesc k _ d sc hrun
  cases k with
  | func s =>
    obtain ⟨t, ht⟩ := desc_func hsort
    rw [ht]; exact sim_imp_func S hS₁ i n t s
  | inst id xs => exact sim_import_inst S hS hrun hdecls hl₁ hS₁
  | comp id xs ys =>
    obtain ⟨t, ht⟩ := desc_comp hsort
    rw [ht]; exact sim_imp_comp S hS₁ i n t id xs ys
  | type k' =>
    obtain ⟨b, hb⟩ := desc_type hsort
    rw [hb]; exact sim_imp_type S hS₁ i n b _ rfl
  | resource r =>
    obtain ⟨b, hb⟩ := desc_type hsort
    rw [hb]; exact sim_imp_type S hS₁ i n b _ rfl
  | value t => exact absurd rfl hv

/-- **An import node** keeps the simulation. -/
theorem sim_import (S : Nat → PkgSig) {es es' : ESt} {ds : DS} {L : Lower.St} {i : Nat} {n : String}
    {k : Kind} (hS : Sim es ds L) (hv : kindSort k ≠ .value) (h : encImport i n k es = .ok es') :
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧ Ext L L' ∧
      Sim es' (dImport i n k ds) L' := by
  have h₀ : (runT (externDesc k) es >>= fun p => .ok (impFinish p.2 i n p.1)) = .ok es' :=
    (encImport_eq i n k es).symm.trans h
  obtain ⟨⟨d, es₁⟩, hr, hf⟩ := ebind_ok h₀
  have he' : es' = impFinish es₁ i n d := by cases hf; rfl
  obtain ⟨ts, L₁, sc, hrun, hdecls, he₁, hl₁, hS₁, hx₁⟩ := sim_runT S (Pres.externDesc k) hS hr
  have hitems : es'.items = es.items ++ (ts.map Item.type ++ [.imp n d]) := by
    rw [he', impFinish_items, he₁]
    exact List.append_assoc _ _ _
  obtain ⟨L', hl, hx, hs⟩ := sim_import_item S hS hv hrun hdecls hl₁ hS₁
  refine ⟨_, L', hitems, by rw [lowerItems_append, hl₁]; exact hl, hx₁.trans hx, ?_⟩
  rw [he']; exact hs

/-- The import nodes. -/
theorem sim_imports (S : Nat → PkgSig) : ∀ (l : List (Nat × String × Kind)) {es es' : ESt} {ds : DS}
    {L : Lower.St}, Sim es ds L → (∀ x ∈ l, kindSort x.2.2 ≠ .value) → encImports l es = .ok es' →
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧ Sim es' (dImports l ds) L'
  | [], es, es', ds, L, hS, _, h => by
    have : es' = es := by cases h; rfl
    exact ⟨[], L, by rw [this, List.append_nil], rfl, this ▸ hS⟩
  | (i, n, k) :: l, es, es', ds, L, hS, hv, h => by
    obtain ⟨es₁, h₁, h₂⟩ := ebind_ok h
    obtain ⟨new₁, L₁, hi₁, hl₁, _, hS₁⟩ := sim_import S hS (hv _ List.mem_cons_self) h₁
    obtain ⟨new₂, L₂, hi₂, hl₂, hS₂⟩ :=
      sim_imports S l hS₁ (fun x hx => hv x (List.mem_cons_of_mem _ hx)) h₂
    refine ⟨new₁ ++ new₂, L₂, by rw [hi₂, hi₁, List.append_assoc], ?_, hS₂⟩
    rw [lowerItems_append, hl₁]; exact hl₂

section lowering
variable (S : Nat → PkgSig) {L : Lower.St}

theorem lowerItems_aliasFunc {i : Nat} {l : Loc} (n : String) (hl : L.insts[i]? = some l) :
    lowerItems S [.alias .func i n] L = .ok { L with funcs := L.funcs.push (l.func n) } := by
  simp [lowerItems, Item.toSection, Lower.section_, Lower.alias_, Lower.get?, hl, List.forM]; rfl

theorem lowerItems_aliasInst {i : Nat} {l : Loc} (n : String) (hl : L.insts[i]? = some l) :
    lowerItems S [.alias .instance i n] L = .ok { L with insts := L.insts.push (l.inst n) } := by
  simp [lowerItems, Item.toSection, Lower.section_, Lower.alias_, Lower.get?, hl, List.forM]; rfl

theorem lowerItems_aliasType {i : Nat} {l : Loc} (n : String) (hl : L.insts[i]? = some l) :
    lowerItems S [.alias .type i n] L = .ok { L with types := L.types.push none } := by
  simp [lowerItems, Item.toSection, Lower.section_, Lower.alias_, Lower.get?, hl, List.forM]; rfl

theorem lowerItems_aliasComp {i : Nat} {l : Loc} (n : String) (hl : L.insts[i]? = some l) :
    lowerItems S [.alias .component i n] L = .ok { L with comps := L.comps + 1 } := by
  simp [lowerItems, Item.toSection, Lower.section_, Lower.alias_, Lower.get?, hl, List.forM]; rfl

theorem lowerItems_expFunc {x : Nat} {s : Src} (n : String) (hs : L.funcs[x]? = some s) :
    lowerItems S [.exp n ⟨.func, x⟩] L =
      .ok { L with exports := L.exports.push (n, s), funcs := L.funcs.push s } := by
  simp [lowerItems, Item.toSection, Lower.section_, Lower.export_, Lower.get?, hs, List.forM]; rfl

theorem lowerItems_expInst {x : Nat} {l : Loc} (n : String) (hl : L.insts[x]? = some l) :
    lowerItems S [.exp n ⟨.instance, x⟩] L =
      .ok { L with exports := L.exports ++ ((Lower.locFuncs S L l).map fun f => (qual n f, l.func f)).toArray,
                   insts := L.insts.push l } := by
  simp [lowerItems, Item.toSection, Lower.section_, Lower.export_, Lower.get?, hl, List.forM]; rfl

theorem lowerItems_expType (n : String) (x : Nat) :
    lowerItems S [.exp n ⟨.type, x⟩] L = .ok { L with types := L.types.push none } := by
  simp [lowerItems, Item.toSection, Lower.section_, Lower.export_, List.forM]; rfl

theorem lowerItems_expComp (n : String) (x : Nat) :
    lowerItems S [.exp n ⟨.component, x⟩] L = .ok { L with comps := L.comps + 1 } := by
  simp [lowerItems, Item.toSection, Lower.section_, Lower.export_, List.forM]; rfl

theorem lowerItems_impComp (n : String) (t : Nat) :
    lowerItems S [.imp n (.component t)] L = .ok { L with comps := L.comps + 1 } := rfl

end lowering

theorem itemOf_ok {es : ESt} {j : Nat} {x : SortIdx} (h : es.itemOf j = .ok x) : es.idx.lookup j = some x := by
  unfold ESt.itemOf at h
  split at h
  · rename_i y hy; cases h; exact hy
  · cases h

/-- The meaning of an instance item. -/
theorem vrel_inst {L : Lower.St} {x : Nat} {v : Option V} (h : VRel L (some ⟨.instance, x⟩) v) :
    ∃ l, v = some (.loc l) ∧ L.insts[x]? = some l := by
  match v, h with
  | some (.loc l), h => exact ⟨l, rfl, h⟩

/-- The rest of an alias of the instance item `x`, as sort `s`. -/
def aliasFinish (es : ESt) (i : Nat) (s : ItemSort) (x : Nat) (n : String) : ESt :=
  let st := es.emit (.alias s x n)
  let (j, st) := st.alloc s
  st.setIdx i ⟨s, j⟩

theorem encNode_alias {g : CGraph} {i src : Nat} {n : String} {k : Kind} {es es' : ESt}
    (h : encNode g i ⟨.alias src n, k⟩ es = .ok es') :
    ∃ x, es.idx.lookup src = some ⟨.instance, x⟩ ∧ es' = aliasFinish es i (kindSort k) x n := by
  unfold encNode at h
  obtain ⟨⟨srt, x⟩, hx, h'⟩ := ebind_ok h
  have hl := itemOf_ok hx
  by_cases hs : srt = .instance
  · rw [hs] at h' hl
    refine ⟨x, hl, ?_⟩
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at h'
    cases h'; rfl
  · have hb : (srt != ItemSort.instance) = true := by simpa using hs
    simp only [hb, ite_true] at h'
    cases h'

theorem dNode_alias (S : Nat → PkgSig) (g : CGraph) (i src : Nat) (n : String) (k : Kind) (ds : DS) (l : Loc)
    (hl : ds.vals.lookup src = some (.loc l)) :
    dNode S g i ⟨.alias src n, k⟩ ds =
      if kindSort k = .component then { ds.setVal i (aliasVal l n (kindSort k)) with comps := ds.comps + 1 }
      else ds.setVal i (aliasVal l n (kindSort k)) := by
  simp only [dNode, hl]

section aliasSteps
variable (S : Nat → PkgSig) {es : ESt} {ds : DS} {L : Lower.St} {i x : Nat} {n : String} {l : Loc}

theorem sim_alias_func (hS : Sim es ds L) :
    Sim (aliasFinish es i .func x n) (ds.setVal i (.src (l.func n))) { L with funcs := L.funcs.push (l.func n) } := by
  have hnew : VRel { L with funcs := L.funcs.push (l.func n) } (some ⟨.func, es.funcs⟩) (some (.src (l.func n))) := by
    show (L.funcs.push _)[es.funcs]? = _
    rw [← hS.funcs]; exact Array.getElem?_push_size
  exact { types := hS.types, comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
          funcs := by show (L.funcs.push _).size = es.funcs + 1; rw [Array.size_push, hS.funcs]
          insts := hS.insts
          vals := vals_snoc hS.vals (Ext.pushFunc L _) hnew
          imports := hS.imports, nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem sim_alias_inst (hS : Sim es ds L) :
    Sim (aliasFinish es i .instance x n) (ds.setVal i (.loc (l.inst n))) { L with insts := L.insts.push (l.inst n) } := by
  have hnew : VRel { L with insts := L.insts.push (l.inst n) } (some ⟨.instance, es.insts⟩) (some (.loc (l.inst n))) := by
    show (L.insts.push _)[es.insts]? = _
    rw [← hS.insts]; exact Array.getElem?_push_size
  exact { types := hS.types, comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
          funcs := hS.funcs
          insts := by show (L.insts.push _).size = es.insts + 1; rw [Array.size_push, hS.insts]
          vals := vals_snoc hS.vals (Ext.pushInst L _) hnew
          imports := hS.imports, nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem sim_alias_type (hS : Sim es ds L) :
    Sim (aliasFinish es i .type x n) (ds.setVal i .type) { L with types := L.types.push none } :=
  { types := by show (L.types.push none).size = es.sc.ntypes + 1; rw [Array.size_push, hS.types]
    comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
    funcs := hS.funcs, insts := hS.insts
    vals := vals_snoc hS.vals (Ext.of_eq rfl rfl) trivial
    imports := hS.imports, nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem sim_alias_comp (hS : Sim es ds L) :
    Sim (aliasFinish es i .component x n) { ds.setVal i .comp with comps := ds.comps + 1 }
      { L with comps := L.comps + 1 } :=
  { types := hS.types
    comps := by show L.comps + 1 = es.comps + 1; rw [hS.comps]
    dcomps := by show ds.comps + 1 = es.comps + 1; rw [hS.dcomps]
    pkgs := hS.pkgs
    pkgs_lt := fun k c hc => Nat.lt_succ_of_lt (hS.pkgs_lt k c hc)
    funcs := hS.funcs, insts := hS.insts
    vals := vals_snoc hS.vals (Ext.of_eq rfl rfl) trivial
    imports := hS.imports, nodes := hS.nodes, exports := hS.exports, share := hS.share }

/-- The alias item, by sort. -/
theorem sim_alias_item (hS : Sim es ds L) (hl : L.insts[x]? = some l) {s : ItemSort} (hs : s ≠ .value)
    (hc : ∀ c, s ≠ .core c) :
    ∃ L', lowerItems S [.alias s x n] L = .ok L' ∧
      Sim (aliasFinish es i s x n)
        (if s = .component then { ds.setVal i (aliasVal l n s) with comps := ds.comps + 1 }
         else ds.setVal i (aliasVal l n s)) L' := by
  cases s with
  | func => exact ⟨_, lowerItems_aliasFunc S n hl, sim_alias_func hS⟩
  | «instance» => exact ⟨_, lowerItems_aliasInst S n hl, sim_alias_inst hS⟩
  | type => exact ⟨_, lowerItems_aliasType S n hl, sim_alias_type hS⟩
  | component => exact ⟨_, lowerItems_aliasComp S n hl, sim_alias_comp hS⟩
  | value => exact absurd rfl hs
  | core c => exact absurd rfl (hc c)

end aliasSteps

theorem aliasFinish_items (es : ESt) (i : Nat) (s : ItemSort) (x : Nat) (n : String) :
    (aliasFinish es i s x n).items = es.items ++ [.alias s x n] := by
  cases s <;> rfl

theorem kindSort_ne_core (k : Kind) (c : CoreSort) : kindSort k ≠ .core c := by
  cases k <;> simp [kindSort]

/-- **An alias node** keeps the simulation. -/
theorem sim_alias (S : Nat → PkgSig) {g : CGraph} {es es' : ESt} {ds : DS} {L : Lower.St} {i src : Nat}
    {n : String} {k : Kind} (hS : Sim es ds L) (hv : kindSort k ≠ .value)
    (h : encNode g i ⟨.alias src n, k⟩ es = .ok es') :
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧
      Sim es' (dNode S g i ⟨.alias src n, k⟩ ds) L' := by
  obtain ⟨x, hx, he⟩ := encNode_alias h
  have hr : VRel L (some ⟨.instance, x⟩) (ds.vals.lookup src) := hx ▸ hS.vals src
  obtain ⟨l, hdl, hl⟩ := vrel_inst hr
  obtain ⟨L', hl', hs'⟩ := sim_alias_item S (i := i) (n := n) hS hl hv (kindSort_ne_core k)
  refine ⟨[.alias (kindSort k) x n], L', ?_, hl', ?_⟩
  · rw [he]; exact aliasFinish_items es i (kindSort k) x n
  · rw [he, dNode_alias S g i src n k ds l hdl]; exact hs'

/-- The rest of a definition node, after its type. -/
def defnFinish (es : ESt) (i : Nat) (n e : String) (t : Nat) : ESt :=
  let st := es.emit (.exp e ⟨.type, t⟩)
  let (j, st) := st.alloc .type
  (st.nameTy n j (.eq t)).setIdx i ⟨.type, j⟩

theorem encNode_defn {g : CGraph} {i : Nat} {n : String} {kd : Kind} {es es' : ESt}
    (h : encNode g i ⟨.defn n, kd⟩ es = .ok es') :
    ∃ k t es₁, kd = .type k ∧ runT (defnTy k) es = .ok (.type (.eq t), es₁) ∧
      es' = defnFinish es₁ i n (defnName g i n) t := by
  cases kd with
  | type k =>
    unfold encNode at h
    obtain ⟨⟨d, es₁⟩, hr, h'⟩ := ebind_ok h
    match d, h' with
    | .type (.eq t), h' => exact ⟨k, t, es₁, rfl, hr, by cases h'; rfl⟩
  | _ => unfold encNode at h; cases h

/-- **A definition node** keeps the simulation. -/
theorem sim_defn (S : Nat → PkgSig) {g : CGraph} {es es' : ESt} {ds : DS} {L : Lower.St} {i : Nat}
    {n : String} {kd : Kind} (hS : Sim es ds L) (h : encNode g i ⟨.defn n, kd⟩ es = .ok es') :
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧
      Sim es' (dNode S g i ⟨.defn n, kd⟩ ds) L' := by
  obtain ⟨k, t, es₁, _, hr, he⟩ := encNode_defn h
  obtain ⟨ts, L₁, sc, _, _, he₁, hl₁, hS₁, _⟩ := sim_runT S (Pres.defnTy k) hS hr
  refine ⟨ts.map Item.type ++ [.exp (defnName g i n) ⟨.type, t⟩], { L₁ with types := L₁.types.push none }, ?_, ?_, ?_⟩
  · rw [he, he₁]; exact List.append_assoc _ _ _
  · rw [lowerItems_append, hl₁]; exact lowerItems_expType S (defnName g i n) t
  · rw [he]
    exact { types := by show (L₁.types.push none).size = es₁.sc.ntypes + 1; rw [Array.size_push, hS₁.types]
            comps := hS₁.comps, dcomps := hS₁.dcomps, pkgs := hS₁.pkgs, pkgs_lt := hS₁.pkgs_lt
            funcs := hS₁.funcs, insts := hS₁.insts
            vals := vals_snoc hS₁.vals (Ext.of_eq rfl rfl) trivial
            imports := hS₁.imports, nodes := hS₁.nodes, exports := hS₁.exports, share := hS₁.share }

/-- The lowering state after an instantiation of `c` with arguments `rs`. -/
def instSt (L : Lower.St) (c : Nat) (rs : List (List (String × Src))) : Lower.St :=
  { L with insts := L.insts.push (.node L.nodes.size none), nodes := L.nodes.push ⟨c, rs.flatten⟩ }

theorem lowerItems_inst (S : Nat → PkgSig) {L : Lower.St} {c : Nat} {as : List (String × SortIdx)}
    {rs : List (List (String × Src))} (hc : c < L.comps)
    (hm : ((firstArgs as).mapM fun a => Lower.withArg (S c) a.1 a.2).run L = .ok (rs, L)) :
    lowerItems S [.inst c as] L = .ok (instSt L c rs) := by
  show Except.map (fun x => x.2) (StateT.run ((Lower.instance_ S (.instantiate c (firstArgs as)) >>=
      fun _ => (pure PUnit.unit : Lower.LM Unit)) >>= fun _ => (pure PUnit.unit : Lower.LM Unit)) L) = _
  unfold Lower.instance_
  simp [hc, hm, StateT.run_bind, StateT.run_get]
  rfl

theorem withArg_run (s : PkgSig) {L : Lower.St} {ds : DS} (n : String) {x : SortIdx} {j : Nat}
    (hv : VRel L (some x) (ds.vals.lookup j)) :
    (Lower.withArg s n x).run L = .ok (dArg s ds (n, j), L) := by
  obtain ⟨srt, xi⟩ := x
  unfold dArg
  revert hv
  cases ds.vals.lookup j with
  | none => intro hv; exact hv.elim
  | some v =>
    intro hv
    cases srt <;> cases v <;> (try exact hv.elim) <;> (try rfl)
    all_goals first
      | (have h : L.funcs[xi]? = _ := hv; simp [Lower.withArg, Lower.get?, h]; rfl)
      | (have h : L.insts[xi]? = _ := hv; simp [Lower.withArg, Lower.get?, h]; rfl)

/-- An argument and its encoding. -/
def ArgRel (es : ESt) (a : String × Nat) (b : String × SortIdx) : Prop :=
  ∃ x, es.idx.lookup a.2 = some x ∧ b = (a.1, x)

theorem argRel_of_mapM {es : ESt} {l : List (String × Nat)} {as : List (String × SortIdx)}
    (h : (l.mapM fun a => (es.itemOf a.2).map (a.1, ·)) = .ok as) : List.Forall₂ (ArgRel es) l as := by
  have h₂ := mapM_forall₂ _ l as h
  refine h₂.imp fun a b hab => ?_
  cases hx : es.itemOf a.2 with
  | error e => rw [hx] at hab; cases hab
  | ok x => rw [hx] at hab; exact ⟨x, itemOf_ok hx, by cases hab; rfl⟩

theorem forall₂_filter {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ R (l.filter p) (m.filter q)
  | [], [], .nil => .nil
  | a :: _, b :: _, .cons hab h => by
    rw [List.filter_cons, List.filter_cons, hpq a b hab]
    split
    · exact .cons hab (forall₂_filter hpq h)
    · exact forall₂_filter hpq h

theorem argRel_first {es : ESt} :
    ∀ {l : List (String × Nat)} {as : List (String × SortIdx)},
      List.Forall₂ (ArgRel es) l as → List.Forall₂ (ArgRel es) (firstNames l) (firstArgs as)
  | [], [], .nil => .nil
  | a :: _, b :: _, .cons hab h => by
    obtain ⟨x, _, hb⟩ := hab
    refine .cons ⟨x, by assumption, hb⟩ (forall₂_filter (fun a' b' h' => ?_) (argRel_first h))
    obtain ⟨_, _, hb'⟩ := h'
    rw [hb', hb]

theorem mapM_withArg (s : PkgSig) {L : Lower.St} {ds : DS} {es : ESt}
    (hv : ∀ j, VRel L (es.idx.lookup j) (ds.vals.lookup j)) :
    ∀ {l : List (String × Nat)} {bs : List (String × SortIdx)}, List.Forall₂ (ArgRel es) l bs →
      (bs.mapM fun a => Lower.withArg s a.1 a.2).run L = .ok (l.map (dArg s ds), L)
  | [], [], .nil => rfl
  | a :: l, b :: bs, .cons hab h => by
    obtain ⟨x, hx, hb⟩ := hab
    have h₁ : (Lower.withArg s b.1 b.2).run L = .ok (dArg s ds a, L) := by
      have hr := hv a.2
      rw [hx] at hr
      rw [hb]; exact withArg_run s a.1 hr
    have h₂ := mapM_withArg s hv h
    rw [List.mapM_cons, StateT.run_bind, h₁]
    show (StateT.run (do let as ← bs.mapM fun a => Lower.withArg s a.1 a.2; pure (dArg s ds a :: as)) L) = _
    rw [StateT.run_bind, h₂]
    rfl

/-- The rest of the first import of a package. -/
def pkgFinish (es : ESt) (key : String) (t : Nat) : ESt :=
  { es.emit (.imp (depName key) (.component t)) with comps := es.comps + 1, pkgs := es.pkgs ++ [(key, es.comps)] }

/-- The packages stay below the component count when one is added at the count. -/
theorem pkgs_lt_snoc {ps : List (String × Nat)} {m : Nat} (key : String) (h : ∀ k c, ps.lookup k = some c → c < m) :
    ∀ k c, (ps ++ [(key, m)]).lookup k = some c → c < m + 1 := by
  intro k c hc
  have hc' := (lookup_snoc ps key k m).symm.trans hc
  revert hc'
  cases hl : ps.lookup k with
  | some y => intro e; exact Nat.lt_succ_of_lt (h k c (hl.trans e))
  | none =>
    intro e
    have hm : c = m := by
      by_cases hkk : k = key
      · simp only [hkk, ite_true, Option.some.injEq] at e; exact e.symm
      · simp only [hkk, ite_false, reduceCtorEq] at e
    rw [hm]; exact Nat.lt_succ_self _

/-- A package already imported. -/
theorem sim_package_old {es : ESt} {ds : DS} {L : Lower.St} {key : String} {c : Nat} (hS : Sim es ds L)
    (hk : es.pkgs.lookup key = some c) :
    dPackage key ds = (c, ds) ∧ c < es.comps := by
  have hd : dPackage key ds = (c, ds) := by simp only [dPackage, hS.pkgs, hk]
  exact ⟨hd, hS.pkgs_lt key c hk⟩

/-- The simulation after the first import of a package. -/
theorem sim_package_new {es es₂ : ESt} {ds : DS} {L L₁ : Lower.St} {key : String} {t : Nat}
    (hS : Sim es ds L) (hS₁ : Sim es₂ ds L₁) (hc₂ : es₂.comps = es.comps) :
    Sim (pkgFinish es₂ key t) { ds with comps := ds.comps + 1, pkgs := ds.pkgs ++ [(key, ds.comps)] }
      { L₁ with comps := L₁.comps + 1 } :=
  { types := hS₁.types
    comps := by show L₁.comps + 1 = es₂.comps + 1; rw [hS₁.comps]
    dcomps := by show ds.comps + 1 = es₂.comps + 1; rw [hS.dcomps, hc₂]
    pkgs := by show ds.pkgs ++ [(key, ds.comps)] = es₂.pkgs ++ [(key, es₂.comps)]; rw [hS₁.pkgs, hS.dcomps, hc₂]
    pkgs_lt := pkgs_lt_snoc key hS₁.pkgs_lt
    funcs := hS₁.funcs, insts := hS₁.insts, vals := hS₁.vals
    imports := hS₁.imports, nodes := hS₁.nodes, exports := hS₁.exports, share := hS₁.share }

theorem encPackage_new {es es₁ : ESt} {key : String} {imps exps : Externs} {c : Nat}
    (hk : es.pkgs.lookup key = none) (h : encPackage key imps exps es = .ok (c, es₁)) :
    ∃ d es₂, runT (externDesc (.comp none imps exps)) es = .ok (d, es₂) ∧
      ∀ t, d = .component t → c = es₂.comps ∧ es₁ = pkgFinish es₂ key t := by
  have h' : (do
      let (d, st) ← runT (externDesc (.comp none imps exps)) es
      let st := st.emit (.imp (depName key) d)
      let (c, st) := st.alloc .component
      pure (c, { st with pkgs := st.pkgs ++ [(key, c)] }) : Except String (Nat × ESt)) = .ok (c, es₁) := by
    unfold encPackage at h; simpa only [hk] using h
  obtain ⟨⟨d, es₂⟩, hr, hf⟩ := ebind_ok h'
  refine ⟨d, es₂, hr, fun t ht => ?_⟩
  rw [ht] at hf
  cases hf; exact ⟨rfl, rfl⟩

/-- The first instantiation of a package imports it. -/
theorem sim_package_first (S : Nat → PkgSig) {es es₁ : ESt} {ds : DS} {L : Lower.St} {key : String}
    {imps exps : Externs} {c : Nat} (hS : Sim es ds L) (hk : es.pkgs.lookup key = none)
    (h : encPackage key imps exps es = .ok (c, es₁)) :
    ∃ new L₁, es₁.items = es.items ++ new ∧ lowerItems S new L = .ok L₁ ∧ Ext L L₁ ∧
      dPackage key ds = (c, (dPackage key ds).2) ∧ c < es₁.comps ∧ Sim es₁ (dPackage key ds).2 L₁ := by
  obtain ⟨d, es₂, hr, hfin⟩ := encPackage_new hk h
  obtain ⟨ts, L₁, sc, hrun, _, he₂, hl₁, hS₁, hx₁⟩ := sim_runT S (Pres.externDesc _) hS hr
  obtain ⟨t, ht⟩ := desc_comp (Ret.externDesc _ _ d sc hrun)
  have he : c = es₂.comps ∧ es₁ = pkgFinish es₂ key t := hfin t ht
  have hc₂ : es₂.comps = es.comps := by rw [he₂]
  have hd : dPackage key ds = (ds.comps, { ds with comps := ds.comps + 1, pkgs := ds.pkgs ++ [(key, ds.comps)] }) := by
    simp only [dPackage, hS.pkgs, hk]
  refine ⟨ts.map Item.type ++ [.imp (depName key) (.component t)], { L₁ with comps := L₁.comps + 1 }, ?_, ?_,
    hx₁.trans (Ext.of_eq rfl rfl), ?_, ?_, ?_⟩
  · rw [he.2, he₂]; exact List.append_assoc _ _ _
  · rw [lowerItems_append, hl₁]; rfl
  · rw [hd, he.1, hc₂, hS.dcomps]
  · rw [he.2, he.1]; exact Nat.lt_succ_self _
  · rw [hd, he.2]; exact sim_package_new hS hS₁ hc₂

/-- **A package**: imported once, at the component index the direct translation gives it. -/
theorem sim_package (S : Nat → PkgSig) {es es₁ : ESt} {ds : DS} {L : Lower.St} {key : String}
    {imps exps : Externs} {c : Nat} (hS : Sim es ds L) (h : encPackage key imps exps es = .ok (c, es₁)) :
    ∃ new L₁, es₁.items = es.items ++ new ∧ lowerItems S new L = .ok L₁ ∧ Ext L L₁ ∧
      dPackage key ds = (c, (dPackage key ds).2) ∧ c < es₁.comps ∧ Sim es₁ (dPackage key ds).2 L₁ := by
  cases hk : es.pkgs.lookup key with
  | some c' =>
    have e : c = c' ∧ es₁ = es := by
      unfold encPackage at h; rw [hk] at h; cases h; exact ⟨rfl, rfl⟩
    obtain ⟨hd, hlt⟩ := sim_package_old hS hk
    rw [hd, e.1, e.2]
    exact ⟨[], L, (List.append_nil _).symm, rfl, Ext.refl L, rfl, hlt, hS⟩
  | none => exact sim_package_first S hS hk h

theorem dNode_inst (S : Nat → PkgSig) (g : CGraph) (i : Nat) (key : String) (imps : Externs)
    (args : List (String × Nat)) (kd : Kind) (ds : DS) :
    dNode S g i ⟨.inst key imps args, kd⟩ ds =
      { (dPackage key ds).2.setVal i (.loc (.node (dPackage key ds).2.nodes.size none)) with
        nodes := (dPackage key ds).2.nodes.push
          ⟨(dPackage key ds).1, ((firstNames (argOrder g args)).map (dArg (S (dPackage key ds).1) (dPackage key ds).2)).flatten⟩ } := rfl

/-- **An instantiation node** keeps the simulation. -/
theorem sim_inst (S : Nat → PkgSig) {g : CGraph} {es es' : ESt} {ds : DS} {L : Lower.St} {i : Nat}
    {key : String} {imps : Externs} {args : List (String × Nat)} {kd : Kind} (hS : Sim es ds L)
    (h : encNode g i ⟨.inst key imps args, kd⟩ es = .ok es') :
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧
      Sim es' (dNode S g i ⟨.inst key imps args, kd⟩ ds) L' := by
  unfold encNode at h
  obtain ⟨⟨c, es₁⟩, hp, h₁⟩ := ebind_ok h
  obtain ⟨new₁, L₁, hi₁, hl₁, _, hdp, hc, hS₁⟩ := sim_package S hS hp
  obtain ⟨as, ha, h₂⟩ := ebind_ok h₁
  have he' : es' = (((es₁.emit (.inst c as)).alloc .instance).2).setIdx i ⟨.instance, es₁.insts⟩ := by
    cases h₂; rfl
  have hfa : List.Forall₂ (ArgRel es₁) (firstNames (argOrder g args)) (firstArgs as) :=
    argRel_first (argRel_of_mapM ha)
  have hm : ((firstArgs as).mapM fun a => Lower.withArg (S c) a.1 a.2).run L₁ =
      .ok ((firstNames (argOrder g args)).map (dArg (S c) (dPackage key ds).2), L₁) :=
    mapM_withArg (S c) hS₁.vals hfa
  have hc₁ : c < L₁.comps := by rw [hS₁.comps]; exact hc
  have hl₂ : lowerItems S [.inst c as] L₁ =
      .ok (instSt L₁ c ((firstNames (argOrder g args)).map (dArg (S c) (dPackage key ds).2))) :=
    lowerItems_inst S hc₁ hm
  rw [dNode_inst, hdp, he']
  refine ⟨new₁ ++ [.inst c as], _, ?_, by rw [lowerItems_append, hl₁]; exact hl₂, ?_⟩
  · show es₁.items ++ [Item.inst c as] = _
    rw [hi₁, List.append_assoc]
  have hnew : VRel { L₁ with insts := L₁.insts.push (.node L₁.nodes.size none) }
      (some ⟨.instance, es₁.insts⟩) (some (.loc (.node (dPackage key ds).2.nodes.size none))) := by
    show (L₁.insts.push _)[es₁.insts]? = _
    rw [← hS₁.insts, Array.getElem?_push_size, hS₁.nodes]
  exact { types := hS₁.types, comps := hS₁.comps, dcomps := hS₁.dcomps, pkgs := hS₁.pkgs, pkgs_lt := hS₁.pkgs_lt
          funcs := hS₁.funcs
          insts := by show (L₁.insts.push _).size = es₁.insts + 1; rw [Array.size_push, hS₁.insts]
          vals := vals_snoc hS₁.vals (Ext.pushInst L₁ _) hnew
          imports := hS₁.imports
          nodes := by show L₁.nodes.push _ = _; rw [hS₁.nodes]
          exports := hS₁.exports, share := hS₁.share }

/-- **A non-import node** keeps the simulation. -/
theorem sim_node (S : Nat → PkgSig) {g : CGraph} {es es' : ESt} {ds : DS} {L : Lower.St} {i : Nat}
    {nd : CNode} (hS : Sim es ds L) (hv : kindSort nd.kind ≠ .value) (himp : isImportNode nd = false)
    (h : encNode g i nd es = .ok es') :
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧ Sim es' (dNode S g i nd ds) L' := by
  obtain ⟨op, kd⟩ := nd
  cases op with
  | defn n => exact sim_defn S hS h
  | inst key imps args => exact sim_inst S hS h
  | «alias» src n => exact sim_alias S hS hv h
  | imp _ | implicit _ => cases himp

/-- The other nodes. -/
theorem sim_nodes (S : Nat → PkgSig) (g : CGraph) : ∀ (l : List (CNode × Nat)) {es es' : ESt} {ds : DS}
    {L : Lower.St}, Sim es ds L → (∀ x ∈ l, kindSort x.1.kind ≠ .value) → encNodes g l es = .ok es' →
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧ Sim es' (dNodes S g l ds) L'
  | [], es, es', ds, L, hS, _, h => by
    have : es' = es := by cases h; rfl
    exact ⟨[], L, by rw [this, List.append_nil], rfl, this ▸ hS⟩
  | (nd, i) :: l, es, es', ds, L, hS, hv, h => by
    have hv' : ∀ x ∈ l, kindSort x.1.kind ≠ .value := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    unfold encNodes at h
    unfold dNodes
    by_cases hi : isImportNode nd = true
    · simp only [hi, ↓reduceIte] at h ⊢
      exact sim_nodes S g l hS hv' h
    · have hf : isImportNode nd = false := by simpa using hi
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨es₁, h₁, h₂⟩ := ebind_ok h
      obtain ⟨new₁, L₁, hi₁, hl₁, hS₁⟩ := sim_node S hS (hv _ List.mem_cons_self) hf h₁
      obtain ⟨new₂, L₂, hi₂, hl₂, hS₂⟩ := sim_nodes S g l hS₁ hv' h₂
      refine ⟨new₁ ++ new₂, L₂, by rw [hi₂, hi₁, List.append_assoc], ?_, hS₂⟩
      rw [lowerItems_append, hl₁]; exact hl₂

theorem locFuncs_eq (S : Nat → PkgSig) {L : Lower.St} {ds : DS} (hi : L.imports = ds.imports)
    (hn : L.nodes = ds.nodes) (l : Loc) : Lower.locFuncs S L l = dLocFuncs S ds l := by
  cases l with
  | imp q => simp only [Lower.locFuncs, dLocFuncs, hi]
  | node k p =>
    simp only [Lower.locFuncs, dLocFuncs, hn]
    cases ds.nodes[k]? <;> cases p <;> rfl

section exportSteps
variable (S : Nat → PkgSig) {es : ESt} {ds : DS} {L : Lower.St} {n : String} {xi : Nat}

theorem sim_export_func {s : Src} (hS : Sim es ds L) :
    Sim ((es.emit (.exp n ⟨.func, xi⟩)).alloc .func).2 { ds with exports := ds.exports.push (n, s) }
      { L with exports := L.exports.push (n, s), funcs := L.funcs.push s } :=
  { types := hS.types, comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
    funcs := by show (L.funcs.push _).size = es.funcs + 1; rw [Array.size_push, hS.funcs]
    insts := hS.insts
    vals := fun j => VRel.mono (Ext.pushFunc L _) (hS.vals j)
    imports := hS.imports
    nodes := hS.nodes
    exports := by show L.exports.push _ = ds.exports.push _; rw [hS.exports]
    share := hS.share }

theorem sim_export_type (hS : Sim es ds L) :
    Sim ((es.emit (.exp n ⟨.type, xi⟩)).alloc .type).2 ds { L with types := L.types.push none } :=
  { types := by show (L.types.push none).size = es.sc.ntypes + 1; rw [Array.size_push, hS.types]
    comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
    funcs := hS.funcs, insts := hS.insts
    vals := fun j => VRel.mono (Ext.of_eq rfl rfl) (hS.vals j)
    imports := hS.imports, nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem sim_export_comp (hS : Sim es ds L) :
    Sim ((es.emit (.exp n ⟨.component, xi⟩)).alloc .component).2 { ds with comps := ds.comps + 1 }
      { L with comps := L.comps + 1 } :=
  { types := hS.types
    comps := by show L.comps + 1 = es.comps + 1; rw [hS.comps]
    dcomps := by show ds.comps + 1 = es.comps + 1; rw [hS.dcomps]
    pkgs := hS.pkgs
    pkgs_lt := fun k c hc => Nat.lt_succ_of_lt (hS.pkgs_lt k c hc)
    funcs := hS.funcs, insts := hS.insts
    vals := fun j => VRel.mono (Ext.of_eq rfl rfl) (hS.vals j)
    imports := hS.imports, nodes := hS.nodes, exports := hS.exports, share := hS.share }

theorem sim_export_inst {l : Loc} (hS : Sim es ds L) :
    Sim ((es.emit (.exp n ⟨.instance, xi⟩)).alloc .instance).2
      { ds with exports := ds.exports ++ ((dLocFuncs S ds l).map fun f => (qual n f, l.func f)).toArray }
      { L with exports := L.exports ++ ((Lower.locFuncs S L l).map fun f => (qual n f, l.func f)).toArray,
               insts := L.insts.push l } :=
  { types := hS.types, comps := hS.comps, dcomps := hS.dcomps, pkgs := hS.pkgs, pkgs_lt := hS.pkgs_lt
    funcs := hS.funcs
    insts := by show (L.insts.push _).size = es.insts + 1; rw [Array.size_push, hS.insts]
    vals := fun j => VRel.mono (Ext.pushInst L _) (hS.vals j)
    imports := hS.imports
    nodes := hS.nodes
    exports := by
      show L.exports ++ _ = ds.exports ++ _
      rw [hS.exports, locFuncs_eq S hS.imports hS.nodes]
    share := hS.share }

/-- The export item, by the meaning of the exported node. -/
theorem sim_export_item (hS : Sim es ds L) {srt : ItemSort} {v : Option V} (hr : VRel L (some ⟨srt, xi⟩) v)
    {j : Nat} (hv : ds.vals.lookup j = v) :
    ∃ L', lowerItems S [.exp n ⟨srt, xi⟩] L = .ok L' ∧
      Sim ((es.emit (.exp n ⟨srt, xi⟩)).alloc srt).2 (dExport S ds n j) L' := by
  unfold dExport
  rw [hv]
  match srt, v, hr with
  | .func, some (.src s), hr => exact ⟨_, lowerItems_expFunc S n hr, sim_export_func hS⟩
  | .instance, some (.loc l), hr => exact ⟨_, lowerItems_expInst S n hr, sim_export_inst S hS⟩
  | .type, some .type, _ => exact ⟨_, lowerItems_expType S n xi, sim_export_type hS⟩
  | .component, some .comp, _ => exact ⟨_, lowerItems_expComp S n xi, sim_export_comp hS⟩

end exportSteps

/-- **An export** keeps the simulation. -/
theorem sim_export (S : Nat → PkgSig) {es es' : ESt} {ds : DS} {L : Lower.St} {n : String} {j : Nat}
    (hS : Sim es ds L) (h : encExport es n j = .ok es') :
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧ Sim es' (dExport S ds n j) L' := by
  unfold encExport at h
  obtain ⟨⟨srt, xi⟩, hx, h'⟩ := ebind_ok h
  have he : es' = ((es.emit (.exp n ⟨srt, xi⟩)).alloc srt).2 := by cases h'; rfl
  have hr : VRel L (some ⟨srt, xi⟩) (ds.vals.lookup j) := itemOf_ok hx ▸ hS.vals j
  obtain ⟨L', hl, hs⟩ := sim_export_item S hS hr rfl
  refine ⟨[.exp n ⟨srt, xi⟩], L', ?_, hl, he ▸ hs⟩
  rw [he]; cases srt <;> rfl

/-- The exports. -/
theorem sim_exports (S : Nat → PkgSig) (g : CGraph) : ∀ (l : List (String × Nat)) {es es' : ESt} {ds : DS}
    {L : Lower.St}, Sim es ds L → encExports g l es = .ok es' →
    ∃ new L', es'.items = es.items ++ new ∧ lowerItems S new L = .ok L' ∧ Sim es' (dExports S g l ds) L'
  | [], es, es', ds, L, hS, h => by
    have : es' = es := by cases h; rfl
    exact ⟨[], L, by rw [this, List.append_nil], rfl, this ▸ hS⟩
  | (n, j) :: l, es, es', ds, L, hS, h => by
    unfold encExports at h
    unfold dExports
    by_cases hd : isDefnNode g j = true
    · simp only [hd, ↓reduceIte] at h ⊢
      exact sim_exports S g l hS h
    · have hf : isDefnNode g j = false := by simpa using hd
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨es₁, h₁, h₂⟩ := ebind_ok h
      obtain ⟨new₁, L₁, hi₁, hl₁, hS₁⟩ := sim_export S hS h₁
      obtain ⟨new₂, L₂, hi₂, hl₂, hS₂⟩ := sim_exports S g l hS₁ h₂
      refine ⟨new₁ ++ new₂, L₂, by rw [hi₂, hi₁, List.append_assoc], ?_, hS₂⟩
      rw [lowerItems_append, hl₁]; exact hl₂

theorem mem_filterMap_zipIdx {g : CGraph} {f : CNode × Nat → Option (Nat × String × Kind)}
    (hf : ∀ p y, f p = some y → y.2.2 = p.1.kind) {y : Nat × String × Kind}
    (hy : y ∈ g.nodes.zipIdx.filterMap f) : ∃ nd ∈ g.nodes, nd.kind = y.2.2 := by
  obtain ⟨p, hp, hfp⟩ := List.mem_filterMap.mp hy
  exact ⟨p.1, List.fst_mem_of_mem_zipIdx hp, (hf p y hfp).symm⟩

theorem mem_importOrder {g : CGraph} {y : Nat × String × Kind} (hy : y ∈ importOrder g) :
    ∃ nd ∈ g.nodes, nd.kind = y.2.2 := by
  have hf₁ : ∀ (p : CNode × Nat) (y : Nat × String × Kind),
      (match p with | (nd, i) => match nd.op with | .implicit n => some (i, n, nd.kind) | _ => none) = some y →
      y.2.2 = p.1.kind := by
    intro ⟨⟨op, k⟩, i⟩ y h
    cases op <;> simp at h; rw [← h]
  have hf₂ : ∀ (p : CNode × Nat) (y : Nat × String × Kind),
      (match p with | (nd, i) => match nd.op with | .imp n => some (i, n, nd.kind) | _ => none) = some y →
      y.2.2 = p.1.kind := by
    intro ⟨⟨op, k⟩, i⟩ y h
    cases op <;> simp at h; rw [← h]
  have hall : y ∈ (g.nodes.zipIdx.filterMap fun (nd, i) => match nd.op with
        | .implicit n => some (i, n, nd.kind) | _ => none) ++
      (g.nodes.zipIdx.filterMap fun (nd, i) => match nd.op with
        | .imp n => some (i, n, nd.kind) | _ => none) := by
    unfold importOrder at hy
    rcases List.mem_append.mp hy with h | h
    · exact (List.mem_filter.mp h).1
    · exact (List.mem_filter.mp h).1
  rcases List.mem_append.mp hall with h | h
  · exact mem_filterMap_zipIdx hf₁ h
  · exact mem_filterMap_zipIdx hf₂ h

theorem run_of_lowerItems (S : Nat → PkgSig) {its : List Item} {L L' : Lower.St}
    (h : lowerItems S its L = .ok L') :
    ((its.map Item.toSection).forM (Lower.section_ S)).run L = .ok ((), L') := by
  unfold lowerItems at h
  cases hr : ((its.map Item.toSection).forM (Lower.section_ S)).run L with
  | error e => rw [hr] at h; cases h
  | ok p => rw [hr] at h; cases h; rfl

theorem sim_init (nom : NomTable) : Sim { sc := { nom } } {} {} :=
  { types := rfl, comps := rfl, dcomps := rfl, pkgs := rfl, pkgs_lt := fun _ _ h => by cases h
    funcs := rfl, insts := rfl, vals := fun _ => trivial, imports := rfl, nodes := rfl, exports := rfl
    share := rfl }

theorem encode_ok {nom : NomTable} {g : CGraph} {c : Ast} (h : encode nom g = .ok c) :
    ∃ es₁ es₂ es₃, encImports (importOrder g) { sc := { nom } } = .ok es₁ ∧
      encNodes g g.nodes.zipIdx es₁ = .ok es₂ ∧ encExports g g.exports es₂ = .ok es₃ ∧
      c = .mk (es₃.items.map Item.toSection) := by
  unfold encode encodeItems at h
  cases he : encGraph g { sc := { nom } } with
  | error e => rw [he] at h; cases h
  | ok es₃ =>
    have hc : c = .mk (es₃.items.map Item.toSection) := by rw [he] at h; cases h; rfl
    unfold encGraph at he
    obtain ⟨es₁, h₁, h₁'⟩ := ebind_ok he
    obtain ⟨es₂, h₂, h₃⟩ := ebind_ok h₁'
    exact ⟨es₁, es₂, es₃, h₁, h₂, h₃, hc⟩

theorem graph_of_run (S : Nat → PkgSig) {its : List Item} {L : Lower.St}
    (hp : isProfile (.mk (its.map Item.toSection)) = true)
    (hrun : ((its.map Item.toSection).forM (Lower.section_ S)).run {} = .ok ((), L)) :
    Lower.graph S (.mk (its.map Item.toSection)) =
      .ok (typeImports S ⟨L.imports.toList, L.nodes.toList, L.exports.toList⟩) := by
  unfold Lower.graph
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Ast.sections, hrun]
  rfl

/-- **Agreement**: lowering the encoding of an elaborated graph gives its direct
translation. -/
theorem lower_encode (S : Nat → PkgSig) {nom : NomTable} {g : CGraph} {c : Ast} (hnv : NoValue g)
    (h : encode nom g = .ok c) : Lower.graph S c = .ok (toGraph S g) := by
  have hp : isProfile c = true := encode_profile h
  obtain ⟨es₁, es₂, es₃, h₁, h₂, h₃, hc⟩ := encode_ok h
  have hv₁ : ∀ x ∈ importOrder g, kindSort x.2.2 ≠ .value := fun x hx => by
    obtain ⟨nd, hnd, hk⟩ := mem_importOrder hx
    rw [← hk]; exact hnv nd hnd
  have hv₂ : ∀ x ∈ g.nodes.zipIdx, kindSort x.1.kind ≠ .value := fun x hx =>
    hnv x.1 (List.fst_mem_of_mem_zipIdx hx)
  obtain ⟨n₁, L₁, hi₁, hl₁, hS₁⟩ := sim_imports S (importOrder g) (sim_init nom) hv₁ h₁
  obtain ⟨n₂, L₂, hi₂, hl₂, hS₂⟩ := sim_nodes S g g.nodes.zipIdx hS₁ hv₂ h₂
  obtain ⟨n₃, L₃, hi₃, hl₃, hS₃⟩ := sim_exports S g g.exports hS₂ h₃
  have hitems : es₃.items = n₁ ++ n₂ ++ n₃ := by rw [hi₃, hi₂, hi₁]; rfl
  have hl : lowerItems S es₃.items {} = .ok L₃ := by
    rw [hitems, lowerItems_append, lowerItems_append, hl₁]; exact (by rw [Except.bind, hl₂]; exact hl₃)
  have hp' : isProfile (.mk (es₃.items.map Item.toSection)) = true := hc ▸ hp
  calc Lower.graph S c
      = .ok (typeImports S ⟨L₃.imports.toList, L₃.nodes.toList, L₃.exports.toList⟩) := by
        rw [hc]; exact graph_of_run S hp' (run_of_lowerItems S hl)
    _ = .ok (toGraph S g) := by
        unfold toGraph; rw [hS₃.imports, hS₃.nodes, hS₃.exports]

end Silmaril.Wasm.Wac.Bridge
