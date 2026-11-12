module

public import Silmaril.Wasm.Wac.Bridge.EncodeUse.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeUse.Thms

/-!
# WAC bridge: `decodePkgU` on the instance type of an interface that uses others

The scope of the instance type is `bst W O N L`: its types are the list `L`, the
enclosing scopes `W :: O` (`W` the wrapper's types), the nominal table `N`, no
instances. Each block of `ifaceBody` is read by one lemma, by induction on its list:

* `useAliases_run`: the aliases `outer 1 (2 k + 1)` push the used types `usedT e`;
* `useExports_run`: their exports are `WitDecl.usedKind e.I e.t`, pushing them again;
* `resExports_run`: the own resources;
* `funcDecls_run`: each parameter type (`decDefValU_par`), the function type
  (`parVals_mapM`), the export.

`ifaceBody_run` combines them: the items are `rdIface u`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner IfaceName)

namespace EncodeUse

open DecodeUse

attribute [local simp] ok_bindE' pure_okE Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind DecodeNamed.throw_run

/-- A used type, as the type index space keeps it. -/
def usedT (e : UseT) : TInfo := .val (.own ⟨.iface e.I, e.t⟩)

/-- The scope of an instance type: types `L`, enclosing scopes `W :: O`. -/
def bst (W : Array TInfo) (O : List (Array TInfo)) (N : NomTable) (L : List TInfo) : UScope :=
  { base := { types := L.toArray, outer := W :: O, nom := N } }

theorem decIDeclsU_cons (d : InstanceDecl) (ds : List InstanceDecl) (es : Externs) (u u1 : UScope)
    (es1 : Externs) (h : (decIDeclU d es).run u = .ok (es1, u1)) :
    (decIDeclsU (d :: ds) es).run u = (decIDeclsU ds es1).run u1 := by
  rw [decIDeclsU, bind_runU h]

theorem getElem?_append_of_some {α : Type} {L X : List α} {i : Nat} {a : α} (h : L[i]? = some a) :
    (L ++ X)[i]? = some a := by
  have hi : i < L.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hi, h]

section
variable (W : Array TInfo) (O : List (Array TInfo)) (N : NomTable)

theorem useAliases_run : ∀ (k : Nat) (l : List UseT) (L : List TInfo) (rest : List InstanceDecl) (es : Externs),
    (∀ i (h : i < l.length), W[2 * (k + i) + 1]? = some (usedT l[i])) →
    (decIDeclsU (useAliases k l ++ rest) es).run (bst W O N L) =
      (decIDeclsU rest es).run (bst W O N (L ++ l.map usedT))
  | _, [], L, rest, es, _ => by simp [useAliases]
  | k, e :: l, L, rest, es, h => by
    have h0 : W[2 * k + 1]? = some (usedT e) := h 0 (by simp)
    have ih := useAliases_run (k + 1) l (L ++ [usedT e]) rest es fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show k + (i + 1) = k + 1 + i by omega] at this
      simpa using this
    rw [useAliases, List.cons_append]
    rw [decIDeclsU_cons _ _ _ _ (bst W O N (L ++ [usedT e])) es]
    · simpa using ih
    · simp [decIDeclU, decAliasU, onBase_run, decAlias, bst, pushTy, StateT.run_bind, StateT.run_get, h0]

theorem useExports_run : ∀ (k : Nat) (l : List UseT) (L : List TInfo) (rest : List InstanceDecl) (es : Externs),
    (∀ i (h : i < l.length), L[k + i]? = some (usedT l[i])) →
    (decIDeclsU (useExports k l ++ rest) es).run (bst W O N L) =
      (decIDeclsU rest (es ++ l.map fun e => (e.l, WitDecl.usedKind e.I e.t))).run (bst W O N (L ++ l.map usedT))
  | _, [], L, rest, es, _ => by simp [useExports]
  | k, e :: l, L, rest, es, h => by
    have h0 : L[k]? = some (usedT e) := h 0 (by simp)
    have ih := useExports_run (k + 1) l (L ++ [usedT e]) rest (es ++ [(e.l, WitDecl.usedKind e.I e.t)])
      fun i hi => by
        have := h (i + 1) (by simp; omega)
        rw [show k + (i + 1) = k + 1 + i by omega] at this
        simpa using getElem?_append_of_some this
    rw [useExports, List.cons_append]
    rw [decIDeclsU_cons _ _ _ _ (bst W O N (L ++ [usedT e])) (es ++ [(e.l, WitDecl.usedKind e.I e.t)])]
    · simpa using ih
    · simp [decIDeclU, decExternU, onBase_run, typeAt, bst, pushTy, StateT.run_bind, StateT.run_get, h0,
        namedInfoU, isUsed, usedT, addNom, typeKindU, WitDecl.usedKind]

theorem resExports_run : ∀ (rs : List String) (L : List TInfo) (rest : List InstanceDecl) (es : Externs),
    (decIDeclsU (resExports rs ++ rest) es).run (bst W O N L) =
      (decIDeclsU rest (es ++ rs.map fun r => (r, .type (.resource r)))).run (bst W O N (L ++ rs.map .res))
  | [], L, rest, es => by simp [resExports]
  | r :: rs, L, rest, es => by
    have ih := resExports_run rs (L ++ [.res r]) rest (es ++ [(r, .type (.resource r))])
    simp only [resExports, List.map_cons, List.cons_append]
    rw [decIDeclsU_cons _ _ _ _ (bst W O N (L ++ [.res r])) (es ++ [(r, .type (.resource r))])]
    · simpa using ih
    · simp [decIDeclU, decExternU, onBase_run, decExtern, bst, pushTy]

/-! ### Functions -/

/-- The types every scope of an instance type of `u` starts with: the used types (aliases),
again (their exports), the own resources. -/
def P0 (u : UIface) : List TInfo := u.uses.map usedT ++ u.uses.map usedT ++ u.res.map .res

theorem P0_length (u : UIface) : (P0 u).length = 2 * u.uses.length + u.res.length := by
  simp [P0]; omega

theorem lookup_used (u : UIface) {j : Nat} {e : UseT} (he : u.uses[j]? = some e) (X : List TInfo) :
    (P0 u ++ X)[u.uses.length + j]? = some (usedT e) := by
  have hj : j < u.uses.length := (List.getElem?_eq_some_iff.mp he).1
  have h1 : (u.uses.map usedT ++ u.res.map TInfo.res ++ X)[j]? = some (usedT e) := by
    rw [List.append_assoc, List.getElem?_append_left (by simpa using hj)]
    simp [he]
  simp only [P0, List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simpa using h1

theorem lookup_own (u : UIface) {j : Nat} {r : String} (hr : u.res[j]? = some r) (X : List TInfo) :
    (P0 u ++ X)[2 * u.uses.length + j]? = some (.res r) := by
  have hj : j < u.res.length := (List.getElem?_eq_some_iff.mp hr).1
  simp only [P0, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [show 2 * u.uses.length + j - u.uses.length - u.uses.length = j by omega, hr]

theorem decDefValU_own (u : UIface) (r : URes) (hr : r.Ok u) (X : List TInfo) :
    (decDefValU ((UPar.own r).def u.uses.length)).run (bst W O N (P0 u ++ X)) =
      .ok (.val ((UPar.own r).rd u), bst W O N (P0 u ++ X)) := by
  cases r with
    | used j =>
      have hj : j < u.uses.length := hr
      have he : u.uses[j]? = some u.uses[j] := List.getElem?_eq_getElem hj
      have hl : (P0 u ++ X)[u.uses.length + j]? = some (usedT u.uses[j]) := lookup_used u he X
      simp [UPar.def, URes.idx, UPar.rd, URes.rd, decDefValU, onBase_run, typeAt, bst, hl, he, usedRes,
        usedT, StateT.run_bind, StateT.run_get]
    | own j =>
      have hj : j < u.res.length := hr
      have hq : u.res[j]? = some u.res[j] := List.getElem?_eq_getElem hj
      have hl : (P0 u ++ X)[2 * u.uses.length + j]? = some (.res u.res[j]) := lookup_own u hq X
      simp [UPar.def, URes.idx, UPar.rd, URes.rd, decDefValU, onBase_run, typeAt, bst, hl, hq, usedRes,
        decDefVal, resAt, StateT.run_bind, StateT.run_get, List.getD_eq_getElem?_getD]

theorem decDefValU_borrow (u : UIface) (r : URes) (hr : r.Ok u) (X : List TInfo) :
    (decDefValU ((UPar.borrow r).def u.uses.length)).run (bst W O N (P0 u ++ X)) =
      .ok (.val ((UPar.borrow r).rd u), bst W O N (P0 u ++ X)) := by
  cases r with
    | used j =>
      have hj : j < u.uses.length := hr
      have he : u.uses[j]? = some u.uses[j] := List.getElem?_eq_getElem hj
      have hl : (P0 u ++ X)[u.uses.length + j]? = some (usedT u.uses[j]) := lookup_used u he X
      simp [UPar.def, URes.idx, UPar.rd, URes.rd, decDefValU, onBase_run, typeAt, bst, hl, he, usedRes,
        usedT, StateT.run_bind, StateT.run_get]
    | own j =>
      have hj : j < u.res.length := hr
      have hq : u.res[j]? = some u.res[j] := List.getElem?_eq_getElem hj
      have hl : (P0 u ++ X)[2 * u.uses.length + j]? = some (.res u.res[j]) := lookup_own u hq X
      simp [UPar.def, URes.idx, UPar.rd, URes.rd, decDefValU, onBase_run, typeAt, bst, hl, hq, usedRes,
        decDefVal, resAt, StateT.run_bind, StateT.run_get, List.getD_eq_getElem?_getD]

theorem decDefValU_par (u : UIface) (p : UPar) (hp : p.Ok u) (X : List TInfo) :
    (decDefValU (p.def u.uses.length)).run (bst W O N (P0 u ++ X)) =
      .ok (.val (p.rd u), bst W O N (P0 u ++ X)) := by
  cases p with
  | prim q => simp [UPar.def, UPar.rd, decDefValU, onBase_run, decDefVal]
  | own r => exact decDefValU_own W O N u r hp X
  | borrow r => exact decDefValU_borrow W O N u r hp X

/-- What the parameter types of a function push. -/
def parInfo (u : UIface) (ps : List (String × UPar)) : List TInfo := ps.map fun p => .val (p.2.rd u)

@[simp] theorem parInfo_length (u : UIface) (ps : List (String × UPar)) : (parInfo u ps).length = ps.length := by
  simp [parInfo]

theorem parInfo_cons (u : UIface) (p : String × UPar) (ps : List (String × UPar)) :
    parInfo u (p :: ps) = .val (p.2.rd u) :: parInfo u ps := rfl

theorem parTys_run (u : UIface) : ∀ (ps : List (String × UPar)) (X : List TInfo) (rest : List InstanceDecl)
    (es : Externs), (∀ p ∈ ps, p.2.Ok u) →
    (decIDeclsU (ps.map (fun p => .type (.val (p.2.def u.uses.length))) ++ rest) es).run (bst W O N (P0 u ++ X)) =
      (decIDeclsU rest es).run (bst W O N (P0 u ++ (X ++ parInfo u ps)))
  | [], X, rest, es, _ => by simp [parInfo]
  | p :: ps, X, rest, es, h => by
    have ih := parTys_run u ps (X ++ [.val (p.2.rd u)]) rest es fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hd := decDefValU_par W O N u p.2 (h p List.mem_cons_self) X
    rw [List.map_cons, List.cons_append, decIDeclsU_cons _ _ _ _ (bst W O N (P0 u ++ X ++ [.val (p.2.rd u)])) es]
    · simpa [parInfo_cons] using ih
    · simp only [decIDeclU, decDefTypeU, StateT.run_bind, hd, onBase_run, pushTy, ok_bindE', StateT.run_modify]
      simp [bst]

theorem parVals_mapM (u : UIface) : ∀ (ps : List (String × UPar)) (c : Nat) (δ : DScope),
    (∀ i (h : i < ps.length), δ.types[c + i]? = some (.val (ps[i].2.rd u))) →
    ((parVals c ps).mapM fun (p : String × Silmaril.Wasm.Component.Binary.ValType) => Prod.mk p.1 <$> decVal p.2).run δ =
      .ok (ps.map fun p => (p.1, p.2.rd u), δ)
  | [], c, δ, _ => by simp [parVals]
  | (x, p) :: ps, c, δ, h => by
    have h0 : δ.types[c]? = some (.val (p.rd u)) := h 0 (by simp)
    have ih := parVals_mapM u ps (c + 1) δ fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show c + (i + 1) = c + 1 + i by omega] at this
      exact this
    have hd : (decVal (.idx c)).run δ = .ok (p.rd u, δ) := by
      simp [decVal, typeAt, StateT.run_bind, StateT.run_get, h0]
    simp [parVals, List.mapM_cons, StateT.run_bind, hd, ih]

theorem decFunc_par (u : UIface) (ps : List (String × UPar)) (c : Nat) (L X : List TInfo) (hc : (L ++ X).length = c) :
    (decFunc ⟨parVals c ps, none, false⟩).run { types := (L ++ (X ++ parInfo u ps)).toArray, outer := W :: O, nom := N } =
      .ok (sigRd u ps, { types := (L ++ (X ++ parInfo u ps)).toArray, outer := W :: O, nom := N }) := by
  have hm := parVals_mapM u ps c { types := (L ++ (X ++ parInfo u ps)).toArray, outer := W :: O, nom := N }
    fun i hi => by
      simp only [List.getElem?_toArray]
      rw [← List.append_assoc, List.getElem?_append_right (by omega),
        show c + i - (L ++ X).length = i by omega]
      simp [parInfo, List.getElem?_eq_getElem hi]
  simp [decFunc, hm, decValOpt, sigRd]

theorem funcDecls_run (u : UIface) (hu : ∀ f ∈ u.funcs, ∀ p ∈ f.2, p.2.Ok u) :
    ∀ (fs : List (String × List (String × UPar))) (c : Nat) (X : List TInfo) (rest : List InstanceDecl)
      (es : Externs), (∀ f ∈ fs, f ∈ u.funcs) → (P0 u ++ X).length = c →
    ∃ X', (decIDeclsU (funcDecls u.uses.length c fs ++ rest) es).run (bst W O N (P0 u ++ X)) =
      (decIDeclsU rest (es ++ fs.map fun f => (f.1, .func (sigRd u f.2)))).run (bst W O N (P0 u ++ X'))
  | [], c, X, rest, es, _, _ => ⟨X, by simp [funcDecls]⟩
  | (f, ps) :: fs, c, X, rest, es, hfs, hc => by
    have hps : ∀ p ∈ ps, p.2.Ok u := hu (f, ps) (hfs _ List.mem_cons_self)
    have hc' : (P0 u).length + X.length = c := by simpa using hc
    obtain ⟨X', hX'⟩ := funcDecls_run u hu fs (c + ps.length + 1) (X ++ (parInfo u ps ++ [.func (sigRd u ps)])) rest
      (es ++ [(f, .func (sigRd u ps))]) (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) (by simp; omega)
    refine ⟨X', ?_⟩
    have hP := parTys_run W O N u ps X
      ([.type (.func ⟨parVals c ps, none, false⟩), .export ⟨f, .plain0⟩ (.func (c + ps.length))] ++
        funcDecls u.uses.length (c + ps.length + 1) fs ++ rest) es hps
    have hF := decFunc_par W O N u ps c (P0 u) X hc
    have hT : (P0 u ++ (X ++ (parInfo u ps ++ [.func (sigRd u ps)])))[c + ps.length]? =
        some (.func (sigRd u ps)) := by
      rw [← List.append_assoc, ← List.append_assoc,
        List.getElem?_append_right (by simp; omega), show c + ps.length - (P0 u ++ X ++ parInfo u ps).length = 0 by
          simp; omega]
      rfl
    simp only [funcDecls, List.append_assoc, List.cons_append, List.nil_append] at hP ⊢
    rw [hP]
    rw [decIDeclsU_cons _ _ _ _ (bst W O N (P0 u ++ (X ++ (parInfo u ps ++ [.func (sigRd u ps)])))) es]
    · rw [decIDeclsU_cons _ _ _ _ (bst W O N (P0 u ++ (X ++ (parInfo u ps ++ [.func (sigRd u ps)]))))
        (es ++ [(f, .func (sigRd u ps))])]
      · simpa using hX'
      · simp [decIDeclU, decExternU, onBase_run, decExtern, typeAt, StateT.run_bind, StateT.run_get, bst, hT]
    · simp [decIDeclU, decDefTypeU, StateT.run_bind, onBase_run, bst, hF, pushTy]

/-! ### The instance type -/

/-- **The instance type of an interface is read as its items** `rdIface u`, in a scope
whose enclosing scope `W` holds the used type `k` at index `2 k + 1`. -/
theorem ifaceBody_run (u : UIface) (hu : u.Ok)
    (hW : ∀ i (h : i < u.uses.length), W[2 * i + 1]? = some (usedT u.uses[i])) :
    ∃ L', (decIDeclsU (ifaceBody u) []).run (bst W O N []) = .ok (rdIface u, bst W O N L') := by
  have h1 := useAliases_run W O N 0 u.uses [] (useExports 0 u.uses ++ resExports u.res ++
    funcDecls u.uses.length (2 * u.uses.length + u.res.length) u.funcs) [] fun i h => by simpa using hW i h
  have h2 := useExports_run W O N 0 u.uses ([] ++ u.uses.map usedT) (resExports u.res ++
    funcDecls u.uses.length (2 * u.uses.length + u.res.length) u.funcs) [] fun i h => by
      simp [List.getElem?_eq_getElem h]
  have h3 := resExports_run W O N u.res ([] ++ u.uses.map usedT ++ u.uses.map usedT)
    (funcDecls u.uses.length (2 * u.uses.length + u.res.length) u.funcs ++ [])
    ([] ++ u.uses.map fun e => (e.l, WitDecl.usedKind e.I e.t))
  obtain ⟨X', h4⟩ := funcDecls_run W O N u hu.pars u.funcs (2 * u.uses.length + u.res.length) [] []
    ([] ++ (u.uses.map fun e => (e.l, WitDecl.usedKind e.I e.t)) ++ u.res.map fun r => (r, .type (.resource r)))
    (fun _ h => h) (by simp [P0_length])
  have e3 : u.uses.map usedT ++ (u.uses.map usedT ++ u.res.map TInfo.res) = P0 u := by simp [P0]
  refine ⟨P0 u ++ X', ?_⟩
  simp only [ifaceBody, List.nil_append, List.append_assoc, List.append_nil] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, e3, h4]
  simp [decIDeclsU, rdIface]

end

end EncodeUse

end Silmaril.Wasm.Wac.Bridge
