module

public import Silmaril.Proofs.Wasm.Wac.Bridge.EncodeUse.Body

/-!
# WAC bridge: `decodePkgU` on the wrappers and the package of `usePkg`

* `useDecls_run`: the declarations of the used interfaces in a wrapper (instance type,
  import, alias of the type export) record each import with its interface and push the
  used type `usedT e` at the type index `2 k + 1`;
* `wrapper_run`: a wrapper is read as the component type importing the used interfaces
  and exporting the interface with items `rdIface u`;
* `itemDecls_run`: the package's declarations (as projected) are read item by item;
* `norm_ifaceDefU`: the WAT normal form does not change the wrappers;
* `pkgOfWorldU_usePkg`: the package read from the world is `usePkgRd items`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner IfaceName)
open Silmaril.Wasm.Component.Wat (normName normDefType normComponentDecls normComponentDecl normInstanceDecls
  normInstanceDecl)

namespace EncodeUse

open DecodeUse

attribute [local simp] ok_bindE' pure_okE Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind DecodeNamed.throw_run

/-- The exports of a used interface's instance type. -/
def instEs (e : UseT) : Externs := [(e.t, .type (.resource e.t))]

/-- The types the used interfaces push in the wrapper. -/
def useTys (l : List UseT) : List TInfo := l.flatMap fun e => [.inst (instEs e), usedT e]

/-- The imports of the wrapper. -/
def useImps (l : List UseT) : Externs := l.map fun e => (e.iid, .inst (ifaceId e.iid) (instEs e))

/-- The scope of a wrapper. -/
def wst (Op : List (Array TInfo)) (N : NomTable) (Lt : List TInfo) (Li : List Externs)
    (Lj : List (Option IfaceName)) : UScope :=
  { base := { types := Lt.toArray, insts := Li.toArray, outer := Op, nom := N }, ids := Lj.toArray }

theorem decCDeclsU_inst (d : InstanceDecl) (ds : List ComponentDecl) (is es : Externs) (u u1 : UScope)
    (es1 : Externs) (h : (decIDeclU d es).run u = .ok (es1, u1)) :
    (decCDeclsU (.inst d :: ds) is es).run u = (decCDeclsU ds is es1).run u1 := by
  rw [decCDeclsU, bind_runU h]

theorem decCDeclsU_imp (n : ExternName) (d : ExternDesc) (ds : List ComponentDecl) (is es : Externs)
    (u u1 : UScope) (k : Kind) (h : (decExternU n.name d).run u = .ok (k, u1)) :
    (decCDeclsU (.import n d :: ds) is es).run u = (decCDeclsU ds (is ++ [(n.name, k)]) es).run u1 := by
  rw [decCDeclsU, bind_runU h]

theorem inNestedU_run {α : Type} {m : UM α} {u : UScope} {a : α} {u' : UScope}
    (h : m.run { base := { outer := u.base.types :: u.base.outer, nom := u.base.nom } } = .ok (a, u')) :
    (inNestedU m).run u = .ok (a, { u with base := { u.base with nom := u'.base.nom } }) := by
  simp [inNestedU, StateT.run_bind, StateT.run_get, h, StateT.run_set]

theorem length_useTys (l : List UseT) : (useTys l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [useTys] at ih ⊢; omega

theorem useTys_get : ∀ (l : List UseT) (i : Nat) (h : i < l.length), (useTys l)[2 * i + 1]? = some (usedT l[i])
  | [], _, h => absurd h (by simp)
  | e :: l, 0, _ => rfl
  | e :: l, i + 1, h => by
    have := useTys_get l i (by simpa using h)
    simpa [useTys, show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by omega] using this

section
variable (Op : List (Array TInfo)) (N : NomTable)

theorem useDecls_run : ∀ (k : Nat) (l : List UseT) (Lt : List TInfo) (Li : List Externs)
    (Lj : List (Option IfaceName)) (is es : Externs) (rest : List ComponentDecl),
    (∀ e ∈ l, ifaceOf e.iid = some e.I) → Lt.length = 2 * k → Li.length = k → Lj.length = k →
    (decCDeclsU (useDecls k l ++ rest) is es).run (wst Op N Lt Li Lj) =
      (decCDeclsU rest (is ++ useImps l) es).run
        (wst Op N (Lt ++ useTys l) (Li ++ l.map instEs) (Lj ++ l.map fun e => some e.I))
  | _, [], Lt, Li, Lj, is, es, rest, _, _, _, _ => by simp [useDecls, useImps, useTys]
  | k, e :: l, Lt, Li, Lj, is, es, rest, hI, ht, hi, hj => by
    have hIe : ifaceOf e.iid = some e.I := hI e List.mem_cons_self
    have ih := useDecls_run (k + 1) l (Lt ++ [.inst (instEs e), usedT e]) (Li ++ [instEs e]) (Lj ++ [some e.I])
      (is ++ [(e.iid, .inst (ifaceId e.iid) (instEs e))]) es rest (fun x hx => hI x (List.mem_cons_of_mem _ hx))
      (by simp; omega) (by simp; omega) (by simp; omega)
    have g1 : (Lt ++ [TInfo.inst (instEs e)])[2 * k]? = some (.inst (instEs e)) := by
      rw [List.getElem?_append_right (by omega)]; simp [ht]
    have g2 : (Li ++ [instEs e])[k]? = some (instEs e) := by
      rw [List.getElem?_append_right (by omega)]; simp [hi]
    have g3 : (Lj ++ [some e.I])[k]? = some (some e.I) := by
      rw [List.getElem?_append_right (by omega)]; simp [hj]
    rw [useDecls, List.cons_append, List.cons_append, List.cons_append]
    rw [decCDeclsU_inst _ _ _ _ _ (wst Op N (Lt ++ [.inst (instEs e)]) Li Lj) es]
    · rw [decCDeclsU_imp _ _ _ _ _ _ (wst Op N (Lt ++ [.inst (instEs e)]) (Li ++ [instEs e]) (Lj ++ [some e.I]))
        (.inst (ifaceId e.iid) (instEs e))]
      · rw [decCDeclsU_inst _ _ _ _ _ (wst Op N (Lt ++ [.inst (instEs e), usedT e]) (Li ++ [instEs e])
          (Lj ++ [some e.I])) es]
        · simpa [useImps, useTys] using ih
        · have hl : (instEs e).lookup e.t = some (.type (.resource e.t)) := by simp [instEs]
          simp [decIDeclU, decAliasU, wst, StateT.run_bind, StateT.run_get, g2, g3, hl, onBase_run, pushTy,
            usedInfo, usedT]
      · simp [decExternU, onBase_run, typeAt, wst, StateT.run_bind, StateT.run_get, g1, StateT.run_modify, hIe]
    · have hn : (decIDeclsU [.export ⟨e.t, .plain0⟩ (.type .subResource)] []).run
          { base := { outer := Lt.toArray :: Op, nom := N } } =
          .ok (instEs e, { base := { types := #[.res e.t], outer := Lt.toArray :: Op, nom := N } }) := by
        simp [decIDeclsU, decIDeclU, decExternU, onBase_run, decExtern, pushTy, instEs]
      have hN := inNestedU_run (u := wst Op N Lt Li Lj) (by simpa [wst] using hn)
      simp only [wst] at hN ⊢
      simp [decIDeclU, decDefTypeU, StateT.run_bind, hN, pushTy, onBase_run]

/-- **A wrapper is read as the component type** importing the used interfaces and exporting
the interface, with items `rdIface u`. -/
theorem wrapper_run (id : String) (u : UIface) (hu : u.Ok) :
    ∃ s', (decCDeclsU (useDecls 0 u.uses ++ [.inst (.type (.instance (ifaceBody u))),
        .inst (.export ⟨id, .plain0⟩ (.instance (2 * u.uses.length)))]) [] []).run (wst Op N [] [] []) =
      .ok ((useImps u.uses, [(id, .inst (ifaceId id) (rdIface u))]), s') ∧ s'.base.nom = N := by
  rw [useDecls_run Op N 0 u.uses [] [] [] [] [] _ hu.uses rfl rfl rfl]
  simp only [List.nil_append]
  obtain ⟨L', hb⟩ := ifaceBody_run (useTys u.uses).toArray Op N u hu fun i h => by
    simpa using useTys_get u.uses i h
  have hN := inNestedU_run (u := wst Op N (useTys u.uses) (u.uses.map instEs) (u.uses.map fun e => some e.I))
    (m := decIDeclsU (ifaceBody u) []) (by exact hb)
  have g : (useTys u.uses ++ [TInfo.inst (rdIface u)])[2 * u.uses.length]? = some (.inst (rdIface u)) := by
    rw [List.getElem?_append_right (by simp [length_useTys])]; simp [length_useTys]
  rw [decCDeclsU_inst _ _ _ _ _ (wst Op N (useTys u.uses ++ [.inst (rdIface u)]) (u.uses.map instEs)
    (u.uses.map fun e => some e.I)) []]
  · simp [decCDeclsU, decIDeclU, decExternU, onBase_run, typeAt, StateT.run_bind, StateT.run_get,
      StateT.run_modify, g, wst]
  · simp only [wst, bst] at hN ⊢
    simp [decIDeclU, decDefTypeU, StateT.run_bind, hN, pushTy, onBase_run]

end

/-! ## The WAT normal form -/

theorem normCDs_append : ∀ (a b : List ComponentDecl),
    normComponentDecls (a ++ b) = normComponentDecls a ++ normComponentDecls b
  | [], _ => rfl
  | d :: a, b => by simp [normComponentDecls, normCDs_append a b]

theorem normIDs_append : ∀ (a b : List InstanceDecl),
    normInstanceDecls (a ++ b) = normInstanceDecls a ++ normInstanceDecls b
  | [], _ => rfl
  | d :: a, b => by simp [normInstanceDecls, normIDs_append a b]

theorem norm_useDecls : ∀ (k : Nat) (l : List UseT), normComponentDecls (useDecls k l) = useDecls k l
  | _, [] => rfl
  | k, e :: l => by
    simp [useDecls, normComponentDecls, normComponentDecl, normInstanceDecl, normDefType, normInstanceDecls,
      normName, norm_useDecls (k + 1) l]

theorem norm_useAliases : ∀ (k : Nat) (l : List UseT), normInstanceDecls (useAliases k l) = useAliases k l
  | _, [] => rfl
  | k, e :: l => by simp [useAliases, normInstanceDecls, normInstanceDecl, norm_useAliases (k + 1) l]

theorem norm_useExports : ∀ (k : Nat) (l : List UseT), normInstanceDecls (useExports k l) = useExports k l
  | _, [] => rfl
  | k, e :: l => by simp [useExports, normInstanceDecls, normInstanceDecl, normName, norm_useExports (k + 1) l]

theorem norm_resExports : ∀ rs : List String, normInstanceDecls (resExports rs) = resExports rs
  | [] => rfl
  | r :: rs => by simp [resExports, normInstanceDecls, normInstanceDecl, normName, norm_resExports rs]

theorem norm_parTys (nu : Nat) : ∀ ps : List (String × UPar),
    normInstanceDecls (ps.map fun p => .type (.val (p.2.def nu))) = ps.map fun p => .type (.val (p.2.def nu))
  | [] => rfl
  | p :: ps => by simp [normInstanceDecls, normInstanceDecl, normDefType, norm_parTys nu ps]

theorem norm_funcDecls (nu : Nat) : ∀ (c : Nat) (fs : List (String × List (String × UPar))),
    normInstanceDecls (funcDecls nu c fs) = funcDecls nu c fs
  | _, [] => rfl
  | c, (f, ps) :: fs => by
    simp only [funcDecls, normIDs_append, norm_parTys, norm_funcDecls nu (c + ps.length + 1) fs]
    simp [normInstanceDecls, normInstanceDecl, normDefType, normName]

theorem norm_ifaceDefU (id : String) (u : UIface) : normDefType (ifaceDefU id u) = ifaceDefU id u := by
  simp [ifaceDefU, normDefType, normCDs_append, norm_useDecls, normComponentDecls, normComponentDecl,
    normInstanceDecl, ifaceBody, normIDs_append, norm_useAliases, norm_useExports, norm_resExports,
    norm_funcDecls, normName]

/-! ## The package -/

/-- The scope of the package level. -/
def pst (Lt : List TInfo) : UScope := { base := { types := Lt.toArray } }

/-- The type export of the package for an interface. -/
def itemK (p : String × UIface) : String × Kind :=
  (p.1, .type (.comp (ifaceId p.1) (useImps p.2.uses) [(p.1, .inst (ifaceId p.1) (rdIface p.2))]))

theorem itemDecls_run : ∀ (k : Nat) (items : List (String × UIface)) (Lt : List TInfo) (es : Externs),
    (∀ p ∈ items, p.2.Ok) → Lt.length = 2 * k →
    ∃ Lt', (decCDeclsU (Wit.Project.itemDecls k (items.map fun p => (p.1, ifaceDefU p.1 p.2))) [] es).run (pst Lt) =
      .ok (([], es ++ items.map itemK), pst Lt')
  | _, [], Lt, es, _, _ => ⟨Lt, by simp [Wit.Project.itemDecls, decCDeclsU]⟩
  | k, (id, u) :: items, Lt, es, hok, ht => by
    have hu : u.Ok := hok (id, u) List.mem_cons_self
    obtain ⟨s', hw, hn⟩ := wrapper_run [Lt.toArray] [] id u hu
    have hN := inNestedU_run (u := pst Lt) (by exact hw)
    let K : TInfo := .comp (useImps u.uses) [(id, .inst (ifaceId id) (rdIface u))]
    obtain ⟨Lt', ih⟩ := itemDecls_run (k + 1) items (Lt ++ [K, K]) (es ++ [itemK (id, u)])
      (fun p hp => hok p (List.mem_cons_of_mem _ hp)) (by simp; omega)
    have g : (Lt ++ [K])[2 * k]? = some K := by
      rw [List.getElem?_append_right (by omega)]; simp [ht]
    refine ⟨Lt', ?_⟩
    rw [List.map_cons, Wit.Project.itemDecls, norm_ifaceDefU]
    rw [decCDeclsU_inst _ _ _ _ _ (pst (Lt ++ [K])) es]
    · rw [decCDeclsU_inst _ _ _ _ _ (pst (Lt ++ [K, K])) (es ++ [itemK (id, u)])]
      · simpa using ih
      · simp [decIDeclU, decExternU, onBase_run, typeAt, StateT.run_bind, StateT.run_get, pst, g, namedInfoU,
          isUsed, namedInfo, addNom, typeKindU, typeKind, pushTy, itemK, K]
    · simp only [ifaceDefU, pst] at hN ⊢
      simp [decIDeclU, decDefTypeU, StateT.run_bind, hN, pushTy, onBase_run, hn, K]

theorem unwrapU_wrap (x : Option String) (is : Externs) (id : String) (y : Option String) (es : Externs) :
    unwrapU (.comp x is [(id, .inst y es)]) = .inst (some id) es := by
  cases is <;> rfl

/-- **The package `decodePkgU` reads from the projected world of `usePkg items`.** -/
theorem pkgOfWorldU_usePkg (items : List (String × UIface)) (hok : ∀ p ∈ items, p.2.Ok) :
    pkgOfWorldU (Wit.Project.itemDecls 0 (items.map fun p => (p.1, ifaceDefU p.1 p.2))) =
      .ok (usePkgRd items, []) := by
  obtain ⟨Lt', h⟩ := itemDecls_run 0 items [] [] hok rfl
  have h' : (decCDeclsU (Wit.Project.itemDecls 0 (items.map fun p => (p.1, ifaceDefU p.1 p.2))) [] []).run {} =
      .ok (([], items.map itemK), pst Lt') := by
    simp only [List.nil_append] at h; exact h
  simp only [pkgOfWorldU, h', ok_bindE', pure_okE]
  simp [pkgWith, usePkgRd, itemK, unwrapU_wrap, pst, List.filter_map, List.filterMap_map, Function.comp_def]

end EncodeUse

end Silmaril.Wasm.Wac.Bridge
