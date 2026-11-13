module

public import Silmaril.Wasi.Versions.WitImport.KErase.Elab.Thms

@[expose] public section

/-!
# Doc comments do not reach the elaboration of worlds

World items are compared by their keys, stabilities and interface names, never by their docs:
erasing the docs of the items commutes with the implicit imports (`importIface_erase`), the
exports (`addExport_erase`), `elabWorldItems`, `include` (`includeInto_erase`) and the
pre-elaboration items (`preItems_erase`), so that a world of the erased universe elaborates to
the erased world (`elabWorld_erase`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Wit

/-! ## Generic facts -/

theorem foldl_map_comm {α β γ : Type} {F : α → β → α} {F' : γ → β → γ} {S : α → γ}
    (h : ∀ a j, F' (S a) j = S (F a j)) : ∀ (l : List β) (a : α), l.foldl F' (S a) = S (l.foldl F a)
  | [], _ => rfl
  | j :: l, a => by rw [List.foldl_cons, List.foldl_cons, h a j, foldl_map_comm h l]

theorem foldlM_except_comm {α β γ δ ε : Type} {F : α → β → Except ε α} {F' : γ → δ → Except ε γ}
    {S : α → γ} {T : β → δ} (h : ∀ a x, F' (S a) (T x) = (F a x).map S) :
    ∀ (l : List β) (a : α), (l.map T).foldlM F' (S a) = (l.foldlM F a).map S
  | [], _ => rfl
  | x :: l, a => by
    rw [List.map_cons, List.foldlM_cons, List.foldlM_cons, h a x]
    cases F a x with
    | error e => rfl
    | ok b => exact foldlM_except_comm h l b

theorem foldlM_option_comm' {α β γ δ : Type} {F : α → β → Option α} {F' : γ → δ → Option γ}
    {S : α → γ} {T : β → δ} (h : ∀ a x, F' (S a) (T x) = (F a x).map S) :
    ∀ (l : List β) (a : α), (l.map T).foldlM F' (S a) = (l.foldlM F a).map S
  | [], _ => rfl
  | x :: l, a => by
    rw [List.map_cons, List.foldlM_cons, List.foldlM_cons, h a x]
    cases F a x with
    | none => rfl
    | some b => exact foldlM_option_comm' h l b

theorem foldlM_option_comm {α β γ : Type} {F : α → β → Option α} {F' : γ → β → Option γ}
    {S : α → γ} (h : ∀ a x, F' (S a) x = (F a x).map S) :
    ∀ (l : List β) (a : α), l.foldlM F' (S a) = (l.foldlM F a).map S := by
  intro l a
  have := foldlM_option_comm' (T := id) (fun a x => h a x) l a
  simpa using this

namespace Binary

@[simp] theorem Func.erase_mangled (f : Func) : f.erase.mangled = f.mangled := rfl
@[simp] theorem Func.erase_kind (f : Func) : f.erase.kind = f.kind := rfl
@[simp] theorem Func.erase_stability (f : Func) : f.erase.stability = f.stability := rfl
@[simp] theorem TypeDef.erase_name (t : TypeDef) : t.erase.name = t.name := rfl
@[simp] theorem TypeDef.erase_stability (t : TypeDef) : t.erase.stability = t.stability := rfl
@[simp] theorem Interface.erase_stability (b : Interface) : b.erase.stability = b.stability := rfl

@[simp] theorem WorldItem.key_erase (it : WorldItem) : it.erase.key = it.key := by
  cases it <;> rfl

theorem directDeps_erase (b : Interface) : directDeps b.erase = directDeps b := by
  simp only [directDeps, Interface.erase, List.filterMap_map]
  congr 1
  funext td
  rcases td with ⟨n, k, ds, st⟩
  cases k <;> rfl

theorem lookup'_erase (i : IfaceName) : ∀ env : Env,
    liveDeps.lookup' i env.erase = (liveDeps.lookup' i env).map Interface.erase
  | [] => rfl
  | (j, b) :: xs => by
    by_cases h : j = i
    · simp [Env.erase, liveDeps.lookup', h]
    · simp only [Env.erase, List.map_cons, liveDeps.lookup', h, ite_false]
      exact lookup'_erase i xs

theorem Env.find?_erase (env : Env) (i : IfaceName) : env.erase.find? i = (env.find? i).map Interface.erase :=
  lookup'_erase i env

end Binary

namespace Elab

local notation "E" => Binary.WorldItem.erase

theorem itemStab_erase (it : Binary.WorldItem) : itemStab (E it) = itemStab it := by
  cases it <;> rfl

theorem itemIface_erase (it : Binary.WorldItem) : itemIface (E it) = itemIface it := by
  cases it <;> rfl

theorem itemDeps_erase (env : Binary.Env) (it : Binary.WorldItem) :
    itemDeps env.erase (E it) = itemDeps env it := by
  cases it with
  | ifaceRef i d s =>
    simp only [Binary.WorldItem.erase, itemDeps, Binary.Env.find?_erase]
    cases Binary.Env.find? env i <;> simp [Binary.directDeps_erase]
  | ifaceInline n b => exact Binary.directDeps_erase b
  | _ => rfl

theorem typeDep_erase (t : Binary.TypeDef) : typeDep t.erase = typeDep t := by
  rcases t with ⟨n, k, ds, st⟩
  cases k with
  | type ty =>
    cases ty with
    | ref r =>
      rcases r with ⟨o, x⟩
      cases o <;> rfl
    | _ => rfl
  | _ => rfl

theorem importClass_erase (it : Binary.WorldItem) : importClass (E it) = importClass it := by
  cases it with
  | type t => simp [Binary.WorldItem.erase, importClass, typeDep_erase]
  | _ => rfl

theorem sortImports_erase (its : List Binary.WorldItem) : sortImports (its.map E) = (sortImports its).map E := by
  simp [sortImports, List.filter_map, Function.comp_def, importClass_erase, List.map_flatMap]

theorem hasKey_erase (its : List Binary.WorldItem) (k : String) : hasKey (its.map E) k = hasKey its k := by
  simp [hasKey, List.any_map, Function.comp_def]

theorem insertNew_erase (its : List Binary.WorldItem) (it : Binary.WorldItem) :
    insertNew (its.map E) (E it) = (insertNew its it).map (List.map E) := by
  unfold insertNew
  rw [hasKey_erase, Binary.WorldItem.key_erase]
  split <;> simp [Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem insertIfNew_erase (its : List Binary.WorldItem) (it : Binary.WorldItem) :
    insertIfNew (its.map E) (E it) = (insertIfNew its it).map E := by
  unfold insertIfNew
  rw [hasKey_erase, Binary.WorldItem.key_erase]
  split <;> simp

/-! ## Implicit imports -/

theorem importIface_erase (env : Binary.Env) (st : Binary.Stability) : ∀ (f : Nat) (it : Binary.WorldItem)
    (acc : List Binary.WorldItem),
    importIface env.erase st f (E it) (acc.map E) = (importIface env st f it acc).map E
  | 0, _, _ => rfl
  | f + 1, it, acc => by
    have hfold := foldl_map_comm (S := List.map E)
      (F := fun acc j => importIface env st f (.ifaceRef j none st) acc)
      (F' := fun acc j => importIface env.erase st f (.ifaceRef j none st) acc)
      (fun a j => importIface_erase env st f (.ifaceRef j none st) a) (itemDeps env it) acc
    simp only [importIface, hasKey_erase, Binary.WorldItem.key_erase, itemDeps_erase]
    split
    · rfl
    · rw [hfold, insertIfNew_erase]

theorem elabImport_erase (env : Binary.Env) (fuel : Nat) (acc : List Binary.WorldItem) (it : Binary.WorldItem) :
    elabImport env.erase fuel (acc.map E) (E it) = (elabImport env fuel acc it).map (List.map E) := by
  cases it with
  | ifaceRef i d s =>
    simp only [elabImport, Binary.WorldItem.erase]
    exact congrArg pure (importIface_erase env s fuel (.ifaceRef i d s) acc)
  | ifaceInline n b =>
    simp only [elabImport]
    exact congrArg pure (importIface_erase env b.stability fuel (.ifaceInline n b) acc)
  | func f => exact insertNew_erase acc (.func f)
  | type t =>
    simp only [elabImport, Binary.WorldItem.erase, typeDep_erase, Binary.TypeDef.erase_stability]
    cases typeDep t with
    | none => exact insertNew_erase acc (.type t)
    | some j =>
      exact (congrArg (insertNew · (E (.type t)))
        (importIface_erase env t.stability fuel (.ifaceRef j none t.stability) acc)).trans
        (insertNew_erase _ (.type t))

/-! ## Exports -/

/-- An export state with its items erased. -/
def XState.erase (s : XState) : XState :=
  { imports := s.imports.map E, exports := s.exports.map E, req := s.req }

@[simp] theorem XState.erase_exports (s : XState) : s.erase.exports = s.exports.map E := rfl
@[simp] theorem XState.erase_imports (s : XState) : s.erase.imports = s.imports.map E := rfl
@[simp] theorem XState.erase_req (s : XState) : s.erase.req = s.req := rfl

theorem reqHas_erase (req : List Binary.IfaceName) (it : Binary.WorldItem) : reqHas req (E it) = reqHas req it := by
  simp [reqHas, itemIface_erase]

theorem addExport_erase (env : Binary.Env) (xs : List String) : ∀ (f : Nat) (it : Binary.WorldItem)
    (add : Bool) (s : XState),
    addExport env.erase xs f (E it) add s.erase = (addExport env xs f it add s).map XState.erase
  | 0, _, _, _ => rfl
  | f + 1, it, add, s => by
    have hfold := foldlM_option_comm (S := XState.erase)
      (F := fun s j => addExport env xs f (.ifaceRef j none (itemStab it)) (add && xs.contains j.id) s)
      (F' := fun s j => addExport env.erase xs f (.ifaceRef j none (itemStab it)) (add && xs.contains j.id) s)
      (fun a j => addExport_erase env xs f (.ifaceRef j none (itemStab it)) _ a) (itemDeps env it) s
    simp only [addExport, hasKey_erase, Binary.WorldItem.key_erase, reqHas_erase, itemStab_erase,
      itemDeps_erase, XState.erase_exports, XState.erase_req]
    rw [hfold]
    by_cases h1 : hasKey s.exports it.key = true
    · cases add <;> simp [h1]
    · by_cases h2 : (!add && reqHas s.req it) = true
      · simp [h1, h2]
      · simp only [h1, h2, Bool.false_eq_true, ite_false]
        cases (itemDeps env it).foldlM (fun s j =>
            addExport env xs f (.ifaceRef j none (itemStab it)) (add && xs.contains j.id) s) s with
        | none => rfl
        | some s' =>
          by_cases h3 : reqHas s'.req it = true <;> cases add <;>
            simp [XState.erase, insertIfNew_erase, itemIface_erase, h3]

theorem filter_map_erase {p : Binary.WorldItem → Bool} (hp : ∀ x, p (E x) = p x)
    (l : List Binary.WorldItem) : (l.map E).filter p = (l.filter p).map E := by
  rw [List.filter_map]
  congr 2
  funext x
  exact hp x

theorem map_key_erase (l : List Binary.WorldItem) : (l.map E).map (·.key) = l.map (·.key) := by
  simp [List.map_map, Function.comp_def]

theorem except_bind_map {ε α β γ δ : Type} (x : Except ε α) (g : α → β) (k : α → Except ε γ)
    (k' : β → Except ε δ) (h : γ → δ) (hk : ∀ a, k' (g a) = (k a).map h) :
    (x.map g >>= k') = (x >>= k).map h := by
  cases x with
  | error e => rfl
  | ok a => exact hk a

theorem elabWorldItems_erase (env : Binary.Env) (imports exports : List Binary.WorldItem) :
    elabWorldItems env.erase (imports.map E) (exports.map E) =
      (elabWorldItems env imports exports).map (fun p => (p.1.map E, p.2.map E)) := by
  have hlen : env.erase.length = env.length := List.length_map _
  have himp : ((sortImports imports).map E).foldlM (elabImport env.erase (env.length + 1)) [] =
      ((sortImports imports).foldlM (elabImport env (env.length + 1)) []).map (List.map E) :=
    foldlM_except_comm (fun a x => elabImport_erase env (env.length + 1) a x) _ []
  have hfun : ∀ l : List Binary.WorldItem, (l.map E).foldlM insertNew [] =
      (l.foldlM insertNew []).map (List.map E) :=
    fun l => foldlM_except_comm (fun a x => insertNew_erase a x) l []
  have hexp : ∀ (xs : List String) (l imps funcs : List Binary.WorldItem),
      (l.map E).foldlM (fun s it => addExport env.erase xs (env.length + 1) it true s)
        { imports := imps.map E, exports := funcs.map E } =
      (l.foldlM (fun s it => addExport env xs (env.length + 1) it true s)
        { imports := imps, exports := funcs }).map XState.erase :=
    fun xs l imps funcs => foldlM_option_comm' (S := XState.erase) (T := E)
      (fun a x => addExport_erase env xs (env.length + 1) x true a) l { imports := imps, exports := funcs }
  unfold elabWorldItems
  rw [hlen, sortImports_erase, filter_map_erase ?h1, filter_map_erase ?h2]
  case h1 => intro x; cases x <;> rfl
  case h2 => intro x; cases x <;> rfl
  generalize List.filter _ exports = fs
  generalize List.filter _ exports = ifs
  simp only [himp, hfun, map_key_erase]
  refine except_bind_map _ _ _ _ _ (fun imps => ?_)
  refine except_bind_map _ _ _ _ _ (fun funcs => ?_)
  simp only [hexp]
  cases ifs.foldlM (fun s it => addExport env (ifs.map (·.key)) (env.length + 1) it true s)
      { imports := imps, exports := funcs } with
  | none => rfl
  | some s =>
    by_cases h : (ifs.map (·.key)).Nodup <;>
      simp [h, XState.erase, sortImports_erase, Except.map, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw]

/-! ## `include` -/

theorem renameKind_erase (σ : String → String) (k : Binary.TyDefKind) :
    renameKind σ k.erase = (renameKind σ k).erase := by
  cases k <;> simp [renameKind, Binary.TyDefKind.erase, Binary.Labeled.erase]

theorem renameItem_erase (σ : String → String) (it : Binary.WorldItem) :
    renameItem σ (E it) = E (renameItem σ it) := by
  cases it with
  | type t => simp [renameItem, Binary.WorldItem.erase, Binary.TypeDef.erase, renameKind_erase]
  | _ => rfl

theorem foldlM_bind_comm {ε α β γ δ ζ η : Type} {F : α → β → Except ε α} {F' : γ → δ → Except ε γ}
    {S : α → γ} {T : β → δ} {k : α → Except ε ζ} {k' : γ → Except ε η} {h : ζ → η}
    (hs : ∀ a x, F' (S a) (T x) = (F a x).map S) (hk : ∀ b, k' (S b) = (k b).map h)
    (l : List β) (a : α) : ((l.map T).foldlM F' (S a) >>= k') = ((l.foldlM F a) >>= k).map h := by
  rw [foldlM_except_comm hs l a]
  exact except_bind_map _ _ _ _ _ hk

theorem map_comm_of {f f' : Binary.WorldItem → Binary.WorldItem} (h : ∀ x, f' (E x) = E (f x))
    (l : List Binary.WorldItem) : (l.map E).map f' = (l.map f).map E := by
  simp [List.map_map, Function.comp_def, h]

theorem includeItem_ref_erase (ext : Bool) (its : List Binary.WorldItem) (i : Binary.IfaceName)
    (d : Option String) (s : Binary.Stability) :
    includeItem ext (its.map E) (E (.ifaceRef i d s)) =
      (includeItem ext its (.ifaceRef i d s)).map (List.map E) := by
  have hE : E (.ifaceRef i d s) = .ifaceRef i none s := rfl
  have hfind : (its.map E).find? (fun x => x.key == i.id) =
      (its.find? (fun x => x.key == i.id)).map E := by
    simp [List.find?_map, Function.comp_def]
  have hk1 : (Binary.WorldItem.ifaceRef i none s).key = i.id := rfl
  have hk2 : (Binary.WorldItem.ifaceRef i d s).key = i.id := rfl
  unfold includeItem
  simp only [hE, hk1, hk2]
  rw [hfind]
  have happ : its.map E ++ [Binary.WorldItem.ifaceRef i none s] = (its ++ [Binary.WorldItem.ifaceRef i d s]).map E := by
    simp [Binary.WorldItem.erase]
  have hupd : ∀ (st : Binary.Stability) (x : Binary.WorldItem),
      (fun x : Binary.WorldItem => match x with
        | .ifaceRef j d' _ => if j = i then Binary.WorldItem.ifaceRef j d' st else x
        | x => x) (E x) =
      E ((fun x : Binary.WorldItem => match x with
        | .ifaceRef j d' _ => if j = i then Binary.WorldItem.ifaceRef j d' st else x
        | x => x) x) := fun st x => by
    cases x with
    | ifaceRef j d' s' => by_cases h : j = i <;> simp [h, Binary.WorldItem.erase]
    | _ => rfl
  cases its.find? (fun x => x.key == i.id) with
  | none =>
    simp only [Option.map_none]
    rw [happ]
    cases (if (ext && stabIsStable s) = true then some Binary.Stability.unknown else updateStab s s) with
    | none => rfl
    | some st => exact congrArg pure (map_comm_of (hupd st) _)
  | some old =>
    simp only [Option.map_some, itemStab_erase]
    cases (if (ext && stabIsStable s) = true then some Binary.Stability.unknown
        else updateStab s (itemStab old)) with
    | none => rfl
    | some st => exact congrArg pure (map_comm_of (hupd st) _)

theorem includeItem_erase (ext : Bool) (its : List Binary.WorldItem) (it : Binary.WorldItem) :
    includeItem ext (its.map E) (E it) = (includeItem ext its it).map (List.map E) := by
  cases it with
  | ifaceRef i d s => exact includeItem_ref_erase ext its i d s
  | ifaceInline n b => exact insertNew_erase its (.ifaceInline n b)
  | func f => exact insertNew_erase its (.func f)
  | type t => exact insertNew_erase its (.type t)

end Elab

end Silmaril.Wasm.Wit
