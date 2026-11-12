module

public import Silmaril.Wasm.Wac.Bridge.DecodeUse.Defs
public import Silmaril.Wasm.Wac.Bridge.Encode.Defs

/-!
# WAC bridge: the encoder writes no aliases

The encoder's scope computations (`Bridge.Encode`) emit type definitions, imports and
exports, and define instance and component types from the declarations of nested scopes;
they never emit an `alias`. `Pres m`: `m` keeps `naCs` of the declarations. Every encoder
computation of component types has it (`pres_externDesc`, `pres_typeBound`,
`pres_exportDecls`, `pres_importDecls`), so the declarations the encoder writes for a
package's imports and exports have no alias (`encode_naCs`). `naCs_norm`: the normal form
of names does not change `naCs`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef)
open Silmaril.Wasm.Component.Wat (normComponentDecls normInstanceDecls normDefType normInstanceDecl
  normComponentDecl)

namespace DecodeUse

theorem naCs_append : ∀ (l₁ l₂ : List ComponentDecl), naCs (l₁ ++ l₂) = (naCs l₁ && naCs l₂)
  | [], _ => by simp [naCs]
  | d :: l₁, l₂ => by simp [naCs, naCs_append l₁ l₂, Bool.and_assoc]

theorem naIs_instDecls : ∀ (ds : List ComponentDecl), naCs ds = true → naIs (instDecls ds) = true
  | [], _ => rfl
  | .import _ _ :: ds, h => by
    simp only [naCs, Bool.and_eq_true] at h
    simpa [instDecls] using naIs_instDecls ds h.2
  | .inst d :: ds, h => by
    simp only [naCs, naC, Bool.and_eq_true] at h
    have ih := naIs_instDecls ds h.2
    simp only [instDecls, List.filterMap_cons] at ih ⊢
    simp [naIs, h.1, ih]

/-! ## Computations that keep `naCs` -/

/-- `m` keeps `naCs` of the declarations. -/
def Pres {α : Type} (m : TM α) : Prop :=
  ∀ s a s', naCs s.decls = true → m.run s = .ok (a, s') → naCs s'.decls = true

theorem pres_pure {α : Type} (a : α) : Pres (pure a : TM α) := by
  intro s a' s' h hr; cases hr; exact h

theorem pres_throw {α : Type} (e : String) : Pres (throw e : TM α) := by
  intro s a s' h hr; cases hr

theorem pres_bind {α β : Type} {m : TM α} {f : α → TM β} (hm : Pres m) (hf : ∀ a, Pres (f a)) :
    Pres (m >>= f) := by
  intro s b s' h hr
  rw [StateT.run_bind] at hr
  cases h1 : m.run s with
  | error e => rw [h1] at hr; cases hr
  | ok p => rw [h1] at hr; exact hf p.1 p.2 b s' (hm s p.1 p.2 h h1) hr

theorem pres_get {α : Type} {f : Scope → TM α} (hf : ∀ σ, Pres (f σ)) : Pres (get >>= f) := by
  intro s a s' h hr
  exact hf s s a s' h hr

theorem pres_modify {f : Scope → Scope} (hf : ∀ s, naCs s.decls = true → naCs (f s).decls = true) :
    Pres (modify f) := by
  intro s a s' h hr
  cases hr
  exact hf s h

theorem pres_defTy {d : DefType} (hd : naD d = true) : Pres (defTy d) := by
  intro s a s' h hr
  cases hr
  simp [naCs_append, h, naCs, naC, naI, hd]

theorem pres_namedTy (n : String) : Pres (namedTy n) := by
  unfold namedTy
  refine pres_get fun σ => ?_
  split
  · exact pres_pure _
  · exact pres_throw _

theorem pres_defVal (d : DefValType) : Pres (defVal d) := by
  unfold defVal
  refine pres_get fun σ => ?_
  split
  · exact pres_pure _
  · exact pres_bind (pres_defTy rfl) fun _ => pres_bind (pres_modify fun _ h => h) fun _ => pres_pure _

theorem pres_handle (o : Bool) (i : Nat) : Pres (handle o i) := by
  unfold handle
  refine pres_get fun σ => ?_
  split
  · exact pres_pure _
  · exact pres_bind (pres_defTy rfl) fun _ => pres_bind (pres_modify fun _ h => h) fun _ => pres_pure _

mutual
theorem pres_valTy : ∀ t : Silmaril.Wasm.Wit.Binary.Ty, Pres (valTy t)
  | .prim _ => pres_pure _
  | .ref r => by
    rw [valTy]
    refine pres_bind (pres_namedTy _) fun i => pres_get fun σ => ?_
    split
    · exact pres_handle _ _
    · exact pres_pure _
  | .list t | .option t | .fixedList t _ => pres_bind (pres_valTy t) fun _ => pres_defVal _
  | .map k v => pres_bind (pres_valTy k) fun _ => pres_bind (pres_valTy v) fun _ => pres_defVal _
  | .result a b => pres_bind (pres_valTyOpt a) fun _ => pres_bind (pres_valTyOpt b) fun _ => pres_defVal _
  | .tuple ts => pres_bind (pres_valTys ts) fun _ => pres_defVal _
  | .own _ | .borrow _ => pres_bind (pres_namedTy _) fun _ => pres_handle _ _
  | .future a | .stream a => pres_bind (pres_valTyOpt a) fun _ => pres_defVal _
theorem pres_valTyOpt : ∀ a : Option Silmaril.Wasm.Wit.Binary.Ty, Pres (valTyOpt a)
  | none => pres_pure _
  | some t => pres_bind (pres_valTy t) fun _ => pres_pure _
theorem pres_valTys : ∀ ts : List Silmaril.Wasm.Wit.Binary.Ty, Pres (valTys ts)
  | [] => pres_pure _
  | t :: ts => pres_bind (pres_valTy t) fun _ => pres_bind (pres_valTys ts) fun _ => pres_pure _
end

theorem pres_mapM {α β : Type} {f : α → TM β} (hf : ∀ a, Pres (f a)) : ∀ l : List α, Pres (l.mapM f)
  | [] => pres_pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact pres_bind (hf a) fun _ => pres_bind (pres_mapM hf l) fun _ => pres_pure _

theorem pres_nominalTy (d : Nominal) : Pres (nominalTy d) := by
  cases d with
  | record fs =>
    exact pres_bind (pres_mapM (fun (f : String × Silmaril.Wasm.Wit.Binary.Ty) => pres_bind (pres_valTy f.2) fun _ => pres_pure _) fs)
      fun _ => pres_defTy rfl
  | variant cs =>
    exact pres_bind (pres_mapM (fun (c : String × Option Silmaril.Wasm.Wit.Binary.Ty) => pres_bind (pres_valTyOpt c.2) fun _ =>
      pres_pure _) cs) fun _ => pres_defTy rfl
  | enum _ | flags _ => exact pres_defTy rfl

theorem pres_freshVal (t : Silmaril.Wasm.Wit.Binary.Ty) : Pres (freshVal t) := by
  have hd : ∀ d : DefValType, Pres (do pure (some (← defTy (.val d))) : TM (Option Nat)) :=
    fun _ => pres_bind (pres_defTy rfl) fun _ => pres_pure _
  cases t with
  | list t | option t | fixedList t _ => exact pres_bind (pres_valTy t) fun _ => hd _
  | map k v => exact pres_bind (pres_valTy k) fun _ => pres_bind (pres_valTy v) fun _ => hd _
  | result a b => exact pres_bind (pres_valTyOpt a) fun _ => pres_bind (pres_valTyOpt b) fun _ => hd _
  | tuple ts => exact pres_bind (pres_valTys ts) fun _ => hd _
  | future a | stream a => exact pres_bind (pres_valTyOpt a) fun _ => hd _
  | prim _ | ref _ | own _ | borrow _ => exact pres_pure _

theorem pres_paramTys : ∀ ps : List (String × Silmaril.Wasm.Wit.Binary.Ty), Pres (paramTys ps)
  | [] => pres_pure _
  | (_, t) :: ps => pres_bind (pres_valTy t) fun _ => pres_bind (pres_paramTys ps) fun _ => pres_pure _

theorem pres_funcTy (s : Sig) : Pres (funcTy s) := by
  unfold funcTy
  refine pres_get fun σ => pres_get fun σ' => ?_
  split
  · exact pres_pure _
  · exact pres_bind (pres_paramTys _) fun _ => pres_bind (pres_valTyOpt _) fun _ =>
      pres_bind (pres_defTy rfl) fun _ => pres_bind (pres_modify fun _ h => h) fun _ => pres_pure _

theorem pres_shared (k : Kind) {m : TM Nat} (hm : Pres m) : Pres (shared k m) := by
  unfold shared
  refine pres_get fun σ => pres_get fun σ' => ?_
  split
  · exact pres_pure _
  · exact pres_bind hm fun _ => pres_bind (pres_modify fun _ h => h) fun _ => pres_pure _

theorem pure_bindE {ε α β : Type} (a : α) (f : α → Except ε β) : (pure a >>= f) = f a := rfl

theorem ok_bindE {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem nested_ok {b : Bool} {m : TM Unit} {s s' : Scope} {ds : List ComponentDecl}
    (h : (nested b m).run s = .ok (ds, s')) :
    s' = s ∧ ∃ σ, m.run { nom := s.nom, share := b } = .ok ((), σ) ∧ ds = σ.decls := by
  unfold nested at h
  rw [StateT.run_bind, StateT.run_get] at h
  cases h1 : m.run { nom := s.nom, share := b } with
  | error e => simp only [pure_bindE, h1] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, σ⟩ := p
    simp only [pure_bindE, h1, StateT.run_pure] at h
    cases h
    exact ⟨rfl, σ, rfl, rfl⟩

/-- A computation on the declarations of a nested scope. -/
theorem pres_nested {β : Type} {b : Bool} {m : TM Unit} (hm : Pres m) {g : List ComponentDecl → TM β}
    (hg : ∀ ds, naCs ds = true → Pres (g ds)) : Pres (nested b m >>= g) := by
  intro s a s' h hr
  rw [StateT.run_bind] at hr
  cases h1 : (nested b m).run s with
  | error e => rw [h1] at hr; cases hr
  | ok p =>
    obtain ⟨ds, s1⟩ := p
    rw [h1, ok_bindE] at hr
    obtain ⟨e, σ, hσ, hds⟩ := nested_ok h1
    rw [e] at hr
    exact hg ds (hds ▸ hm _ _ _ rfl hσ) s a s' h hr

theorem pres_declared (n : String) (d : ExternDesc) : Pres (declared n d) := by
  unfold declared
  split
  · exact pres_modify fun _ h => h
  · exact pres_pure _

theorem pres_emit {c : ComponentDecl} (hc : naC c = true) :
    Pres (modify fun s : Scope => { s with decls := s.decls ++ [c] }) :=
  pres_modify fun s h => by simp [naCs_append, h, naCs, hc]

mutual
theorem pres_externDesc : ∀ k : Kind, Pres (externDesc k)
  | .func s => pres_bind (pres_funcTy s) fun _ => pres_pure _
  | .value t => pres_bind (pres_valTy t) fun _ => pres_pure _
  | .resource _ => pres_pure _
  | .type k => pres_typeBound k
  | .inst _ es => pres_bind (pres_shared _ (pres_nested (pres_exportDecls es) fun ds h =>
      pres_defTy (naIs_instDecls ds h))) fun _ => pres_pure _
  | .comp _ is es => pres_bind (pres_shared _ (pres_nested
      (pres_bind (pres_importDecls is) fun _ => pres_exportDecls es) fun _ h => pres_defTy h)) fun _ => pres_pure _
theorem pres_typeBound : ∀ k : Kind, Pres (typeBound k)
  | .resource _ => pres_pure _
  | .value t => by
    rw [typeBound]
    refine pres_get fun σ => ?_
    split
    · exact pres_bind (pres_namedTy _) fun _ => pres_pure _
    · split
      · exact pres_bind (pres_nominalTy _) fun _ => pres_pure _
      · exact pres_bind (pres_namedTy _) fun _ => pres_pure _
    · refine pres_bind (pres_freshVal _) fun o => ?_
      split
      · exact pres_pure _
      · refine pres_bind (pres_valTy _) fun v => ?_
        split
        · exact pres_pure _
        · exact pres_bind (pres_defTy rfl) fun _ => pres_pure _
  | .func s => pres_bind (pres_funcTy s) fun _ => pres_pure _
  | .inst _ es => pres_nested (pres_exportDecls es) fun ds h =>
      pres_bind (pres_defTy (naIs_instDecls ds h)) fun _ => pres_pure _
  | .comp _ is es => pres_nested (pres_bind (pres_importDecls is) fun _ => pres_exportDecls es)
      fun _ h => pres_bind (pres_defTy h) fun _ => pres_pure _
  | .type _ => pres_throw _
theorem pres_exportDecls : ∀ es : Externs, Pres (exportDecls es)
  | [] => pres_pure _
  | (_, k) :: es => pres_bind (pres_externDesc k) fun _ => pres_bind (pres_emit rfl) fun _ =>
      pres_bind (pres_declared _ _) fun _ => pres_exportDecls es
theorem pres_importDecls : ∀ es : Externs, Pres (importDecls es)
  | [] => pres_pure _
  | (_, k) :: es => pres_bind (pres_externDesc k) fun _ => pres_bind (pres_emit rfl) fun _ =>
      pres_bind (pres_declared _ _) fun _ => pres_importDecls es
end

/-- **The declarations the encoder writes for a package's imports and exports have no
alias.** -/
theorem encode_naCs {is es : Externs} {s σ : Scope} (hs : s.decls = [])
    (h : ((do importDecls is; exportDecls es : TM Unit)).run s = .ok ((), σ)) : naCs σ.decls = true :=
  pres_bind (pres_importDecls is) (fun _ => pres_exportDecls es) s () σ (by rw [hs]; rfl) h

/-! ## The normal form of names -/

mutual
theorem naD_norm : ∀ t : DefType, naD (normDefType t) = naD t
  | .val _ | .func _ | .resource _ _ => rfl
  | .component ds => by simp only [normDefType, naD, naCs_norm ds]
  | .instance ds => by simp only [normDefType, naD, naIs_norm ds]
theorem naI_norm : ∀ d : InstanceDecl, naI (normInstanceDecl d) = naI d
  | .coreType _ | .alias _ | .export _ _ => rfl
  | .type t => by simp only [normInstanceDecl, naI, naD_norm t]
theorem naIs_norm : ∀ ds : List InstanceDecl, naIs (normInstanceDecls ds) = naIs ds
  | [] => rfl
  | d :: ds => by simp only [normInstanceDecls, naIs, naI_norm d, naIs_norm ds]
theorem naCs_norm : ∀ ds : List ComponentDecl, naCs (normComponentDecls ds) = naCs ds
  | [] => rfl
  | .import _ _ :: ds => by simp only [normComponentDecls, normComponentDecl, naCs, naC, naCs_norm ds]
  | .inst d :: ds => by simp only [normComponentDecls, normComponentDecl, naCs, naC, naI_norm d, naCs_norm ds]
end

end DecodeUse

end Silmaril.Wasm.Wac.Bridge
