module

public import Silmaril.Wasm.Wac.Bridge.DecodeUse.Defs

/-!
# WAC bridge: `decodePkgU` agrees with `decodePkg` on declarations without aliases

The two decoders differ only at aliases (`decAliasU`), at type items and handles of used
types (`isUsed`), and in recording the interfaces of instances (`UScope.ids`). Used types
enter the type index space only through aliases, so on declarations without aliases
(`naCs`) the scopes of `decodePkg` contain none (`Good`), and `decodePkgU` computes what
`decodePkg` computes, on the base scope.

* `Spec m P`: `m` does not change the scope and its result satisfies `P`;
* `GP m`: `m` keeps `Good`;
* `SimP P mU m`: from a `Good` scope, when `m` succeeds `mU` succeeds with the same result
  and base scope, and the result satisfies `P`;
* `sim_cDecls`: the declaration-level simulation, by mutual structural recursion.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner IfaceName)

namespace DecodeUse

/-! ## Monadic plumbing -/

theorem throw_runD {α : Type} (e : String) (δ : DScope) : (throw e : DM α).run δ = .error e := rfl

theorem ok_bindE {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem pure_bindE {ε α β : Type} (a : α) (f : α → Except ε β) : (pure a >>= f) = f a := rfl

theorem throw_runU {α : Type} (e : String) (u : UScope) : (throw e : UM α).run u = .error e := rfl

theorem onBase_run {α : Type} (m : DM α) (u : UScope) : (onBase m).run u =
    match m.run u.base with
    | .ok (a, b) => .ok (a, { u with base := b })
    | .error e => .error e := rfl

theorem bind_okD {α β : Type} {m : DM α} {f : α → DM β} {δ : DScope} {r : β × DScope}
    (h : (m >>= f).run δ = .ok r) : ∃ a δ1, m.run δ = .ok (a, δ1) ∧ (f a).run δ1 = .ok r := by
  rw [StateT.run_bind] at h
  cases hm : m.run δ with
  | error e => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem bind_runU {α β : Type} {m : UM α} {f : α → UM β} {u u1 : UScope} {a : α}
    (h : m.run u = .ok (a, u1)) : (m >>= f).run u = (f a).run u1 := by
  rw [StateT.run_bind, h]; rfl

/-! ## The invariant: no used types in the type index space -/

/-- No type index of the scope is a used type. -/
def Good (δ : DScope) : Prop := ∀ x ∈ δ.types, isUsed x = false

theorem good_empty (δ : DScope) (h : δ.types = #[]) : Good δ := by
  intro x hx; rw [h] at hx; cases hx; contradiction

theorem good_push {δ : DScope} (hg : Good δ) {x : TInfo} (hx : isUsed x = false) :
    Good { δ with types := δ.types.push x } := by
  intro y hy
  rcases Array.mem_push.mp hy with h | h
  · exact hg y h
  · rw [h]; exact hx

theorem namedInfo_good (n : String) (t : TInfo) : isUsed (namedInfo n t) = false := by
  cases t <;> rfl

theorem usedRes_none {t : TInfo} (h : isUsed t = false) : usedRes t = none := by
  unfold isUsed at h; unfold usedRes; split <;> simp_all

theorem namedInfoU_eq (n : String) {t : TInfo} (h : isUsed t = false) : namedInfoU n t = namedInfo n t := by
  simp [namedInfoU, h]

theorem typeKindU_eq (n : String) {t : TInfo} (h : isUsed t = false) : typeKindU n t = typeKind n t := by
  simp [typeKindU, h]

/-! ## Read-only computations with a postcondition -/

/-- `m` does not change the scope, and its result satisfies `P`. -/
def Spec {α : Type} (m : DM α) (P : α → Prop) : Prop :=
  ∀ δ a b, m.run δ = .ok (a, b) → b = δ ∧ P a

theorem spec_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : Spec (pure a : DM α) P := by
  intro δ a' b hr; cases hr; exact ⟨rfl, h⟩

theorem spec_throw {α : Type} {P : α → Prop} (e : String) : Spec (throw e : DM α) P := by
  intro δ a b hr; cases hr

theorem spec_bind {α β : Type} {m : DM α} {f : α → DM β} {Q : α → Prop} {P : β → Prop} (hm : Spec m Q)
    (hf : ∀ a, Q a → Spec (f a) P) : Spec (m >>= f) P := by
  intro δ c b hr
  obtain ⟨a, δ1, h1, h2⟩ := bind_okD hr
  obtain ⟨e1, hq⟩ := hm δ a δ1 h1
  rw [e1] at h2
  exact hf a hq δ c b h2

theorem spec_mono {α : Type} {m : DM α} {P Q : α → Prop} (h : Spec m P) (hpq : ∀ a, P a → Q a) :
    Spec m Q := by
  intro δ a b hr
  exact (h δ a b hr).imp_right (hpq a)

theorem spec_typeAt (i : Nat) : Spec (typeAt i) (fun _ => True) := by
  intro δ a b hr
  unfold typeAt at hr
  rw [StateT.run_bind] at hr
  cases hx : δ.types[i]? <;> simp [hx, StateT.run_get] at hr
  · cases hr
  · cases hr; exact ⟨rfl, trivial⟩

theorem typeAt_ok {i : Nat} {δ b : DScope} {t : TInfo} (h : (typeAt i).run δ = .ok (t, b)) :
    b = δ ∧ δ.types[i]? = some t := by
  unfold typeAt at h
  rw [StateT.run_bind] at h
  cases hx : δ.types[i]? <;> simp [hx, StateT.run_get] at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

theorem typeAt_of {i : Nat} {δ : DScope} {t : TInfo} (h : δ.types[i]? = some t) :
    (typeAt i).run δ = .ok (t, δ) := by
  unfold typeAt; rw [StateT.run_bind]; simp [h, StateT.run_get]; rfl

theorem spec_mapM {α β : Type} {f : α → DM β} (hf : ∀ a, Spec (f a) (fun _ => True)) :
    ∀ l : List α, Spec (l.mapM f) (fun _ => True)
  | [] => spec_pure trivial
  | a :: l => by
    rw [List.mapM_cons]
    exact spec_bind (hf a) fun _ _ => spec_bind (spec_mapM hf l) fun _ _ => spec_pure trivial

theorem spec_decVal (v : ValType) : Spec (decVal v) (fun _ => True) := by
  cases v with
  | prim p => exact spec_pure trivial
  | idx i =>
    refine spec_bind (spec_typeAt i) fun t _ => ?_
    cases t <;> dsimp only <;> first | exact spec_pure trivial | exact spec_throw _

theorem spec_decValOpt (v : Option ValType) : Spec (decValOpt v) (fun _ => True) := by
  cases v with
  | none => exact spec_pure trivial
  | some v => exact spec_bind (spec_decVal v) fun _ _ => spec_pure trivial

theorem spec_decFunc (f : FuncType) : Spec (decFunc f) (fun _ => True) :=
  spec_bind (spec_mapM (fun (p : String × ValType) => spec_bind (spec_decVal p.2) fun _ _ => spec_pure trivial) _) fun _ _ =>
    spec_bind (spec_decValOpt _) fun _ _ => spec_pure trivial

theorem spec_resAt (i : Nat) : Spec (resAt i) (fun r => r.owner = .local) := by
  refine spec_bind (spec_typeAt i) fun t _ => ?_
  cases t <;> dsimp only <;> first | exact spec_pure rfl | exact spec_throw _

theorem spec_decDefVal_own (i : Nat) : Spec (decDefVal (.own i)) (fun t => isUsed t = false) := by
  refine spec_bind (spec_typeAt i) fun t _ => ?_
  cases t
  case resAlias n r => exact spec_pure rfl
  all_goals
    refine spec_bind (spec_resAt i) fun r hr => spec_pure ?_
    obtain ⟨o, n⟩ := r
    cases hr
    rfl

/-- The results of `decDefVal` are not used types. -/
theorem spec_decDefVal (d : DefValType) : Spec (decDefVal d) (fun t => isUsed t = false) := by
  have hv : ∀ (v : ValType) (g : Ty → TInfo), (∀ t, isUsed (g t) = false) →
      Spec (do pure (g (← decVal v)) : DM TInfo) (fun t => isUsed t = false) :=
    fun v g hg => spec_bind (spec_decVal v) fun t _ => spec_pure (hg t)
  have ho : ∀ (v : Option ValType) (g : Option Ty → TInfo), (∀ t, isUsed (g t) = false) →
      Spec (do pure (g (← decValOpt v)) : DM TInfo) (fun t => isUsed t = false) :=
    fun v g hg => spec_bind (spec_decValOpt v) fun t _ => spec_pure (hg t)
  cases d with
  | prim p => exact spec_pure rfl
  | list t => exact hv t _ fun _ => rfl
  | fixedList t n => exact hv t _ fun _ => rfl
  | option t => exact hv t _ fun _ => rfl
  | future t => exact ho t _ fun _ => rfl
  | stream t => exact ho t _ fun _ => rfl
  | borrow i => exact spec_bind (spec_resAt i) fun _ _ => spec_pure rfl
  | enum ls => exact spec_pure rfl
  | flags ls => exact spec_pure rfl
  | map k v => exact spec_bind (spec_decVal k) fun _ _ => hv v _ fun _ => rfl
  | result a b => exact spec_bind (spec_decValOpt a) fun _ _ => ho b _ fun _ => rfl
  | tuple ts => exact spec_bind (spec_mapM spec_decVal ts) fun _ _ => spec_pure rfl
  | record fs =>
    exact spec_bind (spec_mapM (fun f => spec_bind (spec_decVal f.2) fun _ _ => spec_pure trivial) fs)
      fun _ _ => spec_pure rfl
  | variant cs =>
    exact spec_bind (spec_mapM (fun c => spec_bind (spec_decValOpt c.2) fun _ _ => spec_pure trivial) cs)
      fun _ _ => spec_pure rfl
  | own i => exact spec_decDefVal_own i

/-! ## Computations that keep the invariant -/

/-- `m` keeps `Good`. -/
def GP {α : Type} (m : DM α) : Prop := ∀ δ a b, Good δ → m.run δ = .ok (a, b) → Good b

theorem gp_of_spec {α : Type} {m : DM α} {P : α → Prop} (h : Spec m P) : GP m := by
  intro δ a b hg hr
  rw [(h δ a b hr).1]; exact hg

theorem gp_pure {α : Type} {a : α} : GP (pure a : DM α) := by
  intro δ a' b hg hr; cases hr; exact hg

theorem gp_throw {α : Type} (e : String) : GP (throw e : DM α) := by
  intro δ a b hg hr; cases hr

theorem gp_bind {α β : Type} {m : DM α} {f : α → DM β} (hm : GP m) (hf : ∀ a, GP (f a)) : GP (m >>= f) := by
  intro δ c b hg hr
  obtain ⟨a, δ1, h1, h2⟩ := bind_okD hr
  exact hf a δ1 c b (hm δ a δ1 hg h1) h2

theorem gp_pushTy {x : TInfo} (hx : isUsed x = false) : GP (pushTy x) := by
  intro δ a b hg hr
  cases hr
  exact good_push hg hx

theorem gp_addNom (n : String) (t : TInfo) : GP (addNom n t) := by
  intro δ a b hg hr
  unfold addNom at hr
  split at hr <;> (cases hr; exact hg)

/-- `decExtern` keeps `Good` (its type items push `namedInfo`, never a used type). -/
theorem gp_decExtern (n : String) (d : ExternDesc) : GP (decExtern n d) := by
  cases d with
  | func i =>
    exact gp_bind (gp_of_spec (spec_typeAt i)) fun t => by
      cases t <;> dsimp only <;> first | exact gp_throw _ | exact gp_pure
  | component i =>
    exact gp_bind (gp_of_spec (spec_typeAt i)) fun t => by
      cases t <;> dsimp only <;> first | exact gp_throw _ | exact gp_pure
  | «instance» i =>
    refine gp_bind (gp_of_spec (spec_typeAt i)) fun t => ?_
    cases t
    case inst es =>
      intro δ a b hg hr
      cases hr
      exact hg
    all_goals exact gp_throw _
  | type b =>
    cases b with
    | eq i =>
      exact gp_bind (gp_of_spec (spec_typeAt i)) fun t => gp_bind (gp_pushTy (namedInfo_good n t)) fun _ =>
        gp_bind (gp_addNom n t) fun _ => gp_pure
    | subResource => exact gp_bind (gp_pushTy rfl) fun _ => gp_pure
  | value b =>
    cases b with
    | type v => exact gp_bind (gp_of_spec (spec_decVal v)) fun _ => gp_pure
    | eq _ => exact gp_throw _
  | coreModule _ => exact gp_throw _

/-! ## The simulation -/

/-- From a `Good` scope, when `m` succeeds, `mU` succeeds with the same result and base
scope (and any interfaces), the base scope is `Good`, and the result satisfies `P`. -/
def SimP {α : Type} (P : α → Prop) (mU : UM α) (m : DM α) : Prop :=
  ∀ (u : UScope) a b, Good u.base → m.run u.base = .ok (a, b) →
    P a ∧ Good b ∧ ∃ ids, mU.run u = .ok (a, { base := b, ids })

abbrev Sim {α : Type} (mU : UM α) (m : DM α) : Prop := SimP (fun _ => True) mU m

theorem simP_onBase {α : Type} {m : DM α} {P : α → Prop} (hg : GP m)
    (hp : ∀ δ a b, m.run δ = .ok (a, b) → P a) : SimP P (onBase m) m := by
  intro u a b hu hr
  refine ⟨hp _ a b hr, hg _ a b hu hr, u.ids, ?_⟩
  rw [onBase_run, hr]

theorem sim_onBase {α : Type} {m : DM α} (hg : GP m) : Sim (onBase m) m :=
  simP_onBase hg fun _ _ _ _ => trivial

theorem simP_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : SimP P (pure a) (pure a) := by
  intro u a' b hu hr
  cases hr
  exact ⟨h, hu, u.ids, rfl⟩

theorem simP_throw {α : Type} {P : α → Prop} (mU : UM α) (e : String) : SimP P mU (throw e) := by
  intro u a b hu hr; cases hr

theorem simP_bind {α β : Type} {Q : α → Prop} {P : β → Prop} {mU : UM α} {m : DM α} {fU : α → UM β}
    {f : α → DM β} (hm : SimP Q mU m) (hf : ∀ a, Q a → SimP P (fU a) (f a)) : SimP P (mU >>= fU) (m >>= f) := by
  intro u c b hu hr
  obtain ⟨a, δ1, h1, h2⟩ := bind_okD hr
  obtain ⟨hq, hg1, ids1, hu1⟩ := hm u a δ1 hu h1
  obtain ⟨hp, hg2, ids2, hu2⟩ := hf a hq { base := δ1, ids := ids1 } c b hg1 h2
  exact ⟨hp, hg2, ids2, by rw [bind_runU hu1]; exact hu2⟩

theorem simP_mono {α : Type} {P Q : α → Prop} {mU : UM α} {m : DM α} (h : SimP P mU m)
    (hpq : ∀ a, P a → Q a) : SimP Q mU m := by
  intro u a b hu hr
  obtain ⟨hp, rest⟩ := h u a b hu hr
  exact ⟨hpq a hp, rest⟩

/-- The type at an index of a `Good` scope is not a used type. -/
theorem simP_typeAt (i : Nat) : SimP (fun t => isUsed t = false) (onBase (typeAt i)) (typeAt i) := by
  intro u a b hu hr
  obtain ⟨e, hx⟩ := typeAt_ok hr
  subst e
  refine ⟨hu a (Array.mem_of_getElem? hx), hu, u.ids, ?_⟩
  rw [onBase_run, hr]

theorem sim_inNested {α : Type} {mU : UM α} {m : DM α} (h : Sim mU m) : Sim (inNestedU mU) (inNested m) := by
  intro u a b hu hr
  unfold inNested at hr
  rw [StateT.run_bind, StateT.run_get] at hr
  cases hm : m.run { outer := u.base.types :: u.base.outer, nom := u.base.nom } with
  | error e => simp only [pure_bindE, hm] at hr; cases hr
  | ok p =>
    obtain ⟨a', s'⟩ := p
    simp only [pure_bindE, hm, StateT.run_bind, StateT.run_set, StateT.run_pure] at hr
    cases hr
    obtain ⟨-, -, ids, hU⟩ := h { base := { outer := u.base.types :: u.base.outer, nom := u.base.nom } } a s'
      (good_empty _ rfl) hm
    refine ⟨trivial, hu, u.ids, ?_⟩
    unfold inNestedU
    simp only [StateT.run_bind, StateT.run_get, pure_bindE, hU, StateT.run_set, StateT.run_pure]
    rfl

/-- `own`/`borrow` of an index that is not a used resource. -/
theorem simP_handle {i : Nat} {g : TyRef → TInfo} :
    SimP (fun t => isUsed t = false)
      (do match usedRes (← onBase (typeAt i)) with
        | some r => pure (g r)
        | none => onBase (decDefVal (.own i))) (decDefVal (.own i)) := by
  intro u a b hu hr
  obtain ⟨t, δ1, h1, -⟩ := bind_okD (show (typeAt i >>= _).run u.base = _ from hr)
  obtain ⟨e, hx⟩ := typeAt_ok h1
  subst e
  have hnu : usedRes t = none := usedRes_none (hu t (Array.mem_of_getElem? hx))
  obtain ⟨e, hp⟩ := spec_decDefVal (.own i) _ a b hr
  subst e
  refine ⟨hp, hu, u.ids, ?_⟩
  rw [bind_runU (by rw [onBase_run, h1] : (onBase (typeAt i)).run u = .ok (t, u)), hnu, onBase_run, hr]

theorem simP_handleB {i : Nat} {g : TyRef → TInfo} :
    SimP (fun t => isUsed t = false)
      (do match usedRes (← onBase (typeAt i)) with
        | some r => pure (g r)
        | none => onBase (decDefVal (.borrow i))) (decDefVal (.borrow i)) := by
  intro u a b hu hr
  obtain ⟨t, δ1, h1, -⟩ := bind_okD (show (resAt i >>= _).run u.base = _ from hr)
  obtain ⟨t', δ2, h2, -⟩ := bind_okD (show (typeAt i >>= _).run u.base = _ from h1)
  obtain ⟨e, hx⟩ := typeAt_ok h2
  subst e
  have hnu : usedRes t' = none := usedRes_none (hu t' (Array.mem_of_getElem? hx))
  obtain ⟨e, hp⟩ := spec_decDefVal (.borrow i) _ a b hr
  subst e
  refine ⟨hp, hu, u.ids, ?_⟩
  rw [bind_runU (by rw [onBase_run, h2] : (onBase (typeAt i)).run u = .ok (t', u)), hnu, onBase_run, hr]

theorem simP_defVal (d : DefValType) : SimP (fun t => isUsed t = false) (decDefValU d) (decDefVal d) := by
  have hb : SimP (fun t => isUsed t = false) (onBase (decDefVal d)) (decDefVal d) :=
    simP_onBase (gp_of_spec (spec_decDefVal d)) fun δ a b hr => (spec_decDefVal d δ a b hr).2
  cases d
  case own i => exact simP_handle
  case borrow i => exact simP_handleB
  all_goals exact hb

theorem sim_extern (n : String) (d : ExternDesc) : Sim (decExternU n d) (decExtern n d) := by
  cases d
  case «instance» i =>
    refine simP_bind (simP_typeAt i) fun t _ => ?_
    cases t
    case inst es =>
      intro u a b hu hr
      cases hr
      exact ⟨trivial, hu, u.ids.push (ifaceOf n), rfl⟩
    all_goals exact simP_throw _ _
  case type b =>
    cases b
    case eq i =>
      refine simP_bind (simP_typeAt i) fun t ht => ?_
      rw [namedInfoU_eq n ht, typeKindU_eq n ht]
      exact simP_bind (sim_onBase (gp_pushTy (namedInfo_good n t))) fun _ _ =>
        simP_bind (sim_onBase (gp_addNom n t)) fun _ _ => simP_pure trivial
    case subResource => exact sim_onBase (gp_decExtern n _)
  all_goals exact sim_onBase (gp_decExtern n _)

mutual
theorem sim_defType : ∀ d : DefType, naD d = true →
    SimP (fun t => isUsed t = false) (decDefTypeU d) (decDefType d)
  | .val d, _ => simP_defVal d
  | .func f, _ => simP_bind (sim_onBase (gp_of_spec (spec_decFunc f))) fun _ _ => simP_pure rfl
  | .instance ds, h => simP_bind (sim_inNested (sim_iDecls ds [] h)) fun _ _ => simP_pure rfl
  | .component ds, h => simP_bind (sim_inNested (sim_cDecls ds [] [] h)) fun p _ => by
      obtain ⟨is, es⟩ := p
      exact simP_pure rfl
  | .resource .., _ => simP_throw _ _
theorem sim_iDecl : ∀ (d : InstanceDecl) (es : Externs), naI d = true → Sim (decIDeclU d es) (decIDecl d es)
  | .export n d, es, _ => simP_bind (sim_extern n.name d) fun _ _ => simP_pure trivial
  | .type t, es, h => simP_bind (sim_defType t h) fun ti hti =>
      simP_bind (sim_onBase (gp_pushTy hti)) fun _ _ => simP_pure trivial
  | .alias _, _, h => absurd h (by simp [naI])
  | .coreType _, es, _ => simP_pure trivial
theorem sim_iDecls : ∀ (ds : List InstanceDecl) (es : Externs), naIs ds = true →
    Sim (decIDeclsU ds es) (decIDecls ds es)
  | [], es, _ => simP_pure trivial
  | d :: ds, es, h => by
    simp only [naIs, Bool.and_eq_true] at h
    exact simP_bind (sim_iDecl d es h.1) fun es' _ => sim_iDecls ds es' h.2
theorem sim_cDecls : ∀ (ds : List ComponentDecl) (is es : Externs), naCs ds = true →
    Sim (decCDeclsU ds is es) (decCDecls ds is es)
  | [], is, es, _ => simP_pure trivial
  | .import n d :: ds, is, es, h => by
    simp only [naCs, Bool.and_eq_true] at h
    exact simP_bind (sim_extern n.name d) fun k _ => sim_cDecls ds _ es h.2
  | .inst d :: ds, is, es, h => by
    simp only [naCs, naC, Bool.and_eq_true] at h
    exact simP_bind (sim_iDecl d es h.1) fun es' _ => sim_cDecls ds is es' h.2
end

/-- **On declarations without aliases, `decCDeclsU` computes what `decCDecls` computes**
(from any scope without used types, with any interfaces of instances). -/
theorem decCDeclsU_of {w : List ComponentDecl} (hw : naCs w = true) {δ : DScope} (hg : Good δ)
    (ids : Array (Option IfaceName)) {is es : Externs} {δ' : DScope}
    (h : (decCDecls w [] []).run δ = .ok ((is, es), δ')) :
    ∃ ids', (decCDeclsU w [] []).run { base := δ, ids } = .ok ((is, es), { base := δ', ids := ids' }) :=
  ((sim_cDecls w [] [] hw) { base := δ, ids } _ δ' hg h).2.2

end DecodeUse

end Silmaril.Wasm.Wac.Bridge
