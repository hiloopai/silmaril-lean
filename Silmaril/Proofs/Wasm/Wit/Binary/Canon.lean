module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Items

/-!
# The item encoder only sees the normal form

`encodeItems_normalize : encodeItems deps p.normalize = encodeItems deps p`:
the item sections do not depend on docs and stability, and wit-component's
function order is idempotent (`sortFuncs_idem`). With
`decodeItems_encodeItems`, encoding the decoded package gives the same
sections again (`encodeItems_decodeItems`): **encode ∘ decode is the identity
on the image** at the level of item sections.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Function order -/

theorem funcKey_lt (types : List TypeDef) (f : Func) : funcKey types f < types.length + 1 := by
  unfold funcKey
  split
  · exact Nat.lt_succ_self _
  · next r _ =>
    cases h : types.findIdx? (fun x => decide (x.name = r)) with
    | none => simp
    | some k => have := (List.findIdx?_eq_some_iff_getElem.mp h).1; simp; omega

/-- A sum over `range n` of one non-empty term. -/
theorem flatMap_range_single {α : Type} (X : List α) {i : Nat} :
    ∀ n, i < n → (List.range n).flatMap (fun j => if j = i then X else []) = X
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append]
    by_cases hin : i < n
    · rw [flatMap_range_single X n hin]; simp [Nat.ne_of_gt hin]
    · have hi : i = n := by omega
      have hz : (List.range n).flatMap (fun j => if j = i then X else []) = [] :=
        List.flatMap_eq_nil_iff.mpr fun j hj => by simp [Nat.ne_of_lt (hi ▸ List.mem_range.mp hj)]
      rw [hz]; simp [hi]

theorem filter_key_filter (types : List TypeDef) (fs : List Func) (i j : Nat) :
    (fs.filter (funcKey types · = j)).filter (funcKey types · = i) =
      if j = i then fs.filter (funcKey types · = i) else [] := by
  split
  · next h => subst h; simp [List.filter_filter]
  · next h =>
    refine List.filter_eq_nil_iff.mpr fun f hf => ?_
    have hj : funcKey types f = j := of_decide_eq_true (List.mem_filter.mp hf).2
    simp [hj, h]

theorem filter_sortFuncs (types : List TypeDef) (fs : List Func) {i : Nat} (hi : i < types.length + 1) :
    (sortFuncs types fs).filter (funcKey types · = i) = fs.filter (funcKey types · = i) := by
  unfold sortFuncs
  rw [List.filter_flatMap]
  simp only [filter_key_filter]
  exact flatMap_range_single _ _ hi

/-- **wit-component's function order is idempotent.** -/
theorem sortFuncs_idem (types : List TypeDef) (fs : List Func) :
    sortFuncs types (sortFuncs types fs) = sortFuncs types fs := by
  have h : ∀ i ∈ List.range (types.length + 1),
      (sortFuncs types fs).filter (funcKey types · = i) = fs.filter (funcKey types · = i) :=
    fun i hi => filter_sortFuncs types fs (List.mem_range.mp hi)
  show (List.range (types.length + 1)).flatMap (fun i => (sortFuncs types fs).filter (funcKey types · = i)) = _
  rw [List.flatMap_congr h]
  rfl

theorem funcKey_strip (types : List TypeDef) (f : Func) :
    funcKey (types.map TypeDef.strip) f.strip = funcKey types f := by
  simp only [funcKey, Func.strip, List.length_map, List.findIdx?_map, Function.comp_def, TypeDef.strip]
  rfl

theorem sortFuncs_strip (types : List TypeDef) (fs : List Func) :
    sortFuncs (types.map TypeDef.strip) (fs.map Func.strip) = (sortFuncs types fs).map Func.strip := by
  simp [sortFuncs, List.filter_map, List.map_flatMap, Function.comp_def, funcKey_strip]

/-! ## Docs do not reach the item encoder -/

theorem fields_strip : ∀ fs : List (Labeled Ty), fields (fs.map Labeled.strip) = fields fs
  | [] => rfl
  | f :: fs => by simp only [List.map_cons, fields, fields_strip fs]; rfl

theorem cases_strip : ∀ cs : List (Labeled (Option Ty)), cases (cs.map Labeled.strip) = cases cs
  | [] => rfl
  | c :: cs => by simp only [List.map_cons, cases, cases_strip cs]; rfl

theorem names_strip (cs : List (Labeled Unit)) : (cs.map Labeled.strip).map (·.name) = cs.map (·.name) := by
  simp [Function.comp_def, Labeled.strip]

theorem typeDefIdx_strip (k : TyDefKind) : typeDefIdx k.strip = typeDefIdx k := by
  cases k <;> simp only [TyDefKind.strip, typeDefIdx, fields_strip, cases_strip, names_strip]

theorem TyDefKind.strip_ne_resource {k : TyDefKind} (h : k ≠ .resource) : k.strip ≠ .resource := by
  cases k <;> simp_all [TyDefKind.strip]

theorem typeDef_strip (td : TypeDef) : typeDef td.strip = typeDef td := by
  by_cases hk : td.kind = .resource
  · have hk' : td.strip.kind = .resource := by simp [TypeDef.strip, hk, TyDefKind.strip]
    rw [typeDef_resource hk, typeDef_resource hk']; rfl
  · have hk' : td.strip.kind ≠ .resource := TyDefKind.strip_ne_resource hk
    rw [typeDef_other hk, typeDef_other hk']
    show (do
      let idx ← typeDefIdx td.kind.strip
      let k ← exportType td.name (.eq idx)
      insertNamed ⟨.local, td.name⟩ k) = _
    rw [typeDefIdx_strip]

theorem typeDefs_strip : ∀ tds : List TypeDef, typeDefs (tds.map TypeDef.strip) = typeDefs tds
  | [] => rfl
  | td :: tds => by simp only [List.map_cons, typeDefs, typeDef_strip, typeDefs_strip tds]

theorem exportFuncs_strip : ∀ fs : List Func, exportFuncs (fs.map Func.strip) = exportFuncs fs
  | [] => rfl
  | f :: fs => by simp only [List.map_cons, exportFuncs, exportFuncs_strip fs]; rfl

theorem encodeInstance_normalize (i : Option IfaceName) (b : Interface) :
    encodeInstance i b.normalize = encodeInstance i b := by
  simp only [encodeInstance, Interface.normalize, sortFuncs_strip, sortFuncs_idem, typeDefs_strip,
    exportFuncs_strip]

theorem encodeTypesOnly_normalize (i : IfaceName) (b : Interface) :
    encodeTypesOnly i b.normalize = encodeTypesOnly i b := by
  simp only [encodeTypesOnly, Interface.normalize, typeDefs_strip]

theorem directDeps_normalize (b : Interface) : directDeps b.normalize = directDeps b := by
  simp only [directDeps, Interface.normalize, List.filterMap_map]
  congr 1; funext td
  cases hk : td.kind <;> simp [TypeDef.strip, hk, TyDefKind.strip]

/-! ## Environments -/

/-- Interface bodies the encoder cannot tell apart. -/
structure BodyEq (b b' : Interface) : Prop where
  inst : ∀ i, encodeInstance i b' = encodeInstance i b
  types : ∀ i, encodeTypesOnly i b' = encodeTypesOnly i b
  deps : directDeps b' = directDeps b

theorem BodyEq.refl (b : Interface) : BodyEq b b := ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem BodyEq.normalize (b : Interface) : BodyEq b b.normalize :=
  ⟨fun i => encodeInstance_normalize i b, fun i => encodeTypesOnly_normalize i b, directDeps_normalize b⟩

theorem optionRel_refl : ∀ o : Option Interface, Option.Rel BodyEq o o
  | none => .none
  | some b => .some (BodyEq.refl b)

/-- Environments the encoder cannot tell apart. -/
structure EnvEq (env env' : Env) : Prop where
  len : env'.length = env.length
  find : ∀ j, Option.Rel BodyEq (env.find? j) (env'.find? j)

theorem lookup'_norm (pn : PackageName) (deps : Env) (i : IfaceName) : ∀ L : List (String × Interface),
    Option.Rel BodyEq (liveDeps.lookup' i (L.map (fun nb => (pn.iface nb.1, nb.2)) ++ deps))
      (liveDeps.lookup' i (L.map (fun nb => (pn.iface nb.1, nb.2.normalize)) ++ deps))
  | [] => optionRel_refl _
  | (n, b) :: L => by
    simp only [List.map_cons, List.cons_append, liveDeps.lookup']
    split
    · exact .some (BodyEq.normalize b)
    · exact lookup'_norm pn deps i L

theorem env_eq (p : Package) (deps : Env) : EnvEq (p.env deps) (p.normalize.env deps) := by
  have he : p.env deps = p.interfaces.map (fun nb => (p.name.iface nb.1, nb.2)) ++ deps := rfl
  have he' : p.normalize.env deps = p.interfaces.map (fun nb => (p.name.iface nb.1, nb.2.normalize)) ++ deps := by
    simp [Package.env, Package.normalize, Function.comp_def]
  rw [he, he']
  exact ⟨by simp, fun j => lookup'_norm p.name deps j p.interfaces⟩

/-- Related lookups: both absent, or bodies the encoder cannot tell apart. -/
theorem rel_cases {o o' : Option Interface} (h : Option.Rel BodyEq o o') :
    (o = none ∧ o' = none) ∨ ∃ b b', o = some b ∧ o' = some b' ∧ BodyEq b b' := by
  cases h with
  | none => exact .inl ⟨rfl, rfl⟩
  | some hb => exact .inr ⟨_, _, rfl, rfl, hb⟩

theorem liveDeps_congr {env env' : Env} (h : EnvEq env env') :
    ∀ fuel i acc, liveDeps env' fuel i acc = liveDeps env fuel i acc
  | 0, _, _ => rfl
  | fuel + 1, i, acc => by
    unfold liveDeps
    simp only [liveDeps_congr h fuel]
    rcases rel_cases (h.find i) with ⟨h1, h2⟩ | ⟨b, b', h1, h2, hb⟩
    · have e1 : liveDeps.lookup' i env = none := h1
      have e2 : liveDeps.lookup' i env' = none := h2
      rw [e1, e2]
    · have e1 : liveDeps.lookup' i env = some b := h1
      have e2 : liveDeps.lookup' i env' = some b' := h2
      rw [e1, e2]; simp only [hb.deps]

theorem ifacePart_congr {env env' : Env} (h : EnvEq env env') (i : IfaceName) {b b' : Interface}
    (hb : BodyEq b b') (j : IfaceName) : ifacePart env' i b' j = ifacePart env i b j := by
  unfold ifacePart
  split
  · rw [hb.inst]
  · rcases rel_cases (h.find j) with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hc⟩
    · rw [h1, h2]
    · rw [h1, h2]; simp only [hc.types]

theorem ifaceParts_congr {env env' : Env} (h : EnvEq env env') (i : IfaceName) {b b' : Interface}
    (hb : BodyEq b b') : ∀ L, ifaceParts env' i b' L = ifaceParts env i b L
  | [] => rfl
  | j :: L => by simp only [ifaceParts, ifacePart_congr h i hb j, ifaceParts_congr h i hb L]

theorem encodeIface_congr {env env' : Env} (h : EnvEq env env') (i : IfaceName) {b b' : Interface}
    (hb : BodyEq b b') : encodeIface env' i b' = encodeIface env i b := by
  simp only [encodeIface, h.len, liveDeps_congr h, ifaceParts_congr h i hb]

theorem worldItem_congr {env env' : Env} (h : EnvEq env env') (imp : Bool) (it : WorldItem) :
    worldItem env' imp it.normalize = worldItem env imp it := by
  cases it with
  | ifaceRef j d st =>
    simp only [WorldItem.normalize, worldItem]
    rcases rel_cases (h.find j) with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hc⟩
    · rw [h1, h2]
    · rw [h1, h2]; simp only [hc.inst]
  | ifaceInline n b => simp only [WorldItem.normalize, worldItem, encodeInstance_normalize]
  | func f => rfl
  | type td => simp only [WorldItem.normalize, worldItem, typeDef_strip]

theorem worldItems_congr {env env' : Env} (h : EnvEq env env') (imp : Bool) :
    ∀ its : List WorldItem, worldItems env' imp (its.map WorldItem.normalize) = worldItems env imp its
  | [] => rfl
  | it :: its => by simp only [List.map_cons, worldItems, worldItem_congr h, worldItems_congr h imp its]

theorem encodeWorld_congr {env env' : Env} (h : EnvEq env env') (w : World) :
    encodeWorld env' w.normalize = encodeWorld env w := by
  simp only [encodeWorld, World.normalize, worldItems_congr h]

/-- **The item encoder sees only the normal form.** -/
theorem encodeItems_normalize (deps : Env) (p : Package) : encodeItems deps p.normalize = encodeItems deps p := by
  have h := env_eq p deps
  have hn : p.normalize.name = p.name := rfl
  have hI : p.normalize.interfaces = p.interfaces.map (fun x => (x.1, x.2.normalize)) := rfl
  have hW : p.normalize.worlds = p.worlds.map (fun x => (x.1, x.2.normalize)) := rfl
  have fi : (encodeIfaceItem (p.normalize.env deps) p.name ∘ fun x => (x.1, x.2.normalize)) =
      encodeIfaceItem (p.env deps) p.name := funext fun nb => by
    simp only [Function.comp_apply, encodeIfaceItem, encodeIface_congr h _ (BodyEq.normalize nb.2)]
  have fw : (encodeWorldItem (p.normalize.env deps) p.name ∘ fun x => (x.1, x.2.normalize)) =
      encodeWorldItem (p.env deps) p.name := funext fun nw => by
    simp only [Function.comp_apply, encodeWorldItem, encodeWorld_congr h]
  unfold encodeItems
  dsimp only
  rw [hn, hI, hW, List.mapM_map, List.mapM_map, fi, fw]

/-- **encode ∘ decode is the identity on the image** (item sections): the
package decoded from the item sections of `p` encodes to the same sections. -/
theorem encodeItems_decodeItems {deps : Env} {p : Package} (hv : p.Valid deps) {ss : List Section}
    (h : encodeItems deps p = .ok ss) {q : Package} (hq : decodeItems ss = .ok q) :
    encodeItems deps q = .ok ss := by
  have hn : q = p.normalize := by
    rw [decodeItems_encodeItems hv h] at hq; exact (Except.ok.inj hq).symm
  rw [hn, encodeItems_normalize, h]

end Silmaril.Wasm.Wit.Binary
