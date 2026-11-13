module

public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Defs
public import Batteries.Data.Except
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Predicates.Defs
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Thms

/-!
# `Types.Subtype.Check`: laws of the component reference

Theorems of the component reference copy `Types.Subtype.Check`, refined out of
`Silmaril.Raw.Wasm.Component.Types.Subtype.Check`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Types

universe u v
variable {R : Type u} {X : Type v}

theorem mem_of_lookupKey {K : Type u} {V : Type v} [DecidableEq K] :
    ∀ {kvs : List (K × V)} {k : K} {v : V}, lookupKey kvs k = some v → (k, v) ∈ kvs
  | [], _, _, h => nomatch h
  | (k', v') :: kvs, k, v, h => by
    simp only [lookupKey] at h
    split at h
    · cases h; subst k'; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookupKey h)

theorem withCtx_ok {ctx : String} {e : Except String Unit} (h : withCtx ctx e = .ok ()) :
    e = .ok () := by
  cases e with
  | ok u => rfl
  | error m => simp only [withCtx, reduceCtorEq] at h

theorem checkEach_ok {α : Type u} {f : α → Except String Unit} :
    ∀ {l : List α}, checkEach f l = .ok () → ∀ a ∈ l, f a = .ok ()
  | [], _, _, h => nomatch h
  | a :: as, h, b, hb => by
    simp only [checkEach] at h
    split at h
    · rename_i hfa
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hfa
      · exact checkEach_ok h b hb
    · cases h

theorem valSub?_sound [DecidableEq R] {a b : ValType R} (h : valSub? a b = .ok ()) : a = b := by
  unfold valSub? at h
  split at h
  · assumption
  · cases h

theorem funcSub?_sound [DecidableEq R] {a b : FuncType R} (h : funcSub? a b = .ok ()) :
    a = b := by
  unfold funcSub? at h
  split at h
  · assumption
  · cases h

theorem moduleSub?_sound {xsub? : X → X → Except String Unit} {XSub : X → X → Prop}
    (hx : ∀ x y, xsub? x y = .ok () → XSub x y) {a b : CoreModuleType X}
    (h : moduleSub? xsub? a b = .ok ()) : CoreModuleType.Sub XSub a b := by
  unfold moduleSub? at h
  split at h
  · cases h
  · rename_i hi
    refine ⟨fun k x hkx => ?_, fun k y hky => ?_⟩
    · have := checkEach_ok hi _ hkx
      simp only at this
      split at this
      · cases this
      · rename_i y hy
        exact ⟨y, mem_of_lookupKey hy, hx _ _ (withCtx_ok this)⟩
    · have := checkEach_ok h _ hky
      simp only at this
      split at this
      · cases this
      · rename_i x hx'
        exact ⟨x, mem_of_lookupKey hx', hx _ _ (withCtx_ok this)⟩

section Structural

variable [DecidableEq R]

theorem checkTargets_sound {a b : ComponentType R X} {binders : List R} {φ : R → R}
    (h : checkTargets a b binders φ = .ok ()) :
    ∀ r ∈ binders, φ r = r ∨ ComponentType.RenameTarget a b (φ r) := by
  intro r hr
  have := checkEach_ok h r hr
  split at this
  · assumption
  · cases this

variable {chk : Entity R X → Entity R X → Except String Unit} {XSub : X → X → Prop}

omit [DecidableEq R] in
theorem instanceSub?_sound (hchk : ∀ a b, chk a b = .ok () → Entity.Sub XSub a b)
    {a b : InstanceType R X} (h : instanceSub? chk a b = .ok ()) :
    InstanceType.Sub XSub a b := by
  unfold instanceSub? at h
  split at h
  · cases h
  refine .mk (Entity.ListSub.of_forall fun n eb hm => ?_)
  have := checkEach_ok h _ hm
  simp only at this
  split at this
  · cases this
  · rename_i x hx
    exact ⟨x, mem_of_lookupKey hx, hchk _ _ (withCtx_ok this)⟩

end Structural

end Silmaril.Wasm.Component.Types

namespace Silmaril.Wasm.Component.Types

universe u v
variable {R : Type u} {X : Type v}

section Structural

variable [DecidableEq R]
variable {chk : Entity R X → Entity R X → Except String Unit} {XSub : X → X → Prop}

omit [DecidableEq R] in
/-- A list of renamed expectations, each matched by a named subtype entity. -/
theorem Entity.ListSub.of_mapList {f : R → R} {args expected : List (String × Entity R X)}
    (key : ∀ n e, (n, e) ∈ expected → ∃ a, (n, a) ∈ args ∧ Entity.Sub XSub a (e.map f)) :
    Entity.ListSub XSub args (Entity.mapList f expected) := by
  induction expected with
  | nil => exact .nil
  | cons p es ih =>
    obtain ⟨n, e⟩ := p
    obtain ⟨a, ha, hs⟩ := key n e List.mem_cons_self
    exact .cons ha hs (ih fun n' e' hm => key n' e' (List.mem_cons_of_mem _ hm))

/-- A successful `openInstanceType?` returns the inferred remapping, and every expectation
has a same-named argument that `chk` accepts against the remapped expectation. -/
theorem openInstanceType?_ok {args expected : List (String × Entity R X)} {binders : List R}
    {kind : String} {m : Remapping R}
    (h : openInstanceType? chk args binders expected kind = .ok m) :
    m = inferRemapping binders args expected ∧ ∀ n e, (n, e) ∈ expected →
      ∃ a, (n, a) ∈ args ∧ chk a (e.map (m.apply binders)) = .ok () := by
  unfold openInstanceType? at h
  simp only at h
  split at h
  · cases h
  split at h
  · rename_i hc
    cases h
    refine ⟨rfl, fun n e hm => ?_⟩
    have := checkEach_ok hc _ hm
    simp only at this
    split at this
    · cases this
    · rename_i x hx
      exact ⟨x, mem_of_lookupKey hx, withCtx_ok this⟩
  · cases h

theorem openInstanceType?_sound (hchk : ∀ a b, chk a b = .ok () → Entity.Sub XSub a b)
    {args expected : List (String × Entity R X)} {binders : List R} {kind : String}
    {m : Remapping R} (h : openInstanceType? chk args binders expected kind = .ok m) :
    Entity.ListSub XSub args (Entity.mapList (m.apply binders) expected) := by
  obtain ⟨-, key⟩ := openInstanceType?_ok h
  exact Entity.ListSub.of_mapList fun n e hm =>
    let ⟨a, ha, hc⟩ := key n e hm
    ⟨a, ha, hchk _ _ hc⟩

theorem componentSub?_sound (hchk : ∀ a b, chk a b = .ok () → Entity.Sub XSub a b)
    {a b : ComponentType R X} (h : componentSub? chk a b = .ok ()) :
    ComponentType.Sub XSub a b := by
  unfold componentSub? at h
  split at h
  · cases h
  · rename_i m hm
    split at h
    · cases h
    · rename_i ht
      split at h
      · cases h
      · rename_i m' hm'
        exact .mk (m.apply a.imported) (m'.apply b.defined)
          (fun _ hr => Remapping.apply_of_not_mem m hr) (checkTargets_sound ht)
          (openInstanceType?_sound hchk hm)
          (fun _ hr => Remapping.apply_of_not_mem m' hr) (checkTargets_sound h)
          (openInstanceType?_sound hchk hm')

theorem typeDefSub?_sound (hchk : ∀ a b, chk a b = .ok () → Entity.Sub XSub a b)
    {a b : TypeDef R X} (h : typeDefSub? chk a b = .ok ()) : TypeDef.Sub XSub a b := by
  cases a <;> cases b <;> simp only [typeDefSub?, reduceCtorEq] at h
  · cases valSub?_sound h; exact .val
  · split at h
    · subst_vars; exact .resource
    · cases h
  · cases funcSub?_sound h; exact .func
  · exact .instance (instanceSub?_sound hchk h)
  · exact .component (componentSub?_sound hchk h)

theorem entitySubStep_sound {xsub? : X → X → Except String Unit}
    (hx : ∀ x y, xsub? x y = .ok () → XSub x y)
    (hchk : ∀ a b, chk a b = .ok () → Entity.Sub XSub a b)
    {a b : Entity R X} (h : entitySubStep xsub? chk a b = .ok ()) : Entity.Sub XSub a b := by
  cases a <;> cases b <;> simp only [entitySubStep, reduceCtorEq] at h
  · exact .module (moduleSub?_sound hx h)
  · cases funcSub?_sound h; exact .func
  · cases valSub?_sound h; exact .value
  · exact .type (typeDefSub?_sound hchk h)
  · exact .instance (instanceSub?_sound hchk h)
  · exact .component (componentSub?_sound hchk h)

theorem subFuel_sound {xsub? : X → X → Except String Unit}
    (hx : ∀ x y, xsub? x y = .ok () → XSub x y) :
    ∀ (n : Nat) (a b : Entity R X), subFuel xsub? n a b = .ok () → Entity.Sub XSub a b
  | 0, _, _, h => by simp only [subFuel, reduceCtorEq] at h
  | n + 1, _, _, h => entitySubStep_sound hx (subFuel_sound hx n) h

/-- Soundness of the executable checker against the relational subtyping. -/
theorem Entity.sub?_sound {xsub? : X → X → Except String Unit}
    (hx : ∀ x y, xsub? x y = .ok () → XSub x y) {a b : Entity R X}
    (h : Entity.sub? xsub? a b = .ok ()) : Entity.Sub XSub a b :=
  subFuel_sound hx _ a b h

end Structural

end Silmaril.Wasm.Component.Types
