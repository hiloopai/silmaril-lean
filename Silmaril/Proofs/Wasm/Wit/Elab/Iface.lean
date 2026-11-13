module

public import Silmaril.Proofs.Wasm.Wit.Elab.Scope

/-!
# Elaboration: interfaces of a valid universe

* `iface?_of_mem`: in a valid universe an interface is found by its id;
* `elabBody_iface_isSome`: the body of every interface of a valid universe is
  elaborated (its types have a topological order);
* `elabEnv_ok`: `elabEnv` succeeds on every valid universe.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

theorem pkg?_of_mem {U : Universe} (hn : (U.map (·.name)).Nodup) {P : Package} (hP : P ∈ U) :
    Universe.pkg? U P.name = some P := by
  induction U with
  | nil => exact absurd hP List.not_mem_nil
  | cons Q U ih =>
    have hn' : (U.map (·.name)).Nodup := (List.nodup_cons.mp (by simpa using hn)).2
    have hQ : Q.name ∉ U.map (·.name) := (List.nodup_cons.mp (by simpa using hn)).1
    rcases List.mem_cons.mp hP with rfl | hP
    · simp [Universe.pkg?]
    · have hne : Q.name ≠ P.name := fun he => hQ (he ▸ List.mem_map_of_mem hP)
      have ih' : Universe.pkg? U P.name = some P := ih hn' hP
      simpa [Universe.pkg?, List.find?_cons, hne] using ih'

theorem iface?_of_mem {P : Package} (hn : (P.items.map PackageItem.name).Nodup) {I : Interface}
    (hI : PackageItem.iface I ∈ P.items) : P.iface? I.name = some I := by
  unfold Package.iface?
  generalize P.items = items at hn hI ⊢
  induction items with
  | nil => exact absurd hI List.not_mem_nil
  | cons it items ih =>
    have hn' : (items.map PackageItem.name).Nodup := (List.nodup_cons.mp (by simpa using hn)).2
    have hit : it.name ∉ items.map PackageItem.name := (List.nodup_cons.mp (by simpa using hn)).1
    rcases List.mem_cons.mp hI with rfl | hI
    · simp
    · have hne : it.name ≠ I.name := fun he => hit (he ▸ List.mem_map_of_mem (f := PackageItem.name) hI)
      have ih' := ih hn' hI
      cases it with
      | iface J =>
        have hJ : J.name ≠ I.name := hne
        simpa [hJ] using ih'
      | world W => simpa using ih'
      | use u => simpa using ih'

/-- The names a scope binds are among the names of the interface items. -/
theorem scope_names_sublist : ∀ items : List IfaceItem,
    ((items.filterMap IfaceItem.scope).flatMap ScopeItem.names).Sublist (items.flatMap IfaceItem.names)
  | [] => List.nil_sublist _
  | it :: rest => by
    have ih := scope_names_sublist rest
    cases it with
    | type d => simpa [IfaceItem.scope, ScopeItem.names, IfaceItem.names] using ih
    | use u => simpa [IfaceItem.scope, ScopeItem.names, IfaceItem.names] using ih
    | func f =>
      show ((rest.filterMap IfaceItem.scope).flatMap ScopeItem.names).Sublist (f.name :: rest.flatMap IfaceItem.names)
      exact ih.cons f.name

theorem refsOpt_mem {r : Ref} : ∀ {o : Option Ty}, r ∈ Ty.refsOpt o → ∃ t, o = some t ∧ r ∈ t.refs
  | none, h => absurd h List.not_mem_nil
  | some t, h => ⟨t, rfl, h⟩

/-- A well-formed definition's references are resolved. -/
theorem kindOk_ref {U : Universe} {o : Owner} {d : TypeDef} (hk : KindOk (specLeaves U) o d.kind)
    {r : Ref} (hr : r ∈ d.refs) : (specLeaves U).ref o r := by
  unfold TypeDef.refs at hr
  revert hk hr
  cases d.kind with
  | «alias» t => exact fun hk hr => hk.2 r hr
  | record fs =>
    exact fun hk hr => (List.mem_flatMap.mp hr).elim fun f ⟨hf, hrf⟩ => (hk.2 f hf).2 r hrf
  | variant cs =>
    exact fun hk hr => (List.mem_flatMap.mp hr).elim fun k ⟨hk', hrk⟩ =>
      (refsOpt_mem hrk).elim fun t ⟨hty, hrt⟩ => (hk.2 k hk' t hty).2 r hrt
  | enum _ => exact fun _ hr => absurd hr List.not_mem_nil
  | flags _ => exact fun _ hr => absurd hr List.not_mem_nil
  | resource _ => exact fun _ hr => absurd hr List.not_mem_nil

/-- A well-formed definition's references denote types. -/
theorem kindOk_refs {U : Universe} {o : Owner} {d : TypeDef} (hk : KindOk (specLeaves U) o d.kind) :
    ∀ r ∈ d.refs, ∃ t, Binds U o r.2 t := fun _ hr =>
  (kindOk_ref hk hr).elim fun t ⟨hb, _⟩ => ⟨t, hb⟩

/-- The scope of a well-formed list of interface items satisfies the hypotheses
of `elabTypes_isSome`. -/
theorem itemsOk_scope {U : Universe} {o : Owner} {items : List IfaceItem}
    (h : ItemsOk (specLeaves U) o items) :
    ((items.filterMap IfaceItem.scope).flatMap ScopeItem.names).Nodup ∧
      ∀ d, ScopeItem.type d ∈ items.filterMap IfaceItem.scope → ∀ r ∈ d.refs, ∃ t, Binds U o r.2 t := by
  refine ⟨(scope_names_sublist items).nodup h.1, fun d hd => ?_⟩
  obtain ⟨it, hit, hsc⟩ := List.mem_filterMap.mp hd
  cases it with
  | type d' =>
    have hdd : d' = d := by simpa [IfaceItem.scope] using hsc
    subst hdd
    exact kindOk_refs (h.2 _ hit).2.2
  | use u => simp [IfaceItem.scope] at hsc
  | func f => simp [IfaceItem.scope] at hsc

/-- **The body of an interface of a valid universe is elaborated.** -/
theorem elabBody_iface_isSome {U : Universe} (hv : Valid U) (c : Ctx) {P : Package} (hP : P ∈ U)
    {I : Interface} (hI : PackageItem.iface I ∈ P.items) :
    (elabBody c (.iface ⟨P.name, I.name⟩) I.items I.docs I.gates).isSome := by
  have hpk : PackageOk (specLeaves U) P := hv.pkgs.2 P hP
  have hU : U.iface? ⟨P.name, I.name⟩ = some I := by
    simp only [Universe.iface?, pkg?_of_mem hv.pkgs.1 hP, Option.bind_some]
    exact iface?_of_mem hpk.2.1 hI
  have hsc : (Owner.iface ⟨P.name, I.name⟩).scope U = some (I.items.filterMap IfaceItem.scope) := by
    simp only [Owner.scope, hU, Option.map_some]
  have hok : ItemsOk (specLeaves U) (.iface ⟨P.name, I.name⟩) I.items := (hpk.2.2 _ hI).2.2
  obtain ⟨hn, hrefs⟩ := itemsOk_scope hok
  have ht : (elabTypes c (.iface ⟨P.name, I.name⟩) (I.items.filterMap IfaceItem.scope)).isSome :=
    elabTypes_isSome hsc hn hrefs hv.typeAcyclic
  obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp ht
  simp [elabBody, hts]

theorem mapM_ok_of_forall {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ l', l.mapM f = .ok l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl'⟩ := mapM_ok_of_forall (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: l', by rw [List.mapM_cons, hb, hl']; rfl⟩

/-- **`elabEnv` succeeds on every valid universe**: all interfaces have a
topological type order. -/
theorem elabEnv_ok {U : Universe} (hv : Valid U) (c : Ctx) (hc : c.U = U) :
    ∃ env, elabEnv c = .ok env := by
  unfold elabEnv
  apply mapM_ok_of_forall
  intro pI hpI
  obtain ⟨P, hP, hpI'⟩ := List.mem_flatMap.mp (hc ▸ hpI)
  obtain ⟨it, hit, hsome⟩ := List.mem_filterMap.mp hpI'
  cases it with
  | iface I =>
    have hpI_eq : pI = (P.name, I) := by simpa using hsome.symm
    subst hpI_eq
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (elabBody_iface_isSome hv c hP hit)
    exact ⟨_, by simp only [hb]; rfl⟩
  | world W => simp at hsome
  | use u => simp at hsome

end Silmaril.Wasm.Wit.Elab
