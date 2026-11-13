module

public import Silmaril.Wasm.Wit.Valid.Defs
public import Silmaril.Wasm.Wit.Resolve.Thms

/-!
# WIT: the validity checker is sound and complete

* `refB_sound`/`refB_complete`, `useB_iff`, `path_iff`, `inclB_iff`: each resolution
  fact computed with fuel is the one given by the relations, once the interface (and,
  for references, type) graph is accepted by `kahn`.
* `funLeaves_eq`: then the computed facts are the specified ones.
* `check_iff`: `check U = true ↔ Valid U`, with `check_sound` and `check_complete`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit

open Graph

variable {U : Universe}

theorem Leaves.eq_of_iff {L₁ L₂ : Leaves} (h₁ : ∀ o r, L₁.ref o r ↔ L₂.ref o r)
    (h₂ : ∀ p path y, L₁.use p path y ↔ L₂.use p path y)
    (h₃ : ∀ k p path, L₁.path k p path ↔ L₂.path k p path)
    (h₄ : ∀ p path ns, L₁.incl p path ns ↔ L₂.incl p path ns) : L₁ = L₂ := by
  obtain ⟨r₁, u₁, p₁, i₁⟩ := L₁
  obtain ⟨r₂, u₂, p₂, i₂⟩ := L₂
  have er : r₁ = r₂ := funext fun o => funext fun r => propext (h₁ o r)
  have eu : u₁ = u₂ := funext fun p => funext fun path => funext fun y => propext (h₂ p path y)
  have ep : p₁ = p₂ := funext fun k => funext fun p => funext fun path => propext (h₃ k p path)
  have ei : i₁ = i₂ := funext fun p => funext fun path => funext fun ns => propext (h₄ p path ns)
  rw [er, eu, ep, ei]

theorem refB_sound {F G : Nat} {o : Owner} {r : Ref} (h : refB U F G o r = true) :
    (specLeaves U).ref o r := by
  unfold refB at h
  cases hb : bind U F o r.2 with
  | none => simp [hb] at h
  | some t =>
    have h' : (r.1 == .plain || isRes U F G t) = true := by simpa [hb] using h
    refine ⟨t, bind_sound hb, fun hk => isRes_sound (f := F) G t ?_⟩
    simpa [hk] using h'

theorem refB_complete (hi : kahn (ifaceDeps U) U.ifaceIds = true)
    (ht : kahn (typeDeps U U.ifaceIds.length) U.typeIds = true) {o : Owner} {r : Ref}
    (h : (specLeaves U).ref o r) : refB U U.ifaceIds.length U.typeIds.length o r = true := by
  obtain ⟨t, hb, hr⟩ := h
  have hb' : bind U U.ifaceIds.length o r.2 = some t := (bind_iff_of_kahn hi).mpr hb
  cases hk : r.1 with
  | plain => simp [refB, hb', hk]
  | handle => simp [refB, hb', hk, (isRes_iff_of_kahn hi ht).mpr (hr hk)]

theorem useB_iff (hi : kahn (ifaceDeps U) U.ifaceIds = true) {p : PackageName}
    {path : UsePath} {y : Name} :
    useB U U.ifaceIds.length p path y = true ↔ (specLeaves U).use p path y := by
  constructor
  · intro h
    unfold useB at h
    cases hr : resolve U .iface p path with
    | none => simp [hr] at h
    | some j =>
      have h' : (denote U U.ifaceIds.length j y).isSome = true := by simpa [hr] using h
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h'
      exact ⟨j, t, resolve_sound hr, denote_sound _ _ _ _ ht⟩
  · rintro ⟨j, t, hr, hd⟩
    simp [useB, resolve_complete hr, (denote_iff_of_kahn hi).mpr hd]

theorem path_iff {k : Kind} {p : PackageName} {path : UsePath} :
    (resolve U k p path).isSome = true ↔ (specLeaves U).path k p path := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, resolve_sound hj⟩
  · rintro ⟨j, hj⟩
    simp [resolve_complete hj]

theorem inclB_iff {p : PackageName} {path : UsePath} {ns : List Name} :
    inclB U p path ns = true ↔ (specLeaves U).incl p path ns := by
  constructor
  · intro h
    unfold inclB at h
    cases hr : resolve U .world p path with
    | none => simp [hr] at h
    | some w =>
      cases hW : U.world? w with
      | none => simp [hr, hW] at h
      | some W =>
        have h' : ∀ n ∈ ns, n ∈ W.externNames := by simpa [hr, hW] using h
        exact ⟨w, W, resolve_sound hr, hW, h'⟩
  · rintro ⟨w, W, hr, hW, hns⟩
    have hall : (ns.all fun n => W.externNames.contains n) = true := by simpa using hns
    simp only [inclB, resolve_complete hr, hW, hall]

/-- Once the interface and type graphs are accepted, the computed resolution facts are
the specified ones. -/
theorem funLeaves_eq (hi : kahn (ifaceDeps U) U.ifaceIds = true)
    (ht : kahn (typeDeps U U.ifaceIds.length) U.typeIds = true) :
    funLeaves U U.ifaceIds.length U.typeIds.length = specLeaves U :=
  Leaves.eq_of_iff (fun _ _ => ⟨refB_sound, refB_complete hi ht⟩) (fun _ _ _ => useB_iff hi)
    (fun _ _ _ => path_iff) (fun _ _ _ => inclB_iff)

/-- The checker accepts exactly the valid universes. -/
theorem check_iff : check U = true ↔ Valid U := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hi, ht⟩, hw⟩, hv⟩
    have hv' : ValidWith (specLeaves U) U := funLeaves_eq hi ht ▸ hv
    exact ⟨hv', kahn_iface_iff.mp hi, (kahn_type_iff hi).mp ht, kahn_world_iff.mp hw⟩
  · rintro ⟨hv, hi, ht, hw⟩
    have hi' := kahn_iface_iff.mpr hi
    have ht' := (kahn_type_iff hi').mpr ht
    exact ⟨⟨⟨hi', ht'⟩, kahn_world_iff.mpr hw⟩, (funLeaves_eq hi' ht').symm ▸ hv⟩

theorem check_sound (h : check U = true) : Valid U := check_iff.mp h

theorem check_complete (h : Valid U) : check U = true := check_iff.mpr h

end Silmaril.Wasm.Wit
