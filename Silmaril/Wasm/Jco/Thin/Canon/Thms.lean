module

public import Silmaril.Wasm.Jco.Thin.Canon.Defs
public import Silmaril.Wasm.Jco.Wrap.Thms

/-!
# Thin wrappers over the canonical ABI: behaviour and agreement with `wrap`

* `thinComp_callExport`: the thin wrapper's behaviour is the canonical
  convention, `canonSpec`. This holds for every module and every metadata.
* `lowerParams_realloc`, `lowerParams_memFree`: canonical lowering through
  the module's `realloc` is the C convention's copying through `alloc`. The
  first needs `ReallocAgrees`. The second needs memory-free parameters and
  works for any `realloc`.
* **Relating the two FFI styles.** `canonSpec_eq_spec` says that on a world
  where no function returns through memory and `ReallocAgrees` holds, the
  canonical convention is the C convention. `canonSpec_eq_spec_memFree` drops
  `ReallocAgrees` for memory-free worlds.
* **Agreement of (b) with (a).** `recognizeThin_agrees` and
  `recognizeThin_agrees_memFree`: when recognition succeeds and the module
  conforms, the thin wrapper and the monadic construction `wrap md` have
  equal behaviour relations on every export. The adaptor is then
  behaviourally the identity.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst) (md : Meta)

/-- **The thin wrapper follows the canonical convention**, for every module. -/
theorem thinComp_callExport (r name : String) (vs : List PVal) :
    (thinComp md r).callExport M name vs = canonSpec M md.world r name vs := by
  simp only [Comp.callExport, thinComp, canonSpec, List.find?_map]
  have hp : ((fun x : Lift => x.sig.name == name) ∘
      fun s : Sig => ({ sig := s, callee := .core s.name, realloc := .core r } : Lift)) =
      fun s : Sig => s.name == name := rfl
  rw [hp]
  cases md.world.find? (·.name == name) <;> rfl

theorem lowerParam_realloc {r : String} (hR : ReallocAgrees M md r) (t : PTy) (v : PVal) :
    lowerParam M (M.call r) t v = md.specParam M t v := by
  cases t <;> cases v <;> simp only [lowerParam, Meta.specParam, lowerBytes, Meta.specBytes]
  all_goals
    congr 1
    funext _
    rw [hR]

/-- Canonical lowering through an agreeing `realloc` is the C convention. -/
theorem lowerParams_realloc {r : String} (hR : ReallocAgrees M md r) :
    ∀ (ps : List PTy) (vs : List PVal), lowerParams M (M.call r) ps vs = md.specParams M ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, v :: vs => by
    simp only [lowerParams, Meta.specParams, lowerParam_realloc M md hR,
      lowerParams_realloc hR ts vs]

/-- Memory-free parameters are lowered as the C convention, whatever the
`realloc`. -/
theorem lowerParams_memFree (R : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List PTy) (vs : List PVal), (ps.all PTy.memFree = true) →
      lowerParams M R ps vs = md.specParams M ps vs
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | t :: ts, v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ht, hts⟩ := h
    have hp : lowerParam M R t v = md.specParam M t v := by
      cases t with
      | val t' => cases v <;> rfl
      | string => simp [PTy.memFree] at ht
      | bytes => simp [PTy.memFree] at ht
    simp only [lowerParams, Meta.specParams, hp, lowerParams_memFree R ts vs hts]

/-- One call: the canonical call of the module's own export is the C
convention's call when the result is not passed through memory. -/
theorem canonCall_specCall {R : List Flat → RM M.St (List Flat)} (s : Sig)
    (hs : inMem s.result = false) (hp : ∀ vs, lowerParams M R s.params vs = md.specParams M s.params vs)
    (vs : List PVal) : canonCall M R (M.call s.name) s vs = md.specCall M s vs := by
  simp only [canonCall, Meta.specCall, hs, hp, Bool.false_eq_true, ↓reduceIte]

theorem find?_mem {name : String} {s : Sig} (h : md.world.find? (·.name == name) = some s) :
    s ∈ md.world := List.mem_of_find?_eq_some h

theorem thinOk_mem (h : md.thinOk = true) {s : Sig} (hs : s ∈ md.world) :
    inMem s.result = false := by
  simp only [Meta.thinOk, List.all_eq_true, Bool.not_eq_true'] at h
  exact h s hs

theorem memFree_mem (h : md.memFree = true) {s : Sig} (hs : s ∈ md.world) :
    s.params.all PTy.memFree = true ∧ inMem s.result = false := by
  simp only [Meta.memFree, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h₁, h₂⟩ := h s hs
  exact ⟨List.all_eq_true.mpr h₁, h₂⟩

/-- **The canonical convention is the C convention** on worlds without
results in memory, for a module whose `realloc` agrees with its allocator. -/
theorem canonSpec_eq_spec {r : String} (h : md.thinOk = true) (hR : ReallocAgrees M md r) :
    canonSpec M md.world r = md.spec M := by
  funext name vs
  simp only [canonSpec, Meta.spec]
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    exact canonCall_specCall M md s (thinOk_mem md h (find?_mem md hf))
      (lowerParams_realloc M md hR s.params) vs

/-- The same on memory-free worlds, for any `realloc`. -/
theorem canonSpec_eq_spec_memFree (r : String) (h : md.memFree = true) :
    canonSpec M md.world r = md.spec M := by
  funext name vs
  simp only [canonSpec, Meta.spec]
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    obtain ⟨hp, hs⟩ := memFree_mem md h (find?_mem md hf)
    exact canonCall_specCall M md s hs (fun vs => lowerParams_memFree M md _ s.params vs hp) vs

theorem recognizeThin_eq {r : String} {c : Comp} (h : recognizeThin md r = some c) :
    md.thinOk = true ∧ c = thinComp md r := by
  unfold recognizeThin at h
  split at h
  · next hk => exact ⟨hk, (Option.some.inj h).symm⟩
  · cases h

/-- **Agreement of thin-wrapper recognition with the monadic construction**:
a recognized thin wrapper of a conforming module whose `realloc` agrees with
its allocator behaves as `wrap md`, on every export. -/
theorem recognizeThin_agrees {r : String} {c : Comp} (h : recognizeThin md r = some c)
    (hC : md.Conforms M) (hR : ReallocAgrees M md r) :
    c.callExport M = (wrap md).callExport M := by
  obtain ⟨hk, rfl⟩ := recognizeThin_eq md h
  funext name vs
  rw [thinComp_callExport, canonSpec_eq_spec M md hk hR, wrap_correct M md hC]

/-- The same on memory-free worlds, with no condition on the `realloc`. -/
theorem recognizeThin_agrees_memFree {r : String} {c : Comp} (h : recognizeThin md r = some c)
    (hm : md.memFree = true) (hC : md.Conforms M) :
    c.callExport M = (wrap md).callExport M := by
  obtain ⟨-, rfl⟩ := recognizeThin_eq md h
  funext name vs
  rw [thinComp_callExport, canonSpec_eq_spec_memFree M md r hm, wrap_correct M md hC]

/-- Memory-free worlds are recognized. -/
theorem thinOk_of_memFree (h : md.memFree = true) : md.thinOk = true := by
  simp only [Meta.thinOk, List.all_eq_true]
  intro s hs
  simp [(memFree_mem md h hs).2]

end Silmaril.Wasm.Jco
