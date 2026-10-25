module

public import Silmaril.Wasm.Binaryen.CtxRefines
public import Silmaril.Wasm.Binaryen.Contracts

@[expose] public section

/-! # Function-table uniformity: replacing bodies

`replaceBodies` replaces the bodies of a set `D` of defined functions at once.
Because `SeqRefines` quantifies over **every** module, its hypotheses already
hold in the modules where the other functions of `D` have been replaced, so
recursion through replaced functions is handled (the hypothesis is uniform in
the function table). The proof replaces one function at a time and chains
`ExportRefines.trans`.

This is the Core 3.0 counterpart of a separate congruence development (not included in this package)'s
`moduleRefines_replaceOn`. The per-function step is an instance of the
contextual hypothesis itself; no new operational store simulation is needed.
Universal typing preservation supplies validity of every partial replacement.
`SoundPass.mapBodies` packages the result for composable pass pipelines, and
`SoundPass.foldBodies` is a concrete example certified by equal lowerings.
See `Silmaril.Wasm.Binaryen.Equiv` for the distinct obligations of linking and
operational-to-contextual bridges.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

/-- Replace the bodies of the defined functions in `D` (relative indices). -/
def BModule.replace (m : BModule) (D : List Nat) (spec : Nat → List BExpr) : BModule :=
  { m with funcs := m.funcs.mapIdx fun g f => if g ∈ D then { f with body := spec g } else f }

/-- Apply a body transformation to every function. -/
def BModule.mapBodies (T : List BExpr → List BExpr) (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := T f.body } }

/-- The typing of defined function `g`'s body, read off the lowered module's
validation: some context and instruction type at which it is typed. -/
def BModule.BodyTyped (m : BModule) (g : Nat) (C : Context) (it : InstrType) : Prop :=
  ∃ b, m.body? g = some b ∧ SeqOk C b it

namespace BodyReplacement

/-- Lookup after a body update, including an out-of-range update. -/
theorem getElem?_modifyAt {α : Type} (F : α → α) (g i : Nat) (fs : List α) :
    (modifyAt F g fs)[i]? = if i = g then (fs[i]?).map F else fs[i]? := by
  induction fs generalizing g i with
  | nil => simp [modifyAt]
  | cons f fs ih =>
    cases g <;> cases i <;> simp [modifyAt, ih]

/-- The empty simultaneous replacement is the identity. -/
theorem replace_nil (m : BModule) (spec : Nat → List BExpr) : m.replace [] spec = m := by
  change { m with funcs := _ } = { m with funcs := m.funcs }
  apply congrArg (fun fs => ({ m with funcs := fs } : BModule))
  apply List.ext_getElem?
  intro i
  simp

/-- Restoring a function's existing body is the identity. -/
theorem withBody_self {m : BModule} {g : Nat} {b : List BExpr}
    (hb : m.body? g = some b) : m.withBody g b = m := by
  change { m with funcs := _ } = { m with funcs := m.funcs }
  apply congrArg (fun fs => ({ m with funcs := fs } : BModule))
  apply List.ext_getElem?
  intro i
  rw [getElem?_modifyAt]
  split
  · subst i
    cases he : m.funcs[g]? with
    | none => simp [BModule.body?, he] at hb
    | some f =>
      have hf : f.body = b := by simpa [BModule.body?, he] using hb
      cases hf
      rfl
  · rfl

/-- A simultaneous replacement is one update after the remaining replacements. -/
theorem replace_cons (m : BModule) (g : Nat) (D : List Nat) (spec : Nat → List BExpr) :
    m.replace (g :: D) spec = (m.replace D spec).withBody g (spec g) := by
  change { m with funcs := _ } = { m with funcs := _ }
  apply congrArg (fun fs => ({ m with funcs := fs } : BModule))
  apply List.ext_getElem?
  intro i
  simp only [BModule.replace, getElem?_modifyAt, List.getElem?_mapIdx]
  by_cases hi : i = g
  · subst i
    by_cases hg : g ∈ D <;> cases he : m.funcs[g]? <;> simp_all
  · cases he : m.funcs[i]? <;> simp_all

/-- Duplicate indices do not create extra replacements. -/
theorem replace_cons_of_mem (m : BModule) {g : Nat} {D : List Nat}
    (hg : g ∈ D) (spec : Nat → List BExpr) : m.replace (g :: D) spec = m.replace D spec := by
  unfold BModule.replace
  congr 1
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro i hi
  by_cases he : i = g
  · subst i; simp [hg]
  · simp [he]

/-- Bodies outside the selected set are unchanged. -/
theorem body?_replace (m : BModule) {g : Nat} {D : List Nat} (hg : g ∉ D)
    (spec : Nat → List BExpr) : (m.replace D spec).body? g = m.body? g := by
  simp [BModule.body?, BModule.replace, hg]

/-- A missing function cannot be replaced. -/
theorem replace_cons_of_none (m : BModule) {g : Nat} (D : List Nat)
    (spec : Nat → List BExpr) (hg : m.body? g = none) :
    m.replace (g :: D) spec = m.replace D spec := by
  have hf : m.funcs[g]? = none := by
    cases he : m.funcs[g]? <;> simp_all [BModule.body?]
  unfold BModule.replace
  congr 1
  apply List.ext_getElem?
  intro i
  by_cases hi : i = g
  · subst i; simp [hf]
  · simp [hi]

/-- Universal typing preservation supplies validity at every partial replacement. -/
theorem replace_ok (T : List BExpr → List BExpr)
    (hT : ∀ C it es, SeqOk C es it → SeqOk C (T es) it)
    (m : BModule) (hm : m.Ok) (D : List Nat) :
    (m.replace D (fun g => T ((m.body? g).getD []))).Ok := by
  induction D with
  | nil => simpa only [replace_nil] using hm
  | cons g D ih =>
    by_cases hg : g ∈ D
    · simpa [replace_cons_of_mem m hg] using ih
    · cases hb : m.body? g with
      | none => simpa [replace_cons_of_none m D _ hb] using ih
      | some b =>
        have old : (m.replace D (fun j => T ((m.body? j).getD []))).body? g = some b := by
          rw [body?_replace m hg, hb]
        rw [replace_cons]
        have hr := withBody_self old
        have hv : ((m.replace D (fun j => T ((m.body? j).getD []))).withBody g b).Ok :=
          hr.symm ▸ ih
        have ht : TyRepl (BExpr.lowerList b) (BExpr.lowerList (T b)) :=
          fun C it _ h => hT C it b h
        simpa [hb] using ok_transfer ht hv

/-- Every actual body of a valid module has a typing. -/
theorem body_typed {m : BModule} (hm : m.Ok) {g : Nat} {b : List BExpr}
    (hb : m.body? g = some b) : ∃ C it, SeqOk C b it := by
  have hr := withBody_self hb
  have hg : g < m.funcs.length := by
    cases he : m.funcs[g]? with
    | none => simp [BModule.body?, he] at hb
    | some f => exact (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨C, it, _, ht⟩ := funcBody_typed hg (hr.symm ▸ hm)
  exact ⟨C, it, ht⟩

/-- Replacing every defined body is `mapBodies`. -/
theorem replace_range (m : BModule) (T : List BExpr → List BExpr) :
    m.replace (List.range m.funcs.length) (fun g => T ((m.body? g).getD [])) = m.mapBodies T := by
  change { m with funcs := _ } = { m with funcs := _ }
  apply congrArg (fun fs => ({ m with funcs := fs } : BModule))
  apply List.ext_getElem?
  intro i
  cases he : m.funcs[i]? with
  | none => simp [he]
  | some f =>
    have hi : i < m.funcs.length := (List.getElem?_eq_some_iff.mp he).1
    simp_all [BModule.body?]

end BodyReplacement

/-- **Replacing bodies.** If each new body contextually refines the old one at the
old one's typing, and every partially replaced module is valid, the replaced
module export-refines the original. -/
theorem replaceBodies {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    (hR : ∀ b, R b b) (hRt : ∀ x y z, R x y → R y z → R x z)
    (m : BModule) (D : List Nat) (spec : Nat → List BExpr)
    (h : ∀ g ∈ D, ∃ C it b, m.body? g = some b ∧ SeqRefines R P C it (spec g) b)
    (hok : ∀ D', D' ⊆ D → (m.replace D' spec).Ok)
    {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    ExportRefines R P host (m.replace D spec).lower m.lower := by
  revert h hok
  induction D with
  | nil =>
    intro _ _
    simpa only [BodyReplacement.replace_nil] using (ExportRefines.refl hR m.lower : ExportRefines R P host m.lower m.lower)
  | cons g D ih =>
    intro h hok
    have hd := ih (fun j hj => h j (List.mem_cons_of_mem g hj))
      (fun D' hD' => hok D' (fun j hj => List.mem_cons_of_mem g (hD' hj)))
    by_cases hg : g ∈ D
    · simpa [BodyReplacement.replace_cons_of_mem m hg] using hd
    · obtain ⟨C, it, b, hb, hs⟩ := h g List.mem_cons_self
      have hold : (m.replace D spec).body? g = some b := by
        rw [BodyReplacement.body?_replace m hg, hb]
      have he := BodyReplacement.withBody_self hold
      have hv := hok D (fun j hj => List.mem_cons_of_mem g hj)
      have hv' := hok (g :: D) (fun _ hj => hj)
      rw [BodyReplacement.replace_cons] at hv' ⊢
      have step := hs.2.2 host (m.replace D spec) g .hole hhost
        (by simpa [BCtx.plug] using hv') (by simpa [BCtx.plug, he] using hv)
      have hs' : ExportRefines R P host ((m.replace D spec).withBody g (spec g)).lower
          (m.replace D spec).lower := by simpa [BCtx.plug, he] using step
      exact hs'.trans hRt hd

/-- **Whole-module passes.** A body transformation that contextually refines its
input at every typing, and preserves validity, refines on whole modules. -/
theorem mapBodies_sound {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    (hR : ∀ b, R b b) (hRt : ∀ x y z, R x y → R y z → R x z)
    {T : List BExpr → List BExpr}
    (hT : ∀ C it es, SeqOk C es it → SeqRefines R P C it (T es) es)
    (hvalid : ∀ m : BModule, m.Ok → (m.mapBodies T).Ok)
    {m : BModule} (hm : m.Ok) {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    ExportRefines R P host (m.mapBodies T).lower m.lower := by
  let spec := fun g => T ((m.body? g).getD [])
  have hpartial : ∀ D : List Nat, (m.replace D spec).Ok :=
    BodyReplacement.replace_ok T (fun C it es h => (hT C it es h).1) m hm
  have hlocal : ∀ g ∈ List.range m.funcs.length,
      ∃ C it b, m.body? g = some b ∧ SeqRefines R P C it (spec g) b := by
    intro g hg
    have hlt : g < m.funcs.length := List.mem_range.mp hg
    have hb : m.body? g = some m.funcs[g].body := by
      simp [BModule.body?, List.getElem?_eq_getElem hlt]
    obtain ⟨C, it, ht⟩ := BodyReplacement.body_typed hm hb
    exact ⟨C, it, _, hb, by simpa [spec, hb] using hT C it _ ht⟩
  have result := replaceBodies hR hRt m (List.range m.funcs.length) spec hlocal
    (fun D _ => hpartial D) host hhost
  -- `hvalid` is retained for API compatibility; local contextual refinement
  -- already proves validity of all partial replacements, including the endpoint.
  have _endpoint := hvalid m hm
  simpa [spec, BodyReplacement.replace_range] using result

/-- Local contextual refinement gives a composable pass contract. Partial
validity, and hence endpoint validity, follows from the typing component. -/
theorem SoundPass.mapBodies {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    (hR : Contract.Rel R) {T : List BExpr → List BExpr}
    (hT : ∀ C it es, SeqOk C es it → SeqRefines R P C it (T es) es)
    {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    SoundPass R P host (BModule.mapBodies T) := by
  have hvalid : ∀ m : BModule, m.Ok → (m.mapBodies T).Ok := by
    intro m hm
    have hv := BodyReplacement.replace_ok T (fun C it es h => (hT C it es h).1)
      m hm (List.range m.funcs.length)
    simpa [BodyReplacement.replace_range] using hv
  exact fun m hm => ⟨hvalid m hm, mapBodies_sound hR.refl hR.trans hT hvalid hm host hhost⟩

/-- Example for the composable pass API: operand folding, certified locally
by equality of lowerings, is a sound whole-module pass for every preorder contract. -/
theorem SoundPass.foldBodies {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    (hR : Contract.Rel R) (arity : Instr → Option Nat)
    {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    SoundPass R P host (BModule.mapBodies (fold arity)) := by
  apply SoundPass.mapBodies hR (host := host) (hhost := hhost)
  intro C it es ht
  refine ⟨?_, ht, ?_⟩
  · simpa [SeqOk, lowerList_fold] using ht
  · intro H host m g K _ _ _
    rw [withBody_lower_congr m g (K.lowerList_plug_eq (lowerList_fold arity es))]
    exact ExportRefines.refl hR.refl _

end Silmaril.Wasm.Binaryen
