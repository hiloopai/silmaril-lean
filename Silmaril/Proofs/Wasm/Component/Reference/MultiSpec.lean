module

public import Silmaril.Proofs.Wasm.Component.Reference.CallTyping
public import Silmaril.Proofs.Wasm.Component.Reference.CoreRun

/-!
# Export calls at later Core stores

The canonical-ABI specification of an export call at an arbitrary Core store `s` of the
instance `I` (`specAt`), returned calls with the store they leave (`RetAt`), and sequences of
returned calls (`SeqSpec`). The typing facts of `CallTyping` hold at every well-formed store
(`run_typed_at`, `run_no_callout_at`), and returned calls keep the store well formed
(`RetAt.wellFormed`, through a complete activation of the instance's strategy).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-! ## The specification at a store (defined in the `Sound` header) -/

export Silmaril.Wasm.Component.Reference (coreAt specAt RetAt SeqSpec)

/-- At the instance's store, `specAt` is `exportSpec`. -/
theorem specAt_store {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    {x : SimpleExport} {vs : List Silmaril.Wasm.Component.Val} {b : Outcome}
    (h : b ∈ specAt P c I x vs I.store) : b ∈ exportSpec P c x vs := by
  unfold specAt at h
  unfold exportSpec
  cases hl : checkLower x.ty.params vs with
  | none => rw [hl] at h; exact h
  | some xs =>
    rw [hl] at h
    rcases h with ⟨r, hr, rfl⟩ | ⟨rfl, hd⟩
    · exact .inl ⟨r, ⟨I, hI, hr⟩, rfl⟩
    · exact .inr ⟨rfl, I, hI, hd⟩

/-! ## Typing at well-formed stores -/

/-- The closed-program operation of a typed call of core export `k`. -/
noncomputable def opAt {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) : I.F.Op :=
  ⟨Fin.cast (by rw [hI.2.2, List.length_map]) ⟨k, hk⟩,
    ⟨xs.map ofFlat, by
      have hj : I.exports.get (Fin.cast (by rw [hI.2.2, List.length_map]) ⟨k, hk⟩) =
          fnOf m.exports[k].2 := by
        simp only [List.get_eq_getElem, Fin.val_cast, hI.2.2, List.getElem_map]
      have hp : (I.exports.get (Fin.cast (by rw [hI.2.2, List.length_map]) ⟨k, hk⟩)).params =
          xs.map fun x => .num x.type := by
        rw [hj]
        show m.exports[k].2.params.map _ = _
        rw [← hxs, List.map_map]
        rfl
      exact hp ▸ forall₂_hasVal_ofFlat xs⟩⟩

theorem opAt_addr {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) :
    I.addr (opAt hI hk hxs).1 = I.addrs.getD k 0 := rfl

theorem opAt_args {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) :
    (opAt hI hk hxs).2.1 = xs.map ofFlat := rfl

theorem opAt_type {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) :
    I.exports.get (opAt hI hk hxs).1 = fnOf m.exports[k].2 := by
  simp only [opAt, List.get_eq_getElem, Fin.val_cast, hI.2.2, List.getElem_map]

/-- The Core run of a typed call at a well-formed store answers. -/
theorem answer_at {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {s : Store Nat} (hw : I.WellFormed s) {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) {c' : Config Nat} {r : Result}
    (run : Steps P Det.noHost (invoke s (I.addrs.getD k 0) (xs.map ofFlat)) c')
    (final : c'.code = r.toAdmin) :
    ∃ w, Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get (opAt hI hk hxs).1) r = some w := by
  have run' : Steps P (Silmaril.Wasm.Game.hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
      (invoke s (I.addr (opAt hI hk hxs).1) (opAt hI hk hxs).2.1) c' := by
    rw [hostOf_nil hI.2.1]
    exact run
  obtain ⟨w, hw', -⟩ := Silmaril.Wasm.Game.ScalarInstance.answer_of_run hw
    (throwsBelow_silent I _) run' final
  exact ⟨w, hw'⟩

/-- **Typed results at a well-formed store.** -/
theorem run_typed_at {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {s : Store Nat} (hw : I.WellFormed s) {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) {c' : Config Nat}
    {vs : List Execution.Core.Val}
    (run : Steps P Det.noHost (invoke s (I.addrs.getD k 0) (xs.map ofFlat)) c')
    (final : c'.code = vals vs) {fvs : List Silmaril.Wasm.Execution.Runtime.Value}
    (hf : vs.mapM toFlat? = some fvs) : fvs.map (·.type) = m.exports[k].2.results := by
  obtain ⟨w, hw'⟩ := answer_at hI hw hk hxs run (r := .values vs) final
  have ht : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
      (I.exports.get (opAt hI hk hxs).1).results vs := by
    unfold Silmaril.Wasm.Game.Answer.ofResult? at hw'
    dsimp only at hw'
    split_ifs at hw' with ht
    exact ht
  rw [opAt_type] at ht
  exact toFlat?_types _ vs fvs ht hf

/-- **No callout at a well-formed store.** -/
theorem run_no_callout_at {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {s : Store Nat} (hw : I.WellFormed s) {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) {c' : Config Nat}
    (run : Steps P Det.noHost (invoke s (I.addrs.getD k 0) (xs.map ofFlat)) c') :
    decompose? c'.store c'.code = none := by
  have run' : Steps P (Silmaril.Wasm.Game.hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
      (invoke s (I.addr (opAt hI hk hxs).1) (opAt hI hk hxs).2.1) c' := by
    rw [hostOf_nil hI.2.1]
    exact run
  rcases Silmaril.Wasm.Game.ScalarInstance.progress_hostOf hw (throwsBelow_silent I _) run' with
    ⟨r, hr⟩ | ⟨c'', hs⟩
  · rw [hr]
    exact Silmaril.Wasm.Binaryen.LinkBehaviours.decompose?_result r
  · rw [hostOf_nil hI.2.1] at hs
    exact decompose?_none_of_noRedex (Step.noRedex hs)

/-! ## Well-formedness after a returned call -/

variable {H : Type}

/-- Host-free thread steps commute with renaming the host type. -/
theorem internalP_mapH (g : H → Nat) {x y : Store H × Thread}
    (h : Silmaril.Wasm.Game.InternalP P x y) :
    Silmaril.Wasm.Game.InternalP P (Store.mapH g x.1, x.2) (Store.mapH g y.1, y.2) := by
  obtain ⟨f', code', hy, hs⟩ := h
  refine ⟨f', code', hy, ?_⟩
  have hc : Config.mapH g (x.2.config x.1) = x.2.config (Store.mapH g x.1) := by
    cases x.2 with
    | pending a args => exact invoke_mapH g _ _ _
    | active f code => rfl
  have hs' := Step.mapH g hs
  rw [hc] at hs'
  exact hs'

/-- Host-free thread runs commute with renaming the host type. -/
theorem reach_mapH (g : H → Nat) {x y : Store H × Thread}
    (h : Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) x y) :
    Silmaril.Wasm.Game.Reach P (Store.mapH g x.1, x.2) (Store.mapH g y.1, y.2) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (internalP_mapH g hs)

/-- **A returned call keeps the store well formed.** -/
theorem _root_.Silmaril.Wasm.Component.Reference.RetAt.wellFormed {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    {x : SimpleExport} (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    {vs : List Silmaril.Wasm.Component.Val} {s s' : Store Nat} {ws : List Silmaril.Wasm.Component.Val}
    (hw : I.WellFormed s) (h : RetAt P c I x vs s ws s') : I.WellFormed s' := by
  obtain ⟨nm, hc⟩ := hcore
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hc
  obtain ⟨t', cvs, ys, run, final, -, -⟩ := h.run
  have hxs : (lowerArgs x.ty.params vs).map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact lowerList_types _ _ h.typed
  have steps : Steps P Det.noHost (invoke s (I.addrs.getD x.core 0)
      ((lowerArgs x.ty.params vs).map ofFlat)) (t'.config s') :=
    internalP_steps (H := Nat) run
  obtain ⟨w, hw'⟩ := answer_at hI hw hk hxs steps (r := .values cvs) final
  have hpath : I.Activation P s [.inr (.ask (opAt hI hk hxs)),
      .inr (.ans (opAt hI hk hxs) w)] s' :=
    .cons (.call s _) (.cons (.oret run final hw') (.nil _))
  refine (Silmaril.Wasm.Game.ScalarInstance.WellFormed.activation hw ?_ hpath).1
  intro e v hm
  simp at hm

export Silmaril.Wasm.Component.Reference (RetAt.wellFormed)

end Silmaril.Proofs.Wasm.Component.Reference
