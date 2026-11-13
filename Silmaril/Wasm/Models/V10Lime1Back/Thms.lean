module

public import Silmaril.Proofs.Wasm.Models.V10Lime1Back.Refute
public import Silmaril.Proofs.Wasm.Models.V10Lime1Back.Runs

/-!
# The converse of `v10own → lime1own`

**Refutation.** The converse of `V10Lime1.v10Lime1Emb` (Lime1 behaviours of the image point are
1.0 behaviours) is false on the domain of `v10own`. That domain does not restrict the types of
the store's Wasm functions, and 1.0's `invokeWasm` asks `ft.results.length ≤ 1` where Lime1's
does not. At `cxPt` (one function `[] → [i32 i32]`, the empty host, in the domain by `cx_dom`):

* the 1.0 behaviours of calling address `0` are empty (`v1_behaviours_empty`, from `v1_stuck`);
* Lime1 returns `[0, 0]` (`lime1_returns`).

* **`converse_false`**: `¬ ∀ p, dom p → ∀ c, obs_lime1 (ptL p) c ⊆ obs_v10 p c`;
* **`no_eq_or_sup`**: so no embedding `v10own → lime1own` with `v10Lime1Emb`'s point, call and
  readback maps has direction `eq` or `sup`.

**Restatement, proved.** `Store1` (every Wasm function of the store has at most one result) is
the missing restriction.

* **`stepBack_holds`**: the backward lock-step simulation `StepBack` (`Defs`) holds at every 1.0
  host. A Lime1 step under the transported host from the image of a `Store1` configuration is the
  image of a 1.0 step (`Silmaril.Proofs.Wasm.Models.V10Lime1Back.step_back`: `pure_back` for the
  pure rules, inversion of `codeToLime` for the code, `store_injective` for host calls,
  `Store1` for `invokeWasm`, no preimage for `memory.copy`/`memory.fill`);
* `behaviours_back`: so on `Store1` points of the domain, the Lime1 behaviours of `ptL p` are 1.0
  behaviours (runs by `steps_back`, divergence by `diverges_back`; 1.0 steps keep functions,
  so `Store1` is invariant);
* **`obs_eq`**: on those points the observations are equal;
* **`v10Lime1EmbEq H : (v10own1 H).Emb (lime1own H)`**, direction **`eq`**, where `v10own1` is
  `v10own` with `Store1` added to the domain. It has `v10Lime1Emb`'s maps
  (`v10Lime1EmbEq_maps`). It is not conservative: validity is still not reflected
  (`v10Lime1EmbEq_not_conservative`, multi-value).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V10Lime1Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models
open Silmaril.Proofs.Wasm.Models.V10Lime1Back (cx_dom v1_behaviours_empty lime1_returns zero32)

/-- The call of the refutation. -/
def cxCall : V10.Call := (⟨0⟩, [])

/-- Lime1 observes a return at the image point. -/
theorem cx_lime1_obs :
    (Behaviour.returns [zero32, zero32]).map Value.toCore ∈
      Lime1Core.obs (V10Lime1.ptL cxPt) cxCall :=
  ⟨by decide, _, lime1_returns _, rfl⟩

/-- 1.0 observes nothing. -/
theorem cx_v10_obs : V10.obs cxPt cxCall = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun b hb => ?_
  obtain ⟨-, b₀, hb₀, -⟩ := hb
  have hempty : Silmaril.Wasm.V1.Execution.behaviours cxHost cxStore ⟨0⟩ [] = ∅ :=
    v1_behaviours_empty cxHost
  have hb₁ : b₀ ∈ Silmaril.Wasm.V1.Execution.behaviours cxHost cxStore ⟨0⟩ [] := hb₀
  rw [hempty] at hb₁
  exact hb₁

/-- **Refutation: the converse of `v10Lime1Emb` fails on the domain of `v10own`.** -/
theorem converse_false :
    ¬ ∀ p : V10.Pt Unit, V10.dom p → ∀ c,
      Lime1Core.obs (V10Lime1.ptL p) c ⊆ V10.obs p c := fun h => by
  have hmem := h cxPt cx_dom cxCall cx_lime1_obs
  rw [cx_v10_obs] at hmem
  exact hmem

/-- **No embedding with `v10Lime1Emb`'s maps has direction `eq` or `sup`.** -/
theorem no_eq_or_sup (e : (V10.v10own Unit).Emb (Lime1Core.lime1own Unit))
    (hpt : e.pt = V10Lime1.ptL) (hcall : e.call = id) (hrb : e.readback = some) :
    e.dir = .sub := by
  rcases e with ⟨mod, valid, pt, call, readback, dom, dir, sat⟩
  subst hpt hcall hrb
  have hview : (Lime1Core.lime1own Unit).view some (V10Lime1.ptL cxPt) (id cxCall) =
      Lime1Core.obs (V10Lime1.ptL cxPt) cxCall := by
    ext o
    exact ⟨fun ⟨b, hb, hbo⟩ => Option.some.inj hbo ▸ hb, fun ho => ⟨o, ho, rfl⟩⟩
  have hs : dir.Holds (V10.obs cxPt cxCall) (Lime1Core.obs (V10Lime1.ptL cxPt) cxCall) :=
    (congrArg (EmbDir.Holds dir (V10.obs cxPt cxCall)) hview).mp (sat cxPt cx_dom cxCall)
  show dir = .sub
  have hsub : ¬ Lime1Core.obs (V10Lime1.ptL cxPt) cxCall ⊆ V10.obs cxPt cxCall := fun h => by
    have hmem : _ ∈ V10.obs cxPt cxCall := h cx_lime1_obs
    rw [cx_v10_obs] at hmem
    exact hmem
  cases dir with
  | sub => rfl
  | eq => exact absurd (fun _ hb => (show _ = _ from hs) ▸ hb) hsub
  | sup => exact absurd hs hsub

/-- **The backward lock-step simulation holds at every 1.0 host.** -/
theorem stepBack_holds {H : Type} (src : V10.OHost H) : StepBack src :=
  Silmaril.Proofs.Wasm.Models.V10Lime1Back.stepBack src

/-- **On `Store1` points of the domain, Lime1 and 1.0 observe the same.** -/
theorem obs_eq {H : Type} {p : V10.Pt H} (hp : V10.dom p) (h₁ : Store1 p.1) (c : V10.Call) :
    Lime1Core.obs (V10Lime1.ptL p) c = V10.obs p c := by
  ext b
  refine ⟨fun ⟨ha, b₀, hb₀, hb⟩ => ⟨?_, b₀,
    Silmaril.Proofs.Wasm.Models.V10Lime1Back.behaviours_back hp h₁ c.1 c.2 hb₀, ?_⟩,
    fun hb => V10Lime1.obs_sub hp c hb⟩
  · simpa [V10Lime1.ptL, V10.limeStore, Store.mapCode] using ha
  · rw [show V10.valCore = Value.toCore from funext V10Lime1.valCore_eq]
    exact hb

/-- `v10own` with `Store1` stores. -/
def v10own1 (H : Type) : WasmModel :=
  { V10.v10own H with dom := fun p => V10.dom p ∧ Store1 p.1 }

/-- **`v10own1 → lime1own` with equal observations.** -/
def v10Lime1EmbEq (H : Type) : (v10own1 H).Emb (Lime1Core.lime1own H) where
  mod := Silmaril.Wasm.V1.Module.toLime
  valid _ h := V10Lime1.v10_lime1_valid h
  pt := V10Lime1.ptL
  call c := c
  readback := some
  dom p hp := (V10Lime1.v10Lime1Emb H).dom p hp.1
  dir := .eq
  sat p hp c := by
    show {o | ∃ b ∈ Lime1Core.obs (V10Lime1.ptL p) c, some b = some o} = V10.obs p c
    rw [← obs_eq hp.1 hp.2 c]
    ext o
    exact ⟨fun ⟨b, hb, hbo⟩ => Option.some.inj hbo ▸ hb, fun ho => ⟨o, ho, rfl⟩⟩

theorem v10Lime1EmbEq_dir (H : Type) : (v10Lime1EmbEq H).dir = .eq := rfl

/-- It has the maps of `v10Lime1Emb`. -/
theorem v10Lime1EmbEq_maps (H : Type) :
    (v10Lime1EmbEq H).mod = (V10Lime1.v10Lime1Emb H).mod ∧
      (v10Lime1EmbEq H).pt = (V10Lime1.v10Lime1Emb H).pt :=
  ⟨rfl, rfl⟩

/-- It is not conservative: validity is not reflected (multi-value). -/
theorem v10Lime1EmbEq_not_conservative (H : Type) : ¬ (v10Lime1EmbEq H).Conservative :=
  fun h => V10Lime1.v10_lime1_valid_reflect_false (H := H) h.reflect

end Silmaril.Wasm.Models.V10Lime1Back

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Models.V10Lime1Back.converse_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1Back.converse_false

/-- info: 'Silmaril.Wasm.Models.V10Lime1Back.no_eq_or_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1Back.no_eq_or_sup

/-- info: 'Silmaril.Wasm.Models.V10Lime1Back.stepBack_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1Back.stepBack_holds

/-- info: 'Silmaril.Wasm.Models.V10Lime1Back.v10Lime1EmbEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1Back.v10Lime1EmbEq
