module

public import Silmaril.Wasm.SpecTec.Institution.Wasm20.Defs
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The SpecTec specification institution and the Wasm atlas: wasm-2.0 transitions

* `mem_stepModel20_iff`: the step facts of `stepModel20 B` are `SStepB (simEnv20 B)`.
* `tags_of_fires`, `not_firesRead_store`, `not_firesStep_store`: a `Step_read` or `Step` rule fires
  only at code whose top-level heads include every constructor its tag table forces; so the
  table, store and bulk-memory rules do not fire on the scalar fragment.
* `bwdPartsS`, `cfgInv_domS`, `bwd_scalar`: **the backward half on `DomS`, unconditionally**, at
  the spec's scalar builtins `Sim.Floats.floatIntB P` and every profile `P`, host and encoding.
* `bwd_of_rest3`: the backward half on all of `DomW`, conditional on `Sim20.Whole.BwdRestW3`.
* `toModelS`, `toModelSE`: transitions from the V2 step chart on `DomS` to
  `modelChart (stepModel20 (floatIntB P))`: universal sentences are preserved, existential ones
  reflected. `toModelW`, `toModelWE`: the same on `DomW`, given `BwdRestW3`.
* `v2_progress_nop`, `not_model_progress_nop`, `model_stuck_nop`, `not_v2_stuck_nop`,
  `not_fwd_progress`, `not_bwd_stuck`: the forward half fails at `nop nop` (a point of `DomS`) for
  every primitives `B`, so no transition with this point map preserves `progress` or reflects
  `stuckSen`; the two one-sided transitions are the best possible on these classes.
* `model_step_nop1`, `model_progress_nop1`: the model does have step facts on `DomS` (`nop` steps
  to the empty code), so the backward half is not vacuous.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Wasm20

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim (Fires cfgV dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn relRules ruleTags not_ruleBody_of_tags)
open Silmaril.Wasm.SpecTec.Sim20
open Silmaril.Wasm.SpecTec.Sim20.Whole
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (modelChart)

set_option maxRecDepth 100000

variable {H : Type}

/-- The step facts of `stepModel20 B` are the backend reading of the 2.0 script's `Step`. -/
theorem mem_stepModel20_iff (B : Builtins) (v w : Value) :
    (stepModel20 B).D "Step" "%~>%" [] (.tuple [v, w]) ↔ SStepB (simEnv20 B) v w :=
  Iff.rfl

/-! ## Rules that force a constructor the code lacks -/

/-- **A firing `Step_read` or `Step` rule forces only constructors among the code's heads**, by
the relation's tag table `T`. -/
theorem tags_of_fires {B : Builtins} {hn : H → String} {x : IL.Id} {T : List (List MixopS)}
    (hT : (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) x).map ruleTags = T)
    {i : Nat} {c : Config H} {w : Value}
    (hf : Fires (simEnv20 B) x i (.tuple [configV hn c, w])) :
    ∃ ts, T[i]? = some ts ∧ ∀ op ∈ ts, op ∈ c.code.map adminHead20 := by
  obtain ⟨t, rules, r, hrel, hr, hb⟩ := hf
  have hrules : rules.map ruleTags = T := by
    rw [← relRules_simEnv20 B] at hT
    simpa [relRules, hrel] using hT
  refine ⟨ruleTags r, by rw [← hrules, List.getElem?_map, hr]; rfl, fun op hop => ?_⟩
  by_contra hS
  exact not_ruleBody_of_tags (Or.inr ⟨_, _, rfl, tagsIn_heads c.code⟩) hop hS hb

/-- The constructors of `storeOp20` instructions. -/
def storeOpTags : List MixopS :=
  ["TABLE.GET", "TABLE.SET", "TABLE.SIZE", "TABLE.GROW", "TABLE.FILL", "TABLE.COPY", "TABLE.INIT",
   "ELEM.DROP", "STORE", "VSTORE", "VSTORE_LANE", "MEMORY.SIZE", "MEMORY.GROW", "MEMORY.FILL",
   "MEMORY.COPY", "MEMORY.INIT", "DATA.DROP"]

/-- An instruction outside `storeOp20` has a constructor outside `storeOpTags`. -/
theorem instrHead20_notStore {i : V2.Instr} (h : storeOp20 i = false) :
    instrHead20 i ∉ storeOpTags := by
  cases i <;> first | (simp only [instrHead20]; decide) | simp [storeOp20] at h

/-- An administrative instruction with no active `storeOp20` instruction has a constructor
outside `storeOpTags`. -/
theorem adminHead20_notStore {a : Admin} (h : NoStoreA a) : adminHead20 a ∉ storeOpTags := by
  cases a with
  | plain i => exact instrHead20_notStore (by simpa [NoStoreA] using h)
  | _ => simp only [adminHead20]; decide

/-- Every instruction of `NoStoreL` code satisfies `NoStoreA`. -/
theorem noStoreA_of_mem : ∀ {code : List Admin}, NoStoreL code → ∀ a ∈ code, NoStoreA a
  | [], _, _, ha => absurd ha List.not_mem_nil
  | _ :: _, h, a, ha => (List.mem_cons.1 ha).elim (fun e => e ▸ h.1) (noStoreA_of_mem h.2 a)

/-- No head of `NoStoreL` code is a `storeOpTags` constructor. -/
theorem heads_notStore {code : List Admin} (h : NoStoreL code) {op : MixopS}
    (hop : op ∈ storeOpTags) : op ∉ code.map adminHead20 := by
  intro hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
  exact adminHead20_notStore (noStoreA_of_mem h a ha) hop

/-- The `Step_read` rules left by `BwdRestW3`. -/
def restRead20 : List Nat := [10, 11, 13, 14, 16, 17, 18, 20, 21, 36, 38, 39, 41, 42, 43, 45, 46]

/-- The `Step` rules left by `BwdRestW3`. -/
def restStep20 : List Nat := [6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 20, 21]

/-- Each rule of `restRead20` forces a `storeOpTags` constructor. -/
theorem restRead20_tags : ∀ i ∈ restRead20, ∃ op ∈ readTags20[i]?.getD [], op ∈ storeOpTags := by
  decide +kernel

/-- Each rule of `restStep20` forces a `storeOpTags` constructor. -/
theorem restStep20_tags : ∀ i ∈ restStep20, ∃ op ∈ stepTags20[i]?.getD [], op ∈ storeOpTags := by
  decide +kernel

/-- The 47 `Step_read` rules: dead, `local.get`/`global.get`, inert, or left. -/
theorem read_cover : ∀ i < 47,
    i ∈ deadRead20 ∨ i ∈ [7, 8] ∨ i ∈ inertRead20 ∨ i ∈ restRead20 := by
  decide

/-- The 22 `Step` rules from `local.set` on: `local.set`/`global.set`, inert, or left. -/
theorem step_cover : ∀ i < 22, 4 ≤ i → i ∈ [4, 5] ∨ i ∈ inertStep20 ∨ i ∈ restStep20 := by
  decide

/-- `readTags20` has 47 entries. -/
theorem readTags20_length : readTags20.length = 47 := rfl

/-- `stepTags20` has 22 entries. -/
theorem stepTags20_length : stepTags20.length = 22 := rfl

/-- **The rules of `restRead20` do not fire on `NoStoreL` code.** -/
theorem not_firesRead_store {B : Builtins} {hn : H → String} {i : Nat} (hi : i ∈ restRead20)
    {c : Config H} (hq : NoStoreL c.code) {w : Value} :
    ¬ Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, w]) := by
  intro hf
  obtain ⟨ts, hts, hall⟩ := tags_of_fires (readTags20_eq) hf
  obtain ⟨op, hop, hst⟩ := restRead20_tags i hi
  rw [hts] at hop
  exact heads_notStore hq hst (hall op hop)

/-- **The rules of `restStep20` do not fire on `NoStoreL` code.** -/
theorem not_firesStep_store {B : Builtins} {hn : H → String} {i : Nat} (hi : i ∈ restStep20)
    {c : Config H} (hq : NoStoreL c.code) {w : Value} :
    ¬ Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) := by
  intro hf
  obtain ⟨ts, hts, hall⟩ := tags_of_fires (stepTags20_eq) hf
  obtain ⟨op, hop, hst⟩ := restStep20_tags i hi
  rw [hts] at hop
  exact heads_notStore hq hst (hall op hop)

/-- No `Step_read` rule exists beyond the 47. -/
theorem not_firesRead_ge {B : Builtins} {hn : H → String} {i : Nat} (hi : 47 ≤ i)
    {c : Config H} {w : Value} :
    ¬ Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, w]) := by
  intro hf
  obtain ⟨ts, hts, -⟩ := tags_of_fires (readTags20_eq) hf
  rw [List.getElem?_eq_none (by rw [readTags20_length]; omega)] at hts
  cases hts

/-- No `Step` rule exists beyond the 22. -/
theorem not_firesStep_ge {B : Builtins} {hn : H → String} {i : Nat} (hi : 22 ≤ i)
    {c : Config H} {w : Value} :
    ¬ Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) := by
  intro hf
  obtain ⟨ts, hts, -⟩ := tags_of_fires (stepTags20_eq) hf
  rw [List.getElem?_eq_none (by rw [stepTags20_length]; omega)] at hts
  cases hts

/-! ## The backward half on the scalar fragment -/

/-- `DomS` passes to the bodies of labels and frames. -/
theorem cfgInv_domS : CfgInv (DomS (H := H)) where
  label s f n cont body h :=
    ⟨cfgInv_goodW.label s f n cont body h.1, by simpa [DomS, NoStoreL, NoStoreA] using h.2⟩
  frame s f n fi body h :=
    ⟨cfgInv_goodW.frame s f n fi body h.1, by simpa [DomS, NoStoreL, NoStoreA] using h.2⟩

/-- `Step_read` backwards on `DomS`, at the spec's scalar builtins. -/
theorem readS {P : Profile} {hn : H → String} {i : Nat} {c : Config H} {w : List Value}
    (hg : DomS c)
    (hc : TypedSome (simEnv20 (Sim.Floats.floatIntB P)) instrsT20 (.list (adminsToV c.code)))
    (hw : TypedSome (simEnv20 (Sim.Floats.floatIntB P)) instrsT20 (.list w))
    (hf : Fires (simEnv20 (Sim.Floats.floatIntB P)) "Step_read" i (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  by_cases hlt : i < 47
  · rcases read_cover i hlt with hd | h78 | hi | hr
    · exact absurd hf (not_firesRead_dead hd hc hw)
    · rcases List.mem_pair.1 h78 with rfl | rfl
      · exact bwdRead_localGet hg.1 hf
      · exact bwdRead_globalGet hg.1 hf
    · exact absurd hf (not_fires_inert inertRead20_ok hi)
    · exact absurd hf (not_firesRead_store hr hg.2)
  · exact absurd hf (not_firesRead_ge (by omega))

/-- `Step` rules from `local.set` on, backwards on `DomS`, at the spec's scalar builtins. -/
theorem stepS {P : Profile} {host : HostSemantics H} {hn : H → String} {i : Nat} (h4 : 4 ≤ i)
    {c : Config H} {w : Value} (hg : DomS c)
    (hf : Fires (simEnv20 (Sim.Floats.floatIntB P)) "Step" i (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  by_cases hlt : i < 22
  · rcases step_cover i hlt h4 with h45 | hi | hr
    · rcases List.mem_pair.1 h45 with rfl | rfl
      · exact bwdStep_localSet hg.1 hf
      · exact bwdStep_globalSet hg.1 hf
    · exact absurd hf (not_fires_inert inertStep20_ok hi)
    · exact absurd hf (not_firesStep_store hr hg.2)
  · exact absurd hf (not_firesStep_ge (by omega))

/-- **Every per-rule obligation holds on `DomS`**, at the spec's scalar builtins. -/
theorem bwdPartsS (P : Profile) (host : HostSemantics H) (hn : H → String) :
    BwdPartsG DomS (Sim.Floats.floatIntB P) hn P host where
  pure _ _ _ hg hc hw hf :=
    pure_bwdW (Sim.Floats.intB_floatIntB P) (Sim.Floats.floatB_floatIntB P) hg.1 hc hw hf
  read _ _ _ hg hc hw hf := readS hg hc hw hf
  step _ h4 _ _ hg hf := stepS h4 hg hf

/-- **The backward half on the scalar fragment, unconditionally**: every step of the wasm-2.0
script under the backend reading at the spec's scalar builtins, from the image of a `DomS`
configuration, is the image of a V2 step. No typing, injectivity or finiteness hypothesis. -/
theorem bwd_scalar (P : Profile) (host : HostSemantics H) (hn : H → String) {c : Config H}
    (hc : DomS c) {w : Value}
    (hs : SStepB (simEnv20 (Sim.Floats.floatIntB P)) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step P host c c' :=
  backward20G_of_parts (bwdPartsS P host hn) cfgInv_domS c w hc hs

/-- **The backward half on all of `DomW`, from `BwdRestW3`** (the obligations `Sim20.Whole` leaves
open). -/
theorem bwd_of_rest3 {P : Profile} {host : HostSemantics H} {hn : H → String}
    (R : BwdRestW3 (Sim.Floats.floatIntB P) hn P host) {c : Config H} (hc : DomW c) {w : Value}
    (hs : SStepB (simEnv20 (Sim.Floats.floatIntB P)) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step P host c c' :=
  backward20G_of_parts (bwdPartsG_of_restW (Sim.Floats.intB_floatIntB P)
    (Sim.Floats.floatB_floatIntB P) (bwdRestW_of_rest2 (bwdRestW2_of_rest3 R))) cfgInv_goodW c w hc hs

/-! ## Transitions -/

section Trans

variable {Pt : Type} {Pt' : Type} {C : Type} {C' : Type} {B : Type}
  {dom : Pt → Prop} {dom' : Pt' → Prop} {obs : Pt → C → Set B} {obs' : Pt' → C' → Set B}

/-- **Target observations are source observations**: the target reflects existential sentences
(a witness in the target is a witness in the source). The dual of `BTrans.ofSupsetUniv`. -/
def ofSupsetExist (f : Pt → Pt') (σ : C → C') (hdom : ∀ p, dom p → dom' (f p))
    (h : ∀ p, dom p → ∀ c, obs' (f p) (σ c) ⊆ obs p c) :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls := BSen.Existential
  dir := .reflects
  dom_pt := hdom
  sat p s hp hs := ⟨fun e => absurd e (by decide), fun _ ht =>
    BSen.sat_of_subset_exist (h p hp) hs ((BSen.sat_rename σ _ s).1 ht)⟩

end Trans

/-- On `DomS`, the step facts of `stepModel20 (floatIntB P)` are V2 observations. -/
theorem model_subset_v2 (P : Profile) (host : HostSemantics H) (hn : H → String) :
    ∀ c, DomS c → ∀ u : Unit,
      {w | (stepModel20 (Sim.Floats.floatIntB P)).D "Step" "%~>%" [] (.tuple [configV hn c, w])} ⊆
        v2Obs P host hn c u := by
  intro c hc _ w hw
  obtain ⟨c', rfl, hs⟩ := bwd_scalar P host hn hc hw
  exact ⟨c', hs, rfl⟩

/-- **The wasm-2.0 transition for universal sentences**: from the V2 step chart on `DomS` to the
step chart of `stepModel20 (floatIntB P)`; a universal sentence true in V2 is true in the model. -/
noncomputable def toModelS (P : Profile) (host : HostSemantics H) (hn : H → String) :
    Transition (v2Chart P host hn DomS) (modelChart (stepModel20 (Sim.Floats.floatIntB P))) :=
  BTrans.ofSupsetUniv (configV hn) id (fun _ _ => trivial) (model_subset_v2 P host hn)

/-- **The wasm-2.0 transition for existential sentences**: an existential sentence true in the
model is true in V2. -/
noncomputable def toModelSE (P : Profile) (host : HostSemantics H) (hn : H → String) :
    Transition (v2Chart P host hn DomS) (modelChart (stepModel20 (Sim.Floats.floatIntB P))) :=
  ofSupsetExist (configV hn) id (fun _ _ => trivial) (model_subset_v2 P host hn)

/-- On `DomW`, given `BwdRestW3`, the step facts of the model are V2 observations. -/
theorem model_subset_v2W {P : Profile} {host : HostSemantics H} {hn : H → String}
    (R : BwdRestW3 (Sim.Floats.floatIntB P) hn P host) :
    ∀ c, DomW c → ∀ u : Unit,
      {w | (stepModel20 (Sim.Floats.floatIntB P)).D "Step" "%~>%" [] (.tuple [configV hn c, w])} ⊆
        v2Obs P host hn c u := by
  intro c hc _ w hw
  obtain ⟨c', rfl, hs⟩ := bwd_of_rest3 R hc hw
  exact ⟨c', hs, rfl⟩

/-- `toModelS` on all of `DomW`, **conditional** on `BwdRestW3`. -/
noncomputable def toModelW {P : Profile} {host : HostSemantics H} {hn : H → String}
    (R : BwdRestW3 (Sim.Floats.floatIntB P) hn P host) :
    Transition (v2Chart P host hn DomW) (modelChart (stepModel20 (Sim.Floats.floatIntB P))) :=
  BTrans.ofSupsetUniv (configV hn) id (fun _ _ => trivial) (model_subset_v2W R)

/-- `toModelSE` on all of `DomW`, **conditional** on `BwdRestW3`. -/
noncomputable def toModelWE {P : Profile} {host : HostSemantics H} {hn : H → String}
    (R : BwdRestW3 (Sim.Floats.floatIntB P) hn P host) :
    Transition (v2Chart P host hn DomW) (modelChart (stepModel20 (Sim.Floats.floatIntB P))) :=
  ofSupsetExist (configV hn) id (fun _ _ => trivial) (model_subset_v2W R)

/-- **The transitions, stated directly**: on `DomS`, a universal sentence true in V2 at `c` is
true in the model at the image of `c`, and an existential sentence true in the model is true in
V2. -/
theorem sat_univ_exist (P : Profile) (host : HostSemantics H) (hn : H → String) {c : Config H}
    (hc : DomS c) {s : BSen Unit Value} :
    (s.Universal → (v2Chart P host hn DomS).Sat c s →
      (modelChart (stepModel20 (Sim.Floats.floatIntB P))).Sat (configV hn c) s) ∧
    (s.Existential → (modelChart (stepModel20 (Sim.Floats.floatIntB P))).Sat (configV hn c) s →
      (v2Chart P host hn DomS).Sat c s) :=
  ⟨fun hs hv => BSen.sat_of_subset_univ (model_subset_v2 P host hn c hc) hs hv,
   fun hs hm => BSen.sat_of_subset_exist (model_subset_v2 P host hn c hc) hs hm⟩

/-! ## The forward half fails at `nop nop` -/

/-- `nop nop` is in the scalar fragment. -/
theorem domS_nopCfg : DomS (nopCfg (H := H)) := by
  simp [DomS, DomW, nopCfg, CvtOkL, CvtOkA, NoVecL, NoVecA, ResOkL, ResOkA, InstrResOk, NoStoreL,
    NoStoreA, storeOp20, vecOp20]

/-- V2 can step from `nop nop`. -/
theorem v2_progress_nop (P : Profile) (host : HostSemantics H) (hn : H → String)
    (D : Config H → Prop) : (v2Chart P host hn D).Sat nopCfg progress :=
  ⟨_, ⟨_, step_nopNop P host {} {}, rfl⟩, trivial⟩

/-- No model `stepModel20 B` can step from the image of `nop nop`. -/
theorem not_model_progress_nop (B : Builtins) (hn : H → String) :
    ¬ (modelChart (stepModel20 B)).Sat (configV hn nopCfg) progress := by
  rintro ⟨w, hw, -⟩
  exact stuck_nopNop B _ w hw

/-- Every model `stepModel20 B` is stuck at the image of `nop nop`. -/
theorem model_stuck_nop (B : Builtins) (hn : H → String) :
    (modelChart (stepModel20 B)).Sat (configV hn nopCfg) stuckSen :=
  fun w hw => stuck_nopNop B _ w hw

/-- V2 is not stuck at `nop nop`. -/
theorem not_v2_stuck_nop (P : Profile) (host : HostSemantics H) (hn : H → String)
    (D : Config H → Prop) : ¬ (v2Chart P host hn D).Sat nopCfg stuckSen :=
  fun h => h _ ⟨_, step_nopNop P host {} {}, rfl⟩

/-- **No transition along `configV` preserves progress**: any transition from the V2 chart on a
domain containing `nop nop` to any `modelChart (stepModel20 B)`, with point map `configV hn` and
`progress` in its class and fixed by its sentence map, does not preserve. -/
theorem not_fwd_progress {P : Profile} {host : HostSemantics H} {hn : H → String}
    {D : Config H → Prop} (hD : D nopCfg) {B : Builtins}
    (T : Transition (v2Chart P host hn D) (modelChart (stepModel20 B)))
    (hpt : T.pt nopCfg = configV hn nopCfg) (hsen : T.sen progress = progress)
    (hcls : T.cls progress) : T.dir.fwd = false := by
  cases hd : T.dir.fwd
  · rfl
  · have h := (T.sat nopCfg progress hD hcls).1 hd (v2_progress_nop P host hn D)
    rw [hpt, hsen] at h
    exact absurd h (not_model_progress_nop B hn)

/-- **No transition along `configV` reflects stuckness**: dually, a transition with `stuckSen` in
its class and fixed by its sentence map does not reflect. -/
theorem not_bwd_stuck {P : Profile} {host : HostSemantics H} {hn : H → String}
    {D : Config H → Prop} (hD : D nopCfg) {B : Builtins}
    (T : Transition (v2Chart P host hn D) (modelChart (stepModel20 B)))
    (hpt : T.pt nopCfg = configV hn nopCfg) (hsen : T.sen stuckSen = stuckSen)
    (hcls : T.cls stuckSen) : T.dir.bwd = false := by
  cases hd : T.dir.bwd
  · rfl
  · have hm := model_stuck_nop B hn
    rw [← hpt, ← hsen] at hm
    exact absurd ((T.sat nopCfg stuckSen hD hcls).2 hd hm) (not_v2_stuck_nop P host hn D)

/-- **No equal transition**: no transition along `configV` from the V2 chart on `DomS` to a model
of the wasm-2.0 script is `equal` on a class containing `progress`. -/
theorem not_equal_progress {P : Profile} {host : HostSemantics H} {hn : H → String}
    {B : Builtins} (T : Transition (v2Chart P host hn DomS) (modelChart (stepModel20 B)))
    (hpt : T.pt nopCfg = configV hn nopCfg) (hsen : T.sen progress = progress)
    (hcls : T.cls progress) : T.dir ≠ .equal := by
  intro he
  have h := not_fwd_progress domS_nopCfg T hpt hsen hcls
  rw [he] at h
  cases h

/-! ## The transitions are not vacuous: a step fact on `DomS` -/

/-- `nop` in the empty store and frame. -/
def nop1Cfg : Config H := ⟨{}, {}, [.plain .nop]⟩

/-- `nop` is in the scalar fragment. -/
theorem domS_nop1Cfg : DomS (nop1Cfg (H := H)) := by
  simp [DomS, DomW, nop1Cfg, CvtOkL, CvtOkA, NoVecL, NoVecA, ResOkL, ResOkA, InstrResOk,
    NoStoreL, NoStoreA, storeOp20, vecOp20]

set_option maxHeartbeats 4000000 in
/-- **Every model `stepModel20 B` steps from the image of `nop`** to the empty code, through
`Step/pure` and `Step_pure/nop`. -/
theorem model_step_nop1 (B : Builtins) (hn : H → String) :
    (stepModel20 B).D "Step" "%~>%" []
      (.tuple [configV hn nop1Cfg, configV hn (⟨{}, {}, []⟩ : Config H)]) := by
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20 B).findRel? "Step_pure" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩
  refine (sstepB20_iff B).2 (sstep20_of_pure ?_ ?_ ?_ ((dderives_iff_fires hrel).2
    ⟨1, Pure.firesB_pure20_iff B |>.1 ((Pure.nop_iff B).2 rfl)⟩))
  · exact ⟨100, by with_unfolding_all rfl⟩
  · exact ⟨100, by with_unfolding_all rfl⟩
  · exact ⟨100, by with_unfolding_all rfl⟩

/-- At `nop`, the model satisfies `progress`, so by `toModelSE` V2 does (here also directly). -/
theorem model_progress_nop1 (B : Builtins) (hn : H → String) :
    (modelChart (stepModel20 B)).Sat (configV hn nop1Cfg) progress :=
  ⟨_, model_step_nop1 B hn, trivial⟩

end Silmaril.Wasm.SpecTec.Institution.Wasm20
