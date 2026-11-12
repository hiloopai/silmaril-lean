module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeVecEdge

/-!
# The backward recursion under a configuration invariant, and `Task.wholeStepBwdW`

`WholeBwdQ` runs the backward recursion under an invariant of the code. The corrected target
`Task.wholeStepBwdW` also asks that the resources the code names exist (`ResOkL`), which depends
on the store and on the frame each piece of code runs in. So this module runs the same recursion
under an invariant `G` of whole configurations that passes to the body of a label (same state) and
of a frame (its own frame): `CfgInv`, `BwdPartsG`, `bwdG_all`, `backward20G_of_parts`.

With `G` = `CvtOkL ∧ NoVecL ∧ ResOkL` (`GoodW`):

* the 23 live vector rules of `Step_pure` cannot fire, since each forces a vector operator on its
  left-hand side (`vecLive20_tags`, `not_firesPure_vec`);
* the 18 other live rules of `Step_pure` are `WholeBwdQ.pureDone_bwd`;
* so `Step_pure` is discharged entirely (`pure_bwdW`), and `Task.wholeStepBwdW` follows from the
  `Step_read` and `Step` obligations alone (`BwdRestW`, `wholeStepBwdW_of_rest`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (Fires SStep dderives_iff_fires cfgV stV)
open Silmaril.Wasm.SpecTec.Sim.Bwd (cfgV_inj stV_inj)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (LhsIn TagsIn relRules ruleTags not_ruleBody_of_tags)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (IntB)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB)

set_option maxRecDepth 100000

variable {H : Type}

/-! ## Vector rules at vector-free code -/

/-- The constructors of the 2.0 IL's vector operators. -/
def vecOpTags : List MixopS :=
  ["VVUNOP", "VVBINOP", "VVTERNOP", "VVTESTOP", "VUNOP", "VBINOP", "VTESTOP", "VRELOP",
   "VSHIFTOP", "VBITMASK", "VSWIZZLE", "VSHUFFLE", "VSPLAT", "VEXTRACT_LANE", "VREPLACE_LANE",
   "VEXTUNOP", "VEXTBINOP", "VNARROW", "VCVTOP"]

/-- The live vector rules of `Step_pure`. -/
def vecLive20 : List Nat :=
  [30, 31, 32, 33, 34, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54]

/-- Each live vector rule forces a vector operator on its left-hand side. -/
theorem vecLive20_tags : ∀ i ∈ vecLive20, ∃ op ∈ pureTags20[i]?.getD [], op ∈ vecOpTags := by
  decide +kernel

/-- A V2 instruction that is not a vector operator has a constructor outside `vecOpTags`. -/
theorem instrHead20_notVec {i : V2.Instr} (h : vecOp20 i = false) :
    instrHead20 i ∉ vecOpTags := by
  cases i <;> first | (simp only [instrHead20]; decide) | simp [vecOp20] at h

/-- An administrative instruction with no active vector operator has a constructor outside
`vecOpTags`. -/
theorem adminHead20_notVec {a : Admin} (h : NoVecA a) : adminHead20 a ∉ vecOpTags := by
  cases a with
  | plain i => exact instrHead20_notVec (by simpa [NoVecA] using h)
  | _ => simp only [adminHead20]; decide

/-- Every instruction of vector-free code has no active vector operator. -/
theorem noVecA_of_mem : ∀ {code : List Admin}, NoVecL code → ∀ a ∈ code, NoVecA a
  | [], _, _, ha => absurd ha List.not_mem_nil
  | _ :: _, h, a, ha => (List.mem_cons.1 ha).elim (fun e => e ▸ h.1) (noVecA_of_mem h.2 a)

/-- The image of any code has its constructors among the heads of its instructions. -/
theorem tagsIn_heads (code : List Admin) : TagsIn (code.map adminHead20) (adminsToV code) := by
  intro x hx op w hxw
  rw [adminsToV_map] at hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact List.mem_map.2 ⟨a, ha, adminToV_case20 hxw⟩

/-- **The live vector rules of `Step_pure` do not fire at vector-free code.** -/
theorem not_firesPure_vec {B : Builtins} {i : Nat} (hi : i ∈ vecLive20) {code : List Admin}
    (hq : NoVecL code) {w : Value} :
    ¬ Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), w]) := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hrules : rules.map ruleTags = pureTags20 := by
    have h₁ := pureTags20_eq
    rw [← relRules_simEnv20 B] at h₁
    simpa [relRules, hrel] using h₁
  have htag : pureTags20[i]?.getD [] = ruleTags r := by
    rw [← hrules, List.getElem?_map, hr]
    rfl
  obtain ⟨op, hop, hv⟩ := vecLive20_tags i hi
  have hop' : op ∈ ruleTags r := htag ▸ hop
  have hS : op ∉ code.map adminHead20 := by
    intro hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
    exact adminHead20_notVec (noVecA_of_mem hq a ha) hv
  exact not_ruleBody_of_tags (Or.inl ⟨_, rfl, tagsIn_heads code⟩) hop' hS hb

/-! ## The recursion under a configuration invariant -/

/-- A predicate on configurations that holds of the body of a label (in the same state) and of the
body of a frame (in that frame) whenever it holds of the label or frame. -/
structure CfgInv (G : Config H → Prop) : Prop where
  label : ∀ s f n cont body, G ⟨s, f, [.label n cont body]⟩ → G ⟨s, f, body⟩
  frame : ∀ s f n fi body, G ⟨s, f, [.frame n fi body]⟩ → G ⟨s, fi, body⟩

/-- `BwdParts20`, asked only at configurations satisfying `G`. -/
structure BwdPartsG (G : Config H → Prop) (B : Builtins) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`. -/
  pure : ∀ (i : Nat) (c : Config H) (w : List Value), G c →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep P c.code code'
  /-- `Step_read`. -/
  read : ∀ (i : Nat) (c : Config H) (w : List Value), G c →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  /-- The `Step` rules from `local.set` on. -/
  step : ∀ (i : Nat), 4 ≤ i → ∀ (c : Config H) (w : Value), G c →
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

section Rec

variable {G : Config H → Prop} {B : Builtins} {hn : H → String} {P : Profile}
  {host : HostSemantics H}

/-- The induction hypothesis under `G`. -/
def IHG (G : Config H → Prop) (B : Builtins) (hn : H → String) (P : Profile)
    (host : HostSemantics H) (n : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), G c → codeSize20 c.code < n →
    SStep (simEnv20 B) (configV hn c) w → BwdAt B hn P host c w

/-- `Step/pure` backwards, under `G`. -/
theorem bwdG_pure (Bk : BwdPartsG G B hn P host) {c : Config H} {w : Value} (hg : G c)
    (hf : Fires (simEnv20 B) "Step" 0 (.tuple [configV hn c, w])) : BwdAt B hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_pure20 (hasRuleAt_stepPure B) hf
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20 B).findRel? "Step_pure" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [e₁.2] at ti hi
  obtain ⟨code', rfl, hst⟩ := Bk.pure i c js hg ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, .pure hst⟩

/-- `Step/read` backwards, under `G`. -/
theorem bwdG_read (Bk : BwdPartsG G B hn P host) {c : Config H} {w : Value} (hg : G c)
    (hf : Fires (simEnv20 B) "Step" 1 (.tuple [configV hn c, w])) : BwdAt B hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_read20 (hasRuleAt_stepRead B) hf
  obtain ⟨t, rules, hrel⟩ := findRel_read20 B
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [← h₁] at hi
  rw [e₁.2] at ti
  obtain ⟨code', rfl, hst⟩ := Bk.read i c js hg ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, .read hst⟩

/-- `Step/ctxt-label` backwards, under `G`. -/
theorem bwdG_ctxtLabel (I : CfgInv G) {n : Nat} (ih : IHG G B hn P host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hg : G ⟨s, f, code⟩)
    (hlt : codeSize20 code < n + 1)
    (hf : Fires (simEnv20 B) "Step" 2 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt B hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cont, is, is', h₁, h₂, hs⟩ := inv_ctxtLabel20 (hasRuleAt_ctxtLabel B) hf
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := adminToV_label_inv ha
  have hp : Value.num (.natN k) = m ∧ instrsToV cont₀ = cont ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.label _ _ _ _ _ hg)
      (Nat.lt_of_lt_of_le (codeSize20_label k cont₀ body) (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq hn _))
  refine ⟨⟨s₂, f₂, [.label k cont₀ K]⟩, ?_, .ctxtLabel hst⟩
  rw [h₂, e₃.1, e₃.2, ← hp.1, ← hp.2.1]
  rfl

/-- `Step/ctxt-frame` backwards, under `G`. -/
theorem bwdG_ctxtFrame (I : CfgInv G) {n : Nat} (ih : IHG G B hn P host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hg : G ⟨s, f, code⟩)
    (hlt : codeSize20 code < n + 1)
    (hf : Fires (simEnv20 B) "Step" 3 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt B hn P host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, m, is, is', h₁, h₂, hs⟩ := inv_ctxtFrame20 (hasRuleAt_ctxtFrame B) hf
  have e₁ := configV_cfgV h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := adminToV_frame_inv ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV (stV sv fr) is = configV hn ⟨s, fi, body⟩ := by
    rw [configV_eq, e₀.1, ← hp.2.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.frame _ _ _ _ _ hg)
      (Nat.lt_of_lt_of_le (codeSize20_frame k fi body) (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq hn _))
  have e₄ : sv' = storeV hn s₂ ∧ fr = frameV f₂ := stV_inj e₃.1
  refine ⟨⟨s₂, f, [.frame k f₂ K]⟩, ?_, .ctxtFrame hst⟩
  rw [h₂, e₄.1, e₃.2, e₀.2, ← hp.1, e₄.2]
  rfl

/-- The backward recursion under `G`, on the size of the code. -/
theorem bwdG_all (Bk : BwdPartsG G B hn P host) (I : CfgInv G) : ∀ n, IHG G B hn P host n
  | 0 => fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨s, f, code⟩ w hg hlt hs => by
    obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_stepPure B
    obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
    match i, hf with
    | 0, hf => exact bwdG_pure Bk hg hf
    | 1, hf => exact bwdG_read Bk hg hf
    | 2, hf => exact bwdG_ctxtLabel I (bwdG_all Bk I n) hg hlt hf
    | 3, hf => exact bwdG_ctxtFrame I (bwdG_all Bk I n) hg hlt hf
    | k + 4, hf => exact Bk.step (k + 4) (by omega) _ w hg hf

end Rec

/-- **The backward half under `G`, from the per-rule obligations under `G`.** -/
theorem backward20G_of_parts {G : Config H → Prop} {B : Builtins} {hn : H → String}
    {P : Profile} {host : HostSemantics H} (Bk : BwdPartsG G B hn P host) (I : CfgInv G)
    (c : Config H) (w : Value) (hg : G c) (hs : SStepB (simEnv20 B) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step P host c c' :=
  bwdG_all Bk I (codeSize20 c.code + 1) c w hg (Nat.lt_succ_self _) ((sstepB20_iff B).1 hs)

/-! ## The invariant of `Task.wholeStepBwdW` -/

/-- Conversions V2 defines, no vector operator, and the named resources exist. -/
def GoodW (c : Config H) : Prop :=
  CvtOkL c.code ∧ NoVecL c.code ∧ ResOkL c.store c.frame c.code

/-- `GoodW` passes to the bodies of labels and frames. -/
theorem cfgInv_goodW : CfgInv (GoodW (H := H)) where
  label _ _ _ _ _ h := by
    simpa [GoodW, CvtOkL, CvtOkA, NoVecL, NoVecA, ResOkL, ResOkA] using h
  frame _ _ _ _ _ h := by
    simpa [GoodW, CvtOkL, CvtOkA, NoVecL, NoVecA, ResOkL, ResOkA] using h

/-- Every rule of `Step_pure` is dead, discharged, or a vector rule. -/
theorem pure_cover : ∀ i < 56, i ∈ deadPure20 ∨ i ∈ pureDone20 ∨ i ∈ vecLive20 := by
  decide

/-- `Step_pure` has 56 rules. -/
theorem pure_length {B : Builtins} {t : Typ} {rules : List Rule}
    (hrel : (simEnv20 B).findRel? "Step_pure" = some ([], "%~>%", t, rules)) : rules.length = 56 := by
  have h₁ : rules.map ruleTags = pureTags20 := by
    have h₀ := pureTags20_eq
    rw [← relRules_simEnv20 B] at h₀
    simpa [relRules, hrel] using h₀
  have h₂ : (rules.map ruleTags).length = 56 := by rw [h₁]; rfl
  simpa using h₂

/-- No `Step_pure` rule exists beyond the 56. -/
theorem not_firesPure_ge {B : Builtins} {i : Nat} (hi : 56 ≤ i) {v : Value} :
    ¬ Fires (simEnv20 B) "Step_pure" i v := by
  rintro ⟨t, rules, r, hrel, hr, -⟩
  have hl := pure_length hrel
  rw [List.getElem?_eq_none (by omega)] at hr
  exact absurd hr (by simp)

/-- **What is left of the backward obligations of `Task.wholeStepBwdW`**: the live `Step_read`
rules and the `Step` rules from `local.set` on, at configurations satisfying `GoodW`. -/
structure BwdRestW (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  read : ∀ (i : Nat), i ∉ deadRead20 → ∀ (c : Config H) (w : List Value), GoodW c →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 4 ≤ i → ∀ (c : Config H) (w : Value), GoodW c →
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- **`Step_pure` is discharged at `GoodW` configurations**: dead rules do not fire, the vector
rules do not fire at vector-free code, the other 18 are `pureDone_bwd`. -/
theorem pure_bwdW {B : Builtins} {P : Profile} (hI : IntB B) (hF : FloatB P B) {i : Nat}
    {c : Config H} {w : List Value} (hg : GoodW c)
    (hc : TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)))
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w])) :
    ∃ code', w = adminsToV code' ∧ PureStep P c.code code' := by
  by_cases hlt : i < 56
  · rcases pure_cover i hlt with hd | hd | hv
    · exact absurd hf (not_firesPure_dead hd hc hw)
    · exact pureDone_bwd hI hF hd hg.1 hf
    · exact absurd hf (not_firesPure_vec hv hg.2.1)
  · exact absurd hf (not_firesPure_ge (by omega))

/-- The per-rule obligations under `GoodW`, from what is left. -/
theorem bwdPartsG_of_restW {B : Builtins} {hn : H → String} {P : Profile}
    {host : HostSemantics H} (hI : IntB B) (hF : FloatB P B) (R : BwdRestW B hn P host) :
    BwdPartsG GoodW B hn P host where
  pure _ _ _ hg hc hw hf := pure_bwdW hI hF hg hc hw hf
  read i c w hg hc hw hf := by
    by_cases hd : i ∈ deadRead20
    · exact absurd hf (not_firesRead_dead hd hc hw)
    · exact R.read i hd c w hg hc hw hf
  step := R.step

/-- **`Task.wholeStepBwdW` from what is left** (`BwdRestW` at the spec's builtins): the structural
rules of `Step` and every rule of `Step_pure` are discharged. -/
theorem wholeStepBwdW_of_rest
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRestW (Sim.Floats.floatIntB (Profile.spec nd r)) hn (Profile.spec nd r) host) :
    Task.wholeStepBwdW := fun H hn hinj host nd r c w _ hq hv hres hs =>
  backward20G_of_parts (bwdPartsG_of_restW (Sim.Floats.intB_floatIntB _)
    (Sim.Floats.floatB_floatIntB _) (h H hn hinj host nd r)) cfgInv_goodW c w ⟨hq, hv, hres⟩ hs

end Silmaril.Wasm.SpecTec.Sim20.Whole
