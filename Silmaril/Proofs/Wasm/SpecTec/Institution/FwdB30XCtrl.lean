module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30X

/-!
# Existence at `Wasm30.builtins` for `block`, `loop` and `try_table`

These redexes are a value prefix of any length followed by one instruction, so the length half of
the tables does not refute `ctxt-instrs` on their proper infixes (the `Step_read` rules force no
length). The shape of Core's successor does instead: it is one label (`block`, `loop`) or one
handler (`try_table`), and a `Step` fact through `ctxt-instrs` keeps a non-empty prefix or
suffix of the redex, whose constructors are values or the block instruction's.

* `cfgRel_single`: a `CfgRel` image of a one-instruction code is a one-instruction code with the
  same constructor (unless that constructor is `CALL_REF`).
* `sread_of_sstep_single`: at every evaluator, a `Step` fact from `z; l` to a one-instruction
  code with a constructor foreign to `l` is `Step/read` at the whole of `l`, when no `Step_pure`
  rule and no `Step` rule beyond the first three names only constructors of `l`.
* `readC_builtins`, `readC_two_sided`: existence and uniqueness of the `Step_read` facts of
  `stepModel builtins` at `ReadC` redexes, up to `CfgRel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn)
open Silmaril.Wasm.SpecTec.Sim.Bwd (inv_pure inv_read inv_ctxtInstrs cfgV_inj)
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)

variable {H : Type}

/-! ## The successor's shape -/

/-- `CALL_REF` instructions have the head `CALL_REF`. -/
theorem adminHead_callRef {a : Admin} (h : a.IsCallRef) : Typing.adminHead a = "CALL_REF" := by
  cases a with
  | plain i => cases i <;> first | rfl | exact absurd h id
  | callRefType _ => rfl
  | _ => exact absurd h id

/-- The image of a one-instruction sequence. -/
theorem single_of_adminsToV {l : List Admin} {v : Value} (h : [v] = adminsToV l) :
    ∃ a, l = [a] ∧ adminToV a = v := by
  match l, h with
  | [a], h => exact ⟨a, rfl, (List.cons.inj h).1.symm⟩
  | [], h => exact absurd h (by simp [adminsToV])
  | _ :: _ :: _, h => exact absurd h (by simp [adminsToV])

/-- A code related to a one-instruction code is one instruction. -/
theorem codeEq_single {a : Admin} {l : List Admin} (h : Bwd.CodeEq [a] l) :
    ∃ b, l = [b] ∧ Bwd.AdminEq a b := by
  cases h with
  | cons hab hrest =>
    cases hrest
    exact ⟨_, rfl, hab⟩

/-- `AdminEq` keeps the constructor of an image, unless it is `CALL_REF`. -/
theorem adminEq_case {a b : Admin} (h : Bwd.AdminEq a b) {u : MixopS} {x : Value}
    (ha : adminToV a = .case u x) (hu : u ≠ "CALL_REF") : ∃ x', adminToV b = .case u x' := by
  cases h with
  | refl => exact ⟨x, ha⟩
  | call h₁ _ => exact absurd ((Typing.adminToV_case ha).trans (adminHead_callRef h₁)) hu
  | label _ =>
    have hu' : "LABEL_%{%}%" = u := (Value.case.inj ha).1
    exact ⟨_, by rw [← hu']; rfl⟩
  | handler _ =>
    have hu' : "HANDLER_%{%}%" = u := (Value.case.inj ha).1
    exact ⟨_, by rw [← hu']; rfl⟩
  | frame _ =>
    have hu' : "FRAME_%{%}%" = u := (Value.case.inj ha).1
    exact ⟨_, by rw [← hu']; rfl⟩

/-- **A `CfgRel` image of a one-instruction code** is a one-instruction code with the same
constructor, unless that constructor is `CALL_REF`. -/
theorem cfgRel_single {hn : H → String} {s : Store H} {f : Frame} {a : Admin} {w : Value}
    (hrel : SpecTec.CfgRel hn (configV hn ⟨s, f, [a]⟩) w) {u : MixopS} {x : Value}
    (ha : adminToV a = .case u x) (hu : u ≠ "CALL_REF") : ∃ z' x', w = cfgV z' [.case u x'] := by
  obtain ⟨c₁, d, ⟨-, -, hce⟩, h₁, hw⟩ := hrel
  obtain ⟨a₁, hl₁, ha₁⟩ : ∃ a₁, c₁.code = [a₁] ∧ adminToV a₁ = adminToV a :=
    single_of_adminsToV (cfgV_inj h₁).2
  obtain ⟨b, hb, hab⟩ : ∃ b, d.code = [b] ∧ Bwd.AdminEq a₁ b := codeEq_single (hl₁ ▸ hce)
  obtain ⟨x', hx'⟩ : ∃ x', adminToV b = .case u x' := adminEq_case hab (ha₁.trans ha) hu
  refine ⟨stateV hn d.store d.frame, x', ?_⟩
  rw [hw, Bwd.configV_eq, hb, ← hx']
  rfl

/-! ## The inversion -/

/-- Every row of `T` names a constructor outside `t :: valTags`. -/
def chkTags (t : MixopS) (T : List (List MixopS × Option Nat)) : Bool :=
  T.all (outside (t :: valTags))

/-- `chkTags`, on the `nonV` tables. -/
theorem chkTags_eq (t : MixopS) (T : List (List MixopS × Option Nat)) :
    chkTags t T = (T.map nonV).all fun row => row.1.any (· != t) := by
  simp only [chkTags, List.all_map]
  congr 1
  funext row
  exact outside_cons_eq t row

/-- `ctxt-instrs` keeps a non-empty prefix or suffix of the redex, so a one-instruction
successor through it has a constructor of the redex. -/
theorem not_ctxt_single {env : Env} (Tb : Tables env) {S : List MixopS} {l : List Value}
    (hl : TagsIn S l) {z z' x' : Value} {u : MixopS} (hu : u ∉ S)
    (hf : Fires env "Step" 2 (.tuple [cfgV z l, cfgV z' [.case u x']])) : False := by
  obtain ⟨z₁, z₁', vs, is, is', rest, -, hne, h₁, h₂, -⟩ := inv_ctxtInstrs Tb.rules.ctxtInstrs hf
  have el : l = vs ++ is ++ rest := (cfgV_inj h₁).2
  have ew : vs ++ (is' ++ rest) = [Value.case u x'] := by
    rw [← List.append_assoc]; exact (cfgV_inj h₂).2.symm
  have ew' : (vs ++ is') ++ rest = [Value.case u x'] := by
    rw [List.append_assoc]; exact ew
  have hmem : Value.case u x' ∈ l := by
    rcases hne with h | h
    · obtain ⟨hv, -⟩ := (List.append_eq_singleton_iff.1 ew).resolve_left (fun h' => h h'.1)
      rw [el, hv]; simp
    · obtain ⟨-, hr⟩ := (List.append_eq_singleton_iff.1 ew').resolve_right (fun h' => h h'.2)
      rw [el, hr]; simp
  exact hu (hl _ hmem u x' rfl)

/-- **Inversion to a one-instruction successor**: at every evaluator with the wasm-3.0 tables,
a `Step` fact from `z; l` (constructors in `t :: valTags`) to a one-instruction code whose
constructor `u` is foreign to `l` is `Step/read` at the whole of `l`, when no `Step_pure` rule
and no `Step` rule beyond the first three names only constructors of `t :: valTags`. -/
theorem sread_of_sstep_single {env : Env} (Tb : Tables env) {t : MixopS} {l : List Value}
    (hl : TagsIn (t :: valTags) l) (hp : chkTags t pureInfoT = true)
    (hst : chkTags t stepRestT = true) {z z' x' : Value} {u : MixopS}
    (hu : u ∉ t :: valTags) (hs : SStep env (cfgV z l) (cfgV z' [.case u x'])) :
    ∃ js, cfgV z' [.case u x'] = cfgV z js ∧ SRead env (cfgV z l) js := by
  have blk : ∀ {T : List (List MixopS × Option Nat)}, chkTags t T = true →
      ∀ row ∈ T, Blk (t :: valTags) l.length row :=
    fun hT row hrow => .inl (outside_spec (List.all_eq_true.1 hT row hrow))
  have hpure : ∀ i v, ¬ Fires env "Step_pure" i (.tuple [.list l, v]) := fun i v =>
    not_fires_of_blk Tb.pureT (Nat.zero_le i) fun row hrow =>
      ⟨_, _, .inl ⟨l, rfl, hl, rfl⟩, blk hp row hrow⟩
  have hstep : ∀ i z v, 3 ≤ i → ¬ Fires env "Step" i (.tuple [cfgV z l, v]) := fun i z v hi =>
    not_fires_of_blk Tb.stepT hi fun row hrow => ⟨_, _, .inr ⟨z, l, rfl, hl, rfl⟩, blk hst row hrow⟩
  obtain ⟨tt, rules, hrel⟩ := Tb.step
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf =>
    obtain ⟨z₁, is, js, h₁, -, hq⟩ := inv_pure Tb.rules.pure hf
    obtain ⟨tp, rp, hrelp⟩ := Tb.pure
    obtain ⟨j, hj⟩ := (dderives_iff_fires hrelp).1 hq
    exact absurd ((cfgV_inj h₁).2 ▸ hj) (hpure j _)
  | 1, hf =>
    obtain ⟨z₁, is, js, h₁, h₂, hq⟩ := inv_read Tb.rules.read hf
    have e : z = z₁ ∧ l = is := cfgV_inj h₁
    exact ⟨js, e.1 ▸ h₂, e.1 ▸ e.2 ▸ hq⟩
  | 2, hf => exact (not_ctxt_single Tb hl hu hf).elim
  | k + 3, hf => exact absurd hf (hstep (k + 3) z _ (by omega))

/-! ## At `Wasm30.builtins` -/

/-- The constructors of values followed by one instruction. -/
theorem tagsIn_vals_last (vs : List Val) (a : Admin) {t : MixopS}
    (ht : Typing.adminHead a = t) : TagsIn (t :: valTags) (adminsToV (vals vs ++ [a])) := by
  subst ht
  intro x hx op w hxe
  rw [adminsToV_eq_map, List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  rw [Typing.adminToV_case hxe]
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hb
    exact List.mem_cons_of_mem _ (adminHead_toAdmin v)
  · rw [List.mem_singleton.1 hb]
    exact List.mem_cons_self

/-- The checks at `block`, `loop` and `try_table`. -/
theorem chkTags_ctrl :
    (chkTags "BLOCK" pureInfoT && chkTags "BLOCK" stepRestT && chkTags "LOOP" pureInfoT &&
      chkTags "LOOP" stepRestT && chkTags "TRY_TABLE" pureInfoT &&
      chkTags "TRY_TABLE" stepRestT) = true := by
  simp only [chkTags_eq, stepRestT, List.map_drop, nvT_eq]
  decide +kernel

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- `ReadC` redexes are `CtrlRead` redexes. -/
theorem ReadC.toCtrl {c : Config H} {is' : List Admin} (h : ReadC c is') :
    FwdX30.CtrlRead c is' := by
  cases h with
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | tryTable hbt hm => exact .tryTable hbt hm

/-- The checks at one of the three block instructions. -/
theorem chkTags_readC {c : Config H} {is' : List Admin} (hr : ReadC c is') :
    ∃ t u, TagsIn (t :: valTags) (adminsToV c.code) ∧ chkTags t pureInfoT = true ∧
      chkTags t stepRestT = true ∧ u ∉ t :: valTags ∧ u ≠ "CALL_REF" ∧
      ∃ a x, is' = [a] ∧ adminToV a = .case u x := by
  have hk := chkTags_ctrl
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hb₁, hb₂⟩, hl₁⟩, hl₂⟩, ht₁⟩, ht₂⟩ := hk
  cases hr with
  | block =>
    exact ⟨"BLOCK", "LABEL_%{%}%", tagsIn_vals_last _ _ rfl, hb₁, hb₂, by decide, by decide,
      _, _, rfl, rfl⟩
  | loop =>
    exact ⟨"LOOP", "LABEL_%{%}%", tagsIn_vals_last _ _ rfl, hl₁, hl₂, by decide, by decide,
      _, _, rfl, rfl⟩
  | tryTable =>
    exact ⟨"TRY_TABLE", "HANDLER_%{%}%", tagsIn_vals_last _ _ rfl, ht₁, ht₂, by decide,
      by decide, _, _, rfl, rfl⟩

/-- **Existence at `builtins` for `block`, `loop`, `try_table`**: on `DomDet`, Core's successor
is a `Step_read` fact of `stepModel builtins` up to `CfgRel`. -/
theorem readC_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadC c is') :
    ∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  have hx : FwdX30.ReadHeadX (Profile.spec nd r) c is' := .ctrl hr.toCtrl
  obtain ⟨⟨w, hw, hrel⟩, -⟩ :=
    FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hx.step
  obtain ⟨t, u, hl, hp, hst, hu, hcr, a, x, ha, hax⟩ := chkTags_readC hr
  obtain ⟨z', x', hw'⟩ : ∃ z' x', w = cfgV z' [.case u x'] :=
    cfgRel_single (ha ▸ hrel) hax hcr
  have hnc : ¬ Round6.Target.CastRedex c.code := hx.not_castRedex
  have hs : SStep EB (cfgV (stateV hn c.store c.frame) (adminsToV c.code)) (cfgV z' [.case u x']) :=
    hw' ▸ (Round6.Transfer.sstepB_iff_of_not_castRedex _ hn hnc w).1 hw
  obtain ⟨js, hjs, hq⟩ := sread_of_sstep_single (tables_simEnv _) hl hp hst hu hs
  have hq' : SRead EB (configV hn c) js := hq
  have hwj : w = cfgV (stateV hn c.store c.frame) js := hw'.trans hjs
  exact ⟨js, (Round6.Transfer.sReadB_iff_noCast hnc).2 hq', hwj ▸ hrel⟩

/-- **`Step_read` at `builtins` is two-sided at `block`, `loop`, `try_table`**. -/
theorem readC_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hr : ReadC c is') :
    (∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js)) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
          (cfgV (stateV hn c.store c.frame) js) :=
  ⟨readC_builtins hc hr, fun _ hjs hq =>
    FwdX30Fin.readFact_unique_builtins hc
      (FwdX30.ReadHeadX.ctrl (P := Profile.spec nd r) hr.toCtrl).step hjs hq⟩

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
