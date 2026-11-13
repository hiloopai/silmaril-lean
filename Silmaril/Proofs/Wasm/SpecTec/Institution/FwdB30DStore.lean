module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DArity
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DDeep

/-!
# The `Step` rules of unbounded arity at `Wasm30.builtins`

`FwdB30S.storeW_exact` covered the store-changing `Step` rules of fixed arity. This module covers
the others: `struct.new`, `array.new_fixed` and `throw` (a value prefix of any length, then the
instruction), and `call_ref-null` and `call_ref-func` (rules 6 and 7). As there, the only
knowledge of `builtins` is `FwdX30Fin.stepObs_builtins`; the rest is inversion at every `B`.

* `struct.new`, `array.new_fixed`, `throw`: by `sstep_head_tail` (the successor is one reference,
  or `throwing a`, and the rules naming only the instruction and values force a right-hand side
  that long).
* `call_ref`: the successor is one `TRAP` or one `FRAME`, a constructor foreign to the redex, so
  `FwdB30X.not_ctxt_single` refutes `ctxt-instrs`.

* `structNew_exact`, `arrayNewFixed_exact`, `throw_exact`, `callRefNull_exact`: on `DomDet`, a
  rule of `Step` from rule 6 on fires at the image of the configuration, under the reading of
  `stepModel`, with the image of Core's successor as its conclusion, and that is the only `Step`
  fact there.
* `callRefFunc_exact`: the same at `call_ref-func` when the function body has no `call_ref` at
  the top (`callFree`); `callRefFunc_builtins` without it, up to `CfgRel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30D

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (DefType Ty Expand CFieldType)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn)
open Silmaril.Wasm.SpecTec.Sim.Bwd (inv_pure inv_read cfgV_inj)
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdB30X

variable {H : Type}

/-! ## The checks -/

/-- The checks at `struct.new`, `array.new_fixed` and `throw`. -/
theorem chk_arity :
    (chkTags "STRUCT.NEW" pureInfoT && chkTags "STRUCT.NEW" readInfoT &&
      chkTags "STRUCT.NEW" (stepRestT.take 3) && rhsOk "STRUCT.NEW" 1 &&
      chkTags "ARRAY.NEW_FIXED" pureInfoT && chkTags "ARRAY.NEW_FIXED" readInfoT &&
      chkTags "ARRAY.NEW_FIXED" (stepRestT.take 3) && rhsOk "ARRAY.NEW_FIXED" 1 &&
      chkTags "THROW" pureInfoT && chkTags "THROW" readInfoT &&
      chkTags "THROW" (stepRestT.take 3) && rhsOk "THROW" 2) = true := by
  decide +kernel

/-- The checks at `call_ref`. -/
theorem chk_callRef :
    (chkTags "CALL_REF" pureInfoT && chkTags "CALL_REF" readInfoT &&
      chkTags "CALL_REF" (stepRestT.take 3)) = true := by
  decide +kernel

/-! ## Inversion to a one-instruction successor of a foreign constructor -/

/-- **Inversion at `call_ref`**: at every evaluator with the wasm-3.0 tables, a `Step` fact from
code with constructors in `t :: valTags` to a one-instruction code whose constructor is foreign
is a rule of `Step` from rule 6 on, when no `Step_pure`, `Step_read` or context rule names only
constructors of `t :: valTags`. -/
theorem sstep_head_single {env : Env} (Tb : Tables env) {t : MixopS}
    (hp : chkTags t pureInfoT = true) (hrd : chkTags t readInfoT = true)
    (hctx : chkTags t (stepRestT.take 3) = true) {l : List Value} (hl : TagsIn (t :: valTags) l)
    {z z' x' : Value} {u : MixopS} (hu : u ∉ t :: valTags)
    (hs : SStep env (cfgV z l) (cfgV z' [.case u x'])) :
    ∃ i, 6 ≤ i ∧ Fires env "Step" i (.tuple [cfgV z l, cfgV z' [.case u x']]) := by
  obtain ⟨tt, rules, hrel⟩ := Tb.step
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  have hctx3 : ∀ i, 3 ≤ i → i < 6 →
      ¬ Fires env "Step" i (.tuple [cfgV z l, cfgV z' [.case u x']]) :=
    fun i hi3 hi6 => not_fires_of_row Tb.stepT fun row hrow =>
      ⟨_, _, .inr ⟨z, l, rfl, hl, rfl⟩, .inl (outside_spec (List.all_eq_true.1 hctx row (by
        apply List.mem_of_getElem? (i := i - 3)
        rw [List.getElem?_take_of_lt (by omega), stepRestT, List.getElem?_drop,
          Nat.add_sub_cancel' hi3]
        exact hrow)))⟩
  match i, hf with
  | 0, hf => exact absurd hf (not_pure_tags Tb hp hl)
  | 1, hf => exact absurd hf (not_read_tags Tb hrd hl)
  | 2, hf => exact (not_ctxt_single Tb hl hu hf).elim
  | 3, hf => exact absurd hf (hctx3 3 (by omega) (by omega))
  | 4, hf => exact absurd hf (hctx3 4 (by omega) (by omega))
  | 5, hf => exact absurd hf (hctx3 5 (by omega) (by omega))
  | k + 6, hf => exact ⟨k + 6, by omega, hf⟩

/-! ## The shapes of the redexes -/

/-- No element of an image has the constructor `t` when no instruction has the head `t`. -/
theorem noTag_of_heads {l : List Admin} {t : MixopS} (h : ∀ a ∈ l, Typing.adminHead a ≠ t) :
    ∀ w, Value.case t w ∉ adminsToV l := by
  intro w hw
  rw [adminsToV_eq_map, List.mem_map] at hw
  obtain ⟨a, ha, he⟩ := hw
  exact h a ha (Typing.adminToV_case he).symm

/-- The last element of the image of `vals vs ++ [a]`. -/
theorem getLast?_vals_last (vs : List Val) (a : Admin) :
    (adminsToV (vals vs ++ [a])).getLast? = some (adminToV a) := by
  rw [adminsToV_eq_map, List.map_append, List.map_singleton, List.getLast?_append_of_ne_nil _
    (List.cons_ne_nil _ _)]
  rfl

/-- Constructors from the heads of the instructions. -/
theorem tagsIn_of_heads {l : List Admin} {S : List MixopS}
    (h : ∀ a ∈ l, Typing.adminHead a ∈ S) : TagsIn S (adminsToV l) := by
  intro x hx op w hxe
  rw [adminsToV_eq_map, List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [Typing.adminToV_case hxe]
  exact h a ha

/-- A `CALL_REF` cannot start a cast redex. -/
theorem noCast_callRef {c : Admin} (h : c.IsCallRef) : FwdX30.noCastAdmin c = true := by
  rcases Bwd.isCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> rfl

/-- The `call_ref` redex `val* (REF.FUNC_ADDR a) CALL_REF` (or `(REF.NULL) CALL_REF`). -/
theorem callRef_shape (vs : List Val) (r : Ref) {c : Admin} (hc : c.IsCallRef)
    (hr : Typing.adminHead (.ref r) ∈ valTags) :
    TagsIn ("CALL_REF" :: valTags) (adminsToV (vals vs ++ [.ref r, c])) ∧
      ¬ Round6.Target.CastRedex (vals vs ++ [.ref r, c]) := by
  refine ⟨tagsIn_of_heads fun a ha => ?_, FwdX30.not_castRedex_of_all fun a ha => ?_⟩
  · simp only [vals, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    rcases ha with ⟨v, -, rfl⟩ | rfl | rfl
    · exact List.mem_cons_of_mem _ (adminHead_toAdmin v)
    · exact List.mem_cons_of_mem _ hr
    · rw [adminHead_callRef hc]; exact List.mem_cons_self
  · simp only [vals, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    rcases ha with ⟨v, -, rfl⟩ | rfl | rfl
    · exact FwdX30.noCastAdmin_toAdmin v
    · rfl
    · exact noCast_callRef hc

/-- The redex `val* instr` of `struct.new`, `array.new_fixed` and `throw`. -/
theorem flat_shape (vs : List Val) (i : Instr) (hi : Round6.Target.castInstr i = false) :
    TagsIn (Typing.adminHead (.plain i) :: valTags) (adminsToV (vals vs ++ [.plain i])) ∧
      ¬ Round6.Target.CastRedex (vals vs ++ [.plain i]) := by
  refine ⟨tagsIn_vals_last vs _ rfl, FwdX30.not_castRedex_of_all fun a ha => ?_⟩
  simp only [vals, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with ⟨v, -, rfl⟩ | rfl
  · exact FwdX30.noCastAdmin_toAdmin v
  · simp [FwdX30.noCastAdmin, hi]

/-! ## At `Wasm30.builtins` -/

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- **A Core step at a redex of unbounded arity, exactly**: on `DomDet`, when the redex ends in
`t` and the successor is deeply rigid, without `t` and no longer than `M`, a rule of `Step`
from rule 6 on fires (under `stepModel`'s reading) at the image of the configuration with the
image of Core's successor as its conclusion, and that is the only `Step` fact there. -/
theorem tail_exact {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') (hnc : ¬ Round6.Target.CastRedex c.code)
    {t : MixopS} {M : Nat} (hp : chkTags t pureInfoT = true) (hrd : chkTags t readInfoT = true)
    (hctx : chkTags t (stepRestT.take 3) = true) (hok : rhsOk t M = true)
    (hl : TagsIn (t :: valTags) (adminsToV c.code)) {w₀ : Value}
    (hlast : (adminsToV c.code).getLast? = some (.case t w₀))
    (hjM : (adminsToV c'.code).length ≤ M) (hjs : ∀ w, Value.case t w ∉ adminsToV c'.code)
    (hrig : deepRigidL c'.code = true) :
    (∃ i, 6 ≤ i ∧ Round6.Reading.FiresB EB "Step" i (.tuple [configV hn c, configV hn c'])) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) → w = configV hn c' := by
  obtain ⟨⟨w, hw, hrel⟩, hall⟩ :=
    FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hs
  have hw' : SStep EB (configV hn c) w :=
    (Round6.Transfer.sstepB_iff_of_not_castRedex _ hn hnc w).1 hw
  rw [cfgRel_exact_deep hrel hrig, Bwd.configV_eq, Bwd.configV_eq] at hw'
  obtain ⟨i, hi, hfi⟩ :=
    sstep_head_tail (tables_simEnv _) (rhsT_simEnv _) hp hrd hctx hok hl hlast hjM hjs hw'
  refine ⟨⟨i, hi, ?_⟩, fun w' hw'' => cfgRel_exact_deep (hall w' hw'') hrig⟩
  rw [Bwd.configV_eq, Bwd.configV_eq]
  exact (Round6.Reading.firesB_step_iff _ (.inr hi)).2 hfi

/-- **A Core step to one instruction of a foreign constructor**: on `DomDet`, a rule of `Step`
from rule 6 on fires at the image of the configuration with a conclusion `CfgRel`-related to
Core's successor, and every `Step` fact there is that successor up to `CfgRel`. -/
theorem single_builtins {c : Config H} {s' : Store H} {f' : Frame} {a : Admin}
    (hc : DomDet (Profile.spec nd r) host c) (hs : Step (Profile.spec nd r) host c ⟨s', f', [a]⟩)
    (hnc : ¬ Round6.Target.CastRedex c.code) {t : MixopS} (hp : chkTags t pureInfoT = true)
    (hrd : chkTags t readInfoT = true) (hctx : chkTags t (stepRestT.take 3) = true)
    (hl : TagsIn (t :: valTags) (adminsToV c.code)) {u : MixopS} {x : Value}
    (ha : adminToV a = .case u x) (hu : u ∉ t :: valTags) (hcr : u ≠ "CALL_REF") :
    (∃ i, 6 ≤ i ∧ ∃ w, Round6.Reading.FiresB EB "Step" i (.tuple [configV hn c, w]) ∧
      SpecTec.CfgRel hn (configV hn ⟨s', f', [a]⟩) w) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) →
        SpecTec.CfgRel hn (configV hn ⟨s', f', [a]⟩) w := by
  obtain ⟨⟨w, hw, hrel⟩, hall⟩ :=
    FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hs
  have hw' : SStep EB (configV hn c) w :=
    (Round6.Transfer.sstepB_iff_of_not_castRedex _ hn hnc w).1 hw
  obtain ⟨z', x', rfl⟩ := cfgRel_single hrel ha hcr
  rw [Bwd.configV_eq] at hw'
  obtain ⟨i, hi, hfi⟩ := sstep_head_single (tables_simEnv _) hp hrd hctx hl hu hw'
  refine ⟨⟨i, hi, _, ?_, hrel⟩, hall⟩
  rw [Bwd.configV_eq]
  exact (Round6.Reading.firesB_step_iff _ (.inr hi)).2 hfi

/-- `single_builtins`, exactly, at a deeply rigid successor. -/
theorem single_exact {c : Config H} {s' : Store H} {f' : Frame} {a : Admin}
    (hc : DomDet (Profile.spec nd r) host c) (hs : Step (Profile.spec nd r) host c ⟨s', f', [a]⟩)
    (hnc : ¬ Round6.Target.CastRedex c.code) {t : MixopS} (hp : chkTags t pureInfoT = true)
    (hrd : chkTags t readInfoT = true) (hctx : chkTags t (stepRestT.take 3) = true)
    (hl : TagsIn (t :: valTags) (adminsToV c.code)) {u : MixopS} {x : Value}
    (ha : adminToV a = .case u x) (hu : u ∉ t :: valTags) (hcr : u ≠ "CALL_REF")
    (hrig : deepRigid a = true) :
    (∃ i, 6 ≤ i ∧
      Round6.Reading.FiresB EB "Step" i (.tuple [configV hn c, configV hn ⟨s', f', [a]⟩])) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) → w = configV hn ⟨s', f', [a]⟩ := by
  have hr : deepRigidL ([a] : List Admin) = true := by simp [hrig]
  obtain ⟨⟨i, hi, w, hfi, hrel⟩, hall⟩ := single_builtins (hinj := hinj) (hf := hf) (hh := hh)
    hc hs hnc hp hrd hctx hl ha hu hcr
  exact ⟨⟨i, hi, cfgRel_exact_deep hrel hr ▸ hfi⟩,
    fun w' hw' => cfgRel_exact_deep (hall w' hw') hr⟩

/-! ## The rules -/

/-- **`struct.new` at `builtins`, exactly.** -/
theorem structNew_exact {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {vs : List Val} (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hn' : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩) :
    let c' : Config H := ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) =>
      packField (fieldStorage ft) v⟩, f, [.ref (.struct s.structs.length)]⟩
    (∃ i, 6 ≤ i ∧ Round6.Reading.FiresB EB "Step" i
        (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩, configV hn c'])) ∧
      ∀ w, (SB).D "Step" "%~>%" []
        (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩, w]) →
        w = configV hn c' := by
  have hk := chk_arity
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hl, hnc⟩ := flat_shape vs (.structNew x) rfl
  exact tail_exact (hinj := hinj) (hf := hf) (hh := hh) hc
    (.aggregate (.structNew hd he hn' hp)) hnc hk.1.1.1.1.1.1.1.1.1.1.1
    hk.1.1.1.1.1.1.1.1.1.1.2 hk.1.1.1.1.1.1.1.1.1.2 hk.1.1.1.1.1.1.1.1.2 hl
    (by rw [getLast?_vals_last]; rfl) (by simp [adminsToV])
    (noTag_of_heads (by simp [Typing.adminHead, Typing.refHead])) rfl

/-- **`array.new_fixed` at `builtins`, exactly.** -/
theorem arrayNewFixed_exact {s : Store H} {f : Frame} {x : TypeIdx} {n : Fin (2 ^ 32)}
    {d : DefType} {ft : Silmaril.Wasm.Validation.CFieldType} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hn' : vs.length = n.val)
    (hp : ∀ v ∈ vs, packable (fieldStorage ft) v)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩) :
    let c' : Config H :=
      ⟨s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩, f, [arrRef s.arrays.length]⟩
    (∃ i, 6 ≤ i ∧ Round6.Reading.FiresB EB "Step" i
        (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩, configV hn c'])) ∧
      ∀ w, (SB).D "Step" "%~>%" []
        (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩, w]) →
        w = configV hn c' := by
  have hk := chk_arity
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hl, hnc⟩ := flat_shape vs (.arrayNewFixed x n) rfl
  exact tail_exact (hinj := hinj) (hf := hf) (hh := hh) hc
    (.aggregate (.arrayNewFixed hd he hn' hp)) hnc hk.1.1.1.1.1.1.1.2
    hk.1.1.1.1.1.1.2 hk.1.1.1.1.1.2 hk.1.1.1.1.2 hl
    (by rw [getLast?_vals_last]; rfl) (by simp [adminsToV])
    (noTag_of_heads (by simp [arrRef, Typing.adminHead, Typing.refHead])) rfl

/-- **`throw` at `builtins`, exactly.** -/
theorem throw_exact {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat}
    {ti : TagInst} {ts : Ty (.list .val)} (ht : s.tag? f x = some (ta, ti))
    (he : Expand ti.type (.func ts .nil)) (hn' : vs.length = ts.length)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, vals vs ++ [.plain (.throw x)]⟩) :
    let c' : Config H := ⟨s.addExn ⟨ta, vs⟩, f, throwing s.exns.length⟩
    (∃ i, 6 ≤ i ∧ Round6.Reading.FiresB EB "Step" i
        (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.throw x)]⟩, configV hn c'])) ∧
      ∀ w, (SB).D "Step" "%~>%" []
        (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.throw x)]⟩, w]) →
        w = configV hn c' := by
  have hk := chk_arity
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hl, hnc⟩ := flat_shape vs (.throw x) rfl
  exact tail_exact (hinj := hinj) (hf := hf) (hh := hh) hc (.throw ht he hn') hnc
    hk.1.1.1.2 hk.1.1.2 hk.1.2 hk.2 hl
    (by rw [getLast?_vals_last]; rfl) (by simp [adminsToV])
    (noTag_of_heads (by simp [Typing.adminHead, Typing.refHead, Typing.instrHead])) rfl

/-- **`call_ref-null` at `builtins`, exactly.** -/
theorem callRefNull_exact {s : Store H} {f : Frame} {c : Admin} (hcr : c.IsCallRef)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, [.ref .null, c]⟩) :
    (∃ i, 6 ≤ i ∧ Round6.Reading.FiresB EB "Step" i
        (.tuple [configV hn ⟨s, f, [.ref .null, c]⟩, configV hn ⟨s, f, [.trap]⟩])) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn ⟨s, f, [.ref .null, c]⟩, w]) →
        w = configV hn ⟨s, f, [.trap]⟩ := by
  have hk := chk_callRef
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hl, hnc⟩ := callRef_shape [] .null hcr (by decide)
  exact single_exact (hinj := hinj) (hf := hf) (hh := hh) hc (.callRefNull hcr) hnc
    hk.1.1 hk.1.2 hk.2 hl rfl (by decide) (by decide) rfl

/-- **`call_ref-func` at `builtins`, up to `CfgRel`.** -/
theorem callRefFunc_builtins {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func} (hcr : c.IsCallRef)
    (hfa : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn' : vs.length = ps.length) (hcode : fi.code = .wasm code)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) :
    let c' : Config H := ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]]⟩
    (∃ i, 6 ≤ i ∧ ∃ w, Round6.Reading.FiresB EB "Step" i
        (.tuple [configV hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩, w]) ∧
        SpecTec.CfgRel hn (configV hn c') w) ∧
      ∀ w, (SB).D "Step" "%~>%" []
        (.tuple [configV hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩, w]) →
        SpecTec.CfgRel hn (configV hn c') w := by
  have hk := chk_callRef
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hl, hnc⟩ := callRef_shape vs (.func a) hcr (by simp [Typing.adminHead, Typing.refHead, valTags])
  exact single_builtins (hinj := hinj) (hf := hf) (hh := hh) hc
    (.callRefFunc hcr hfa he hn' hcode) hnc hk.1.1 hk.1.2 hk.2 hl rfl (by decide) (by decide)

/-- **`call_ref-func` at `builtins`, exactly**, when the function body has no `call_ref` at the
top. -/
theorem callRefFunc_exact {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func} (hcr : c.IsCallRef)
    (hfa : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn' : vs.length = ps.length) (hcode : fi.code = .wasm code) (hcf : callFree code.body = true)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) :
    let c' : Config H := ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]]⟩
    (∃ i, 6 ≤ i ∧ Round6.Reading.FiresB EB "Step" i
        (.tuple [configV hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩, configV hn c'])) ∧
      ∀ w, (SB).D "Step" "%~>%" []
        (.tuple [configV hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩, w]) →
        w = configV hn c' := by
  have hk := chk_callRef
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hl, hnc⟩ := callRef_shape vs (.func a) hcr (by simp [Typing.adminHead, Typing.refHead, valTags])
  exact single_exact (hinj := hinj) (hf := hf) (hh := hh) hc
    (.callRefFunc hcr hfa he hn' hcode) hnc hk.1.1 hk.1.2 hk.2 hl rfl (by decide) (by decide)
    (by simp [deepRigidL_expression, hcf])

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30D
