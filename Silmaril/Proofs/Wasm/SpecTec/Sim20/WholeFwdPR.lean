module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeNest
public import Silmaril.Wasm.SpecTec.Sim20.Pure.Thms
public import Silmaril.Wasm.SpecTec.Sim20.State.Thms

/-!
# The pure and read rules forward, assembled into fragments

Pass 5 left the Pure and State tracks' per-rule iffs and the lifting lemmas `fwdS_pure`/`fwdS_read`
unassembled. This module assembles them into two base fragments for `fwd_nest20`:

* `typedV_admin_val20`: every V2 value is an `admininstr` (each case of `val` is declared, with
  the same premise-free payload type, in `admininstr`). This is the subject-reduction ingredient
  for rules whose result is a value.
* **`PureFrag20 P`**: fifteen `PureStep` constructors, with V2's premises (`intUnOp` also carries
  `op.valid t`, which `Pure.intUnOp_iff` needs): `unreachable`, `nop`, `drop`, `label-vals`,
  `frame-vals`, `trap-label`, `trap-frame`, and the numeric `unop` (integer and float), `binop`
  (integer and float), `binop-trap` (integer), `testop` and `relop` (integer and float).
  `spure_of_pureFrag20`: at `NumAgree` builtins each is a `Step_pure` derivation of the original
  script from a typed image, through the Pure track's iffs. `fwdBase20_pure`: `PureFwd20 P` (these
  steps at any state) is a `FwdBase20` at every store condition.
* **`ReadFwd20`**: `local.get`, `global.get` and `ref.func` where V2's lookups are defined
  (`State.localGet_iff`, `globalGet_iff`, `refFunc_iff`); `fwdBase20_read`.
* **`FwdStep20 P`**: `TopVStep20`, `PureFwd20` and `ReadFwd20` together, closed under the three
  contexts. **`Task.wholeStepFwd20`** (stated and proved, `wholeStepFwd20`): at `growB`, every
  `Nest20 (FwdStep20 P)` step from a typed image with whole pages is a corrected-script step with
  a typed successor image. Every such step is a V2 step (`FwdStep20.step`, `Nest20.step`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (TypedV SPure SRead Fires dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB FiresB)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase recCases instCases)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.Pure (NumAgree)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d282 Original.d295)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Values are administrative instructions -/

/-- A case declared alike in `val` and `admininstr` moves from one to the other. -/
theorem typedV_admin_ofVal20 {op : MixopS} {t : Typ} {w : Value}
    (hv : findCase (instCases Original.d282 0) op = some (t, []))
    (ha : findCase (recCases Original.d295 0 0) op = some (t, []))
    (h : TypedV (simEnv20 B) Pure.valT (.case op w)) :
    TypedV (simEnv20 B) (.varT "admininstr" []) (.case op w) := by
  obtain ⟨op', w', he, hc⟩ :=
    hasTypDef_variantT_iff.1 (hasTypDef_of_closed Pure.findTyp_val20 (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he
  exact Pure.typedV_closedCase20 findTyp_admininstr20 ha (Sim.IntNumeric.hasTyp_of_hasTypCase hc hv)

/-- **Every V2 value is an `admininstr`.** -/
theorem typedV_admin_val20 : ∀ v : Val,
    TypedV (simEnv20 B) (.varT "admininstr" []) (valV v)
  | .num n => typedV_admin_num20 n
  | .vec b => typedV_admin_ofVal20 rfl rfl (typedV_val20 (.vec b))
  | .ref (.null t) => typedV_admin_ofVal20 rfl rfl (typedV_val20 (.ref (.null t)))
  | .ref (.funcAddr a) => typedV_admin_ofVal20 rfl rfl (typedV_val20 (.ref (.funcAddr a)))
  | .ref (.hostAddr a) => typedV_admin_ofVal20 rfl rfl (typedV_val20 (.ref (.hostAddr a)))

/-- A value sequence is a typed `admininstr*`. -/
theorem typedV_admins_vals20 (vs : List Val) :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV (vals vs))) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  rw [Pure.adminsToV_vals] at hu
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
  exact typedV_admin_val20 v

/-- One value is a typed `admininstr*`. -/
theorem typedV_admins_val20 (v : Val) :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV [v.toAdmin])) := by
  simpa [vals] using typedV_admins_vals20 (B := B) [v]

/-- `vals vs` is a typed `val*`. -/
theorem typedV_valsT_vals20 (vs : List Val) :
    TypedV (simEnv20 B) Pure.valsT (.list (adminsToV (vals vs))) := by
  rw [Pure.adminsToV_vals]
  exact typedV_vals20 vs

/-! ## The pure fragment -/

/-- **Fifteen `PureStep` rules**, with V2's premises (`intUnOp` also with `op.valid t`). -/
inductive PureFrag20 (P : Profile) : List Admin → List Admin → Prop where
  | unreachable : PureFrag20 P [.plain .unreachable] [.trap]
  | nop : PureFrag20 P [.plain .nop] []
  | drop (v : Val) : PureFrag20 P [v.toAdmin, .plain .drop] []
  | labelVals {n : Nat} {cont : List Silmaril.Wasm.V2.Instr} {vs : List Val} :
      PureFrag20 P [.label n cont (vals vs)] (vals vs)
  | frameVals {n : Nat} {fr : Frame} {vs : List Val} (hn : vs.length = n) :
      PureFrag20 P [.frame n fr (vals vs)] (vals vs)
  | trapLabel {n : Nat} {cont : List Silmaril.Wasm.V2.Instr} :
      PureFrag20 P [.label n cont [.trap]] [.trap]
  | trapFrame {n : Nat} {fr : Frame} : PureFrag20 P [.frame n fr [.trap]] [.trap]
  | intUnOp {t : IntType} {op : IntUnOp} {x z : BitVec t.width} (hop : op.valid t)
      (h : IntUnOpResult t op x z) :
      PureFrag20 P [.plain (.intConst t x), .plain (.intUnOp t op)] [.plain (.intConst t z)]
  | floatUnOp {t : FloatType} {op : FloatUnOp} {x z : BitVec t.width}
      (h : FloatUnOpResult P t op x z) :
      PureFrag20 P [.plain (.floatConst t x), .plain (.floatUnOp t op)] [.plain (.floatConst t z)]
  | intBinOp {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
      (h : IntBinOpResult t op x y z) :
      PureFrag20 P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)]
        [.plain (.intConst t z)]
  | floatBinOp {t : FloatType} {op : FloatBinOp} {x y z : BitVec t.width}
      (h : FloatBinOpResult P t op x y z) :
      PureFrag20 P [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatBinOp t op)]
        [.plain (.floatConst t z)]
  | intBinOpTrap {t : IntType} {op : IntBinOp} {x y : BitVec t.width}
      (h : IntBinOpTraps t op x y) :
      PureFrag20 P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)] [.trap]
  | testOp {t : IntType} {op : IntTestOp} {x : BitVec t.width} :
      PureFrag20 P [.plain (.intConst t x), .plain (.intTestOp t op)] [constI32 (testOp t op x)]
  | intRelOp {t : IntType} {op : IntRelOp} {x y : BitVec t.width} :
      PureFrag20 P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intRelOp t op)]
        [constI32 (intRelOp t op x y)]
  | floatRelOp {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width} :
      PureFrag20 P [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatRelOp t op)]
        [constI32 (floatRelOp t op x y)]

/-- Every rule of the fragment is a V2 `PureStep`. -/
theorem PureFrag20.pureStep {P : Profile} {is is' : List Admin} (h : PureFrag20 P is is') :
    PureStep P is is' := by
  cases h with
  | unreachable => exact .unreachable
  | nop => exact .nop
  | drop v => exact .drop v
  | labelVals => exact .labelVals
  | frameVals hn => exact .frameVals hn
  | trapLabel => exact .trapLabel
  | trapFrame => exact .trapFrame
  | intUnOp _ h => exact .intUnOp h
  | floatUnOp h => exact .floatUnOp h
  | intBinOp h => exact .intBinOp h
  | floatBinOp h => exact .floatBinOp h
  | intBinOpTrap h => exact .intBinOpTrap h
  | testOp => exact .testOp
  | intRelOp => exact .intRelOp
  | floatRelOp => exact .floatRelOp

/-- A firing of `Step_pure` under the backend reading is a `Step_pure` derivation. -/
theorem spure_of_firesB20 {i : Nat} {is js : List Value}
    (h : FiresB (simEnv20 B) "Step_pure" i (.tuple [.list is, .list js])) :
    SPure (simEnv20 B) is js := by
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20 B).findRel? "Step_pure" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩
  exact (dderives_iff_fires hrel).2 ⟨i, (Pure.firesB_pure20_iff B).1 h⟩

/-- The arity and continuation of a typed single label. -/
theorem label_parts20 {n : Nat} {cont : List Silmaril.Wasm.V2.Instr} {body : List Admin}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV [.label n cont body]))) :
    TypedV (simEnv20 B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV cont)) := by
  obtain ⟨h₁, h₂, -⟩ := typedV_adminLabel20_iff.1 (typedV_admins_single20_iff.1 hc)
  exact ⟨h₁, h₂⟩

/-- The arity and frame of a typed single frame. -/
theorem frame_parts20 {n : Nat} {fr : Frame} {body : List Admin}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV [.frame n fr body]))) :
    TypedV (simEnv20 B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20 B) Pure.frameT (frameV fr) := by
  obtain ⟨h₁, h₂, -⟩ := typedV_adminFrame20_iff.1 (typedV_admins_single20_iff.1 hc)
  exact ⟨h₁, h₂⟩

/-- **Every rule of the pure fragment, from a typed image, is a `Step_pure` derivation of the
original script**, at `NumAgree` builtins. -/
theorem spure_of_pureFrag20 {P : Profile} (A : NumAgree (simEnv20 B) P) {is is' : List Admin}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV is))) (h : PureFrag20 P is is') :
    SPure (simEnv20 B) (adminsToV is) (adminsToV is') := by
  have T : Pure.NumTyped (simEnv20 B) := Pure.numTyped_simEnv20 B
  cases h with
  | unreachable => exact spure_of_firesB20 ((Pure.unreachable_iff B).2 rfl)
  | nop => exact spure_of_firesB20 ((Pure.nop_iff B).2 rfl)
  | drop v => exact spure_of_firesB20 ((Pure.drop_iff B (typedV_val20 v)).2 rfl)
  | labelVals =>
    obtain ⟨h₁, h₂⟩ := label_parts20 hc
    exact spure_of_firesB20 ((Pure.labelVals_iff B h₁ h₂ (typedV_valsT_vals20 _)).2 rfl)
  | frameVals hn =>
    obtain ⟨h₁, h₂⟩ := frame_parts20 hc
    exact spure_of_firesB20 ((Pure.frameVals_iff B h₁ h₂ (typedV_valsT_vals20 _)).2 ⟨hn, rfl⟩)
  | trapLabel =>
    obtain ⟨h₁, h₂⟩ := label_parts20 hc
    exact spure_of_firesB20 ((Pure.trapLabel_iff B h₁ h₂).2 rfl)
  | trapFrame =>
    obtain ⟨h₁, h₂⟩ := frame_parts20 hc
    exact spure_of_firesB20 ((Pure.trapFrame_iff B h₁ h₂).2 rfl)
  | intUnOp hop h => exact spure_of_firesB20 ((Pure.intUnOp_iff B A T hop).2 ⟨_, h, rfl⟩)
  | floatUnOp h => exact spure_of_firesB20 ((Pure.floatUnOp_iff B A T).2 ⟨_, h, rfl⟩)
  | intBinOp h => exact spure_of_firesB20 ((Pure.intBinOp_iff B A T).2 ⟨_, h, rfl⟩)
  | floatBinOp h => exact spure_of_firesB20 ((Pure.floatBinOp_iff B A T).2 ⟨_, h, rfl⟩)
  | intBinOpTrap h => exact spure_of_firesB20 ((Pure.intBinOpTrap_iff B A T).2 ⟨h, rfl⟩)
  | testOp => exact spure_of_firesB20 ((Pure.testOp_iff B A T).2 rfl)
  | intRelOp => exact spure_of_firesB20 ((Pure.intRelOp_iff B A T).2 rfl)
  | floatRelOp => exact spure_of_firesB20 ((Pure.floatRelOp_iff B A T).2 rfl)

/-- **Subject reduction for the pure fragment**: the result code is a typed `admininstr*`. -/
theorem typedV_succ_pureFrag20 {P : Profile} {is is' : List Admin}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV is))) (h : PureFrag20 P is is') :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV is')) := by
  cases h with
  | unreachable | trapLabel | trapFrame | intBinOpTrap _ => exact typedV_admins_trap20
  | nop | drop _ => exact typedV_admins_nil20
  | labelVals | frameVals _ => exact typedV_admins_vals20 _
  | intUnOp _ _ | intBinOp _ => exact typedV_admins_val20 (.num ⟨.int _, _⟩)
  | floatUnOp _ | floatBinOp _ => exact typedV_admins_val20 (.num ⟨.float _, _⟩)
  | testOp | intRelOp | floatRelOp => exact typedV_admins_const20 _

/-- **The pure fragment at any state.** -/
inductive PureFwd20 (P : Profile) : Config H → Config H → Prop where
  | mk {s : Store H} {f : Frame} {is is' : List Admin} (h : PureFrag20 P is is') :
      PureFwd20 P ⟨s, f, is⟩ ⟨s, f, is'⟩

/-- **The pure fragment is a base**, at `NumAgree` builtins and any store condition. -/
theorem fwdBase20_pure {P : Profile} {W : Store H → Prop} (A : NumAgree (simEnv20 B) P) :
    FwdBase20 B hn W (PureFwd20 P) where
  sr _ _ hc h := by
    cases h with
    | mk h =>
      obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
      exact typed20_iff.2 ⟨hz, typedV_succ_pureFrag20 hcode h⟩
  fwd _ _ hc _ h := by
    cases h with
    | mk h =>
      obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
      exact fwdS_pure hc (typed20_iff.2 ⟨hz, typedV_succ_pureFrag20 hcode h⟩)
        (spure_of_pureFrag20 A hcode h)

/-! ## The read fragment -/

/-- **`local.get`, `global.get` and `ref.func`**, where V2's lookups are defined. -/
inductive ReadFwd20 : Config H → Config H → Prop where
  | localGet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
      (hv : f.locals[x.toNat]? = some v) :
      ReadFwd20 ⟨s, f, [.plain (.localGet x)]⟩ ⟨s, f, [v.toAdmin]⟩
  | globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
      (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g) :
      ReadFwd20 ⟨s, f, [.plain (.globalGet x)]⟩ ⟨s, f, [g.value.toAdmin]⟩
  | refFunc {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
      (ha : f.module.funcs[x.toNat]? = some a) :
      ReadFwd20 ⟨s, f, [.plain (.refFunc x)]⟩ ⟨s, f, [.refFuncAddr a]⟩

/-- Every read step of the fragment is a V2 step. -/
theorem ReadFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : ReadFwd20 c c') : Step P host c c' := by
  cases h with
  | localGet hv => exact .read (State.localGet_step hv)
  | globalGet ha hg => exact .read (State.globalGet_step ha hg)
  | refFunc ha => exact .read (State.refFunc_step ha)

/-- A firing of `Step_read` under the backend reading is a `Step_read` derivation. -/
theorem sread_of_firesB20 {i : Nat} {c : Value} {js : List Value}
    (h : FiresB (simEnv20 B) "Step_read" i (.tuple [c, .list js])) :
    SRead (simEnv20 B) c js := by
  obtain ⟨t, rules, hrel⟩ := findRel_read20 B
  exact (dderives_iff_fires hrel).2 ⟨i,
    (Sim.Round6.Reading.firesB_iff_of_closed (closed_step20 B) (by simp)).1 h⟩

/-- **Subject reduction for the read fragment.** -/
theorem typed20_succ_read20 {c c' : Config H} (hc : Typed20 (simEnv20 B) hn c)
    (h : ReadFwd20 c c') : Typed20 (simEnv20 B) hn c' := by
  cases h with
  | localGet _ => exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_val20 _⟩
  | globalGet _ _ => exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_val20 _⟩
  | refFunc _ =>
    exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_val20 (.ref (.funcAddr _))⟩

/-- **The read fragment is a base**, at every builtins and any store condition. -/
theorem fwdBase20_read {W : Store H → Prop} : FwdBase20 B hn W (ReadFwd20 (H := H)) where
  sr _ _ hc h := typed20_succ_read20 hc h
  fwd _ _ hc _ h := by
    have hz := typedV_state_of_typed20 hc
    have hc' := typed20_succ_read20 hc h
    cases h with
    | localGet hv =>
      exact fwdS_read hc hc' (sread_of_firesB20 ((State.localGet_iff B hn hv hz
        (typedV_idx20 _)).2 rfl))
    | globalGet ha hg =>
      exact fwdS_read hc hc' (sread_of_firesB20 ((State.globalGet_iff B hn ha hg hz
        (typedV_idx20 _)).2 rfl))
    | refFunc ha =>
      exact fwdS_read hc hc' (sread_of_firesB20 ((State.refFunc_iff B hn ha hz
        (typedV_idx20 _)).2 rfl))

/-! ## One forward statement -/

/-- **The assembled base**: the top-level store and variable steps, the pure fragment and the
read fragment. -/
inductive FwdStep20 (P : Profile) : Config H → Config H → Prop where
  | top {c c' : Config H} (h : TopVStep20 P c c') : FwdStep20 P c c'
  | pure {c c' : Config H} (h : PureFwd20 P c c') : FwdStep20 P c c'
  | read {c c' : Config H} (h : ReadFwd20 c c') : FwdStep20 P c c'

/-- Every assembled base step is a V2 step. -/
theorem FwdStep20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20 P c c') : Step P host c c' := by
  cases h with
  | top h => exact h.step
  | pure h =>
    cases h with
    | mk h => exact .pure h.pureStep
  | read h => exact h.step

/-- **The assembled base is a base**, at `GrowCalls20` and `NumAgree` builtins, under whole
pages. -/
theorem fwdBase20_fwd {P : Profile} (hG : GrowCalls20 B) (A : NumAgree (simEnv20 B) P) :
    FwdBase20 B hn WholePages (FwdStep20 (H := H) P) where
  sr c c' hc h := by
    cases h with
    | top h => exact (fwdBase20_topV hG).sr c c' hc h
    | pure h => exact (fwdBase20_pure (W := WholePages) A).sr c c' hc h
    | read h => exact (fwdBase20_read (W := WholePages)).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | top h => exact (fwdBase20_topV hG).fwd c c' hc hw h
    | pure h => exact (fwdBase20_pure A).fwd c c' hc hw h
    | read h => exact fwdBase20_read.fwd c c' hc hw h

/-- **The forward 2.0 half on the assembled nested fragment** (stated and proved): at `growB`,
every step of `Nest20 (FwdStep20 P)` (the top-level store and variable rules, fifteen pure rules
and three read rules, under any nesting of `ctxt-instrs`, `ctxt-label` and `ctxt-frame`) from a
configuration with typed image and whole pages is a step of the corrected script between the
images, with a typed successor image. -/
def Task.wholeStepFwd20 : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : RelaxedChoice) (c c' : Config H),
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn c → WholePages c.store →
    Nest20 (FwdStep20 (Profile.spec nd r)) c c' →
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn c' ∧
      SStepB (simEnv20S (growB (Profile.spec nd r))) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20` is proved.** -/
theorem wholeStepFwd20 : Task.wholeStepFwd20 := by
  intro H hn nd r c c' hc hw h
  have G := growLike20_growB (Profile.spec nd r)
  exact fwd_nest20 (fwdBase20_fwd G.calls (Pure.numAgree_simEnv20 G.int G.float)) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
