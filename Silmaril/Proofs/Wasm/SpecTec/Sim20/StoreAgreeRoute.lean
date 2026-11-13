module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeCtx
public import Silmaril.Wasm.SpecTec.Sim10.Route.Thms
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The 1.0 → 2.0-script composite at `simEnv20T`

`Sim10.Task.composite10` is stated over `StepFix.simEnv20S`, where no configuration whose code or
store holds a `STORE` has a typed image, so its forward condition `Fwd20` is discharged only on
store-free sets. Here the target is `StoreFix.simEnv20T`:

* `Fwd20T`, **`Task.composite10T20`** (stated and proved, `composite10T20`): the composite route
  of `Sim10.composite10` with `simEnv20T` in place of `simEnv20S`;
* `fwd20T_of_fwd20`: under `ElseAgree20T B`, `Fwd20` at `simEnv20S B` gives `Fwd20T` at
  `simEnv20T B` on the same set (`sstepB20T_of_sstepB20S`);
* `StoreCtx20`, `StoreCtxOk20`, `GoodStore20T`: a scalar store under a value prefix and a suffix,
  from a state typed in `simEnv20`, with a suffix typed in `simEnv20T` and pack sizes below the
  width; **`fwd20T_goodStore20T`**: `Fwd20T` holds on `GoodStore20T` with no further hypothesis
  (`fwdT_storeCtx`);
* `GoodT20 = Good20C ∨ GoodStore20T`; **`fwd20T_goodT20`**: `Fwd20T` holds on it under
  `ElseAgree20T`;
* `storeCtxOk20_memStore`, `sstepT_memStore`: a configuration with a store below the top of the
  code (`i32.const 0; i32.const 0; i32.store; nop` over one memory page) satisfies the hypotheses
  of `fwdT_storeCtx` and steps in `simEnv20T`, so the store part is not vacuous.

What is not proved: that every V2 step from the example is the store step (the step-shape clause
of `GoodStore20T` needs an inversion of V2's `Step` on concrete code), and `ElseAgree20T`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.Whole (StoreTop20 storeB Good20C)
open Silmaril.Wasm.SpecTec.Sim10 (Fwd20 RunGood20)

variable {H : Type}

/-! ## The composite at `simEnv20T` -/

/-- **The 2.0 forward obligation at `simEnv20T`.** -/
def Fwd20T (hn : H → String) (host20 : HostSemantics H) (B : Builtins)
    (Good : Config H → Prop) : Prop :=
  ∀ c c', Good c → Step v2Profile host20 c c' →
    Relation.TransGen (SStepB (simEnv20T B)) (configV hn c) (configV hn c')

theorem transGen_fwd20T {hn : H → String} {tgt : HostSemantics H} {B : Builtins}
    {Good : Config H → Prop} (hF : Fwd20T hn tgt B Good) {c c' : Config H}
    (h : Relation.TransGen (Step v2Profile tgt) c c') (hg : RunGood20 tgt Good c) :
    Relation.TransGen (SStepB (simEnv20T B)) (configV hn c) (configV hn c') := by
  induction h with
  | single h => exact hF _ _ (hg _ .refl) h
  | @tail c₁ c₂ h₁ h₂ ih => exact ih.trans (hF _ _ (hg c₁ h₁.to_reflTransGen) h₂)

/-- **The 1.0 → 2.0-script composite route at `simEnv20T`** (stated and proved). -/
def Task.composite10T20 : Prop :=
  ∀ (H : Type) (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : HostSemantics H) (B : Builtins) (Good : Config H → Prop),
    Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt → Fwd20T hn tgt B Good →
    ∀ (a b : V1.Execution.Config H) (c : Config H), V1.Execution.Step src a b →
      Lime1.Execution.ToV2.Sim a.toLime c → RunGood20 tgt Good c →
      ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
        Relation.TransGen (SStepB (simEnv20T B)) (configV hn c) (configV hn c')

/-- **`Task.composite10T20` holds**: `Sim10.composite10`'s proof, at `simEnv20T`. -/
theorem composite10T20 : Task.composite10T20 := by
  intro H hn src tgt B Good hosts hF a b c hab hs hg
  obtain ⟨c', hcc, hs'⟩ := V1.Execution.Step.toV2 hosts hab hs
  exact ⟨c', hs', transGen_fwd20T hF hcc hg⟩

/-- Under `ElseAgree20T`, a run of `simEnv20S B` is a run of `simEnv20T B`. -/
theorem transGen_T {B : Builtins} (hE : ElseAgree20T B) {v w : Value}
    (h : Relation.TransGen (SStepB (StepFix.simEnv20S B)) v w) :
    Relation.TransGen (SStepB (simEnv20T B)) v w := by
  induction h with
  | single h => exact .single (sstepB20T_of_sstepB20S hE h)
  | tail _ h ih => exact .tail ih (sstepB20T_of_sstepB20S hE h)

/-- Under `ElseAgree20T`, the forward obligation at `simEnv20S` gives the one at `simEnv20T`. -/
theorem fwd20T_of_fwd20 {hn : H → String} {tgt : HostSemantics H} {B : Builtins}
    {Good : Config H → Prop} (hE : ElseAgree20T B) (h : Fwd20 hn tgt B Good) :
    Fwd20T hn tgt B Good := fun c c' hg hs => transGen_T hE (h c c' hg hs)

/-! ## Stores under a context -/

/-- A scalar store under a value prefix and a suffix. -/
inductive StoreCtx20 : Config H → Config H → Prop where
  | mk {s s' : Store H} {f f' : Frame} {code code' : List Admin} (vs : List Val)
      (rest : List Admin) (h : StoreTop20 ⟨s, f, code⟩ ⟨s', f', code'⟩) :
      StoreCtx20 ⟨s, f, vals vs ++ code ++ rest⟩ ⟨s', f', vals vs ++ code' ++ rest⟩

/-- Every such step is a V2 step. -/
theorem StoreCtx20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : StoreCtx20 c c') : Step P host c c' := by
  obtain ⟨vs, rest, h⟩ := h
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact .ctxtInstrs h.step hne
  · obtain ⟨rfl, rfl⟩ : vs = [] ∧ rest = [] := by simpa [not_or] using hne
    simpa [vals] using h.step

/-- **A store under a context, with the hypotheses of `fwdT_storeCtx`.** -/
def StoreCtxOk20 (hn : H → String) (P : Profile) (c c' : Config H) : Prop :=
  ∃ (s s' : Store H) (f f' : Frame) (code code' : List Admin) (vs : List Val) (rest : List Admin),
    c = ⟨s, f, vals vs ++ code ++ rest⟩ ∧ c' = ⟨s', f', vals vs ++ code' ++ rest⟩ ∧
    StoreTop20 ⟨s, f, code⟩ ⟨s', f', code'⟩ ∧
    TypedV (simEnv20 (storeB P)) stateT (stateV hn s f) ∧
    TypedV (simEnv20T (storeB P)) adminsTy (.list (adminsToV rest)) ∧ PackOk20 code

theorem StoreCtxOk20.storeCtx {hn : H → String} {P : Profile} {c c' : Config H}
    (h : StoreCtxOk20 hn P c c') : StoreCtx20 c c' := by
  obtain ⟨s, s', f, f', code, code', vs, rest, rfl, rfl, h, -⟩ := h
  exact .mk vs rest h

/-- **Such a store is a step of `simEnv20T (storeB P)`.** -/
theorem fwd_storeCtxOk20 {hn : H → String} {P : Profile} {c c' : Config H}
    (h : StoreCtxOk20 hn P c c') : SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  obtain ⟨s, s', f, f', code, code', vs, rest, rfl, rfl, h, hz, hrest, hp⟩ := h
  exact fwdT_storeCtx (Whole.floatB_storeB P) (Whole.laneCalls20_storeB P) (Whole.nbytes20_storeB P)
    vs rest hz hrest hp h

/-- **The configurations whose every V2 step is such a store.** -/
def GoodStore20T (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c', Step P host c c' → StoreCtxOk20 hn P c c'

/-- **`Fwd20T` holds on `GoodStore20T`**, with no further hypothesis. -/
theorem fwd20T_goodStore20T (hn : H → String) (host : HostSemantics H) :
    Fwd20T hn host (storeB v2Profile) (GoodStore20T hn v2Profile host) :=
  fun _ _ hg h => .single (fwd_storeCtxOk20 (hg _ h))

/-- Covered store-free configurations, or configurations whose every step is a store under a
context. -/
def GoodT20 (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  Good20C hn P c ∨ GoodStore20T hn P host c

/-- **`Fwd20T` holds on `GoodT20`**, under `ElseAgree20T`. -/
theorem fwd20T_goodT20 (hn : H → String) (host : HostSemantics H)
    (hE : ElseAgree20T (storeB v2Profile)) :
    Fwd20T hn host (storeB v2Profile) (GoodT20 hn v2Profile host) := by
  rintro c c' (hg | hg) h
  · exact .single (sstepB20T_of_sstepB20S hE (Whole.fwd_good20C hg h).2)
  · exact .single (fwd_storeCtxOk20 (hg _ h))

/-! ## Non-vacuity of the store part -/

/-- One empty memory and nothing else. -/
def memOnlyStore : Store Empty := { mems := [⟨⟨⟨0, none⟩⟩, ByteArray.empty⟩] }

/-- `i32.const 0; i32.const 0; i32.store; nop` over that memory. -/
def memStoreCfg2 : Config Empty :=
  ⟨memOnlyStore, StoreFix.memFrame, [constI32 0, .plain (.intConst .i32 0), .plain StoreFix.i32Store0,
    .plain .nop]⟩

/-- Its successor: the store traps. -/
def memStoreCfg2' : Config Empty := ⟨memOnlyStore, StoreFix.memFrame, [.trap, .plain .nop]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem typedV_memOnly (P : Profile) :
    TypedV (simEnv20 (storeB P)) stateT (stateV Empty.elim memOnlyStore StoreFix.memFrame) :=
  typedV_of_empty ⟨300, by with_unfolding_all rfl⟩

theorem typedV_nop20T (B : Builtins) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV [.plain .nop])) :=
  StoreFix.typedV_nopM

/-- **The example satisfies the hypotheses of `fwdT_storeCtx`.** -/
theorem storeCtxOk20_memStore (P : Profile) :
    StoreCtxOk20 Empty.elim P memStoreCfg2 memStoreCfg2' :=
  ⟨memOnlyStore, memOnlyStore, StoreFix.memFrame, StoreFix.memFrame,
    [constI32 0, .plain (.intConst .i32 0), .plain StoreFix.i32Store0], [.trap], [], [.plain .nop],
    rfl, rfl, .intTrap (a := 0) rfl rfl (by decide), typedV_memOnly P, typedV_nop20T _,
    fun _ _ _ h => by simp at h⟩

/-- **It steps in `simEnv20T` below the top of the code.** -/
theorem sstepT_memStore (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim memStoreCfg2) (configV Empty.elim memStoreCfg2') :=
  fwd_storeCtxOk20 (storeCtxOk20_memStore P)

/-- **And V2 steps it there.** -/
theorem step_memStore (P : Profile) (host : HostSemantics Empty) :
    Step P host memStoreCfg2 memStoreCfg2' :=
  (storeCtxOk20_memStore P).storeCtx.step

end Silmaril.Wasm.SpecTec.Sim20.StoreAgree
