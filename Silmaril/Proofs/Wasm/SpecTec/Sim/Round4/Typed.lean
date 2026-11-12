module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Leaves

/-!
# Round 4: `ConfigOk ∧ Bounded → Typed`, reduced to the leaves

`typed_of_configOk`: a valid (`ConfigOk c ts`), bounded configuration is `Typed` in `simEnv B`,
given the positive typing of the encoding's leaves (`PosTyping B hn`: instructions, runtime
`CALL_REF` annotations, frame modules, stores). The proof follows Core's typing
derivation of the code (`AdminsOk`, `AdminOk`, by mutual recursion), so every nested label body,
handler body and frame body is reached with its own validity and bounds; values, references,
traps, catch clauses (`typedV_catch`) and the administrative `throw_ref` are typed outright, and labels, handlers and frames are
assembled by `typedV_label`, `typedV_handler`, `typedV_frame`.

Consequences:

* `oneStep_of_rel`: with `PosTyping`, the composable one-step simulation `OneStepRel` gives the
  frozen target's one-step simulation `OneStep` (take the witness to be `c`);
* `wholeStepValid_of`: `Task.wholeStepValid` follows from `PosTyping` and `OneStepRel` for some
  `B` per encoding, host and profile.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type} {B : Builtins} {hn : H → String}

/-- `AdminsBnd` splits over `++`. -/
theorem adminsBnd_append : ∀ {a b : List Admin}, AdminsBnd (a ++ b) ↔ AdminsBnd a ∧ AdminsBnd b
  | [], b => by simp [AdminsBnd]
  | x :: a, b => by
    simp only [List.cons_append, AdminsBnd]
    rw [adminsBnd_append]
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨⟨h₁, h₂⟩, h₃⟩, fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- A bounded instruction sequence is bounded as code. -/
theorem adminsBnd_expression : ∀ {l : List Instr}, instrsBnd l = true → AdminsBnd (expression l)
  | [], _ => trivial
  | i :: l, h => by
    simp only [instrsBnd, Bool.and_eq_true] at h
    exact ⟨h.1, adminsBnd_expression h.2⟩

set_option maxRecDepth 100000 in
/-- `TRAP` is a typed `instr`. -/
theorem typedV_trap : TypedV (simEnv B) (.varT "instr" []) (adminToV (.trap : Admin)) :=
  FwdMem.typedV_instrCase rfl rfl hasTyp_tupT_nil

set_option maxRecDepth 100000 in
/-- `THROW_REF` is a typed `instr`. -/
theorem typedV_throwRef : TypedV (simEnv B) (.varT "instr" []) (instrToV .throwRef) :=
  FwdMem.typedV_instrCase rfl rfl hasTyp_tupT_nil

/-- A reference is a typed `instr`. -/
theorem typedV_refAdmin (r : Ref) :
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.ref r)) :=
  Typing.typedV_instr_val (.ref r)

/-- A frame whose module is typed is a typed `frame`. -/
theorem typedV_frame_of {f : Frame}
    (hm : TypedV (simEnv B) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT f.module)) :
    TypedV (simEnv B) frameT (frameV f) := fun ρ hρ =>
  hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) Typing.findTyp_frame
    Equiv.evalArgs_nil matchArgs_nil
    (hasTypFields_cons_iff.2 ⟨_, _, rfl, Typing.hasTyp_locals f.locals, premsOk_nil,
      hasTypFields_cons_iff.2 ⟨_, _, rfl, hm _ ⟨rfl, rfl, rfl⟩, premsOk_nil,
        hasTypFields_nil_iff.2 rfl⟩⟩)

/-- The frame of a valid frame judgement, within SpecTec's syntax, is typed. -/
theorem typedV_frame_ok (K : PosTyping B hn) {s : Store H} {f : Frame} {C : Context}
    (hf : FrameOk s f C) (hb : ModuleBnd f.module) : TypedV (simEnv B) frameT (frameV f) := by
  obtain ⟨C₀, lts, hm, -, -⟩ := hf
  exact typedV_frame_of (K.moduleinst _ _ _ hm hb)

mutual
/-- **Every valid, bounded administrative instruction is typed**, by recursion on its typing. -/
theorem adminOk_typed (K : PosTyping B hn) {s : Store H} :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → AdminBnd a →
      TypedV (simEnv B) instrsT (.list [adminToV a])
  | _, _, _, .plain h, hb => typedV_list_single.2 (K.instr _ _ _ h hb)
  | _, _, _, .callRefType hok _, hb => typedV_list_single.2 (K.callRefType _ hok hb)
  | _, _, _, .returnCallRefType hok _ _ _ _, hb =>
    typedV_list_single.2 (K.returnCallRefType _ hok hb)
  | _, _, _, .ref _, _ => typedV_list_single.2 (typedV_refAdmin _)
  | _, _, _, .label (n := n) (cont := cont) _ hc hbody, hb => by
    have hcont := adminsOk_typed K hc (adminsBnd_expression hb.1)
    rw [adminsToV_expression] at hcont
    exact FwdMem.typedV_label ((Typing.stateTyping_simEnv B).nat n) hcont
      (adminsOk_typed K hbody hb.2)
  | _, _, _, .frame (n := n) hf _ hbody _, hb =>
    FwdMem.typedV_frame ((Typing.stateTyping_simEnv B).nat n) (typedV_frame_ok K hf hb.1)
      (adminsOk_typed K hbody hb.2)
  | _, _, _, .handler (n := n) _ hbody, hb =>
    FwdMem.typedV_handler ((Typing.stateTyping_simEnv B).nat n)
      (typedV_list_iff.2 fun u hu => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hu
        exact typedV_catch c)
      (adminsOk_typed K hbody hb)
  | _, _, _, .trap _, _ => typedV_list_single.2 typedV_trap
  | _, _, _, .throwRefInits _, _ => typedV_list_single.2 typedV_throwRef

/-- **Every valid, bounded code sequence is typed**, by recursion on its typing. -/
theorem adminsOk_typed (K : PosTyping B hn) {s : Store H} :
    ∀ {C : Context} {l : List Admin} {it : InstrType}, AdminsOk s C l it → AdminsBnd l →
      TypedV (simEnv B) instrsT (.list (adminsToV l))
  | _, _, _, .nil, _ => typedV_list_nil
  | _, _, _, .single h, hb => adminOk_typed K h hb.1
  | _, _, _, .seq h₁ _ h₂, hb => by
    obtain ⟨hb₁, hb₂⟩ := adminsBnd_append.1 hb
    rw [adminsToV_append]
    exact typedV_list_append.2 ⟨adminsOk_typed K h₁ hb₁, adminsOk_typed K h₂ hb₂⟩
  | _, _, _, .cons ha _ hs, hb => by
    have h₁ := adminOk_typed K ha hb.1
    have h₂ := adminsOk_typed K hs hb.2
    exact typedV_list_cons_iff.2 ⟨typedV_list_single.1 h₁, h₂⟩
  | _, _, _, .sub h _ _, hb => adminsOk_typed K h hb
  | _, _, _, .frame h _, hb => adminsOk_typed K h hb
end

/-- **`ConfigOk ∧ Bounded → Typed`**, given the positive typing of the leaves. -/
theorem typed_of_configOk (K : PosTyping B hn) {c : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hb : Bounded c) : Typed (simEnv B) hn c := by
  obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := hc
  have T := Typing.typingFacts_simEnv B hn
  exact (T.config c).2 ⟨(T.state _ _).2 ⟨K.store _ hs hb.store hb.storeBnd,
    typedV_frame_ok K hf hb.frame⟩, adminsOk_typed K hcode hb.code⟩

/-- **The composable simulation gives the frozen target's**, given `PosTyping`. -/
theorem oneStep_of_rel (K : PosTyping B hn) {P : Profile} {host : HostSemantics H}
    (h : OneStepRel B hn P host) : OneStep B hn P host := by
  unfold OneStep
  refine ⟨fun c c' ts hc hb hb' hs => ?_, fun c ts w hc hb hs => ?_⟩
  · obtain ⟨d', hr, hst⟩ :=
      h.1 c c c' ts hc hb ⟨Bwd.ConfigEq.refl c, typed_of_configOk K hc hb⟩ hb' hs
    exact ⟨d', hr.1, hst⟩
  · obtain ⟨c', d', hr, hw, hst⟩ :=
      h.2 c c ts w hc hb ⟨Bwd.ConfigEq.refl c, typed_of_configOk K hc hb⟩ hs
    exact ⟨c', d', hr.1, hw, hst⟩

/-- **`Task.wholeStepValid`, reduced** to the positive typing of the leaves and the composable
one-step simulation, for some `B` per encoding, host and profile. -/
theorem wholeStepValid_of
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        ∃ B : Builtins, PosTyping B hn ∧ OneStepRel B hn (Profile.spec nd r) host) :
    Task.wholeStepValid := by
  intro H hn hinj host hfin nd r
  obtain ⟨B, K, hr⟩ := h H hn hinj host hfin nd r
  exact ⟨B, oneStep_of_rel K hr⟩

end Silmaril.Wasm.SpecTec.Sim.Round4
