module

public import Silmaril.Proofs.Wasm.Verify.Split.Basic

/-!
# Escaping references: preservation by every Core 3.0 step rule

`Step.vIn`: for every profile `P` and every host relation returning the store unchanged with
references into `V` (`HostIn V host`), a step `Step P host c c'` from a configuration
satisfying the reachability invariant `CfgIn C fs (PlVC V C fs)` and the escaping-reference
invariant `VIn V b` leads to a configuration satisfying `VIn V b`. With `Step.cfgIn` at `C`
(`Silmaril.Proofs.Wasm.Verify.Reach.Step`) the pair is preserved.

* The delegated families (`ParametricStep`, …, `AggregateStep`) have a left-hand side made of
  values and one source instruction (silmaril-lean's `Det.FamShape`), with no transient
  reference: there `LooseIn V` is the reachability invariant at `V` (`codeIn_of_looseIn`), so the
  family theorems of `Silmaril.Proofs.Wasm.Verify.Reach.Families` apply at `V`, with the instruction
  predicate `RFPl V fs` (`ref.func` targets in `V`; `vIn_of_family`).
* A step never starts at a call instruction (`Step.nextCall_false`), so in the context rule
  `vals vs ++ is ++ rest` the values `vs` are not transient before or after the step.
* `call` and `return_call` create a transient reference (`callAdm` follows it); `call_ref` of a
  Wasm function makes a frame whose locals are the arguments (non-transient values, so in `V`);
  `return_call_ref` leaving a frame keeps the pair together (`callAdm_retToCallIn`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {V C : Nat → Prop} {fs : List Nat}

/-! ## The families at `V` -/

/-- The instruction predicate for the families at `V`: `ref.func` with its target in `V`. -/
def RFPl (V : Nat → Prop) (fs : List Nat) (i : Instr) : Prop :=
  (∃ x, i = .refFunc x) ∧ RefFuncIn V fs i

theorem rfPl_plainOK : PlainOK V (fun _ => True) fs (RFPl V fs) where
  block _ _ h := by obtain ⟨⟨_, hx⟩, -⟩ := h; cases hx
  loop _ _ h := by obtain ⟨⟨_, hx⟩, -⟩ := h; cases hx
  tryTable _ _ _ h := by obtain ⟨⟨_, hx⟩, -⟩ := h; cases hx
  ifLeft _ _ _ h := by obtain ⟨⟨_, hx⟩, -⟩ := h; cases hx
  ifRight _ _ _ h := by obtain ⟨⟨_, hx⟩, -⟩ := h; cases hx
  call _ _ _ _ := .inr trivial
  returnCall _ _ h := by obtain ⟨⟨_, hx⟩, -⟩ := h; cases hx
  refFunc x a h ha := h.2 x.toNat (by simp [instrRefFuncs]) a ha

/-- The only instruction of a delegated family that names a function is `ref.func`. -/
theorem callees_family {i : Instr} (hk : Det.famOf (.plain i) ≠ .control)
    (hc : instrCallees i ≠ []) : ∃ x, i = .refFunc x := by
  cases i <;> first | exact ⟨_, rfl⟩ | exact absurd rfl hc | exact absurd rfl hk

theorem PlOK.rfPl {i : Instr} (hk : Det.famOf (.plain i) ≠ .control)
    (h : PlOK (PlVC V C fs) i) : PlOK (RFPl V fs) i := by
  by_cases hc : instrCallees i = []
  · exact .inl hc
  · obtain ⟨x, rfl⟩ := callees_family hk hc
    exact .inr ⟨⟨x, rfl⟩, (h.of_callee (x := x.toNat) (by simp [instrCallees])).2⟩

/-- **A family step keeps `VIn V`**, through the family theorem at `V`. -/
theorem vIn_of_family {k : Det.Fam} {s : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    {b : Bool} (hshape : Det.FamShape k l) (hk : k ≠ .control)
    (hc : CfgIn C fs (PlVC V C fs) ⟨s, f, l⟩) (hV : VIn V b ⟨s, f, l⟩)
    (hstep : CfgIn V fs (RFPl V fs) ⟨s, f, l⟩ → CfgIn V fs (RFPl V fs) c') : VIn V b c' := by
  obtain ⟨args, e, rfl, -, hfam⟩ := hshape
  have hplain : ∃ i, e = .plain i := by
    cases e with
    | plain i => exact ⟨i, rfl⟩
    | _ => subst hfam; exact absurd rfl hk
  obtain ⟨i, rfl⟩ := hplain
  have hk' : Det.famOf (.plain i) ≠ .control := fun h => hk (hfam ▸ h)
  have hi : PlOK (PlVC V C fs) i := hc.2.2.last_plain
  have hcV : CfgIn V fs (RFPl V fs) ⟨s, f, vals args ++ [.plain i]⟩ :=
    ⟨hV.1, ⟨hc.2.1.1, hV.2.1⟩, codeIn_of_looseIn hV.2.2 (hi.rfPl hk')⟩
  have h' : CfgIn V fs (RFPl V fs) c' := hstep hcV
  exact ⟨h'.1, h'.2.1.2, looseIn_of_codeIn h'.2.2 b⟩

section
variable {P : Profile} {b : Bool}

theorem VariableStep.vIn {c c' : Config H} (h : VariableStep c c')
    (hc : CfgIn C fs (PlVC V C fs) c) (hV : VIn V b c) : VIn V b c' := by
  obtain ⟨s, f, l⟩ := c
  exact vIn_of_family (Det.VariableStep.shape h) (by decide) hc hV (VariableStep.cfgIn h)

theorem TableStep.vIn {c c' : Config H} (h : TableStep P c c')
    (hc : CfgIn C fs (PlVC V C fs) c) (hV : VIn V b c) : VIn V b c' := by
  obtain ⟨s, f, l⟩ := c
  exact vIn_of_family (Det.TableStep.shape h) (by decide) hc hV (TableStep.cfgIn h)

theorem MemoryStep.vIn {c c' : Config H} (h : MemoryStep P c c')
    (hc : CfgIn C fs (PlVC V C fs) c) (hV : VIn V b c) : VIn V b c' := by
  obtain ⟨s, f, l⟩ := c
  exact vIn_of_family (Det.MemoryStep.shape h) (by decide) hc hV (MemoryStep.cfgIn h)

theorem RefStep.vIn {c c' : Config H} (h : RefStep c c')
    (hc : CfgIn C fs (PlVC V C fs) c) (hV : VIn V b c) : VIn V b c' := by
  obtain ⟨s, f, l⟩ := c
  exact vIn_of_family (Det.RefStep.shape h) (by decide) hc hV (RefStep.cfgIn rfPl_plainOK h)

theorem AggregateStep.vIn {c c' : Config H} (h : AggregateStep c c')
    (hc : CfgIn C fs (PlVC V C fs) c) (hV : VIn V b c) : VIn V b c' := by
  obtain ⟨s, f, l⟩ := c
  exact vIn_of_family (Det.AggregateStep.shape h) (by decide) hc hV (AggregateStep.cfgIn h)

end

/-! ## Steps never start at a call instruction -/

theorem nextCall_famShape {k : Det.Fam} {l : List Admin} (h : Det.FamShape k l)
    (hk : k ≠ .control) (b : Bool) : nextCall b l = false := by
  obtain ⟨args, e, rfl, -, hfam⟩ := h
  refine nextCall_vals_append ?_ args
  cases e with
  | callRefType d => subst hfam; exact absurd rfl hk
  | returnCallRefType d => subst hfam; exact absurd rfl hk
  | _ => rfl

/-- **A stepping code list never starts with a call instruction.** -/
theorem Step.nextCall_false {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (b : Bool) : nextCall b c.code = false := by
  induction h generalizing b with
  | parametric h => exact nextCall_famShape (Det.ParametricStep.shape h) (by decide) b
  | numeric h => exact nextCall_famShape (Det.NumericStep.shape h) (by decide) b
  | vector h => exact nextCall_famShape (Det.VectorStep.shape h) (by decide) b
  | «variable» h => exact nextCall_famShape (Det.VariableStep.shape h) (by decide) b
  | table h => exact nextCall_famShape (Det.TableStep.shape h) (by decide) b
  | memory h => exact nextCall_famShape (Det.MemoryStep.shape h) (by decide) b
  | reference h => exact nextCall_famShape (Det.RefStep.shape h) (by decide) b
  | aggregate h => exact nextCall_famShape (Det.AggregateStep.shape h) (by decide) b
  | ctxtInstrs _ _ ih =>
    show nextCall b (vals _ ++ _ ++ _) = false
    rw [List.append_assoc]
    exact nextCall_vals_append (by rw [nextCall_append]; exact ih _) _
  | _ =>
    first
      | rfl
      | exact nextCall_vals_append rfl _
      | (rw [List.append_assoc]; exact nextCall_vals_append rfl _)
      | simp

/-! ## Context rules -/

theorem vIn_ctxtInstrs {P : Profile} {host : HostSemantics H} {Pl : Instr → Prop}
    {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hs : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hc : CfgIn C fs Pl ⟨s, f, vals vs ++ is ++ rest⟩)
    {b : Bool} (hV : VIn V b ⟨s, f, vals vs ++ is ++ rest⟩)
    (ih : ∀ b, CfgIn C fs Pl ⟨s, f, is⟩ → VIn V b ⟨s, f, is⟩ → VIn V b ⟨s', f', is'⟩) :
    VIn V b ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  have hn : nextCall (nextCall b rest) is = false := Step.nextCall_false hs _
  have h₁ := (looseIn_append b (vals vs ++ is) rest).1 hV.2.2
  have h₂ := (looseIn_append _ (vals vs) is).1 h₁.1
  rw [hn] at h₂
  have hcis : CfgIn C fs Pl ⟨s, f, is⟩ :=
    ⟨hc.1, hc.2.1, (CodeIn.append.1 (CodeIn.append.1 hc.2.2).1).2⟩
  have h' : VIn V (nextCall b rest) ⟨s', f', is'⟩ := ih _ hcis ⟨hV.1, hV.2.1, h₂.2⟩
  exact ⟨h'.1, h'.2.1, (looseIn_append b _ rest).2
    ⟨(looseIn_append _ _ _).2 ⟨LooseIn.mono h₂.1, h'.2.2⟩, h₁.2⟩⟩

theorem vIn_ctxtLabel {Pl : Instr → Prop} {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List Instr} {is is' : List Admin} (hc : CfgIn C fs Pl ⟨s, f, [.label n cont is]⟩)
    {b : Bool} (hV : VIn V b ⟨s, f, [.label n cont is]⟩)
    (ih : ∀ b, CfgIn C fs Pl ⟨s, f, is⟩ → VIn V b ⟨s, f, is⟩ → VIn V b ⟨s', f', is'⟩) :
    VIn V b ⟨s', f', [.label n cont is']⟩ := by
  have hl : LooseIn V false is := ((looseIn_label ..).1 hV.2.2).1
  have h' : VIn V false ⟨s', f', is'⟩ :=
    ih false ⟨hc.1, hc.2.1, (CodeIn.label_iff.1 hc.2.2).2⟩ ⟨hV.1, hV.2.1, hl⟩
  exact ⟨h'.1, h'.2.1, (looseIn_label ..).2 ⟨h'.2.2, looseIn_nil b⟩⟩

theorem vIn_ctxtHandler {Pl : Instr → Prop} {s s' : Store H} {f f' : Frame} {n : Nat}
    {cs : List Catch} {is is' : List Admin} (hc : CfgIn C fs Pl ⟨s, f, [.handler n cs is]⟩)
    {b : Bool} (hV : VIn V b ⟨s, f, [.handler n cs is]⟩)
    (ih : ∀ b, CfgIn C fs Pl ⟨s, f, is⟩ → VIn V b ⟨s, f, is⟩ → VIn V b ⟨s', f', is'⟩) :
    VIn V b ⟨s', f', [.handler n cs is']⟩ := by
  have hl : LooseIn V false is := ((looseIn_handler ..).1 hV.2.2).1
  have h' : VIn V false ⟨s', f', is'⟩ :=
    ih false ⟨hc.1, hc.2.1, CodeIn.handler_iff.1 hc.2.2⟩ ⟨hV.1, hV.2.1, hl⟩
  exact ⟨h'.1, h'.2.1, (looseIn_handler ..).2 ⟨h'.2.2, looseIn_nil b⟩⟩

theorem vIn_ctxtFrame {Pl : Instr → Prop} {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (hc : CfgIn C fs Pl ⟨s, f, [.frame n fi is]⟩)
    {b : Bool} (hV : VIn V b ⟨s, f, [.frame n fi is]⟩)
    (ih : ∀ b, CfgIn C fs Pl ⟨s, fi, is⟩ → VIn V b ⟨s, fi, is⟩ → VIn V b ⟨s', fi', is'⟩) :
    VIn V b ⟨s', f, [.frame n fi' is']⟩ := by
  have hl : LocalsIn V fi ∧ LooseIn V false is ∧ LooseIn V b [] := (looseIn_frame ..).1 hV.2.2
  have hcf : FrameIn C fs fi ∧ CodeIn C fs Pl is := CodeIn.frame_iff.1 hc.2.2
  have h' : VIn V false ⟨s', fi', is'⟩ := ih false ⟨hc.1, hcf.1, hcf.2⟩ ⟨hV.1, hl.1, hl.2.1⟩
  exact ⟨h'.1, hV.2.1, (looseIn_frame ..).2 ⟨h'.2.1, h'.2.2, looseIn_nil b⟩⟩

/-! ## Base rules -/

theorem looseIn_expression (b : Bool) (es : List Instr) : LooseIn V b (expression es) :=
  looseIn_of_refs b _ (by simp) (by simp)

theorem looseIn_throwing (b : Bool) (a : Nat) : LooseIn V b (throwing a) := by
  simp [throwing]

theorem looseIn_val_cons {b : Bool} (v : Val) (l : List Admin) :
    LooseIn V b (v.toAdmin :: l) ↔
      (∀ r, v = .ref r → RefIn V r ∨ nextCall b l = true) ∧ LooseIn V b l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | r <;> simp [Val.toAdmin]

theorem localsIn_forCall {m : ModuleInst} {vs : List Val}
    (hvs : ∀ r, Val.ref r ∈ vs → RefIn V r) (ls : List ValType) :
    LocalsIn V (Frame.forCall m vs ls) := by
  intro r hr
  simp only [Frame.forCall, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨v, hv, hv'⟩ | ⟨ty, -, hty⟩
  · exact hvs r (Option.some.inj hv' ▸ hv)
  · exact defaultVal?_ref hty ▸ refIn_null

theorem callAdm_retToCallIn {c : Admin} (m : ModuleInst) (h : callAdm c = true) :
    callAdm (c.retToCallIn m) = true := by
  cases c <;> simp_all [callAdm, Admin.retToCallIn]

theorem looseIn_retToCallIn {b : Bool} {c : Admin} (m : ModuleInst) (hc : c.IsReturnCallRef) :
    LooseIn V b [c.retToCallIn m] := by
  rcases c with ⟨i⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [Admin.IsReturnCallRef] at hc
  · cases i <;> simp only at hc
    simp only [Admin.retToCallIn]
    split <;> simp
  · simp [Admin.retToCallIn]

theorem looseIn_single_returnCallRef {b : Bool} {c : Admin} (hc : c.IsReturnCallRef) :
    LooseIn V b [c] := by
  rcases c with ⟨i⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [Admin.IsReturnCallRef] at hc <;> simp

/-- Values taken from a body `vals vs ++ [x] ++ rest` whose element `x` is not a call. -/
theorem LooseIn.pre_vals {b : Bool} {vs : List Val} {x : Admin} {rest : List Admin}
    (h : LooseIn V b (vals vs ++ [x] ++ rest)) (hx : callAdm x = false) :
    ∀ r, Val.ref r ∈ vs → RefIn V r := by
  rw [List.append_assoc] at h
  exact h.vals_refs (by simpa using hx)

/-- Values taken from a body `vals vs' ++ vals vs ++ [x] ++ rest`. -/
theorem LooseIn.mid_vals {b : Bool} {vs' vs : List Val} {x : Admin} {rest : List Admin}
    (h : LooseIn V b (vals vs' ++ vals vs ++ [x] ++ rest)) (hx : callAdm x = false) :
    ∀ r, Val.ref r ∈ vs → RefIn V r := by
  rw [← Execution.Core.vals_append] at h
  exact fun r hr => h.pre_vals hx r (List.mem_append_right _ hr)

/-! ## Base rules: the code -/

/-- A value followed by a non-call is not transient. -/
theorem LooseIn.head_val {b : Bool} {v : Val} {x : Admin} {l : List Admin}
    (h : LooseIn V b (v.toAdmin :: x :: l)) (hx : callAdm x = false) :
    ∀ r, v = .ref r → RefIn V r := by
  have h₁ : (∀ r, v = .ref r → RefIn V r ∨ nextCall b (x :: l) = true) ∧ LooseIn V b (x :: l) :=
    (looseIn_val_cons v _).1 h
  exact fun r hr => (h₁.1 r hr).resolve_right (by simp [hx])

/-- `return_call_ref` leaving a label or handler: the values and the call stay together. -/
theorem looseIn_returnCall_out {b : Bool} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef) (h : LooseIn V false (vals vs ++ [c] ++ rest)) :
    LooseIn V b (vals vs ++ [c]) := by
  have h₁ : LooseIn V (nextCall false ([c] ++ rest)) (vals vs) ∧ LooseIn V false ([c] ++ rest) := by
    rw [← looseIn_append, ← List.append_assoc]; exact h
  exact (looseIn_append ..).2 ⟨h₁.1, looseIn_single_returnCallRef hc⟩

/-- `return_call_ref` leaving a frame: the reference and its call stay together. -/
theorem looseIn_returnCallFrame_out {b : Bool} {vs' vs : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) (m : ModuleInst)
    (h : LooseIn V false (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)) :
    LooseIn V b (vals vs ++ [.ref (.func a), c.retToCallIn m]) := by
  have h₁ : (∀ r, Val.ref r ∈ vs' ++ vs → RefIn V r) ∧
      LooseIn V false (.ref (.func a) :: c :: rest) := by
    rw [← looseIn_vals_append (by rfl), Execution.Core.vals_append]
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  have ha : RefIn V (.func a) ∨ callAdm c = true := by
    simpa only [nextCall_cons] using ((looseIn_ref ..).1 h₁.2).1
  have ha' : RefIn V (.func a) ∨ nextCall b [c.retToCallIn m] = true :=
    ha.imp id (callAdm_retToCallIn m)
  exact LooseIn.vals_append (fun r hr => h₁.1 r (List.mem_append_right _ hr))
    ((looseIn_ref ..).2 ⟨ha', looseIn_retToCallIn m hc⟩)

/-- The code changes; the store and the frame do not. -/
theorem VIn.code {b : Bool} {s : Store H} {f : Frame} {l l' : List Admin}
    (hV : VIn V b ⟨s, f, l⟩) (h : LooseIn V b l') : VIn V b ⟨s, f, l'⟩ :=
  ⟨hV.1, hV.2.1, h⟩

/-- A host call: the host returns the store unchanged and results with references in `V`. -/
theorem vIn_callRefHost {host : HostSemantics H} (hh : HostIn V host) {b : Bool} {s s' : Store H}
    {f : Frame} {l : List Admin} {h : H} {vs : List Val} {r : Result}
    (hhost : host h s vs (.returned s' r)) (hV : VIn V b ⟨s, f, l⟩) :
    VIn V b ⟨s', f, r.toAdmin⟩ := by
  have h₁ : s' = s ∧ ∀ x ∈ codeRefs r.toAdmin, RefIn V x := hh _ _ _ _ _ hhost
  have h₂ : LooseIn V b r.toAdmin :=
    looseIn_of_codeIn (CodeIn.toAdmin (fs := []) (Pl := fun _ => True) h₁.2) b
  exact h₁.1 ▸ hV.code h₂

/-- Close `LooseIn` of a rule's right-hand side made of instructions, traps and references
naming no function, or of the references of the left-hand side. -/
macro "vin_simple_tac" hV:term : tactic => `(tactic| (
  refine ($hV).code ?_
  first
    | (simp [callAdm, throwing]; done)
    | (have h₃ := ($hV).2.2
       simp only [looseIn_ref, looseIn_plain, looseIn_nil, nextCall_cons, nextCall_nil, callAdm,
         and_true, Bool.false_eq_true, or_false] at h₃ ⊢
       first | exact h₃ | exact .inl h₃)))

/-- **Every Core 3.0 step preserves the escaping-reference invariant** `VIn V b`, from a
configuration satisfying the reachability invariant at `C` (every profile, every host returning
the store unchanged with references in `V`). -/
theorem Step.vIn {P : Profile} {host : HostSemantics H} (hh : HostIn V host) {c c' : Config H}
    (h : Step P host c c') (hc : CfgIn C fs (PlVC V C fs) c) {b : Bool} (hV : VIn V b c) :
    VIn V b c' := by
  induction h generalizing b with
  | parametric h =>
    exact vIn_of_family (Det.ParametricStep.shape h) (by decide) hc hV
      fun hcv => ⟨hcv.1, hcv.2.1, ParametricStep.out h hcv.2.2⟩
  | numeric h =>
    exact vIn_of_family (Det.NumericStep.shape h) (by decide) hc hV
      fun hcv => ⟨hcv.1, hcv.2.1, CodeIn.of_out (NumericStep.out h)⟩
  | vector h =>
    exact vIn_of_family (Det.VectorStep.shape h) (by decide) hc hV
      fun hcv => ⟨hcv.1, hcv.2.1, CodeIn.of_out (VectorStep.out h)⟩
  | «variable» h => exact VariableStep.vIn h hc hV
  | table h => exact TableStep.vIn h hc hV
  | memory h => exact MemoryStep.vIn h hc hV
  | reference h => exact RefStep.vIn h hc hV
  | aggregate h => exact AggregateStep.vIn h hc hV
  | ctxtInstrs hs _ ih => exact vIn_ctxtInstrs hs hc hV fun b h₁ h₂ => ih h₁ h₂
  | ctxtLabel _ ih => exact vIn_ctxtLabel hc hV fun b h₁ h₂ => ih h₁ h₂
  | ctxtHandler _ ih => exact vIn_ctxtHandler hc hV fun b h₁ h₂ => ih h₁ h₂
  | ctxtFrame _ ih => exact vIn_ctxtFrame hc hV fun b h₁ h₂ => ih h₁ h₂
  | block =>
    exact hV.code ((looseIn_label ..).2
      ⟨LooseIn.vals_append (hV.2.2.vals_refs rfl) (looseIn_expression _ _), looseIn_nil b⟩)
  | loop =>
    exact hV.code ((looseIn_label ..).2
      ⟨LooseIn.vals_append (hV.2.2.vals_refs rfl) (looseIn_expression _ _), looseIn_nil b⟩)
  | tryTable =>
    exact hV.code ((looseIn_handler ..).2 ⟨(looseIn_label ..).2
      ⟨LooseIn.vals_append (hV.2.2.vals_refs rfl) (looseIn_expression _ _), looseIn_nil _⟩,
      looseIn_nil b⟩)
  | labelVals => exact hV.code (LooseIn.mono ((looseIn_label ..).1 hV.2.2).1)
  | frameVals => exact hV.code (LooseIn.mono ((looseIn_frame ..).1 hV.2.2).2.1)
  | handlerVals => exact hV.code (LooseIn.mono ((looseIn_handler ..).1 hV.2.2).1)
  | brLabelZero =>
    exact hV.code (LooseIn.vals_append (((looseIn_label ..).1 hV.2.2).1.mid_vals (by rfl))
      (looseIn_expression _ _))
  | returnFrame =>
    exact hV.code (LooseIn.mono ((looseIn_vals_false _).2
      (((looseIn_frame ..).1 hV.2.2).2.1.mid_vals (by rfl))))
  | brLabelSucc =>
    exact hV.code (LooseIn.vals_append (((looseIn_label ..).1 hV.2.2).1.pre_vals (by rfl))
      (by simp))
  | brHandler =>
    exact hV.code (LooseIn.vals_append (((looseIn_handler ..).1 hV.2.2).1.pre_vals (by rfl))
      (by simp))
  | returnLabel =>
    exact hV.code (LooseIn.vals_append (((looseIn_label ..).1 hV.2.2).1.pre_vals (by rfl))
      (by simp))
  | returnHandler =>
    exact hV.code (LooseIn.vals_append (((looseIn_handler ..).1 hV.2.2).1.pre_vals (by rfl))
      (by simp))
  | brOnNullAddr =>
    exact hV.code ((looseIn_val_cons ..).2
      ⟨fun r hr => .inl (hV.2.2.head_val rfl r hr), looseIn_nil b⟩)
  | brOnNonNullAddr =>
    exact hV.code ((looseIn_val_cons ..).2
      ⟨fun r hr => .inl (hV.2.2.head_val rfl r hr), by simp⟩)
  | callRefFunc =>
    exact hV.code ((looseIn_frame ..).2 ⟨localsIn_forCall (hV.2.2.vals_refs rfl) _,
      (looseIn_label ..).2 ⟨looseIn_expression _ _, looseIn_nil _⟩, looseIn_nil b⟩)
  | callRefHost _ _ _ _ _ hhost => exact vIn_callRefHost hh hhost hV
  | callRefHostDiv => exact hV
  | returnCallRefLabel hc' =>
    exact hV.code (looseIn_returnCall_out hc' ((looseIn_label ..).1 hV.2.2).1)
  | returnCallRefHandler hc' =>
    exact hV.code (looseIn_returnCall_out hc' ((looseIn_handler ..).1 hV.2.2).1)
  | returnCallRefFrameAddr hc' =>
    exact hV.code (looseIn_returnCallFrame_out hc' _ ((looseIn_frame ..).1 hV.2.2).2.1)
  | throw => exact ⟨hV.1.addExn (hV.2.2.vals_refs rfl), hV.2.1, looseIn_throwing _ _⟩
  | throwRefHandlerCatch he =>
    exact hV.code (LooseIn.vals_append (fun r hr => hV.1.exn he hr) (by simp))
  | throwRefHandlerCatchRef he =>
    exact hV.code (LooseIn.vals_append (fun r hr => hV.1.exn he hr) (by simp))
  | _ => vin_simple_tac hV

end Silmaril.Wasm.Verify
