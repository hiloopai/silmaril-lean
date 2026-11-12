module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Runtime
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Step simulation: administrative label/frame/trap rules

Head-rule lemmas for the Lime1 → Core step simulation, one per administrative
`PureStep` constructor (`labelDone`, `labelBranch`, `labelBranchOuter`,
`labelReturn`, `frameDone`, `frameReturn`, `trapValues`, `trapTail`,
`labelTrap`, `frameTrap`). Each is simulated by exactly one Core step.

The Core profile is written `Numerics.Profile.spec` (the `coreProfile` abbreviation lives
in `Lime1/ToCore/Execution.lean`, which is downstream of this file).
-/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution.ToCore
open Silmaril.Wasm.Execution.Core (Step vals)

variable {H : Type}

/-! ## Helpers -/

theorem adm_listWF_append (s : Store H) :
    (xs ys : List Admin) → (Admin.listWF s (xs ++ ys) ↔ Admin.listWF s xs ∧ Admin.listWF s ys)
  | [], ys => by simp [Admin.listWF]
  | x :: xs, ys => by
    simp only [List.cons_append, Admin.listWF]
    rw [adm_listWF_append s xs ys, and_assoc]

theorem adm_listWF_values (s : Store H) : (vs : List Value) → Admin.listWF s (values vs)
  | [] => by simp [values, Admin.listWF]
  | v :: vs => by
    simp only [values, List.map_cons, Admin.listWF]
    refine ⟨?_, adm_listWF_values s vs⟩
    rcases v with ⟨⟨_ | _⟩, _⟩ <;> simp [value, Admin.WF]

theorem adm_listWF_expression (s : Store H) : (es : Expr) → Admin.listWF s (expression es)
  | [] => by simp [expression, Admin.listWF]
  | e :: es => by
    simp only [expression, List.map_cons, Admin.listWF]
    exact ⟨by simp [Admin.WF], adm_listWF_expression s es⟩

theorem adm_listWF_trap (s : Store H) : Admin.listWF s [.trap] := by
  simp [Admin.listWF, Admin.WF]

theorem adm_listWF_source (s : Store H) (i : Instr) : Admin.listWF s [.source i] := by
  simp [Admin.listWF, Admin.WF]

/-- Transfer `Sim` to a new code sequence on the same store and frame. -/
theorem adm_sim_of {s : Store H} {f : Frame} {before after : List Admin}
    {cs : CStore H} {cf : CFrame} {cl cl' : List CAdmin}
    (hs : Sim ⟨s, f, before⟩ ⟨cs, cf, cl⟩) (hwf : Admin.listWF s after)
    (hmap : cl'.map (ToCore.Admin.norm cf.module) = Admin.listToCore s after) :
    Sim ⟨s, f, after⟩ ⟨cs, cf, cl'⟩ := by
  obtain ⟨hn, hw⟩ := hs
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  refine ⟨?_, hw.1, hw.2.1, hwf⟩
  rw [ToCore.Config.norm_eq_toCore_iff]
  exact ⟨hn.1, hn.2.1, hmap⟩

theorem adm_code {s : Store H} {f : Frame} {before : List Admin}
    {cs : CStore H} {cf : CFrame} {cl : List CAdmin}
    (hs : Sim ⟨s, f, before⟩ ⟨cs, cf, cl⟩) :
    cl.map (ToCore.Admin.norm cf.module) = Admin.listToCore s before := by
  have hn := hs.1
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  exact hn.2.2

theorem adm_split {m : CModuleInst} {l A B : List CAdmin}
    (h : l.map (ToCore.Admin.norm m) = A ++ B) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.map (ToCore.Admin.norm m) = A ∧
      l₂.map (ToCore.Admin.norm m) = B :=
  List.map_eq_append_iff.mp h

theorem adm_single {m : CModuleInst} {l : List CAdmin} {y : CAdmin}
    (h : l.map (ToCore.Admin.norm m) = [y]) : ∃ x, l = [x] ∧ ToCore.Admin.norm m x = y :=
  List.map_eq_singleton_iff.mp h

theorem adm_trap {m : CModuleInst} {l : List CAdmin}
    (h : l.map (ToCore.Admin.norm m) = [.trap]) : l = [.trap] :=
  map_norm_eq_of_rigid (by simp [Rigid]) h

theorem adm_br {m : CModuleInst} {l : List CAdmin} {i : Silmaril.Wasm.Instr}
    (hi : Rigid (.plain i))
    (h : l.map (ToCore.Admin.norm m) = [.plain i]) : l = [.plain i] :=
  map_norm_eq_of_rigid (by simpa using hi) h

theorem adm_br_toCore (l : LabelIdx) : (Instr.br l).toCore = .br l := rfl

theorem adm_return_toCore : (Instr.return_).toCore = .return_ := rfl

theorem adm_rigid_br (l : LabelIdx) : Rigid (.plain (.br l)) := by simp [Rigid]

theorem adm_rigid_return : Rigid (.plain .return_) := by simp [Rigid]

/-! ## Label rules -/

theorem pure_labelDone {tgt : CHostSemantics H} {n : Nat} {cont : Expr} {vs : List Value}
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont (values vs)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, values vs⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, listToCore_nil, label_toCore, values_toCore,
    List.append_nil] at hm
  obtain ⟨x, rfl, hx⟩ := adm_single hm
  obtain ⟨b, rfl, hb⟩ := norm_eq_label hx
  obtain rfl := map_norm_vals hb
  exact ⟨_, .single Step.labelVals, adm_sim_of hs (adm_listWF_values s vs) (by simp)⟩

theorem pure_labelBranch {tgt : CHostSemantics H} {n : Nat} {cont : Expr}
    {extra vs : List Value} {tail : List Admin} (arity : vs.length = n)
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f,
      [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, values vs ++ expression cont⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, listToCore_nil, label_toCore, listToCore_append, values_toCore,
    source_toCore, adm_br_toCore, List.append_nil] at hm
  obtain ⟨x, rfl, hx⟩ := adm_single hm
  obtain ⟨b, rfl, hb⟩ := norm_eq_label hx
  obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ := adm_split hb
  obtain ⟨b₃, b₄, rfl, h₃, h₄⟩ := adm_split h₁
  obtain ⟨b₅, b₆, rfl, h₅, h₆⟩ := adm_split h₃
  obtain rfl := map_norm_vals h₅
  obtain rfl := map_norm_vals h₆
  obtain rfl := adm_br (adm_rigid_br _) h₄
  refine ⟨_, .single (Step.brLabelZero (vs' := extra.map Value.toCore)
    (vs := vs.map Value.toCore) (rest := b₂) rfl (by simpa using arity)), ?_⟩
  refine adm_sim_of hs ((adm_listWF_append s _ _).2
    ⟨adm_listWF_values s vs, adm_listWF_expression s cont⟩) ?_
  simp [listToCore_append]

theorem pure_labelBranchOuter {tgt : CHostSemantics H} {n : Nat} {cont : Expr}
    {vs : List Value} {tail : List Admin} {l : LabelIdx} (outer : l.toNat ≠ 0)
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont (values vs ++ [.source (.br l)] ++ tail)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, values vs ++ [.source (.br (lowerLabel l))]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, listToCore_nil, label_toCore, listToCore_append, values_toCore,
    source_toCore, adm_br_toCore, List.append_nil] at hm
  obtain ⟨x, rfl, hx⟩ := adm_single hm
  obtain ⟨b, rfl, hb⟩ := norm_eq_label hx
  obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ := adm_split hb
  obtain ⟨b₃, b₄, rfl, h₃, h₄⟩ := adm_split h₁
  obtain rfl := map_norm_vals h₃
  obtain rfl := adm_br (adm_rigid_br _) h₄
  refine ⟨_, .single (Step.brLabelSucc (vs := vs.map Value.toCore) (rest := b₂)
    (Nat.pos_of_ne_zero outer)), ?_⟩
  refine adm_sim_of hs ((adm_listWF_append s _ _).2
    ⟨adm_listWF_values s vs, adm_listWF_source s _⟩) ?_
  simp [listToCore_append, adm_br_toCore]
  rfl

theorem pure_labelReturn {tgt : CHostSemantics H} {n : Nat} {cont : Expr}
    {vs : List Value} {tail : List Admin}
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont (values vs ++ [.source .return_] ++ tail)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, values vs ++ [.source .return_]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, listToCore_nil, label_toCore, listToCore_append, values_toCore,
    source_toCore, adm_return_toCore, List.append_nil] at hm
  obtain ⟨x, rfl, hx⟩ := adm_single hm
  obtain ⟨b, rfl, hb⟩ := norm_eq_label hx
  obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ := adm_split hb
  obtain ⟨b₃, b₄, rfl, h₃, h₄⟩ := adm_split h₁
  obtain rfl := map_norm_vals h₃
  obtain rfl := adm_br adm_rigid_return h₄
  refine ⟨_, .single (Step.returnLabel (vs := vs.map Value.toCore) (rest := b₂)), ?_⟩
  refine adm_sim_of hs ((adm_listWF_append s _ _).2
    ⟨adm_listWF_values s vs, adm_listWF_source s _⟩) ?_
  simp [listToCore_append, adm_return_toCore, adm_rigid_return.norm]

/-! ## Frame rules -/

theorem pure_frameDone {tgt : CHostSemantics H} {n : Nat} {fr : Frame} {vs : List Value}
    (arity : vs.length = n)
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, [.frame n fr (values vs)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, values vs⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, listToCore_nil, frame_toCore, values_toCore,
    List.append_nil] at hm
  obtain ⟨x, rfl, hx⟩ := adm_single hm
  obtain ⟨fi, b, rfl, -, hb⟩ := norm_eq_frame hx
  obtain rfl := map_norm_vals hb
  exact ⟨_, .single (Step.frameVals (by simpa using arity)),
    adm_sim_of hs (adm_listWF_values s vs) (by simp)⟩

theorem pure_frameReturn {tgt : CHostSemantics H} {n : Nat} {fr : Frame}
    {extra vs : List Value} {tail : List Admin} (arity : vs.length = n)
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f,
      [.frame n fr (values extra ++ values vs ++ [.source .return_] ++ tail)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, values vs⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, listToCore_nil, frame_toCore, listToCore_append, values_toCore,
    source_toCore, adm_return_toCore, List.append_nil] at hm
  obtain ⟨x, rfl, hx⟩ := adm_single hm
  obtain ⟨fi, b, rfl, -, hb⟩ := norm_eq_frame hx
  obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ := adm_split hb
  obtain ⟨b₃, b₄, rfl, h₃, h₄⟩ := adm_split h₁
  obtain ⟨b₅, b₆, rfl, h₅, h₆⟩ := adm_split h₃
  obtain rfl := map_norm_vals h₅
  obtain rfl := map_norm_vals h₆
  obtain rfl := adm_br adm_rigid_return h₄
  exact ⟨_, .single (Step.returnFrame (vs' := extra.map Value.toCore)
    (vs := vs.map Value.toCore) (rest := b₂) (by simpa using arity)),
    adm_sim_of hs (adm_listWF_values s vs) (by simp)⟩

/-! ## Trap rules -/

theorem pure_trapValues {tgt : CHostSemantics H} {v : Value} {vs : List Value}
    {tail : List Admin}
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, values (v :: vs) ++ [.trap] ++ tail⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_append, values_toCore, listToCore_cons, listToCore_nil, trap_toCore,
    List.append_nil] at hm
  obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ := adm_split hm
  obtain ⟨b₃, b₄, rfl, h₃, h₄⟩ := adm_split h₁
  obtain rfl := map_norm_vals h₃
  obtain rfl := adm_trap h₄
  exact ⟨_, .single (Step.trapInstrs (vs := (v :: vs).map Value.toCore) (rest := b₂)
    (.inl (by simp))), adm_sim_of hs (adm_listWF_trap s) (by simp)⟩

theorem pure_trapTail {tgt : CHostSemantics H} {i : Admin} {tail : List Admin}
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, .trap :: i :: tail⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, trap_toCore] at hm
  obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ := adm_split hm
  obtain rfl := adm_trap h₁
  have hne : b₂ ≠ [] := by
    rintro rfl
    simp only [List.map_nil] at h₂
    exact toCore_ne_nil s i (List.append_eq_nil_iff.mp h₂.symm).1
  have hstep := Step.trapInstrs (P := Numerics.Profile.spec) (host := tgt) (s := cs) (f := cf)
    (vs := []) (rest := b₂) (.inr hne)
  exact ⟨_, .single (by simpa [vals] using hstep), adm_sim_of hs (adm_listWF_trap s) (by simp)⟩

theorem pure_labelTrap {tgt : CHostSemantics H} {n : Nat} {cont : Expr}
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont [.trap]]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, listToCore_nil, label_toCore, trap_toCore,
    List.append_nil] at hm
  obtain ⟨x, rfl, hx⟩ := adm_single hm
  obtain ⟨b, rfl, hb⟩ := norm_eq_label hx
  obtain rfl := adm_trap hb
  exact ⟨_, .single Step.trapLabel, adm_sim_of hs (adm_listWF_trap s) (by simp)⟩

theorem pure_frameTrap {tgt : CHostSemantics H} {n : Nat} {fr : Frame}
    {s : Store H} {f : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, [.frame n fr [.trap]]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Numerics.Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hm := adm_code hs
  simp only [listToCore_cons, listToCore_nil, frame_toCore, trap_toCore,
    List.append_nil] at hm
  obtain ⟨x, rfl, hx⟩ := adm_single hm
  obtain ⟨fi, b, rfl, -, hb⟩ := norm_eq_frame hx
  obtain rfl := adm_trap hb
  exact ⟨_, .single Step.trapFrame, adm_sim_of hs (adm_listWF_trap s) (by simp)⟩

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
