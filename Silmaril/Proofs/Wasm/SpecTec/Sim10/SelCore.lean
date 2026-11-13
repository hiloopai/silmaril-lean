module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.GSetRun

/-!
# `select` operands in a typed Core image, and `SelOk` along V1 runs

`GoodV1`'s third field, `SelOk`, asks every active `select` redex of a V1 configuration to have
operands of one type. V1 checks this (`sameType`), the 1.0 script does not. Here it is derived
from validation read through Core 3.0, as round 4 derived `GSetOk` (`GSetCore`, `GSetRun`):

* `select_core`: in a typed Core sequence, the two value operands of a `select` (no annotation)
  redex have the same numeric type. Core's `redex_inv` types the operands at subtypes of the
  instruction's parameters, `select-impl` has parameters `t t i32`, and a numeric type has no
  proper supertype (`Sub.num_fwd`).
* `selCoreP_of_active`: the induction over V1's `Active` (the redex, inside labels and frames),
  through the copied `Lime1 → Core` simulation relation, with the normalisation lemmas
  `norm_eq_label`, `norm_eq_frame` and `map_norm_eq_of_rigid`.
* **`selOk_of_coreTyped10`**: a `CoreTyped10` configuration satisfies `SelOk`.
* **`selOk_steps`**: so `SelOk` holds at every configuration of a V1 run from a `CoreTyped10`
  configuration whose store has no host function (`coreTyped10_steps`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Valid

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Lime1.Execution.ToCore (Rigid map_norm_eq_of_rigid norm_eq_label norm_eq_frame)

variable {H : Type}

/-! ## The Core side -/

/-- A typed `select` (no annotation) redex: its two value operands have the same numeric type. -/
theorem select_redex {s : Store H} {C : Context} {n₁ n₂ : NumVal} {c : BitVec 32}
    {it : InstrType}
    (h : AdminsOk s C (vals [.num n₁, .num n₂, .num ⟨.int .i32, c⟩] ++ [.plain (.select none)])
      it) : n₁.type = n₂.type := by
  have hI : ∀ it', InstrOk C (.select none) it' → it'.inits = [] ∧ it'.params.length = 3 := by
    intro it' hi
    cases hi <;> rename_i hi <;> cases hi
    simp
  obtain ⟨t₁, t₂, ts, hi, hvs, hsub, -⟩ := redex_inv hI h
  obtain ⟨t, rfl⟩ : ∃ t, t₁ = [t, t, .i32] := by
    cases hi <;> rename_i hp <;> cases hp
    exact ⟨_, rfl⟩
  obtain ⟨ta, tb, tc, rfl⟩ : ∃ ta tb tc, ts = [ta, tb, tc] := by
    rcases hvs with _ | ⟨_, _ | ⟨_, _ | ⟨_, hn⟩⟩⟩
    cases hn
    exact ⟨_, _, _, rfl⟩
  simp only [List.forall₂_cons] at hvs
  obtain ⟨hva, hvb, -, -⟩ := hvs
  cases hva
  cases hvb
  simp only [ResultSub, List.forall₂_cons] at hsub
  have ea : t = .num n₁.type := Sub.num_fwd hsub.1
  have eb : t = .num n₂.type := Sub.num_fwd hsub.2.1
  have e := ea.symm.trans eb
  injection e

/-- **The operands of a typed `select` redex have the same type**, in any typed sequence that
has the redex as an infix. -/
theorem select_core {s : Store H} {C : Context} (hC : C.Wf) {L₁ L₂ : List Admin} {n₁ n₂ : NumVal}
    {c : BitVec 32} {it : InstrType}
    (hty : AdminsOk s C (L₁ ++ [Val.toAdmin (.num n₁), Val.toAdmin (.num n₂),
      Val.toAdmin (.num ⟨.int .i32, c⟩), .plain (.select none)] ++ L₂) it) :
    n₁.type = n₂.type := by
  obtain ⟨C', it', h', -, -⟩ := infix_typed hty (by simp) hC
  exact select_redex h'

/-! ## Through the simulation relation -/

/-- The statement of the `Active` induction. -/
def SelCoreP (s : V1.Execution.Store H) (sC : Store H) (code w : List V1.Execution.Admin) :
    Prop :=
  ∀ (a b : Execution.Runtime.Value) (c : BitVec 32),
    w = [V1.Execution.value a, V1.Execution.value b, V1.Execution.value ⟨.int .i32, c⟩,
      .source .select] →
    ∀ (fC : Frame) (L : List Admin) (C : Context) (it : InstrType),
      L.map (Lime1.Execution.ToCore.Admin.norm fC.module) =
        Lime1.Execution.Admin.listToCore (s.mapCode V1.Func.toLime) (V1.Execution.codeToLime code) →
      C.Wf → AdminsOk sC C L it → a.type = b.type

/-- The image of a `select` redex. -/
theorem listToCore_sel (s : V1.Execution.Store H) (a b : Execution.Runtime.Value)
    (c : BitVec 32) :
    Lime1.Execution.Admin.listToCore (s.mapCode V1.Func.toLime)
      (V1.Execution.codeToLime [V1.Execution.value a, V1.Execution.value b,
        V1.Execution.value ⟨.int .i32, c⟩, .source .select]) =
      [Val.toAdmin (.num ⟨a.type, a.bits⟩), Val.toAdmin (.num ⟨b.type, b.bits⟩),
        Val.toAdmin (.num ⟨.int .i32, c⟩), .plain (.select none)] := by
  simp
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A normalised image with a `select` redex in its middle has that redex in its middle. -/
theorem split_sel {m : ModuleInst} {L A B : List Admin} {n₁ n₂ n₃ : NumVal}
    (h : L.map (Lime1.Execution.ToCore.Admin.norm m) =
      A ++ [Val.toAdmin (.num n₁), Val.toAdmin (.num n₂), Val.toAdmin (.num n₃),
        .plain (.select none)] ++ B) :
    ∃ L₁ L₂, L = L₁ ++ [Val.toAdmin (.num n₁), Val.toAdmin (.num n₂), Val.toAdmin (.num n₃),
      .plain (.select none)] ++ L₂ := by
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split h
  have hr : ∀ y ∈ [Val.toAdmin (.num n₁), Val.toAdmin (.num n₂), Val.toAdmin (.num n₃),
      Admin.plain (.select none)], Rigid y := by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Lime1.Execution.ToCore.Rigid.val _
    · exact Lime1.Execution.ToCore.Rigid.val _
    · exact Lime1.Execution.ToCore.Rigid.val _
    · simp [Lime1.Execution.ToCore.Rigid]
  exact ⟨L₁, L₂, by rw [map_norm_eq_of_rigid hr hM]⟩

/-- The piece case. -/
theorem selCoreP_piece {s : V1.Execution.Store H} {sC : Store H}
    {l₁ w l₂ : List V1.Execution.Admin} : SelCoreP s sC (l₁ ++ w ++ l₂) w := by
  intro a b c hw fC L C it hL hC hty
  subst hw
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append,
    listToCore_sel] at hL
  obtain ⟨L₁, L₂, rfl⟩ := split_sel hL
  exact select_core hC hty

/-- The label case. -/
theorem selCoreP_label {s : V1.Execution.Store H} {sC : Store H}
    {code w body : List V1.Execution.Admin} {n : Nat} {cont : V1.Expr}
    (hm : .label n cont body ∈ code) (ih : SelCoreP s sC body w) : SelCoreP s sC code w := by
  intro a b c hw fC L C it hL hC hty
  obtain ⟨l₁, l₂, rfl⟩ := split_mem hm
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append] at hL
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split hL
  simp only [V1.Execution.codeToLime_cons, V1.Execution.codeToLime_nil,
    Execution.Runtime.AdminInstr.map, Lime1.Execution.listToCore_cons,
    Lime1.Execution.listToCore_nil, List.append_nil] at hM
  obtain ⟨z, rfl, hz⟩ := List.map_eq_singleton_iff.mp hM
  obtain ⟨b', rfl, hb'⟩ := norm_eq_label hz
  obtain ⟨C', it', ha', -, hC'⟩ := single_typed hty hC
  cases ha' with
  | label hn hc hb =>
    have hr := (AdminsOk.params_ok hC' hc).1
    exact ih a b c hw fC b' _ _ hb' (hC'.withLabel hr) hb

/-- The frame case. -/
theorem selCoreP_frame {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hts : StoreTypesOk sC) {fi : Execution.Runtime.Frame}
    {code w body : List V1.Execution.Admin} {n : Nat}
    (hm : .frame n fi body ∈ code) (ih : SelCoreP s sC body w) : SelCoreP s sC code w := by
  intro a b c hw fC L C it hL hC hty
  obtain ⟨l₁, l₂, rfl⟩ := split_mem hm
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append] at hL
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split hL
  simp only [V1.Execution.codeToLime_cons, V1.Execution.codeToLime_nil,
    Execution.Runtime.AdminInstr.map, Lime1.Execution.listToCore_cons,
    Lime1.Execution.listToCore_nil, List.append_nil] at hM
  obtain ⟨z, rfl, hz⟩ := List.map_eq_singleton_iff.mp hM
  obtain ⟨fz, b', rfl, -, hb'⟩ := norm_eq_frame hz
  obtain ⟨C', it', ha', -, -⟩ := single_typed hty hC
  cases ha' with
  | frame hf' hn hb hok =>
    rename_i C'' ts
    have hwf : ({ C'' with return_ := some ts } : Context).Wf :=
      (FrameOk.ctxWf hs hts hf').withReturn fun t h => TyOk.of_empty _ (hok t h)
    exact ih a b c hw fz b' _ _ hb' hwf hb

/-- **The `Active` induction.** -/
theorem selCoreP_of_active {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hts : StoreTypesOk sC) {code w : List V1.Execution.Admin}
    (h : Silmaril.Wasm.SpecTec.Sim10.Active code w) : SelCoreP s sC code w := by
  induction h with
  | piece => exact selCoreP_piece
  | label hm _ ih => exact selCoreP_label hm ih
  | frame hm _ ih => exact selCoreP_frame hs hts hm ih

/-- **A V1 configuration related to a typed Core configuration satisfies `SelOk`.** -/
theorem selOk_of_core {c : V1.Execution.Config H} {cc : Config H} {ts : List CValType}
    (hsim : Lime1.Execution.Sim c.toLime cc) (hok : ConfigOk cc ts) :
    Silmaril.Wasm.SpecTec.Sim10.SelOk c.code := by
  obtain ⟨C, ⟨hs, hf⟩, hty⟩ := hok
  have hts : StoreTypesOk cc.store := ⟨hs.structsClosed, hs.arraysClosed⟩
  have hn := hsim.1
  rcases cc with ⟨sC, fC, L⟩
  obtain ⟨-, -, hL⟩ := Lime1.Execution.ToCore.Config.norm_eq_toCore_iff.mp hn
  intro a b c hact
  exact selCoreP_of_active hs hts hact a b c rfl fC L C _ hL (FrameOk.ctxWf hs hts hf) hty

/-- **`SelOk` at a `CoreTyped10` configuration.** -/
theorem selOk_of_coreTyped10 {c : V1.Execution.Config H} (hc : CoreTyped10 c) :
    Silmaril.Wasm.SpecTec.Sim10.SelOk c.code := by
  obtain ⟨_, _, hsim, hok⟩ := hc
  exact selOk_of_core hsim hok

/-- **`SelOk` at every configuration of a V1 run** from a `CoreTyped10` configuration whose store
has no host function. -/
theorem selOk_steps {host : V1.Execution.HostSemantics H} {c d : V1.Execution.Config H}
    (h : V1.Execution.Steps host c d) (hnh : Whole.NoHost10 c.store) (hc : CoreTyped10 c) :
    Silmaril.Wasm.SpecTec.Sim10.SelOk d.code :=
  selOk_of_coreTyped10 (coreTyped10_steps h hnh hc).2

end Silmaril.Wasm.SpecTec.Sim10.Valid
