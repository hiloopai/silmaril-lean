module

public import Silmaril.Wasm.Component.Engine.Core3.Defs

/-!
# `Engine.Core3.StepLaws.Callout`: the laws that definitions cite

The theorems of the component reference copy `Engine.Core3.StepLaws.Callout` that definition parts
cite (engine records bundle such laws as fields). The other theorems stay in
`Silmaril.Raw.Wasm.Component.Engine.Core3.StepLaws.Callout`, which imports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core
variable {H : Type}

namespace StepLaws

/-- A code with a host-call redex has a first non-value, at which `decompHead` finds it. -/
theorem decompose?_some_split {s : Store H} {code : List Admin}
    {x : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? s code = some x) :
    ∃ vs d rest, SingleThreaded.splitVals code = (vs, d :: rest) ∧
      SingleThreaded.decompHead s vs d rest = some x := by
  rcases hs : SingleThreaded.splitVals code with ⟨vs, _ | ⟨d, rest⟩⟩
  · rw [SingleThreaded.decompose?_of_split_nil hs] at h; cases h
  · exact ⟨vs, d, rest, rfl, by rw [← SingleThreaded.decompose?_of_split hs]; exact h⟩

/-- `decompHead` finds a redex in a nested body, or at a `call_ref` of a host function. -/
theorem decompHead_cases {s : Store H} {vs : List Val} {d : Admin} {rest : List Admin}
    {x : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompHead s vs d rest = some x) :
    (∃ n cont body y, d = .label n cont body ∧ SingleThreaded.decompose? s body = some y) ∨
    (∃ n cs body y, d = .handler n cs body ∧ SingleThreaded.decompose? s body = some y) ∨
    (∃ n fi body y, d = .frame n fi body ∧ SingleThreaded.decompose? s body = some y) ∨
    ((∃ y, d = .plain (.callRef y)) ∨ (∃ dt, d = .callRefType dt)) ∧
      SingleThreaded.topRedex s vs rest = some x := by
  unfold SingleThreaded.decompHead at h
  split at h
  · obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨_, _, _, y, rfl, hy⟩
  · obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp h
    exact .inr (.inl ⟨_, _, _, y, rfl, hy⟩)
  · obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp h
    exact .inr (.inr (.inl ⟨_, _, _, y, rfl, hy⟩))
  · split at h
    · rename_i hc
      exact .inr (.inr (.inr
        ⟨SingleThreaded.Det.IsCallRef.cases (Admin.IsCallRef_of_isCallRef hc), h⟩))
    · cases h

/-- The first non-value of a body with a host-call redex is a nested context or a `call_ref`,
and the structured head rules (`labelAt`, `handlerAt`, `frameAt`) do not fire there. -/
theorem body_split {s : Store H} {body : List Admin}
    {y : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? s body = some y) :
    ∃ vs d rest, SingleThreaded.splitVals body = (vs, d :: rest) ∧
      (∀ (f : Frame) n cont, SingleThreaded.Exec.Adm.labelAt s f n cont vs d rest = none) ∧
      (∀ (f : Frame) n cs, SingleThreaded.Exec.Adm.handlerAt s f n cs vs d rest = none) ∧
      (∀ (f : Frame) n fi, SingleThreaded.Exec.Adm.frameAt s f n fi vs d rest = none) := by
  obtain ⟨vs, d, rest, hs, hd⟩ := decompose?_some_split h
  refine ⟨vs, d, rest, hs, ?_⟩
  rcases decompHead_cases hd with ⟨_, _, _, _, rfl, -⟩ | ⟨_, _, _, _, rfl, -⟩ |
    ⟨_, _, _, _, rfl, -⟩ | ⟨⟨_, rfl⟩ | ⟨_, rfl⟩, -⟩ <;>
    exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem labelStep_none {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {body : List Admin} {y : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? s body = some y) :
    SingleThreaded.Exec.Adm.labelStep s f n cont body = none := by
  obtain ⟨vs, d, rest, hs, hl, -, -⟩ := body_split h
  unfold SingleThreaded.Exec.Adm.labelStep
  rw [hs]
  exact hl f n cont

theorem handlerStep_none {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {body : List Admin} {y : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? s body = some y) :
    SingleThreaded.Exec.Adm.handlerStep s f n cs body = none := by
  obtain ⟨vs, d, rest, hs, -, hh, -⟩ := body_split h
  unfold SingleThreaded.Exec.Adm.handlerStep
  rw [hs]
  exact hh f n cs

theorem frameStep_none {s : Store H} {f : Frame} {n : Nat} {fi : Frame}
    {body : List Admin} {y : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? s body = some y) :
    SingleThreaded.Exec.Adm.frameStep s f n fi body = none := by
  obtain ⟨vs, d, rest, hs, -, -, hf⟩ := body_split h
  unfold SingleThreaded.Exec.Adm.frameStep
  rw [hs]
  exact hf f n fi

theorem interpHead_label_none {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame}
    {vs : List Val} {n : Nat} {cont : List Instr} {body : List Admin}
    {y : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? s body = some y) :
    SingleThreaded.Exec.interpHead o s f vs (.label n cont body) = none := by
  have e : SingleThreaded.Exec.interpHead o s f vs (.label n cont body) =
      (none <|> (SingleThreaded.Exec.Adm.labelStep s f n cont body).map (0, ·)) := rfl
  rw [e, labelStep_none h]
  rfl

theorem interpHead_handler_none {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame}
    {vs : List Val} {n : Nat} {cs : List Catch} {body : List Admin}
    {y : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? s body = some y) :
    SingleThreaded.Exec.interpHead o s f vs (.handler n cs body) = none := by
  have e : SingleThreaded.Exec.interpHead o s f vs (.handler n cs body) =
      (none <|> (SingleThreaded.Exec.Adm.handlerStep s f n cs body).map (0, ·)) := rfl
  rw [e, handlerStep_none h]
  rfl

theorem interpHead_frame_none {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame}
    {vs : List Val} {n : Nat} {fi : Frame} {body : List Admin}
    {y : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? s body = some y) :
    SingleThreaded.Exec.interpHead o s f vs (.frame n fi body) = none := by
  have e : SingleThreaded.Exec.interpHead o s f vs (.frame n fi body) =
      (none <|> (SingleThreaded.Exec.Adm.frameStep s f n fi body).map (0, ·)) := rfl
  rw [e, frameStep_none h]
  rfl

/-- `call_ref` does not call a host function. -/
theorem callRef?_host_none {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    {x : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.topRedex s vs rest = some x) :
    SingleThreaded.Exec.Ctl.callRef? s f vs = none := by
  obtain ⟨a, hc, n, hl, hh⟩ := SingleThreaded.topRedex_some h
  obtain ⟨fi, ps, rs, hfi, hcode, -, -⟩ := SingleThreaded.hostArity?_eq_some hh
  unfold SingleThreaded.Exec.Ctl.callRef?
  rw [hl]
  dsimp only
  rw [hfi]
  dsimp only
  split
  · rename_i hw
    rw [hcode] at hw
    cases hw
  · rfl

theorem interpHead_callRef_none {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame}
    {vs : List Val} {rest : List Admin} {d : Admin}
    {x : SingleThreaded.Ctx × Nat × H × List Val}
    (hd : (∃ y, d = .plain (.callRef y)) ∨ (∃ dt, d = .callRefType dt))
    (h : SingleThreaded.topRedex s vs rest = some x) :
    SingleThreaded.Exec.interpHead o s f vs d = none := by
  have e : SingleThreaded.Exec.interpHead o s f vs d =
      (SingleThreaded.Exec.Ctl.callRef? s f vs <|> none) := by
    rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  rw [e, callRef?_host_none h]
  rfl

theorem stepI_none_aux {o : SingleThreaded.GrowOracle} :
    ∀ (n : Nat) (c : Config H) (x : SingleThreaded.Ctx × Nat × H × List Val),
      sizeOf c.code = n → SingleThreaded.decompose? c.store c.code = some x →
      SingleThreaded.Exec.stepI o c = none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c x hn h
  obtain ⟨vs, d, rest, hs, hd⟩ := decompose?_some_split h
  have hlt : sizeOf d < sizeOf c.code := SingleThreaded.Exec.Drv.sizeOf_lt_of_split hs
  rw [SingleThreaded.Exec.stepI, SingleThreaded.Exec.step?_cons hs]
  rcases decompHead_cases hd with ⟨n', cont, body, y, rfl, hy⟩ | ⟨n', cs, body, y, rfl, hy⟩ |
    ⟨n', fi, body, y, rfl, hy⟩ | ⟨hc, ht⟩
  · have hb : SingleThreaded.Exec.stepI o ⟨c.store, c.frame, body⟩ = none :=
      ih _ (hn ▸ lt_trans SingleThreaded.Exec.Drv.sizeOf_label_body hlt) _ y rfl hy
    unfold SingleThreaded.Exec.Drv.layer
    rw [interpHead_label_none hy]
    show Option.map _ (SingleThreaded.Exec.stepI o ⟨c.store, c.frame, body⟩) = none
    rw [hb]
    rfl
  · have hb : SingleThreaded.Exec.stepI o ⟨c.store, c.frame, body⟩ = none :=
      ih _ (hn ▸ lt_trans SingleThreaded.Exec.Drv.sizeOf_handler_body hlt) _ y rfl hy
    unfold SingleThreaded.Exec.Drv.layer
    rw [interpHead_handler_none hy]
    show Option.map _ (SingleThreaded.Exec.stepI o ⟨c.store, c.frame, body⟩) = none
    rw [hb]
    rfl
  · have hb : SingleThreaded.Exec.stepI o ⟨c.store, fi, body⟩ = none :=
      ih _ (hn ▸ lt_trans SingleThreaded.Exec.Drv.sizeOf_frame_body hlt) _ y rfl hy
    unfold SingleThreaded.Exec.Drv.layer
    rw [interpHead_frame_none hy]
    show Option.map _ (SingleThreaded.Exec.stepI o ⟨c.store, fi, body⟩) = none
    rw [hb]
    rfl
  · have hh : SingleThreaded.Exec.interpHead o c.store c.frame vs d = none :=
      interpHead_callRef_none hc ht
    unfold SingleThreaded.Exec.Drv.layer
    rw [hh]
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

end StepLaws

/-- No step at a host-call redex. -/
theorem stepI_none_of_decompose? {o : SingleThreaded.GrowOracle} {c : Config H}
    {x : SingleThreaded.Ctx × Nat × H × List Val}
    (h : SingleThreaded.decompose? c.store c.code = some x) :
    SingleThreaded.Exec.stepI o c = none :=
  StepLaws.stepI_none_aux _ c x rfl h

end Silmaril.Wasm.Component.Engine.Core3
