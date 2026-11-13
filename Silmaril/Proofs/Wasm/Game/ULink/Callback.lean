module

public import Silmaril.Proofs.Wasm.Game.ULink.Example

/-!
# Worked example: partial linking and a callback

`exApply` exports `apply : [(ref null $cb)] → [i32]`, which calls its argument; `exUse` imports
a host function `env.host` (not provided by `exApply`) and `apply`, and exports
`run = ref.func cb; call apply` with `cb = call env.host`. Both are validated and allocated by
the spec's `prepare?` into one store `cbS` (kernel evaluation), after the host function.

* `shape`: the four functions of the linked store (host, `apply`, `cb`, `run`);
* `cbS_layout`: the store has the layout of the partial link `cbLink` (`apply` stubbed, the host
  import kept);
* `run_to_callout`: `$invoke(run)` runs, through `apply` and the callback `cb`, to the host
  call, three frames deep; `run_unwind`: the host's answer `v` unwinds to `v`.

New proofs, following `Silmaril.Proofs.Wasm.Game.ULinkExample`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.ULinkCallback

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril.Wasm.Game.ULinkCallback
  Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.ULink Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-! ### Kernel-checked facts -/

theorem exApply_valid : (validate? exApply).isSome = true := by decide +kernel
theorem exUse_valid : (validate? exUse).isSome = true := by decide +kernel
theorem applyPrep_some : (prepare? evalConst? hostS exApply []).isSome = true := by decide +kernel
theorem usePrep_some :
    (prepare? evalConst? applyPrep.1.store exUse [.func 0, .func 1]).isSome = true := by
  decide +kernel
theorem t_len : cbS.funcs.length = 4 := by decide +kernel
theorem t_addrs : exportFuncAddrs usePrep.1.frame.module = [2, 3] := by decide +kernel
theorem t_mod : cbS.funcs.map (fun fi => fi.module.funcs) = [[], [1], [0, 1, 2, 3], [0, 1, 2, 3]] := by
  decide +kernel
/-- The provider's `apply`. -/
def isApplyBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.localGet x, .callRef y]⟩ => x.toNat == 0 && y.toNat == 0
  | _ => false

/-- The consumer's `cb`. -/
def isCbBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.call x]⟩ => x.toNat == 0
  | _ => false

/-- The consumer's `run`. -/
def isRunBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.refFunc x, .call y]⟩ => x.toNat == 2 && y.toNat == 1
  | _ => false

/-- The host function with host code `0`. -/
def isHost0 (fi : FuncInst Nat) : Bool := match fi.code with
  | .host 0 => true
  | _ => false

theorem t_bodies : cbS.funcs.map (fun fi => (isHost0 fi, isApplyBody fi, isCbBody fi, isRunBody fi)) =
    [(true, false, false, false), (false, true, false, false), (false, false, true, false),
      (false, false, false, true)] := by
  decide +kernel

/-- The parameter and result counts of a function type. -/
def tyShape : Option CCompType → Option (Nat × Nat)
  | some (.func ps rs) => some (ps.length, rs.length)
  | _ => none

theorem t_shape : cbS.funcs.map (fun fi => tyShape fi.type.expand?) =
    [some (0, 1), some (1, 1), some (0, 1), some (0, 1)] := by
  decide +kernel

/-! ### The shape of the linked store -/

theorem isApplyBody_code {fi : FuncInst Nat} (h : isApplyBody fi = true) :
    ∃ (t : TypeIdx) (x : LocalIdx) (y : TypeIdx),
      fi.code = .wasm ⟨t, [], [.localGet x, .callRef y]⟩ ∧ x.toNat = 0 := by
  unfold isApplyBody at h
  split at h
  · rename_i t x y hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨t, x, y, hc, h.1⟩
  · cases h

theorem isCbBody_code {fi : FuncInst Nat} (h : isCbBody fi = true) :
    ∃ (t : TypeIdx) (z : FuncIdx), fi.code = .wasm ⟨t, [], [.call z]⟩ ∧ z.toNat = 0 := by
  unfold isCbBody at h
  split at h
  · rename_i t z hc
    simp only [beq_iff_eq] at h
    exact ⟨t, z, hc, h⟩
  · cases h

theorem isRunBody_code {fi : FuncInst Nat} (h : isRunBody fi = true) :
    ∃ (t : TypeIdx) (r c : FuncIdx), fi.code = .wasm ⟨t, [], [.refFunc r, .call c]⟩ ∧
      r.toNat = 2 ∧ c.toNat = 1 := by
  unfold isRunBody at h
  split at h
  · rename_i t r c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨t, r, c, hc, h.1, h.2⟩
  · cases h

theorem isHost0_code {fi : FuncInst Nat} (h : isHost0 fi = true) : fi.code = .host 0 := by
  unfold isHost0 at h
  split at h
  · assumption
  · cases h

theorem expand_of_shape {fi : FuncInst Nat} {m n : Nat} (h : tyShape fi.type.expand? = some (m, n)) :
    ∃ ps rs, Expand fi.type (.func ps rs) ∧ ps.length = m ∧ rs.length = n := by
  cases he : fi.type.expand? with
  | none => rw [he] at h; cases h
  | some c =>
    rw [he] at h
    cases c with
    | func ps rs =>
      obtain ⟨hm, hn⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨ps, rs, Expand.iff.mpr he, hm, hn⟩
    | _ => cases h

/-- The shape of the linked store. -/
structure Shape (fi₀ fi₁ fi₂ fi₃ : FuncInst Nat) : Prop where
  funcs : cbS.funcs = [fi₀, fi₁, fi₂, fi₃]
  code₀ : fi₀.code = .host 0
  code₁ : ∃ (t : TypeIdx) (x : LocalIdx) (y : TypeIdx),
    fi₁.code = .wasm ⟨t, [], [.localGet x, .callRef y]⟩ ∧ x.toNat = 0
  code₂ : ∃ (t : TypeIdx) (z : FuncIdx), fi₂.code = .wasm ⟨t, [], [.call z]⟩ ∧ z.toNat = 0
  code₃ : ∃ (t : TypeIdx) (r c : FuncIdx), fi₃.code = .wasm ⟨t, [], [.refFunc r, .call c]⟩ ∧
    r.toNat = 2 ∧ c.toNat = 1
  ty₀ : ∃ ps rs, Expand fi₀.type (.func ps rs) ∧ ps.length = 0 ∧ rs.length = 1
  ty₁ : ∃ ps rs, Expand fi₁.type (.func ps rs) ∧ ps.length = 1 ∧ rs.length = 1
  ty₂ : ∃ ps rs, Expand fi₂.type (.func ps rs) ∧ ps.length = 0 ∧ rs.length = 1
  ty₃ : ∃ ps rs, Expand fi₃.type (.func ps rs) ∧ ps.length = 0 ∧ rs.length = 1
  mod₂ : fi₂.module.funcs = [0, 1, 2, 3]
  mod₃ : fi₃.module.funcs = [0, 1, 2, 3]

theorem shape : ∃ fi₀ fi₁ fi₂ fi₃, Shape fi₀ fi₁ fi₂ fi₃ := by
  obtain ⟨fi₀, fi₁, fi₂, fi₃, hf⟩ : ∃ fi₀ fi₁ fi₂ fi₃, cbS.funcs = [fi₀, fi₁, fi₂, fi₃] := by
    match h : cbS.funcs, t_len with
    | [fi₀, fi₁, fi₂, fi₃], _ => exact ⟨fi₀, fi₁, fi₂, fi₃, rfl⟩
  have hb : [fi₀, fi₁, fi₂, fi₃].map (fun fi => (isHost0 fi, isApplyBody fi, isCbBody fi, isRunBody fi)) =
      _ := hf ▸ t_bodies
  have hs : [fi₀, fi₁, fi₂, fi₃].map (fun fi => tyShape fi.type.expand?) = _ := hf ▸ t_shape
  have hm : [fi₀, fi₁, fi₂, fi₃].map (fun fi => fi.module.funcs) = _ := hf ▸ t_mod
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq] at hb hs hm
  exact ⟨fi₀, fi₁, fi₂, fi₃, hf, isHost0_code hb.1.1, isApplyBody_code hb.2.1.2.1,
    isCbBody_code hb.2.2.1.2.2.1, isRunBody_code hb.2.2.2.1.2.2.2, expand_of_shape hs.1,
    expand_of_shape hs.2.1, expand_of_shape hs.2.2.1, expand_of_shape hs.2.2.2.1, hm.2.2.1,
    hm.2.2.2.1⟩

/-! ### Layout -/

theorem applyCode_eq {fi₀ fi₁ fi₂ fi₃ : FuncInst Nat} (h : Shape fi₀ fi₁ fi₂ fi₃) :
    fi₁.code = .wasm applyCode := by
  obtain ⟨t, x, y, hc, -⟩ := h.code₁
  have hf : cbS.funcs[1]? = some fi₁ := by rw [h.funcs]; rfl
  unfold applyCode
  rw [hf, Option.map_some, hc]

/-- The only stub is `apply`. -/
theorem cbLink_stub {a k : Nat} {c : Func} (hs : cbLink.stub a = some (k, c)) :
    a = 1 ∧ k = 1 ∧ c = applyCode := by
  by_cases ha : a = 1
  · have hs' : (1, applyCode) = (k, c) := by simpa [cbLink, ha] using hs
    exact ⟨ha, (Prod.mk.inj hs').1.symm, (Prod.mk.inj hs').2.symm⟩
  · simp [cbLink, ha] at hs

/-- The only host function of the linked store has host code `0`. -/
theorem cbS_host {fi₀ fi₁ fi₂ fi₃ : FuncInst Nat} (h : Shape fi₀ fi₁ fi₂ fi₃) {a k : Nat}
    {fi : FuncInst Nat} (ha : cbS.funcs[a]? = some fi) (hc : fi.code = .host k) : k = 0 := by
  rw [h.funcs] at ha
  obtain ⟨t₁, x, y, hc₁, -⟩ := h.code₁
  obtain ⟨t₂, z, hc₂, -⟩ := h.code₂
  obtain ⟨t₃, r, c, hc₃, -⟩ := h.code₃
  match a, ha with
  | 0, ha => rw [← Option.some.inj ha, h.code₀] at hc; cases hc; rfl
  | 1, ha => rw [← Option.some.inj ha, hc₁] at hc; cases hc
  | 2, ha => rw [← Option.some.inj ha, hc₂] at hc; cases hc
  | 3, ha => rw [← Option.some.inj ha, hc₃] at hc; cases hc

/-- **The linked store has the layout of the partial link.** -/
theorem cbS_layout : cbLink.Layout cbS := by
  obtain ⟨fi₀, fi₁, fi₂, fi₃, h⟩ := shape
  refine ⟨fun a fi k c ha hs => ?_, fun a fi k ha hc => ?_⟩
  · obtain ⟨rfl, -, rfl⟩ := cbLink_stub hs
    have hfi : fi = fi₁ := by rw [h.funcs] at ha; exact (Option.some.inj ha).symm
    rw [hfi, applyCode_eq h]
  · rw [cbS_host h ha hc]
    rfl

/-! ### The linked run -/

section Run

variable {P : Silmaril.Wasm.Numerics.Profile}

local notation "noH" => (fun _ _ _ _ => False : HostSemantics Nat)

/-- A function body under its frame and label (one result). -/
abbrev wrap (F : Frame) (X : List Admin) : List Admin := [.frame 1 F [.label 1 [] X]]

/-- The frame of `run`. -/
abbrev F₃ (fi₃ : FuncInst Nat) : Frame := Frame.forCall fi₃.module [] []

/-- The frame of `apply`, holding the reference to `cb`. -/
abbrev F₁ (fi₁ : FuncInst Nat) : Frame := Frame.forCall fi₁.module [.ref (.func 2)] []

/-- The frame of `cb`. -/
abbrev F₂ (fi₂ : FuncInst Nat) : Frame := Frame.forCall fi₂.module [] []

/-- A step under a frame and a label. -/
theorem step_in {s s' : Store Nat} {F : Frame} {X Y : List Admin}
    (h : Execution.Core.Step P noH ⟨s, F, X⟩ ⟨s', F, Y⟩) (g : Frame) :
    Execution.Core.Step P noH ⟨s, g, wrap F X⟩ ⟨s', g, wrap F Y⟩ :=
  Step.ctxtFrame (Step.ctxtLabel h)

/-- Steps under a frame and a label. -/
theorem steps_in {c c' : Config Nat} (h : Steps P noH c c') (g : Frame) :
    Steps P noH ⟨c.store, g, wrap c.frame c.code⟩ ⟨c'.store, g, wrap c'.frame c'.code⟩ :=
  Relation.ReflTransGen.lift (fun c : Config Nat => (⟨c.store, g, wrap c.frame c.code⟩ : Config Nat))
    (fun _ _ hab => Step.ctxtFrame (Step.ctxtLabel hab)) _ _ h

/-- A finished call returns its value. -/
theorem unwrap (s : Store Nat) (F g : Frame) (v : Val) :
    Steps P noH ⟨s, g, wrap F (vals [v])⟩ ⟨s, g, vals [v]⟩ := by
  have h₁ : Execution.Core.Step P noH ⟨s, g, wrap F (vals [v])⟩ ⟨s, g, [.frame 1 F (vals [v])]⟩ :=
    Step.ctxtFrame Step.labelVals
  have h₂ : Execution.Core.Step P noH ⟨s, g, [.frame 1 F (vals [v])]⟩ ⟨s, g, vals [v]⟩ :=
    Step.frameVals rfl
  exact h₁.steps.trans h₂.steps

variable {fi₀ fi₁ fi₂ fi₃ : FuncInst Nat}

/-- Entering `run`. -/
theorem enter_run (h : Shape fi₀ fi₁ fi₂ fi₃) :
    ∃ r c : FuncIdx, r.toNat = 2 ∧ c.toNat = 1 ∧ Execution.Core.Step P noH (invoke cbS 3 [])
      ⟨cbS, {}, wrap (F₃ fi₃) [.plain (.refFunc r), .plain (.call c)]⟩ := by
  obtain ⟨t, r, c, hc, hr, hcc⟩ := h.code₃
  obtain ⟨ps, rs, he, hps, hrs⟩ := h.ty₃
  have hf : cbS.funcs[3]? = some fi₃ := by rw [h.funcs]; rfl
  have hs := Step.callRefFunc (P := P) (host := noH) (s := cbS) (f := {})
    (c := .callRefType ((cbS.funcs[3]?.map FuncInst.type).getD default)) (vs := [])
    trivial hf he hps.symm hc
  rw [hrs] at hs
  exact ⟨r, c, hr, hcc, hs⟩

/-- `ref.func cb; call apply` enters `apply` with the reference to `cb`. -/
theorem run_to_apply (h : Shape fi₀ fi₁ fi₂ fi₃) {r c : FuncIdx} (hr : r.toNat = 2)
    (hc : c.toNat = 1) : ∃ (x : LocalIdx) (y : TypeIdx), x.toNat = 0 ∧
      Steps P noH ⟨cbS, F₃ fi₃, [.plain (.refFunc r), .plain (.call c)]⟩
        ⟨cbS, F₃ fi₃, wrap (F₁ fi₁) [.plain (.localGet x), .plain (.callRef y)]⟩ := by
  obtain ⟨t, x, y, hcode, hx⟩ := h.code₁
  obtain ⟨ps, rs, he, hps, hrs⟩ := h.ty₁
  have hf : cbS.funcs[1]? = some fi₁ := by rw [h.funcs]; rfl
  have href : (F₃ fi₃).module.funcs[r.toNat]? = some 2 := by simp [Frame.forCall, h.mod₃, hr]
  have hcall : (F₃ fi₃).module.funcs[c.toNat]? = some 1 := by simp [Frame.forCall, h.mod₃, hc]
  have h₁ : Execution.Core.Step P noH ⟨cbS, F₃ fi₃, [.plain (.refFunc r), .plain (.call c)]⟩
      ⟨cbS, F₃ fi₃, [.ref (.func 2), .plain (.call c)]⟩ :=
    ULinkExample.step_head (is := [.plain (.refFunc r)]) (Step.reference (RefStep.refFunc href))
      (by simp)
  have h₂ : Execution.Core.Step P noH ⟨cbS, F₃ fi₃, [.ref (.func 2), .plain (.call c)]⟩
      ⟨cbS, F₃ fi₃, [.ref (.func 2), .ref (.func 1), .callRefType fi₁.type]⟩ :=
    Step.ctxtInstrs (vs := [.ref (.func 2)]) (rest := [])
      (Step.call (P := P) (host := noH) hcall hf) (.inl (by simp))
  have h₃ := Step.callRefFunc (P := P) (host := noH) (s := cbS) (f := F₃ fi₃)
    (c := .callRefType fi₁.type) (vs := [.ref (.func 2)]) trivial hf he (by rw [hps]; rfl) hcode
  rw [hrs] at h₃
  exact ⟨x, y, hx, h₁.steps.trans (h₂.steps.trans h₃.steps)⟩

/-- `apply` calls back `cb`, which calls the host import. -/
theorem apply_to_host (h : Shape fi₀ fi₁ fi₂ fi₃) {x : LocalIdx} {y : TypeIdx} (hx : x.toNat = 0) :
    Steps P noH ⟨cbS, F₁ fi₁, [.plain (.localGet x), .plain (.callRef y)]⟩
      ⟨cbS, F₁ fi₁, wrap (F₂ fi₂) [.ref (.func 0), .callRefType fi₀.type]⟩ := by
  obtain ⟨t, z, hcode, hz⟩ := h.code₂
  obtain ⟨ps, rs, he, hps, hrs⟩ := h.ty₂
  have hf₂ : cbS.funcs[2]? = some fi₂ := by rw [h.funcs]; rfl
  have hf₀ : cbS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  have hl : (F₁ fi₁).local? x = some (some (.ref (.func 2))) := by
    simp [Frame.local?, Frame.forCall, hx]
  have h₁ : Execution.Core.Step P noH ⟨cbS, F₁ fi₁, [.plain (.localGet x), .plain (.callRef y)]⟩
      ⟨cbS, F₁ fi₁, [.ref (.func 2), .plain (.callRef y)]⟩ :=
    ULinkExample.step_head (is := [.plain (.localGet x)]) (Step.variable (VariableStep.localGet hl))
      (by simp)
  have h₂ := Step.callRefFunc (P := P) (host := noH) (s := cbS) (f := F₁ fi₁)
    (c := .plain (.callRef y)) (vs := []) trivial hf₂ he hps.symm hcode
  rw [hrs] at h₂
  have hcall : (F₂ fi₂).module.funcs[z.toNat]? = some 0 := by simp [Frame.forCall, h.mod₂, hz]
  have h₃ : Execution.Core.Step P noH ⟨cbS, F₂ fi₂, [.plain (.call z)]⟩
      ⟨cbS, F₂ fi₂, [.ref (.func 0), .callRefType fi₀.type]⟩ := Step.call hcall hf₀
  exact h₁.steps.trans (h₂.steps.trans (step_in h₃ _).steps)

/-- The callout context: `run`, `apply` and `cb`, each under its frame and label. -/
def calloutCtx (fi₁ fi₂ fi₃ : FuncInst Nat) : Ctx :=
  .frame [] 1 (F₃ fi₃) (.label [] 1 [] (.frame [] 1 (F₁ fi₁) (.label [] 1 []
    (.frame [] 1 (F₂ fi₂) (.label [] 1 [] (.top [] []) []) []) []) []) []) []

theorem calloutCtx_fill (X : List Admin) :
    (calloutCtx fi₁ fi₂ fi₃).fill X = wrap (F₃ fi₃) (wrap (F₁ fi₁) (wrap (F₂ fi₂) X)) := by
  simp [calloutCtx, Ctx.fill, vals]

/-- **`$invoke(run)` runs, through `apply` and the callback `cb`, to the host call.** -/
theorem run_to_callout (h : Shape fi₀ fi₁ fi₂ fi₃) :
    ∃ r c : FuncIdx, Execution.Core.Step P noH (invoke cbS 3 [])
      ⟨cbS, {}, wrap (F₃ fi₃) [.plain (.refFunc r), .plain (.call c)]⟩ ∧
      Steps P noH ⟨cbS, {}, wrap (F₃ fi₃) [.plain (.refFunc r), .plain (.call c)]⟩
        ⟨cbS, {}, (calloutCtx fi₁ fi₂ fi₃).fill [.ref (.func 0), .callRefType fi₀.type]⟩ := by
  obtain ⟨r, c, hr, hc, h₀⟩ := enter_run (P := P) h
  obtain ⟨x, y, hx, h₁⟩ := run_to_apply (P := P) h hr hc
  have h₂ := apply_to_host (P := P) h (y := y) hx
  have h₁' := steps_in h₁ {}
  have h₂' := steps_in (steps_in h₂ (F₃ fi₃)) {}
  rw [calloutCtx_fill]
  exact ⟨r, c, h₀, h₁'.trans h₂'⟩

/-- The host call is a callout of the linked thread. -/
theorem callout (h : Shape fi₀ fi₁ fi₂ fi₃) :
    decompose? cbS ((calloutCtx fi₁ fi₂ fi₃).fill [.ref (.func 0), .callRefType fi₀.type]) =
      some (calloutCtx fi₁ fi₂ fi₃, 0, 0, []) := by
  obtain ⟨ps, rs, he, hps, -⟩ := h.ty₀
  have hf₀ : cbS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  exact Linking.decompose?_fill (args := []) _ trivial hf₀ he hps.symm h.code₀

/-- **The host's answer `v` unwinds to `v`**, in any store. -/
theorem run_unwind (s' : Store Nat) (v : Val) :
    Steps P noH ⟨s', {}, (calloutCtx fi₁ fi₂ fi₃).fill (vals [v])⟩ ⟨s', {}, vals [v]⟩ := by
  rw [calloutCtx_fill]
  have h₁ := steps_in (steps_in (unwrap (P := P) s' (F₂ fi₂) (F₁ fi₁) v) (F₃ fi₃)) {}
  have h₂ := steps_in (unwrap (P := P) s' (F₁ fi₁) (F₃ fi₃) v) {}
  exact h₁.trans (h₂.trans (unwrap s' (F₃ fi₃) {} v))

end Run

/-! ### The games -/

section Games

variable {P : Silmaril.Wasm.Numerics.Profile}

/-- **The linked module's play**: asked `run`, it asks the host (from the callback `cb`, inside
`apply`), and answers with the host's answer, every profile, every answer value and store. -/
theorem linked_play (s' : Store Nat) (v : Val) :
    runPlay ⟨s', .values [v]⟩ ∈ cbLink.U.strategy P := by
  obtain ⟨fi₀, fi₁, fi₂, fi₃, h⟩ := shape
  obtain ⟨r, c, h₀, hrun⟩ := run_to_callout (P := P) h
  have hd := callout h
  have hint : InternalP P (cbS, .pending 3 [])
      (cbS, .active {} (wrap (F₃ fi₃) [.plain (.refFunc r), .plain (.call c)])) := ⟨_, _, rfl, h₀⟩
  have r₁ := ULinkExample.run_of_steps (U := cbLink.U) (q := runQ) hrun
  have hco : CalloutAt cbS (.active {} ((calloutCtx fi₁ fi₂ fi₃).fill
      [.ref (.func 0), .callRefType fi₀.type])) 0 [] := ⟨_, _, hd⟩
  have hres : resumeResult cbS (.active {} ((calloutCtx fi₁ fi₂ fi₃).fill
      [.ref (.func 0), .callRefType fi₀.type])) (.values [v]) =
      .active {} ((calloutCtx fi₁ fi₂ fi₃).fill (vals [v])) := resume_active hd _
  have r₂ := ULinkExample.run_of_steps (U := cbLink.U) (q := runQ) (run_unwind (P := P) (fi₁ := fi₁) (fi₂ := fi₂) (fi₃ := fi₃) s' v)
  have hfinal : ResultAt s' (.active {} (vals [v])) (.values [v]) := rfl
  have r₃ : (cbLink.U.lts P).Run (.waiting runQ cbS (.active {} ((calloutCtx fi₁ fi₂ fi₃).fill
      [.ref (.func 0), .callRefType fi₀.type])) hostQ)
      [.inl (.ans hostQ ⟨s', .values [v]⟩), .inr (.ans runQ ⟨s', .values [v]⟩)] .idle := by
    refine .vis (UInstance.Trans.uret ⟨s', .values [v]⟩) ?_
    rw [hres]
    exact r₂.append (.vis (UInstance.Trans.oret hfinal) (.nil _))
  exact Untyped.mem_strategy_iff.2 ⟨.idle, .vis (UInstance.Trans.call runQ)
    (.tau (UInstance.Trans.tau hint) (r₁.append (.vis (UInstance.Trans.ucall hco) r₃)))⟩

/-- The play's stores have the layout when the host's store has it. -/
theorem play_layout {s' : Store Nat} (hs' : cbLink.Layout s') (v : Val) :
    cbLink.LayoutPlay (runPlay ⟨s', .values [v]⟩) := by
  intro m hm
  simp only [runPlay, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact cbS_layout
  · trivial
  · exact hs'
  · exact ⟨cbS_layout, hs'⟩

/-- **The composite of provider and consumer has the same play**, read through `stubUp`: the
consumer's call of `apply` is a question to the provider, which calls back `cb` in the shared
store, whose host call (an import the provider does not resolve) is the composite's own import
call. -/
theorem comp_play {s' : Store Nat} (hs' : cbLink.Layout s') (v : Val) :
    (runPlay ⟨s', .values [v]⟩).map cbLink.stubUp ∈ cbLink.compStrategy P :=
  link_le_comp (play_layout hs' v) (linked_play s' v)

end Games

end Silmaril.Proofs.Wasm.Game.ULinkCallback
