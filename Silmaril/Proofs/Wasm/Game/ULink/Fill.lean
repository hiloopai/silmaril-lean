module

public import Silmaril.Proofs.Wasm.Game.ULink.Inv

/-!
# Provider code in the consumer's context: steps and callouts

* `step_fill_inv`: **every linked step of `E.fill Y`, for live provider code `Y`, is a provider
  step of `Y` (under the empty frame of `$invoke`) in the hole of `E`.**
* `decompose_fill`: the host-call redex of `E.fill Y` is that of `Y`, in the context `E`.
* `fill_ne_result`: `E.fill Y` is not a result.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det

/-- Live provider code has a live first non-value. -/
theorem ProvLive.top {s : Store Nat} {Y : List Admin} (h : ProvLive s Y) :
    ∃ W x R, Y = vals W ++ x :: R ∧ LiveTop x := by
  rcases h with ⟨n, F, B, rfl⟩ | ⟨vs, a, c, fi, ps, rs, rfl, hc, -⟩ | ⟨c, rfl, hc⟩
  · exact ⟨[], _, [], rfl, .inl ⟨_, _, _, rfl⟩⟩
  · exact ⟨vs ++ [Val.ref (.func a)], c, [], by simp [vals_append]; rfl, .inr (.inr (.inr hc))⟩
  · exact ⟨[Val.ref .null], c, [], rfl, .inr (.inr (.inr hc))⟩

/-- The first non-value of live code in a context is live. -/
theorem liveBody_fill (E : Ctx) {Y : List Admin} (hY : ∃ W x R, Y = vals W ++ x :: R ∧ LiveTop x) :
    LiveBody (E.fill Y) := by
  cases E with
  | top pre rest =>
    obtain ⟨W, x, R, rfl, hx⟩ := hY
    exact ⟨pre ++ W, x, R ++ rest, fnv_at (by simp [Ctx.fill, vals_append]) hx.val_none, hx⟩
  | label pre n c E rest =>
    exact ⟨pre, .label n c (E.fill Y), rest, fnv_at (by simp [Ctx.fill]) rfl,
      .inr (.inl ⟨_, _, _, rfl⟩)⟩
  | handler pre n cs E rest =>
    exact ⟨pre, .handler n cs (E.fill Y), rest, fnv_at (by simp [Ctx.fill]) rfl,
      .inr (.inr (.inl ⟨_, _, _, rfl⟩))⟩
  | frame pre n F E rest =>
    exact ⟨pre, .frame n F (E.fill Y), rest, fnv_at (by simp [Ctx.fill]) rfl,
      .inl ⟨_, _, _, rfl⟩⟩

/-- **Live provider code in a context is not a result.** -/
theorem fill_ne_result {s : Store Nat} {Y : List Admin} (hY : ProvLive s Y) (E : Ctx)
    (r : Result) : E.fill Y ≠ r.toAdmin := by
  intro h
  obtain ⟨W, x, R, hf, hx⟩ := liveBody_fill E hY.top
  rw [h] at hf
  cases r with
  | values vs => simp [Result.toAdmin] at hf
  | trap =>
    have := (fnv_at (l := [Admin.trap]) (W := []) (R := []) rfl rfl).symm.trans hf
    obtain ⟨-, rfl, -⟩ : [] = W ∧ Admin.trap = x ∧ [] = R := by simpa using this
    exact notLive_trap hx
  | throw a =>
    have := (fnv_at (l := [Admin.ref (.exn a), .plain .throwRef]) (W := [Val.ref (.exn a)]) (R := [])
      rfl rfl).symm.trans hf
    obtain ⟨-, rfl, -⟩ : [Val.ref (.exn a)] = W ∧ Admin.plain .throwRef = x ∧ [] = R := by
      simpa using this
    exact notLive_throwRef hx

theorem frame_ne_trap {n : Nat} {F : Frame} {B : List Admin} : Admin.frame n F B ≠ .trap := by
  intro h; cases h
theorem frame_ne_throwRef {n : Nat} {F : Frame} {B : List Admin} :
    Admin.frame n F B ≠ .plain .throwRef := by
  intro h; cases h
theorem callRef_ne_trap {c : Admin} (hc : c.IsCallRef) : c ≠ .trap := by
  rintro rfl; exact hc
theorem callRef_ne_throwRef {c : Admin} (hc : c.IsCallRef) : c ≠ .plain .throwRef := by
  rintro rfl; exact hc

/-- A provider frame at top level, under a value prefix. -/
theorem step_top_frame {P : Profile} {s : Store Nat} {f : Frame} {pre : List Val} {rest : List Admin}
    {n : Nat} {F : Frame} {B : List Admin} {d : Config Nat}
    (h : Execution.Core.Step P Det.noHost ⟨s, f, vals pre ++ [.frame n F B] ++ rest⟩ d) :
    ∃ s' Y', d = ⟨s', f, vals pre ++ Y' ++ rest⟩ ∧ ProvCode s' Y' ∧
      Execution.Core.Step P Det.noHost ⟨s, {}, [.frame n F B]⟩ ⟨s', {}, Y'⟩ := by
  obtain ⟨vs, args, c₀, hpre, hh, rfl⟩ := step_single_inv h rfl frame_ne_trap frame_ne_throwRef
  obtain ⟨rfl, hf, hp, hall⟩ := head_frame hh
  have hvs : pre = vs := by simpa using hpre
  subst hvs
  exact ⟨c₀.store, c₀.code, by rw [hf], hp, hall {}⟩

/-- The provider's call, read back from the linked head step. -/
theorem top_call_func {P : Profile} {s : Store Nat} {f : Frame} {pre : List Val}
    {rest : List Admin} {vs : List Val} {a : Nat} {c : Admin} {fi : FuncInst Nat}
    {ps rs : Ty (.list .val)} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) {vs₀ vs' : List Val}
    {a' : Nat} {fi' : FuncInst Nat} {ps' rs' : Ty (.list .val)} {code : Func}
    (hpre : pre ++ vs ++ [Val.ref (.func a)] = vs₀ ++ (vs' ++ [Val.ref (.func a')]))
    (hf' : s.funcs[a']? = some fi') (he' : Expand fi'.type (.func ps' rs'))
    (hn' : vs'.length = ps'.length) (hcode' : fi'.code = .wasm code) :
    ∃ s' Y', (⟨s, f, vals vs₀ ++ callCode fi' rs' code vs' ++ rest⟩ : Config Nat) =
        ⟨s', f, vals pre ++ Y' ++ rest⟩ ∧ ProvCode s' Y' ∧
      Execution.Core.Step P Det.noHost ⟨s, {}, vals vs ++ [.ref (.func a), c]⟩ ⟨s', {}, Y'⟩ := by
  have hpre' : pre ++ vs ++ [Val.ref (.func a)] = (vs₀ ++ vs') ++ [Val.ref (.func a')] := by
    rw [hpre, List.append_assoc]
  obtain ⟨hpv, ha⟩ := append_singleton_inj.mp hpre'
  have ha' : a' = a := by simpa using ha.symm
  subst ha'
  have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  subst hfi
  obtain ⟨rfl, rfl⟩ : ps' = ps ∧ rs' = rs := Ty.func.inj (Expand.func_eq he' he)
  obtain ⟨rfl, rfl⟩ := List.append_inj' hpv (hn.trans hn'.symm)
  exact ⟨s, _, rfl, .inl (.inl ⟨_, _, _, rfl⟩), Step.callRefFunc hc hf' he' hn' hcode'⟩

/-- A provider call at top level, under a value prefix. -/
theorem step_top_call {P : Profile} {s : Store Nat} {f : Frame} {pre : List Val}
    {rest : List Admin} {vs : List Val} {a : Nat} {c : Admin} {fi : FuncInst Nat}
    {ps rs : Ty (.list .val)} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) {d : Config Nat}
    (h : Execution.Core.Step P Det.noHost
      ⟨s, f, vals pre ++ (vals vs ++ [.ref (.func a), c]) ++ rest⟩ d) :
    ∃ s' Y', d = ⟨s', f, vals pre ++ Y' ++ rest⟩ ∧ ProvCode s' Y' ∧
      Execution.Core.Step P Det.noHost ⟨s, {}, vals vs ++ [.ref (.func a), c]⟩ ⟨s', {}, Y'⟩ := by
  have hcode : vals pre ++ (vals vs ++ [.ref (.func a), c]) ++ rest =
      vals (pre ++ vs ++ [Val.ref (.func a)]) ++ [c] ++ rest := by simp [vals_append]; rfl
  obtain ⟨vs₀, args, c₀, hpre, hh, rfl⟩ := step_single_inv (hcode ▸ h) (IsCallRef.val_none hc)
    (callRef_ne_trap hc) (callRef_ne_throwRef hc)
  rcases head_call hc hh with ⟨rfl, rfl⟩ | ⟨vs', a', fi', ps', rs', code, rfl, hf', he', hn', hcode', rfl⟩
  · have := (append_singleton_inj.mp hpre).2
    cases this
  · exact top_call_func hc hf he hn hpre hf' he' hn' hcode'

/-- A provider call on `null` at top level, under a value prefix. -/
theorem step_top_null {P : Profile} {s : Store Nat} {f : Frame} {pre : List Val}
    {rest : List Admin} {c : Admin} (hc : c.IsCallRef) {d : Config Nat}
    (h : Execution.Core.Step P Det.noHost ⟨s, f, vals pre ++ [.ref .null, c] ++ rest⟩ d) :
    ∃ s' Y', d = ⟨s', f, vals pre ++ Y' ++ rest⟩ ∧ ProvCode s' Y' ∧
      Execution.Core.Step P Det.noHost ⟨s, {}, [.ref .null, c]⟩ ⟨s', {}, Y'⟩ := by
  have hcode : vals pre ++ [.ref .null, c] ++ rest = vals (pre ++ [Val.ref .null]) ++ [c] ++ rest := by
    simp only [vals_append, List.append_assoc]; rfl
  rw [hcode] at h
  obtain ⟨vs₀, args, c₀, hpre, hh, rfl⟩ :=
    step_single_inv h (IsCallRef.val_none hc) (callRef_ne_trap hc) (callRef_ne_throwRef hc)
  rcases head_call hc hh with ⟨rfl, rfl⟩ | ⟨vs', a', fi', ps', rs', code, rfl, -⟩
  · have hv : pre = vs₀ := (append_singleton_inj.mp hpre).1
    subst hv
    exact ⟨s, [.trap], by simp, .inr ⟨.trap, rfl⟩, Step.callRefNull hc⟩
  · have hpre' : pre ++ [Val.ref .null] = (vs₀ ++ vs') ++ [Val.ref (.func a')] := by
      rw [hpre, List.append_assoc]
    have := (append_singleton_inj.mp hpre').2
    cases this

/-- The induction hypothesis of `step_fill_inv`. -/
abbrev FillInv (P : Profile) (E : Ctx) : Prop :=
  ∀ {s : Store Nat} {f : Frame} {Y : List Admin} {d : Config Nat}, ProvLive s Y →
    Execution.Core.Step P Det.noHost ⟨s, f, E.fill Y⟩ d →
    ∃ s' Y', d = ⟨s', f, E.fill Y'⟩ ∧ ProvCode s' Y' ∧
      Execution.Core.Step P Det.noHost ⟨s, {}, Y⟩ ⟨s', {}, Y'⟩

theorem fill_label_inv {P : Profile} {pre : List Val} {n : Nat} {cont : List Instr} {E : Ctx}
    {rest : List Admin} (ih : FillInv P E) : FillInv P (.label pre n cont E rest) := by
  intro s f Y d hY h
  have h' : Execution.Core.Step P Det.noHost
      ⟨s, f, vals pre ++ [.label n cont (E.fill Y)] ++ rest⟩ d := h
  obtain ⟨vs, args, c₀, hpre, hh, rfl⟩ := step_single_inv h' rfl (by simp) (by simp)
  obtain ⟨rfl, s', f', B', hin, rfl⟩ := head_label_live hh (liveBody_fill E hY.top)
  obtain ⟨s'', Y', hd, hp, hst⟩ := ih hY hin
  obtain ⟨rfl, rfl, rfl⟩ : s' = s'' ∧ f' = f ∧ B' = E.fill Y' := by
    simpa only [Config.mk.injEq] using hd
  have hv : pre = vs := by simpa using hpre
  subst hv
  exact ⟨s', Y', rfl, hp, hst⟩

theorem fill_handler_inv {P : Profile} {pre : List Val} {n : Nat} {cs : List Catch} {E : Ctx}
    {rest : List Admin} (ih : FillInv P E) : FillInv P (.handler pre n cs E rest) := by
  intro s f Y d hY h
  have h' : Execution.Core.Step P Det.noHost
      ⟨s, f, vals pre ++ [.handler n cs (E.fill Y)] ++ rest⟩ d := h
  obtain ⟨vs, args, c₀, hpre, hh, rfl⟩ := step_single_inv h' rfl (by simp) (by simp)
  obtain ⟨rfl, s', f', B', hin, rfl⟩ := head_handler_live hh (liveBody_fill E hY.top)
  obtain ⟨s'', Y', hd, hp, hst⟩ := ih hY hin
  obtain ⟨rfl, rfl, rfl⟩ : s' = s'' ∧ f' = f ∧ B' = E.fill Y' := by
    simpa only [Config.mk.injEq] using hd
  have hv : pre = vs := by simpa using hpre
  subst hv
  exact ⟨s', Y', rfl, hp, hst⟩

theorem fill_frame_inv {P : Profile} {pre : List Val} {n : Nat} {F : Frame} {E : Ctx}
    {rest : List Admin} (ih : FillInv P E) : FillInv P (.frame pre n F E rest) := by
  intro s f Y d hY h
  have h' : Execution.Core.Step P Det.noHost
      ⟨s, f, vals pre ++ [.frame n F (E.fill Y)] ++ rest⟩ d := h
  obtain ⟨vs, args, c₀, hpre, hh, rfl⟩ := step_single_inv h' rfl (by simp) (by simp)
  obtain ⟨rfl, s', F', B', hin, rfl⟩ := head_frame_live hh (liveBody_fill E hY.top)
  obtain ⟨s'', Y', hd, hp, hst⟩ := ih hY hin
  obtain ⟨rfl, rfl, rfl⟩ : s' = s'' ∧ F' = F ∧ B' = E.fill Y' := by
    simpa only [Config.mk.injEq] using hd
  have hv : pre = vs := by simpa using hpre
  subst hv
  exact ⟨s', Y', rfl, hp, hst⟩

/-- **A linked step of live provider code in a context is a provider step in the hole.** -/
theorem step_fill_inv {P : Profile} (E : Ctx) : FillInv P E := by
  induction E with
  | top pre rest =>
    intro s f Y d hY h
    rcases hY with ⟨n, F, B, rfl⟩ | ⟨vs, a, c, fi, ps, rs, rfl, hc, hf, he, hn⟩ | ⟨c, rfl, hc⟩
    · exact step_top_frame h
    · exact step_top_call hc hf he hn h
    · exact step_top_null hc h
  | label pre n cont E rest ih => exact fill_label_inv ih
  | handler pre n cs E rest ih => exact fill_handler_inv ih
  | frame pre n F E rest ih => exact fill_frame_inv ih

/-! ### Callouts -/

/-- Plugging the redex context into an outer context. -/
abbrev compR (E : Ctx) (p : Ctx × Nat × Nat × List Val) : Ctx × Nat × Nat × List Val :=
  (Ctx.comp E p.1, p.2)

theorem topRedex_call {s : Store Nat} {pre vs : List Val} {rest : List Admin} {a : Nat}
    {fi : FuncInst Nat} {ps rs : Ty (.list .val)} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) :
    topRedex s (pre ++ vs ++ [Val.ref (.func a)]) rest =
      (topRedex s (vs ++ [Val.ref (.func a)]) []).map (compR (.top pre rest)) := by
  unfold topRedex
  simp only [List.getLast?_concat, List.dropLast_concat]
  cases hh : hostArity? s a with
  | none => rfl
  | some hn' =>
    obtain ⟨h, n⟩ := hn'
    obtain ⟨fi', ps', rs', hf', -, he', rfl⟩ := hostArity?_eq_some hh
    have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    subst hfi
    have hps : ps' = ps := (Ty.func.inj (Expand.func_eq he' he)).1
    subst hps
    rw [← hn]
    simp [Ctx.comp]

theorem decompose_frame_top (s : Store Nat) (pre : List Val) (rest : List Admin) (n : Nat)
    (F : Frame) (B : List Admin) :
    decompose? s (vals pre ++ [.frame n F B] ++ rest) =
      (decompose? s B).map fun (E, a, h, args) => (.frame pre n F E rest, a, h, args) := by
  have hsp : splitVals (vals pre ++ [.frame n F B] ++ rest) = (pre, .frame n F B :: rest) := by
    simpa using SingleThreaded.splitVals_vals_cons (vs := pre) (d := .frame n F B) rfl rest
  rw [decompose?_of_split hsp]
  rfl

theorem toAdmin_ref (r : Ref) : (Val.ref r).toAdmin = Admin.ref r := rfl

theorem decompose_top_frameY (s : Store Nat) (pre : List Val) (rest : List Admin) (n : Nat)
    (F : Frame) (B : List Admin) :
    decompose? s ((Ctx.top pre rest).fill [.frame n F B]) =
      (decompose? s [.frame n F B]).map (compR (.top pre rest)) := by
  have h₁ := decompose_frame_top s pre rest n F B
  have h₂ := decompose_frame_top s [] [] n F B
  simp only [vals, List.map_nil, List.nil_append, List.append_nil] at h₂
  show decompose? s (vals pre ++ [.frame n F B] ++ rest) = _
  rw [h₁, h₂, Option.map_map]
  congr 1
  funext p
  obtain ⟨E, a, h, args⟩ := p
  simp [Ctx.comp]

theorem splitVals_call {pre : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef)
    (rest : List Admin) :
    splitVals (vals pre ++ [.ref (.func a), c] ++ rest) = (pre ++ [Val.ref (.func a)], c :: rest) := by
  have := SingleThreaded.splitVals_vals_cons (vs := pre ++ [Val.ref (.func a)])
    (IsCallRef.val_none hc) rest
  simpa [vals_append, toAdmin_ref] using this

theorem decompose_top_callY {s : Store Nat} {pre vs : List Val} {rest : List Admin} {a : Nat}
    {c : Admin} {fi : FuncInst Nat} {ps rs : Ty (.list .val)} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) :
    decompose? s ((Ctx.top pre rest).fill (vals vs ++ [.ref (.func a), c])) =
      (decompose? s (vals vs ++ [.ref (.func a), c])).map (compR (.top pre rest)) := by
  have hsp₁ : splitVals ((Ctx.top pre rest).fill (vals vs ++ [.ref (.func a), c])) =
      (pre ++ vs ++ [Val.ref (.func a)], c :: rest) := by
    have := splitVals_call (pre := pre ++ vs) (a := a) hc rest
    simpa [Ctx.fill, vals_append] using this
  have hsp₂ : splitVals (vals vs ++ [.ref (.func a), c]) = (vs ++ [Val.ref (.func a)], [c]) := by
    simpa using splitVals_call (pre := vs) (a := a) hc []
  rw [decompose?_of_split hsp₁, decompose?_of_split hsp₂, decompHead_of_IsCallRef hc,
    decompHead_of_IsCallRef hc]
  exact topRedex_call hf he hn

theorem decompose_top_nullY {s : Store Nat} {pre : List Val} {rest : List Admin} {c : Admin}
    (hc : c.IsCallRef) :
    decompose? s ((Ctx.top pre rest).fill [.ref .null, c]) =
      (decompose? s [.ref .null, c]).map (compR (.top pre rest)) := by
  have hsp₁ : splitVals ((Ctx.top pre rest).fill [.ref .null, c]) = (pre ++ [Val.ref .null], c :: rest) := by
    have := SingleThreaded.splitVals_vals_cons (vs := pre ++ [Val.ref .null]) (IsCallRef.val_none hc) rest
    simpa [Ctx.fill, vals_append, toAdmin_ref] using this
  have hsp₂ : splitVals [.ref .null, c] = ([Val.ref .null], [c]) := by
    simpa [toAdmin_ref] using SingleThreaded.splitVals_vals_cons (vs := [Val.ref .null])
      (IsCallRef.val_none hc) []
  rw [decompose?_of_split hsp₁, decompose?_of_split hsp₂, decompHead_of_IsCallRef hc,
    decompHead_of_IsCallRef hc]
  simp [topRedex]

theorem decompose_label_fill (s : Store Nat) (pre : List Val) (n : Nat) (cont : List Instr) (E : Ctx)
    (rest Y : List Admin) :
    decompose? s ((Ctx.label pre n cont E rest).fill Y) =
      (decompose? s (E.fill Y)).map fun (E', a, h, args) => (.label pre n cont E' rest, a, h, args) := by
  have hsp : splitVals (vals pre ++ [.label n cont (E.fill Y)] ++ rest) =
      (pre, .label n cont (E.fill Y) :: rest) := by
    simpa using SingleThreaded.splitVals_vals_cons (vs := pre) (d := .label n cont (E.fill Y)) rfl rest
  exact (decompose?_of_split hsp).trans (decompHead_label _ _ _ _ _ _)

theorem decompose_handler_fill (s : Store Nat) (pre : List Val) (n : Nat) (cs : List Catch) (E : Ctx)
    (rest Y : List Admin) :
    decompose? s ((Ctx.handler pre n cs E rest).fill Y) =
      (decompose? s (E.fill Y)).map fun (E', a, h, args) => (.handler pre n cs E' rest, a, h, args) := by
  have hsp : splitVals (vals pre ++ [.handler n cs (E.fill Y)] ++ rest) =
      (pre, .handler n cs (E.fill Y) :: rest) := by
    simpa using SingleThreaded.splitVals_vals_cons (vs := pre) (d := .handler n cs (E.fill Y)) rfl rest
  exact (decompose?_of_split hsp).trans (decompHead_handler _ _ _ _ _ _)

/-- **The callouts of live provider code in a context.** -/
theorem decompose_fill {s : Store Nat} {Y : List Admin} (hY : ProvLive s Y) (E : Ctx) :
    decompose? s (E.fill Y) = (decompose? s Y).map (compR E) := by
  induction E with
  | top pre rest =>
    rcases hY with ⟨n, F, B, rfl⟩ | ⟨vs, a, c, fi, ps, rs, rfl, hc, hf, he, hn⟩ | ⟨c, rfl, hc⟩
    · exact decompose_top_frameY s pre rest n F B
    · exact decompose_top_callY hc hf he hn
    · exact decompose_top_nullY hc
  | label pre n cont E rest ih =>
    rw [decompose_label_fill, ih, Option.map_map]
    rfl
  | handler pre n cs E rest ih =>
    rw [decompose_handler_fill, ih, Option.map_map]
    rfl
  | frame pre n F E rest ih =>
    rw [show (Ctx.frame pre n F E rest).fill Y = vals pre ++ [.frame n F (E.fill Y)] ++ rest from rfl,
      decompose_frame_top, ih, Option.map_map]
    rfl

end Silmaril.Proofs.Wasm.Game.ULink
