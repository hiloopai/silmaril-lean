module

public import Silmaril.Wasm.Jco.Async.Native.Defs
public import Silmaril.Wasm.Jco.Async.Thms
public import Silmaril.Wasm.Jco.Thin.Canon.Thms

/-!
# Natively async modules and thin async recognition: proofs

Proofs of `Silmaril.Wasm.Jco.Async.Native.Thms`.

* `thinA_find`, `thinA_callExport`: the thin async wrapper follows the native async convention.
* `drive_yield_exit`: a `YIELD` whose callback answers `EXIT` ends the callback loop.
  `asyncCall_yield`: so a yielding epilogue is the plain one.
* `lift_native`: one world function of the native convention, for a module that inlines the
  epilogue, is `aspecCall`.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Native

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)

variable (M : CoreInst)

theorem thinA_find (md : AMeta) (r name : String) :
    (thinA md r).lifts.find? (·.sig.name == name) =
      (md.world.find? (·.sig.name == name)).map
        fun s => (⟨s.sig, s.sig.name, r, s.async⟩ : NLift) := by
  simp only [thinA, List.find?_map]
  rfl

theorem thinA_callExport (N : NInst M) (md : AMeta) (r name : String) (vs : List PVal) :
    (thinA md r).callExport N name vs = canonSpecA N md r name vs := by
  unfold NComp.callExport canonSpecA
  rw [thinA_find]
  cases md.world.find? (·.sig.name == name) with
  | none => rfl
  | some s =>
    rcases s with ⟨sig, _ | st⟩ <;> rfl

/-! ## The callback loop -/

/-- The outcomes of a `YIELD` whose callback answers `EXIT`. -/
theorem drive_yield_out (cb : List Flat → RM M.withStore.St (List Flat))
    (hcb : ∀ a, cb a = pure [i32n cbExit]) (s : M.withStore.St) (o : Out M.withStore.St Unit)
    (h : Drive M cb [i32n cbYield] s o) : o = .ok () s := by
  have hex : @Eq (RM M.withStore.St Unit) (Drive M cb [i32n cbExit]) (pure ()) := drive_exit M cb
  cases h with
  | exit _ hc => exact absurd hc (by simp [cbYield])
  | yieldOk hc hcb' hd =>
    have e : (Out.ok _ _ : Out M.withStore.St (List Flat)) = .ok [i32n cbExit] s :=
      (RM.pure_apply _ _ _).1 (hcb _ ▸ hcb')
    cases e
    exact (RM.pure_apply _ _ _).1 (hex ▸ hd)
  | yieldTrap hc hcb' =>
    have e : (Out.trap : Out M.withStore.St (List Flat)) = .ok [i32n cbExit] s :=
      (RM.pure_apply _ _ _).1 (hcb _ ▸ hcb')
    cases e
  | waitOk hc => exact absurd hc (by simp [cbYield])
  | waitTrap hc => exact absurd hc (by simp [cbYield])
  | bad hb => exact absurd ⟨_, rfl, by simp [cbYield]⟩ hb

theorem drive_yield_exit (cb : List Flat → RM M.withStore.St (List Flat))
    (hcb : ∀ a, cb a = pure [i32n cbExit]) :
    @Eq (RM M.withStore.St Unit) (Drive M cb [i32n cbYield]) (pure ()) := by
  funext s o
  apply propext
  refine ⟨drive_yield_out M cb hcb s o, fun h => ?_⟩
  have ho : o = .ok () s := (RM.pure_apply _ _ _).1 h
  have h1 : cb [i32n 0, i32n 0, i32n 0] s (.ok [i32n cbExit] s) := by
    rw [hcb]
    rfl
  have h2 : Drive M cb [i32n cbExit] s (.ok () s) := Drive.exit s (by simp [cbExit])
  rw [ho]
  exact Drive.yieldOk (by simp [cbYield]) h1 h2

/-- A yielding epilogue, whose callback answers `EXIT`, is the plain one. -/
theorem asyncCall_yield (R core cb cb' : List Flat → RM M.withStore.St (List Flat))
    (hcb : ∀ a, cb a = pure [i32n cbExit]) (sig : Sig) (vs : List PVal) :
    asyncCall M R (shimRunWith M core sig.result [i32n cbYield]) cb .callback sig vs =
      asyncCall M R (shimRun M core sig.result .callback) cb' .callback sig vs := by
  simp only [asyncCall, shimRun, shimRunWith, Style.exitResult, RM.bind_assoc, RM.pure_bind,
    drive_yield_exit M cb hcb, drive_exit]

/-! ## Agreement with `awrap` -/

theorem reallocAgrees_withStore (md : Meta) (r : String) (hR : ReallocAgrees M md r) :
    ReallocAgrees M.withStore md r := fun n => by
  show RM.liftFst _ = RM.liftFst _
  rw [hR]

/-- The async epilogue under `canon lift async` is `aspecCall`, once the lowering is the C
convention's. -/
theorem asyncCall_shim_spec (md : AMeta) (R cb : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (st : Style) (hs : inMem sig.result = false)
    (hp : ∀ vs, lowerParams M.withStore R sig.params vs = md.sync.specParams M.withStore sig.params vs)
    (vs : List PVal) :
    asyncCall M R (shimRun M (M.withStore.call sig.name) sig.result st) cb st sig vs =
      aspecCall M md ⟨sig, some st⟩ vs := by
  rw [asyncCall_shim, canonCall_specCall M.withStore md.sync sig hs hp]
  rfl

/-- One world function of the native async convention, for a module that inlines the epilogue. -/
theorem lift_native (N : NInst M) (md : AMeta) (R : List Flat → RM M.withStore.St (List Flat))
    (hN : N.Inlines md) (s : ASig) (hsw : s ∈ md.world) (hs : inMem s.sig.result = false)
    (hp : ∀ vs, lowerParams M.withStore R s.sig.params vs =
      md.sync.specParams M.withStore s.sig.params vs) (vs : List PVal) :
    (match s with
      | ⟨sig, none⟩ => canonCall M.withStore R (M.withStore.call sig.name) sig vs
      | ⟨sig, some st⟩ => asyncCall M R (N.body sig.name) (N.callback sig.name) st sig vs) =
      aspecCall M md s vs := by
  rcases s with ⟨sig, _ | st⟩
  · exact canonCall_specCall M.withStore md.sync sig hs hp vs
  · rcases hN _ hsw st rfl with hb | ⟨rfl, hb, hcb⟩
    · show asyncCall M R (N.body sig.name) _ st sig vs = _
      rw [hb]
      exact asyncCall_shim_spec M md R _ sig st hs hp vs
    · show asyncCall M R (N.body sig.name) _ .callback sig vs = _
      rw [hb, asyncCall_yield M R _ _ (AComp.noCallback M) hcb]
      exact asyncCall_shim_spec M md R _ sig .callback hs hp vs

theorem sig_mem {md : AMeta} {s : ASig} (h : s ∈ md.world) : s.sig ∈ md.sync.world :=
  List.mem_map_of_mem h

/-- **The native async convention is `aspec`**, under a condition on the lowering. -/
theorem canonSpecA_eq_aspec (N : NInst M) (md : AMeta) (r : String) (hN : N.Inlines md)
    (hk : md.sync.thinOk = true)
    (hp : ∀ s ∈ md.world, ∀ vs, lowerParams M.withStore (M.withStore.call r) s.sig.params vs =
      md.sync.specParams M.withStore s.sig.params vs) :
    canonSpecA N md r = aspec M md := by
  funext name vs
  unfold canonSpecA aspec
  cases hf : md.world.find? (·.sig.name == name) with
  | none => rfl
  | some s =>
    have hsw : s ∈ md.world := List.mem_of_find?_eq_some hf
    have hs : inMem s.sig.result = false := thinOk_mem md.sync hk (sig_mem hsw)
    have e := lift_native M N md _ hN s hsw hs (hp s hsw) vs
    rcases s with ⟨sig, _ | st⟩ <;> exact e

/-! ## The inlined module -/

theorem find_name_nodup {ws : List ASig} (hn : (ws.map (·.sig.name)).Nodup) {s : ASig}
    (hs : s ∈ ws) : ws.find? (·.sig.name == s.sig.name) = some s := by
  induction ws with
  | nil => cases hs
  | cons w ws ih =>
    have hn' : w.sig.name ∉ ws.map (·.sig.name) ∧ (ws.map (·.sig.name)).Nodup := by
      simpa using hn
    rcases List.mem_cons.1 hs with rfl | hs'
    · simp
    · have hne : (w.sig.name == s.sig.name) = false := by
        have : w.sig.name ≠ s.sig.name := fun he => hn'.1 (he ▸ List.mem_map_of_mem hs')
        simpa using this
      simp [hne, ih hn'.2 hs']

theorem inlined_inlines (md : AMeta) (hn : (md.world.map (·.sig.name)).Nodup) :
    (NInst.inlined M md).Inlines md := by
  intro s hs sty hst
  left
  show (match md.world.find? (·.sig.name == s.sig.name) with
    | some ⟨sig, some st⟩ => shimRun M (M.withStore.call s.sig.name) sig.result st
    | _ => fun _ _ => RM.fail) = _
  rw [find_name_nodup hn hs]
  rcases s with ⟨sig, _ | st⟩
  · cases hst
  · cases hst
    rfl

end Silmaril.Proofs.Wasm.Jco.Async.Native
