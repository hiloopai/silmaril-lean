module

public import Silmaril.Wasm.Jco.Async.Defs
public import Silmaril.Wasm.Jco.Wrap.Thms

/-!
# Async lifts through the adaptor: proofs

Proofs of `Silmaril.Wasm.Jco.Async.Thms`. The async construction keeps the synchronous component
underneath (`base_awrap`, `base_ofComp`); an export is found at the same index as in the world
(`find_awrap`); an async shim, run under `canon lift async`, is the synchronous lift followed by
`task.return` (`asyncCall_shim`), because the shim's exit code ends the callback loop at once
(`drive_exit`) and the stackful check passes.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Jco.RM

variable (M : CoreInst)

/-! ## The synchronous component underneath -/

theorem base_ofComp (c : Comp) : (AComp.ofComp c).base = c := by
  cases c
  simp [AComp.ofComp, AComp.base, Function.comp_def]

theorem find_ofComp (c : Comp) (name : String) :
    (AComp.ofComp c).lifts.find? (·.lift.sig.name == name) =
      (c.lifts.find? (·.sig.name == name)).map fun l => ⟨l, none⟩ := by
  simp only [AComp.ofComp, List.find?_map]
  rfl

theorem callExport_ofComp (c : Comp) (name : String) (vs : List PVal) :
    (AComp.ofComp c).callExport M name vs = c.callExport M.withStore name vs := by
  unfold AComp.callExport Comp.callExport
  rw [find_ofComp, base_ofComp]
  cases c.lifts.find? (·.sig.name == name) <;> rfl

theorem sync_ofMeta (md : Meta) : (AMeta.ofMeta md).sync = md := by
  cases md
  simp [AMeta.ofMeta, AMeta.sync, Function.comp_def]

theorem zip_none : ∀ (k : Nat) (ws : List Sig),
    (liftsFrom k ws).zipWith (fun l s => (⟨l, s.async⟩ : ALift))
        (ws.map fun s => (⟨s, none⟩ : ASig)) = (liftsFrom k ws).map fun l => ⟨l, none⟩
  | _, [] => rfl
  | k, _ :: ws => by simp [liftsFrom, zip_none (k + 1) ws]

theorem awrap_ofMeta (md : Meta) : awrap (AMeta.ofMeta md) = AComp.ofComp (wrap md) := by
  have h : (AMeta.ofMeta md).world = md.world.map fun s => (⟨s, none⟩ : ASig) := rfl
  simp only [awrap, sync_ofMeta, AComp.ofComp, wrap, h, zip_none]

theorem map_sig_none : ∀ ws : List ASig, ws.all (fun s => s.async.isNone) = true →
    (ws.map (·.sig)).map (fun s => (⟨s, none⟩ : ASig)) = ws
  | [], _ => rfl
  | ⟨s, a⟩ :: ws, h => by
    have h₁ : a = none ∧ ws.all (fun s => s.async.isNone) = true := by
      simpa using h
    simp [h₁.1, map_sig_none ws h₁.2]

theorem ofMeta_sync (md : AMeta) (h : md.asyncFree = true) : AMeta.ofMeta md.sync = md := by
  cases md
  simp only [AMeta.ofMeta, AMeta.sync]
  rw [map_sig_none _ h]

theorem awrap_sync (md : AMeta) (h : md.asyncFree = true) :
    awrap md = AComp.ofComp (wrap md.sync) := by
  have e := awrap_ofMeta md.sync
  rwa [ofMeta_sync md h] at e

/-! ## The construction -/

theorem map_lift_zip : ∀ (k : Nat) (ws : List ASig),
    ((liftsFrom k (ws.map (·.sig))).zipWith (fun l s => (⟨l, s.async⟩ : ALift)) ws).map
      (·.lift) = liftsFrom k (ws.map (·.sig))
  | _, [] => rfl
  | k, _ :: ws => by simp [liftsFrom, map_lift_zip (k + 1) ws]

theorem base_awrap (md : AMeta) : (awrap md).base = wrap md.sync := by
  simp only [AComp.base, awrap, wrap]
  rw [show md.sync.world = md.world.map (·.sig) from rfl, map_lift_zip]

theorem find_awrap (name : String) : ∀ (k : Nat) (ws : List ASig) (al : ALift),
    ((liftsFrom k (ws.map (·.sig))).zipWith (fun l s => (⟨l, s.async⟩ : ALift)) ws).find?
        (·.lift.sig.name == name) = some al →
      ∃ i s, ws[i]? = some s ∧ ws.find? (·.sig.name == name) = some s ∧
        al = ⟨⟨s.sig, .adapt (k + i + 1), .adapt 0⟩, s.async⟩
  | _, [], _, h => by cases h
  | k, s :: ws, al, h => by
    by_cases hn : (s.sig.name == name) = true
    · have e : al = ⟨⟨s.sig, .adapt (k + 1), .adapt 0⟩, s.async⟩ := by
        simpa [liftsFrom, hn] using h.symm
      exact ⟨0, s, rfl, by simp [hn], e⟩
    · have h' : ((liftsFrom (k + 1) (ws.map (·.sig))).zipWith
          (fun l s => (⟨l, s.async⟩ : ALift)) ws).find? (·.lift.sig.name == name) = some al := by
        simpa [liftsFrom, hn] using h
      obtain ⟨i, s', hi, hf, e⟩ := find_awrap name (k + 1) ws al h'
      refine ⟨i + 1, s', hi, by simp [hn, hf], ?_⟩
      rw [e]
      congr 3
      omega

theorem find_awrap_none (name : String) : ∀ (k : Nat) (ws : List ASig),
    ((liftsFrom k (ws.map (·.sig))).zipWith (fun l s => (⟨l, s.async⟩ : ALift)) ws).find?
        (·.lift.sig.name == name) = none → ws.find? (·.sig.name == name) = none
  | _, [], _ => rfl
  | k, s :: ws, h => by
    by_cases hn : (s.sig.name == name) = true
    · simp [liftsFrom, hn] at h
    · have h' : ((liftsFrom (k + 1) (ws.map (·.sig))).zipWith
          (fun l s => (⟨l, s.async⟩ : ALift)) ws).find? (·.lift.sig.name == name) = none := by
        simpa [liftsFrom, hn] using h
      simpa [hn] using find_awrap_none name (k + 1) ws h'

/-! ## Conformance next to the store -/

theorem returns_liftFst {σ τ α : Type} {m : RM σ α} {P : α → Prop} (h : Returns m P) :
    Returns (RM.liftFst (τ := τ) m) P := fun s a s' hm => h s.1 a s'.1 hm.2

theorem conforms_withStore (md : Meta) (hC : md.Conforms M) : md.Conforms M.withStore :=
  ⟨fun xs => returns_liftFst (hC.alloc xs), fun s hs hm xs => returns_liftFst (hC.outPtr s hs hm xs)⟩

/-! ## The async shim -/

theorem drive_exit (cb : List Flat → RM M.withStore.St (List Flat)) :
    @Eq (RM M.withStore.St Unit) (Drive M cb [i32n cbExit]) (pure ()) := by
  funext s o
  apply propext
  constructor
  · intro h
    cases h with
    | exit _ _ => rfl
    | yieldOk hc => simp [cbExit] at hc
    | yieldTrap hc => simp [cbExit] at hc
    | waitOk hc => simp [cbExit] at hc
    | waitTrap hc => simp [cbExit] at hc
    | bad hb => exact absurd ⟨_, rfl, by simp [cbExit]⟩ hb
  · intro h
    rw [pure_apply] at h
    rw [h]
    exact Drive.exit s (by simp [cbExit])

/-- Under `canon lift async`, an async shim is the synchronous lift followed by `task.return`. -/
theorem asyncCall_shim (realloc core : List Flat → RM M.withStore.St (List Flat))
    (cb : List Flat → RM M.withStore.St (List Flat)) (st : Style) (sig : Sig) (vs : List PVal) :
    asyncCall M realloc (shimRun M core sig.result st) cb st sig vs =
      (startTask M >>= fun t => canonCall M.withStore realloc core sig vs >>= fun v =>
        RM.ofOption (resVals v) >>= fun ws => builtin M (.taskReturn t ws) >>= fun _ =>
          taskResult M t >>= fun ws' => RM.ofOption (valsRes sig.result ws')) := by
  cases st <;>
    simp only [asyncCall, shimRun, canonCall, Style.exitResult, RM.bind_assoc, RM.pure_bind,
      List.isEmpty_nil, check_true, drive_exit]

/-- One lift of the async construction. -/
theorem lift_awrap (md : AMeta) (hC : md.sync.Conforms M) (i : Nat) (s : ASig)
    (hi : md.world[i]? = some s) (vs : List PVal) :
    (match (⟨⟨s.sig, .adapt (0 + i + 1), .adapt 0⟩, s.async⟩ : ALift) with
      | ⟨l, none⟩ =>
        canonCall M.withStore ((awrap md).base.callRef M.withStore l.realloc)
          ((awrap md).base.callRef M.withStore l.callee) l.sig vs
      | ⟨l, some st⟩ =>
        asyncCall M ((awrap md).base.callRef M.withStore l.realloc)
          (shimRun M ((awrap md).base.callRef M.withStore l.callee) l.sig.result st)
          (AComp.noCallback M) st l.sig vs) = aspecCall M md s vs := by
  have hi' : md.sync.world[i]? = some s.sig := by simp [AMeta.sync, hi]
  have hw := canonCall_wrap M.withStore md.sync (conforms_withStore M md.sync hC) i s.sig hi'
  rw [base_awrap, Nat.zero_add]
  rcases s with ⟨sig, _ | st⟩
  · exact hw vs
  · show asyncCall M _ _ _ st sig vs = _
    rw [asyncCall_shim, hw vs]
    rfl

end Silmaril.Proofs.Wasm.Jco.Async
