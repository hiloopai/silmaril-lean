module

public import Silmaril.Wasm.Jco.Async.XWorld.Defs
public import Silmaril.Wasm.Jco.Async.Future.Thms

/-!
# Stream and future results in the world syntax: proofs

Proofs of `Silmaril.Wasm.Jco.Async.XWorld.Thms`.

* `toAMeta_ofAMeta`, `kindOf_ofAMeta`: metadata with every result plain.
* `xcallExport_ofAMeta`: then the wrapper is `awrap`.
* `xcallExport_stream`, `xcallExport_future`: an async function with a stream (future) result is
  `asyncCallS` (`asyncCallF`) of its shim's core function, returning the handle.
* `handle_bind_ok`: what the caller sees of such a call.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.XWorld

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Val)
open Silmaril.Proofs.Wasm.Jco.Async.Early (sB)
open Silmaril.Proofs.Wasm.Jco.Async.Future (fB)

theorem toAMeta_ofAMeta (md : AMeta) : (XMeta.ofAMeta md).toAMeta = md := by
  cases md
  simp [XMeta.ofAMeta, XMeta.toAMeta, List.map_map, Function.comp_def]

/-- In metadata with every result plain, every kind found is plain. -/
theorem kindOf_ofAMeta (md : AMeta) (name : String) :
    (XMeta.ofAMeta md).kindOf name = none ∨ (XMeta.ofAMeta md).kindOf name = some .plain := by
  unfold XMeta.kindOf
  cases h : (XMeta.ofAMeta md).world.find? (·.asig.sig.name == name) with
  | none => exact .inl rfl
  | some a =>
    have ha : a ∈ (XMeta.ofAMeta md).world := List.mem_of_find?_eq_some h
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
    exact .inr rfl

variable (M : CoreInst)

/-- **With every result plain, the wrapper is `awrap`.** -/
theorem xcallExport_ofAMeta (md : AMeta) (name : String) (vs : List PVal) :
    xcallExport M (XMeta.ofAMeta md) name vs = (awrap md).callExport M name vs := by
  have hk := kindOf_ofAMeta md name
  unfold xcallExport
  rw [toAMeta_ofAMeta]
  split
  · next h _ => exact absurd h (by rcases hk with hk | hk <;> rw [hk] <;> simp)
  · next h _ => exact absurd h (by rcases hk with hk | hk <;> rw [hk] <;> simp)
  · rfl

/-- **An async function whose result is a stream** returns the readable end of `asyncCallS`. -/
theorem xcallExport_stream (md : XMeta) (name : String) (vs : List PVal) (l : Lift) (sty : Style)
    (hk : md.kindOf name = some .stream)
    (hl : (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) = some ⟨l, some sty⟩) :
    xcallExport M md name vs =
      (asyncCallS M ((awrap md.toAMeta).base.callRef M.withStore l.realloc)
        ((awrap md.toAMeta).base.callRef M.withStore l.callee) l.sig vs >>= fun h =>
          pure (handleRes h)) := by
  unfold xcallExport
  rw [hk, hl]

/-- **An async function whose result is a future** returns the readable end of `asyncCallF`. -/
theorem xcallExport_future (md : XMeta) (name : String) (vs : List PVal) (l : Lift) (sty : Style)
    (hk : md.kindOf name = some .future)
    (hl : (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) = some ⟨l, some sty⟩) :
    xcallExport M md name vs =
      (asyncCallF M ((awrap md.toAMeta).base.callRef M.withStore l.realloc)
        ((awrap md.toAMeta).base.callRef M.withStore l.callee) l.sig vs >>= fun h =>
          pure (handleRes h)) := by
  unfold xcallExport
  rw [hk, hl]

/-- The values of a call followed by `handleRes`. -/
theorem handle_bind_ok (m : RM M.withStore.St Nat) (s : M.withStore.St) (r : Option PVal)
    (s' : M.withStore.St) :
    (m >>= fun h => pure (handleRes h)) s (.ok r s') ↔ ∃ h, m s (.ok h s') ∧ r = handleRes h := by
  rw [RM.bind_apply]
  constructor
  · rintro (⟨h, s₁, hm, hp⟩ | ⟨-, he⟩)
    · have he : Out.ok r s' = Out.ok (handleRes h) s₁ := hp
      obtain ⟨hr, hs⟩ := Out.ok.inj he
      exact ⟨h, hs ▸ hm, hr⟩
    · cases he
  · rintro ⟨h, hm, rfl⟩
    exact .inl ⟨h, s', hm, rfl⟩

/-- The lift of the world function `name` in `awrap md`. -/
theorem find_awrap_some (md : AMeta) (name : String) (s : ASig)
    (hs : md.world.find? (·.sig.name == name) = some s) :
    ∃ i, md.world[i]? = some s ∧ (awrap md).lifts.find? (·.lift.sig.name == name) =
      some ⟨⟨s.sig, .adapt (0 + i + 1), .adapt 0⟩, s.async⟩ := by
  have hd : (awrap md).lifts = (liftsFrom 0 (md.world.map (·.sig))).zipWith
      (fun l s => (⟨l, s.async⟩ : ALift)) md.world := rfl
  rw [hd]
  cases h : ((liftsFrom 0 (md.world.map (·.sig))).zipWith
      (fun l s => (⟨l, s.async⟩ : ALift)) md.world).find? (·.lift.sig.name == name) with
  | none =>
    have hn : md.world.find? (·.sig.name == name) = none :=
      Silmaril.Proofs.Wasm.Jco.Async.find_awrap_none name 0 md.world h
    exact absurd (hn.symm.trans hs) (by simp)
  | some al =>
    obtain ⟨i, s', hi, hf, e⟩ := Silmaril.Proofs.Wasm.Jco.Async.find_awrap name 0 md.world al h
    have hss : s' = s := Option.some.inj (hf.symm.trans hs)
    exact ⟨i, hss ▸ hi, by rw [e, hss]⟩

/-- One lift of `awrap md` over `M.withStore` is the lifted C convention over `M`. -/
theorem awrap_canon (md : AMeta) (hC : md.sync.Conforms M) (i : Nat) (s : ASig)
    (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCall M.withStore ((awrap md).base.callRef M.withStore (.adapt 0))
        ((awrap md).base.callRef M.withStore (.adapt (0 + i + 1))) s.sig vs =
      RM.liftFst (md.sync.specCall M s.sig vs) := by
  have hi' : md.sync.world[i]? = some s.sig := by simp [AMeta.sync, hi]
  rw [Silmaril.Proofs.Wasm.Jco.Async.base_awrap, Nat.zero_add]
  exact (canonCall_wrap M.withStore md.sync
    (Silmaril.Proofs.Wasm.Jco.Async.conforms_withStore M md.sync hC) i s.sig hi' vs).trans
    (specCall_withStore M md.sync s.sig vs)

/-- A call returning a handle `n`, characterised, followed by `handleRes`. -/
theorem handle_ok_iff (m : RM M.withStore.St Nat) (P : Option PVal → M.St → List Val → Prop)
    (n : Nat) (Q : M.St → M.withStore.St) (s : M.withStore.St)
    (hm : ∀ h s', m s (.ok h s') ↔ ∃ v x ws, P v x ws ∧ h = n ∧ s' = Q x) (r : Option PVal)
    (s' : M.withStore.St) :
    (m >>= fun h => pure (handleRes h)) s (.ok r s') ↔
      ∃ v x ws, P v x ws ∧ r = handleRes n ∧ s' = Q x := by
  rw [handle_bind_ok]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨v, x, ws, hp, rfl, hs⟩ := (hm h s').1 hh
    exact ⟨v, x, ws, hp, rfl, hs⟩
  · rintro ⟨v, x, ws, hp, rfl, hs⟩
    exact ⟨n, (hm n s').2 ⟨v, x, ws, hp, rfl, hs⟩, rfl⟩

/-- **The caller of a stream-result export of the wrapper gets the readable end**, and `M` ran
its C convention. -/
theorem xcallExport_stream_ok (md : XMeta) (hC : md.toAMeta.sync.Conforms M) (name : String)
    (vs : List PVal) (s : ASig) (sty : Style)
    (hs : md.toAMeta.world.find? (·.sig.name == name) = some s) (hsty : s.async = some sty)
    (hk : md.kindOf name = some .stream) (σ : M.withStore.St) (hU : Unused σ.2)
    (hb : σ.2.next + 1 < 2 ^ 32) (r : Option PVal) (σ' : M.withStore.St) :
    xcallExport M md name vs σ (.ok r σ') ↔
      ∃ v x ws, (md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧ resVals v = some ws) ∧
        r = handleRes (σ.2.next + 1) ∧ σ' = (x, sB σ.2) := by
  obtain ⟨i, hi, hl⟩ := find_awrap_some md.toAMeta name s hs
  have hl' : (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) =
      some ⟨⟨s.sig, .adapt (0 + i + 1), .adapt 0⟩, some sty⟩ := hsty ▸ hl
  have hc := awrap_canon M md.toAMeta hC i s hi vs
  rw [xcallExport_stream M md name vs _ sty hk hl']
  exact handle_ok_iff M _ (fun v x ws => md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧
    resVals v = some ws) _ (fun x => (x, sB σ.2)) σ
    (fun h σ'' => by simpa only [and_assoc] using asyncCallS_ok M _ _ s.sig vs _ hc σ hU hb h σ'')
    r σ'

/-- **The caller of a future-result export of the wrapper gets the readable end**, and `M` ran
its C convention. -/
theorem xcallExport_future_ok (md : XMeta) (hC : md.toAMeta.sync.Conforms M) (name : String)
    (vs : List PVal) (s : ASig) (sty : Style)
    (hs : md.toAMeta.world.find? (·.sig.name == name) = some s) (hsty : s.async = some sty)
    (hk : md.kindOf name = some .future) (σ : M.withStore.St) (hU : Unused σ.2)
    (hb : σ.2.next + 1 < 2 ^ 32) (r : Option PVal) (σ' : M.withStore.St) :
    xcallExport M md name vs σ (.ok r σ') ↔
      ∃ v x ws, (md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧ resVals v = some ws) ∧
        r = handleRes (σ.2.next + 1) ∧ σ' = (x, fB σ.2) := by
  obtain ⟨i, hi, hl⟩ := find_awrap_some md.toAMeta name s hs
  have hl' : (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) =
      some ⟨⟨s.sig, .adapt (0 + i + 1), .adapt 0⟩, some sty⟩ := hsty ▸ hl
  have hc := awrap_canon M md.toAMeta hC i s hi vs
  rw [xcallExport_future M md name vs _ sty hk hl']
  exact handle_ok_iff M _ (fun v x ws => md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧
    resVals v = some ws) _ (fun x => (x, fB σ.2)) σ
    (fun h σ'' => by simpa only [and_assoc] using asyncCallF_ok M _ _ s.sig vs _ hc σ hU hb h σ'')
    r σ'

end Silmaril.Proofs.Wasm.Jco.Async.XWorld
