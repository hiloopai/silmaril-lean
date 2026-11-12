module

public import Silmaril.Wasm.Jco.Async.SyncStream.Defs
public import Silmaril.Wasm.Jco.Async.XWorld.Thms

/-!
# Synchronous functions with stream or future results: proofs

Proofs of `Silmaril.Wasm.Jco.Async.SyncStream.Thms`. From a store `st` whose channel `st.next` is
fresh, the readable end is `st.next` (also the channel) and the writable end `st.next + 1`.

* `yS`: after `stream.new` and the pending `stream.write`; `syncStreamCall_ok`: the caller gets
  the readable end there. `yR`: after the caller's read (`syncStream_read`); `yR2`: after a
  second read, which is pending (`syncStream_read_again`).
* `zS`, `zR`: the same for a future (`syncFutureCall_ok`, `syncFuture_read`); a second read traps
  (`syncFuture_read_again`).
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.SyncStream

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store step upd packCopy CopyResult blocked)
open Silmaril.Proofs.Wasm.Jco.Async.Frame
open Silmaril.Proofs.Wasm.Jco.Async.Wait

/-! ## The stores -/

section Stores

variable (st : Store) (ws : List Val) (y : Val)

/-- After `stream.new`. -/
@[expose] def y₁ : Store := (st.alloc2 .streamR .streamW).1

/-- After the pending `stream.write`: the store when the caller has the readable end. -/
@[expose] def yS : Store := (y₁ st).setChan st.next { pend := .write (st.next + 1) ws }

/-- After the caller's `stream.read r m`. -/
@[expose] def yR (m : Nat) : Store :=
  ((yS st ws).setChan st.next { pend := .idle, sent := ws.take (min m ws.length) }).post
    (st.next + 1) ⟨.streamWrite, st.next + 1, packCopy .completed (min m ws.length), []⟩

/-- After a second read, pending. -/
@[expose] def yR2 (m m' : Nat) : Store :=
  (yR st ws m).setChan st.next { pend := .read st.next m', sent := ws.take (min m ws.length) }

/-- After `future.new`. -/
@[expose] def z₁ : Store := (st.alloc2 .futureR .futureW).1

/-- After the pending `future.write`. -/
@[expose] def zS : Store := (z₁ st).setChan st.next { pend := .write (st.next + 1) [y] }

/-- After the caller's `future.read r`. -/
@[expose] def zR : Store :=
  ((zS st y).setChan st.next { pend := .idle, done := true, sent := [y] }).post (st.next + 1)
    ⟨.futureWrite, st.next + 1, CopyResult.completed.toNat, []⟩

end Stores

theorem step_newS (st : Store) : step st .streamNew = some (y₁ st, .ends st.next (st.next + 1)) :=
  rfl

theorem step_writeS (st : Store) (ws : List Val) (hf : st.chans st.next = {}) :
    step (y₁ st) (.streamWrite (st.next + 1) ws) = some (yS st ws, .nat blocked) := by
  simp [step, Silmaril.Wasm.Component.Async.streamWrite, y₁, yS, Store.alloc2, upd, hf]

theorem step_newF (st : Store) : step st .futureNew = some (z₁ st, .ends st.next (st.next + 1)) :=
  rfl

theorem step_writeF (st : Store) (y : Val) (hf : st.chans st.next = {}) :
    step (z₁ st) (.futureWrite (st.next + 1) y) = some (zS st y, .nat blocked) := by
  simp [step, Silmaril.Wasm.Component.Async.futureWrite, z₁, zS, Store.alloc2, upd, hf]

/-- **The caller's read delivers the values.** -/
theorem syncStream_read (st : Store) (ws : List Val) (m : Nat) :
    step (yS st ws) (.streamRead st.next m) =
      some (yR st ws m, .read (packCopy .completed (min m ws.length)) (ws.take (min m ws.length))) := by
  simp [step, Silmaril.Wasm.Component.Async.streamRead, yS, yR, y₁, Store.alloc2, upd, Store.setChan]

/-- **A second read waits**: the writable end is never dropped. -/
theorem syncStream_read_again (st : Store) (ws : List Val) (m m' : Nat) :
    step (yR st ws m) (.streamRead st.next m') = some (yR2 st ws m m', .nat blocked) := by
  simp [step, Silmaril.Wasm.Component.Async.streamRead, yR2, yR, yS, y₁, Store.alloc2, upd,
    Store.setChan, Store.post]

/-- **The caller's read of the future delivers the value.** -/
theorem syncFuture_read (st : Store) (y : Val) :
    step (zS st y) (.futureRead st.next) = some (zR st y, .read CopyResult.completed.toNat [y]) := by
  simp [step, Silmaril.Wasm.Component.Async.futureRead, zS, zR, z₁, Store.alloc2, upd, Store.setChan]

/-- A second read of the future traps. -/
theorem syncFuture_read_again (st : Store) (y : Val) :
    step (zR st y) (.futureRead st.next) = none := by
  simp [step, Silmaril.Wasm.Component.Async.futureRead, zR, zS, z₁, Store.alloc2, upd,
    Store.setChan, Store.post]

variable (M : CoreInst)

/-- The synchronous stream function after `M` returned `v`. -/
@[expose] def streamTail (v : Option PVal) : RM M.withStore.St Nat :=
  RM.ofOption (resVals v) >>= fun ws => builtin M .streamNew >>= fun e =>
    match e with
    | .ends r w => builtin M (.streamWrite w ws) >>= fun _ => pure r
    | _ => RM.fail

/-- The synchronous future function after `M` returned the values `ws`. -/
@[expose] def futureOne (ws : List Val) : RM M.withStore.St Nat :=
  match ws with
  | [y] => builtin M .futureNew >>= fun e =>
    match e with
    | .ends r w => builtin M (.futureWrite w y) >>= fun _ => pure r
    | _ => RM.fail
  | _ => RM.fail

theorem syncStreamCall_eq (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) :
    syncStreamCall M R core sig vs = (canonCall M.withStore R core sig vs >>= streamTail M) := rfl

theorem syncFutureCall_eq (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) :
    syncFutureCall M R core sig vs =
      (canonCall M.withStore R core sig vs >>= fun v =>
        RM.ofOption (resVals v) >>= futureOne M) := rfl

theorem pure_ok_iff {a h : Nat} {s₀ s' : M.withStore.St} :
    (pure a : RM M.withStore.St Nat) s₀ (.ok h s') ↔ h = a ∧ s' = s₀ :=
  ⟨fun hk => Out.ok.inj (show Out.ok h s' = Out.ok a s₀ from hk),
    fun ⟨h1, h2⟩ => show Out.ok h s' = Out.ok a s₀ by rw [h1, h2]⟩

theorem fail_noOk {α : Type} (a : α) (s s' : M.withStore.St) :
    ¬ (RM.fail : RM M.withStore.St α) s (.ok a s') := nofun

/-- The tail of the stream function, as outcomes with a value. -/
theorem streamTail_ok (st : Store) (hf : st.chans st.next = {}) (v : Option PVal) (x : M.St)
    (h : Nat) (s' : M.withStore.St) :
    streamTail M v (x, st) (.ok h s') ↔
      ∃ ws, resVals v = some ws ∧ h = st.next ∧ s' = (x, yS st ws) := by
  cases hv : resVals v with
  | none =>
    have he : streamTail M v (x, st) = RM.fail (x, st) := by
      rw [streamTail, hv, RM.ofOption_none, RM.fail_bind]
      rfl
    rw [he]
    exact ⟨fun hk => (fail_noOk M h (x, st) s' hk).elim, fun ⟨_, hw, _⟩ => nomatch hw⟩
  | some ws =>
    have he : streamTail M v (x, st) = (pure st.next : RM M.withStore.St Nat) (x, yS st ws) := by
      rw [streamTail, hv, RM.ofOption_some, RM.pure_bind, builtin_then M (step_newS st)]
      exact builtin_then M (step_writeS st ws hf) _ x
    rw [he]
    exact (pure_ok_iff M).trans
      ⟨fun ⟨h1, h2⟩ => ⟨ws, rfl, h1, h2⟩, fun ⟨_, hw, h1, h2⟩ => ⟨h1, by cases hw; exact h2⟩⟩

/-- The tail of the future function, as outcomes with a value. -/
theorem futureOne_ok (st : Store) (hf : st.chans st.next = {}) (ws : List Val) (x : M.St)
    (h : Nat) (s' : M.withStore.St) :
    futureOne M ws (x, st) (.ok h s') ↔ ∃ y, ws = [y] ∧ h = st.next ∧ s' = (x, zS st y) := by
  match ws with
  | [] => exact ⟨fun hk => (fail_noOk M h (x, st) s' hk).elim, fun ⟨_, hw, _⟩ => nomatch hw⟩
  | _ :: _ :: _ =>
    exact ⟨fun hk => (fail_noOk M h (x, st) s' hk).elim, fun ⟨_, hw, _⟩ => nomatch hw⟩
  | [y] =>
    have he : futureOne M [y] (x, st) = (pure st.next : RM M.withStore.St Nat) (x, zS st y) := by
      rw [futureOne, builtin_then M (step_newF st)]
      exact builtin_then M (step_writeF st y hf) _ x
    rw [he]
    exact (pure_ok_iff M).trans
      ⟨fun ⟨h1, h2⟩ => ⟨y, rfl, h1, h2⟩, fun ⟨_, hw, h1, h2⟩ => ⟨h1, by cases hw; exact h2⟩⟩

/-- The future function after `M` returned `v`, as outcomes with a value. -/
theorem futureTail_ok (st : Store) (hf : st.chans st.next = {}) (v : Option PVal) (x : M.St)
    (h : Nat) (s' : M.withStore.St) :
    (RM.ofOption (resVals v) >>= futureOne M) (x, st) (.ok h s') ↔
      ∃ y, resVals v = some [y] ∧ h = st.next ∧ s' = (x, zS st y) := by
  cases hv : resVals v with
  | none =>
    rw [RM.ofOption_none, RM.fail_bind]
    exact ⟨fun hk => (fail_noOk M h (x, st) s' hk).elim, fun ⟨_, hw, _⟩ => nomatch hw⟩
  | some ws =>
    rw [RM.ofOption_some, RM.pure_bind, futureOne_ok M st hf ws x h s']
    exact ⟨fun ⟨y, hw, h1⟩ => ⟨y, hw ▸ rfl, h1⟩, fun ⟨y, hw, h1⟩ => ⟨y, Option.some.inj hw, h1⟩⟩

/-- **The caller of a synchronous stream function gets the readable end** at `yS`. -/
theorem syncStreamCall_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hf : s.2.chans s.2.next = {}) (h : Nat) (s' : M.withStore.St) :
    syncStreamCall M R core sig vs s (.ok h s') ↔
      ∃ v x ws, m₀ s.1 (.ok v x) ∧ resVals v = some ws ∧ h = s.2.next ∧ s' = (x, yS s.2 ws) := by
  unfold syncStreamCall
  rw [hc]
  refine (liftFst_bind_apply_ws M m₀ (streamTail M) s _).trans ?_
  constructor
  · rintro (⟨v, x, hm, hk⟩ | ⟨-, hk⟩)
    · obtain ⟨ws, hv, h1, h2⟩ := (streamTail_ok M s.2 hf v x h s').1 hk
      exact ⟨v, x, ws, hm, hv, h1, h2⟩
    · cases hk
  · rintro ⟨v, x, ws, hm, hv, h1, h2⟩
    exact .inl ⟨v, x, hm, (streamTail_ok M s.2 hf v x h s').2 ⟨ws, hv, h1, h2⟩⟩

/-- **The caller of a synchronous future function gets the readable end** at `zS`. -/
theorem syncFutureCall_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hf : s.2.chans s.2.next = {}) (h : Nat) (s' : M.withStore.St) :
    syncFutureCall M R core sig vs s (.ok h s') ↔
      ∃ v x y, m₀ s.1 (.ok v x) ∧ resVals v = some [y] ∧ h = s.2.next ∧ s' = (x, zS s.2 y) := by
  unfold syncFutureCall
  rw [hc]
  refine (liftFst_bind_apply_ws M m₀ (fun v => RM.ofOption (resVals v) >>= futureOne M) s _).trans ?_
  constructor
  · rintro (⟨v, x, hm, hk⟩ | ⟨-, hk⟩)
    · obtain ⟨y, hv, h1, h2⟩ := (futureTail_ok M s.2 hf v x h s').1 hk
      exact ⟨v, x, y, hm, hv, h1, h2⟩
    · cases hk
  · rintro ⟨v, x, y, hm, hv, h1, h2⟩
    exact .inl ⟨v, x, hm, (futureTail_ok M s.2 hf v x h s').2 ⟨y, hv, h1, h2⟩⟩


/-! ## The wrapper -/

open Silmaril.Proofs.Wasm.Jco.Async.XWorld (kindOf_ofAMeta find_awrap_some awrap_canon handle_bind_ok)

/-- With every result plain, the new wrapper is `xcallExport`. -/
theorem xcallExportS_ofAMeta (md : AMeta) (name : String) (vs : List PVal) :
    xcallExportS M (XMeta.ofAMeta md) name vs = xcallExport M (XMeta.ofAMeta md) name vs := by
  have hk := kindOf_ofAMeta md name
  unfold xcallExportS
  split
  · next h _ => exact absurd h (by rcases hk with hk | hk <;> rw [hk] <;> simp)
  · next h _ => exact absurd h (by rcases hk with hk | hk <;> rw [hk] <;> simp)
  · rfl

/-- An async function: the new wrapper is `xcallExport`. -/
theorem xcallExportS_async (md : XMeta) (name : String) (vs : List PVal) (l : Lift) (sty : Style)
    (hl : (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) = some ⟨l, some sty⟩) :
    xcallExportS M md name vs = xcallExport M md name vs := by
  unfold xcallExportS
  split
  · rename_i h; rw [hl] at h; cases h
  · rename_i h; rw [hl] at h; cases h
  · rfl

/-- **The caller of a synchronous stream-result export gets the readable end.** -/
theorem xcallExportS_stream_ok (md : XMeta) (hC : md.toAMeta.sync.Conforms M) (name : String)
    (vs : List PVal) (s : ASig) (hs : md.toAMeta.world.find? (·.sig.name == name) = some s)
    (hsty : s.async = none) (hk : md.kindOf name = some .stream) (σ : M.withStore.St)
    (hf : σ.2.chans σ.2.next = {}) (r : Option PVal) (σ' : M.withStore.St) :
    xcallExportS M md name vs σ (.ok r σ') ↔
      ∃ v x ws, (md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧ resVals v = some ws) ∧
        r = handleRes σ.2.next ∧ σ' = (x, yS σ.2 ws) := by
  obtain ⟨i, hi, hl⟩ := find_awrap_some md.toAMeta name s hs
  rw [hsty] at hl
  have hc := awrap_canon M md.toAMeta hC i s hi vs
  unfold xcallExportS
  rw [hk, hl]
  dsimp only
  rw [handle_bind_ok]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨v, x, ws, hm, hv, rfl, rfl⟩ := (syncStreamCall_ok M _ _ s.sig vs _ hc σ hf h σ').1 hh
    exact ⟨v, x, ws, ⟨hm, hv⟩, rfl, rfl⟩
  · rintro ⟨v, x, ws, ⟨hm, hv⟩, rfl, rfl⟩
    exact ⟨σ.2.next, (syncStreamCall_ok M _ _ s.sig vs _ hc σ hf _ _).2
      ⟨v, x, ws, hm, hv, rfl, rfl⟩, rfl⟩

/-- **The caller of a synchronous future-result export gets the readable end.** -/
theorem xcallExportS_future_ok (md : XMeta) (hC : md.toAMeta.sync.Conforms M) (name : String)
    (vs : List PVal) (s : ASig) (hs : md.toAMeta.world.find? (·.sig.name == name) = some s)
    (hsty : s.async = none) (hk : md.kindOf name = some .future) (σ : M.withStore.St)
    (hf : σ.2.chans σ.2.next = {}) (r : Option PVal) (σ' : M.withStore.St) :
    xcallExportS M md name vs σ (.ok r σ') ↔
      ∃ v x y, (md.toAMeta.sync.specCall M s.sig vs σ.1 (.ok v x) ∧ resVals v = some [y]) ∧
        r = handleRes σ.2.next ∧ σ' = (x, zS σ.2 y) := by
  obtain ⟨i, hi, hl⟩ := find_awrap_some md.toAMeta name s hs
  rw [hsty] at hl
  have hc := awrap_canon M md.toAMeta hC i s hi vs
  unfold xcallExportS
  rw [hk, hl]
  dsimp only
  rw [handle_bind_ok]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨v, x, y, hm, hv, rfl, rfl⟩ := (syncFutureCall_ok M _ _ s.sig vs _ hc σ hf h σ').1 hh
    exact ⟨v, x, y, ⟨hm, hv⟩, rfl, rfl⟩
  · rintro ⟨v, x, y, ⟨hm, hv⟩, rfl, rfl⟩
    exact ⟨σ.2.next, (syncFutureCall_ok M _ _ s.sig vs _ hc σ hf _ _).2
      ⟨v, x, y, hm, hv, rfl, rfl⟩, rfl⟩

/-! ## From WIT -/

theorem ofWitS_of_ofWit (f : Silmaril.Wasm.Wit.Binary.Func) (x : XSig) (h : XSig.ofWit f = .ok x) :
    XSig.ofWitS f = .ok x := by
  simp [XSig.ofWitS, h]

theorem mapM_ofWitS (l : List Silmaril.Wasm.Wit.Binary.WorldItem) (r : List XSig)
    (h : l.mapM xexportSig = .ok r) : l.mapM xexportSigS = .ok r := by
  induction l generalizing r with
  | nil => simpa using h
  | cons a l ih =>
    cases ha : xexportSig a with
    | error e => simp [List.mapM_cons, ha] at h; cases h
    | ok x =>
      have ha' : xexportSigS a = .ok x := by
        cases a with
        | func f => exact ofWitS_of_ofWit f x ha
        | _ => cases ha
      cases hl : l.mapM xexportSig with
      | error e => simp [List.mapM_cons, ha, hl] at h; cases h
      | ok xs =>
        simp [List.mapM_cons, ha, hl] at h
        simp [List.mapM_cons, ha', ih xs hl, h]

/-- On every world `XMeta.ofWorld` reads, the new reader gives the same metadata. -/
theorem ofWorldS_of_ofWorld (w : Silmaril.Wasm.Wit.Binary.World) (alloc : String) (md : XMeta)
    (h : XMeta.ofWorld w alloc = .ok md) : XMeta.ofWorldS w alloc = .ok md := by
  unfold XMeta.ofWorld at h
  unfold XMeta.ofWorldS
  cases hi : w.imports.isEmpty with
  | false => simp [hi] at h; cases h
  | true =>
    cases hl : w.exports.mapM xexportSig with
    | error e => simp [hi, hl] at h
    | ok ss =>
      simp [hi, hl] at h
      simp [mapM_ofWitS _ ss hl, h]

end Silmaril.Proofs.Wasm.Jco.Async.SyncStream
