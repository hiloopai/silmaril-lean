module

public import Silmaril.Proofs.Wasm.Jco.Async.Future

/-!
# The stream function's callee loop has one outcome: proofs

Part of `Silmaril.Wasm.Jco.Async.Future.Thms`: from `sE` (after the caller's read of
`Silmaril.Wasm.Jco.Async.Early`), the callback loop with `closeCb` has exactly one outcome, the
store `sF` (`stream_close_iff`).
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Future

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event Chan startSync step Waits upd packCopy
  CopyResult EventCode blocked)
open Silmaril.Proofs.Wasm.Jco.Async.Frame
open Silmaril.Proofs.Wasm.Jco.Async.Wait
open Silmaril.Proofs.Wasm.Jco.Async.Early

variable (M : CoreInst)

/-- The only wait from `sE` takes the writable end's event. -/
theorem sE_waits (st : Store) (hU : Unused st) (ws : List Val) (m : Nat) {h : Nat} {e : Event}
    {st' : Store} (hw : Waits (sE st ws m) (st.next + 3) h e st') :
    h = st.next + 2 ∧ e = ⟨.streamWrite, st.next + 2, packCopy .completed (min m ws.length), []⟩ ∧
      st' = sE' st ws m := by
  obtain ⟨-, hj, he, rfl⟩ := hw
  have hj' : (sD st ws).joined h = some (st.next + 3) := hj
  rw [sD_joined] at hj'
  split_ifs at hj' with hh
  · subst hh
    refine ⟨rfl, ?_, rfl⟩
    have : (sE st ws m).ev (st.next + 2) =
        some ⟨.streamWrite, st.next + 2, packCopy .completed (min m ws.length), []⟩ := by
      simp [sE, Store.post, upd]
    rw [this] at he
    cases he
    rfl
  · exact absurd hj' ((hU (st.next + 3) (by omega)).2.2.2.2 h)

/-- The stream's callback on the writable end's event drops it and answers `EXIT`. -/
theorem closeCb_eq (st : Store) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (ws : List Val) (m : Nat)
    (a c : Flat) (x : M.St) :
    closeCb M [a, i32n (st.next + 2), c] (x, sE' st ws m) =
      (pure [i32n cbExit] : RM M.withStore.St (List Flat)) (x, sF st ws m) := by
  have hw32 : (BitVec.ofNat 32 (st.next + 2)).toNat = st.next + 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htw : (sE' st ws m).tbl (st.next + 2) = some (.streamW (st.next + 1)) := by
    show (sD st ws).tbl (st.next + 2) = _
    rw [sD_tbl st ws _ (by omega), st₂_tbl]
    simp
  have hcw : (sE' st ws m).chans (st.next + 1) = { pend := .idle, sent := got ws m } := by
    simp [sE', sE, Store.setChan, Store.post, upd]
  have hdrop : step (sE' st ws m) (.streamDropW (st.next + 2)) = some (sF st ws m, .unit) := by
    simp only [step, Silmaril.Wasm.Component.Async.streamDropW, htw, hcw]
    rfl
  show (builtin M (.streamDropW (BitVec.ofNat 32 (st.next + 2)).toNat) >>= fun _ =>
    pure [i32n cbExit]) _ = _
  rw [hw32, builtin_then M hdrop _ x]

/-- **The stream callee's loop has exactly one outcome**: from `sE`, with `closeCb`, it ends at
`sF`. -/
theorem stream_close_iff (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (ws : List Val) (m : Nat) (x : M.St) (o : Out M.withStore.St Unit) :
    Drive M (closeCb M) (waitCode (st.next + 3)) (x, sE st ws m) o ↔
      o = .ok () (x, sF st ws m) := by
  refine ⟨fun h => ?_, fun h => h ▸ Early.stream_close M st hb ws m x⟩
  have ⟨hm, hd⟩ := code_toNat (st.next + 3) hb
  have hex : @Eq (RM M.withStore.St Unit) (Drive M (closeCb M) [i32n cbExit]) (pure ()) :=
    Silmaril.Proofs.Wasm.Jco.Async.drive_exit M _
  cases h with
  | exit _ hc => exact absurd (hm ▸ hc) (by decide)
  | yieldOk hc => exact absurd (hm ▸ hc) (by decide)
  | yieldTrap hc => exact absurd (hm ▸ hc) (by decide)
  | waitOk _ hw hcb hdr =>
    obtain ⟨rfl, rfl, rfl⟩ := sE_waits st hU ws m (hd ▸ hw)
    rw [closeCb_eq M st hb] at hcb
    cases hcb
    exact (RM.pure_apply _ _ _).1 (hex ▸ hdr)
  | waitTrap _ hw hcb =>
    obtain ⟨rfl, rfl, rfl⟩ := sE_waits st hU ws m (hd ▸ hw)
    rw [closeCb_eq M st hb] at hcb
    cases hcb
  | bad hb' => exact absurd ⟨_, rfl, by rw [hm]⟩ hb'

end Silmaril.Proofs.Wasm.Jco.Async.Future
