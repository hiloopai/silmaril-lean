module

public import Silmaril.Wasm.Component.Streams.AStore.Defs
public import Silmaril.Wasm.Component.Streams.ACancel.Thms

/-!
# Asynchronous cancellation: the store

* `astep_ofD`, `atakeEv_ofD`, `await_ofD`: on a `Drop` store embedded with no flags and no
  futures (`ofD`), the stream built-ins and the waits of `ACancel` are `Cancel.cstep`'s and
  `Drop`'s (a `join` of a future handle aside, which a `Drop` store has none of).
* `astep_cancelRead_blocked`, `astep_cancelWrite_blocked`: a `BLOCKED` cancel at the store comes
  from a host-owned peer, and leaves the end cancelling.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.ACancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event upd blocked)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Cancel
open Silmaril.Wasm.Component.Streams.ACancel

theorem upd_const {β : Type} (b : β) (k : Nat) : upd (fun _ => b) k b = fun _ => b := by
  funext j
  simp only [upd]
  split <;> rfl

theorem ofD_chan (st : DStore) (s : Nat) : (ofD st).chan s = ⟨st.chans s, {}⟩ := rfl

theorem ofD_setChan (st : DStore) (s : Nat) (c : DChan) :
    (ofD st).setChan s ⟨c, {}⟩ = ofD (st.setChan s c) := by
  simp only [ofD, AStore.setChan, upd_const]

theorem ofD_remove (st : DStore) (h : Nat) : (ofD st).remove h = ofD (st.remove h) := rfl

theorem read_ofD (c : DChan) (n : Nat) :
    (AChan.read ⟨c, {}⟩ n) = (c.zread n).map fun p => (⟨p.1, {}⟩, p.2) := rfl

theorem write_ofD (c : DChan) (xs : List Val) :
    (AChan.write ⟨c, {}⟩ xs) = (c.zwrite xs).map fun p => (⟨p.1, {}⟩, p.2) := rfl

theorem onR_ofD {st : DStore} {r : Nat} {g : DChan → Option (DChan × Res)}
    {f : AChan → Option (AChan × Res)}
    (hf : ∀ c, f ⟨c, {}⟩ = (g c).map fun (p : DChan × Res) => ((⟨p.1, {}⟩ : AChan), p.2)) :
    onR (ofD st) r f = (match st.tbl r with
      | some (.streamR s) => (g (st.chans s)).map fun (p : DChan × Res) => (st.setChan s p.1, p.2)
      | _ => none).map fun (p : DStore × Res) => (ofD p.1, p.2) := by
  unfold onR
  simp only [ofD_chan]
  have ht : (ofD st).d.tbl r = st.tbl r := rfl
  rw [ht]
  cases hh : st.tbl r with
  | none => rfl
  | some ob =>
    cases ob
    case streamR s =>
      simp only [hf, Option.map_map]
      congr 1
      funext p
      simp only [Function.comp, ofD_setChan]
    all_goals rfl

theorem onW_ofD {st : DStore} {w : Nat} {g : DChan → Option (DChan × Res)}
    {f : AChan → Option (AChan × Res)}
    (hf : ∀ c, f ⟨c, {}⟩ = (g c).map fun (p : DChan × Res) => ((⟨p.1, {}⟩ : AChan), p.2)) :
    onW (ofD st) w f = (match st.tbl w with
      | some (.streamW s) => (g (st.chans s)).map fun (p : DChan × Res) => (st.setChan s p.1, p.2)
      | _ => none).map fun (p : DStore × Res) => (ofD p.1, p.2) := by
  unfold onW
  simp only [ofD_chan]
  have ht : (ofD st).d.tbl w = st.tbl w := rfl
  rw [ht]
  cases hh : st.tbl w with
  | none => rfl
  | some ob =>
    cases ob
    case streamW s =>
      simp only [hf, Option.map_map]
      congr 1
      funext p
      simp only [Function.comp, ofD_setChan]
    all_goals rfl

/-- A drop on a component-owned channel: the flags stay empty. -/
theorem dropR_ofD (c : DChan) :
    (AChan.dropR ⟨c, {}⟩).map (fun a' => (a', Res.unit)) =
      (c.dropR.map fun c' => (c', Res.unit)).map fun p => (⟨p.1, {}⟩, p.2) := by
  simp only [AChan.dropR, Option.map_map]
  rfl

theorem dropW_ofD (c : DChan) :
    (AChan.dropW ⟨c, {}⟩).map (fun a' => (a', Res.unit)) =
      (c.dropW.map fun c' => (c', Res.unit)).map fun p => (⟨p.1, {}⟩, p.2) := by
  simp only [AChan.dropW, Option.map_map]
  rfl

theorem astep_ofD_write (st : DStore) (w : Nat) (xs : List Val) :
    astep (ofD st) (.streamWrite w xs) = (cstep st (.op (.streamWrite w xs))).map fun p => (ofD p.1, p.2) := by
  simp only [astep, cstep]
  rw [onW_ofD (g := fun c => c.zwrite xs) (fun c => write_ofD c xs)]
  cases st.tbl w with
  | none => rfl
  | some ob => cases ob <;> rfl

theorem astep_ofD_read (st : DStore) (r n : Nat) :
    astep (ofD st) (.streamRead r n) = (cstep st (.op (.streamRead r n))).map fun p => (ofD p.1, p.2) := by
  simp only [astep, cstep]
  rw [onR_ofD (g := fun c => c.zread n) (fun c => read_ofD c n)]
  cases st.tbl r with
  | none => rfl
  | some ob => cases ob <;> rfl

theorem astep_ofD_dropR (st : DStore) (r : Nat) :
    astep (ofD st) (.streamDropR r) = (cstep st (.op (.streamDropR r))).map fun p => (ofD p.1, p.2) := by
  simp only [astep, cstep, dstep]
  rw [onR_ofD (g := fun c => c.dropR.map fun c' => (c', Res.unit)) dropR_ofD]
  cases st.tbl r with
  | none => rfl
  | some ob => cases ob <;> simp [Option.map_map, Function.comp_def, ofD_remove]

theorem astep_ofD_dropW (st : DStore) (w : Nat) :
    astep (ofD st) (.streamDropW w) = (cstep st (.op (.streamDropW w))).map fun p => (ofD p.1, p.2) := by
  simp only [astep, cstep, dstep]
  rw [onW_ofD (g := fun c => c.dropW.map fun c' => (c', Res.unit)) dropW_ofD]
  cases st.tbl w with
  | none => rfl
  | some ob => cases ob <;> simp [Option.map_map, Function.comp_def, ofD_remove]

theorem astep_ofD_join {st : DStore} (hNF : NoFut st) (h s : Nat) :
    astep (ofD st) (.join h s) = (cstep st (.op (.join h s))).map fun p => (ofD p.1, p.2) := by
  simp only [astep, cstep, dstep, ofD]
  have hn := hNF h
  cases hh : st.tbl h with
  | none => rfl
  | some ob =>
    cases ob with
    | futureR f => exact absurd hh (hn f).1
    | futureW f => exact absurd hh (hn f).2
    | streamR _ => by_cases hs : st.tbl s = some .wset <;> simp [hs]
    | streamW _ => by_cases hs : st.tbl s = some .wset <;> simp [hs]
    | subtask _ => rfl
    | wset => rfl

/-- **Conservativity of the stream built-ins**: on an embedded `Drop` store, every stream
built-in of this variant is `Cancel.cstep`'s (which, for nonzero copies, is `Drop.dstep`'s). -/
theorem astep_ofD {st : DStore} (hNF : NoFut st) (o : DOp) :
    astep (ofD st) (liftD o) = (cstep st (.op o)).map fun p => (ofD p.1, p.2) := by
  cases o with
  | streamNew => simp only [liftD, astep, cstep, dstep, Option.map_some, ofD, upd_const]
  | streamWrite w xs => exact astep_ofD_write st w xs
  | streamRead r n => exact astep_ofD_read st r n
  | streamDropR r => exact astep_ofD_dropR st r
  | streamDropW w => exact astep_ofD_dropW st w
  | wsNew => rfl
  | join h s => exact astep_ofD_join hNF h s

/-- The cancels on an embedded `Drop` store are `Cancel`'s. -/
theorem astep_ofD_cancelRead (st : DStore) (r : Nat) (now : Bool) :
    astep (ofD st) (.cancelRead r now) = (cstep st (.cancelRead r)).map fun p => (ofD p.1, p.2) := by
  simp only [astep, cstep]
  rw [onR_ofD (g := fun c => c.cancelR) (fun c => cancelR_comp_eq c now)]
  cases st.tbl r with
  | none => rfl
  | some ob => cases ob <;> rfl
where
  cancelR_comp_eq (c : DChan) (now : Bool) :
      AChan.cancelR ⟨c, {}⟩ now = (c.cancelR).map fun p => (⟨p.1, {}⟩, p.2) := by
    unfold AChan.cancelR DChan.cancelR AChan.startCancelR AChan.takeR
    by_cases hg : c.r.gone = true ∨ c.r.st ≠ .copying
    · rcases hg with hg | hg <;> simp [hg]
    · have hg' : c.r.gone = false ∧ c.r.st = .copying := by simpa [not_or] using hg
      cases he : c.r.ev <;> simp [hg'.1, hg'.2]

theorem astep_ofD_cancelWrite (st : DStore) (w : Nat) (now : Bool) :
    astep (ofD st) (.cancelWrite w now) = (cstep st (.cancelWrite w)).map fun p => (ofD p.1, p.2) := by
  simp only [astep, cstep]
  rw [onW_ofD (g := fun c => c.cancelW) (fun c => cancelW_comp_eq c now)]
  cases st.tbl w with
  | none => rfl
  | some ob => cases ob <;> rfl
where
  cancelW_comp_eq (c : DChan) (now : Bool) :
      AChan.cancelW ⟨c, {}⟩ now = (c.cancelW).map fun p => (⟨p.1, {}⟩, p.2) := by
    unfold AChan.cancelW DChan.cancelW AChan.startCancelW AChan.takeW
    by_cases hg : c.w.gone = true ∨ c.w.st ≠ .copying
    · rcases hg with hg | hg <;> simp [hg]
    · have hg' : c.w.gone = false ∧ c.w.st = .copying := by simpa [not_or] using hg
      cases he : c.w.ev <;> simp [hg'.1, hg'.2]

theorem atakeEv_ofD_r (st : DStore) (h s : Nat) :
    ((ofD st).chan s).takeR.map (fun p => ((ofD st).setChan s p.1, (⟨.streamRead, h, p.2.1, p.2.2⟩ : Event))) =
      ((st.chans s).takeR.map fun p => (st.setChan s p.1, (⟨.streamRead, h, p.2.1, p.2.2⟩ : Event))).map
        fun p => (ofD p.1, p.2) := by
  simp only [ofD_chan, AChan.takeR, DChan.takeR]
  cases (st.chans s).r.ev with
  | none => rfl
  | some p => simp only [Option.map_some, ← ofD_setChan]; rfl

theorem atakeEv_ofD_w (st : DStore) (h s : Nat) :
    ((ofD st).chan s).takeW.map (fun p => ((ofD st).setChan s p.1, (⟨.streamWrite, h, p.2, []⟩ : Event))) =
      ((st.chans s).takeW.map fun p => (st.setChan s p.1, (⟨.streamWrite, h, p.2, []⟩ : Event))).map
        fun p => (ofD p.1, p.2) := by
  simp only [ofD_chan, AChan.takeW, DChan.takeW]
  cases (st.chans s).w.ev with
  | none => rfl
  | some p => simp only [Option.map_some, ← ofD_setChan]; rfl

/-- **Event delivery** on an embedded `Drop` store is `Drop`'s. -/
theorem atakeEv_ofD (st : DStore) (h : Nat) :
    atakeEv (ofD st) h = (takeEv st h).map fun p => (ofD p.1, p.2) := by
  unfold atakeEv takeEv
  have ht : (ofD st).d.tbl h = st.tbl h := rfl
  rw [ht]
  cases st.tbl h with
  | none => rfl
  | some ob =>
    cases ob with
    | streamR s => exact atakeEv_ofD_r st h s
    | streamW s => exact atakeEv_ofD_w st h s
    | futureR s => rfl
    | futureW s => rfl
    | subtask _ => rfl
    | wset => rfl

/-- **`waitable-set.wait`** on an embedded `Drop` store is `Drop`'s. -/
theorem await_ofD {st : DStore} {s h : Nat} {st' : AStore} {e : Event} :
    AWait (ofD st) s h st' e ↔ ∃ st'', DWait st s h st'' e ∧ st' = ofD st'' := by
  unfold AWait DWait
  rw [atakeEv_ofD]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h3
    exact ⟨q.1, ⟨h1, h2, by rw [hq, ← (Prod.mk.inj he).2]⟩, (Prod.mk.inj he).1.symm⟩
  · rintro ⟨st'', ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨h1, h2, by rw [h3]; rfl⟩

theorem setChan_chan (st : AStore) (s : Nat) (a : AChan) : (st.setChan s a).chan s = a := by
  simp [AStore.setChan, AStore.chan, DStore.setChan, upd]

/-- **A `BLOCKED` cancel at the store** comes from a host-owned writer and the host's choice,
and leaves the end cancelling. -/
theorem astep_cancelRead_blocked {st st' : AStore} {r : Nat} {now : Bool}
    (h : astep st (.cancelRead r now) = some (st', .nat blocked)) :
    ∃ s, st.d.tbl r = some (.streamR s) ∧ (st.sf s).hostW = true ∧ now = false ∧
      (st'.chan s).rstate = .cancelling := by
  simp only [astep, onR] at h
  split at h
  · rename_i s hs
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    have hq' : (st.chan s).cancelR now = some (q.1, .nat blocked) := by
      rw [hq, ← (Prod.mk.inj he).2]
    obtain ⟨h1, h2, -, h4⟩ := cancelR_blocked_only hq'
    refine ⟨s, hs, h1, h2, ?_⟩
    rw [← (Prod.mk.inj he).1, setChan_chan]
    exact h4
  · cases h

end Silmaril.Proofs.Wasm.Component.Streams.ACancel
