module

public import Silmaril.Proofs.Wasm.Jco.Resource.Lift

/-!
# The monadic construction with resources: proofs

* `callRef_reallocR`, `callRef_shimR`: the adaptor functions of `wrapR md`;
* `canonCallR_wrapR`, `specCall_eq`: both sides as a chain of phases;
* **`sim_liftR`**: the lift of world function `i` simulates `md.specCall`;
* `find_liftsFromR`, **`wrapR_sim`**: the component's exports are the world's functions.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst) (H : HTab) (md : MetaR)

theorem callRef_reallocR :
    (wrapR md).callRef M H (.adapt 0) =
      fun xs => ((wrap md.erase).callRef M (.adapt 0) xs).onFst := by
  funext xs
  simp only [RComp.callRef, wrapR, adaptorR, List.getElem?_cons_zero, RFn.run, execR_nil,
    RM.pure_bind, List.isEmpty_nil, RM.check_true, run_withTab, List.reverse_reverse,
    RM.bind_pure, Comp.callRef, wrap, adaptorOf]
  rfl

theorem callRef_shimR (i : Nat) (s : RSig) (hi : md.world[i]? = some s) :
    (wrapR md).callRef M H (.adapt (i + 1)) = (shimR md s).run M H := by
  funext xs
  simp [RComp.callRef, wrapR, adaptorR, hi]

/-- The component side of one lift, as phases. -/
theorem canonCallR_wrapR (i : Nat) (s : RSig) (hi : md.world[i]? = some s) (vs : List RVal) :
    canonCallR M H ((wrapR md).callRef M H (.adapt 0)) ((wrapR md).callRef M H (.adapt (i + 1)))
        s vs =
      (lowerParamsR M H (fun xs => ((wrap md.erase).callRef M (.adapt 0) xs).onFst) s.params vs
        >>= fun xs => execR M H (prologue 0 s.params) ⟨xs, []⟩ >>= fun f =>
          RM.check f.stack.isEmpty >>= fun _ =>
            ((exportShim md.erase s.erase).run M f.locals).onFst >>= fun rs =>
              postC M H s.result rs) := by
  rw [callRef_reallocR, callRef_shimR M H md i s hi]
  simp only [canonCallR, RFn.run, shimR, run_withTab, postC, RM.bind_assoc]

/-- The convention's side of one world function, as phases. -/
theorem specCall_eq (hC : md.erase.Conforms M) (i : Nat) (s : RSig)
    (hi : md.world[i]? = some s) (vs : List RVal) :
    md.specCall M s vs =
      (lowerParams M ((wrap md.erase).callRef M (.adapt 0)) (s.params.map RTy.erase)
        (eraseVals s.params vs) >>= fun ys => (exportShim md.erase s.erase).run M ys >>= fun rs =>
          liftResult M (s.result.map RTy.erase) rs >>= fun r =>
            if resultOk s.result then pure (unerase s.result r) else RM.fail) := by
  have hi' : md.erase.world[i]? = some s.erase := by simp [MetaR.erase, hi]
  rw [MetaR.specCall, ← canonCall_wrap M md.erase hC i s.erase hi',
    Silmaril.Proofs.Wasm.Jco.callRef_shim M md.erase i _ hi']
  simp only [canonCall, RM.bind_assoc]
  rfl

/-- **One lift of the wrapper** simulates the rep-passing convention's call. -/
theorem sim_liftR (hH : H.Lawful) (hC : md.erase.Conforms M) (i : Nat) (s : RSig)
    (hi : md.world[i]? = some s) (vs : List RVal) {t : H.T} (hI : H.Inv t)
    (hR : H.Room t (ownCount s.params + ownRes s.result)) :
    Sim (canonCallR M H ((wrapR md).callRef M H (.adapt 0))
        ((wrapR md).callRef M H (.adapt (i + 1))) s vs) (md.specCall M s vs) t
      fun a b t' => a = b ∧ H.Same t t' := by
  rw [canonCallR_wrapR M H md i s hi, specCall_eq M md hC i s hi]
  have hRl : H.Room t (ownCount s.params) := room_mono hR (Nat.le_add_right _ _)
  have hRr : H.Room t (ownRes s.result) := room_mono hR (Nat.le_add_left _ _)
  refine sim_bind (sim_lowerParamsR M hH _ s.params vs hI hRl) fun xs ys t1 hL => ?_
  obtain ⟨L, hM, hE⟩ := hL
  obtain ⟨tf, hEf, hd⟩ := prologue_det M hH hM [] hE
  refine sim_det_bind (fun st => hd st) ?_
  show Sim (RM.check true >>= fun _ => ((exportShim md.erase s.erase).run M ys).onFst >>= fun rs =>
    postC M H s.result rs) _ tf _
  rw [RM.check_true, RM.pure_bind]
  refine sim_bind (sim_onFst _ tf) fun rs rs' t' hab => ?_
  rw [hab.1, hab.2]
  exact sim_epilogue M hH s.result (ext_same hEf) hRr rs'

/-- Looking up an export of the lifts of `ws`, numbered from `k`. -/
theorem find_liftsFromR (name : String) : ∀ (k : Nat) (ws : List RSig),
    (∀ s, ws.find? (·.name == name) = some s → ∃ i, ws[i]? = some s ∧
      (liftsFromR k ws).find? (·.sig.name == name) = some ⟨s, .adapt (k + i + 1), .adapt 0⟩) ∧
    (ws.find? (·.name == name) = none → (liftsFromR k ws).find? (·.sig.name == name) = none)
  | _, [] => ⟨fun _ h => by simp at h, fun _ => rfl⟩
  | k, w :: ws => by
    by_cases hw : (w.name == name) = true
    · have hs0 : ∀ s, (w :: ws).find? (·.name == name) = some s → w = s := by
        intro s hs
        simpa [List.find?_cons, hw] using hs
      have hl0 : (liftsFromR k (w :: ws)).find? (·.sig.name == name) =
          some ⟨w, .adapt (k + 0 + 1), .adapt 0⟩ := by
        simp [liftsFromR, hw]
      refine ⟨fun s hs => ⟨0, ?_, ?_⟩, fun hn => absurd hn (by simp [hw])⟩
      · rw [← hs0 s hs]
        rfl
      · rw [← hs0 s hs, hl0]
    · have hw' : (w.name == name) = false := by simpa using hw
      have ih := find_liftsFromR name (k + 1) ws
      refine ⟨fun s hs => ?_, fun hn => ?_⟩
      · have hs' : ws.find? (·.name == name) = some s := by simpa [List.find?_cons, hw'] using hs
        obtain ⟨i, hi, hl⟩ := ih.1 s hs'
        refine ⟨i + 1, by simpa using hi, ?_⟩
        have hidx : k + 1 + i + 1 = k + (i + 1) + 1 := by omega
        simpa [liftsFromR, List.find?_cons, hw', hidx] using hl
      · have hn' : ws.find? (·.name == name) = none := by simpa [List.find?_cons, hw'] using hn
        simpa [liftsFromR, List.find?_cons, hw'] using ih.2 hn'

/-- **The behaviour theorem with resources.** -/
theorem wrapR_sim (hH : H.Lawful) (hC : md.erase.Conforms M) (name : String) (vs : List RVal)
    {t : H.T} (hI : H.Inv t) (hR : md.Room H t name) :
    Sim ((wrapR md).callExport M H name vs) (md.spec M name vs) t
      fun a b t' => a = b ∧ H.Same t t' := by
  have hl : (wrapR md).lifts = liftsFromR 0 md.world := rfl
  unfold RComp.callExport MetaR.spec
  rw [hl]
  cases hf : md.world.find? (·.name == name) with
  | none =>
    rw [(find_liftsFromR name 0 md.world).2 hf]
    exact sim_fail
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFromR name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx]
    exact sim_liftR M H md hH hC i s hi vs hI (hR s hf)

end Silmaril.Proofs.Wasm.Jco.Res
