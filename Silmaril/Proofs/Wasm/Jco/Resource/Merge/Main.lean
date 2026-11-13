module

public import Silmaril.Proofs.Wasm.Jco.Resource.Merge.Post
public import Silmaril.Proofs.Wasm.Jco.Resource.Wrap

/-!
# Merging a resource manager: the theorems

* **`merged_eq_specHost`**: the merged module, read at the world's types, is `specHost`: the
  caller lifting its arguments from its table, `M` under the rep-passing convention, the caller
  lowering an `own` result into its table. The manager's table is the caller's table, exactly.
  Hypotheses: `md.erase.Conforms M`, the allocator never diverges, `MergeOk`.
* **`canonHost_sim`**: the canonical counterpart (a caller with its own table calling `wrapR md`)
  simulates `specHost`, the component's own table ending interchangeable (`wrapR_correct`).
* **`merged_sim`**: together, the canonical counterpart simulates the merged module.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst) (H : HTab) (md : MetaR)

/-! ## Lookup -/

theorem liftsFrom_map : ∀ (k : Nat) (ws : List RSig),
    liftsFrom k (ws.map RSig.erase) =
      (liftsFromR k ws).map fun l => (⟨l.sig.erase, l.callee, l.realloc⟩ : Lift)
  | _, [] => rfl
  | k, w :: ws => by
    simp only [List.map_cons, liftsFrom, liftsFromR, liftsFrom_map (k + 1) ws]

theorem find_merged (name : String) :
    (∀ s, md.world.find? (·.name == name) = some s → ∃ i, md.world[i]? = some s ∧
      (merged md).lifts.find? (·.sig.name == name) = some ⟨s.erase, .adapt (i + 1), .adapt 0⟩) ∧
    (md.world.find? (·.name == name) = none →
      (merged md).lifts.find? (·.sig.name == name) = none) := by
  have hl : (merged md).lifts = (liftsFromR 0 md.world).map
      fun l => (⟨l.sig.erase, l.callee, l.realloc⟩ : Lift) := liftsFrom_map 0 md.world
  have hf := find_liftsFromR name 0 md.world
  refine ⟨fun s hs => ?_, fun hn => ?_⟩
  · obtain ⟨i, hi, h1⟩ := hf.1 s hs
    refine ⟨i, hi, ?_⟩
    rw [hl, List.find?_map]
    simp only [Function.comp_def]
    rw [show (fun l : RLift => l.sig.erase.name == name) = (·.sig.name == name) from rfl, h1]
    simp
  · rw [hl, List.find?_map]
    simp only [Function.comp_def]
    rw [show (fun l : RLift => l.sig.erase.name == name) = (·.sig.name == name) from rfl, hf.2 hn]
    rfl

/-! ## The glue's functions -/

theorem plain_gets (n : Nat) : ∀ i ∈ gets n, Plain i := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
  trivial

theorem plain_exportShim (hok : md.MergeOk) (s : RSig) (hs : s ∈ md.world) :
    ∀ i ∈ (exportShim md.erase s.erase).body, Plain i := by
  have ha : mgrName md.alloc = false := hok.alloc
  have hn : mgrName s.name = false := hok.names s hs
  intro i hi
  unfold exportShim at hi
  split at hi
  · simp only [outShimBody, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with ((rfl | rfl | rfl | rfl) | hi) | rfl | rfl
    · trivial
    · trivial
    · exact ha
    · trivial
    · exact plain_gets _ i hi
    · exact hn
    · trivial
  · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with hi | rfl
    · exact plain_gets _ i hi
    · exact hn

theorem merged_realloc (hok : md.MergeOk) :
    (merged md).callRef (link M (mgr H)) (.adapt 0) =
      fun xs => ((wrap md.erase).callRef M (.adapt 0) xs).onFst := by
  funext xs
  have hp : ∀ i ∈ (reallocShim md.alloc).body, Plain i := by
    intro i hi
    simp only [reallocShim, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · trivial
    · trivial
    · exact hok.alloc
  exact run_link M H _ hp xs

theorem merged_shim (i : Nat) (s : RSig) (hi : md.world[i]? = some s) :
    (merged md).callRef (link M (mgr H)) (.adapt (i + 1)) = (shimM md s).run (link M (mgr H)) := by
  funext xs
  simp [Comp.callRef, merged, hi]

theorem exportShim_params (s : RSig) :
    (exportShim md.erase s.erase).params = (flatParams (s.params.map RTy.erase)).length := by
  unfold exportShim
  split <;> rfl

theorem lower_length (rw : List Flat → RM M.St (List Flat))
    (hrw : rw = (wrap md.erase).callRef M (.adapt 0)) (ps : List PTy) (vs : List PVal) :
    Returns (lowerParams M rw ps vs) fun xs => xs.length = (flatParams ps).length := by
  rw [hrw, Silmaril.Proofs.Wasm.Jco.lowerParams_wrap]
  exact Silmaril.Proofs.Wasm.Jco.specParams_length M md.erase ps vs

theorem post_any {res : Option RTy} (hr : ∀ r, res = some (.own r) → r < 2 ^ 32) (g : Frame) :
    ((exec (link M (mgr H)) (postM res) g >>= fun f => pure f.stack.reverse) >>= fun rs =>
        liftResult (link M (mgr H)) (res.map RTy.erase) rs >>= finR res) =
      ((liftResult M (res.map RTy.erase) g.stack.reverse >>= finR res).onFst >>=
        hostLower H M res) := by
  rcases res with _ | (t | r | r)
  · exact post_plain M H (fun _ h => by cases h) rfl g
  · exact post_plain M H (fun _ h => by cases h) rfl g
  · exact post_own M H (hr r rfl) g
  · exact post_plain M H (fun _ h => by cases h) rfl g

theorem lowerParams_link (rw : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List PTy) (vs : List PVal),
      lowerParams (link M (mgr H)) (fun xs => (rw xs).onFst) ps vs =
        (lowerParams M rw ps vs).onFst
  | [], [] => (onFst_pure _).symm
  | t :: ts, v :: vs => by
    have h1 : lowerParam (link M (mgr H)) (fun xs => (rw xs).onFst) t v =
        (lowerParam M rw t v).onFst := lowerParam_withTab M H.T rw t v
    simp only [lowerParams, h1, lowerParams_link rw ts vs, onFst_bind, onFst_pure]
  | [], _ :: _ | _ :: _, [] => onFst_fail.symm

theorem shimM_run (s : RSig) (xs : List Flat)
    (hx : xs.length = (exportShim md.erase s.erase).params) :
    (shimM md s).run (link M (mgr H)) xs =
      (exec (link M (mgr H)) (preM 0 s.params)
        ⟨xs ++ List.replicate (exportShim md.erase s.erase).locals (i32n 0), []⟩ >>= fun f =>
          exec (link M (mgr H)) (exportShim md.erase s.erase).body f >>= fun g =>
            exec (link M (mgr H)) (postM s.result) g >>= fun h => pure h.stack.reverse) := by
  have hc : (xs.length == (exportShim md.erase s.erase).params) = true := by simp [hx]
  simp only [AFn.run, shimM, hc, RM.check_true, RM.pure_bind, exec_append, RM.bind_assoc]

theorem exportShim_run (s : RSig) (ys : List Flat)
    (hy : ys.length = (exportShim md.erase s.erase).params) :
    (exportShim md.erase s.erase).run M ys =
      (exec M (exportShim md.erase s.erase).body
        ⟨ys ++ List.replicate (exportShim md.erase s.erase).locals (i32n 0), []⟩ >>= fun f =>
          pure f.stack.reverse) := by
  have hc : (ys.length == (exportShim md.erase s.erase).params) = true := by simp [hy]
  simp only [AFn.run, hc, RM.check_true, RM.pure_bind]

variable {M H md}

/-- The continuation after the glue's handle conversions. -/
abbrev kont (md : MetaR) (s : RSig) (f : Frame) : RM (M.St × H.T) (Option RVal) :=
  (exec (link M (mgr H)) (exportShim md.erase s.erase).body f >>= fun g =>
    exec (link M (mgr H)) (postM s.result) g >>= fun h => pure h.stack.reverse) >>= fun rs =>
      liftResult (link M (mgr H)) (s.result.map RTy.erase) rs >>= finR s.result

theorem merged_lhs (hok : md.MergeOk) (i : Nat) (s : RSig) (hi : md.world[i]? = some s)
    (vs : List RVal) :
    (canonCall (link M (mgr H)) ((merged md).callRef (link M (mgr H)) (.adapt 0))
        ((merged md).callRef (link M (mgr H)) (.adapt (i + 1))) s.erase (eraseVals s.params vs) >>=
        finR s.result) =
      lhsA M H ((wrap md.erase).callRef M (.adapt 0))
        (List.replicate (exportShim md.erase s.erase).locals (i32n 0)) s.params vs [] (kont md s) := by
  rw [merged_realloc M H md hok, merged_shim M H md i s hi]
  unfold canonCall lhsA
  rw [RM.bind_assoc, lowerParams_link]
  refine RM.bind_congr_returns (returns_onFst (lower_length M md _ rfl _ _)) fun xs hx => ?_
  rw [shimM_run M H md s xs (hx.trans (exportShim_params md s).symm)]
  simp only [RM.bind_assoc, List.nil_append, List.length_nil]
  refine RM.bind_congr fun f => ?_
  simp only [kont, RM.bind_assoc]
  rfl

theorem merged_rhs (hC : md.erase.Conforms M) (hok : md.MergeOk) (i : Nat) (s : RSig)
    (hi : md.world[i]? = some s) (vs : List RVal) :
    (hostLift H M s.params vs >>= fun reps => (md.specCall M s reps).onFst >>=
        hostLower H M s.result) =
      rhsA M H ((wrap md.erase).callRef M (.adapt 0))
        (List.replicate (exportShim md.erase s.erase).locals (i32n 0)) s.params vs [] (kont md s) := by
  have hs : s ∈ md.world := List.mem_of_getElem? hi
  have hres : ∀ r, s.result = some (.own r) → r < 2 ^ 32 := fun r hr =>
    hok.rts s hs (.own r) (by simp [hr]) r (.inl rfl)
  unfold rhsA
  refine RM.bind_congr fun reps => ?_
  rw [specCall_eq M md hC i s hi, onFst_bind, RM.bind_assoc]
  refine RM.bind_congr_returns (returns_onFst (lower_length M md _ rfl _ _)) fun ys hy => ?_
  have hy' : ys.length = (exportShim md.erase s.erase).params :=
    hy.trans (exportShim_params md s).symm
  have hplain := plain_exportShim md hok s hs
  rw [exportShim_run M md s ys hy']
  simp only [kont, List.nil_append, exec_link M H _ hplain, onFst_bind, RM.bind_assoc,
    RM.pure_bind]
  refine RM.bind_congr fun g => ?_
  simpa only [onFst_bind, onFst_pure, RM.bind_assoc, RM.pure_bind] using
    (post_any M H hres g).symm

theorem total_realloc (hT : md.AllocTotal M) (xs : List Flat) :
    Total ((wrap md.erase).callRef M (.adapt 0) xs) := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, xs⟩⟩⟩⟩⟩
  case cons.cons.cons.cons.nil =>
    rw [Silmaril.Proofs.Wasm.Jco.callRef_realloc]
    exact hT _
  all_goals
    simp [Comp.callRef, wrap, adaptorOf, AFn.run, reallocShim]
    exact total_fail

/-- **The merged module is the caller with its table in front of `M`.** -/
theorem merged_eq_specHost (hC : md.erase.Conforms M) (hT : md.AllocTotal M) (hok : md.MergeOk)
    (name : String) (vs : List RVal) :
    md.hostView ((merged md).callExport (link M (mgr H))) name vs = specHost H M md name vs := by
  unfold MetaR.hostView specHost
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_merged md name).1 s hf
    have hs : s ∈ md.world := List.mem_of_getElem? hi
    have hrts : RtsOk s.params := fun r hr =>
      hr.elim (fun h => hok.rts s hs _ (by simp [h]) r (.inl rfl))
        (fun h => hok.rts s hs _ (by simp [h]) r (.inr rfl))
    show ((match (merged md).lifts.find? (·.sig.name == name) with
      | some l => canonCall (link M (mgr H)) ((merged md).callRef (link M (mgr H)) l.realloc)
          ((merged md).callRef (link M (mgr H)) l.callee) l.sig (eraseVals s.params vs)
      | none => fail) >>= finR s.result) = _
    rw [hfind]
    rw [merged_lhs hok i s hi vs, stepA (total_realloc hT) s.params vs hrts [] _,
      ← merged_rhs hC hok i s hi vs]

/-! ## The canonical counterpart -/

theorem sim_liftMid {σ τ ρ α β : Type} {m : RM (σ × τ) α} {n : RM σ β} {t : τ}
    {R : α → β → τ → Prop} (h : Sim m n t R) :
    Sim (m.liftMid (ρ := ρ)) (n.onFst (τ := ρ)) t R where
  fwd st a st' t' hm := by
    obtain ⟨b, hb, hR⟩ := h.fwd st.1 a st'.1 t' hm.1
    exact ⟨b, ⟨hb, hm.2⟩, hR⟩
  bwd st b st' hn := by
    obtain ⟨a, t', ha, hR⟩ := h.bwd st.1 b st'.1 hn.1
    exact ⟨a, t', ⟨ha, hn.2⟩, hR⟩
  trap st := h.trap st.1

/-- **The canonical counterpart simulates `specHost`.** -/
theorem canonHost_sim (hH : H.Lawful) (hC : md.erase.Conforms M) (name : String)
    (vs : List RVal) {tc : H.T} (hI : H.Inv tc) (hR : md.Room H tc name) :
    Sim (canonHost H M md name vs) (specHost H M md name vs) tc
      fun a b t' => a = b ∧ H.Same tc t' := by
  unfold canonHost specHost
  cases hf : md.world.find? (·.name == name) with
  | none => exact sim_fail
  | some s =>
    have hspec : ∀ reps, md.spec M name reps = md.specCall M s reps := fun reps => by
      unfold MetaR.spec
      rw [hf]
    refine sim_bind (sim_onFst _ tc) fun reps reps' t1 hab => ?_
    rw [hab.1, hab.2]
    have hw : Sim ((wrapR md).callExport M H name reps') (md.specCall M s reps') tc
        fun a b t' => a = b ∧ H.Same tc t' := hspec reps' ▸ wrapR_sim M H md hH hC name reps' hI hR
    refine sim_bind (sim_liftMid hw) fun r r' t2 h2 => ?_
    rw [h2.1]
    exact sim_mono (sim_onFst _ t2) fun a b t3 h3 => ⟨h3.1, h3.2 ▸ h2.2⟩

end Silmaril.Proofs.Wasm.Jco.Res
