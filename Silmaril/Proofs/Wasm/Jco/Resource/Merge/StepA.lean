module

public import Silmaril.Proofs.Wasm.Jco.Resource.Merge.Lower

/-!
# Merging a resource manager: lowering, then converting handles

**`stepA`**: in the merged module, lowering handles as `u32`s and then converting them to reps
through the manager (`preM`) is, as a relation, the caller lifting its arguments from its table
(`hostLift`) and then lowering the reps, provided `realloc` never diverges. The table operations
are the same in the same order; they commute with the lowering of the other parameters
(`comm_ofTab`), which is where totality is needed: the caller lifts all arguments before the
callee runs, the merged module converts after lowering.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst) (H : HTab) (rw : List Flat → RM M.St (List Flat)) (z : List Flat)

/-- The resource types of the parameters fit in an `i32`. -/
def RtsOk (ps : List RTy) : Prop := ∀ r, (RTy.own r ∈ ps ∨ RTy.borrow r ∈ ps) → r < 2 ^ 32

theorem rtsOk_tail {p : RTy} {ps : List RTy} (h : RtsOk (p :: ps)) : RtsOk ps :=
  fun r hr => h r (hr.imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _))

/-- The merged module's side. -/
def lhsA {β : Type} (ps : List RTy) (vs : List RVal) (pre : List Flat)
    (K : Frame → RM (M.St × H.T) β) : RM (M.St × H.T) β :=
  (lowerParams M rw (ps.map RTy.erase) (eraseVals ps vs)).onFst >>= fun xs =>
    exec (link M (mgr H)) (preM pre.length ps) ⟨pre ++ xs ++ z, []⟩ >>= K

/-- The caller's side. -/
def rhsA {β : Type} (ps : List RTy) (vs : List RVal) (pre : List Flat)
    (K : Frame → RM (M.St × H.T) β) : RM (M.St × H.T) β :=
  hostLift H M ps vs >>= fun reps =>
    (lowerParams M rw (ps.map RTy.erase) (eraseVals ps reps)).onFst >>= fun ys =>
      K ⟨pre ++ ys ++ z, []⟩

theorem hostLift_base (t : PTy) (v : RVal) (ts : List RTy) (vs : List RVal) :
    hostLift H M (.base t :: ts) (v :: vs) = (hostLift H M ts vs >>= fun b => pure (v :: b)) := by
  show (hostLiftP H M (.base t) v >>= fun a => hostLift H M ts vs >>= fun b => pure (a :: b)) = _
  cases v <;> exact RM.pure_bind _ _

theorem lowerParams_cons (t : RTy) (ts : List RTy) (v : RVal) (vs : List RVal) :
    lowerParams M rw ((t :: ts).map RTy.erase) (eraseVals (t :: ts) (v :: vs)) =
      (lowerParam M rw t.erase (eraseVal t v) >>= fun a =>
        lowerParams M rw (ts.map RTy.erase) (eraseVals ts vs) >>= fun b => pure (a ++ b)) := rfl

theorem append_set (pre rest : List Flat) (x y : Flat) :
    (pre ++ x :: rest).set pre.length y = (pre ++ [y]) ++ rest := by
  simp

variable {M H rw z}

theorem stepA_base_lhs {β : Type} (t : PTy) (v : RVal) (ts : List RTy)
    (vs : List RVal) (ih : ∀ pre (K : Frame → RM (M.St × H.T) β),
      lhsA M H rw z ts vs pre K = rhsA M H rw z ts vs pre K) (pre : List Flat)
    (K : Frame → RM (M.St × H.T) β) :
    lhsA M H rw z (.base t :: ts) (v :: vs) pre K =
      ((lowerParam M rw t (eraseVal (.base t) v)).onFst >>= fun a =>
        rhsA M H rw z ts vs (pre ++ a) K) := by
  unfold lhsA
  rw [lowerParams_cons, onFst_bind, RM.bind_assoc]
  refine RM.bind_congr_returns (returns_onFst (lowerParam_length M rw t _)) fun a ha => ?_
  have hlen : pre.length + t.flat.length = (pre ++ a).length := by simp [ha]
  rw [← ih (pre ++ a) K, lhsA, onFst_bind, RM.bind_assoc]
  refine RM.bind_congr fun b => ?_
  simp only [onFst_pure, RM.pure_bind, List.append_assoc]
  rw [show preM pre.length (.base t :: ts) = preM (pre.length + t.flat.length) ts from rfl, hlen]

theorem stepA_base_rhs {β : Type} {F : H.T → Option (List RVal × H.T)} (t : PTy) (v : RVal)
    (ts : List RTy) (vs : List RVal) (hF : hostLift H M ts vs = RM.ofTab F) (pre : List Flat)
    (K : Frame → RM (M.St × H.T) β) :
    rhsA M H rw z (.base t :: ts) (v :: vs) pre K =
      (RM.ofTab F >>= fun reps => (lowerParam M rw t (eraseVal (.base t) v)).onFst >>= fun a =>
        (lowerParams M rw (ts.map RTy.erase) (eraseVals ts reps)).onFst >>= fun ys =>
          K ⟨(pre ++ a) ++ ys ++ z, []⟩) := by
  unfold rhsA
  rw [hostLift_base, hF, RM.bind_assoc]
  refine RM.bind_congr fun b => ?_
  rw [RM.pure_bind, lowerParams_cons, onFst_bind, RM.bind_assoc]
  refine RM.bind_congr fun a => ?_
  rw [onFst_bind, RM.bind_assoc]
  refine RM.bind_congr fun c => ?_
  simp only [onFst_pure, RM.pure_bind, List.append_assoc]

/-- The case of a parameter of the first fragment. -/
theorem stepA_base {β : Type} (hrw : ∀ xs, Total (rw xs)) (t : PTy) (v : RVal) (ts : List RTy)
    (vs : List RVal) (ih : ∀ pre (K : Frame → RM (M.St × H.T) β),
      lhsA M H rw z ts vs pre K = rhsA M H rw z ts vs pre K) (pre : List Flat)
    (K : Frame → RM (M.St × H.T) β) :
    lhsA M H rw z (.base t :: ts) (v :: vs) pre K = rhsA M H rw z (.base t :: ts) (v :: vs) pre K := by
  obtain ⟨F, hF⟩ := hostLift_ofTab M H ts vs
  have hLP : Total (lowerParam M rw t (eraseVal (.base t) v)) := total_lowerParam M hrw _ _
  rw [stepA_base_lhs t v ts vs ih pre K, stepA_base_rhs t v ts vs hF pre K]
  unfold rhsA
  rw [hF]
  exact comm_ofTab hLP F _

theorem stepA_handle_lhs {β : Type} (hrw : ∀ xs, Total (rw xs)) {p : RTy} {op : String}
    {r : RtId} {F : BitVec 32 → H.T → Option (BitVec 32 × H.T)}
    (hp : ∀ n ts, preM n (p :: ts) = preHandle op r n ++ preM (n + 1) ts)
    (he : p.erase = .val .u32) (hev : ∀ x, eraseVal p (.res x) = .val (.u32 x))
    (hc : ∀ x, (link M (mgr H)).call op [Flat.i32 x, Flat.i32 (BitVec.ofNat 32 r)] =
      (RM.ofTab (F x) >>= fun rep => pure [Flat.i32 rep]))
    (h : BitVec 32) (ts : List RTy) (vs : List RVal) (pre : List Flat)
    (K : Frame → RM (M.St × H.T) β) :
    lhsA M H rw z (p :: ts) (.res h :: vs) pre K =
      (RM.ofTab (F h) >>= fun rep => lhsA M H rw z ts vs (pre ++ [Flat.i32 rep]) K) := by
  unfold lhsA
  refine Eq.trans ?_ (comm_ofTab (total_lowerParams M hrw _ _) (F h) _)
  rw [lowerParams_cons, he, hev, lowerParam_u32, RM.pure_bind, onFst_bind, RM.bind_assoc]
  refine RM.bind_congr fun b => ?_
  have hget : (pre ++ Flat.i32 h :: (b ++ z))[pre.length]? = some (Flat.i32 h) := by simp
  rw [onFst_pure, RM.pure_bind, hp, exec_append, RM.bind_assoc]
  rw [show pre ++ ([Flat.i32 h] ++ b) ++ z = pre ++ Flat.i32 h :: (b ++ z) by simp,
    exec_preHandle M H (hc h) hget, RM.bind_assoc]
  refine RM.bind_congr fun rep => ?_
  rw [RM.pure_bind, append_set]
  simp only [List.length_append, List.length_singleton, List.append_assoc]

theorem stepA_handle_rhs {β : Type} {p : RTy} {F : BitVec 32 → H.T → Option (BitVec 32 × H.T)}
    (he : p.erase = .val .u32) (hev : ∀ x, eraseVal p (.res x) = .val (.u32 x))
    (hlift : ∀ x, hostLiftP H M p (.res x) = (RM.ofTab (F x) >>= fun rep => pure (RVal.res rep)))
    (h : BitVec 32) (ts : List RTy) (vs : List RVal) (pre : List Flat)
    (K : Frame → RM (M.St × H.T) β) :
    rhsA M H rw z (p :: ts) (.res h :: vs) pre K =
      (RM.ofTab (F h) >>= fun rep => rhsA M H rw z ts vs (pre ++ [Flat.i32 rep]) K) := by
  unfold rhsA
  rw [show hostLift H M (p :: ts) (.res h :: vs) = (hostLiftP H M p (.res h) >>= fun a =>
    hostLift H M ts vs >>= fun b => pure (a :: b)) from rfl, hlift, RM.bind_assoc, RM.bind_assoc]
  refine RM.bind_congr fun rep => ?_
  rw [RM.pure_bind, RM.bind_assoc]
  refine RM.bind_congr fun b => ?_
  rw [RM.pure_bind, lowerParams_cons, he, hev, lowerParam_u32, RM.pure_bind, onFst_bind,
    RM.bind_assoc]
  refine RM.bind_congr fun ys => ?_
  simp only [onFst_pure, RM.pure_bind, List.append_assoc, List.singleton_append]

/-- The case of a handle parameter, converted by the manager's `op` (`take` or `rep`). -/
theorem stepA_handle {β : Type} (hrw : ∀ xs, Total (rw xs)) {p : RTy} {op : String} {r : RtId}
    {F : BitVec 32 → H.T → Option (BitVec 32 × H.T)}
    (hp : ∀ n ts, preM n (p :: ts) = preHandle op r n ++ preM (n + 1) ts)
    (he : p.erase = .val .u32) (hev : ∀ x, eraseVal p (.res x) = .val (.u32 x))
    (hlift : ∀ x, hostLiftP H M p (.res x) = (RM.ofTab (F x) >>= fun rep => pure (RVal.res rep)))
    (hc : ∀ x, (link M (mgr H)).call op [Flat.i32 x, Flat.i32 (BitVec.ofNat 32 r)] =
      (RM.ofTab (F x) >>= fun rep => pure [Flat.i32 rep]))
    (h : BitVec 32) (ts : List RTy) (vs : List RVal) (ih : ∀ pre (K : Frame → RM (M.St × H.T) β),
      lhsA M H rw z ts vs pre K = rhsA M H rw z ts vs pre K) (pre : List Flat)
    (K : Frame → RM (M.St × H.T) β) :
    lhsA M H rw z (p :: ts) (.res h :: vs) pre K = rhsA M H rw z (p :: ts) (.res h :: vs) pre K := by
  rw [stepA_handle_lhs hrw hp he hev hc h ts vs pre K, stepA_handle_rhs he hev hlift h ts vs pre K]
  exact RM.bind_congr fun rep => ih _ K

theorem stepA_handle_base {β : Type} {p : RTy} (hp : ∀ t, p ≠ .base t) (v : PVal)
    (ts : List RTy) (vs : List RVal) (pre : List Flat) (K : Frame → RM (M.St × H.T) β) :
    lhsA M H rw z (p :: ts) (.base v :: vs) pre K = rhsA M H rw z (p :: ts) (.base v :: vs) pre K := by
  have hf : lowerParam M rw p.erase (eraseVal p (.base v)) = fail := by
    rcases p with _ | r | r
    · exact absurd rfl (hp _)
    · rfl
    · rfl
  have hl : hostLiftP H M p (.base v) = fail := by
    rcases p with _ | r | r
    · exact absurd rfl (hp _)
    · rfl
    · rfl
  unfold lhsA rhsA
  rw [lowerParams_cons, hf, RM.fail_bind, onFst_fail, RM.fail_bind]
  show fail = ((hostLiftP H M p (.base v) >>= fun a => hostLift H M ts vs >>= fun b =>
    pure (a :: b)) >>= _)
  rw [hl, RM.fail_bind, RM.fail_bind]

theorem stepA_base_res {β : Type} (t : PTy) (x : BitVec 32) (ts : List RTy) (vs : List RVal)
    (pre : List Flat) (K : Frame → RM (M.St × H.T) β) :
    lhsA M H rw z (.base t :: ts) (.res x :: vs) pre K =
      rhsA M H rw z (.base t :: ts) (.res x :: vs) pre K := by
  obtain ⟨F, hF⟩ := hostLift_ofTab M H ts vs
  have hf : lowerParam M rw (RTy.base t).erase (eraseVal (.base t) (.res x)) = fail :=
    lowerParam_poison M rw t
  unfold lhsA rhsA
  rw [lowerParams_cons, hf, RM.fail_bind, onFst_fail, RM.fail_bind, hostLift_base, hF,
    RM.bind_assoc]
  have hk : ∀ b : List RVal, (pure (RVal.res x :: b) >>= fun reps =>
      (lowerParams M rw ((RTy.base t :: ts).map RTy.erase)
        (eraseVals (.base t :: ts) reps)).onFst >>= fun ys => K ⟨pre ++ ys ++ z, []⟩) =
      (fail : RM (M.St × H.T) β) := by
    intro b
    rw [RM.pure_bind, lowerParams_cons, hf, RM.fail_bind, onFst_fail, RM.fail_bind]
  rw [RM.bind_congr hk, ofTab_bind_fail]

/-- **Lowering, then converting handles through the manager, is lifting from the caller's table,
then lowering.** -/
theorem stepA {β : Type} (hrw : ∀ xs, Total (rw xs)) :
    ∀ (ps : List RTy) (vs : List RVal), RtsOk ps → ∀ (pre : List Flat)
      (K : Frame → RM (M.St × H.T) β), lhsA M H rw z ps vs pre K = rhsA M H rw z ps vs pre K
  | [], [], _, pre, K => by
    unfold lhsA rhsA
    simp only [List.map_nil, eraseVals, List.map_nil, lowerParams, onFst_pure, RM.pure_bind,
      preM, exec_nil, hostLift]
  | [], v :: vs, _, pre, K => by
    unfold lhsA rhsA
    simp only [List.map_nil, eraseVals, List.map_cons, lowerParams, onFst_fail, RM.fail_bind,
      hostLift, RM.pure_bind]
  | t :: ts, [], _, pre, K => by
    unfold lhsA rhsA
    simp only [List.map_cons, eraseVals, lowerParams, onFst_fail, RM.fail_bind, hostLift,
      RM.pure_bind]
  | .base t :: ts, v :: vs, hr, pre, K =>
    stepA_base hrw t v ts vs (stepA hrw ts vs (rtsOk_tail hr)) pre K
  | .own r :: ts, .res h :: vs, hr, pre, K =>
    stepA_handle (F := takeF H r) hrw (fun _ _ => rfl) rfl (fun _ => rfl) (fun _ => rfl)
      (call_take M H (hr r (.inl (List.mem_cons_self ..)))) h ts vs
      (stepA hrw ts vs (rtsOk_tail hr)) pre K
  | .borrow r :: ts, .res h :: vs, hr, pre, K =>
    stepA_handle (F := repF H r) hrw (fun _ _ => rfl) rfl (fun _ => rfl) (fun _ => rfl)
      (call_rep M H (hr r (.inr (List.mem_cons_self ..)))) h ts vs
      (stepA hrw ts vs (rtsOk_tail hr)) pre K
  | .own r :: ts, .base v :: vs, _, pre, K =>
    stepA_handle_base (fun _ h => by cases h) v ts vs pre K
  | .borrow r :: ts, .base v :: vs, _, pre, K =>
    stepA_handle_base (fun _ h => by cases h) v ts vs pre K

end Silmaril.Proofs.Wasm.Jco.Res
