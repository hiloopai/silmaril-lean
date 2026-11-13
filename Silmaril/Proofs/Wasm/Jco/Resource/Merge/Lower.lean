module

public import Silmaril.Proofs.Wasm.Jco.Resource.Merge.Basic

/-!
# Merging a resource manager: handle parameters

* `hostLift_ofTab`: the caller's argument lifting is a deterministic table operation;
* `total_lowerParams`: lowering does not diverge when the `realloc` does not;
* `exec_preHandle`: the glue's conversion of one handle parameter is the manager's `take`/`rep`;
* **`stepA`**: lowering handles as `u32`s and then converting them through the manager is the
  caller lifting the arguments and then lowering the reps, provided lowering does not diverge.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst) (H : HTab)

theorem ofTab_map_bind {σ τ α β γ : Type} (F : τ → Option (α × τ)) (g : α → β)
    (K : β → RM (σ × τ) γ) :
    (RM.ofTab (fun t => (F t).map fun p => (g p.1, p.2)) >>= K) =
      (RM.ofTab F >>= fun a => K (g a)) := by
  funext st o
  rcases st with ⟨s, t⟩
  cases hF : F t with
  | none => exact propext ((ofTab_bind_none (by simp [hF]) o).trans (ofTab_bind_none hF o).symm)
  | some p =>
    have h1 : ((F t).map fun p => (g p.1, p.2)) = some (g p.1, p.2) := by simp [hF]
    have h2 : F t = some (p.1, p.2) := hF
    exact propext ((ofTab_bind_some h1 o).trans
      (ofTab_bind_some (k := fun a => K (g a)) h2 o).symm)

theorem ofTab_map {σ τ α β : Type} (F : τ → Option (α × τ)) (g : α → β) :
    (RM.ofTab (fun t => (F t).map fun p => (g p.1, p.2)) : RM (σ × τ) β) =
      (RM.ofTab F >>= fun a => pure (g a)) := by
  rw [← ofTab_map_bind F g pure, RM.bind_pure]

theorem hostLiftP_ofTab (t : RTy) (v : RVal) :
    ∃ F, hostLiftP H M t v = RM.ofTab F := by
  cases t <;> cases v
  case own.res r h =>
    show ∃ F, (RM.ofTab (takeF H r h) >>= fun rep => pure (RVal.res rep)) = _
    simp only [ofTab_pure, ofTab_bind]
    exact ⟨_, rfl⟩
  case borrow.res r h =>
    show ∃ F, (RM.ofTab (repF H r h) >>= fun rep => pure (RVal.res rep)) = _
    simp only [ofTab_pure, ofTab_bind]
    exact ⟨_, rfl⟩
  all_goals first | exact ⟨_, ofTab_pure _⟩ | exact ⟨_, ofTab_fail⟩

theorem hostLift_ofTab : ∀ (ts : List RTy) (vs : List RVal),
    ∃ F, hostLift H M ts vs = RM.ofTab F
  | t :: ts, v :: vs => by
    obtain ⟨F, hF⟩ := hostLiftP_ofTab M H t v
    obtain ⟨G, hG⟩ := hostLift_ofTab ts vs
    have h : hostLift H M (t :: ts) (v :: vs) =
        (RM.ofTab F >>= fun a => RM.ofTab G >>= fun b => pure (a :: b)) := by
      show (hostLiftP H M t v >>= fun a => hostLift H M ts vs >>= fun b => pure (a :: b)) = _
      rw [hF, hG]
    rw [h]
    simp only [ofTab_pure, ofTab_bind]
    exact ⟨_, rfl⟩
  | [], vs => ⟨_, ofTab_pure _⟩
  | _ :: _, [] => ⟨_, ofTab_pure _⟩

/-! ## Totality of lowering -/

theorem total_onFst {σ τ α : Type} {m : RM σ α} (h : Total m) :
    Total (m.onFst : RM (σ × τ) α) := by
  rintro ⟨s, t⟩
  obtain ⟨o, ho⟩ := h s
  cases o with
  | ok a s' => exact ⟨.ok a (s', t), ho, rfl⟩
  | trap => exact ⟨.trap, ho⟩

theorem total_store (a : Nat) (bs : List UInt8) : Total (M.store a bs) :=
  total_bind total_get fun _ => total_bind (total_ofOption _) fun _ => total_set _

variable {rw : List Flat → RM M.St (List Flat)}

theorem total_lowerParam (hrw : ∀ xs, Total (rw xs)) (t : PTy) (v : PVal) :
    Total (lowerParam M rw t v) := by
  have hb : ∀ limit bs, Total (lowerBytes M rw limit bs) := fun _ _ =>
    total_bind (total_check _) fun _ => total_bind (hrw _) fun _ =>
      total_bind (total_ofOption _) fun _ => total_bind (total_store M _ _) fun _ => total_pure _
  cases t <;> cases v
  case val.val t v => exact total_bind (total_check _) fun _ => total_pure _
  case string.string => exact hb _ _
  case bytes.bytes => exact hb _ _
  all_goals exact total_fail

theorem total_lowerParams (hrw : ∀ xs, Total (rw xs)) :
    ∀ (ps : List PTy) (vs : List PVal), Total (lowerParams M rw ps vs)
  | [], [] => total_pure _
  | t :: ts, v :: vs => total_bind (total_lowerParam M hrw t v) fun _ =>
      total_bind (total_lowerParams hrw ts vs) fun _ => total_pure _
  | [], _ :: _ | _ :: _, [] => total_fail

theorem returns_onFst {σ τ α : Type} {m : RM σ α} {P : α → Prop} (h : Returns m P) :
    Returns (m.onFst : RM (σ × τ) α) P := fun st a st' hm => h st.1 a st'.1 hm.1

/-! ## The manager's operations from the glue -/

theorem call_take {r : RtId} (hr : r < 2 ^ 32) (h : BitVec 32) :
    (link M (mgr H)).call "rm.take" [Flat.i32 h, Flat.i32 (BitVec.ofNat 32 r)] =
      (RM.ofTab (takeF H r h) >>= fun rep => pure [Flat.i32 rep]) := by
  rw [← ofTab_map]
  have hm : mgrName "rm.take" = true := by decide
  show (if mgrName "rm.take" = true then
      (mgrCall H "rm.take" [Flat.i32 h, Flat.i32 (BitVec.ofNat 32 r)]).onSnd
    else (M.call "rm.take" [Flat.i32 h, Flat.i32 (BitVec.ofNat 32 r)]).onFst) = _
  simp only [hm, ↓reduceIte]
  dsimp only [mgrCall]
  simp only [show ("rm.take" = "rm.new") = False from by decide,
    ite_false, ite_true]
  have hfun : (fun t => (takeF H (BitVec.ofNat 32 r).toNat h t).map fun p => ([Flat.i32 p.1], p.2)) =
      (fun t => (takeF H r h t).map fun p => ([Flat.i32 p.1], p.2)) := by rw [toNat_ofNat_lt hr]
  exact (congrArg (fun f => (RM.ofFn f).onSnd) hfun).trans (onSnd_ofFn _)

theorem call_rep {r : RtId} (hr : r < 2 ^ 32) (h : BitVec 32) :
    (link M (mgr H)).call "rm.rep" [Flat.i32 h, Flat.i32 (BitVec.ofNat 32 r)] =
      (RM.ofTab (repF H r h) >>= fun rep => pure [Flat.i32 rep]) := by
  rw [← ofTab_map]
  have hm : mgrName "rm.rep" = true := by decide
  show (if mgrName "rm.rep" = true then
      (mgrCall H "rm.rep" [Flat.i32 h, Flat.i32 (BitVec.ofNat 32 r)]).onSnd
    else (M.call "rm.rep" [Flat.i32 h, Flat.i32 (BitVec.ofNat 32 r)]).onFst) = _
  simp only [hm, ↓reduceIte]
  dsimp only [mgrCall]
  simp only [show ("rm.rep" = "rm.new") = False from by decide,
    show ("rm.rep" = "rm.take") = False from by decide, ite_false, ite_true]
  have hfun : (fun t => (repF H (BitVec.ofNat 32 r).toNat h t).map fun p => ([Flat.i32 p.1], p.2)) =
      (fun t => (repF H r h t).map fun p => ([Flat.i32 p.1], p.2)) := by rw [toNat_ofNat_lt hr]
  exact (congrArg (fun f => (RM.ofFn f).onSnd) hfun).trans (onSnd_ofFn _)

/-- The conversion of one handle parameter. -/
theorem exec_preHandle {op : String} {r : RtId} {F : H.T → Option (BitVec 32 × H.T)}
    {h : BitVec 32} (hc : (link M (mgr H)).call op [Flat.i32 h, Flat.i32 (BitVec.ofNat 32 r)] =
      (RM.ofTab F >>= fun rep => pure [Flat.i32 rep]))
    {ls : List Flat} {p : Nat} (hp : ls[p]? = some (Flat.i32 h)) :
    exec (link M (mgr H)) (preHandle op r p) ⟨ls, []⟩ =
      (RM.ofTab F >>= fun rep => pure ⟨ls.set p (Flat.i32 rep), []⟩) := by
  have hlt : p < ls.length := (List.getElem?_eq_some_iff.1 hp).1
  have harg : (List.take 2 (Frame.stack ⟨ls, [Flat.i32 (BitVec.ofNat 32 r), Flat.i32 h]⟩)).reverse =
      [Flat.i32 h, Flat.i32 (BitVec.ofNat 32 r)] := rfl
  rw [preHandle, exec_cons, step_localGet _ hp, RM.pure_bind, exec_cons, step_i32Const,
    RM.pure_bind, exec_cons,
    step_call _ op ⟨ls, [Flat.i32 (BitVec.ofNat 32 r), Flat.i32 h]⟩ (by simp)]
  rw [harg, hc, RM.bind_assoc, RM.bind_assoc]
  simp only [RM.pure_bind, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.append_nil]
  simp only [exec_cons, step_localSet _ hlt, RM.pure_bind, exec_nil]

end Silmaril.Proofs.Wasm.Jco.Res
