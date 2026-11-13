module

public import Silmaril.Proofs.Wasm.Jco.Styles.Wide.Lift

/-!
# Wide results: the canonical lift after the shim's stores

* `fieldWrites_sep`: the writes of a record's fields are separated;
* **`liftWide_after`**: after storing the fields of a wide result at `p`, the canonical lift
  from `p` (alignment and bounds checks, loads) is the same checks followed by the flat lift
  of the stored values. It needs a lawful memory.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val liftArgs)

theorem fieldWrites_mem (p : Nat) : ∀ (ts : List ValTy) (os ns : List Nat) (rs : List Flat)
    (w : Nat × List UInt8), w ∈ fieldWrites p ts os ns rs → ∃ o ∈ os, w.1 = p + o
  | t :: ts, o :: os, n :: ns, r :: rs, w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact ⟨o, List.mem_cons_self, rfl⟩
    · obtain ⟨o', ho', he⟩ := fieldWrites_mem p ts os ns rs w hw'
      exact ⟨o', List.mem_cons_of_mem _ ho', he⟩
  | [], _, _, _, _, hw | _ :: _, [], _, _, _, hw | _ :: _, _ :: _, [], _, _, hw
  | _ :: _, _ :: _, _ :: _, [], _, hw => by simp [fieldWrites] at hw

theorem fieldWrites_sep (p : Nat) : ∀ (off : Nat) (ns : List Nat), (∀ n ∈ ns, 0 < n) →
    ∀ (ts : List ValTy) (rs : List Flat), Sep (fieldWrites p ts (fieldOffs off ns) ns rs)
  | off, n :: ns, hp, t :: ts, r :: rs => by
    have hpos : ∀ m ∈ ns, 0 < m := fun m hm => hp m (List.mem_cons_of_mem _ hm)
    refine ⟨fun w hw => ?_, fieldWrites_sep p _ ns hpos ts rs⟩
    obtain ⟨o, ho, he⟩ := fieldWrites_mem p ts _ ns rs w hw
    have hge := fieldOffs_ge (alignUp off n + n) ns hpos o ho
    rw [he, leBytes_length]
    omega
  | _, [], _, _, _ | _, _ :: _, _, [], _ | _, _ :: _, _, _ :: _, [] => by
    simp [fieldOffs, fieldWrites, Sep]

theorem scalarSize_pos : ∀ {ts : List ValTy} {ns : List Nat}, ts.mapM scalarSize = some ns →
    ∀ n ∈ ns, 0 < n
  | [], ns, h, n, hn => by simp at h; subst h; simp at hn
  | t :: ts, ns, h, n, hn => by
    obtain ⟨m, hm, ns', hts, rfl⟩ := mapM_cons_some h
    rcases List.mem_cons.mp hn with rfl | hn'
    · cases t <;> simp [scalarSize] at hm <;> omega
    · exact scalarSize_pos hts n hn'

theorem fieldOffs_length : ∀ (off : Nat) (ns : List Nat), (fieldOffs off ns).length = ns.length
  | _, [] => rfl
  | off, n :: ns => by simp [fieldOffs, fieldOffs_length _ ns]

variable (M : CoreInst)

theorem check_at {b : Bool} {σ β : Type} {s : σ} {K K' : Unit → RM σ β} (h : K () s = K' () s) :
    (RM.check b >>= K) s = (RM.check b >>= K') s := by
  cases b
  · rw [check_false, RM.fail_bind, RM.fail_bind]
  · rw [check_true, RM.pure_bind, RM.pure_bind]
    exact h

/-- **The canonical lift after the stores is the flat lift.** -/
theorem liftWide_after (hL : MemLawful M) {ts : List ValTy} {ns : List Nat}
    (hn : ts.mapM scalarSize = some ns) {rs : List Flat}
    (hr : rs.map (·.type) = ValTy.flatList ts) (p : BitVec 32) :
    (storeAll M (fieldWrites p.toNat ts (fieldOffs 0 ns) ns rs) >>= fun _ => liftWide M ts ns p) =
      (storeAll M (fieldWrites p.toNat ts (fieldOffs 0 ns) ns rs) >>= fun _ => do
        RM.check (p.toNat % tupleAlign ns == 0)
        let s ← RM.get
        RM.check (decide (p.toNat + tupleSize ns ≤ (M.mem s).length))
        let v ← RM.ofOption (liftArgs ts rs)
        pure (some (.val (.record v)))) := by
  refine bind_congr_ok fun s u s' h => ?_
  have hw := storeAll_ok M hL _ s s' u h
  have hsep := fieldWrites_sep p.toNat 0 ns (scalarSize_pos hn) ts rs
  have hread := writeAll_read hw hsep
  have hl := loadFields_at M (s := s') p.toNat ts _ ns rs hn (fieldOffs_length 0 ns) hr hread
  unfold liftWide
  refine check_at ?_
  rw [bind_at (m := RM.get) (a := s') rfl, bind_at (m := RM.get) (a := s') rfl]
  refine check_at ?_
  exact bind_eq_at hl _

end Silmaril.Proofs.Wasm.Jco
