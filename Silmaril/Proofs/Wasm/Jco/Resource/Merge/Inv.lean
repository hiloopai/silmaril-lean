module

public import Silmaril.Proofs.Wasm.Jco.Resource.Merge.Main

/-!
# Merging a resource manager: the manager keeps its invariant

`KeepsInv H m`: every returning run of `m` from a table satisfying `H.Inv` ends in one. The
caller's (equivalently, the manager's) table operations keep the invariant of a lawful table
(`keeps_takeF`, `keeps_repF`, `keeps_newF`), hence so do `specHost` and, by
`merged_eq_specHost`, the merged module (`keeps_merged`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM

variable {H : HTab}

/-- Every returning run from a table satisfying the invariant ends in one. -/
def KeepsInv (H : HTab) {σ α : Type} (m : RM (σ × H.T) α) : Prop :=
  ∀ s t a s' t', H.Inv t → m (s, t) (.ok a (s', t')) → H.Inv t'

theorem keeps_pure {σ α : Type} (a : α) : KeepsInv H (pure a : RM (σ × H.T) α) := by
  intro s t b s' t' hI h
  have he : t' = t := (Prod.mk.inj (Out.ok.inj h).2).2
  rw [he]
  exact hI

theorem keeps_fail {σ α : Type} : KeepsInv H (fail : RM (σ × H.T) α) := by
  intro _ _ _ _ _ _ h
  cases h

theorem keeps_bind {σ α β : Type} {m : RM (σ × H.T) α} {k : α → RM (σ × H.T) β}
    (hm : KeepsInv H m) (hk : ∀ a, KeepsInv H (k a)) : KeepsInv H (m >>= k) := by
  intro s t b s' t' hI h
  rcases h with ⟨a, ⟨s1, t1⟩, h1, h2⟩ | ⟨_, h⟩
  · exact hk a s1 t1 b s' t' (hm s t a s1 t1 hI h1) h2
  · cases h

theorem keeps_onFst {σ α : Type} (m : RM σ α) : KeepsInv H (m.onFst : RM (σ × H.T) α) := by
  intro s t a s' t' hI h
  have he : t' = t := h.2
  rw [he]
  exact hI

theorem keeps_ofTab {σ α : Type} {F : H.T → Option (α × H.T)}
    (hF : ∀ t a t', H.Inv t → F t = some (a, t') → H.Inv t') :
    KeepsInv H (RM.ofTab F : RM (σ × H.T) α) := by
  intro s t a s' t' hI h
  cases hFt : F t with
  | none =>
    have h' : Out.ok a (s', t') = .trap := (ofTab_apply_none hFt _).1 h
    cases h'
  | some p =>
    have h' : Out.ok a (s', t') = .ok p.1 (s, p.2) := (ofTab_apply_some hFt _).1 h
    have he : t' = p.2 := (Prod.mk.inj (Out.ok.inj h').2).2
    rw [he]
    exact hF t p.1 p.2 hI hFt

theorem keeps_newF (hH : H.Lawful) (r : RtId) (rep : BitVec 32) :
    ∀ t a t', H.Inv t → newF H r rep t = some (a, t') → H.Inv t' := by
  intro t a t' hI h
  obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 h
  have hp' : H.add? t ⟨r, rep⟩ = some (p.1, t') := by rw [hp, ← (Prod.mk.inj hpe).2]
  exact (hH.add_spec t _ _ _ hI hp').2.2.2.2.1

theorem keeps_takeF (hH : H.Lawful) (r : RtId) (h : BitVec 32) :
    ∀ t a t', H.Inv t → takeF H r h t = some (a, t') → H.Inv t' := by
  intro t a t' hI hT
  obtain ⟨p, hp, hpe⟩ := Option.bind_eq_some_iff.1 hT
  have ht : p.2 = t' := by
    by_cases hr : (p.1.rt == r) = true
    · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hpe
      exact hpe.2
    · simp [hr] at hpe
  rw [← ht]
  exact (hH.remove_spec t _ p.1 p.2 hI hp).2.2.2.1

theorem keeps_repF (hH : H.Lawful) (r : RtId) (h : BitVec 32) :
    ∀ t a t', H.Inv t → repF H r h t = some (a, t') → H.Inv t' := by
  intro t a t' hI hT
  obtain ⟨e, he, hpe⟩ := Option.bind_eq_some_iff.1 hT
  have ht : H.touch t h.toNat = t' := by
    by_cases hr : (e.rt == r) = true
    · simp only [hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hpe
      exact hpe.2
    · simp [hr] at hpe
  rw [← ht]
  exact (hH.touch_spec t _ e hI he).2.2

variable (M : CoreInst)

theorem keeps_hostLiftP (hH : H.Lawful) (t : RTy) (v : RVal) : KeepsInv H (hostLiftP H M t v) := by
  cases t <;> cases v
  case own.res r h =>
    exact keeps_bind (keeps_ofTab (keeps_takeF hH r h)) fun _ => keeps_pure _
  case borrow.res r h =>
    exact keeps_bind (keeps_ofTab (keeps_repF hH r h)) fun _ => keeps_pure _
  all_goals first | exact keeps_pure _ | exact keeps_fail

theorem keeps_hostLift (hH : H.Lawful) :
    ∀ (ts : List RTy) (vs : List RVal), KeepsInv H (hostLift H M ts vs)
  | t :: ts, v :: vs => keeps_bind (keeps_hostLiftP M hH t v) fun _ =>
      keeps_bind (keeps_hostLift hH ts vs) fun _ => keeps_pure _
  | [], _ => keeps_pure _
  | _ :: _, [] => keeps_pure _

theorem keeps_hostLower (hH : H.Lawful) (res : Option RTy) (v : Option RVal) :
    KeepsInv H (hostLower H M res v) := by
  rcases res with _ | (_ | r | _)
  · exact keeps_pure _
  · exact keeps_pure _
  · rcases v with _ | (_ | rep)
    · exact keeps_pure _
    · exact keeps_pure _
    · exact keeps_bind (keeps_ofTab (keeps_newF hH r rep)) fun _ => keeps_pure _
  · exact keeps_pure _

theorem keeps_specHost (hH : H.Lawful) (md : MetaR) (name : String) (vs : List RVal) :
    KeepsInv H (specHost H M md name vs) := by
  unfold specHost
  split
  · exact keeps_bind (keeps_hostLift M hH _ _) fun _ =>
      keeps_bind (keeps_onFst _) fun _ => keeps_hostLower M hH _ _
  · exact keeps_fail

/-- **The merged module keeps the manager's invariant.** -/
theorem keeps_merged (hH : H.Lawful) (md : MetaR) (hC : md.erase.Conforms M)
    (hT : md.AllocTotal M) (hok : md.MergeOk) (name : String) (vs : List RVal) :
    KeepsInv H (md.hostView ((merged md).callExport (link M (mgr H))) name vs) := by
  rw [merged_eq_specHost hC hT hok]
  exact keeps_specHost M hH md name vs

end Silmaril.Proofs.Wasm.Jco.Res
