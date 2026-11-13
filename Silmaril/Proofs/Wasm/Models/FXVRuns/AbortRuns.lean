module

public import Silmaril.Proofs.Wasm.Models.FXVRuns.Abort

/-!
# The abortive fragment: the source's behaviours are exactly the join's

* **`src_step_inv`**: every `StepFX'` step of `abortSrc hs W x ks` (no host calls) is `suspend`
  with a split `W = U ++ vs`, to the label around `vs; ref.cont; br l`;
* **`mid_inv`**, `split_stuck`: from there, a step exists only for `U = []`, and it is the
  branch to `W; ref.cont; drop; ks` (the other splits are one value short of the label's arity);
* **`src_behaviours_eq`**: the source's `StepFX'` behaviours without FX functions are exactly the
  Core behaviours of the join `W; ks` at the source's store (`contdrop_inv` for the last step,
  `src_behaviours_sup` for the converse).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXVRuns

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXAbort
open Silmaril.Proofs.Wasm.Models.FXLower (ofCoreK)
open Silmaril.Proofs.Wasm.Models.FX (isCore)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- The label the source branches to, after `suspend` kept the values `vs`. -/
def midCode (W : List Val) (ks : List Instr) (vs : List FVal) (j : Nat) (l : LabelIdx) :
    List AdminFX :=
  [.label (W.length + 1) (.core .drop :: ks.map .core)
    (fvals vs ++ [.contRef j, .core (.plain (.br l))])]

/-- The code after the branch: the payload, the continuation, `drop`, then `ks`. -/
def dropCode (W : List Val) (ks : List Instr) (j : Nat) : List AdminFX :=
  fvals (liftV W) ++ [.contRef j, .core (.plain .drop)] ++ (ks.map InstrFX.core).map InstrFX.toAdmin

/-- The `ctxt-label` case of `src_step_inv`. -/
theorem src_label_case {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {hs : List HClause} {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} {es' : List AdminFX} (ht : s.tag? f x = some (ta, ti))
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l))
    (h' : StepFX' P noHost fx ⟨s, K, f, [.handler hs (cvals W ++ [.fx (.suspend x)])]⟩
      ⟨s', K', f', es'⟩) :
    ∃ (U vs : List FVal) (E : CtxV), liftV W = U ++ vs ∧
      (⟨s', K', f', [.label (W.length + 1) (.core .drop :: ks.map .core) es']⟩ : ConfigFX H) =
        ⟨s, K ++ [some ⟨E.plug⟩], f, midCode W ks vs K.length l⟩ := by
  rw [← fvals_liftV'] at h'
  obtain ⟨U, vs, E, ta', ti', l', hU, ht', hcl', hy⟩ := handler_inv h'
  have hta : ta' = ta := (Prod.mk.inj (Option.some.inj (ht'.symm.trans ht))).1
  subst hta
  have hl' : l' = l := by
    have h1 := hcl'.symm.trans hcl
    injection h1 with h2
    injection h2
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
  exact ⟨U, vs, E, hU, by rw [hl']; rfl⟩

/-- **Every step of the source is a `suspend`**, with some split of the payload. -/
theorem src_step_inv {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti))
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, abortSrc hs W x ks⟩ y) :
    ∃ (U vs : List FVal) (E : CtxV), liftV W = U ++ vs ∧
      y = ⟨s, K ++ [some ⟨E.plug⟩], f, midCode W ks vs K.length l⟩ := by
  unfold abortSrc at h
  generalize hx : (⟨s, K, f, [.label (W.length + 1) (.core .drop :: ks.map .core)
    [.handler hs (cvals W ++ [.fx (.suspend x)])]]⟩ : ConfigFX H) = c at h
  have hc : c.code = [.label (W.length + 1) (.core .drop :: ks.map .core)
      [.handler hs (cvals W ++ [.fx (.suspend x)])]] := by rw [← hx]
  have hcs : c.store = s := by rw [← hx]
  have hcK : c.conts = K := by rw [← hx]
  have hcf : c.frame = f := by rw [← hx]
  cases h with
  | @ctxLabel s₀ s' K₀ K' f₀ f' n k es es' h' =>
    obtain ⟨rfl, rfl, rfl⟩ := label_inj hc
    obtain rfl : s₀ = s := hcs
    obtain rfl : K₀ = K := hcK
    obtain rfl : f₀ = f := hcf
    exact src_label_case ht hcl h'
  | seq h' hne => exact absurd (seq_single' rfl hne hc) (no_step_nil' h')
  | labelVals => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | brLabelZero => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | brLabelSucc => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | returnLabel => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | trapLabel => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | throwLabel => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | invoke hci =>
    have h1 := congrArg (fun l => (fnvF l).1) hc
    simp at h1
  | _ => fnvF_absurd hc

theorem midCode_eq (W : List Val) (ks : List Instr) (vs : List FVal) (j : Nat) (l : LabelIdx) :
    midCode W ks vs j l = [.label (W.length + 1) (.core .drop :: ks.map .core)
      (fvals (vs ++ [.cont j]) ++ [.core (.plain (.br l))])] := by
  simp [midCode, FVal.toAdmin]

/-- **From the branch, only the split that kept the whole payload steps**, to `dropCode`. -/
theorem mid_inv {s : Store H} {K : List (Option ContFX)} {f : Frame} {W : List Val}
    {ks : List Instr} {U vs : List FVal} {j : Nat} {l : LabelIdx} (hl : l.toNat = 0)
    (hU : liftV W = U ++ vs) {z : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, midCode W ks vs j l⟩ z) :
    U = [] ∧ z = ⟨s, K, f, dropCode W ks j⟩ := by
  rw [midCode_eq] at h
  obtain ⟨va, vb, hV, hn, rfl⟩ := label_br_inv hl h
  have hl₁ := congrArg List.length hU
  have hl₂ := congrArg List.length hV
  simp only [Silmaril.Proofs.Wasm.Models.FXV.liftV_length, List.length_append,
    List.length_singleton] at hl₁ hl₂
  obtain rfl : U = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain rfl : va = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [List.nil_append] at hU hV
  subst hU hV
  refine ⟨rfl, ?_⟩
  simp [dropCode, InstrFX.toAdmin, FVal.toAdmin]

/-- **The other splits are stuck**: when `suspend` captured a non-empty prefix, the branch is
short of the label's arity. -/
theorem split_stuck {s : Store H} {K : List (Option ContFX)} {f : Frame} {W : List Val}
    {ks : List Instr} {U vs : List FVal} {j : Nat} {l : LabelIdx} (hl : l.toNat = 0)
    (hU : liftV W = U ++ vs) (hne : U ≠ []) (z : ConfigFX H) :
    ¬ StepFX' P noHost fx ⟨s, K, f, midCode W ks vs j l⟩ z :=
  fun h => hne (mid_inv hl hU h).1

/-- The last step reaches the join. -/
theorem dropCode_join (s : Store H) (K : List (Option ContFX)) (f : Frame) (W : List Val)
    (ks : List Instr) :
    (⟨s, K, f, fvals (liftV W) ++ (ks.map InstrFX.core).map InstrFX.toAdmin⟩ : ConfigFX H) =
      ofCoreK K ⟨s, f, abortJoin W ks⟩ := by
  simp only [ofCoreK, abortJoin, fvals_liftV', Silmaril.Proofs.Wasm.Models.FXAbort.toAdmin_core_map,
    cvals, List.map_append]

/-- **Behaviours through a non-result** (`StepFX'`): they are behaviours of its successors. -/
theorem behavioursFX'_sub_of_succ {host : HostSemantics H} {x : ConfigFX H}
    {B : Set (Behaviour Val)} (hnr : ∀ r : Result, x.code ≠ r.toAdmin.map .core)
    (h : ∀ y, StepFX' P host fx x y → behavioursFX' P host fx y ⊆ B) :
    behavioursFX' P host fx x ⊆ B := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · rcases Relation.ReflTransGen.cases_head hrun with rfl | ⟨y, hy, hrest⟩
    · exact absurd hd (hnr r)
    · exact h y hy (Or.inl ⟨d, r, hrest, hd, rfl⟩)
  · obtain ⟨y, hy, htr⟩ := hdiv.unfold
    exact h y hy (Or.inr ⟨rfl, htr⟩)

/-- Code with a non-Core instruction is not a result. -/
theorem not_result_of_mem {code : List AdminFX} {a : AdminFX} (ha : a ∈ code)
    (hc : isCore a = false) (r : Result) : code ≠ r.toAdmin.map .core := by
  intro h
  rw [h] at ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
  simp [isCore] at hc

/-- **The source's behaviours are the join's**, without host calls or FX functions. -/
theorem src_behaviours_eq {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    behavioursFX' P noHost noFX ⟨s, K, f, abortSrc hs W x ks⟩ =
      behavioursOf P noHost ⟨s, f, abortJoin W ks⟩ := by
  refine Set.Subset.antisymm ?_ (Silmaril.Wasm.Models.FXAbort.src_behaviours_sup ht hcl hl)
  refine behavioursFX'_sub_of_succ
    (not_result_of_mem (List.mem_singleton_self _) (by simp [isCore])) fun y hy => ?_
  obtain ⟨U, vs, E, hU, rfl⟩ := src_step_inv ht hcl hy
  refine behavioursFX'_sub_of_succ
    (not_result_of_mem (List.mem_singleton_self _) (by simp [isCore])) fun z hz => ?_
  obtain ⟨rfl, rfl⟩ := mid_inv hl hU hz
  refine behavioursFX'_sub_of_succ
    (not_result_of_mem (a := .contRef K.length) (by simp [dropCode]) (by simp [isCore]))
    fun w hw => ?_
  rw [contdrop_inv hw (liftV W) K.length ((ks.map InstrFX.core).map InstrFX.toAdmin) rfl,
    dropCode_join,
    Silmaril.Wasm.Models.FXV.behavioursFX'_ofCoreK]

end Silmaril.Proofs.Wasm.Models.FXVRuns
