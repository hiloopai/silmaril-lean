module

public import Silmaril.Wasm.Instantiation.Defs

/-!
# Completeness of direct segment initialisation (proofs)

The converse of silmaril-lean's `initSegments?_steps`: in the host-free deterministic profile
`profile o`, a run of `initCode m` to the empty code from frame `f` is computed by
`initSegments?`, provided every offset of `m` is complete at `f` (`OffsetCompleteAt`).
The proof follows the segment code one segment at a time: offset, then `table.init` or
`memory.init` (silmaril-lean's `tableInitLoop_complete`, `memoryInitLoop_complete`), then
`elem.drop` or `data.drop`.

Ported from an earlier development `Silmaril/Wasm/Execution/Core/Exec/
{SegmentInitComplete,InstantiateInitComplete}.lean`. The source proves every segment lemma
twice, once with frame-independent and once with frame-restricted offset completeness. Here
only the frame-restricted form is proved, and `initSegments?_complete` derives the other form
from it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Instantiation

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Instantiation

variable {H : Type} {o : GrowOracle} {ev : Store H → Frame → Expr → Option (Store H × Val)}

theorem expression_append (a b : List Instr) :
    expression (a ++ b) = expression a ++ expression b := by
  simp [expression]

theorem elemDrop?_complete {s s' : Store H} {f f' : Frame} {y : ElemIdx} {W : List Val}
    (h : Steps (profile o) noHost ⟨s, f, [.plain (.elemDrop y)]⟩ ⟨s', f', vals W⟩) :
    elemDrop? s f y = some s' ∧ f' = f ∧ W = [] := by
  unfold elemDrop?
  cases he : s.elem? f y with
  | none =>
    exfalso
    obtain ⟨d, hd⟩ := Steps.first h (ne_vals_of_mem (e := .plain (.elemDrop y)) (by simp) rfl)
    obtain ⟨ea, ei, he'⟩ := elemDrop_inv (rest := []) hd
    rw [he] at he'
    cases he'
  | some p =>
    obtain ⟨rfl, rfl, rfl⟩ := Steps.nil_nf (Steps.of_step_nf h (Step.table (.elemDrop he)))
    exact ⟨by simp, rfl, rfl⟩

theorem dataDrop?_complete {s s' : Store H} {f f' : Frame} {y : DataIdx} {W : List Val}
    (h : Steps (profile o) noHost ⟨s, f, [.plain (.dataDrop y)]⟩ ⟨s', f', vals W⟩) :
    dataDrop? s f y = some s' ∧ f' = f ∧ W = [] := by
  unfold dataDrop?
  cases hd : s.data? f y with
  | none =>
    exfalso
    obtain ⟨d, hd'⟩ := Steps.first h (ne_vals_of_mem (e := .plain (.dataDrop y)) (by simp) rfl)
    obtain ⟨da, di, hd''⟩ := dataDrop_inv (rest := []) hd'
    rw [hd] at hd''
    cases hd''
  | some p =>
    obtain ⟨rfl, rfl, rfl⟩ := Steps.nil_nf (Steps.of_step_nf h (Step.memory (.dataDrop hd)))
    exact ⟨by simp, rfl, rfl⟩

/-- An active element segment: the offset, `table.init` from its value, then `elem.drop`. -/
theorem initElemSeg?_active {s s₁ s' : Store H} {f f' : Frame} {k : Nat} {e : Elem}
    {y : TableIdx} {off : Expr} {v : Val} {rest : List Admin} {W : List Val}
    (hm : e.mode = .active y off) (hev : ev s f off = some (s₁, v))
    (h : Steps (profile o) noHost
      ⟨s₁, f, v.toAdmin :: constI32 0 :: constI32 (BitVec.ofNat 32 e.init.length) ::
        .plain (.tableInit y ⟨Fin.ofNat _ k⟩) :: .plain (.elemDrop ⟨Fin.ofNat _ k⟩) :: rest⟩
      ⟨s', f', vals W⟩) :
    ∃ s₂, initElemSeg? ev s f k e = some s₂ ∧
      Steps (profile o) noHost ⟨s₂, f, rest⟩ ⟨s', f', vals W⟩ := by
  obtain ⟨d, hd⟩ := Steps.first h
    (ne_vals_of_mem (e := .plain (.tableInit y ⟨Fin.ofNat _ k⟩)) (by simp) rfl)
  obtain ⟨⟨a, i, hv⟩, -, -⟩ := tableInit_inv hd
  have h₁ := (Val.toAdmin_of_addr? hv) ▸ h
  obtain ⟨s₂, f₂, vs₂, h3, h4⟩ := Steps.append_split
    (is := [aconst a i, constI32 0, constI32 (BitVec.ofNat 32 e.init.length),
      .plain (.tableInit y ⟨Fin.ofNat _ k⟩)]) h₁
  obtain ⟨h5, rfl, rfl⟩ := tableInitLoop_complete _ h3
  obtain ⟨s₃, f₃, vs₃, h6, h7⟩ := Steps.append_split
    (is := [.plain (.elemDrop ⟨Fin.ofNat _ k⟩)]) (by simpa using h4)
  obtain ⟨h8, rfl, rfl⟩ := elemDrop?_complete h6
  exact ⟨s₃, by simp only [initElemSeg?, hm, hev, hv, h5, h8], by simpa using h7⟩

/-- An active data segment: the offset, `memory.init` from its value, then `data.drop`. -/
theorem initDataSeg?_active {s s₁ s' : Store H} {f f' : Frame} {k : Nat} {d : Data}
    {y : MemIdx} {off : Expr} {v : Val} {rest : List Admin} {W : List Val}
    (hm : d.mode = .active y off) (hev : ev s f off = some (s₁, v))
    (h : Steps (profile o) noHost
      ⟨s₁, f, v.toAdmin :: constI32 0 :: constI32 (BitVec.ofNat 32 d.bytes.size) ::
        .plain (.memoryInit y ⟨Fin.ofNat _ k⟩) :: .plain (.dataDrop ⟨Fin.ofNat _ k⟩) :: rest⟩
      ⟨s', f', vals W⟩) :
    ∃ s₂, initDataSeg? ev s f k d = some s₂ ∧
      Steps (profile o) noHost ⟨s₂, f, rest⟩ ⟨s', f', vals W⟩ := by
  obtain ⟨c, hc⟩ := Steps.first h
    (ne_vals_of_mem (e := .plain (.memoryInit y ⟨Fin.ofNat _ k⟩)) (by simp) rfl)
  obtain ⟨⟨a, i, hv⟩, -, -⟩ := memoryInit_inv hc
  have h₁ := (Val.toAdmin_of_addr? hv) ▸ h
  obtain ⟨s₂, f₂, vs₂, h3, h4⟩ := Steps.append_split
    (is := [aconst a i, constI32 0, constI32 (BitVec.ofNat 32 d.bytes.size),
      .plain (.memoryInit y ⟨Fin.ofNat _ k⟩)]) h₁
  obtain ⟨h5, rfl, rfl⟩ := memoryInitLoop_complete _ h3
  obtain ⟨s₃, f₃, vs₃, h6, h7⟩ := Steps.append_split
    (is := [.plain (.dataDrop ⟨Fin.ofNat _ k⟩)]) (by simpa using h4)
  obtain ⟨h8, rfl, rfl⟩ := dataDrop?_complete h6
  exact ⟨s₃, by simp only [initDataSeg?, hm, hev, hv, h5, h8], by simpa using h7⟩

theorem initElemSeg?_complete {s s' : Store H} {f f' : Frame} {k : Nat} {e : Elem}
    {rest : List Admin} {W : List Val}
    (hoff : ∀ y off, e.mode = .active y off → OffsetCompleteAt o ev f off)
    (h : Steps (profile o) noHost ⟨s, f, expression (runElem k e) ++ rest⟩ ⟨s', f', vals W⟩) :
    ∃ s₁, initElemSeg? ev s f k e = some s₁ ∧
      Steps (profile o) noHost ⟨s₁, f, rest⟩ ⟨s', f', vals W⟩ := by
  unfold runElem at h
  rcases hm : e.mode with _ | ⟨y, off⟩ | _ <;> rw [hm] at h
  · exact ⟨s, by simp [initElemSeg?, hm], by simpa [expression] using h⟩
  · rw [expression_append, List.append_assoc] at h
    obtain ⟨s₁, f₁, vs, h1, h2⟩ := Steps.append_split h
    obtain ⟨rfl, v, rfl, hev⟩ := hoff y off hm s s₁ f₁ vs h1
    exact initElemSeg?_active hm hev h2
  · obtain ⟨s₁, f₁, vs, h1, h2⟩ := Steps.append_split
      (is := [.plain (.elemDrop ⟨Fin.ofNat _ k⟩)]) h
    obtain ⟨h3, rfl, rfl⟩ := elemDrop?_complete h1
    exact ⟨s₁, by simp only [initElemSeg?, hm]; exact h3, by simpa using h2⟩

theorem initDataSeg?_complete {s s' : Store H} {f f' : Frame} {k : Nat} {d : Data}
    {rest : List Admin} {W : List Val}
    (hoff : ∀ y off, d.mode = .active y off → OffsetCompleteAt o ev f off)
    (h : Steps (profile o) noHost ⟨s, f, expression (runData k d) ++ rest⟩ ⟨s', f', vals W⟩) :
    ∃ s₁, initDataSeg? ev s f k d = some s₁ ∧
      Steps (profile o) noHost ⟨s₁, f, rest⟩ ⟨s', f', vals W⟩ := by
  unfold runData at h
  rcases hm : d.mode with _ | ⟨y, off⟩ <;> rw [hm] at h
  · exact ⟨s, by simp [initDataSeg?, hm], by simpa [expression] using h⟩
  · rw [expression_append, List.append_assoc] at h
    obtain ⟨s₁, f₁, vs, h1, h2⟩ := Steps.append_split h
    obtain ⟨rfl, v, rfl, hev⟩ := hoff y off hm s s₁ f₁ vs h1
    exact initDataSeg?_active hm hev h2

theorem initElemList?_complete :
    ∀ {s s' : Store H} {f f' : Frame} {es : List (Nat × Elem)} {rest : List Admin} {W : List Val},
      (∀ p ∈ es, ∀ y off, p.2.mode = .active y off → OffsetCompleteAt o ev f off) →
      Steps (profile o) noHost
        ⟨s, f, expression (es.flatMap fun (i, e) => runElem i e) ++ rest⟩ ⟨s', f', vals W⟩ →
      ∃ s₁, initElemList? ev s f es = some s₁ ∧
        Steps (profile o) noHost ⟨s₁, f, rest⟩ ⟨s', f', vals W⟩
  | s, _, _, _, [], _, _, _, h => ⟨s, rfl, by simpa [expression] using h⟩
  | _, _, _, _, (k, e) :: es, _, _, hoff, h => by
    rw [List.flatMap_cons, expression_append, List.append_assoc] at h
    obtain ⟨s₁, h1, h2⟩ := initElemSeg?_complete (hoff (k, e) (by simp)) h
    obtain ⟨s₂, h3, h4⟩ := initElemList?_complete (fun p hp => hoff p (by simp [hp])) h2
    exact ⟨s₂, by simp [initElemList?, h1, h3], h4⟩

theorem initDataList?_complete :
    ∀ {s s' : Store H} {f f' : Frame} {ds : List (Nat × Data)} {rest : List Admin} {W : List Val},
      (∀ p ∈ ds, ∀ y off, p.2.mode = .active y off → OffsetCompleteAt o ev f off) →
      Steps (profile o) noHost
        ⟨s, f, expression (ds.flatMap fun (i, d) => runData i d) ++ rest⟩ ⟨s', f', vals W⟩ →
      ∃ s₁, initDataList? ev s f ds = some s₁ ∧
        Steps (profile o) noHost ⟨s₁, f, rest⟩ ⟨s', f', vals W⟩
  | s, _, _, _, [], _, _, _, h => ⟨s, rfl, by simpa [expression] using h⟩
  | _, _, _, _, (k, d) :: ds, _, _, hoff, h => by
    rw [List.flatMap_cons, expression_append, List.append_assoc] at h
    obtain ⟨s₁, h1, h2⟩ := initDataSeg?_complete (hoff (k, d) (by simp)) h
    obtain ⟨s₂, h3, h4⟩ := initDataList?_complete (fun p hp => hoff p (by simp [hp])) h2
    exact ⟨s₂, by simp [initDataList?, h1, h3], h4⟩

/-- **Segment initialisation is complete** for runs from frame `f`, given offset completeness
at `f`. -/
theorem initSegments?_completeAt {s s' : Store H} {f f' : Frame} {m : Module}
    (hc : ∀ e, IsOffset m e → OffsetCompleteAt o ev f e)
    (h : Steps (profile o) noHost ⟨s, f, initCode m⟩ ⟨s', f', []⟩) :
    initSegments? ev s f m = some (s', f') := by
  have h' : Steps (profile o) noHost _ ⟨s', f', vals []⟩ := h
  obtain ⟨s₁, h1, h2⟩ := initElemList?_complete (fun p hp y off hm =>
    hc off (.inl ⟨p.2, (List.of_mem_zip hp).2, y, hm⟩)) h'
  obtain ⟨s₂, h3, h4⟩ := initDataList?_complete (rest := []) (fun p hp y off hm =>
    hc off (.inr ⟨p.2, (List.of_mem_zip hp).2, y, hm⟩)) (by rw [List.append_nil]; exact h2)
  obtain ⟨rfl, rfl, -⟩ := Steps.nil_nf h4
  simp [initSegments?, initElem?, initData?, h1, h3]

/-- Offset completeness at every frame, from completeness of `ev` on frame-preserving
single-value evaluations and the fact that offsets keep the frame and yield one value. -/
theorem offsetCompleteAt_of {m : Module}
    (hevc : ∀ s f e s' v, EvalExpr (profile o) noHost s f e s' f [v] → ev s f e = some (s', v))
    (hoff : ∀ e, IsOffset m e → ∀ (s : Store H) (f : Frame) (s' : Store H) (f' : Frame) vs,
      EvalExpr (profile o) noHost s f e s' f' vs → f' = f ∧ vs.length = 1)
    {e : Expr} (he : IsOffset m e) (f : Frame) : OffsetCompleteAt o ev f e := by
  intro s s' f' vs hx
  obtain ⟨rfl, hl⟩ := hoff e he s f s' f' vs hx
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hl
  exact ⟨rfl, v, rfl, hevc _ _ _ _ _ hx⟩

/-- **Relative completeness of segment initialisation** for an arbitrary evaluator. -/
theorem initSegments?_complete {s s' : Store H} {f f' : Frame} {m : Module}
    (hevc : ∀ s f e s' v, EvalExpr (profile o) noHost s f e s' f [v] → ev s f e = some (s', v))
    (hoff : ∀ e, IsOffset m e → ∀ (s : Store H) (f : Frame) (s' : Store H) (f' : Frame) vs,
      EvalExpr (profile o) noHost s f e s' f' vs → f' = f ∧ vs.length = 1)
    (h : Steps (profile o) noHost ⟨s, f, initCode m⟩ ⟨s', f', []⟩) :
    initSegments? ev s f m = some (s', f') :=
  initSegments?_completeAt (fun _ he => offsetCompleteAt_of hevc hoff he f) h

end Silmaril.Proofs.Wasm.Instantiation
