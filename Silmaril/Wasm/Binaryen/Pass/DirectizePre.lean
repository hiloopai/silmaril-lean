module

public import Silmaril.Wasm.Binaryen.Pass.DirectizeProfileInit
public import Silmaril.Wasm.Binaryen.Pass.DirectizeInit
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

@[expose] public section

/-! # Directize: the element segments start the simulation

The instantiation configurations of the module and of its rewrite have the same code and
stores that differ only in their functions. Their element segments run the same on both
sides (`DirectizeInit.initElemListT?_withFuncs`) and either run or trap
(`DirectizeInit.initElemListT?_cases`). When they run, the simulation starts after them,
given the invariant there; when they trap, both sides trap (`pre_of_segments`).
-/

namespace Silmaril.Wasm.Binaryen

namespace DirectizePre

open Execution.Core Numerics Validation ElemInit InlS DirectizeInit

variable {H : Type}

theorem elemDrop?_funcs {s s' : Store H} {f : Frame} {y : ElemIdx} (h : elemDrop? s f y = some s') :
    s'.funcs = s.funcs := by
  unfold elemDrop? at h
  cases he : s.elem? f y with
  | none => rw [he] at h; cases h
  | some q => rw [he] at h; cases h; rfl

theorem initElemSeg?_funcs {ev : Store H → Frame → Expr → Option (Store H × Val)} {s s' : Store H}
    {f : Frame} {k : Nat} {e : Elem} (hev : ConstOffsets ev f) (hc : ConstSeg e)
    (h : initElemSeg? ev s f k e = some s') : s'.funcs = s.funcs := by
  unfold initElemSeg? at h
  split at h
  · cases h; rfl
  · exact elemDrop?_funcs h
  · rename_i y off hm
    obtain ⟨o, rfl⟩ := hc y off hm
    rw [hev] at h
    simp only [Val.addr?] at h
    split at h
    · cases h
    · rename_i s₂ h₂
      rw [elemDrop?_funcs h, (tableInitLoop_elems _ h₂).2]

theorem initElemList?_funcs {ev : Store H → Frame → Expr → Option (Store H × Val)} {f : Frame}
    (hev : ConstOffsets ev f) :
    ∀ {L : List (Nat × Elem)} {s s' : Store H}, (∀ p ∈ L, ConstSeg p.2) →
      initElemList? ev s f L = some s' → s'.funcs = s.funcs
  | [], s, s', _, h => by cases h; rfl
  | (k, e) :: L, s, s', hc, h => by
    simp only [initElemList?] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      rw [initElemList?_funcs hev (fun p hp => hc p (by simp [hp])) h,
        initElemSeg?_funcs hev (hc (k, e) (by simp)) h₁]

section profile

variable {P : Profile}

/-- **The instantiation configurations correspond.** -/
theorem pre_of_segments_profile {ok : DirSim.SiteOk} {mi : ModuleInst} {s₄ : Store H}
    {G : List (FuncInst H)} {f : Frame} {L : List (Nat × Elem)} {R : List Admin}
    (hG : List.Forall₂ (DirSim.FR ok mi) s₄.funcs G) (hc : ∀ p ∈ L, ConstSeg p.2)
    (hl : ∀ p ∈ L, SegLookups s₄ f p)
    (hfin : ∀ s₅, initElemList? evalConst? s₄ f L = some s₅ →
      s₅.funcs = s₄.funcs → DirSim.FInv ok mi ⟨s₅, f, R⟩) :
    DirSim.InitAligned P ok mi ⟨s₄, f, expression (L.flatMap fun (i, e) => runElem i e) ++ R⟩
      ⟨withFuncs s₄ G, f, expression (L.flatMap fun (i, e) => runElem i e) ++ R⟩ := by
  have hev := evalConst?_constOffsets (H := H) f
  have hw := initElemListT?_withFuncs hev G L s₄ hc
  rcases initElemListT?_cases hev L s₄ hc hl with ⟨s₅, h5⟩ | ⟨s₅, h5⟩
  · have hok := (initElemListT?_ok_iff (ev := evalConst?)).mp h5
    rw [h5] at hw
    have hok' := (initElemListT?_ok_iff (ev := evalConst?)).mp hw
    have hfs := initElemList?_funcs hev hc hok
    refine .inl ⟨⟨s₅, f, R⟩, ⟨withFuncs s₅ G, f, R⟩,
      InitPrefix.initElemList?_prefix hc R hok,
      InitPrefix.initElemList?_prefix hc R hok',
      rfl, rfl, DirSim.SR.mk' (by rw [hfs]; exact hG), hfin s₅ hok hfs⟩
  · rw [h5] at hw
    exact .inr ⟨⟨s₅, f, [.trap]⟩, ⟨withFuncs s₅ G, f, [.trap]⟩,
      InitPrefix.initElemListT?_trap_prefix hc R h5,
      InitPrefix.initElemListT?_trap_prefix hc R hw, rfl, rfl⟩

end profile

/-- Backwards-compatible deterministic specialization. -/
theorem pre_of_segments {o : GrowKind → Nat → Nat → Nat → Bool}
    {ok : DirSim.SiteOk} {mi : ModuleInst} {s₄ : Store H}
    {G : List (FuncInst H)} {f : Frame} {L : List (Nat × Elem)} {R : List Admin}
    (hG : List.Forall₂ (DirSim.FR ok mi) s₄.funcs G) (hc : ∀ p ∈ L, ConstSeg p.2)
    (hl : ∀ p ∈ L, SegLookups s₄ f p)
    (hfin : ∀ s₅, initElemList? evalConst? s₄ f L = some s₅ →
      s₅.funcs = s₄.funcs → DirSim.FInv ok mi ⟨s₅, f, R⟩) :
    DirSim.Pre ok mi o ⟨s₄, f, expression (L.flatMap fun (i, e) => runElem i e) ++ R⟩
      ⟨withFuncs s₄ G, f, expression (L.flatMap fun (i, e) => runElem i e) ++ R⟩ :=
  (pre_of_segments_profile hG hc hl hfin).toPre

end DirectizePre

end Silmaril.Wasm.Binaryen
