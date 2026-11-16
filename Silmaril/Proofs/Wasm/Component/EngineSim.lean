module

public import Silmaril.Wasm.Component.Engine.Sim.Defs

/-! Proofs for `Silmaril.Wasm.Component.Engine.Sim.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.EngineSim

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Engine.CoreEngine

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I)

theorem internal {H : Type} {c c' : (E.withStore I).Config H}
    (h : (E.withStore I).Internal c c') : E.Internal (S.map c) (S.map c') := by
  obtain ⟨s, t⟩ := c
  obtain ⟨s', t'⟩ := c'
  exact S.internal h

theorem internal_lift {H : Type} {c : (E.withStore I).Config H} {d : E.Config H}
    (h : E.Internal (S.map c) d) : ∃ c', (E.withStore I).Internal c c' ∧ d = S.map c' := by
  obtain ⟨s, t⟩ := c
  obtain ⟨s', t', h', rfl⟩ := S.internal_lift h
  exact ⟨(s', t'), h', rfl⟩

theorem steps {H : Type} {c c' : (E.withStore I).Config H} (h : (E.withStore I).Steps c c') :
    E.Steps (S.map c) (S.map c') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (internal S hs)

theorem steps_lift {H : Type} {c : (E.withStore I).Config H} {d : E.Config H}
    (h : E.Steps (S.map c) d) : ∃ c', (E.withStore I).Steps c c' ∧ d = S.map c' := by
  induction h with
  | refl => exact ⟨c, .refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨c₁, h₁, rfl⟩ := ih
    obtain ⟨c₂, h₂, rfl⟩ := internal_lift S hs
    exact ⟨c₂, h₁.tail h₂, rfl⟩

theorem diverges_iff {H : Type} {c : (E.withStore I).Config H} :
    (E.withStore I).Diverges c ↔ E.Diverges (S.map c) := by
  constructor
  · exact Silmaril.InfiniteTrace.map S.map (fun _ _ h => internal S h)
  · exact Silmaril.InfiniteTrace.of_map S.map (fun _ => True)
      (fun _ _ _ h => by
        obtain ⟨c', h', e⟩ := internal_lift S h
        exact ⟨c', h', trivial, e.symm⟩) trivial

theorem extends_iff {H : Type} {s s' : I.Store H} :
    (E.withStore I).Extends s s' ↔ E.Extends (S.φ s) (S.φ s') := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a ft e
      rw [S.funcType?] at e ⊢
      exact h.funcType a ft e
    · intro m t e
      rw [S.memAddrType?] at e ⊢
      exact h.memAddrType m t e
    · intro m n e
      rw [S.memSize?] at e ⊢
      exact h.memSize m n e
    · intro t at_ e
      rw [S.tableAddrType?] at e ⊢
      exact h.tableAddrType t at_ e
    · intro t hh args e
      rw [S.status] at e ⊢
      exact h.callout t hh args e
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a ft e
      have := h.funcType a ft (by rw [S.funcType?]; exact e)
      rwa [S.funcType?] at this
    · intro m t e
      have := h.memAddrType m t (by rw [S.memAddrType?]; exact e)
      rwa [S.memAddrType?] at this
    · intro m n e
      have := h.memSize m n (by rw [S.memSize?]; exact e)
      rwa [S.memSize?] at this
    · intro t at_ e
      have := h.tableAddrType t at_ (by rw [S.tableAddrType?]; exact e)
      rwa [S.tableAddrType?] at this
    · intro t hh args e
      have := h.callout t hh args (by rw [S.status]; exact e)
      rwa [S.status] at this

theorem prepare?_some {H : Type} {s s' : I.Store H} {m : E.Module} {vs : List E.ExternVal}
    {i : E.Inst} {st : Option E.FuncAddr} (h : I.prepare? s m vs = some (s', i, st)) :
    E.prepare? (S.φ s) m vs = some (S.φ s', i, st) := by
  rw [S.prepare?, h]; rfl

theorem allocHost_eq {H : Type} {s s' : I.Store H} {ft : Silmaril.Wasm.V1.FuncType} {hh : H}
    {a : E.FuncAddr}
    (h : I.allocHost s ft hh = (s', a)) : E.allocHost (S.φ s) ft hh = (S.φ s', a) := by
  rw [S.allocHost, h]

theorem memWrite?_some {H : Type} {s s' : I.Store H} {m : E.MemAddr} {st : Nat}
    {bs : ByteArray} (h : I.memWrite? s m st bs = some s') :
    E.memWrite? (S.φ s) m st bs = some (S.φ s') := by
  rw [S.memWrite?, h]; rfl

/-- The engine laws carry over to `E.withStore I`. -/
theorem lawful (S : E.StoreSim I) [L : E.Lawful] : (E.withStore I).Lawful where
  flatType?_ofFlatType := L.flatType?_ofFlatType
  returned_no_step {_ s t r c'} hs hi := by
    obtain ⟨s', t'⟩ := c'
    exact L.returned_no_step (by rw [S.status]; exact hs) (S.internal hi)
  callout_no_step {_ s t h args c'} hs hi := by
    obtain ⟨s', t'⟩ := c'
    exact L.callout_no_step (by rw [S.status]; exact hs) (S.internal hi)
  stuck_no_step {_ s t c'} hs hi := by
    obtain ⟨s', t'⟩ := c'
    exact L.stuck_no_step (by rw [S.status]; exact hs) (S.internal hi)
  externSub_refl := L.externSub_refl
  externSub_trans := L.externSub_trans
  asFunc?_ofFunc := L.asFunc?_ofFunc
  internal_extends hi := (extends_iff S).2 (L.internal_extends (S.internal hi))
  prepare_extends h := (extends_iff S).2 (L.prepare_extends (prepare?_some S h))
  allocHost_extends h := (extends_iff S).2 (L.allocHost_extends (allocHost_eq S h))
  allocHost_fresh h := by
    have := L.allocHost_fresh (allocHost_eq S h)
    rwa [S.funcType?] at this
  allocHost_frame h hb := by
    have := L.allocHost_frame (allocHost_eq S h) hb
    rwa [S.funcType?, S.funcType?] at this
  allocHost_funcType h := by
    have := L.allocHost_funcType (allocHost_eq S h)
    rwa [S.funcType?] at this
  allocHost_callout h ha := by
    have := L.allocHost_callout (allocHost_eq S h) ha
    rwa [S.status] at this
  memWrite_extends h := (extends_iff S).2 (L.memWrite_extends (memWrite?_some S h))
  memWrite_memSize h m' := by
    have := L.memWrite_memSize (memWrite?_some S h) m'
    rwa [S.memSize?, S.memSize?] at this
  memWrite_memAddrType h m' := by
    have := L.memWrite_memAddrType (memWrite?_some S h) m'
    rwa [S.memAddrType?, S.memAddrType?] at this
  memWrite_read h := by
    have := L.memWrite_read (memWrite?_some S h)
    rwa [S.memRead?] at this
  memWrite_read_other h ho := by
    have := L.memWrite_read_other (memWrite?_some S h) ho
    rwa [S.memRead?, S.memRead?] at this
  memRead_isSome_iff {_ s m st len} := by
    have := L.memRead_isSome_iff (s := S.φ s) (m := m) (st := st) (len := len)
    rwa [S.memRead?, S.memSize?] at this
  memRead_size {_ s m st len bs} h := L.memRead_size (s := S.φ s) (by rw [S.memRead?]; exact h)
  memWrite_isSome_iff {_ s m st bs} := by
    have := L.memWrite_isSome_iff (s := S.φ s) (m := m) (st := st) (bs := bs)
    rwa [S.memWrite?, Option.isSome_map, S.memSize?] at this
  memAddrType_isSome_iff {_ s m} := by
    have := L.memAddrType_isSome_iff (s := S.φ s) (m := m)
    rwa [S.memAddrType?, S.memSize?] at this

theorem runCore {X : E.Exec} {X' : (E.withStore I).Exec} (hX : ExecSim S X X') {H : Type}
    (n : Nat) (c : (E.withStore I).Config H) :
    X.runCore n (S.map c) = Prod.map S.map id (X'.runCore n c) := by
  induction n generalizing c with
  | zero => simp [Exec.runCore, hX.step?]
  | succ n ih =>
    simp only [Exec.runCore, hX.step?]
    cases X'.step? c with
    | none => rfl
    | some c' => exact ih c'

end Silmaril.Proofs.Wasm.Component.EngineSim
