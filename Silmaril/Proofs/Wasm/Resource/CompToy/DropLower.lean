module

public import Silmaril.Proofs.Wasm.Resource.CompToy.CallX

/-!
# The toy resource component: lowering the argument of `drop`

`drop(own<r>)` lowers its argument `own n` with `lower_own`: a handle object
`{rt := 0, rep := n, own := true}` is allocated and added to the instance's handle table
(`runs_lower_drop`); a full table, or any other argument list, traps (`lower_drop_traps`).
New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs

variable {P : Silmaril.Wasm.Numerics.Profile}

theorem lower_drop_eq (cx : LiftLowerContext (E3 P)) (vs : List Val) :
    (lowerFlatValues Silmaril.Wasm.Component.Limits.spec Quirks.none cx ABI.maxFlatParams vs (paramTypes ftDrop) none :
      Canon.P (E3 P) Unit _) =
      ptrType cx >>= fun p => lowerFlatTypes Silmaril.Wasm.Component.Limits.spec Quirks.none cx p vs [.own ⟨0⟩] := by
  unfold lowerFlatValues
  congr 1
  funext p
  cases p <;> (rw [ite_eq_right_iff.mpr (by intro h; exact absurd h (by decide +kernel))]; rfl)

theorem lowerFlatAt_own_other (cx : LiftLowerContext (E3 P)) (p : Silmaril.Wasm.AddrType)
    (v : Val) (hv : ∀ n, v ≠ .own n) :
    (lowerFlatAt Silmaril.Wasm.Component.Limits.spec Quirks.none cx p v (.own ⟨0⟩) : Canon.P (E3 P) Unit _) =
      flatMismatch := by
  rw [lowerFlatAt.eq_def]
  cases v <;> first | rfl | exact absurd rfl (hv _)

/-- `lower_own` of `n` into instance `0` when its handle table has room. -/
theorem runs_lowerOwn {th : Option ThreadId} (t : TaskId) (n : ℕ) {m : Machine.Config (E3 P) Unit}
    {ι₁ ι₂ : InstState} {i : ℕ} (hi : m.store.insts = [ι₁])
    (hadd : ι₁.addHandle? (.resource ⟨m.store.resHandles.length⟩) = some (i, ι₂)) :
    RunsQ (D P) th (lowerOwn Silmaril.Wasm.Component.Limits.spec
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)) ⟨0⟩ n) m
      ([.tau, .tau] ++ ([.tau] ++ ([.tau] ++ []))) i { m with store := newSt m.store n ι₂ } := by
  let h : ResourceHandle := { rt := ⟨0⟩, rep := n, own := true }
  let s₁ := ArenaOps.allocSt ArenaField.resHandles h m.store
  have hgi : ArenaField.insts.get? s₁ ⟨0⟩ = some ι₁ := insts_get₀ (s := s₁) hi
  have hadd' : ι₁.addHandle? (.resource ((ArenaField.resHandles (E := E3 P)).mkId
      ((ArenaField.resHandles (E := E3 P)).size m.store))) = some (i, ι₂) := hadd
  have hm : RunsQ (D P) th (modifyInst ⟨0⟩ (InstState.addHandle (.resource
      ((ArenaField.resHandles (E := E3 P)).mkId ((ArenaField.resHandles (E := E3 P)).size
        m.store))))) { m with store := s₁ } [.tau] () { m with store := newSt m.store n ι₂ } := by
    have e : ArenaOps.updateSt ArenaField.insts ⟨0⟩ (InstState.addHandle (.resource
        ((ArenaField.resHandles (E := E3 P)).mkId ((ArenaField.resHandles (E := E3 P)).size
          m.store)))) s₁ = newSt m.store n ι₂ := by
      have hl : List.modify m.store.insts 0 (InstState.addHandle (.resource
          ((ArenaField.resHandles (E := E3 P)).mkId ((ArenaField.resHandles (E := E3 P)).size
            m.store)))) = [ι₂] := by
        rw [hi, ← InstState.addHandle_eq hadd']
        rfl
      show ({ s₁ with insts := List.modify m.store.insts 0 _ } : CStore (E3 P)) = _
      rw [hl]
      rfl
    rw [← e]
    exact runs_modifyStore _ _ rfl
  unfold lowerOwn addResHandle handlesAdd
  refine RunsQ.bind (runs_allocObj ArenaField.resHandles h m rfl)
    (RunsQ.bind (runs_getObj ArenaField.insts _ { m with store := s₁ } hgi) ?_)
  rw [hadd']
  exact RunsQ.bind hm (.pure _ _)

/-- `lower_own` into instance `0` traps when its handle table is full. -/
theorem traps_lowerOwn {th : Option ThreadId} (t : TaskId) (n : ℕ) {m : Machine.Config (E3 P) Unit}
    {ι₁ : InstState} (hi : m.store.insts = [ι₁])
    (hadd : ι₁.addHandle? (.resource ⟨m.store.resHandles.length⟩) = none) :
    ∃ tr mT, TrapsQ (D P) th (lowerOwn Silmaril.Wasm.Component.Limits.spec
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)) ⟨0⟩ n) m tr mT := by
  let h : ResourceHandle := { rt := ⟨0⟩, rep := n, own := true }
  let s₁ := ArenaOps.allocSt ArenaField.resHandles h m.store
  have hgi : ArenaField.insts.get? s₁ ⟨0⟩ = some ι₁ := insts_get₀ (s := s₁) hi
  have hadd' : ι₁.addHandle? (.resource ((ArenaField.resHandles (E := E3 P)).mkId
      ((ArenaField.resHandles (E := E3 P)).size m.store))) = none := hadd
  unfold lowerOwn addResHandle handlesAdd
  refine ⟨_, { m with store := s₁ }, TrapsQ.bind (tr₂ := [.tau] ++ [])
    (runs_allocObj ArenaField.resHandles h m rfl)
    (TrapsQ.bind (tr₂ := []) (runs_getObj ArenaField.insts _ { m with store := s₁ } hgi) ?_)⟩
  rw [hadd']
  exact TrapsQ.trap _ (isTrap_trap _)

/-- The lowering of `own n` when the handle table has room: the result is `[i32 i]`, `i` the
new entry. -/
theorem runs_lower_drop {th : Option ThreadId} (t : TaskId) (n : ℕ) :
    ∃ tr, ∀ (m : Machine.Config (E3 P) Unit) (ι₁ ι₂ : InstState) (i : ℕ),
      m.store.insts = [ι₁] →
      ι₁.addHandle? (.resource ⟨m.store.resHandles.length⟩) = some (i, ι₂) →
      RunsQ (D P) th (lowerFlatValues Silmaril.Wasm.Component.Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))
        ABI.maxFlatParams [.own n] (paramTypes ftDrop) none) m tr ([i32Flat i] ++ [])
        { m with store := newSt m.store n ι₂ } := by
  refine ⟨[.tau] ++ (([.tau, .tau] ++ ([.tau] ++ ([.tau] ++ []))) ++ [] ++ ([] ++ [])), ?_⟩
  intro m ι₁ ι₂ i hi hadd
  rw [lower_drop_eq]
  apply RunsQ.get
  show RunsQ _ _ (lowerFlatTypes Silmaril.Wasm.Component.Limits.spec Quirks.none _ (ptrTypeIn m.store
    ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))) [.own n]
    [.own ⟨0⟩]) _ _ _ _
  unfold lowerFlatTypes
  rw [lowerFlatAt.eq_def]
  dsimp only
  apply RunsQ.bind (RunsQ.bind
    (f := fun x => (pure [i32Flat x] : Canon.P (E3 P) Unit (List FlatValue)))
    (runs_lowerOwn t n hi hadd) (.pure _ _))
  unfold lowerFlatTypes
  exact RunsQ.bind (.pure _ _) (.pure _ _)

/-- **The lowering of `drop`'s arguments traps** unless they are one `own n` and the handle
table has room. -/
theorem lower_drop_traps {th : Option ThreadId} (t : TaskId) (args : List Val)
    (m : Machine.Config (E3 P) Unit) {ι₁ : InstState} (hi : m.store.insts = [ι₁])
    (h : (∀ n, args ≠ [.own n]) ∨
      ∃ n, args = [.own n] ∧ ι₁.addHandle? (.resource ⟨m.store.resHandles.length⟩) = none) :
    ∃ trT mT, TrapsQ (D P) th (lowerFlatValues Silmaril.Wasm.Component.Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))
      ABI.maxFlatParams args (paramTypes ftDrop) none) m trT mT := by
  have hp : ∀ p, ∃ trT mT, TrapsQ (D P) th (lowerFlatTypes Silmaril.Wasm.Component.Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)) p args
      [.own ⟨0⟩]) m trT mT := by
    intro p
    match args, h with
    | [], _ => exact ⟨_, _, TrapsQ.trap _ (isTrap_trap _)⟩
    | v :: rest, h =>
      unfold lowerFlatTypes
      by_cases hv : ∃ n, v = .own n
      · obtain ⟨n, rfl⟩ := hv
        have hown : ∀ q, (lowerFlatAt Silmaril.Wasm.Component.Limits.spec Quirks.none
            ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)) q (.own n)
            (.own ⟨0⟩) : Canon.P (E3 P) Unit _) = lowerOwn Silmaril.Wasm.Component.Limits.spec
              ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)) ⟨0⟩ n >>=
              fun x => pure [i32Flat x] := by
          intro q
          rw [lowerFlatAt.eq_def]
        rw [hown]
        cases hadd : ι₁.addHandle? (.resource ⟨m.store.resHandles.length⟩) with
        | none =>
          obtain ⟨trT, mT, hT⟩ := traps_lowerOwn (th := th) t n hi hadd
          exact ⟨_, _, TrapsQ.left (TrapsQ.left hT)⟩
        | some r =>
          obtain ⟨i, ι₂⟩ := r
          match rest, h with
          | [], .inl h' => exact absurd rfl (h' n)
          | [], .inr ⟨n', e, h'⟩ => rw [hadd] at h'; cases h'
          | x :: xs, _ =>
            apply Exists.intro; apply Exists.intro
            apply TrapsQ.bind (RunsQ.bind
              (f := fun x => (pure [i32Flat x] : Canon.P (E3 P) Unit (List FlatValue)))
              (runs_lowerOwn t n hi hadd) (.pure _ _))
            unfold lowerFlatTypes
            exact TrapsQ.left (TrapsQ.trap _ (isTrap_trap _))
      · rw [lowerFlatAt_own_other _ _ v (fun n e => hv ⟨n, e⟩)]
        exact ⟨_, _, TrapsQ.left (TrapsQ.trap _ (isTrap_trap _))⟩
  obtain ⟨trT, mT, hT⟩ := hp (ptrTypeIn m.store
    ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)))
  rw [lower_drop_eq]
  exact ⟨_, _, TrapsQ.bind (RunsQ.get (RunsQ.pure _ _)) hT⟩

end Silmaril.Wasm.Resource.CompToy
