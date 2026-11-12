module

public import Silmaril.Proofs.Wasm.Resource.CompToy.MakeCore
public import Silmaril.Wasm.Resource.Table.Thms

/-!
# The toy resource component: calls of `make`

`make() -> own<r>` lifts the core function `2`, at every profile `P`:

* `runs_lower_make`, `lower_make_traps`: the lowering of no arguments, and of any other
  argument list (a trap);
* `runs_newCallout`, `traps_newCallout`: the machine's program for a core callout to the canon
  built-in `resource.new` of the toy's instance (entry check, `may_leave`, `Table.add`), to its
  index or to the trap `tableFull`.

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

/-! ## Lowering no arguments -/

theorem lower_make_eq (cx : LiftLowerContext (E3 P)) (vs : List Silmaril.Wasm.Component.Reference.Val) :
    (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams vs (paramTypes ftMake) none :
      Canon.P (E3 P) Unit _) =
      ptrType cx >>= fun p => lowerFlatTypes Limits.spec Quirks.none cx p vs [] := by
  unfold lowerFlatValues
  congr 1
  funext p
  cases p <;> (rw [ite_eq_right_iff.mpr (by intro h; exact absurd h (by decide +kernel))]; rfl)

theorem runs_lower_make {th : Option ThreadId} (t : TaskId) (m : Machine.Config (E3 P) Unit) :
    RunsQ (D P) th (lowerFlatValues Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))
      ABI.maxFlatParams [] (paramTypes ftMake) none) m [.tau] [] m := by
  rw [lower_make_eq]
  exact .get (.pure _ _)

/-- Any argument list but `[]` makes the lowering of `make`'s arguments trap. -/
theorem lower_make_traps {th : Option ThreadId} (t : TaskId) (args : List Silmaril.Wasm.Component.Reference.Val) (hne : args ≠ [])
    (m : Machine.Config (E3 P) Unit) :
    ∃ trT mT, TrapsQ (D P) th (lowerFlatValues Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))
      ABI.maxFlatParams args (paramTypes ftMake) none) m trT mT := by
  obtain ⟨v, vs, rfl⟩ : ∃ v vs, args = v :: vs := by
    cases args with
    | nil => exact absurd rfl hne
    | cons v vs => exact ⟨v, vs, rfl⟩
  rw [lower_make_eq]
  exact ⟨_, _, TrapsQ.bind (RunsQ.get (RunsQ.pure _ _)) (TrapsQ.trap _ (isTrap_trap _))⟩

/-! ## The callout to `resource.new` -/

/-- The only instance of a store with one instance. -/
theorem insts_get₀ {s : CStore (E3 P)} {ι : InstState} (h : s.insts = [ι]) :
    ArenaField.insts.get? s ⟨0⟩ = some ι := by
  show s.insts[0]? = some ι
  rw [h]
  rfl

/-- The entry check passes for a built-in of instance `0` called from a thread of a task of
instance `0`. -/
theorem calloutEntry_builtin {s : CStore (E3 P)} {th : ThreadId} {thr : Runtime.Thread}
    {tk : Runtime.Task (E3 P)} {b : ResolvedBuiltin (E3 P)}
    (hthr : ArenaField.threads.get? s th = some thr)
    (htk : ArenaField.tasks.get? s thr.task = some tk) (hinst : tk.inst = ⟨0⟩) :
    calloutEntry s (some th) (.builtin b ⟨0⟩) = none := by
  simp [calloutEntry, instOfThread?, hthr, htk, hinst]

/-- The program of the current instance. -/
theorem runs_currentInst {th : ThreadId} {m : Machine.Config (E3 P) Unit} {thr : Runtime.Thread}
    {tk : Runtime.Task (E3 P)}
    (hthr : ArenaField.threads.get? m.store th = some thr)
    (htk : ArenaField.tasks.get? m.store thr.task = some tk) :
    ∃ tr, RunsQ (D P) (some th) currentInst m tr tk.inst m := by
  have h₁ : ∃ tr, RunsQ (D P) (some th) (currentTask? : Canon.P (E3 P) Unit (Option TaskId)) m tr
      (some thr.task) m := by
    unfold currentTask?
    exact ⟨_, RunsQ.bind (a := some th) (RunsQ.currentThread (RunsQ.pure _ _))
      (RunsQ.bind (runs_getObj ArenaField.threads _ _ hthr) (.pure _ _))⟩
  obtain ⟨tr₁, h₁⟩ := h₁
  have h₂ : ∃ tr, RunsQ (D P) (some th) (currentInst? : Canon.P (E3 P) Unit (Option InstId)) m tr
      (some tk.inst) m := by
    unfold currentInst?
    exact ⟨_, RunsQ.bind (a := some thr.task) h₁
      (RunsQ.bind (runs_getObj ArenaField.tasks _ _ htk) (.pure _ _))⟩
  obtain ⟨tr₂, h₂⟩ := h₂
  unfold currentInst
  exact ⟨_, RunsQ.bind (a := some tk.inst) h₂ (.pure _ _)⟩

/-- The entry of `resource.new`/`resource.drop` from a thread of instance `0` that may leave. -/
theorem runs_resourceEnter {th : ThreadId} {m : Machine.Config (E3 P) Unit} {thr : Runtime.Thread}
    {tk : Runtime.Task (E3 P)} {ι : InstState}
    (hthr : ArenaField.threads.get? m.store th = some thr)
    (htk : ArenaField.tasks.get? m.store thr.task = some tk) (hinst : tk.inst = ⟨0⟩)
    (hi : m.store.insts = [ι]) (hleave : ι.mayLeave = true) :
    ∃ tr, RunsQ (D P) (some th) Builtins.resourceEnter m tr ⟨0⟩ m := by
  have hgi : ArenaField.insts.get? m.store ⟨0⟩ = some ι := by
    exact insts_get₀ hi
  obtain ⟨tr₁, h₁⟩ := runs_currentInst hthr htk
  rw [hinst] at h₁
  unfold Builtins.resourceEnter
  exact ⟨_, RunsQ.bind (a := ⟨0⟩) h₁ (RunsQ.bind (runs_getObj ArenaField.insts _ _ hgi)
    (RunsQ.bind (runs_trapIf (by simp [hleave]) _ _) (.pure _ _)))⟩

/-- The store after `resource.new` of representation `rep` updated the instance to `ι'`. -/
def newSt (s : CStore (E3 P)) (rep : ℕ) (ι' : InstState) : CStore (E3 P) :=
  { s with insts := [ι'], resHandles := s.resHandles ++ [{ rt := ⟨0⟩, rep := rep, own := true }] }

/-- The core of `resource.new`, when the table has room. -/
theorem runs_newCore {th : ThreadId} {m : Machine.Config (E3 P) Unit} {ι ι' : InstState}
    {rep i : ℕ} (hi : m.store.insts = [ι])
    (hadd : ι.addHandle? (.resource ⟨m.store.resHandles.length⟩) = some (i, ι')) :
    ∃ tr, RunsQ (D P) (some th) (resourceNewCore Limits.spec ⟨0⟩ ⟨0⟩ rep) m tr i
      { m with store := newSt m.store rep ι' } := by
  let h : ResourceHandle := { rt := ⟨0⟩, rep := rep, own := true }
  let s₁ := ArenaOps.allocSt ArenaField.resHandles h m.store
  have hgi : ArenaField.insts.get? s₁ ⟨0⟩ = some ι := by
    exact insts_get₀ (s := s₁) hi
  have hadd' : ι.addHandle? (.resource ((ArenaField.resHandles (E := E3 P)).mkId
      ((ArenaField.resHandles (E := E3 P)).size m.store))) = some (i, ι') := hadd
  have hm : RunsQ (D P) (some th) (modifyInst ⟨0⟩ (InstState.addHandle (.resource
      ((ArenaField.resHandles (E := E3 P)).mkId ((ArenaField.resHandles (E := E3 P)).size m.store)))))
      { m with store := s₁ } [.tau] () { m with store := newSt m.store rep ι' } := by
    have e : ArenaOps.updateSt ArenaField.insts ⟨0⟩ (InstState.addHandle (.resource
        ((ArenaField.resHandles (E := E3 P)).mkId ((ArenaField.resHandles (E := E3 P)).size m.store)))) s₁ =
        newSt m.store rep ι' := by
      have hl : List.modify m.store.insts 0 (InstState.addHandle (.resource
          ((ArenaField.resHandles (E := E3 P)).mkId ((ArenaField.resHandles (E := E3 P)).size
            m.store)))) = [ι'] := by
        rw [hi, ← InstState.addHandle_eq hadd']
        rfl
      show ({ s₁ with insts := List.modify m.store.insts 0 _ } : CStore (E3 P)) = _
      rw [hl]
      rfl
    rw [← e]
    exact runs_modifyStore _ _ rfl
  unfold resourceNewCore addResHandle handlesAdd
  refine ⟨_, RunsQ.bind (tr₂ := [.tau] ++ ([.tau] ++ []))
    (runs_allocObj ArenaField.resHandles h m rfl)
    (RunsQ.bind (tr₂ := [.tau] ++ []) (runs_getObj ArenaField.insts _ { m with store := s₁ } hgi) ?_)⟩
  rw [hadd']
  exact RunsQ.bind hm (.pure _ _)

/-- **The callout to `resource.new`**, when the table has room: the handle object is
allocated, its index `i` is added to the instance's table, and the result is `[i32 i]`. -/
theorem runs_newCallout {th : ThreadId} {m : Machine.Config (E3 P) Unit} {thr : Runtime.Thread}
    {tk : Runtime.Task (E3 P)} {ι ι' : InstState} {a : FlatValue} {i : ℕ}
    (hthr : ArenaField.threads.get? m.store th = some thr)
    (htk : ArenaField.tasks.get? m.store thr.task = some tk) (hinst : tk.inst = ⟨0⟩)
    (hi : m.store.insts = [ι]) (hleave : ι.mayLeave = true)
    (hadd : ι.addHandle? (.resource ⟨m.store.resHandles.length⟩) = some (i, ι')) :
    ∃ tr, RunsQ (D P) (some th) (D P (.hostCallout (newH P) [a])) m tr (.flat [i32Flat i])
      { m with store := newSt m.store (flatNat a) ι' } := by
  have hentry := calloutEntry_builtin (b := .resourceNew ⟨0⟩ .i32) hthr htk hinst
  obtain ⟨tr₁, h₁⟩ := runs_resourceEnter hthr htk hinst hi hleave
  obtain ⟨tr₂, h₂⟩ := runs_newCore (th := th) (rep := flatNat a) hi hadd
  have hb : RunsQ (D P) (some th) (Builtins.resourceNew Limits.spec ⟨0⟩ (flatNat a)) m
      (tr₁ ++ (tr₂ ++ [])) [i32Flat i] { m with store := newSt m.store (flatNat a) ι' } := by
    unfold Builtins.resourceNew
    exact RunsQ.bind h₁ (RunsQ.bind h₂ (.pure _ _))
  refine ⟨_, RunsQ.currentThread (RunsQ.get (tr := tr₁ ++ (tr₂ ++ []) ++ []) ?_)⟩
  show RunsQ _ _ (match calloutEntry m.store (some th) (newH P) with
    | some r => trap r | none => _) _ _ _ _
  rw [hentry]
  exact RunsQ.bind hb (.pure _ _)

/-- **The callout to `resource.new` when the table is full** traps. -/
theorem traps_newCallout {th : ThreadId} {m : Machine.Config (E3 P) Unit} {thr : Runtime.Thread}
    {tk : Runtime.Task (E3 P)} {ι : InstState} {a : FlatValue}
    (hthr : ArenaField.threads.get? m.store th = some thr)
    (htk : ArenaField.tasks.get? m.store thr.task = some tk) (hinst : tk.inst = ⟨0⟩)
    (hi : m.store.insts = [ι]) (hleave : ι.mayLeave = true)
    (hadd : ι.addHandle? (.resource ⟨m.store.resHandles.length⟩) = none) :
    ∃ tr mT, TrapsQ (D P) (some th) (D P (.hostCallout (newH P) [a])) m tr mT := by
  have hentry := calloutEntry_builtin (b := .resourceNew ⟨0⟩ .i32) hthr htk hinst
  obtain ⟨tr₁, h₁⟩ := runs_resourceEnter hthr htk hinst hi hleave
  let h : ResourceHandle := { rt := ⟨0⟩, rep := flatNat a, own := true }
  let s₁ := ArenaOps.allocSt ArenaField.resHandles h m.store
  have hgi : ArenaField.insts.get? s₁ ⟨0⟩ = some ι := by
    exact insts_get₀ (s := s₁) hi
  have hadd' : ι.addHandle? (.resource ((ArenaField.resHandles (E := E3 P)).mkId
      ((ArenaField.resHandles (E := E3 P)).size m.store))) = none := hadd
  have hcore : ∃ tr mT, TrapsQ (D P) (some th) (resourceNewCore Limits.spec ⟨0⟩ ⟨0⟩ (flatNat a)) m
      tr mT := by
    unfold resourceNewCore addResHandle handlesAdd
    refine ⟨_, { m with store := s₁ }, TrapsQ.bind (tr₂ := [.tau] ++ [])
      (runs_allocObj ArenaField.resHandles h m rfl)
      (TrapsQ.bind (tr₂ := []) (runs_getObj ArenaField.insts _ { m with store := s₁ } hgi) ?_)⟩
    rw [hadd']
    exact TrapsQ.trap _ (isTrap_trap _)
  obtain ⟨tr₂, mT, h₂⟩ := hcore
  have hb : TrapsQ (D P) (some th) (Builtins.resourceNew Limits.spec ⟨0⟩ (flatNat a)) m
      (tr₁ ++ tr₂) mT := by
    unfold Builtins.resourceNew
    exact TrapsQ.bind h₁ (TrapsQ.left h₂)
  refine ⟨_, mT, TrapsQ.bind (RunsQ.currentThread (RunsQ.pure _ _))
    (TrapsQ.bind (tr₂ := tr₁ ++ tr₂) (RunsQ.get (RunsQ.pure _ _)) ?_)⟩
  show TrapsQ _ _ (match calloutEntry m.store (some th) (newH P) with
    | some r => trap r | none => _) _ _ _
  rw [hentry]
  exact TrapsQ.left hb

/-! ## Handle tables -/

/-- `add?` keeps `TabB` and returns an index below `2^32`. -/
theorem add?_tabB {t t' : Silmaril.Wasm.Component.Runtime.Table HandleEntry} {e : HandleEntry} {i : ℕ} (hb : TabB t)
    (h : t.add? e = some (i, t')) : i < 2 ^ 32 ∧ TabB t' ∧ AddRes t t' e i := by
  have hr := add?_fresh hb.1 h
  obtain ⟨arr, fr⟩ := t
  have hm : Table.maxLength < 2 ^ 32 := by decide
  cases fr with
  | cons k fr =>
    have h' : k = i ∧ (⟨arr.setIfInBounds k (some e), fr⟩ : Silmaril.Wasm.Component.Runtime.Table HandleEntry) = t' := by
      simpa [Table.add?] using h
    obtain ⟨rfl, rfl⟩ := h'
    have hk : arr[k]? = some none := hb.1.1 k (by simp)
    have hlt : k < arr.size := lt_of_getElem?_eq_some hk
    have hs : arr.size ≤ Table.maxLength + 1 := hb.2
    exact ⟨by omega, ⟨hr.2.2.2, by simpa using hs⟩, hr⟩
  | nil =>
    have hs : arr.size ≤ Table.maxLength ∧ arr.size = i ∧
        (⟨arr.push (some e), []⟩ : Silmaril.Wasm.Component.Runtime.Table HandleEntry) = t' := by
      simp only [Table.add?] at h
      split at h <;> simp_all
    obtain ⟨hs, rfl, rfl⟩ := hs
    exact ⟨by omega, ⟨hr.2.2.2, by simp; omega⟩, hr⟩

/-- `remove?` keeps `TabB`. -/
theorem remove?_tabB {t t' : Silmaril.Wasm.Component.Runtime.Table HandleEntry} {e : HandleEntry} {i : ℕ} (hb : TabB t)
    (h : t.remove? i = some (e, t')) : TabB t' ∧ RemoveRes t t' e i := by
  have hr := remove?_live hb.1 h
  obtain ⟨-, rfl⟩ := remove?_parts h
  exact ⟨⟨hr.2.2.2, by simpa using hb.2⟩, hr⟩

/-! ## The core phase of `make` -/

/-- The frames of `make`'s core phase: the call's configuration `M₀` with the instance `ι'`
holding the handle table `T`, the handle objects `Hs` and the core store `cs`. -/
def mkB (M₀ : Machine.Config (E3 P) Unit) (ι' : InstState) (T : Silmaril.Wasm.Component.Runtime.Table HandleEntry)
    (Hs : List ResourceHandle) (cs : (E3 P).Store (CanonHost (E3 P))) : Machine.Config (E3 P) Unit :=
  { M₀ with
    store := { M₀.store with
      core := cs
      insts := [{ ι' with handles := T }]
      resHandles := Hs } }

/-- The table `T` extends `T₀`, and every entry not live in `T₀` is an own handle of
representation `c`. -/
def NewOwn (T₀ T : Silmaril.Wasm.Component.Runtime.Table HandleEntry) (Hs : List ResourceHandle) (c : ℕ) : Prop :=
  (∀ j e, T₀.get? j = some e → T.get? j = some e) ∧
  ∀ j e, T.get? j = some e → T₀.get? j = none →
    ∃ hid : HandleObjId, e = .resource hid ∧ Hs[hid.idx]? = some { rt := ⟨0⟩, rep := c, own := true }

/-- The invariant of `make`'s core phase. -/
def MkInv (M₀ : Machine.Config (E3 P) Unit) (ι' : InstState) (c : ℕ) (B : Machine.Config (E3 P) Unit) :
    Prop :=
  ∃ T Hs cs, B = mkB M₀ ι' T Hs cs ∧ TabB T ∧ NewOwn ι'.handles T Hs c

/-- The indices `make` may return: below `2^32` and not live at the start of the call. -/
def Jmake (T₀ : Silmaril.Wasm.Component.Runtime.Table HandleEntry) (j : ℕ) : Prop := j < 2 ^ 32 ∧ T₀.get? j = none

theorem newOwn_refl (T₀ : Silmaril.Wasm.Component.Runtime.Table HandleEntry) (Hs : List ResourceHandle) (c : ℕ) :
    NewOwn T₀ T₀ Hs c :=
  ⟨fun _ _ h => h, fun _ _ h h' => absurd (h.symm.trans h') (by simp)⟩

/-- An added handle keeps `NewOwn`. -/
theorem newOwn_add {T₀ T T' : Silmaril.Wasm.Component.Runtime.Table HandleEntry} {Hs : List ResourceHandle} {c i : ℕ}
    (hn : NewOwn T₀ T Hs c) (hr : AddRes T T' (.resource ⟨Hs.length⟩) i) :
    NewOwn T₀ T' (Hs ++ [{ rt := ⟨0⟩, rep := c, own := true }]) c := by
  obtain ⟨hfresh, hnew, hframe, -⟩ := hr
  refine ⟨fun j e h => ?_, fun j e h h₀ => ?_⟩
  · have hT := hn.1 j e h
    have hji : j ≠ i := fun hji => by rw [hji, hfresh] at hT; cases hT
    rw [hframe j hji]
    exact hT
  · by_cases hji : j = i
    · subst hji
      rw [hnew] at h
      cases h
      exact ⟨⟨Hs.length⟩, rfl, by simp⟩
    · rw [hframe j hji] at h
      obtain ⟨hid, rfl, hh⟩ := hn.2 j e h h₀
      have hlt : hid.idx < Hs.length := by
        by_contra hc
        simp [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hh
      exact ⟨hid, rfl, by rw [List.getElem?_append_left hlt]; exact hh⟩

theorem flatNat_i32 {c : ℕ} (hc : c < 2 ^ 32) : flatNat (.int .i32 (BitVec.ofNat 32 c)) = c := by
  show (BitVec.ofNat 32 c).toNat = c
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hc

/-- A callout that the host relation of `make` answers is to `resource.new` on the counter. -/
theorem hnew_inv {c : ℕ} {J : ℕ → Prop} {h : CanonHost (E3 P)}
    {s : (E3 P).Store (CanonHost (E3 P))} {args : List Silmaril.Wasm.Execution.Core.Val}
    {o : Silmaril.Wasm.Execution.Host.Outcome (Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P)))
      Silmaril.Wasm.Execution.Core.Result}
    (ho : Hnew P c J h s args o) : h = newH P ∧ args = [.i32 (BitVec.ofNat 32 c)] := by
  obtain ⟨S, hS, hpre, -⟩ := ho
  have hh : h = newH P := by
    by_contra hne
    have h0 : toyBind P h ≠ 0 := by
      unfold toyBind
      split_ifs <;> simp_all
    simp [Γnew, h0] at hS
  subst hh
  rw [toyBind_new] at hS
  obtain rfl : newSpec P c J = S := Option.some.inj hS
  exact ⟨rfl, hpre⟩

/-- The flat arguments of a callout of the core thread are those of its redex. -/
theorem callout_args {x : CoreSt (E3 P)} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : ℕ}
    {h : CanonHost (E3 P)} {args : List Silmaril.Wasm.Execution.Core.Val} {ys : List FlatValue}
    (hd : Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, h, args))
    (hst : (E3 P).status x.1 x.2 = .callout h ys) :
    args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys := by
  obtain ⟨E', a', args', hd', hm⟩ := status_callout_redex hst
  rw [hd] at hd'
  cases hd'
  exact hm

/-- **The callouts of `make`'s core phase** are run by the machine as the host relation of
`make` allows: `resource.new` on the counter adds an own handle of representation `c` at a
fresh index below `2^32` (or traps when the table is full). -/
theorem make_calloutsAns {prof : ProfileKind} {M₀ : Machine.Config (E3 P) Unit} {ι' : InstState}
    {c : ℕ} {th : ThreadId} {thr : Runtime.Thread} {tk : Runtime.Task (E3 P)}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} (hc : c < 2 ^ 32)
    (hthr : ArenaField.threads.get? M₀.store th = some thr)
    (htk : ArenaField.tasks.get? M₀.store thr.task = some tk) (hinst : tk.inst = ⟨0⟩)
    (hl : M₀.store.lockdown = false) (hleave : ι'.mayLeave = true) :
    CalloutsAns (prof := prof) (Hnew P c (Jmake ι'.handles)) (MkInv M₀ ι' c) (some th) K segs
      rest := by
  rintro B x E a h args ys o ⟨T, Hs, cs, rfl, hTB, hn⟩ hd hst ho
  obtain ⟨rfl, rfl⟩ := hnew_inv ho
  have hys : ys = [.int .i32 (BitVec.ofNat 32 c)] := by
    have hm := callout_args hd hst
    have e : ([.i32 (BitVec.ofNat 32 c)] : List Silmaril.Wasm.Execution.Core.Val).mapM
        Silmaril.Wasm.SingleThreaded.toFlat? = some [.int .i32 (BitVec.ofNat 32 c)] := rfl
    exact (Option.some.inj (hm.symm.trans e))
  subst hys
  let m := calloutCfg (mkB M₀ ι' T Hs cs) (some th) K segs rest x (newH P)
    [.int .i32 (BitVec.ofNat 32 c)]
  have hi : m.store.insts = [{ ι' with handles := T }] := rfl
  cases hadd : T.add? (.resource ⟨Hs.length⟩) with
  | none =>
    right
    have hadd' : InstState.addHandle? (.resource ⟨m.store.resHandles.length⟩)
        { ι' with handles := T } = none := by
      simp [InstState.addHandle?, m, mkB, coreCfg, hadd]
    obtain ⟨trT, mT, hT⟩ := traps_newCallout (m := m) hthr htk hinst hi hleave hadd'
    exact builtin_traps hl hst hT
  | some p =>
    obtain ⟨i, T'⟩ := p
    left
    obtain ⟨hi32, hTB', hr⟩ := add?_tabB hTB hadd
    have hadd' : InstState.addHandle? (.resource ⟨m.store.resHandles.length⟩)
        { ι' with handles := T } = some (i, { ι' with handles := T' }) := by
      simp [InstState.addHandle?, m, mkB, coreCfg, hadd]
    obtain ⟨tr, hrun⟩ := runs_newCallout (m := m) hthr htk hinst hi hleave hadd'
    rw [flatNat_i32 hc] at hrun
    have hfree : ι'.handles.get? i = none := by
      cases h₀ : ι'.handles.get? i with
      | none => rfl
      | some e => exact absurd (hr.1.symm.trans (hn.1 i e h₀)) (by simp)
    refine ⟨mkB M₀ ι' T' (Hs ++ [{ rt := ⟨0⟩, rep := c, own := true }]) x.1, [i32Flat i], tr ++ [.tau],
      ⟨T', _, x.1, rfl, hTB', newOwn_add hn hr⟩, ⟨newSpec P c (Jmake ι'.handles), by rw [toyBind_new]; rfl, rfl, rfl, i, ⟨hi32, hfree⟩,
        rfl⟩, ?_⟩
    exact builtin_lrun hl hst hl rfl hrun

/-! ## Lifting the `own` result -/

theorem lift_make_eq (cx : LiftLowerContext (E3 P)) (vi : FlatCursor) :
    (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults vi (resultTypes ftMake) :
      Canon.P (E3 P) Unit _) =
      ptrType cx >>= fun p => liftFlatTypes Limits.spec Quirks.none cx p [.own ⟨0⟩] vi := by
  unfold liftFlatValues
  congr 1
  funext p
  cases p <;> (rw [ite_eq_right_iff.mpr (by intro h; exact absurd h (by decide +kernel))]; rfl)

/-- The program of `liftOwn` up to the removal from the table. -/
theorem liftOwn_eq (cx : LiftLowerContext (E3 P)) (rt : RtId) (i : ℕ) :
    (liftOwn Limits.spec cx rt i : Canon.P (E3 P) Unit ℕ) =
      handlesRemove cx.inst i >>= fun e => (expectResource e >>= fun hid => getResHandle hid >>=
        fun h => trapIf (h.rt != rt) .resourceTypeMismatch >>= fun _ =>
          trapIf (h.numLends != 0) .ownLent >>= fun _ => trapIf (!h.own) .notOwnHandle >>=
            fun _ => pure h.rep) := by
  unfold liftOwn
  rfl

/-- The lift of `[i32 j]` at `own<r>` with `j` an own handle of representation `c` in the
instance's table: the handle is removed and the result is `own c`. -/
theorem runs_lift_make {th : Option ThreadId} (t : TaskId) {m : Machine.Config (E3 P) Unit}
    {ι₁ ι₂ : InstState} {j : ℕ} {hid : HandleObjId} {c : ℕ} (hj : j < 2 ^ 32)
    (hins : m.store.insts = [ι₁])
    (hrem : ι₁.removeHandle? j = some (.resource hid, ι₂))
    (hH : ArenaField.resHandles.get? m.store hid = some { rt := ⟨0⟩, rep := c, own := true }) :
    RunsQ (D P) th (liftFlatValues Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))
      ABI.maxFlatResults (.ofList [.int .i32 (BitVec.ofNat 32 j)]) (resultTypes ftMake)) m
      [.tau, .tau, .tau, .tau] ([.own c], ⟨[.int .i32 (BitVec.ofNat 32 j)], 1⟩)
      { m with store := { m.store with insts := [ι₂] } } := by
  have hgi : ArenaField.insts.get? m.store ⟨0⟩ = some ι₁ := by
    exact insts_get₀ hins
  have hst : ArenaOps.updateSt ArenaField.insts ⟨0⟩ (InstState.removeHandle j) m.store =
      { m.store with insts := [ι₂] } := by
    have hl : List.modify m.store.insts 0 (InstState.removeHandle j) = [ι₂] := by
      rw [hins]
      simp [InstState.removeHandle, hrem]
    show ({ m.store with insts := List.modify m.store.insts 0 _ } : CStore (E3 P)) = _
    rw [hl]
  have hrm : RunsQ (D P) th (handlesRemove ⟨0⟩ j) m ([.tau] ++ ([.tau] ++ []))
      (.resource hid) { m with store := { m.store with insts := [ι₂] } } := by
    unfold handlesRemove
    refine RunsQ.bind (runs_getObj ArenaField.insts _ m hgi) ?_
    rw [hrem]
    rw [← hst]
    exact RunsQ.bind (runs_modifyStore _ _ rfl) (.pure _ _)
  have hH' : ArenaField.resHandles.get? { m.store with insts := [ι₂] } hid =
      some { rt := ⟨0⟩, rep := c, own := true } := hH
  have hown : RunsQ (D P) th (liftOwn Limits.spec
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)) ⟨0⟩ j) m
      (([.tau] ++ ([.tau] ++ [])) ++ ([] ++ ([.tau] ++ ([] ++ ([] ++ ([] ++ []))))))
      c { m with store := { m.store with insts := [ι₂] } } := by
    rw [liftOwn_eq]
    exact RunsQ.bind hrm (RunsQ.bind (.pure _ _) (RunsQ.bind
      (runs_getObj ArenaField.resHandles _ _ hH') (RunsQ.bind (runs_trapIf rfl _ _)
        (RunsQ.bind (runs_trapIf rfl _ _) (RunsQ.bind (runs_trapIf rfl _ _) (.pure _ _))))))
  rw [lift_make_eq]
  have hjn : flatNat (.int .i32 (BitVec.ofNat 32 j)) = j := flatNat_i32 hj
  have hat : ∀ p, RunsQ (D P) th (liftFlatAt Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)) p (.own ⟨0⟩)
      (.ofList [.int .i32 (BitVec.ofNat 32 j)])) m
      ([] ++ ((([.tau] ++ ([.tau] ++ [])) ++ ([] ++ ([.tau] ++ ([] ++ ([] ++ ([] ++ [])))))) ++ []))
      (.own c, ⟨[.int .i32 (BitVec.ofNat 32 j)], 1⟩)
      { m with store := { m.store with insts := [ι₂] } } := by
    intro p
    rw [liftFlatAt.eq_def]
    refine RunsQ.bind (RunsQ.pure _ _) ?_
    show RunsQ _ _ (liftOwn Limits.spec _ ⟨0⟩ (flatNat (.int .i32 (BitVec.ofNat 32 j))) >>= _) _ _ _ _
    rw [hjn]
    exact RunsQ.bind hown (.pure _ _)
  refine RunsQ.get ?_
  show RunsQ _ _ (liftFlatTypes Limits.spec Quirks.none _ (ptrTypeIn m.store
    ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))) [.own ⟨0⟩]
    (.ofList [.int .i32 (BitVec.ofNat 32 j)])) _ _ _ _
  unfold liftFlatTypes
  apply RunsQ.of_tr
  · refine RunsQ.bind (tr₂ := [] ++ []) (hat _) ?_
    unfold liftFlatTypes
    exact RunsQ.bind (.pure _ _) (.pure _ _)
  · rfl

/-- The lift of `[i32 j]` at `own<r>` traps when `j` is not live in the instance's table. -/
theorem traps_lift_make {th : Option ThreadId} (t : TaskId) {m : Machine.Config (E3 P) Unit}
    {ι₁ : InstState} {j : ℕ} (hj : j < 2 ^ 32) (hins : m.store.insts = [ι₁])
    (hrem : ι₁.removeHandle? j = none) :
    ∃ tr mT, TrapsQ (D P) th (liftFlatValues Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))
      ABI.maxFlatResults (.ofList [.int .i32 (BitVec.ofNat 32 j)]) (resultTypes ftMake)) m tr mT := by
  have hgi : ArenaField.insts.get? m.store ⟨0⟩ = some ι₁ := by
    exact insts_get₀ hins
  have h₁ : TrapsQ (D P) th (handlesRemove ⟨0⟩ j) m ([.tau] ++ []) m := by
    unfold handlesRemove
    refine TrapsQ.bind (runs_getObj ArenaField.insts _ m hgi) ?_
    rw [hrem]
    exact TrapsQ.trap _ (isTrap_trap _)
  have h₂ : TrapsQ (D P) th (liftOwn Limits.spec
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P)) ⟨0⟩ j) m
      ([.tau] ++ []) m := by
    rw [liftOwn_eq]
    exact TrapsQ.left h₁
  have hjn : flatNat (.int .i32 (BitVec.ofNat 32 j)) = j := flatNat_i32 hj
  rw [lift_make_eq]
  exact ⟨_, _, TrapsQ.bind (RunsQ.get (RunsQ.pure _ _)) (by
    show TrapsQ _ _ (liftFlatTypes Limits.spec Quirks.none _ (ptrTypeIn m.store
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 P))) [.own ⟨0⟩]
      (.ofList [.int .i32 (BitVec.ofNat 32 j)])) _ _ _
    unfold liftFlatTypes
    rw [liftFlatAt.eq_def]
    dsimp only
    exact TrapsQ.left (TrapsQ.bind (RunsQ.pure _ _) (TrapsQ.left (hjn ▸ h₂))))⟩

end Silmaril.Wasm.Resource.CompToy
