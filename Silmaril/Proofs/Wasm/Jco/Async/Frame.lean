module

public import Silmaril.Wasm.Jco.Async.Frame.Defs
public import Silmaril.Wasm.Jco.Basic.Thms

/-!
# A closed form of the async specification: proofs

Proofs of `Silmaril.Wasm.Jco.Async.Frame.Thms`.

* `RM.liftFst` commutes with the monad operations (`liftFst_pure`, `liftFst_bind`, …), and the
  memory operations of `M.withStore` are those of `M` lifted (`load_withStore`,
  `store_withStore`). Hence the C convention over `M.withStore` is the lifted C convention
  (`specCall_withStore`): the frame lemma.
* `startTask_bind`: the runtime's task creation is a deterministic update of the store.
* `tail_iff`: after `M` returned `r`, the rest of an async call (`task.return` of the fresh task,
  reading back its results) is deterministic, with outcome `tailOut`.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Frame

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store startSync)

variable {σ τ α β : Type}

/-! ## `RM.liftFst` and the monad -/

theorem liftFst_pure (a : α) : RM.liftFst (τ := τ) (pure a : RM σ α) = pure a := by
  funext s o
  apply propext
  cases o with
  | ok b s' =>
    simp only [RM.liftFst, RM.pure_apply, Out.ok.injEq]
    constructor
    · rintro ⟨h2, rfl, h1⟩
      exact ⟨rfl, Prod.ext h1 h2⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
  | trap => simp [RM.liftFst, RM.pure_apply]

theorem liftFst_fail : RM.liftFst (τ := τ) (RM.fail : RM σ α) = RM.fail := by
  funext s o
  cases o <;> simp [RM.liftFst, RM.fail]

theorem liftFst_bind (m : RM σ α) (k : α → RM σ β) :
    RM.liftFst (τ := τ) (m >>= k) = (RM.liftFst m >>= fun a => RM.liftFst (k a)) := by
  funext s o
  apply propext
  cases o with
  | ok b s' =>
    simp only [RM.liftFst, RM.bind_apply, reduceCtorEq, and_false, or_false]
    constructor
    · rintro ⟨h2, a, s1, h1, hk⟩
      exact ⟨a, (s1, s.2), ⟨rfl, h1⟩, h2, hk⟩
    · rintro ⟨a, p, ⟨hp, h1⟩, h2, hk⟩
      exact ⟨h2.trans hp, a, p.1, h1, hk⟩
  | trap =>
    simp only [RM.liftFst, RM.bind_apply, and_true]
    constructor
    · rintro (⟨a, s1, h1, hk⟩ | h)
      · exact .inl ⟨a, (s1, s.2), ⟨rfl, h1⟩, hk⟩
      · exact .inr h
    · rintro (⟨a, p, ⟨-, h1⟩, hk⟩ | h)
      · exact .inl ⟨a, p.1, h1, hk⟩
      · exact .inr h

theorem liftFst_ofOption (x : Option α) :
    RM.liftFst (τ := τ) (RM.ofOption x : RM σ α) = RM.ofOption x := by
  cases x
  · exact liftFst_fail
  · exact liftFst_pure _

theorem liftFst_check (b : Bool) : RM.liftFst (τ := τ) (RM.check b : RM σ Unit) = RM.check b := by
  cases b
  · exact liftFst_fail
  · exact liftFst_pure _

/-! ## The instance next to the store -/

variable (M : CoreInst)

theorem withStore_call (n : String) (xs : List Flat) :
    M.withStore.call n xs = RM.liftFst (M.call n xs) := rfl

theorem get_bind (f : σ → RM σ α) : (RM.get >>= f) = fun s => f s s := by
  funext s o
  apply propext
  simp only [RM.bind_apply, RM.get]
  constructor
  · rintro (⟨a, s', ⟨⟩, h⟩ | ⟨⟨⟩, -⟩)
    exact h
  · intro h
    exact .inl ⟨s, s, rfl, h⟩

theorem liftFst_get_bind (f : σ → RM σ α) :
    RM.liftFst (τ := τ) (RM.get >>= f) = (RM.get >>= fun p => RM.liftFst (f p.1)) := by
  rw [get_bind, get_bind]
  funext s o
  cases o <;> rfl

theorem load_withStore (a n : Nat) : M.withStore.load a n = RM.liftFst (M.load a n) := by
  show ((RM.get : RM (M.St × Store) _) >>= fun p => RM.ofOption ((M.mem p.1).read a n)) = _
  rw [CoreInst.load, liftFst_get_bind]
  simp only [liftFst_ofOption]

theorem store_withStore (a : Nat) (bs : List UInt8) :
    M.withStore.store a bs = RM.liftFst (M.store a bs) := by
  show ((RM.get : RM (M.St × Store) _) >>= fun p => RM.ofOption ((M.mem p.1).write a bs) >>= fun m =>
    RM.set ((M.setMem p.1 m, p.2) : M.St × Store)) = _
  rw [CoreInst.store, liftFst_get_bind, get_bind, get_bind]
  funext s o
  rcases h : (M.mem s.1).write a bs with _ | m
  · simp only [RM.ofOption_none, RM.fail_bind, liftFst_fail]
  · simp only [RM.ofOption_some, RM.pure_bind]
    cases o <;> simp [RM.liftFst, RM.set, Prod.ext_iff, and_comm]

/-! ## The frame lemma -/

variable (md : Meta)

theorem specBytes_withStore (lim : Nat) (bs : List UInt8) :
    md.specBytes M.withStore lim bs = RM.liftFst (md.specBytes M lim bs) := by
  simp only [Meta.specBytes, liftFst_bind, liftFst_check, liftFst_ofOption, liftFst_pure,
    withStore_call, store_withStore]
  rfl

theorem specParam_withStore (t : PTy) (v : PVal) :
    md.specParam M.withStore t v = RM.liftFst (md.specParam M t v) := by
  cases t <;> cases v <;>
    simp only [Meta.specParam, liftFst_bind, liftFst_check, liftFst_pure, liftFst_fail,
      specBytes_withStore] <;> rfl

theorem specParams_withStore : ∀ (ts : List PTy) (vs : List PVal),
    md.specParams M.withStore ts vs = RM.liftFst (md.specParams M ts vs)
  | [], [] => (liftFst_pure _).symm
  | [], _ :: _ => liftFst_fail.symm
  | _ :: _, [] => liftFst_fail.symm
  | t :: ts, v :: vs => by
    simp only [Meta.specParams, liftFst_bind, liftFst_pure, specParam_withStore,
      specParams_withStore ts vs]
    rfl

theorem readPair_withStore (rp : BitVec 32) :
    readPair M.withStore rp = RM.liftFst (readPair M rp) := by
  simp only [readPair, liftFst_bind, liftFst_check, liftFst_ofOption, load_withStore]
  rfl

theorem liftResult_withStore (r : Option PTy) (xs : List Flat) :
    liftResult M.withStore r xs = RM.liftFst (liftResult M r xs) := by
  unfold liftResult
  split <;> (try split) <;>
    simp only [liftFst_bind, liftFst_pure, liftFst_fail, liftFst_ofOption, readPair_withStore] <;> rfl

/-- **The frame lemma**: the C convention over `M.withStore` is the lifted C convention. -/
theorem specCall_withStore (sig : Sig) (vs : List PVal) :
    md.specCall M.withStore sig vs = RM.liftFst (md.specCall M sig vs) := by
  unfold Meta.specCall
  cases inMem sig.result <;>
    simp only [Bool.false_eq_true, ↓reduceIte, liftFst_bind, liftFst_ofOption,
      specParams_withStore, withStore_call, liftResult_withStore] <;> rfl

/-! ## Results of the C convention -/

/-- The values `task.return` receives for `r` read back as `r` at the result type `res`. -/
@[expose] def ResOk (res : Option PTy) (r : Option PVal) : Prop :=
  ∀ ws, resVals r = some ws → valsRes res ws = some r

theorem liftResult_resOk (res : Option PTy) (xs : List Flat) :
    RM.Returns (liftResult M res xs) (ResOk res) := by
  unfold liftResult
  split
  · exact RM.returns_pure (by intro ws h; cases h; rfl)
  · split
    · exact RM.returns_pure (by intro ws h; cases h; rfl)
    · exact RM.returns_fail
  · refine RM.returns_bind (RM.returns_true _) fun _ _ => RM.returns_bind (RM.returns_true _)
      fun _ _ => RM.returns_bind (RM.returns_true _) fun _ _ => RM.returns_pure ?_
    intro ws h
    cases h
  · refine RM.returns_bind (RM.returns_true _) fun _ _ => RM.returns_bind (RM.returns_true _)
      fun _ _ => RM.returns_pure ?_
    intro ws h
    cases h
  · exact RM.returns_fail

theorem specCall_resOk (sig : Sig) (vs : List PVal) :
    RM.Returns (md.specCall M sig vs) (ResOk sig.result) := by
  unfold Meta.specCall
  refine RM.returns_bind (RM.returns_true _) fun xs _ => ?_
  split
  · exact RM.returns_bind (RM.returns_true _) fun _ _ => RM.returns_bind (RM.returns_true _)
      fun _ _ => RM.returns_bind (RM.returns_true _) fun _ _ => liftResult_resOk M _ _
  · exact RM.returns_bind (RM.returns_true _) fun _ _ => liftResult_resOk M _ _

/-- A string or list result is outside the async fragment. -/
theorem liftResult_inMem (res : Option PTy) (h : inMem res = true) (xs : List Flat) :
    RM.Returns (liftResult M res xs) (fun r => resVals r = none) := by
  unfold liftResult
  split
  · cases h
  · cases h
  · exact RM.returns_bind (RM.returns_true _) fun _ _ => RM.returns_bind (RM.returns_true _)
      fun _ _ => RM.returns_bind (RM.returns_true _) fun _ _ => RM.returns_pure rfl
  · exact RM.returns_bind (RM.returns_true _) fun _ _ => RM.returns_bind (RM.returns_true _)
      fun _ _ => RM.returns_pure rfl
  · exact RM.returns_fail

theorem specCall_inMem (sig : Sig) (h : inMem sig.result = true) (vs : List PVal) :
    RM.Returns (md.specCall M sig vs) (fun r => resVals r = none) := by
  unfold Meta.specCall
  refine RM.returns_bind (RM.returns_true _) fun xs _ => ?_
  simp only [h, ↓reduceIte]
  exact RM.returns_bind (RM.returns_true _) fun _ _ => RM.returns_bind (RM.returns_true _)
    fun _ _ => RM.returns_bind (RM.returns_true _) fun _ _ => liftResult_inMem M _ h _

/-! ## The runtime's part of an async call -/

theorem set_bind (x : σ) (f : Unit → RM σ α) : (RM.set x >>= f) = fun _ => f () x := by
  funext s o
  apply propext
  simp only [RM.bind_apply, RM.set]
  constructor
  · rintro (⟨a, s', ⟨⟩, h⟩ | ⟨⟨⟩, -⟩)
    exact h
  · intro h
    exact .inl ⟨(), x, rfl, h⟩

theorem liftFst_bind_apply (m : RM σ α) (k : α → RM (σ × τ) β) (p : σ × τ) (o : Out (σ × τ) β) :
    (RM.liftFst m >>= k) p o ↔ (∃ a x', m p.1 (.ok a x') ∧ k a (x', p.2) o) ∨
      (m p.1 .trap ∧ o = .trap) := by
  simp only [RM.bind_apply, RM.liftFst]
  constructor
  · rintro (⟨a, q, ⟨hq, h1⟩, hk⟩ | h)
    · refine .inl ⟨a, q.1, h1, ?_⟩
      rw [← hq]
      exact hk
    · exact .inr h
  · rintro (⟨a, x', h1, hk⟩ | h)
    · exact .inl ⟨a, (x', p.2), ⟨rfl, h1⟩, hk⟩
    · exact .inr h

theorem liftFst_bind_apply_ws (m : RM M.St α) (k : α → RM M.withStore.St β) (p : M.withStore.St)
    (o : Out M.withStore.St β) :
    ((RM.liftFst m : RM M.withStore.St α) >>= k) p o ↔ (∃ a x', m p.1 (.ok a x') ∧ k a (x', p.2) o) ∨
      (m p.1 .trap ∧ o = .trap) :=
  liftFst_bind_apply m k p o

theorem startTask_bind (k : Nat → RM M.withStore.St β) :
    (startTask M >>= k) = fun s => k s.2.next (s.1, (startSync s.2).1) := by
  unfold startTask
  simp only [RM.bind_assoc]
  rw [get_bind]
  funext s
  simp only [RM.pure_bind]
  erw [set_bind]
  rfl

theorem builtin_bind (op : Silmaril.Wasm.Component.Async.Op)
    (k : Silmaril.Wasm.Component.Async.Res → RM M.withStore.St β) :
    (builtin M op >>= k) = fun s =>
      match Silmaril.Wasm.Component.Async.step s.2 op with
      | some p => k p.2 (s.1, p.1)
      | none => RM.fail s := by
  unfold builtin
  simp only [RM.bind_assoc]
  rw [get_bind]
  funext s
  cases Silmaril.Wasm.Component.Async.step s.2 op with
  | none => simp only [RM.ofOption_none, RM.fail_bind]
  | some p =>
    simp only [RM.ofOption_some, RM.pure_bind]
    erw [set_bind]

theorem taskResult_bind (t : Nat) (k : List Val → RM M.withStore.St β) :
    (taskResult M t >>= k) = fun s =>
      match (s.2.tasks t).result with
      | some ws => k ws s
      | none => RM.fail s := by
  unfold taskResult
  simp only [RM.bind_assoc]
  rw [get_bind]
  funext s
  cases (s.2.tasks t).result with
  | none => simp only [RM.ofOption_none, RM.fail_bind]
  | some ws => simp only [RM.ofOption_some, RM.pure_bind]

/-- `task.return` on the fresh task succeeds and stores its values. -/
theorem step_fresh (st : Store) (ws : List Val) :
    ∃ st', Silmaril.Wasm.Component.Async.step (startSync st).1 (.taskReturn st.next ws) =
      some (st', .unit) ∧ (st'.tasks st.next).result = some ws ∧ asyncStore st ws = st' := by
  have hres : ((startSync st).1.tasks st.next).result = none := by
    simp [startSync, Silmaril.Wasm.Component.Async.upd]
  rcases hs : Silmaril.Wasm.Component.Async.step (startSync st).1 (.taskReturn st.next ws) with
    _ | ⟨st', r⟩
  · simp only [Silmaril.Wasm.Component.Async.step, hres, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte] at hs
    split at hs <;> cases hs
  · have hst : asyncStore st ws = st' := by
      show (retStore (startSync st).1 st.next ws).getD _ = st'
      simp [retStore, hs]
    have hs' := hs
    simp only [Silmaril.Wasm.Component.Async.step, hres, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte] at hs'
    split at hs' <;>
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      exact ⟨_, rfl, by simp [Silmaril.Wasm.Component.Async.Store.post, Silmaril.Wasm.Component.Async.upd],
        hst⟩

/-- The rest of an async call after `M` returned `r`. -/
@[expose] def tail (t : Nat) (res : Option PTy) (r : Option PVal) : RM M.withStore.St (Option PVal) := do
  let ws ← RM.ofOption (resVals r)
  let _ ← builtin M (.taskReturn t ws)
  let ws' ← taskResult M t
  RM.ofOption (valsRes res ws')

/-- Its outcome. -/
@[expose] def tailOut (st : Store) (x : M.St) (r : Option PVal) : Out M.withStore.St (Option PVal) :=
  match resVals r with
  | some ws => .ok r (x, asyncStore st ws)
  | none => .trap

theorem tail_iff (st : Store) (x : M.St) (res : Option PTy) (r : Option PVal) (hr : ResOk res r)
    (o : Out M.withStore.St (Option PVal)) :
    tail M st.next res r (x, (startSync st).1) o ↔ o = tailOut M st x r := by
  unfold tail tailOut
  cases h : resVals r with
  | none => simp only [RM.ofOption_none, RM.fail_bind]; rfl
  | some ws =>
    obtain ⟨st', hstep, hres, hst⟩ := step_fresh st ws
    simp only [RM.ofOption_some, RM.pure_bind]
    rw [builtin_bind]
    simp only [hstep]
    rw [taskResult_bind]
    simp only [hres, hr ws h, RM.ofOption_some, hst]
    exact Iff.rfl

/-! ## The closed form -/

theorem aspecCall_sync (md : AMeta) (sig : Sig) (vs : List PVal) :
    aspecCall M md ⟨sig, none⟩ vs = RM.liftFst (md.sync.specCall M sig vs) :=
  specCall_withStore M md.sync sig vs

theorem aspecCall_eq_tail (md : AMeta) (sig : Sig) (sty : Style) (vs : List PVal) :
    aspecCall M md ⟨sig, some sty⟩ vs = (startTask M >>= fun t =>
      md.sync.specCall M.withStore sig vs >>= fun r => tail M t sig.result r) := rfl

theorem tail_ok_iff (st : Store) (x : M.St) (res : Option PTy) (a r : Option PVal)
    (hr : ResOk res a) (s' : M.withStore.St) :
    tail M st.next res a (x, (startSync st).1) (.ok r s') ↔
      r = a ∧ s'.1 = x ∧ asyncPost a st = some s'.2 := by
  rw [tail_iff M st x res a hr]
  unfold tailOut asyncPost
  cases h : resVals a with
  | none => simp
  | some ws =>
    rcases s' with ⟨y, z⟩
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, h1, h2⟩
      have e1 : y = x := h1
      have e2 : asyncStore st ws = z := h2
      rw [e1, e2]

theorem tail_trap_iff (st : Store) (x : M.St) (res : Option PTy) (a : Option PVal)
    (hr : ResOk res a) :
    tail M st.next res a (x, (startSync st).1) .trap ↔ asyncPost a st = none := by
  rw [tail_iff M st x res a hr]
  unfold tailOut asyncPost
  cases resVals a <;> simp

/-- The returning outcomes of an async function. -/
theorem async_ok_iff (md : AMeta) (sig : Sig) (vs : List PVal) (s s' : M.withStore.St)
    (r : Option PVal) :
    ((∃ a x', md.sync.specCall M sig vs s.1 (.ok a x') ∧
        tail M s.2.next sig.result a (x', (startSync s.2).1) (.ok r s')) ∨
      (md.sync.specCall M sig vs s.1 .trap ∧ (.ok r s' : Out M.withStore.St _) = .trap)) ↔
      RM.alongside (md.sync.specCall M sig vs) asyncPost s (.ok r s') := by
  have hret := specCall_resOk M md.sync sig vs
  simp only [RM.alongside, reduceCtorEq, and_false, or_false]
  constructor
  · rintro ⟨a, x', hm, hk⟩
    obtain ⟨rfl, h1, h2⟩ := (tail_ok_iff M s.2 x' sig.result a r (hret _ _ _ hm) s').1 hk
    exact ⟨h1 ▸ hm, h2⟩
  · rintro ⟨hm, hp⟩
    have hk : tail M s.2.next sig.result r (s'.1, (startSync s.2).1) (.ok r s') :=
      (tail_ok_iff M s.2 s'.1 sig.result r r (hret _ _ _ hm) s').2 ⟨rfl, rfl, hp⟩
    exact ⟨r, s'.1, hm, hk⟩

/-- The trapping outcome of an async function. -/
theorem async_trap_iff (md : AMeta) (sig : Sig) (vs : List PVal) (s : M.withStore.St) :
    ((∃ a x', md.sync.specCall M sig vs s.1 (.ok a x') ∧
        tail M s.2.next sig.result a (x', (startSync s.2).1) .trap) ∨
      (md.sync.specCall M sig vs s.1 .trap ∧ (.trap : Out M.withStore.St (Option PVal)) = .trap)) ↔
      RM.alongside (md.sync.specCall M sig vs) asyncPost s .trap := by
  have hret := specCall_resOk M md.sync sig vs
  simp only [RM.alongside, and_true]
  constructor
  · rintro (⟨a, x', hm, hk⟩ | h)
    · exact .inr ⟨a, x', hm, (tail_trap_iff M s.2 x' sig.result a (hret _ _ _ hm)).1 hk⟩
    · exact .inl h
  · rintro (h | ⟨a, x', hm, hp⟩)
    · exact .inr h
    · exact .inl ⟨a, x', hm, (tail_trap_iff M s.2 x' sig.result a (hret _ _ _ hm)).2 hp⟩

/-- **The closed form of an async function's specification.** -/
theorem aspecCall_async (md : AMeta) (sig : Sig) (sty : Style) (vs : List PVal) :
    aspecCall M md ⟨sig, some sty⟩ vs = RM.alongside (md.sync.specCall M sig vs) asyncPost := by
  rw [aspecCall_eq_tail, specCall_withStore, startTask_bind]
  funext s o
  apply propext
  refine (liftFst_bind_apply_ws M _ _ _ _).trans ?_
  cases o with
  | ok r s' => exact async_ok_iff M md sig vs s s' r
  | trap => exact async_trap_iff M md sig vs s

theorem aspecCall_closed (md : AMeta) (s : ASig) (vs : List PVal) :
    aspecCall M md s vs = aspecCallClosed M md s vs := by
  rcases s with ⟨sig, _ | sty⟩
  · exact aspecCall_sync M md sig vs
  · exact aspecCall_async M md sig sty vs

theorem aspec_closed (md : AMeta) : aspec M md = aspecClosed M md := by
  funext name vs
  unfold aspec aspecClosed
  cases md.world.find? (·.sig.name == name) with
  | none => rfl
  | some s => exact aspecCall_closed M md s vs

end Silmaril.Proofs.Wasm.Jco.Async.Frame
