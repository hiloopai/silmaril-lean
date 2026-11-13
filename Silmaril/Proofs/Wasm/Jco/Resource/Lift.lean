module

public import Silmaril.Proofs.Wasm.Jco.Resource.Lower

/-!
# Resources in the jco toolchain: the adaptor's epilogue and lifting the result

**`sim_epilogue`**: the shim's epilogue (`resource.new` of an `own` result) followed by
`lift_own` simulates lifting the erased (`u32`) result, back to a table interchangeable with the
original one, while the table has room for one handle.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst) {H : HTab}

theorem same_trans {t t1 t2 : H.T} (h1 : H.Same t t1) (h2 : H.Same t1 t2) : H.Same t t2 :=
  ⟨h2.1, fun j => (h2.2.1 j).trans (h1.2.1 j), h2.2.2.trans h1.2.2⟩

theorem unerase_of_not_own {res : Option RTy} (h : ∀ r, res ≠ some (.own r))
    (x : Option PVal) : unerase res x = x.map .base := by
  rcases res with _ | (_ | r | _)
  · rfl
  · rfl
  · exact absurd rfl (h r)
  · rfl

theorem asI32_eq {x : Flat} {b : BitVec 32} (h : asI32? x = some b) : x = Flat.i32 b := by
  rcases x with ⟨(_ | _) | (_ | _), y⟩ <;> simp [asI32?] at h
  cases h
  rfl

theorem builtinNew_none {x : Flat} (h : asI32? x = none) (r : RtId) :
    builtinNew M H r [x] = fail := by
  rcases x with ⟨(_ | _) | (_ | _), y⟩ <;> simp [asI32?] at h <;> rfl

theorem liftResult_u32 (rs : List Flat) :
    liftResult M (some (.val .u32)) rs = match single32? rs with
      | some x => pure (some (.val (.u32 x)))
      | none => fail := by
  rcases rs with _ | ⟨⟨(_ | _) | (_ | _), y⟩, _ | ⟨z, rs⟩⟩ <;> rfl

theorem liftResultR_long {xs : List Flat} (h : 2 ≤ xs.length) (r : RtId) :
    liftResultR M H (some (.own r)) xs = fail := by
  rcases xs with _ | ⟨x, _ | ⟨y, xs⟩⟩
  · simp at h
  · simp at h
  · rfl

variable (H) in
/-- The shim's epilogue on the core results, then the lift of the result. -/
def postC (res : Option RTy) (rs : List Flat) : RM (withTab M H.T).St (Option RVal) :=
  (execR M H (epilogue res) ⟨[], rs.reverse⟩ >>= fun g => pure g.stack.reverse) >>= fun rs' =>
    liftResultR M H res rs'

/-- The epilogue and `lift_own` of an `own` result, as one computation. -/
theorem post_own_eq (r : RtId) (rs : List Flat) :
    postC M H (some (.own r)) rs =
      match rs.reverse with
      | [] => fail
      | y :: st => builtinNew M H r [y] >>= fun ys =>
          liftResultR M H (some (.own r)) (ys.reverse ++ st).reverse := by
  unfold postC
  cases rs.reverse with
  | nil => simp only [epilogue, execR_cons, RInstr.step, callTop, RM.fail_bind]
  | cons y st =>
    simp only [epilogue, execR_cons, execR_nil, RInstr.step, callTop, RM.bind_assoc,
      RM.pure_bind, RM.bind_pure]

theorem tabNew_bind_fail_det (e : HEntry) {γ : Type} (t : H.T) (s : M.St) :
    Det (tabNew M H e >>= fun _ => (fail : RM (withTab M H.T).St γ)) (s, t) .trap := by
  cases ha : H.add? t e with
  | none =>
    refine det_bind_trap ?_
    intro o
    simp only [tabNew, RM.ofTab, ha, Option.map_none]
  | some p =>
    rcases p with ⟨h, t1⟩
    exact det_bind (det_tabNew M ha s) (det_fail _)

theorem post_own_trap_i32 (r : RtId) {rs st : List Flat} {y : Flat} {b : BitVec 32}
    (hs : single32? rs = none) (hrv : rs.reverse = y :: st) (hyb : y = Flat.i32 b) (t : H.T)
    (s : M.St) : Det (builtinNew M H r [Flat.i32 b] >>= fun ys =>
      liftResultR M H (some (.own r)) (ys.reverse ++ st).reverse) (s, t) .trap := by
  have hst : st ≠ [] := fun h0 => by
    have hrs : rs = [Flat.i32 b] := by
      rw [← List.reverse_reverse rs, hrv, h0, hyb]
      rfl
    rw [hrs] at hs
    cases hs
  have hlen : ∀ h : BitVec 32, 2 ≤ ([Flat.i32 h].reverse ++ st).reverse.length := by
    intro h
    cases st with
    | nil => exact absurd rfl hst
    | cons z st => simp
  show Det ((tabNew M H ⟨r, b⟩ >>= fun h => pure [Flat.i32 h]) >>= fun ys =>
    liftResultR M H (some (.own r)) (ys.reverse ++ st).reverse) (s, t) .trap
  simp only [RM.bind_assoc, RM.pure_bind, liftResultR_long M (hlen _)]
  exact tabNew_bind_fail_det M _ t s

/-- An `own` result that is not one `i32` traps. -/
theorem post_own_trap (r : RtId) {rs : List Flat} (hs : single32? rs = none) (t : H.T)
    (s : M.St) : Det (postC M H (some (.own r)) rs) (s, t) .trap := by
  rw [post_own_eq]
  cases hrv : rs.reverse with
  | nil => exact det_fail _
  | cons y st =>
    show Det (builtinNew M H r [y] >>= fun ys =>
      liftResultR M H (some (.own r)) (ys.reverse ++ st).reverse) (s, t) .trap
    cases hy : asI32? y with
    | none => rw [builtinNew_none M hy, RM.fail_bind]; exact det_fail _
    | some b =>
      have hyb : y = Flat.i32 b := asI32_eq hy
      rw [hyb]
      exact post_own_trap_i32 M r hs hrv hyb t s

theorem single32_eq {rs : List Flat} {x : BitVec 32} (h : single32? rs = some x) :
    rs = [Flat.i32 x] := by
  rcases rs with _ | ⟨⟨(_ | _) | (_ | _), y⟩, _ | ⟨z, rs⟩⟩ <;> simp [single32?] at h
  cases h
  rfl

/-- An `own` result that is one `i32`: `resource.new`, then `lift_own`. -/
theorem post_own_ok (hH : H.Lawful) {tf : H.T} (hI : H.Inv tf) (hR : H.Room tf 1) (r : RtId)
    (x : BitVec 32) : ∃ t5, H.Same tf t5 ∧ ∀ s, Det (postC M H (some (.own r)) [Flat.i32 x])
      (s, tf) (.ok (some (.res x)) (s, t5)) := by
  have hc : H.cap tf ≠ some 0 := fun h0 => by simpa using hR 0 h0
  obtain ⟨⟨h, t4⟩, ha⟩ := Option.isSome_iff_exists.1 (hH.add_some tf ⟨r, x⟩ hI hc)
  have hspec := hH.add_spec tf _ h t4 hI ha
  have hE4 : Ext H tf t4 [(h, ⟨r, x⟩)] := ext_cons hH hI ha hR (ext_nil hspec.2.2.2.2.1)
  obtain ⟨t5, hr⟩ := hH.remove_some t4 h _ hspec.2.2.1
  have hE5 : Ext H tf t5 [] := (ext_remove hH hE4 hr).2
  have hn : (BitVec.ofNat 32 h).toNat = h := toNat_ofNat_lt hspec.1
  have hr' : H.remove? t4 (BitVec.ofNat 32 h).toNat = some (⟨r, x⟩, t5) := by rw [hn]; exact hr
  refine ⟨t5, ext_same hE5, fun s => ?_⟩
  rw [post_own_eq]
  show Det ((tabNew M H ⟨r, x⟩ >>= fun h => pure [Flat.i32 h]) >>= fun ys =>
    liftResultR M H (some (.own r)) (ys.reverse ++ []).reverse) (s, tf) _
  refine det_bind (det_bind (det_tabNew M ha s) (det_pure _ _)) ?_
  show Det (RM.ofOption (some (BitVec.ofNat 32 h)) >>= fun h => tabRemove M H h >>= fun e =>
    RM.check (e.rt == r) >>= fun _ => pure (some (RVal.res e.rep))) (s, t4) _
  exact det_bind (det_pure _ _) (det_bind (det_tabRemove M hr' s)
    (det_bind (det_check (by simp) _) (det_pure _ _)))

theorem postC_plain {res : Option RTy} (h : epilogue res = []) (rs : List Flat) :
    postC M H res rs = liftResultR M H res rs := by
  simp only [postC, h, execR_nil, RM.pure_bind, List.reverse_reverse]

/-- A result that is not a handle: lifted as in the first fragment. -/
theorem sim_lift_plain {t tf : H.T} {res : Option RTy} (hS : H.Same t tf)
    (h : ∀ r, res ≠ some (.own r)) (hb : ∀ r, res ≠ some (.borrow r)) (rs : List Flat) :
    Sim (postC M H res rs) (liftResult M (res.map RTy.erase) rs >>= fun r =>
      if resultOk res then pure (unerase res r) else fail) tf fun a b t' => a = b ∧ H.Same t t' := by
  have hres : (∃ t', res = some (.base t')) ∨ res = none := by
    rcases res with _ | (t' | r | r)
    · exact .inr rfl
    · exact .inl ⟨t', rfl⟩
    · exact absurd rfl (h r)
    · exact absurd rfl (hb r)
  have hok : resultOk res = true := by
    rcases hres with ⟨t', rfl⟩ | rfl <;> rfl
  have hl : liftResultR M H res rs = ((liftResult M (res.map RTy.erase) rs).onFst >>= fun r =>
      pure (r.map RVal.base)) := by
    rcases hres with ⟨t', rfl⟩ | rfl <;> simp only [liftResultR, liftResult_withTab] <;> rfl
  have he : epilogue res = [] := by rcases hres with ⟨t', rfl⟩ | rfl <;> rfl
  rw [postC_plain M he, hl, hok]
  refine sim_bind (sim_onFst _ tf) fun a b t' hab => ?_
  simp only [↓reduceIte]
  rw [unerase_of_not_own h, hab.1]
  exact sim_pure ⟨rfl, hab.2 ▸ hS⟩

/-- **The epilogue and the lift of the result.** -/
theorem sim_epilogue (hH : H.Lawful) {t tf : H.T} (res : Option RTy) (hS : H.Same t tf)
    (hR : H.Room t (ownRes res)) (rs : List Flat) :
    Sim (postC M H res rs) (liftResult M (res.map RTy.erase) rs >>= fun r =>
      if resultOk res then pure (unerase res r) else fail) tf fun a b t' => a = b ∧ H.Same t t' := by
  rcases res with _ | (t' | r | r)
  · exact sim_lift_plain M hS (fun _ h => by cases h) (fun _ h => by cases h) rs
  · exact sim_lift_plain M hS (fun _ h => by cases h) (fun _ h => by cases h) rs
  · show Sim _ (liftResult M (some (.val .u32)) rs >>= fun v => pure (unerase (some (.own r)) v))
      tf _
    have hR1 : H.Room tf 1 := fun c hc => hR c (hS.2.2 ▸ hc)
    rw [liftResult_u32]
    cases hs : single32? rs with
    | none =>
      rw [RM.fail_bind]
      exact sim_trap (post_own_trap M r hs tf) det_fail
    | some x =>
      obtain ⟨t5, h5, hd⟩ := post_own_ok M hH hS.1 hR1 r x
      rw [single32_eq hs, RM.pure_bind]
      exact sim_det hd ⟨rfl, same_trans hS h5⟩
  · have hc : postC M H (some (.borrow r)) rs = fail := by
      rw [postC_plain M rfl]
      rfl
    show Sim _ (liftResult M (some (.val .u32)) rs >>= fun _ => fail) tf _
    rw [hc, liftResult_u32]
    cases single32? rs with
    | none => rw [RM.fail_bind]; exact sim_fail
    | some x => rw [RM.pure_bind]; exact sim_fail

end Silmaril.Proofs.Wasm.Jco.Res
