module

public import Silmaril.Proofs.Wasm.Jco.Resource.Basic
public import Silmaril.Wasm.Jco.Resource.Wrap.Defs
public import Silmaril.Wasm.Jco.Wrap.Thms

/-!
# Resources in the jco toolchain: lowering handles and the adaptor's prologue

* `Ext H t t' L`: the table `t'` is `t` with the entries `L` (fresh in `t`, distinct) added.
* `Match ps xs ys L`: the flat parameters `xs` of the component and `ys` of the erased
  signature agree, except that the `own` parameters are the handles of `L` in `xs` and their reps
  in `ys`.
* **`sim_lowerParamsR`**: canonical lowering with handle types simulates the erased lowering
  through `wrap`'s `cabi_realloc`, the relation being `Match` and `Ext`, while there is room.
* **`prologue_det`**: the prologue of the export shim turns the handles back into reps and drops
  them; deterministically, back to a table `Ext t · []`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst) (H : HTab)

/-- The entries of `L` added to `t`. -/
structure Ext (t t' : H.T) (L : List (Nat × HEntry)) : Prop where
  inv : H.Inv t'
  nodup : (L.map Prod.fst).Nodup
  fresh : ∀ p ∈ L, H.get? t p.1 = none
  get : ∀ j, H.get? t' j = (L.lookup j).or (H.get? t j)
  room : H.Room t L.length
  cap : H.cap t' = (H.cap t).map (· - L.length)

/-- Flat parameters of the component and of the erased signature. -/
inductive Match : List RTy → List Flat → List Flat → List (Nat × HEntry) → Prop
  | nil : Match [] [] [] []
  | own {ps xs ys L} {r : RtId} {rep : BitVec 32} {h : Nat} :
      h < 2 ^ 32 → Match ps xs ys L →
      Match (.own r :: ps) (Flat.i32 (BitVec.ofNat 32 h) :: xs) (Flat.i32 rep :: ys)
        ((h, ⟨r, rep⟩) :: L)
  | keep {p ps xs ys L} {seg : List Flat} : (∀ r, p ≠ .own r) → seg.length = p.flatLen →
      Match ps xs ys L → Match (p :: ps) (seg ++ xs) (seg ++ ys) L

variable {H}

theorem lookup_cons_ne {j i : Nat} {e : HEntry} {L : List (Nat × HEntry)} (hj : j ≠ i) :
    ((i, e) :: L).lookup j = L.lookup j := by
  have hb : (j == i) = false := beq_eq_false_iff_ne.2 hj
  simp only [List.lookup, hb]

theorem lookup_cons_self {i : Nat} {e : HEntry} {L : List (Nat × HEntry)} :
    ((i, e) :: L).lookup i = some e := by
  simp [List.lookup]

theorem lookup_of_not_mem {j : Nat} : ∀ {L : List (Nat × HEntry)}, j ∉ L.map Prod.fst →
    L.lookup j = none
  | [], _ => rfl
  | (i, e) :: L, h => by
    have hji : j ≠ i := fun hj => h (by simp [hj])
    have hL : j ∉ L.map Prod.fst := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [lookup_cons_ne hji, lookup_of_not_mem hL]

theorem room_mono {t : H.T} {m n : Nat} (h : H.Room t n) (hm : m ≤ n) : H.Room t m :=
  fun c hc => le_trans hm (h c hc)

theorem ext_nil {t : H.T} (hI : H.Inv t) : Ext H t t [] where
  inv := hI
  nodup := List.nodup_nil
  fresh _ h := by cases h
  get _ := by simp
  room _ _ := Nat.zero_le _
  cap := by cases H.cap t <;> simp

theorem ext_same {t t' : H.T} (h : Ext H t t' []) : H.Same t t' :=
  ⟨h.inv, fun j => by simpa using h.get j, by rw [h.cap]; cases H.cap t <;> simp⟩

/-- An entry added before the entries `L`. -/
theorem ext_cons (hH : H.Lawful) {t t1 t2 : H.T} {e : HEntry} {i : Nat} {L : List (Nat × HEntry)}
    (hI : H.Inv t) (ha : H.add? t e = some (i, t1)) (hR : H.Room t (L.length + 1))
    (hE : Ext H t1 t2 L) : Ext H t t2 ((i, e) :: L) := by
  obtain ⟨_, hn, hs, hf, hi', hc⟩ := hH.add_spec t e i t1 hI ha
  have hfresh : ∀ p ∈ L, p.1 ≠ i := fun p hp heq => by
    have h1 : H.get? t1 p.1 = none := hE.fresh p hp
    rw [heq, hs] at h1
    cases h1
  have hget : ∀ j, H.get? t2 j = (((i, e) :: L).lookup j).or (H.get? t j) := fun j => by
    rw [hE.get j]
    by_cases hj : j = i
    · have hl : L.lookup i = none := lookup_of_not_mem fun hm => by
        obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hm
        exact hfresh p hp hpi
      rw [hj, hl, hs, lookup_cons_self]
      rfl
    · rw [lookup_cons_ne hj, hf j hj]
  refine ⟨hE.inv, ?_, ?_, hget, hR, ?_⟩
  · exact List.nodup_cons.2 ⟨fun hm => by
      obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hm
      exact hfresh p hp hpi, hE.nodup⟩
  · rintro p (_ | ⟨_, hp⟩)
    · exact hn
    · rw [← hf p.1 (hfresh p hp)]
      exact hE.fresh p hp
  · rw [hE.cap, hc]
    cases H.cap t <;> simp [Nat.sub_sub, Nat.add_comm]

/-- Removing the first entry. -/
theorem ext_remove (hH : H.Lawful) {t tc tc' : H.T} {e e' : HEntry} {i : Nat}
    {L : List (Nat × HEntry)} (hE : Ext H t tc ((i, e) :: L))
    (hr : H.remove? tc i = some (e', tc')) : e' = e ∧ Ext H t tc' L := by
  obtain ⟨hg, hn, hf, hI', hc⟩ := hH.remove_spec tc i e' tc' hE.inv hr
  have hgi : H.get? tc i = some e := by rw [hE.get i, lookup_cons_self]; rfl
  have hee : e' = e := Option.some.inj (hg.symm.trans hgi)
  have hnd : i ∉ L.map Prod.fst ∧ (L.map Prod.fst).Nodup := List.nodup_cons.1 hE.nodup
  have hget : ∀ j, H.get? tc' j = (L.lookup j).or (H.get? t j) := fun j => by
    by_cases hj : j = i
    · have hl : L.lookup i = none := lookup_of_not_mem hnd.1
      have ht : H.get? t i = none := hE.fresh (i, e) (List.mem_cons_self ..)
      rw [hj, hn, hl, ht]
      rfl
    · have h1 : H.get? tc j = (L.lookup j).or (H.get? t j) := by
        rw [hE.get j, lookup_cons_ne hj]
      rw [hf j hj, h1]
  have hroom : H.Room t (L.length + 1) := hE.room
  refine ⟨hee, hI', hnd.2, fun p hp => hE.fresh p (List.mem_cons_of_mem _ hp), hget,
    room_mono hroom (Nat.le_succ _), ?_⟩
  rw [hc, hE.cap]
  cases hct : H.cap t with
  | none => rfl
  | some c =>
    have hle : L.length + 1 ≤ c := hroom c hct
    simp only [Option.map_some, List.length_cons, Option.some.injEq]
    omega

/-- A recorded use keeps `Ext`. -/
theorem ext_touch (hH : H.Lawful) {t tc : H.T} {L : List (Nat × HEntry)} {i : Nat} {e : HEntry}
    (hE : Ext H t tc L) (hg : H.get? tc i = some e) : Ext H t (H.touch tc i) L :=
  have ht := hH.touch_spec tc i e hE.inv hg
  ⟨ht.2.2, hE.nodup, hE.fresh, fun j => (ht.1 j).trans (hE.get j), hE.room, ht.2.1.trans hE.cap⟩

theorem match_length {ps : List RTy} {xs ys : List Flat} {L : List (Nat × HEntry)}
    (h : Match ps xs ys L) : L.length = ownCount ps := by
  induction h with
  | nil => rfl
  | own _ _ ih => simp [ownCount, ih]
  | @keep p _ _ _ _ _ hp _ _ ih =>
    cases p with
    | own r => exact absurd rfl (hp r)
    | base _ => exact ih
    | borrow _ => exact ih

/-! ## Lowering -/

variable (H) in
/-- What lowering one parameter does. -/
def SP (t : H.T) (p : RTy) (x y : List Flat) (t1 : H.T) : Prop :=
  (∃ r rep h, p = .own r ∧ h < 2 ^ 32 ∧ H.add? t ⟨r, rep⟩ = some (h, t1) ∧
      x = [Flat.i32 (BitVec.ofNat 32 h)] ∧ y = [Flat.i32 rep]) ∨
    ((∀ r, p ≠ .own r) ∧ x = y ∧ t1 = t ∧ y.length = p.flatLen)

theorem det_tabNew {t t1 : H.T} {e : HEntry} {h : Nat} (ha : H.add? t e = some (h, t1))
    (s : M.St) : Det (tabNew M H e) (s, t) (.ok (BitVec.ofNat 32 h) (s, t1)) := by
  intro o
  simp only [tabNew, RM.ofTab, ha, Option.map_some]

theorem lowerBytes_length (rw : List Flat → RM M.St (List Flat)) (limit : Nat)
    (bs : List UInt8) : Returns (lowerBytes M rw limit bs) fun xs => xs.length = 2 :=
  returns_bind returns_check fun _ _ => returns_bind (returns_true _) fun _ _ =>
    returns_bind (returns_true _) fun _ _ => returns_bind (returns_true _) fun _ _ =>
      returns_pure rfl

theorem lowerParam_length (rw : List Flat → RM M.St (List Flat)) (t : PTy) (v : PVal) :
    Returns (lowerParam M rw t v) fun xs => xs.length = t.flat.length := by
  cases t <;> cases v
  case val.val t v =>
    by_cases hc : t.check v = true
    · have hl : (t.lower v).length = t.flat.length := by
        rw [← ValTy.lower_types t v hc, List.length_map]
      simp only [lowerParam, hc, RM.check_true, RM.pure_bind]
      exact returns_pure (P := fun xs : List Flat => xs.length = (PTy.val t).flat.length) hl
    · simp only [Bool.not_eq_true] at hc
      simp only [lowerParam, hc, RM.check_false, RM.fail_bind]
      exact returns_fail
  case string.string => exact lowerBytes_length M _ _ _
  case bytes.bytes => exact lowerBytes_length M _ _ _
  all_goals exact returns_fail

theorem lowerParam_poison (rw : List Flat → RM M.St (List Flat)) (t : PTy) :
    lowerParam M rw t (poison t) = fail := by
  cases t <;> rfl

theorem lowerParam_u32 (rw : List Flat → RM M.St (List Flat)) (x : BitVec 32) :
    lowerParam M rw (.val .u32) (.val (.u32 x)) = pure [Flat.i32 x] := by
  simp [lowerParam, ValTy.check, ValTy.lower]

theorem sim_lower_base (rw : List Flat → RM M.St (List Flat)) (t : H.T) (t' : PTy) (v : PVal) :
    Sim (lowerParamR M H (fun xs => (rw xs).onFst) (.base t') (.base v))
      (lowerParam M rw t' v) t (SP H t (.base t')) := by
  have hs : Sim ((lowerParam M rw t' v).onFst : RM (M.St × H.T) _) (lowerParam M rw t' v) t
      fun a b t1 => (a = b ∧ t1 = t) ∧ b.length = t'.flat.length :=
    sim_returns (sim_onFst _ t) (lowerParam_length M rw t' v)
  show Sim (lowerParam (withTab M H.T) (fun xs => (rw xs).onFst) t' v) (lowerParam M rw t' v) t _
  rw [lowerParam_withTab]
  exact sim_mono hs fun a b t1 h => Or.inr ⟨fun r hr => (by cases hr), h.1.1, h.1.2, h.2⟩

theorem sim_lower_own (hH : H.Lawful) (rw : List Flat → RM M.St (List Flat)) {t : H.T}
    (hI : H.Inv t) (r : RtId) (x : BitVec 32) (hR : H.Room t 1) :
    Sim (lowerParamR M H (fun xs => (rw xs).onFst) (.own r) (.res x))
      (lowerParam M rw (.val .u32) (.val (.u32 x))) t (SP H t (.own r)) := by
  have hc : H.cap t ≠ some 0 := fun h0 => by simpa using hR 0 h0
  obtain ⟨⟨h, t1⟩, ha⟩ := Option.isSome_iff_exists.1 (hH.add_some t ⟨r, x⟩ hI hc)
  have h32 : h < 2 ^ 32 := (hH.add_spec t _ h t1 hI ha).1
  show Sim (tabNew M H ⟨r, x⟩ >>= fun h => pure [Flat.i32 h])
    (lowerParam M rw (.val .u32) (.val (.u32 x))) t _
  rw [lowerParam_u32]
  exact sim_det (fun s => det_bind (det_tabNew M ha s) (det_pure _ _))
    (.inl ⟨r, x, h, rfl, h32, ha, rfl, rfl⟩)

theorem sim_lower_borrow (rw : List Flat → RM M.St (List Flat)) (t : H.T) (r : RtId)
    (x : BitVec 32) :
    Sim (lowerParamR M H (fun xs => (rw xs).onFst) (.borrow r) (.res x))
      (lowerParam M rw (.val .u32) (.val (.u32 x))) t (SP H t (.borrow r)) := by
  have hp : SP H t (.borrow r) [Flat.i32 x] [Flat.i32 x] t :=
    Or.inr ⟨fun r h => (by cases h), rfl, rfl, rfl⟩
  show Sim (pure [Flat.i32 x]) (lowerParam M rw (.val .u32) (.val (.u32 x))) t _
  rw [lowerParam_u32]
  exact sim_pure hp

theorem sim_lower_poison (rw : List Flat → RM M.St (List Flat)) (t : H.T) (t' : PTy)
    (x : BitVec 32) :
    Sim (lowerParamR M H (fun xs => (rw xs).onFst) (.base t') (.res x))
      (lowerParam M rw t' (poison t')) t (SP H t (.base t')) := by
  rw [lowerParam_poison]
  exact sim_fail

/-- **Lowering one parameter.** -/
theorem sim_lowerParamR (hH : H.Lawful) (rw : List Flat → RM M.St (List Flat)) {t : H.T}
    (hI : H.Inv t) (p : RTy) (v : RVal) (hR : H.Room t (ownCount [p])) :
    Sim (lowerParamR M H (fun xs => (rw xs).onFst) p v) (lowerParam M rw p.erase (eraseVal p v))
      t (SP H t p) := by
  cases p <;> cases v
  case base.base t' v => exact sim_lower_base M rw t t' v
  case base.res t' x => exact sim_lower_poison M rw t t' x
  case own.res r x => exact sim_lower_own M hH rw hI r x hR
  case borrow.res r x => exact sim_lower_borrow M rw t r x
  all_goals exact sim_fail

theorem ownCount_keep {p : RTy} (hp : ∀ r, p ≠ .own r) (ps : List RTy) :
    ownCount (p :: ps) = ownCount ps := by
  cases p with
  | own r => exact absurd rfl (hp r)
  | base _ => rfl
  | borrow _ => rfl

theorem room_add (hH : H.Lawful) {t t1 : H.T} {e : HEntry} {i n : Nat} (hI : H.Inv t)
    (ha : H.add? t e = some (i, t1)) (hR : H.Room t (n + 1)) : H.Room t1 n := by
  intro c hc
  have hcap : H.cap t1 = (H.cap t).map (· - 1) := (hH.add_spec t e i t1 hI ha).2.2.2.2.2
  cases hct : H.cap t with
  | none => simp [hct] at hcap; rw [hcap] at hc; cases hc
  | some c0 =>
    have hle : n + 1 ≤ c0 := hR c0 hct
    have hc1 : c = c0 - 1 := by
      rw [hcap, hct] at hc
      exact (Option.some.inj hc).symm
    omega

/-- The step of the lowering simulation after one parameter. -/
theorem lower_combine (hH : H.Lawful) {t t1 t2 : H.T} {p : RTy} {ps : List RTy}
    {a b a' b' : List Flat} {L : List (Nat × HEntry)} (hI : H.Inv t)
    (hR : H.Room t (ownCount (p :: ps))) (hSP : SP H t p a b t1) (hM : Match ps a' b' L)
    (hE : Ext H t1 t2 L) : ∃ L', Match (p :: ps) (a ++ a') (b ++ b') L' ∧ Ext H t t2 L' := by
  rcases hSP with ⟨r, rep, h, rfl, h32, ha, rfl, rfl⟩ | ⟨hp, rfl, rfl, hl⟩
  · have hR' : H.Room t (L.length + 1) := by
      rw [match_length hM]
      exact hR
    exact ⟨_, .own h32 hM, ext_cons hH hI ha hR' hE⟩
  · exact ⟨L, .keep hp hl hM, hE⟩

/-- The invariant and the room after one parameter. -/
theorem lower_next (hH : H.Lawful) {t t1 : H.T} {p : RTy} {ps : List RTy} {a b : List Flat}
    (hI : H.Inv t) (hR : H.Room t (ownCount (p :: ps))) (hSP : SP H t p a b t1) :
    H.Inv t1 ∧ H.Room t1 (ownCount ps) := by
  rcases hSP with ⟨r, rep, h, rfl, -, ha, -, -⟩ | ⟨hp, -, rfl, -⟩
  · exact ⟨(hH.add_spec t _ h t1 hI ha).2.2.2.2.1, room_add hH hI ha hR⟩
  · exact ⟨hI, by rw [← ownCount_keep hp]; exact hR⟩

/-- **Lowering the parameters.** -/
theorem sim_lowerParamsR (hH : H.Lawful) (rw : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List RTy) (vs : List RVal) {t : H.T}, H.Inv t → H.Room t (ownCount ps) →
      Sim (lowerParamsR M H (fun xs => (rw xs).onFst) ps vs)
        (lowerParams M rw (ps.map RTy.erase) (eraseVals ps vs)) t
        fun xs ys t' => ∃ L, Match ps xs ys L ∧ Ext H t t' L
  | [], [], _, hI, _ => sim_pure ⟨[], .nil, ext_nil hI⟩
  | [], _ :: _, _, _, _ => sim_fail
  | _ :: _, [], _, _, _ => sim_fail
  | p :: ps, v :: vs, t, hI, hR => by
    have h1 : H.Room t (ownCount [p]) := room_mono hR (by cases p <;> simp [ownCount])
    show Sim (lowerParamR M H _ p v >>= fun a => lowerParamsR M H _ ps vs >>= fun b =>
        pure (a ++ b)) (lowerParam M rw p.erase (eraseVal p v) >>= fun a =>
        lowerParams M rw (ps.map RTy.erase) (eraseVals ps vs) >>= fun b => pure (a ++ b)) t _
    refine sim_bind (sim_lowerParamR M hH rw hI p v h1) fun a b t1 hSP => ?_
    have hn : H.Inv t1 ∧ H.Room t1 (ownCount ps) := lower_next hH hI hR hSP
    refine sim_bind (sim_lowerParamsR hH rw ps vs hn.1 hn.2) fun a' b' t2 hL => ?_
    obtain ⟨L, hM, hE⟩ := hL
    exact sim_pure (lower_combine hH hI hR hSP hM hE)

/-! ## The prologue -/

theorem toNat_ofNat_lt {h : Nat} (h32 : h < 2 ^ 32) : (BitVec.ofNat 32 h).toNat = h := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h32

theorem det_tabGet {t : H.T} {h : BitVec 32} {e : HEntry} (hg : H.get? t h.toNat = some e)
    (s : M.St) : Det (tabGet M H h) (s, t) (.ok e (s, H.touch t h.toNat)) := by
  intro o
  simp only [tabGet, RM.ofTab, hg, Option.map_some]

theorem det_tabRemove {t t' : H.T} {h : BitVec 32} {e : HEntry}
    (hr : H.remove? t h.toNat = some (e, t')) (s : M.St) :
    Det (tabRemove M H h) (s, t) (.ok e (s, t')) := by
  intro o
  simp only [tabRemove, RM.ofTab, hr]

theorem execR_nil (f : Frame) : execR M H [] f = pure f := rfl

theorem execR_cons (i : RInstr) (is : List RInstr) (f : Frame) :
    execR M H (i :: is) f = (i.step M H f >>= fun f' => execR M H is f') := rfl

theorem execR_append (a b : List RInstr) (f : Frame) :
    execR M H (a ++ b) f = (execR M H a f >>= fun f' => execR M H b f') := by
  induction a generalizing f with
  | nil => exact (RM.pure_bind _ _).symm
  | cons i is ih => simp only [List.cons_append, execR_cons, ih, RM.bind_assoc]

theorem det_base {i : AInstr} {f f' : Frame} (h : i.step (withTab M H.T) f = pure f')
    (st : M.St × H.T) : Det ((RInstr.base i).step M H f) st (.ok f' st) := by
  show Det (i.step (withTab M H.T) f) st _
  rw [h]
  exact det_pure _ _

/-- The prologue of one `own` parameter. -/
theorem det_preOwn {ls : List Flat} {p h : Nat} {r : RtId} {rep : BitVec 32} {tc tc' : H.T}
    (hp : ls[p]? = some (Flat.i32 (BitVec.ofNat 32 h))) (h32 : h < 2 ^ 32)
    (hg : H.get? tc h = some ⟨r, rep⟩)
    (hr : H.remove? (H.touch tc h) h = some (⟨r, rep⟩, tc')) (s : M.St) :
    Det (execR M H (preOwn r p) ⟨ls, []⟩) (s, tc) (.ok ⟨ls.set p (Flat.i32 rep), []⟩ (s, tc')) := by
  have hlt : p < ls.length := (List.getElem?_eq_some_iff.1 hp).1
  have hn : (BitVec.ofNat 32 h).toNat = h := toNat_ofNat_lt h32
  have hg' : H.get? tc (BitVec.ofNat 32 h).toNat = some ⟨r, rep⟩ := by rw [hn]; exact hg
  have hr' : H.remove? (H.touch tc h) (BitVec.ofNat 32 h).toNat = some (⟨r, rep⟩, tc') := by
    rw [hn]; exact hr
  have hrep : Det (builtinRep M H r [Flat.i32 (BitVec.ofNat 32 h)]) (s, tc)
      (.ok [Flat.i32 rep] (s, H.touch tc h)) := by
    have hd := det_bind (det_tabGet M hg' s) (det_bind (det_check (by simp) _) (det_pure _ _))
      (k := fun e => RM.check (e.rt == r) >>= fun _ => pure [Flat.i32 e.rep])
    rw [hn] at hd
    exact hd
  have hdrop : Det (builtinDrop M H r [Flat.i32 (BitVec.ofNat 32 h)]) (s, H.touch tc h)
      (.ok [] (s, tc')) :=
    det_bind (det_tabRemove M hr' s) (det_bind (det_check (by simp) _) (det_pure _ _))
  refine det_bind (det_base M (step_localGet _ hp []) _) ?_
  refine det_bind (det_base M (step_localGet _ hp _) _) ?_
  refine det_bind (det_bind hrep (det_pure _ _)) ?_
  refine det_bind (det_base M (step_localSet _ hlt _ _) _) ?_
  exact det_bind (det_bind hdrop (det_pure _ _)) (det_pure _ _)

theorem prologue_keep {p : RTy} (hp : ∀ r, p ≠ .own r) (n : Nat) (ps : List RTy) :
    prologue n (p :: ps) = prologue (n + p.flatLen) ps := by
  cases p with
  | own r => exact absurd rfl (hp r)
  | base _ => rfl
  | borrow _ => rfl

/-- The prologue step of one `own` parameter, in context. -/
theorem prologue_own (hH : H.Lawful) {t tc : H.T} {r : RtId} {rep : BitVec 32} {h : Nat}
    {L : List (Nat × HEntry)} (h32 : h < 2 ^ 32) (pre xs : List Flat)
    (hE : Ext H t tc ((h, ⟨r, rep⟩) :: L)) :
    ∃ tc', Ext H t tc' L ∧ ∀ s, Det (execR M H (preOwn r pre.length)
      ⟨pre ++ Flat.i32 (BitVec.ofNat 32 h) :: xs, []⟩) (s, tc)
        (.ok ⟨(pre ++ [Flat.i32 rep]) ++ xs, []⟩ (s, tc')) := by
  have hg : H.get? tc h = some ⟨r, rep⟩ := by rw [hE.get h, lookup_cons_self]; rfl
  have hE1 : Ext H t (H.touch tc h) ((h, ⟨r, rep⟩) :: L) := ext_touch hH hE hg
  have hg1 : H.get? (H.touch tc h) h = some ⟨r, rep⟩ := ((hH.touch_spec tc h _ hE.inv hg).1 h).trans hg
  obtain ⟨tc', hr⟩ := hH.remove_some _ h _ hg1
  have hp : (pre ++ Flat.i32 (BitVec.ofNat 32 h) :: xs)[pre.length]? =
      some (Flat.i32 (BitVec.ofNat 32 h)) := by simp
  have hset : (pre ++ Flat.i32 (BitVec.ofNat 32 h) :: xs).set pre.length (Flat.i32 rep) =
      (pre ++ [Flat.i32 rep]) ++ xs := by simp
  refine ⟨tc', (ext_remove hH hE1 hr).2, fun s => ?_⟩
  rw [← hset]
  exact det_preOwn M hp h32 hg hr s

/-- **The prologue** turns the handles of the `own` parameters back into reps and drops them. -/
theorem prologue_det (hH : H.Lawful) {t : H.T} {ps : List RTy} {xs ys : List Flat}
    {L : List (Nat × HEntry)} (hM : Match ps xs ys L) :
    ∀ {tc : H.T} (pre : List Flat), Ext H t tc L →
      ∃ tf, Ext H t tf [] ∧ ∀ s, Det (execR M H (prologue pre.length ps) ⟨pre ++ xs, []⟩)
        (s, tc) (.ok ⟨pre ++ ys, []⟩ (s, tf)) := by
  induction hM with
  | nil => exact fun _ hE => ⟨_, hE, fun _ => det_pure _ _⟩
  | @own ps xs ys L r rep h h32 _ ih =>
    intro tc pre hE
    obtain ⟨tc', hE', hd1⟩ := prologue_own M hH h32 pre xs hE
    obtain ⟨tf, hEf, hd⟩ := ih (pre ++ [Flat.i32 rep]) hE'
    have hlen : (pre ++ [Flat.i32 rep]).length = pre.length + 1 := by simp
    have hys : (pre ++ [Flat.i32 rep]) ++ ys = pre ++ Flat.i32 rep :: ys := by simp
    refine ⟨tf, hEf, fun s => ?_⟩
    show Det (execR M H (preOwn r pre.length ++ prologue (pre.length + 1) ps) _) _ _
    rw [execR_append, ← hlen, ← hys]
    exact det_bind (hd1 s) (hd s)
  | @keep p ps xs ys L seg hp hl _ ih =>
    intro tc pre hE
    obtain ⟨tf, hEf, hd⟩ := ih (pre ++ seg) hE
    have hlen : (pre ++ seg).length = pre.length + p.flatLen := by simp [hl]
    refine ⟨tf, hEf, fun s => ?_⟩
    rw [prologue_keep hp, ← hlen, ← List.append_assoc, ← List.append_assoc]
    exact hd s

end Silmaril.Proofs.Wasm.Jco.Res
