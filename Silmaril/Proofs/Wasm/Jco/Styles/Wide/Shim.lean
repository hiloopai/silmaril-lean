module

public import Silmaril.Proofs.Wasm.Jco.Styles.Wide.After
public import Silmaril.Wasm.Jco.Styles.EncWrap.Thms

/-!
# Wide results: what the multi-value shim computes

* `execX_append`, `execX_setsRev`: popping results into consecutive locals;
* `execX_storeField`, `execX_storeFields`: the field stores are `storeAll` of `fieldWrites`;
* **`mvShim_run`**: the shim calls the function, allocates the block, stores the fields and
  returns the pointer.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst)

theorem execX_append : ∀ (a b : List XInstr) (f : Frame),
    execX M (a ++ b) f = (execX M a f >>= fun f' => execX M b f')
  | [], b, f => by simp [execX]
  | i :: a, b, f => by
    rw [List.cons_append, execX_cons, execX_cons, RM.bind_assoc]
    exact RM.bind_congr fun f' => execX_append a b f'

theorem set_mid (pre zs post : List Flat) (z r : Flat) :
    (pre ++ (zs ++ [z]) ++ post).set (pre.length + zs.length) r = pre ++ zs ++ (r :: post) := by
  simp [List.set_append_right]

theorem execX_setsRev (z : Flat) : ∀ (k : Nat) (pre post rs st : List Flat), rs.length = k →
    execX M (setsRev pre.length k) ⟨pre ++ List.replicate k z ++ post, rs.reverse ++ st⟩ =
      pure ⟨pre ++ rs ++ post, st⟩
  | 0, pre, post, rs, st, h => by
    rw [List.length_eq_zero_iff.mp h]
    rfl
  | k + 1, pre, post, rs, st, h => by
    have hne : rs ≠ [] := by intro h'; simp [h'] at h
    have hrs := List.dropLast_append_getLast hne
    have hl : rs.dropLast.length = k := by simp [h]
    have hloc : pre ++ List.replicate (k + 1) z ++ post =
        pre ++ (List.replicate k z ++ [z]) ++ post := by rw [List.replicate_succ']
    have hset : (AInstr.localSet (pre.length + k)).step M
        ⟨pre ++ List.replicate (k + 1) z ++ post, rs.reverse ++ st⟩ =
          pure ⟨pre ++ List.replicate k z ++ (rs.getLast hne :: post), rs.dropLast.reverse ++ st⟩ := by
      conv => lhs; rw [← hrs]
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons_append,
        step_localSet M (by simp; omega), hloc]
      have := set_mid pre (List.replicate k z) post z (rs.getLast hne)
      simp only [List.length_replicate] at this
      rw [this]
    rw [setsRev, execX_cons]
    show ((AInstr.localSet (pre.length + k)).step M _ >>= _) = _
    rw [hset, RM.pure_bind, execX_setsRev z k pre _ _ st hl]
    conv => rhs; rw [← hrs]
    simp

theorem execX_storeTail {L st : List Flat} {p : BitVec 32} (v : Flat) (ft : Silmaril.Wasm.NumType)
    (n off : Nat) :
    execX M [.store ft n off] ⟨L, v :: Flat.i32 p :: st⟩ =
      (M.store (p.toNat + off) (leBytes n v.bits.toNat) >>= fun _ => pure ⟨L, st⟩) := by
  simp [execX, XInstr.step, asI32?]

theorem eqz_eqz (x : BitVec 32) (L st : List Flat) :
    execX M [.i32Eqz, .i32Eqz] ⟨L, Flat.i32 x :: st⟩ =
      pure ⟨L, normField .bool (Flat.i32 x) :: st⟩ := by
  by_cases hx : x = 0 <;> simp [execX, XInstr.step, asI32?, normField, hx]

theorem normField_ne {t : ValTy} (h : isBoolTy t = false) (r : Flat) : normField t r = r := by
  cases t <;> first | rfl | simp [isBoolTy] at h

theorem execX_storeField {L : List Flat} {pl i : Nat} {p : BitVec 32}
    (hp : L[pl]? = some (Flat.i32 p)) {r : Flat} (hr : L[i]? = some r) {t : ValTy}
    (htr : t = .bool → r.type = .int .i32) (n off : Nat) (ft : Silmaril.Wasm.NumType) :
    execX M ([.base (.localGet pl), .base (.localGet i)] ++
        (if isBoolTy t then [.i32Eqz, .i32Eqz] else []) ++ [.store ft n off]) ⟨L, []⟩ =
      (M.store (p.toNat + off) (leBytes n (normField t r).bits.toNat) >>= fun _ => pure ⟨L, []⟩) := by
  have hpre : execX M [.base (.localGet pl), .base (.localGet i)] ⟨L, []⟩ =
      pure ⟨L, [r, Flat.i32 p]⟩ := by
    simp [execX, XInstr.step, step_localGet M hp, step_localGet M hr]
  rw [execX_append, execX_append, hpre, RM.pure_bind]
  cases hb : isBoolTy t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show execX M [] ⟨L, [r, Flat.i32 p]⟩ = pure ⟨L, [r, Flat.i32 p]⟩ from rfl, RM.pure_bind,
      execX_storeTail, normField_ne hb]
  · have ht : t = .bool := by cases t <;> simp_all [isBoolTy]
    subst ht
    rcases r with ⟨ty, x⟩
    have hty : ty = .int .i32 := htr rfl
    subst hty
    simp only [↓reduceIte]
    rw [eqz_eqz M x, RM.pure_bind, execX_storeTail]

theorem isBool_flat {t : ValTy} {r : Flat} (h : t.flat = [r.type]) :
    t = .bool → r.type = .int .i32 := by
  rintro rfl
  simpa [ValTy.flat] using h.symm

theorem execX_storeFields {p : BitVec 32} (pl base : Nat) : ∀ (j : Nat) (ts : List ValTy)
    (os ns : List Nat) (pre rs : List Flat), pre.length = base + j →
    (pre ++ rs)[pl]? = some (Flat.i32 p) → rs.map (·.type) = ValTy.flatList ts →
    ts.mapM scalarSize = some ns → os.length = ns.length →
    execX M (storeFields pl base j ts os ns) ⟨pre ++ rs, []⟩ =
      (storeAll M (fieldWrites p.toNat ts os ns rs) >>= fun _ => pure ⟨pre ++ rs, []⟩)
  | j, [], os, ns, pre, rs, _, _, hr, _, _ => by
    have hrs : rs = [] := List.map_eq_nil_iff.mp hr
    subst hrs
    cases os <;> cases ns <;> simp [storeFields, fieldWrites, storeAll, execX]
  | j, t :: ts, o :: os, ns, pre, rs, hpre, hp, hr, hn, hl => by
    obtain ⟨n, ht, ns', hts, rfl⟩ := mapM_cons_some hn
    obtain ⟨r, rs', rfl, htr, hrs'⟩ := types_cons ht hr
    have hri : (pre ++ r :: rs')[base + j]? = some r := by
      rw [← hpre, List.getElem?_append_right (by omega)]
      simp
    have hL : pre ++ r :: rs' = (pre ++ [r]) ++ rs' := by simp
    have ih := execX_storeFields pl base (j + 1) ts os ns' (pre ++ [r]) rs'
      (by simp [hpre]; omega) (by rw [← hL]; exact hp) hrs' hts (by simpa using hl)
    rw [storeFields, execX_append, storeField, execX_storeField M hp hri (isBool_flat htr),
      RM.bind_assoc]
    simp only [RM.pure_bind]
    rw [hL, ih, ← hL]
    simp only [fieldWrites, storeAll, RM.bind_assoc]
  | _, _ :: _, [], _, _, _, _, _, _, hn, hl => by
    obtain ⟨n, _, ns', _, rfl⟩ := mapM_cons_some hn
    simp at hl

theorem flatList_length : ∀ {ts : List ValTy} {ns : List Nat}, ts.mapM scalarSize = some ns →
    (ValTy.flatList ts).length = ts.length
  | [], _, _ => rfl
  | t :: ts, _, h => by
    obtain ⟨n, ht, ns', hts, rfl⟩ := mapM_cons_some h
    obtain ⟨ty, hty⟩ := flat_scalar ht
    simp [ValTy.flatList, hty, flatList_length hts]

theorem execX_callAfterGets (g : String) (xs zs : List Flat) :
    execX M ((gets xs.length).map .base ++ [.base (.call g xs.length)]) ⟨xs ++ zs, []⟩ =
      (M.call g xs >>= fun rs => pure ⟨xs ++ zs, rs.reverse⟩) := by
  have hg : execX M ((gets xs.length).map .base) ⟨xs ++ zs, []⟩ = pure ⟨xs ++ zs, xs.reverse⟩ := by
    rw [execX_map_base, exec_gets M _ _ _ (by simp)]
    simp
  rw [execX_append, hg, RM.pure_bind, execX_cons, XInstr.step,
    step_call M g _ (by simp)]
  have hd : xs.reverse.drop xs.length = [] := List.drop_eq_nil_of_le (by simp)
  simp [take_reverse_full, execX, hd]

theorem execX_alloc (alloc : String) (a b : BitVec 32) (L : List Flat) (n : Nat) :
    execX M [.base (.i32Const a), .base (.i32Const b), .base (.call alloc 2), .base (.localSet n)]
        ⟨L, []⟩ =
      (M.call alloc [Flat.i32 a, Flat.i32 b] >>= fun r =>
        execX M [.base (.localSet n)] ⟨L, r.reverse⟩) := by
  simp [execX, XInstr.step, AInstr.step, RM.bind_assoc]

/-- The shim after the call, on the results `rs`. -/
theorem mvShim_after (md : Meta) {ts : List ValTy} {ns : List Nat}
    (hn : ts.mapM scalarSize = some ns)
    (hA : Returns (M.call md.alloc [i32n (tupleSize ns), i32n (tupleAlign ns)])
      fun r => ∃ p, r = [Flat.i32 p])
    (xs rs : List Flat) (hrs : rs.map (·.type) = ValTy.flatList ts) :
    execX M (setsRev (xs.length + 1) ts.length ++
        [.base (.i32Const (BitVec.ofNat 32 (tupleSize ns))),
          .base (.i32Const (BitVec.ofNat 32 (tupleAlign ns))), .base (.call md.alloc 2),
          .base (.localSet xs.length)] ++
        storeFields xs.length (xs.length + 1) 0 ts (fieldOffs 0 ns) ns ++
        [.base (.localGet xs.length)])
        ⟨xs ++ List.replicate (ts.length + 1) (i32n 0), rs.reverse⟩ =
      (M.call md.alloc [i32n (tupleSize ns), i32n (tupleAlign ns)] >>= fun r =>
        RM.ofOption (single32? r) >>= fun p =>
          storeAll M (fieldWrites p.toNat ts (fieldOffs 0 ns) ns rs) >>= fun _ =>
            pure ⟨xs ++ Flat.i32 p :: rs, [Flat.i32 p]⟩) := by
  have hk : rs.length = ts.length := by
    rw [← List.length_map (f := (·.type)), hrs, flatList_length hn]
  have hL0 : xs ++ List.replicate (ts.length + 1) (i32n 0) =
      (xs ++ [i32n 0]) ++ List.replicate ts.length (i32n 0) ++ [] := by
    simp [List.replicate_succ]
  have hC : execX M (setsRev (xs.length + 1) ts.length)
      ⟨xs ++ List.replicate (ts.length + 1) (i32n 0), rs.reverse⟩ =
        pure ⟨xs ++ i32n 0 :: rs, []⟩ := by
    have h := execX_setsRev M (i32n 0) ts.length (xs ++ [i32n 0]) [] rs [] hk
    simp only [List.length_append, List.length_singleton, List.append_nil] at h
    rw [hL0, List.append_nil, h]
    simp
  rw [execX_append, execX_append, execX_append, hC, RM.pure_bind, execX_alloc, RM.bind_assoc,
    RM.bind_assoc]
  refine RM.bind_congr_returns hA ?_
  rintro r ⟨p, rfl⟩
  have hset : (xs ++ i32n 0 :: rs).set xs.length (Flat.i32 p) = (xs ++ [Flat.i32 p]) ++ rs := by
    simp
  have hE := execX_storeFields M (p := p) xs.length (xs.length + 1) 0 ts (fieldOffs 0 ns) ns
    (xs ++ [Flat.i32 p]) rs (by simp) (by simp) hrs hn (fieldOffs_length 0 ns)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, XInstr.step,
    step_localSet M (by simp : xs.length < (xs ++ i32n 0 :: rs).length), RM.pure_bind, execX,
    hset, single32?, RM.ofOption_some]
  rw [hE, RM.bind_assoc]
  refine RM.bind_congr fun _ => ?_
  have hg : (xs ++ Flat.i32 p :: rs)[xs.length]? = some (Flat.i32 p) := by
    rw [List.getElem?_append_right (le_refl _)]
    simp
  simp only [List.append_assoc, List.singleton_append]
  simp [step_localGet M hg]

theorem append6 {α : Type} (a b c d e f : List α) :
    a ++ b ++ c ++ d ++ e ++ f = (a ++ b) ++ (c ++ d ++ e ++ f) := by simp

/-- **What the multi-value shim computes.** -/
theorem mvShim_run (md : Meta) (s : Sig) {ts : List ValTy} {ns : List Nat}
    (hn : ts.mapM scalarSize = some ns)
    (hA : Returns (M.call md.alloc [i32n (tupleSize ns), i32n (tupleAlign ns)])
      fun r => ∃ p, r = [Flat.i32 p])
    (xs : List Flat) (hx : xs.length = (flatParams s.params).length)
    (hR : Returns (M.call s.name xs) fun rs => rs.map (·.type) = ValTy.flatList ts) :
    (mvShim md s ts ns).run M xs =
      (M.call s.name xs >>= fun rs =>
        M.call md.alloc [i32n (tupleSize ns), i32n (tupleAlign ns)] >>= fun r =>
          RM.ofOption (single32? r) >>= fun p =>
            storeAll M (fieldWrites p.toNat ts (fieldOffs 0 ns) ns rs) >>= fun _ =>
              pure [Flat.i32 p]) := by
  unfold XFn.run mvShim
  simp only [← hx, beq_self_eq_true, RM.check_true, RM.pure_bind]
  rw [append6, execX_append, execX_callAfterGets, RM.bind_assoc, RM.bind_assoc]
  refine RM.bind_congr_returns hR fun rs hrs => ?_
  rw [RM.pure_bind, mvShim_after M md hn hA xs rs hrs]
  simp only [RM.bind_assoc, RM.pure_bind, List.reverse_cons, List.reverse_nil, List.nil_append]

end Silmaril.Proofs.Wasm.Jco
