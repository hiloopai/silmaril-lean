module

public import Silmaril.Proofs.Wasm.Jco.Styles.Wide.Scalar
public import Silmaril.Wasm.Jco.Basic.Thms

/-!
# Wide results: loading the stored fields

* `bind_congr_ok`: continuations that agree at every reachable outcome give the same
  computation;
* `storeAll_ok`: a successful `storeAll` from `s` ends in a state whose memory is `writeAll` of
  `s`'s memory (for a lawful memory);
* **`loadFields_at`**: in a state whose memory holds the stored bytes of the fields, loading the
  fields is the flat lift of their values.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val liftArgs)

variable {σ α β : Type}

theorem bind_congr_ok {m : RM σ α} {k k' : α → RM σ β}
    (h : ∀ s a s', m s (.ok a s') → k a s' = k' a s') : (m >>= k) = (m >>= k') := by
  funext s o
  simp only [bind_apply]
  apply propext
  constructor
  · rintro (⟨a, s', h1, h2⟩ | h1)
    · exact .inl ⟨a, s', h1, by rw [← h s a s' h1]; exact h2⟩
    · exact .inr h1
  · rintro (⟨a, s', h1, h2⟩ | h1)
    · exact .inl ⟨a, s', h1, by rw [h s a s' h1]; exact h2⟩
    · exact .inr h1

theorem bind_at {m : RM σ α} {s : σ} {a : α} (h : m s = (pure a : RM σ α) s) (k : α → RM σ β) :
    (m >>= k) s = k a s := by
  funext o
  simp only [bind_apply, h, pure_apply]
  apply propext
  constructor
  · rintro (⟨a', s', h1, h2⟩ | ⟨h1, -⟩)
    · cases h1
      exact h2
    · cases h1
  · exact fun h2 => .inl ⟨a, s, by simp, h2⟩

theorem bind_at_fail {m : RM σ α} {s : σ} (h : m s = (fail : RM σ α) s) (k : α → RM σ β) :
    (m >>= k) s = (fail : RM σ β) s := by
  funext o
  simp only [bind_apply, h, fail]
  apply propext
  constructor
  · rintro (⟨a', s', h1, -⟩ | ⟨-, h2⟩)
    · cases h1
    · exact h2
  · exact fun h2 => .inr ⟨by simp, h2⟩

variable (M : CoreInst)

theorem load_at {s : M.St} {a n : Nat} {bs : List UInt8} (h : (M.mem s).read a n = some bs) :
    M.load a n s = (pure bs : RM M.St _) s := by
  unfold CoreInst.load
  rw [bind_at (m := RM.get) (a := s) rfl, h]
  rfl

theorem store_ok {a : Nat} {bs : List UInt8} {s s' : M.St} {u : Unit}
    (h : M.store a bs s (.ok u s')) : ∃ m', (M.mem s).write a bs = some m' ∧ s' = M.setMem s m' := by
  unfold CoreInst.store at h
  rw [bind_at (m := RM.get) (a := s) rfl] at h
  cases hw : (M.mem s).write a bs with
  | none =>
    rw [hw, ofOption_none, RM.fail_bind] at h
    cases h
  | some m' =>
    rw [hw, ofOption_some, RM.pure_bind] at h
    exact ⟨m', rfl, by cases h; rfl⟩

theorem storeAll_ok (hL : MemLawful M) : ∀ (ws : List (Nat × List UInt8)) (s s' : M.St) (u : Unit),
    storeAll M ws s (.ok u s') → writeAll (M.mem s) ws = some (M.mem s')
  | [], s, s', u, h => by
    simp only [storeAll, pure_apply, Out.ok.injEq] at h
    rw [← h.2]
    rfl
  | (a, bs) :: ws, s, s', u, h => by
    simp only [storeAll, bind_apply] at h
    rcases h with ⟨u1, s1, h1, h2⟩ | ⟨-, h2⟩
    · obtain ⟨m1, hw, rfl⟩ := store_ok M h1
      have ih := storeAll_ok hL ws _ s' u h2
      rw [hL.mem_set] at ih
      simp only [writeAll, hw, Option.bind_some, ih]
    · cases h2

theorem flat_scalar {t : ValTy} {n : Nat} (ht : scalarSize t = some n) :
    ∃ ty, t.flat = [ty] := by
  cases t <;> simp [scalarSize] at ht <;> exact ⟨_, rfl⟩

theorem types_cons {t : ValTy} {n : Nat} (ht : scalarSize t = some n) {ts : List ValTy}
    {rs : List Flat} (hr : rs.map (·.type) = ValTy.flatList (t :: ts)) :
    ∃ r rs', rs = r :: rs' ∧ t.flat = [r.type] ∧ rs'.map (·.type) = ValTy.flatList ts := by
  obtain ⟨ty, hty⟩ := flat_scalar ht
  rw [ValTy.flatList, hty] at hr
  match rs, hr with
  | r :: rs', hr =>
    simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at hr
    exact ⟨r, rs', rfl, by rw [hty, hr.1], hr.2⟩

theorem mapM_cons_some {t : ValTy} {ts : List ValTy} {ns : List Nat}
    (h : (t :: ts).mapM scalarSize = some ns) :
    ∃ n, scalarSize t = some n ∧ ∃ ns', ts.mapM scalarSize = some ns' ∧ n :: ns' = ns := by
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, ns', hns, h⟩ := h
  exact ⟨n, hn, ns', hns, by simpa using h⟩

theorem bind_eq_at {m m' : RM σ α} {s : σ} (h : m s = m' s) (k : α → RM σ β) :
    (m >>= k) s = (m' >>= k) s := by
  funext o
  simp only [bind_apply, h]

theorem ofOption_map_cons (v : Val) (x : Option (List Val)) (s : M.St) :
    (RM.ofOption x >>= fun vs => (pure (v :: vs) : RM M.St _)) s =
      (RM.ofOption (x.map (v :: ·)) : RM M.St _) s := by
  cases x <;> simp

/-- **Loading stored fields is the flat lift of their values.** -/
theorem loadFields_at {s : M.St} (rp : Nat) : ∀ (ts : List ValTy) (os ns : List Nat)
    (rs : List Flat), ts.mapM scalarSize = some ns → os.length = ns.length →
    rs.map (·.type) = ValTy.flatList ts →
    (∀ w ∈ fieldWrites rp ts os ns rs, (M.mem s).read w.1 w.2.length = some w.2) →
    loadFields M rp ts os ns s = (RM.ofOption (liftArgs ts rs) : RM M.St _) s
  | [], os, ns, rs, _, _, hr, _ => by
    have hrs : rs = [] := List.map_eq_nil_iff.mp hr
    subst hrs
    rfl
  | t :: ts, o :: os, ns, rs, hn, hl, hr, hw => by
    obtain ⟨n, ht, ns', hts, rfl⟩ := mapM_cons_some hn
    obtain ⟨r, rs', rfl, htr, hrs'⟩ := types_cons ht hr
    have hw0 : (M.mem s).read (rp + o) n = some (leBytes n (normField t r).bits.toNat) := by
      have h0 := hw _ List.mem_cons_self
      rwa [leBytes_length] at h0
    have hws : ∀ w ∈ fieldWrites rp ts os ns' rs', (M.mem s).read w.1 w.2.length = some w.2 :=
      fun w h => hw w (List.mem_cons_of_mem _ h)
    have ih := loadFields_at rp ts os ns' rs' hts (by simpa using hl) hrs' hws
    show (M.load (rp + o) n >>= fun bs => RM.ofOption (loadScalar t bs) >>= fun v =>
      loadFields M rp ts os ns' >>= fun vs => pure (v :: vs)) s = _
    rw [bind_at (load_at M hw0), loadScalar_store ht r htr, liftArgs_cons ht]
    cases lift1 t r with
    | none => rw [ofOption_none, RM.fail_bind]; rfl
    | some v =>
      rw [ofOption_some, RM.pure_bind, bind_eq_at ih, ofOption_map_cons]
      rfl
  | _ :: _, [], _, _, hn, hl, _, _ => by
    obtain ⟨n, _, ns', _, rfl⟩ := mapM_cons_some hn
    simp at hl

end Silmaril.Proofs.Wasm.Jco
