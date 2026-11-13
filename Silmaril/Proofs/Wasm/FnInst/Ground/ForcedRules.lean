module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Forced
public import Silmaril.Proofs.Wasm.FnInst.Ground.Refute
public import Silmaril.Proofs.Wasm.FnInst.Ground.Rules

@[expose] public section

/-! # Rule lemmas of the deferred bridge, and reverse rule lemmas

`GoodW` lemmas (left sides that write locals), one `run` computation each:

* `goodW_teeSet`, `goodW_setTee`: `local.tee x` ⟷ `local.set x; local.get x` (`tee-form`,
  both directions);
* `goodW_getSet`, `goodW_getTee`: `local.get x; local.set x` ⟶ `local.get x; drop` and
  `local.get x; local.tee x` ⟶ `local.get x` (`rse-line`, original on the left);
* `goodW_selfCopy`: `local.get x; local.set x` ⟶ nothing;
* `goodW_twoSets`, `goodW_oneSet`: the pair of `not_baseSim_twoSets`, both directions.

`Good` lemmas for the reverse direction of frame-free rules, so that both directions go
through `gBaseSim` and hold at every profile:

* `good_neutralC`, `good_neutralC_rev`: `i32.const k; op; X` ⟷ `X` for a right-neutral `k`
  and a consumer `X` of the fragment (`i32.eqz` or a binary operator), the shape of the
  `neutral-ops` stage;
* `good_eqz3_rev`: `i32.eqz` ⟶ `i32.eqz; i32.eqz; i32.eqz`.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

theorem local?_setLocal_self {f : Frame} {x : LocalIdx} {v : Val}
    (hx : x.toNat < f.locals.length) : (f.setLocal x v).local? x = some (some v) := by
  simp [Frame.setLocal, Frame.local?, hx]

/-- A `GoodW` pair from its parts. -/
theorem goodW_mk {ks : List (BitVec 32)} {i : GInstr} {a₁ b : List GInstr}
    (hi : i.isConst = false) (hiL : i.loc = true) (hlp : LocStk a₁)
    (hcom : ∀ f S r, step1 i f ((kvals ks).reverse ++ S) = some r → (run a₁ r.1 r.2).isSome)
    (href : RunRef (ks.map GInstr.const ++ i :: a₁) b) :
    GoodW (ks.map GInstr.const ++ i :: a₁) b :=
  ⟨ks, i, a₁, rfl, hi, hiL, hlp, hcom, href⟩

/-- Local code is local code followed by no stack-only code. -/
theorem locStk_of_loc {a₁ : List GInstr} (h : ∀ j ∈ a₁, j.loc = true) : LocStk a₁ :=
  ⟨a₁, [], by simp, h, by simp⟩

/-! ## `tee-form` -/

theorem run_tee {x : LocalIdx} {f : Frame} {st : List Val} {r : Frame × List Val}
    (h : run [.localTee x] f st = some r) :
    ∃ v X, st = v :: X ∧ x.toNat < f.locals.length ∧ r = (f.setLocal x v, v :: X) := by
  obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, X', rfl, rfl, hx, rfl⟩ := step1_tee_inv h₁
  exact ⟨v, X', rfl, hx, (Option.some.inj h₂).symm⟩

theorem run_setGet {x : LocalIdx} {f : Frame} {v : Val} {X : List Val}
    (hx : x.toNat < f.locals.length) :
    run [.localSet x, .localGet x] f (v :: X) = some (f.setLocal x v, v :: X) := by
  simp [run, step1, hx, local?_setLocal_self hx]

theorem goodW_teeSet (x : LocalIdx) : GoodW [.localTee x] [.localSet x, .localGet x] := by
  refine goodW_mk (ks := []) rfl rfl (locStk_of_loc (by simp [GInstr.loc])) (fun _ _ _ _ => rfl) ?_
  intro f st r h
  obtain ⟨v, X, rfl, hx, rfl⟩ := run_tee h
  exact run_setGet hx

theorem goodW_setTee (x : LocalIdx) : GoodW [.localSet x, .localGet x] [.localTee x] := by
  refine goodW_mk (ks := []) rfl rfl (locStk_of_loc (by simp [GInstr.loc])) ?_ ?_
  · rintro f S ⟨f₁, Y⟩ h
    obtain ⟨v, rfl, hx, rfl⟩ := step1_set_inv h
    simp [run, step1, local?_setLocal_self hx]
  · intro f st r h
    replace h : run [.localSet x, .localGet x] f st = some r := h
    obtain ⟨⟨f₁, X₁⟩, h₁, -⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, rfl, hx, rfl⟩ := step1_set_inv h₁
    rw [run_setGet hx] at h
    rw [← h]
    simp [run, step1, hx]

/-! ## `rse-line`, original on the left -/

theorem run_get_some {x : LocalIdx} {f : Frame} {st : List Val} {r : Frame × List Val}
    {c : List GInstr} (h : run (.localGet x :: c) f st = some r) :
    ∃ v, f.local? x = some (some v) ∧ run c f (v :: st) = some r := by
  obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, hv, rfl, rfl⟩ := step1_get_inv h₁
  exact ⟨v, hv, h₂⟩

theorem lt_of_local {f : Frame} {x : LocalIdx} {v : Val} (hv : f.local? x = some (some v)) :
    x.toNat < f.locals.length :=
  (List.getElem?_eq_some_iff.mp hv).1

theorem get_commits {x : LocalIdx} {c : List GInstr} (hc : ∀ f v S, f.local? x = some (some v) →
    (run c f (v :: S)).isSome) :
    ∀ f S r, step1 (.localGet x) f ((kvals []).reverse ++ S) = some r → (run c r.1 r.2).isSome := by
  rintro f S ⟨f₁, Y⟩ h
  obtain ⟨v, hv, rfl, rfl⟩ := step1_get_inv h
  exact hc f v S hv

theorem goodW_getSet (x : LocalIdx) :
    GoodW [.localGet x, .localSet x] [.localGet x, .drop] := by
  refine goodW_mk (ks := []) rfl rfl (locStk_of_loc (by simp [GInstr.loc])) (get_commits ?_) ?_
  · intro f v S hv
    show ((if x.toNat < f.locals.length then some (f.setLocal x v, S) else none).bind
      fun r => run [] r.1 r.2).isSome = true
    simp only [lt_of_local hv, ↓reduceIte]
    rfl
  · intro f st r h
    replace h : run [.localGet x, .localSet x] f st = some r := h
    obtain ⟨v, hv, -⟩ := run_get_some h
    have hgs : run [.localGet x, .localSet x] f st = some (f, st) := run_getSet hv st false
    rw [hgs] at h
    rw [← h]
    show ((f.local? x).bind fun o => o.map fun v => (f, v :: st)).bind
      (fun r => run [.drop] r.1 r.2) = _
    rw [hv]
    rfl

theorem goodW_getTee (x : LocalIdx) : GoodW [.localGet x, .localTee x] [.localGet x] := by
  refine goodW_mk (ks := []) rfl rfl (locStk_of_loc (by simp [GInstr.loc])) (get_commits ?_) ?_
  · intro f v S hv
    simp [run, step1, lt_of_local hv]
  · intro f st r h
    replace h : run [.localGet x, .localTee x] f st = some r := h
    obtain ⟨v, hv, -⟩ := run_get_some h
    have hgt : run [.localGet x, .localTee x] f st = some (f, v :: st) := run_getSet hv st true
    rw [hgt] at h
    rw [← h]
    simp [run, step1, hv]

/-- A self-copy is removed. -/
theorem goodW_selfCopy (x : LocalIdx) : GoodW [.localGet x, .localSet x] [] := by
  refine goodW_mk (ks := []) rfl rfl (locStk_of_loc (by simp [GInstr.loc])) (get_commits ?_) ?_
  · intro f v S hv
    simp [run, step1, lt_of_local hv]
  · intro f st r h
    replace h : run [.localGet x, .localSet x] f st = some r := h
    obtain ⟨v, hv, -⟩ := run_get_some h
    have hgs : run [.localGet x, .localSet x] f st = some (f, st) := run_getSet hv st false
    rw [hgs] at h
    exact h

/-! ## Two locals: a repeated copy -/

/-- A write of the value just read from `x` (or a write to another local) keeps that read. -/
theorem local?_setLocal_keep {f : Frame} {x y : LocalIdx} {v w : Val}
    (hv : f.local? x = some (some v)) (hw : x.toNat = y.toNat → w = v) :
    (f.setLocal y w).local? x = some (some v) := by
  have hx := lt_of_local hv
  unfold Frame.local? at hv ⊢
  unfold Frame.setLocal
  rw [List.getElem?_set]
  by_cases e : y.toNat = x.toNat
  · simp only [e, ↓reduceIte, hx, hw e.symm]
  · simpa only [e, ↓reduceIte] using hv

theorem run_getSetOther {f : Frame} {x y : LocalIdx} {v : Val} (st : List Val)
    (hv : f.local? x = some (some v)) (hyx : y.toNat ≤ x.toNat) (c : List GInstr) :
    run (.localGet x :: .localSet y :: c) f st = run c (f.setLocal y v) st := by
  have hy : y.toNat < f.locals.length := Nat.lt_of_le_of_lt hyx (lt_of_local hv)
  show ((f.local? x).bind fun o => o.map fun v => (f, v :: st)).bind
    (fun r => (step1 (.localSet y) r.1 r.2).bind fun r => run c r.1 r.2) = _
  rw [hv]
  show (if y.toNat < f.locals.length then some (f.setLocal y v, st) else none).bind _ = _
  simp only [hy, ↓reduceIte]
  rfl

theorem setLocal_twice (f : Frame) (y : LocalIdx) (v : Val) :
    (f.setLocal y v).setLocal y v = f.setLocal y v := setLocal_setLocal f y v v

/-- **Two locals**: a repeated copy `local.get x; local.set y` (with `y ≤ x`) is one copy. The
left side reads `x` twice and writes `y` twice; it cannot get stuck once its first read has
run, because the read proves that `y` is in bounds. -/
theorem goodW_copyTwice {x y : LocalIdx} (hyx : y.toNat ≤ x.toNat) :
    GoodW [.localGet x, .localSet y, .localGet x, .localSet y] [.localGet x, .localSet y] := by
  refine goodW_mk (ks := []) rfl rfl (locStk_of_loc (by simp [GInstr.loc])) (get_commits ?_) ?_
  · intro f v S hv
    rw [run_getSetOther_tail hv hyx]
    rfl
  · intro f st r h
    replace h : run [.localGet x, .localSet y, .localGet x, .localSet y] f st = some r := h
    obtain ⟨v, hv, -⟩ := run_get_some h
    have hv' : (f.setLocal y v).local? x = some (some v) :=
      local?_setLocal_keep hv (fun _ => rfl)
    rw [run_getSetOther st hv hyx, run_getSetOther st hv' hyx, setLocal_twice] at h
    rw [run_getSetOther st hv hyx]
    exact h
where
  run_getSetOther_tail {f : Frame} {v : Val} {S : List Val} (hv : f.local? x = some (some v))
      (hyx : y.toNat ≤ x.toNat) :
      run [.localSet y, .localGet x, .localSet y] f (v :: S) =
        some ((f.setLocal y v).setLocal y v, S) := by
    have hy : y.toNat < f.locals.length := Nat.lt_of_le_of_lt hyx (lt_of_local hv)
    have hv' : (f.setLocal y v).local? x = some (some v) :=
      local?_setLocal_keep hv (fun _ => rfl)
    show (if y.toNat < f.locals.length then some (f.setLocal y v, S) else none).bind _ = _
    simp only [hy, ↓reduceIte, Option.bind_some]
    exact run_getSetOther S hv' hyx []

theorem goodW_copyOnce {x y : LocalIdx} (hyx : y.toNat ≤ x.toNat) :
    GoodW [.localGet x, .localSet y] [.localGet x, .localSet y, .localGet x, .localSet y] := by
  refine goodW_mk (ks := []) rfl rfl (locStk_of_loc (by simp [GInstr.loc])) (get_commits ?_) ?_
  · intro f v S hv
    have hy : y.toNat < f.locals.length := Nat.lt_of_le_of_lt hyx (lt_of_local hv)
    show ((if y.toNat < f.locals.length then some (f.setLocal y v, S) else none).bind
      fun r => run [] r.1 r.2).isSome = true
    simp only [hy, ↓reduceIte]
    rfl
  · intro f st r h
    replace h : run [.localGet x, .localSet y] f st = some r := h
    obtain ⟨v, hv, -⟩ := run_get_some h
    have hv' : (f.setLocal y v).local? x = some (some v) := local?_setLocal_keep hv (fun _ => rfl)
    rw [run_getSetOther st hv hyx []] at h
    rw [run_getSetOther st hv hyx, run_getSetOther st hv' hyx, setLocal_twice]
    exact h

/-! ## A second read, then stack-only code -/

/-- `local.get x; local.get x; drop` ⟶ `local.get x`: the left side's rest is a read (forced)
followed by stack-only code (`drop`), the second kind of runtime pair. -/
theorem goodW_getGetDrop (x : LocalIdx) :
    GoodW [.localGet x, .localGet x, .drop] [.localGet x] := by
  refine goodW_mk (ks := []) rfl rfl ⟨[.localGet x], [.drop], rfl, by simp [GInstr.loc],
    by simp [GInstr.stk]⟩ (get_commits ?_) ?_
  · intro f v S hv
    show (((f.local? x).bind fun o => o.map fun v' => (f, v' :: v :: S)).bind
      fun r => run [.drop] r.1 r.2).isSome = true
    rw [hv]
    rfl
  · show RunRef [.localGet x, .localGet x, .drop] [.localGet x]
    intro f st r h
    replace h : run [.localGet x, .localGet x, .drop] f st = some r := h
    obtain ⟨v, hv, h'⟩ := run_get_some h
    have e : run [.localGet x, .drop] f (v :: st) = some (f, v :: st) := by
      show (((f.local? x).bind fun o => o.map fun v' => (f, v' :: v :: st)).bind
        fun r => run [.drop] r.1 r.2) = _
      rw [hv]
      rfl
    rw [e] at h'
    rw [← h']
    show ((f.local? x).bind fun o => o.map fun v' => (f, v' :: st)).bind
      (fun r => run [] r.1 r.2) = _
    rw [hv]
    rfl

theorem goodW_getGetDrop_rev (x : LocalIdx) :
    GoodW [.localGet x] [.localGet x, .localGet x, .drop] := by
  refine goodW_mk (ks := []) rfl rfl (locStk_of_loc (by simp)) (fun _ _ _ _ => rfl) ?_
  intro f st r h
  replace h : run [.localGet x] f st = some r := h
  obtain ⟨v, hv, h'⟩ := run_get_some h
  rw [← h']
  show (((f.local? x).bind fun o => o.map fun v' => (f, v' :: st)).bind
    fun r => run [.localGet x, .drop] r.1 r.2) = _
  rw [hv]
  show (((f.local? x).bind fun o => o.map fun v' => (f, v' :: v :: st)).bind
    fun r => run [.drop] r.1 r.2) = _
  rw [hv]
  rfl

/-! ## Two stores to one local -/

theorem run_constSet_eq {x : LocalIdx} {k : BitVec 32} {f : Frame} {st : List Val}
    (c : List GInstr) (hx : x.toNat < f.locals.length) :
    run (.const k :: .localSet x :: c) f st = run c (f.setLocal x (Val.i32 k)) st := by
  show (if x.toNat < f.locals.length then some (f.setLocal x (Val.i32 k), st) else none).bind
    (fun r => run c r.1 r.2) = _
  simp only [hx, ↓reduceIte]
  rfl

theorem goodW_twoSets : GoodW twoSets oneSet := by
  refine goodW_mk (ks := [1]) (i := .localSet l0) (a₁ := [.const 2, .localSet l0]) rfl
    rfl (locStk_of_loc (by simp [GInstr.loc])) ?_ runRef_twoSets
  rintro f S ⟨f₁, Y⟩ h
  obtain ⟨v, -, hx, rfl⟩ := step1_set_inv h
  have hx' : l0.toNat < (f.setLocal l0 v).locals.length := by rw [setLocal_length]; exact hx
  rw [run_constSet_eq [] hx']
  rfl

theorem goodW_oneSet : GoodW oneSet twoSets := by
  refine goodW_mk (ks := [2]) (i := .localSet l0) (a₁ := []) rfl rfl (locStk_of_loc (by simp [GInstr.loc]))
    (fun _ _ _ _ => rfl) ?_
  intro f st r h
  obtain ⟨hx, h₁⟩ := run_constSet [] h
  have hx' : l0.toNat < (f.setLocal l0 (Val.i32 1)).locals.length := by
    rw [setLocal_length]; exact hx
  show run (.const 1 :: .localSet l0 :: [.const 2, .localSet l0]) f st = some r
  rw [run_constSet_eq _ hx, run_constSet_eq _ hx', setLocal_setLocal]
  exact h₁

/-! ## Reverse rule lemmas for the frame-free bridge -/

/-- The consumers of the fragment: `i32.eqz` and the binary operators. -/
def Consumer (X : GInstr) : Prop := X = .eqz ∨ ∃ c, X = .bin c

/-- A consumer that runs had an `i32` on top of the stack. -/
theorem consumer_top {X : GInstr} (hX : Consumer X) {f : Frame} {st : List Val}
    {r : Frame × List Val} (h : run [X] f st = some r) : ∃ y S, st = Val.i32 y :: S := by
  obtain ⟨⟨f₁, X₁⟩, h₁, -⟩ := Option.bind_eq_some_iff.mp h
  rcases hX with rfl | ⟨c, rfl⟩
  · obtain ⟨-, h₁'⟩ := step1_stk_inv rfl h₁
    obtain ⟨x, X', rfl, -⟩ := stepS_eqz_inv h₁'
    exact ⟨x, X', rfl⟩
  · obtain ⟨-, h₁'⟩ := step1_stk_inv rfl h₁
    obtain ⟨x, y, X', rfl, -⟩ := stepS_bin_inv h₁'
    exact ⟨y, _, rfl⟩

theorem consumer_stk {X : GInstr} (hX : Consumer X) : X.stk = true ∧ X.isConst = false := by
  rcases hX with rfl | ⟨c, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- A neutral operation on an `i32` on top of the stack does nothing. -/
theorem run_neutral {b : Bin} {k : BitVec 32} (hk : Neutral b k) (f : Frame) (y : BitVec 32)
    (S : List Val) : run [.const k, .bin b] f (Val.i32 y :: S) = some (f, Val.i32 y :: S) := by
  have h : run [.const k, .bin b] f (Val.i32 y :: S) = some (f, Val.i32 (b.eval y k) :: S) := rfl
  rw [h, hk y]

theorem good_neutralC {b : Bin} {k : BitVec 32} (hk : Neutral b k) {X : GInstr}
    (hX : Consumer X) : Good [.const k, .bin b, X] [X] := by
  refine Or.inl ⟨⟨by rcases hX with rfl | ⟨c, rfl⟩ <;> simp [GInstr.stk],
    ⟨.bin b, by simp, rfl⟩⟩, ?_⟩
  intro f st r h
  have h' : (run [.const k, .bin b] f st).bind (fun r => run [X] r.1 r.2) = some r := by
    rw [← run_append]
    exact h
  obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h'
  have h₀ := good_neutral hk
  rcases h₀ with ⟨-, href⟩ | ⟨⟨x, L, he, -⟩, -⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (href f st _ h₁))
    exact h₂
  · cases he

theorem good_neutralC_rev {b : Bin} {k : BitVec 32} (hk : Neutral b k) {X : GInstr}
    (hX : Consumer X) : Good [X] [.const k, .bin b, X] := by
  refine Or.inl ⟨⟨by simp [(consumer_stk hX).1], ⟨X, by simp, (consumer_stk hX).2⟩⟩, ?_⟩
  intro f st r h
  obtain ⟨y, S, rfl⟩ := consumer_top hX h
  have e : run [.const k, .bin b, X] f (Val.i32 y :: S) =
      (run [.const k, .bin b] f (Val.i32 y :: S)).bind (fun r => run [X] r.1 r.2) :=
    run_append [.const k, .bin b] [X] f _
  rw [e, run_neutral hk]
  exact h

theorem good_eqz3_rev : Good [.eqz] [.eqz, .eqz, .eqz] := by
  refine Or.inl ⟨⟨by simp [GInstr.stk], ⟨.eqz, by simp, rfl⟩⟩, ?_⟩
  intro f st r h
  obtain ⟨y, S, rfl⟩ := consumer_top (Or.inl rfl) h
  have h₁ : run [.eqz] f (Val.i32 y :: S) = some (f, Val.i32 (intTestOp .i32 .eqz y) :: S) := rfl
  have h₃ : run [.eqz, .eqz, .eqz] f (Val.i32 y :: S) = some (f, Val.i32 (intTestOp .i32 .eqz
      (intTestOp .i32 .eqz (intTestOp .i32 .eqz y))) :: S) := rfl
  rw [h₁] at h
  rw [h₃, eqz_eqz_eqz]
  exact h

end Silmaril.Wasm.FnInst.Ground
