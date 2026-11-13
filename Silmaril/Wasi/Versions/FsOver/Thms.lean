module

public import Silmaril.Wasi.Versions.FsOver.Defs
public import Silmaril.Wasi.Versions.FwdT.Thms
public import Silmaril.Wasi.Versions.FsMore.Thms

@[expose] public section

/-!
# Filesystem 0.3 over 0.2: theorems

PROVED (standard axioms):

* **`statChk_tr`**, **`typeChk_tr`**, **`openChk_tr`**: a translated answer passes the 0.3 check
  whenever the 0.2 answer passes the 0.2 check (the kinds shift by one; `no-entry` is `20` in
  0.2 and `19` in 0.3, and only `20` translates to `19`).
* **`fs_sim`**: equal `FsMore` states are a simulation of the forwarder (`FwdT.FwdSim`).
* **`fs3Over2_model`**: over every host of `fsTh2 T`, the forwarder `fs3Over2` is a model of
  `fsTh3 T`, for every tree `T`.
-/

namespace Silmaril.Wasi.Versions.FsOver

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions (FwdSim fwdT_model ofSBody)
open Silmaril.Wasi.Versions.FsMore

/-! ## The translations keep the checks -/

theorem kindOf_succ (n : Node) : kindOf v2 n = kindOf v3 n + 1 := by
  cases n <;> rfl

theorem fsE2to3_noEntry {k : Nat} (h : fsE2to3 k = 19) : k = 20 := by
  match k, h with
  | k + 2, h => simp only [fsE2to3] at h; omega

theorem statChk_tr (o : Option Node) (r : Option (List Val)) (h : statChk v2 o r = true) :
    statChk v3 o (statTr r) = true := by
  unfold statTr
  split
  · next k lc sz ts =>
    cases o with
    | none => simp [statChk, isOkAns] at h
    | some n =>
      cases k with
      | zero => simp [statChk, kind2to3]
      | succ k =>
        have h' : (k + 1 == kindOf v2 n && sizeOk n sz) = true := by simpa [statChk] using h
        simpa [statChk, kind2to3, kindOf_succ] using h'
  · cases o <;> simp [statChk, errTr, isOkAns]
  · cases o <;> simp [statChk, isOkAns]

theorem typeChk_tr (o : Option Node) (r : Option (List Val)) (h : typeChk v2 o r = true) :
    typeChk v3 o (typeTr r) = true := by
  unfold typeTr
  split
  · next k =>
    cases o with
    | none => simp [typeChk, isOkAns] at h
    | some n =>
      cases k with
      | zero => simp [typeChk, kind2to3]
      | succ k =>
        have h' : (k + 1 == kindOf v2 n) = true := by simpa [typeChk] using h
        simpa [typeChk, kind2to3, kindOf_succ] using h'
  · cases o <;> simp [typeChk, errTr, isOkAns]
  · cases o <;> simp [typeChk, isOkAns]

theorem openChk_tr (dirF : Bool) (o : Option Node) (r : Option (List Val))
    (h : openChk v2 dirF o r = true) : openChk v3 dirF o (openTr r) = true := by
  unfold openTr
  split
  · next k =>
    unfold errTr fsEcV3
    by_cases ho : fsE2to3 k = fsOther3
    · simp [ho, openChk]
    · have h' : (k != 20 || o.isNone) = true := by simpa [openChk, v2] using h
      have hk : (fsE2to3 k != 19 || o.isNone) = true := by
        by_cases h19 : fsE2to3 k = 19
        · have ho' : o.isNone = true := by simpa [fsE2to3_noEntry h19] using h'
          simp [ho']
        · simp [h19]
      simpa [ho, openChk, v3] using hk
  · next r' hne =>
    unfold openChk at h ⊢
    split <;> simp_all

/-! ## The forwarder on each function -/

theorem fsTo_eq : fsTo v3.getDirs = v2.getDirs ∧ fsTo v3.openAt = v2.openAt ∧
    fsTo v3.stat = v2.stat ∧ fsTo v3.statAt = v2.statAt ∧ fsTo v3.getType = v2.getType := by
  simp [fsTo, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt, FsVer.getType, v2, v3]

theorem fsTr_eq (r : Option (List Val)) : fsTr v3.getDirs r = r ∧ fsTr v3.openAt r = openTr r ∧
    fsTr v3.stat r = statTr r ∧ fsTr v3.statAt r = statTr r ∧ fsTr v3.getType r = typeTr r := by
  simp [fsTr, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt, FsVer.getType, v3]

theorem fsNext_quiet (V : FsVer) (T : Tree) (q : FsSt) {f : FnName} (a : List Val)
    (r : Option (List Val)) (h1 : f ≠ V.getDirs) (h2 : f ≠ V.openAt) (h3 : f ≠ V.write)
    (h4 : f ≠ V.readDir) (h5 : f ≠ V.readEntry) : fsNext V T q (.imp f a r) = q := by
  unfold fsNext
  simp [h1, h2, h3, h4, h5]

theorem fsNext_getDirs (V : FsVer) (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    fsNext V T q (.imp V.getDirs a r) =
      { q with descs := (preopensOf r).map (fun x => (x.1, [x.2])) ++ q.descs } := by
  unfold fsNext
  simp

theorem fsNext_openAt_err (V : FsVer) (T : Tree) (q : FsSt) (hV : V.openAt ≠ V.getDirs)
    (a : List Val) (x : Option Val) : fsNext V T q (.imp V.openAt a (some [.variant 1 x])) = q := by
  unfold fsNext
  simp only [hV, ↓reduceIte]
  cases atPath q a <;> simp

theorem fsNext_openAt_same (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    fsNext v2 T q (.imp v2.openAt a r) = fsNext v3 T q (.imp v3.openAt a r) := by
  unfold fsNext
  simp [FsVer.getDirs, FsVer.openAt, v2, v3]

/-- One forwarded answer: the 0.3 check passes and the next states agree. -/
abbrev Step1 (T : Tree) (q : FsSt) (f g : FnName) (a : List Val) (r r' : Option (List Val)) :
    Prop :=
  FsMore.fsOk v2 T q (.imp g a r) = true →
    FsMore.fsOk v3 T q (.imp f a r') = true ∧
      fsNext v2 T q (.imp g a r) = fsNext v3 T q (.imp f a r')

theorem step_getDirs (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    Step1 T q v3.getDirs v2.getDirs a r r := by
  intro h
  constructor
  · simpa [FsMore.fsOk, FsVer.getDirs, v2, v3] using h
  · rw [fsNext_getDirs, fsNext_getDirs]

theorem step_stat (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    Step1 T q v3.stat v2.stat a r (statTr r) := by
  intro h
  constructor
  · cases hp : selfPath q a with
    | none => simp [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, v3, hp]
    | some p =>
      have h2 : statChk v2 (nodeAt T q p) r = true := by
        simpa [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, v2, hp] using h
      simpa [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, v3, hp] using
        statChk_tr _ _ h2
  · rw [fsNext_quiet v2 T q a _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fsNext_quiet v3 T q a _ (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem step_statAt (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    Step1 T q v3.statAt v2.statAt a r (statTr r) := by
  intro h
  constructor
  · cases hp : atPath q a with
    | none => simp [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt, v3, hp]
    | some p =>
      have h2 : statChk v2 (nodeAt T q p) r = true := by
        simpa [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt, v2, hp] using h
      simpa [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt, v3, hp] using
        statChk_tr _ _ h2
  · rw [fsNext_quiet v2 T q a _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fsNext_quiet v3 T q a _ (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem step_getType (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    Step1 T q v3.getType v2.getType a r (typeTr r) := by
  intro h
  constructor
  · cases hp : selfPath q a with
    | none => simp [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt,
        FsVer.getType, v3, hp]
    | some p =>
      have h2 : typeChk v2 (nodeAt T q p) r = true := by
        simpa [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt,
          FsVer.getType, v2, hp] using h
      simpa [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt,
        FsVer.getType, v3, hp] using typeChk_tr _ _ h2
  · rw [fsNext_quiet v2 T q a _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fsNext_quiet v3 T q a _ (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem step_openAt (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    Step1 T q v3.openAt v2.openAt a r (openTr r) := by
  intro h
  constructor
  · cases hp : atPath q a with
    | none => simp [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, v3, hp]
    | some p =>
      have h2 : (createSet a || openChk v2 (dirSet a) (nodeAt T q p) r) = true := by
        simpa [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, v2, hp] using h
      have h3 : (createSet a || openChk v3 (dirSet a) (nodeAt T q p) (openTr r)) = true := by
        cases hc : createSet a
        · simpa [hc] using openChk_tr _ _ _ (by simpa [hc] using h2)
        · rfl
      simpa [FsMore.fsOk, FsVer.getDirs, FsVer.openAt, v3, hp] using h3
  · unfold openTr
    split
    · rw [fsNext_openAt_err v2 T q (by decide) a _, errTr, fsNext_openAt_err v3 T q (by decide) a _]
    · exact fsNext_openAt_same T q a r

/-! ## The relation -/

/-- **Equal `FsMore` states simulate the forwarder.** -/
theorem fs_sim (T : Tree) :
    FwdSim fsX3 fsTo fsTr ({} : FsSt) (fsNext v2 T) (FsMore.fsOk v2 T) {} (fsNext v3 T)
      (FsMore.fsOk v3 T) (fun qT qG => qT = qG) where
  init := rfl
  step := by
    intro qT qG f a r hf hR hok
    have hf' : f = v3.getDirs ∨ f = v3.openAt ∨ f = v3.stat ∨ f = v3.statAt ∨ f = v3.getType := by
      simpa only [fsX3, Set.mem_insert_iff, Set.mem_singleton_iff] using hf
    rw [← hR]
    rcases hf' with rfl | rfl | rfl | rfl | rfl
    · rw [fsTo_eq.1, (fsTr_eq r).1] at *; exact step_getDirs T qT a r hok
    · rw [fsTo_eq.2.1, (fsTr_eq r).2.1] at *; exact step_openAt T qT a r hok
    · rw [fsTo_eq.2.2.1, (fsTr_eq r).2.2.1] at *; exact step_stat T qT a r hok
    · rw [fsTo_eq.2.2.2.1, (fsTr_eq r).2.2.2.1] at *; exact step_statAt T qT a r hok
    · rw [fsTo_eq.2.2.2.2, (fsTr_eq r).2.2.2.2] at *; exact step_getType T qT a r hok

/-- **Filesystem 0.3 over 0.2**: over every host of the 0.2 theory of the tree `T`, the
forwarder is a model of the 0.3 theory of the same tree. -/
theorem fs3Over2_model (T : Tree) {Y : Sig.{0}} {η : Host Y fsI2}
    (hη : (hostSat (fsTh2 T).Accepts).holds η) :
    (hostSat (fsTh3 T).Accepts).holds (link η (ofSBody fs3Over2 ())) :=
  fwdT_model (fs_sim T) hη

end Silmaril.Wasi.Versions.FsOver
