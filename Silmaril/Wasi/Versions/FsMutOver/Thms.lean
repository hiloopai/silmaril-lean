module

public import Silmaril.Wasi.Versions.FsMutOver.Defs
public import Silmaril.Wasi.Versions.FsMut.Thms
public import Silmaril.Wasi.Versions.FwdT.Thms

@[expose] public section

/-!
# Filesystem mutations 0.3 over 0.2: theorems

PROVED (standard axioms):

* **`mutOk_ver`**, **`mutNext_ver`**: the mutation theory reads only the method name, so a 0.3
  answer is checked, and changes the state, as the same answer of the 0.2 function.
* **`mutOk_err`**, **`mutNext_err`**: error answers are never rejected and change nothing.
* **`mut3Over2_model`**: over every host of `mutTh2 T`, the forwarder is a model of `mutTh3 T`.
-/

namespace Silmaril.Wasi.Versions.FsMutOver

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions (FwdSim fwdT_model ofSBody)
open Silmaril.Wasi.Versions.FsMore
open Silmaril.Wasi.Versions.FsMut

theorem mutOk_ver (q : MSt) (m : String) (a : List Val) (r : Option (List Val)) :
    mutOk v3 q (.imp ⟨v3.types, m⟩ a r) = mutOk v2 q (.imp ⟨v2.types, m⟩ a r) := by
  simp [mutOk, FsMut.cond, FsVer.getDirs, FsVer.readlink, FsVer.openAt, FsVer.statAt,
    FsVer.setTimesAt, FsVer.createDir, FsVer.removeDir, FsVer.unlink, FsVer.rename,
    FsVer.linkAt, FsVer.symlink, v2, v3]

theorem mutNext_ver (q : MSt) (m : String) (a : List Val) (r : Option (List Val)) :
    mutNext v3 q (.imp ⟨v3.types, m⟩ a r) = mutNext v2 q (.imp ⟨v2.types, m⟩ a r) := by
  simp [mutNext, FsVer.getDirs, FsVer.openAt, FsVer.createDir, FsVer.removeDir, FsVer.unlink,
    FsVer.rename, FsVer.linkAt, FsVer.symlink, v2, v3]

theorem mutOk_dirs (q : MSt) (a : List Val) (r : Option (List Val)) :
    mutOk v3 q (.imp v3.getDirs a r) = mutOk v2 q (.imp v2.getDirs a r) := by
  simp [mutOk]

theorem mutNext_dirs (q : MSt) (a : List Val) (r : Option (List Val)) :
    mutNext v3 q (.imp v3.getDirs a r) = mutNext v2 q (.imp v2.getDirs a r) := by
  simp [mutNext]

theorem mutOk_err (V : FsVer) (q : MSt) (f : FnName) (a : List Val) (x : Option Val) :
    mutOk V q (.imp f a (some [.variant 1 x])) = true := by
  unfold mutOk
  by_cases h1 : f = V.getDirs
  · simp [h1, preopensOf]
  dsimp only
  simp only [h1, ↓reduceIte]
  by_cases h2 : f = V.readlink
  · simp only [h2, ↓reduceIte]
    cases at_ q a 1 <;> simp [rlChk]
  · simp only [h2, ↓reduceIte]
    cases FsMut.cond V q f a <;> simp [okNeeds, isOkAns]

theorem mutNext_err (V : FsVer) (q : MSt) (f : FnName) (a : List Val) (x : Option Val) :
    mutNext V q (.imp f a (some [.variant 1 x])) = q := by
  unfold mutNext
  by_cases h1 : f = V.getDirs
  · simp [h1, preopensOf]
  · simp [h1, isOkAns]

/-- The 0.3 answer is checked, and moves the state, as the 0.2 one of the paired function. -/
theorem mto_ver (q : MSt) (f : FnName) (hf : f ∈ mutX3) (a : List Val) (r : Option (List Val)) :
    mutOk v3 q (.imp f a r) = mutOk v2 q (.imp (mto f) a r) ∧
      mutNext v3 q (.imp f a r) = mutNext v2 q (.imp (mto f) a r) := by
  by_cases h : f = v3.getDirs
  · rw [h, show mto v3.getDirs = v2.getDirs by simp [mto]]
    exact ⟨mutOk_dirs q a r, mutNext_dirs q a r⟩
  · have hi : f.iface = v3.types := by
      rcases hf with h' | ⟨hi, _⟩
      · exact absurd h' h
      · exact hi
    have hfe : f = ⟨v3.types, f.fn⟩ := by cases f; simp_all
    have hm : mto f = ⟨v2.types, f.fn⟩ := by simp [mto, h]
    rw [hm, hfe]
    exact ⟨mutOk_ver q f.fn a r, mutNext_ver q f.fn a r⟩

/-- **Equal states simulate the forwarder.** -/
theorem mut_sim (T : Tree) :
    FwdSim mutX3 mto (fun _ r => FsOver.openTr r) (mutInit T) (mutNext v2) (mutOk v2)
      (mutInit T) (mutNext v3) (mutOk v3) (fun qT qG => qT = qG) where
  init := rfl
  step := by
    intro qT qG f a r hf hR hok
    rw [← hR]
    unfold FsOver.openTr
    split
    · exact ⟨mutOk_err v3 qT f a _, by rw [mutNext_err, FsOver.errTr, mutNext_err]⟩
    · have hv := mto_ver qT f hf a r
      exact ⟨hv.1 ▸ hok, hv.2.symm⟩

/-- **Filesystem mutations 0.3 over 0.2.** -/
theorem mut3Over2_model (T : Tree) {Y : Sig.{0}} {η : Host Y mutI2}
    (hη : (hostSat (mutTh2 T).Accepts).holds η) :
    (hostSat (mutTh3 T).Accepts).holds (link η (ofSBody mut3Over2 ())) :=
  fwdT_model (mut_sim T) hη

end Silmaril.Wasi.Versions.FsMutOver
