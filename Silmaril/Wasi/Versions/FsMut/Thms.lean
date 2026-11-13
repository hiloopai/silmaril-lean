module

public import Silmaril.Wasi.Versions.FsMut.Defs
public import Silmaril.Wasi.Versions.FsMore.Thms

@[expose] public section

/-!
# `wasi:filesystem` mutations: theorems

PROVED (standard axioms):

* **`mutImplV_sat`**: for every version `V`, tree `T` and preopen names `pre`, the host
  `mutImplV V T pre` is a model of `mutThV V T`; `mutImpl2_sat` and `mutImpl3_sat` are the 0.2
  and 0.3 instances.
* **`mutTh2_accepts`, `mutTh2_rejects`**: the theory is not trivial. Accepted: create a
  directory, see it, unlink a file, rename the directory and see it at the new name, create a
  symbolic link and read it back, link a file. Rejected: seeing an unlinked file, seeing a
  directory under its old name after a rename, reading a link back with other contents,
  creating a directory twice, linking an absent file, removing a file as a directory.
-/

namespace Silmaril.Wasi.Versions.FsMut

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net (gated gated_follows)
open Silmaril.Wasi.Versions.FsMore

theorem dirsM_ok (v : Path → Option MNode) (b : Nat) (pre : List Comp) :
    (preopensOf (some [.record (numbered b (pre.filter fun n => isDirM (v [n])))])).all
      (fun x => isDirM (v [x.2])) = true := by
  simp only [preopensOf_numbered, List.all_map, List.all_eq_true]
  intro x hx
  have := (List.of_mem_zip hx).1
  simpa [Function.comp] using (List.mem_filter.1 this).2

theorem rlChk_rlA (V : FsVer) (o : Option MNode) : rlChk o (rlA V o) = true := by
  rcases o with _ | (_ | _ | t) <;> simp [rlA, rlChk, okA, errA, charsV_strC]

theorem okNeeds_condA (V : FsVer) (f : FnName) (h : BitVec 32) (c : Option Bool) :
    (match c with
     | some c' => okNeeds c' (condA V f h c)
     | none => true) = true := by
  rcases c with _ | _ | _
  · rfl
  · simp [condA, okNeeds, errA, isOkAns]
  · simp [okNeeds]

/-- **Every answer of the concrete host passes the check.** -/
theorem mutImplV_ok (V : FsVer) (T : Tree) (pre : List Comp) (p : List WEv) (f : FnName)
    (a : List Val) :
    mutOk V (p.foldl (mutNext V) (mutInit T)) (.imp f a (mutImplV V T pre p f a)) = true := by
  have hs : p.foldl (mutNext V) (mutInit T) = mutState V T p := rfl
  rw [hs]
  unfold mutOk mutImplV
  dsimp only
  by_cases h1 : f = V.getDirs
  · simp only [h1, ↓reduceIte, dirsM_ok, Bool.or_true]
  simp only [h1, ↓reduceIte]
  by_cases h2 : f = V.readlink
  · simp only [h2, ↓reduceIte]
    cases at_ (mutState V T p) a 1 with
    | none => rfl
    | some pa => simp only [rlChk_rlA, Bool.or_true]
  simp only [h2, ↓reduceIte]
  by_cases h3 : f ∈ condFns V
  · simp only [h3, ↓reduceIte]
    exact okNeeds_condA V f _ _
  · simp only [h3, ↓reduceIte]
    cases cond V (mutState V T p) f a <;> simp [okNeeds, isOkAns]

/-- **The concrete mutation host is a model of the mutation theory.** -/
theorem mutImplV_sat {Y : Sig.{0}} {I : Set FnName} (V : FsVer) (T : Tree) (pre : List Comp) :
    (hostSat (mutThV V T).Accepts).holds (concrete (Y := Y) (I := I) (mutImplV V T pre)) :=
  concrete_sat _ fun _ ht => gated_follows (mutImplV_ok V T pre) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-- **The 0.2 mutation host is a model of the 0.2 mutation theory.** -/
theorem mutImpl2_sat {Y : Sig.{0}} {I : Set FnName} (T : Tree) (pre : List Comp) :
    (hostSat (mutTh2 T).Accepts).holds (concrete (Y := Y) (I := I) (mutImpl2 T pre)) :=
  mutImplV_sat v2 T pre

/-- **The 0.3 mutation host is a model of the 0.3 mutation theory.** -/
theorem mutImpl3_sat {Y : Sig.{0}} {I : Set FnName} (T : Tree) (pre : List Comp) :
    (hostSat (mutTh3 T).Accepts).holds (concrete (Y := Y) (I := I) (mutImpl3 T pre)) :=
  mutImplV_sat v3 T pre

/-! ## The theory is not trivial -/

/-- A tree: the preopen `d` holding the file `f`. -/
def treeM : Tree := fun p =>
  if p = [['d']] then some (.dir [['f']])
  else if p = [['d'], ['f']] then some (.file [7])
  else none

def pfl : Val := .record [.bool false]
def dirsE : WEv := .imp v2.getDirs [] (some [.record [.record [.u32 0, strC ['d']]]])
def mkdirE (n : Comp) : WEv := .imp v2.createDir [.u32 0, strC n] okU
def statE (n : Comp) : WEv := .imp v2.statAt [.u32 0, pfl, strC n] (okA (.record []))
def unlinkE (n : Comp) : WEv := .imp v2.unlink [.u32 0, strC n] okU
def rmdirE (n : Comp) : WEv := .imp v2.removeDir [.u32 0, strC n] okU
def renameE (o n : Comp) : WEv := .imp v2.rename [.u32 0, strC o, .u32 0, strC n] okU
def symE (t n : Comp) : WEv := .imp v2.symlink [.u32 0, strC t, strC n] okU
def rlE (n t : Comp) : WEv := .imp v2.readlink [.u32 0, strC n] (okA (strC t))
def linkE (o n : Comp) : WEv := .imp v2.linkAt [.u32 0, pfl, strC o, .u32 0, strC n] okU

/-- **An accepted run.** -/
theorem mutTh2_accepts :
    (mutTh2 treeM).Accepts [dirsE, mkdirE ['x'], statE ['x'], linkE ['f'] ['g'],
      unlinkE ['f'], statE ['g'], renameE ['x'] ['y'], statE ['y'], symE ['g'] ['l'],
      rlE ['l'] ['g']] := by
  unfold Protocol.Accepts; decide +kernel

/-- **Rejected runs.** -/
theorem mutTh2_rejects :
    ¬ (mutTh2 treeM).Accepts [dirsE, unlinkE ['f'], statE ['f']] ∧
    ¬ (mutTh2 treeM).Accepts [dirsE, mkdirE ['x'], renameE ['x'] ['y'], statE ['x']] ∧
    ¬ (mutTh2 treeM).Accepts [dirsE, symE ['f'] ['l'], rlE ['l'] ['g']] ∧
    ¬ (mutTh2 treeM).Accepts [dirsE, mkdirE ['x'], mkdirE ['x']] ∧
    ¬ (mutTh2 treeM).Accepts [dirsE, linkE ['z'] ['g']] ∧
    ¬ (mutTh2 treeM).Accepts [dirsE, rmdirE ['f']] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.FsMut
