module

public import Silmaril.Wasi.Versions.FsDir3.Defs
public import Silmaril.Wasi.Versions.FsMore.Thms

@[expose] public section

/-!
# The 0.3 `read-directory` stream: theorems

PROVED (standard axioms):

* **`dir3Th_fs`**: the first component of the state of `dir3Th T` is the state of
  `FsMore.fsTh3 T` after the same answers, and every trace `dir3Th T` accepts is accepted by
  `fsTh3 T` (`dir3Th_le_fsTh3`): the theory refines `fsTh3`.
* **`dir3Impl_sat`**: the host `dir3Impl T pre` is a model of `dir3Th T`.
* **`dir3Th_examples`**: a listing of a directory with two entries read one at a time and then
  `DROPPED` is accepted; an entry out of order, an entry that is not there, and a premature
  `DROPPED` are rejected.
-/

namespace Silmaril.Wasi.Versions.FsDir3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult packCopy)
open Silmaril.Wasi.Versions.Net (gated gated_follows gated_run)
open Silmaril.Wasi.Versions.FsMore
open Silmaril.Wasi.Versions.P3 (natV natOf copyOf cStreamRead)

/-- **The first component evolves as `fsTh3`'s state.** -/
theorem dir3Th_fs (T : Tree) (p : List WEv) (q : D3St) :
    (p.foldl (d3Next T) q).fs = p.foldl (fsNext v3 T) q.fs := by
  induction p generalizing q with
  | nil => rfl
  | cons e p ih => exact ih (d3Next T q e)

/-- **`dir3Th` refines `fsTh3`.** -/
theorem dir3Th_le_fsTh3 (T : Tree) {t : List WEv} (h : (dir3Th T).Accepts t) :
    (fsTh3 T).Accepts t := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t e ih =>
    have ht : (dir3Th T).Accepts t := (prefixClosed_accepts _).2 (List.prefix_append t [e]) h
    have hok : d3Ok T (t.foldl (d3Next T) {}) e = true :=
      Silmaril.Wasi.Versions.Net.gated_ok h t e [] rfl
    obtain ⟨q, hq⟩ := (Protocol.accepts_iff_exists _ _).1 (ih ht)
    have hqe : q = t.foldl (fsNext v3 T) {} := (gated_run hq).1
    have hfs : FsMore.fsOk v3 T q e = true := by
      rw [hqe, ← dir3Th_fs T t {}]
      simp only [d3Ok, Bool.and_eq_true] at hok
      exact hok.1
    refine (Protocol.accepts_iff_exists _ _).2 ⟨fsNext v3 T q e, ?_⟩
    rw [Protocol.run_concat, hq]
    simp [fsThV, gated, hfs]

theorem entsOf_map (l : List (Comp × Nat)) : entsOf (.record (l.map entV)) = some l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [entsOf] at ih ⊢
    simp [List.mapM_cons, entV, entOf, charsV_strC, ih]

theorem entsOf_take (l : List (Comp × Nat)) (k : Nat) :
    entsOf (.record ((l.map entV).take k)) = some (l.take k) := by
  rw [← List.map_take]; exact entsOf_map _

theorem entsOf_nil : entsOf (.record []) = some [] := rfl

theorem drChk_readA (l : List (Comp × Nat)) (n : Option Nat) : drChk l (readA l n) = true := by
  unfold readA
  by_cases hl : l.isEmpty
  · simp [hl, drChk, natV, natOf, copyOf, packCopy, CopyResult.toNat,
      Silmaril.Wasm.Component.Async.blocked]
  · have hne : 1 ≤ l.length := by
      cases l with
      | nil => simp at hl
      | cons _ _ => simp
    by_cases hn : n = some 0
    · simp [hl, hn, drChk, natV, natOf, copyOf, packCopy, CopyResult.toNat,
        Silmaril.Wasm.Component.Async.blocked, entsOf_nil]
    · simp [hl, hn, drChk, natV, natOf, copyOf, packCopy, CopyResult.toNat,
        Silmaril.Wasm.Component.Async.blocked, entsOf_take, hne]

theorem readDir_ne_read : v3.readDir ≠ cStreamRead := by
  simp [FsVer.readDir, v3, cStreamRead, Silmaril.Wasi.Versions.P3.canon]

/-- The `FsMore` check passes the `read-directory` answer. -/
theorem fsOk_readDir (T : Tree) (q : FsSt) (a : List Val) (x y : Val) :
    FsMore.fsOk v3 T q (.imp v3.readDir a (some [.record [x, y]])) = true := by
  unfold FsMore.fsOk
  simp only [FsVer.readDir, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt,
    FsVer.getType, FsVer.read, FsVer.write, v3, FnName.mk.injEq, String.reduceEq, and_false,
    ↓reduceIte, and_self]
  split <;> simp [readDirChk, isOkAns]

/-- The `FsMore` check passes every `stream.read` answer. -/
theorem fsOk_streamRead (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    FsMore.fsOk v3 T q (.imp cStreamRead a r) = true := by
  unfold FsMore.fsOk
  simp [FsVer.readDir, FsVer.getDirs, FsVer.openAt, FsVer.stat, FsVer.statAt, FsVer.getType,
    FsVer.read, FsVer.write, FsVer.readEntry, v3, cStreamRead, Silmaril.Wasi.Versions.P3.canon]

/-- The host's `read-directory` answer. -/
theorem dir3Impl_readDir (T : Tree) (pre : List Comp) (p : List WEv) (a : List Val) :
    dir3Impl T pre p v3.readDir a =
      some [.record [natV (2 * p.length + 1), natV (2 * p.length + 2)]] := by
  simp [dir3Impl]

set_option linter.unusedTactic false in
/-- The host's `stream.read` answer. -/
theorem dir3Impl_read (T : Tree) (pre : List Comp) (p : List WEv) (a : List Val) :
    dir3Impl T pre p cStreamRead a =
      (match pendingOf (d3State T p) a with
       | some l => readA l (a[1]?.bind natOf)
       | none => none) := by
  simp [dir3Impl, Ne.symm readDir_ne_read]
  try rfl

/-- The stream check passes the host's `stream.read` answer. -/
theorem dirOk_read (q : D3St) (a : List Val) :
    dirOk q (.imp cStreamRead a
      (match pendingOf q a with
       | some l => readA l (a[1]?.bind natOf)
       | none => none)) = true := by
  simp only [dirOk, ↓reduceIte]
  cases pendingOf q a with
  | none => rfl
  | some l => exact drChk_readA l _

/-- **Every answer of the host passes the check.** -/
theorem dir3Impl_ok (T : Tree) (pre : List Comp) (p : List WEv) (f : FnName) (a : List Val) :
    d3Ok T (p.foldl (d3Next T) {}) (.imp f a (dir3Impl T pre p f a)) = true := by
  have hs : p.foldl (d3Next T) {} = d3State T p := rfl
  unfold d3Ok
  rw [Bool.and_eq_true, hs]
  by_cases h1 : f = v3.readDir
  · rw [h1, dir3Impl_readDir]
    exact ⟨fsOk_readDir T _ a _ _, by simp [dirOk, readDir_ne_read]⟩
  by_cases h2 : f = cStreamRead
  · rw [h2, dir3Impl_read]
    exact ⟨fsOk_streamRead T _ a _, dirOk_read _ a⟩
  have hr : dir3Impl T pre p f a = fsImpl3 T pre p f a := by simp [dir3Impl, h1, h2]
  have hfs : (d3State T p).fs = p.foldl (fsNext v3 T) {} := dir3Th_fs T p {}
  rw [hr, hfs]
  exact ⟨fsImplV_ok (by decide) T pre p f a, by simp [dirOk, h2]⟩

/-- **The host is a model of `dir3Th T`.** -/
theorem dir3Impl_sat {Y : Sig.{0}} {I : Set FnName} (T : Tree) (pre : List Comp) :
    (hostSat (dir3Th T).Accepts).holds (concrete (Y := Y) (I := I) (dir3Impl T pre)) :=
  concrete_sat _ fun _ ht => gated_follows (dir3Impl_ok T pre) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## The theory is not trivial -/

/-- A tree: the preopen `d` with a file `a` and a directory `b`. -/
def treeD : Tree := fun p =>
  if p = [['d']] then some (.dir [['a'], ['b']])
  else if p = [['d'], ['a']] then some (.file [])
  else if p = [['d'], ['b']] then some (.dir [])
  else none

def dirsE : WEv := .imp v3.getDirs [] (some [.record [.record [.u32 0, strC ['d']]]])
def rdE : WEv := .imp v3.readDir [.u32 0] (some [.record [natV 5, natV 6]])
def readE (es : List (Comp × Nat)) : WEv :=
  .imp cStreamRead [natV 5, natV 1] (some [natV (packCopy .completed es.length), .record (es.map entV)])
def dropE : WEv := .imp cStreamRead [natV 5, natV 1] (some [natV (packCopy .dropped 0), .record []])

/-- **Accepted and rejected runs** (`regular-file` is case 5 and `directory` case 2 in 0.3). -/
theorem dir3Th_examples :
    (dir3Th treeD).Accepts [dirsE, rdE, readE [(['a'], 5)], readE [(['b'], 2)], dropE] ∧
    ¬ (dir3Th treeD).Accepts [dirsE, rdE, readE [(['b'], 2)]] ∧
    ¬ (dir3Th treeD).Accepts [dirsE, rdE, readE [(['c'], 5)]] ∧
    ¬ (dir3Th treeD).Accepts [dirsE, rdE, readE [(['a'], 5)], dropE] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.FsDir3
