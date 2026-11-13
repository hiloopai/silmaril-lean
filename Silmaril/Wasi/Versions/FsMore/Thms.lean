module

public import Silmaril.Wasi.Versions.FsMore.Defs
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# `wasi:filesystem` beyond the read slice: theorems

PROVED (standard axioms):

* **`fsImplV_sat`**: for every version `V` (whose `not-directory` and `no-entry` differ), tree `T` and preopen names `pre`, the concrete host
  `fsImplV V T pre` is a model of `fsThV V T`; so **`fsImpl2_sat`** (0.2) and
  **`fsImpl3_sat`** (0.3).
* The theory is not trivial: **`fsTh2_rejects`** (a `stat` of a one-byte file answered with size
  `2` is rejected, as is a `read` answering bytes the file does not have, a `read-directory-entry`
  naming an entry that is not there, and `ok` from `open-at` of an absent path), and
  **`fsTh2_accepts`** (the run that opens the file, writes to it and reads back is accepted).
-/

namespace Silmaril.Wasi.Versions.FsMore

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net (gated lookup gated_follows)

/-! ## Values -/

theorem charsV_strC (n : Comp) : charsV (strC n) = some n := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    simp only [strC, charsV, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih]; rfl

theorem u8sV_u8sC (bs : List (BitVec 8)) : u8sV (u8sC bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [u8sC, u8sV, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih]; rfl

theorem preopensOf_numbered (b : Nat) (ns : List Comp) :
    preopensOf (some [.record (numbered b ns)]) =
      (ns.zip (List.range' b ns.length)).map fun x => (BitVec.ofNat 32 x.2, x.1) := by
  induction ns generalizing b with
  | nil => rfl
  | cons n ns ih =>
    have := ih (b + 1)
    simp only [preopensOf] at this ⊢
    simp [numbered, charsV_strC, this, List.range'_succ]

/-! ## Each answer of the host passes its check -/

theorem statChk_statA (V : FsVer) (o : Option Node) : statChk V o (statA V o) = true := by
  rcases o with _ | ⟨bs | ns⟩ <;> simp [statA, statChk, statV, okA, errA, isOkAns, sizeOk]

theorem typeChk_typeA (V : FsVer) (o : Option Node) : typeChk V o (typeA V o) = true := by
  rcases o with _ | ⟨bs | ns⟩ <;> simp [typeA, typeChk, okA, errA, isOkAns]

theorem openChk_openA {V : FsVer} (hV : V.notDir ≠ V.noEntry) (h : BitVec 32) (dirF : Bool)
    (o : Option Node) : openChk V dirF o (openA V h dirF o) = true := by
  rcases o with _ | n
  · simp [openA, openChk, errA]
  · by_cases hd : (!dirF || isDir (some n)) = true
    · simp only [openA, hd, ↓reduceIte, okA, openChk, Option.isSome_some, Bool.true_and]
    · simp only [openA, hd, Bool.false_eq_true, ↓reduceIte, errA, openChk]
      simp [hV]

theorem readChk_readA (V : FsVer) (len off : Nat) (o : Option Node) :
    readChk len off o (readA V len off o) = true := by
  rcases o with _ | ⟨bs | ns⟩
  · simp [readA, readChk, errA, isOkAns]
  · simp only [readA, okA, readChk, u8sV_u8sC]
    simp
  · simp [readA, readChk, errA, isOkAns]

theorem writeChk_writeA (V : FsVer) (buf : Val) (o : Option Node) :
    writeChk buf o (writeA V buf o) = true := by
  rcases o with _ | ⟨bs | ns⟩
  · simp [writeA, writeChk, errA, isOkAns]
  · simp only [writeA, okA, writeChk]
    cases hb : u8sV buf with
    | none => rfl
    | some xs =>
      simp only [Option.getD_some, decide_eq_true_eq, BitVec.toNat_ofNat]
      exact Nat.mod_le _ _
  · simp [writeA, writeChk, errA, isOkAns]

theorem entryChk_entryA (l : List (Comp × Nat)) : entryChk l (entryA l) = true := by
  rcases l with _ | ⟨⟨n, k⟩, l⟩
  · rfl
  · simp [entryA, entryChk, okA, charsV_strC]

theorem dirs_ok (T : Tree) (b : Nat) (pre : List Comp) :
    (preopensOf (dirsA T b pre)).all (fun x => isDir (T [x.2])) = true := by
  simp only [dirsA, preopensOf_numbered, List.all_map, List.all_eq_true]
  intro x hx
  have := (List.of_mem_zip hx).1
  simpa [Function.comp] using (List.mem_filter.1 this).2

/-- **Every answer of the concrete host passes the check.** -/
theorem fsImplV_ok {V : FsVer} (hV : V.notDir ≠ V.noEntry) (T : Tree) (pre : List Comp) (p : List WEv) (f : FnName)
    (a : List Val) : fsOk V T (p.foldl (fsNext V T) {}) (.imp f a (fsImplV V T pre p f a)) =
      true := by
  have hs : p.foldl (fsNext V T) {} = fsState V T p := rfl
  rw [hs]
  unfold fsOk fsImplV
  dsimp only
  by_cases h1 : f = V.getDirs
  · simp only [h1, ↓reduceIte]; exact dirs_ok T _ pre
  simp only [h1, ↓reduceIte]
  by_cases h2 : f = V.openAt
  · simp only [h2, ↓reduceIte]
    cases hq : atPath (fsState V T p) a with
    | none => rfl
    | some pa => simp [openChk_openA hV]
  simp only [h2, ↓reduceIte]
  by_cases h3 : f = V.stat
  · simp only [h3, ↓reduceIte]
    cases hq : selfPath (fsState V T p) a with
    | none => rfl
    | some pa => exact statChk_statA V _
  simp only [h3, ↓reduceIte]
  by_cases h4 : f = V.statAt
  · simp only [h4, ↓reduceIte]
    cases hq : atPath (fsState V T p) a with
    | none => rfl
    | some pa => exact statChk_statA V _
  simp only [h4, ↓reduceIte]
  by_cases h5 : f = V.getType
  · simp only [h5, ↓reduceIte]
    cases hq : selfPath (fsState V T p) a with
    | none => rfl
    | some pa => exact typeChk_typeA V _
  simp only [h5, ↓reduceIte]
  by_cases h6 : f = V.read
  · simp only [h6, ↓reduceIte]
    cases hq : selfPath (fsState V T p) a with
    | none => rfl
    | some pa => exact readChk_readA V _ _ _
  simp only [h6, ↓reduceIte]
  by_cases h7 : f = V.write
  · simp only [h7, ↓reduceIte]
    cases hq : selfPath (fsState V T p) a with
    | none => rfl
    | some pa => exact writeChk_writeA V _ _
  simp only [h7, ↓reduceIte]
  by_cases h8 : f = V.readDir
  · simp only [h8, ↓reduceIte]
    cases hq : selfPath (fsState V T p) a with
    | none => rfl
    | some pa =>
      dsimp only
      unfold readDirChk
      split <;> simp_all [okA, errA, isOkAns]
  simp only [h8, ↓reduceIte]
  by_cases h9 : f = V.readEntry
  · simp only [h9, ↓reduceIte]
    split
    · rename_i s tl
      dsimp only
      cases hl : lookup s (fsState V T p).ents with
      | none => rfl
      | some l => exact entryChk_entryA l
    · rfl
  simp only [h9, ↓reduceIte]

/-- **The concrete filesystem host is a model of the filesystem theory**, in every version. -/
theorem fsImplV_sat {Y : Sig.{0}} {I : Set FnName} {V : FsVer} (hV : V.notDir ≠ V.noEntry)
    (T : Tree) (pre : List Comp) :
    (hostSat (fsThV V T).Accepts).holds (concrete (Y := Y) (I := I) (fsImplV V T pre)) :=
  concrete_sat _ fun _ ht => gated_follows (fsImplV_ok hV T pre) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-- **The 0.2 host is a model of the 0.2 filesystem theory.** -/
theorem fsImpl2_sat {Y : Sig.{0}} {I : Set FnName} (T : Tree) (pre : List Comp) :
    (hostSat (fsTh2 T).Accepts).holds (concrete (Y := Y) (I := I) (fsImpl2 T pre)) :=
  fsImplV_sat (by decide) T pre

/-- **The 0.3 host is a model of the 0.3 filesystem theory.** -/
theorem fsImpl3_sat {Y : Sig.{0}} {I : Set FnName} (T : Tree) (pre : List Comp) :
    (hostSat (fsTh3 T).Accepts).holds (concrete (Y := Y) (I := I) (fsImpl3 T pre)) :=
  fsImplV_sat (by decide) T pre

/-! ## The theory is not trivial -/

/-- A tree: the preopen `d` holding the one-byte file `f` (byte `7`). -/
def tree1 : Tree
  | [['d']] => some (.dir [['f']])
  | [['d'], ['f']] => some (.file [7])
  | _ => none

/-- `get-directories` answering the preopen `d` as descriptor `0`. -/
def ev0 : WEv := .imp v2.getDirs [] (some [.record [.record [.u32 0, strC ['d']]]])
/-- `open-at(0, {}, "f", {}, {})` answering descriptor `1`. -/
def ev1 : WEv := .imp v2.openAt [.u32 0, .record [.bool false], strC ['f'],
  .record [.bool false, .bool false, .bool false, .bool false], .record []] (okA (.u32 1))
/-- `stat(1)` answering size `s`. -/
def evStat (s : Nat) : WEv := .imp v2.stat [.u32 1]
  (okA (.record [.variant 6 none, .u64 1, .u64 (BitVec.ofNat 64 s), noneV, noneV, noneV]))
/-- `read(1, 4, 0)` answering the bytes `bs`. -/
def evRead (bs : List (BitVec 8)) : WEv := .imp v2.read [.u32 1, .u64 4, .u64 0]
  (okA (.record [u8sC bs, .bool true]))
/-- `write(1, [9, 9], 1)` answering `2`. -/
def evWrite : WEv := .imp v2.write [.u32 1, u8sC [9, 9], .u64 1] (okA (.u64 2))
/-- `read-directory(0)` answering stream `2`. -/
def evDir : WEv := .imp v2.readDir [.u32 0] (okA (.u32 2))
/-- `read-directory-entry(2)` answering an entry of kind `k` named `n`. -/
def evEntry (k : Nat) (n : Comp) : WEv := .imp v2.readEntry [.u32 2]
  (okA (.variant 1 (some (.record [.variant k none, strC n]))))
/-- `open-at(0, {}, "g", {}, {})` answering descriptor `3`. -/
def evOpenG : WEv := .imp v2.openAt [.u32 0, .record [.bool false], strC ['g'],
  .record [.bool false, .bool false, .bool false, .bool false], .record []] (okA (.u32 3))

/-- **The theory accepts consistent runs**: open, stat (size 1), read, write two bytes at offset
1, stat (size 3), read back, list the directory. -/
theorem fsTh2_accepts :
    (fsTh2 tree1).Accepts [ev0, ev1, evStat 1, evRead [7], evWrite, evStat 3, evRead [7, 9, 9],
      evDir, evEntry 6 ['f']] := by
  unfold Protocol.Accepts; decide +kernel

/-- **The theory rejects inconsistent answers.** -/
theorem fsTh2_rejects :
    ¬ (fsTh2 tree1).Accepts [ev0, ev1, evStat 2] ∧
    ¬ (fsTh2 tree1).Accepts [ev0, ev1, evRead [8]] ∧
    ¬ (fsTh2 tree1).Accepts [ev0, ev1, evWrite, evStat 1] ∧
    ¬ (fsTh2 tree1).Accepts [ev0, evDir, evEntry 6 ['g']] ∧
    ¬ (fsTh2 tree1).Accepts [ev0, evOpenG] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.FsMore
