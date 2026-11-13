module

public import Silmaril.Wasi.Versions.Tcp3Stream.Defs
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# WASI 0.3 TCP streams: theorems

PROVED (standard axioms):

* **`tcp3sImpl_sat`**: for all peer data `D`, the host `tcp3sImpl D` is a model of
  `tcp3sTh D`.
* **`tcp3sTh_examples`**: the theory is not trivial. Accepted: connect, receive two bytes one at
  a time, `DROPPED`, send and report `ok` after the drop. Rejected: a wrong byte, a premature
  `DROPPED`, data on a second `receive`, a send future reporting `ok` before the drop, and a
  second `send` reporting `ok`.
-/

namespace Silmaril.Wasi.Versions.Tcp3Stream

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult packCopy)
open Silmaril.Wasi.Versions.Net (gated gated_follows)
open Silmaril.Wasi.Versions.P3 (natV natOf copyOf cStreamNew cStreamWrite cStreamRead
  cStreamDropW cFutureRead)

theorem bytesOf_bytesV' (bs : List (BitVec 8)) : bytesOf (bytesV bs) = bs := by
  simp [bytesOf, bytesV, List.filterMap_map]

theorem rdChk_rdA (l : List (BitVec 8)) (n : Option Nat) : rdChk l (rdA l n) = true := by
  unfold rdA
  by_cases hl : l.isEmpty
  · simp [hl, rdChk, natV, natOf, copyOf, packCopy, CopyResult.toNat,
      Silmaril.Wasm.Component.Async.blocked]
  · have hne : 1 ≤ l.length := by
      cases l with
      | nil => simp at hl
      | cons _ _ => simp
    by_cases hn : n = some 0
    · simp [hl, hn, rdChk, natV, natOf, copyOf, packCopy, CopyResult.toNat,
        Silmaril.Wasm.Component.Async.blocked, bytesOf_bytesV']
    · simp [hl, hn, rdChk, natV, natOf, copyOf, packCopy, CopyResult.toNat,
        Silmaril.Wasm.Component.Async.blocked, bytesOf_bytesV', hne]

theorem futA_ok (q : T3St) (x : Nat × Bool) :
    (match some x, futA q x with
     | some x, some [_, .variant 0 none] => sendDone q x
     | _, _ => true) = true := by
  unfold futA
  by_cases hd : sendDone q x
  · simp [hd]
  · by_cases h2 : x.2 <;> simp [hd, h2]

set_option linter.unusedTactic false in
theorem tcp3sImpl_read (D : PeerData) (p : List WEv) (a : List Val) :
    tcp3sImpl D p cStreamRead a =
      (match pendOf (t3State D p) a with
       | some l => rdA l (a[1]?.bind natOf)
       | none => none) := by
  simp [tcp3sImpl, cStreamRead, cStreamNew, cStreamWrite, cStreamDropW,
    Silmaril.Wasi.Versions.P3.canon, Silmaril.Wasi.Versions.Net.connect3, tcpReceive3, tcpSend3]
  try rfl

set_option linter.unusedTactic false in
theorem tcp3sImpl_fut (D : PeerData) (p : List WEv) (a : List Val) :
    tcp3sImpl D p cFutureRead a =
      (match futOf (t3State D p) a with
       | some x => futA (t3State D p) x
       | none => none) := by
  simp [tcp3sImpl, cStreamRead, cStreamNew, cStreamWrite, cStreamDropW, cFutureRead,
    Silmaril.Wasi.Versions.P3.canon, Silmaril.Wasi.Versions.Net.connect3, tcpReceive3, tcpSend3]
  try rfl

theorem t3Ok_read (q : T3St) (a : List Val) :
    t3Ok q (.imp cStreamRead a
      (match pendOf q a with
       | some l => rdA l (a[1]?.bind natOf)
       | none => none)) = true := by
  simp only [t3Ok, ↓reduceIte]
  cases pendOf q a with
  | none => rfl
  | some l => exact rdChk_rdA l _

theorem t3Ok_fut (q : T3St) (a : List Val) :
    t3Ok q (.imp cFutureRead a
      (match futOf q a with
       | some x => futA q x
       | none => none)) = true := by
  have hne : cFutureRead ≠ cStreamRead := by
    simp [cFutureRead, cStreamRead, Silmaril.Wasi.Versions.P3.canon]
  simp only [t3Ok, hne, ↓reduceIte]
  cases futOf q a with
  | none => rfl
  | some x => exact futA_ok _ x

/-- **Every answer of the host passes the check.** -/
theorem tcp3sImpl_ok (D : PeerData) (p : List WEv) (f : FnName) (a : List Val) :
    t3Ok (p.foldl (t3Next D) {}) (.imp f a (tcp3sImpl D p f a)) = true := by
  have hs : p.foldl (t3Next D) {} = t3State D p := rfl
  rw [hs]
  by_cases h1 : f = cStreamRead
  · rw [h1, tcp3sImpl_read]; exact t3Ok_read _ a
  by_cases h2 : f = cFutureRead
  · rw [h2, tcp3sImpl_fut]; exact t3Ok_fut _ a
  · simp [t3Ok, h1, h2]

/-- **The 0.3 TCP stream host is a model of the theory.** -/
theorem tcp3sImpl_sat {Y : Sig.{0}} {I : Set FnName} (D : PeerData) :
    (hostSat (tcp3sTh D).Accepts).holds (concrete (Y := Y) (I := I) (tcp3sImpl D)) :=
  concrete_sat _ fun _ ht => gated_follows (tcp3sImpl_ok D) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## The theory is not trivial -/

/-- The peer at any address sends the bytes `1, 2`. -/
def dataE : PeerData := fun _ => [1, 2]

def addrE : Val := .u32 9
def connE : WEv := .imp Silmaril.Wasi.Versions.Net.connect3 [.u32 0, addrE] (some [.variant 0 none])
def recvE (rv : Nat) : WEv := .imp tcpReceive3 [.u32 0] (some [.record [natV rv, natV (rv + 1)]])
def readB (rv : Nat) (bs : List (BitVec 8)) : WEv :=
  .imp cStreamRead [natV rv, natV 1] (some [natV (packCopy .completed bs.length), bytesV bs])
def dropR (rv : Nat) : WEv :=
  .imp cStreamRead [natV rv, natV 1] (some [natV (packCopy .dropped 0), .record []])
def newE : WEv := .imp cStreamNew [] (some [natV 20, natV 21])
def sendE (fv : Nat) : WEv := .imp tcpSend3 [.u32 0, natV 20] (some [natV fv])
def dropW : WEv := .imp cStreamDropW [natV 21] (some [])
def futOkE (fv : Nat) : WEv :=
  .imp cFutureRead [natV fv] (some [natV CopyResult.completed.toNat, .variant 0 none])

/-- **Accepted and rejected runs of `tcp3sTh dataE`.** -/
theorem tcp3sTh_examples :
    (tcp3sTh dataE).Accepts [connE, recvE 3, readB 3 [1], readB 3 [2], dropR 3, newE, sendE 30,
      dropW, futOkE 30] ∧
    ¬ (tcp3sTh dataE).Accepts [connE, recvE 3, readB 3 [2]] ∧
    ¬ (tcp3sTh dataE).Accepts [connE, recvE 3, readB 3 [1], dropR 3] ∧
    ¬ (tcp3sTh dataE).Accepts [connE, recvE 3, recvE 5, readB 5 [1]] ∧
    ¬ (tcp3sTh dataE).Accepts [connE, newE, sendE 30, futOkE 30] ∧
    ¬ (tcp3sTh dataE).Accepts [connE, newE, sendE 30, sendE 31, dropW, futOkE 31] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.Tcp3Stream
