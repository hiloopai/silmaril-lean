module

public import Silmaril.Wasm.Component.Streams.Proc.Defs

/-!
# The pipeline's store, abstractly

Every store reachable by the pipeline of `Silmaril.Wasm.Component.Streams.Proc` is `toStore A B` for
two **abstract channel states** `A`, `B : CS` (the channel record, the pending events of its two
ends, and whether each end has been dropped). This module defines `toStore`, the abstract
built-ins on one channel (`CS.write`, `CS.read`, `CS.dropR`, `CS.dropW`, generic in the channel's
handles), and proves that `Async.step` on `toStore A B` **is** the abstract built-in on `A` (ends
`1`, `2`) or on `B` (ends `3`, `4`), and that `waitable-set.wait` on the sets `5`, `6`, `7` takes
the event of the right end (`wait5_*`, `wait6_*`, `wait7_*`). It also computes the setup store
(`setup_eq`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Proc

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async
open Silmaril.Wasm.Component.Streams.Proc

/-- The abstract state of one channel. -/
structure CS where
  c : Chan := {}
  er : Option Event := none
  ew : Option Event := none
  dr : Bool := false
  dw : Bool := false

/-- **The store of the pipeline** with channel states `A` and `B`. -/
def toStore (A B : CS) : Store where
  next := 8
  tbl h :=
    if h = 1 then (if A.dr then none else some (.streamR 1))
    else if h = 2 then (if A.dw then none else some (.streamW 1))
    else if h = 3 then (if B.dr then none else some (.streamR 3))
    else if h = 4 then (if B.dw then none else some (.streamW 3))
    else if h = 5 ∨ h = 6 ∨ h = 7 then some .wset else none
  chans s := if s = 1 then A.c else if s = 3 then B.c else {}
  tasks _ := {}
  joined h :=
    if h = 1 then (if A.dr then none else some 5)
    else if h = 2 then (if A.dw then none else some 6)
    else if h = 3 then (if B.dr then none else some 7)
    else if h = 4 then (if B.dw then none else some 5)
    else none
  ev h :=
    if h = 1 then A.er else if h = 2 then A.ew else if h = 3 then B.er else if h = 4 then B.ew
    else none

theorem Store.ext' {a b : Store} (h1 : a.next = b.next) (h2 : a.tbl = b.tbl)
    (h3 : a.chans = b.chans) (h4 : a.tasks = b.tasks) (h5 : a.joined = b.joined)
    (h6 : a.ev = b.ev) : a = b := by
  cases a
  cases b
  simp_all

/-! ## The abstract built-ins on one channel -/

/-- After a write met the pending read of `hr`: `ys` (of count `k`) copied. -/
def CS.metR (hr : Nat) (a : CS) (k : Nat) (ys : List Val) : CS :=
  { a with c := { a.c with pend := .idle, sent := a.c.sent ++ ys },
           er := some ⟨.streamRead, hr, packCopy .completed k, ys⟩ }

/-- After a read met the pending write of `hw`: `ys` (of count `k`) copied. -/
def CS.metW (hw : Nat) (a : CS) (k : Nat) (ys : List Val) : CS :=
  { a with c := { a.c with pend := .idle, sent := a.c.sent ++ ys },
           ew := some ⟨.streamWrite, hw, packCopy .completed k, []⟩ }

/-- A write of `xs` by `hw` is pending. -/
def CS.pendW (hw : Nat) (a : CS) (xs : List Val) : CS := { a with c := { a.c with pend := .write hw xs } }

/-- A read of `n` items by `hr` is pending. -/
def CS.pendR (hr : Nat) (a : CS) (n : Nat) : CS := { a with c := { a.c with pend := .read hr n } }

/-- The readable end is dropped while the write of `hw` is pending. -/
def CS.dropRW (hw : Nat) (a : CS) : CS :=
  { a with c := { a.c with pend := .idle, rDropped := true },
           ew := some ⟨.streamWrite, hw, packCopy .dropped 0, []⟩, er := none, dr := true }

/-- The readable end is dropped with no pending write. -/
def CS.dropRI (a : CS) : CS := { a with c := { a.c with rDropped := true }, er := none, dr := true }

/-- The writable end is dropped while the read of `hr` is pending. -/
def CS.dropWR (hr : Nat) (a : CS) : CS :=
  { a with c := { a.c with pend := .idle, wDropped := true },
           er := some ⟨.streamRead, hr, packCopy .dropped 0, []⟩, ew := none, dw := true }

/-- The writable end is dropped with no pending read. -/
def CS.dropWI (a : CS) : CS := { a with c := { a.c with wDropped := true }, ew := none, dw := true }

/-- `stream.write` by the writer `hw`; the reader is `hr`. -/
def CS.write (hr hw : Nat) (a : CS) (xs : List Val) : Option (CS × Res) :=
  match a.c.pend with
  | .write .. => none
  | .read h n =>
    if h = hr then
      some (a.metR hr (min n xs.length) (xs.take (min n xs.length)),
            .nat (packCopy .completed (min n xs.length)))
    else none
  | .idle =>
    if a.c.rDropped then some (a, .nat (packCopy .dropped 0))
    else some (a.pendW hw xs, .nat blocked)

/-- `stream.read` of up to `n` items by the reader `hr`; the writer is `hw`. -/
def CS.read (hr hw : Nat) (a : CS) (n : Nat) : Option (CS × Res) :=
  match a.c.pend with
  | .read .. => none
  | .write h xs =>
    if h = hw then
      some (a.metW hw (min n xs.length) (xs.take (min n xs.length)),
            .read (packCopy .completed (min n xs.length)) (xs.take (min n xs.length)))
    else none
  | .idle =>
    if a.c.wDropped then some (a, .read (packCopy .dropped 0) [])
    else some (a.pendR hr n, .nat blocked)

/-- `stream.drop-readable`. -/
def CS.dropR (hw : Nat) (a : CS) : Option (CS × Res) :=
  match a.c.pend with
  | .read .. => none
  | .write h _ => if h = hw then some (a.dropRW hw, .unit) else none
  | .idle => some (a.dropRI, .unit)

/-- `stream.drop-writable`. -/
def CS.dropW (hr : Nat) (a : CS) : Option (CS × Res) :=
  match a.c.pend with
  | .write .. => none
  | .read h _ => if h = hr then some (a.dropWR hr, .unit) else none
  | .idle => some (a.dropWI, .unit)

/-! ## The built-ins on `toStore` are the abstract ones -/

/-- Pointwise equality of stores of the pipeline. -/
macro "fun_ext8" : tactic => `(tactic| (
  funext j; rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    simp [toStore, Store.setChan, Store.post, Store.remove, upd, CS.metR, CS.metW, CS.pendW,
      CS.pendR, CS.dropRW, CS.dropRI, CS.dropWR, CS.dropWI, *] <;> rfl))

/-- Pointwise equality of stores of the pipeline. -/
macro "store_ext" : tactic => `(tactic| (
  first
  | (refine Store.ext' rfl ?_ ?_ rfl ?_ ?_ <;> fun_ext8)
  | fun_ext8))

/-- A field of `toStore` updated at the handle `k` (by `Store.setChan`, `Store.post`,
`Store.remove` or `upd`): equal at `k`, and at every other handle. -/
macro "upd_ext " k:term : tactic => `(tactic| (
  funext j; by_cases hj : j = $k <;>
    simp [toStore, Store.setChan, Store.post, Store.remove, upd, hj]))

/-! ### Each store update is an update of one channel state

The step functions update the store with `Store.setChan`, `Store.post` and `Store.remove` (and
`upd` of the events, in `take`); on `toStore A B` each of them at the handles `1`-`4` (channels
`1`, `3`) is `toStore` of an update of `A` or `B`, so the built-ins below are proved by rewriting
with these lemmas, without comparing whole stores. -/

theorem setChan_A (A B : CS) (c : Chan) : (toStore A B).setChan 1 c = toStore { A with c := c } B :=
  Store.ext' rfl rfl (by upd_ext 1) rfl rfl rfl

theorem setChan_B (A B : CS) (c : Chan) : (toStore A B).setChan 3 c = toStore A { B with c := c } :=
  Store.ext' rfl rfl (by upd_ext 3) rfl rfl rfl

theorem ev_A1 (A B : CS) (x : Option Event) :
    { toStore A B with ev := upd (toStore A B).ev 1 x } = toStore { A with er := x } B :=
  Store.ext' rfl rfl rfl rfl rfl (by upd_ext 1)

theorem ev_A2 (A B : CS) (x : Option Event) :
    { toStore A B with ev := upd (toStore A B).ev 2 x } = toStore { A with ew := x } B :=
  Store.ext' rfl rfl rfl rfl rfl (by upd_ext 2)

theorem ev_B3 (A B : CS) (x : Option Event) :
    { toStore A B with ev := upd (toStore A B).ev 3 x } = toStore A { B with er := x } :=
  Store.ext' rfl rfl rfl rfl rfl (by upd_ext 3)

theorem ev_B4 (A B : CS) (x : Option Event) :
    { toStore A B with ev := upd (toStore A B).ev 4 x } = toStore A { B with ew := x } :=
  Store.ext' rfl rfl rfl rfl rfl (by upd_ext 4)

theorem post_A1 (A B : CS) (e : Event) :
    (toStore A B).post 1 e = toStore { A with er := some e } B := ev_A1 A B (some e)

theorem post_A2 (A B : CS) (e : Event) :
    (toStore A B).post 2 e = toStore { A with ew := some e } B := ev_A2 A B (some e)

theorem post_B3 (A B : CS) (e : Event) :
    (toStore A B).post 3 e = toStore A { B with er := some e } := ev_B3 A B (some e)

theorem post_B4 (A B : CS) (e : Event) :
    (toStore A B).post 4 e = toStore A { B with ew := some e } := ev_B4 A B (some e)

theorem remove_A1 (A B : CS) :
    (toStore A B).remove 1 = toStore { A with er := none, dr := true } B :=
  Store.ext' rfl (by upd_ext 1) rfl rfl (by upd_ext 1) (by upd_ext 1)

theorem remove_A2 (A B : CS) :
    (toStore A B).remove 2 = toStore { A with ew := none, dw := true } B :=
  Store.ext' rfl (by upd_ext 2) rfl rfl (by upd_ext 2) (by upd_ext 2)

theorem remove_B3 (A B : CS) :
    (toStore A B).remove 3 = toStore A { B with er := none, dr := true } :=
  Store.ext' rfl (by upd_ext 3) rfl rfl (by upd_ext 3) (by upd_ext 3)

theorem remove_B4 (A B : CS) :
    (toStore A B).remove 4 = toStore A { B with ew := none, dw := true } :=
  Store.ext' rfl (by upd_ext 4) rfl rfl (by upd_ext 4) (by upd_ext 4)

/-- A store reached from `toStore A B` by the updates of a built-in is `toStore` of its
abstract result: rewrite the updates into the channel states, then compare those (using the
hypotheses on the pending operation and the dropped flags of the case). -/
macro "store_rw" : tactic => `(tactic| (
  simp only [setChan_A, setChan_B, post_A1, post_A2, post_B3, post_B4, remove_A1, remove_A2,
    remove_B3, remove_B4] <;>
  first
  | rfl
  | simp [CS.metR, CS.metW, CS.pendW, CS.pendR, CS.dropRW, CS.dropRI, CS.dropWR, CS.dropWI, *]))

/-- The map of an abstract built-in on `A` to the store. -/
def onA (B : CS) : Option (CS × Res) → Option (Store × Res) := Option.map fun p => (toStore p.1 B, p.2)

/-- The map of an abstract built-in on `B` to the store. -/
def onB (A : CS) : Option (CS × Res) → Option (Store × Res) := Option.map fun p => (toStore A p.1, p.2)

theorem write_A (A B : CS) (xs : List Val) (hA : A.dw = false)
    (hr : ∀ h n, A.c.pend = .read h n → h = 1) :
    step (toStore A B) (.streamWrite 2 xs) = onA B (A.write 1 2 xs) := by
  have ht : (toStore A B).tbl 2 = some (.streamW 1) := by simp [toStore, hA]
  have hc : (toStore A B).chans 1 = A.c := by simp [toStore]
  simp only [step, streamWrite, ht, hc, CS.write, onA]
  rcases hp : A.c.pend with _ | ⟨h', n⟩ | ⟨h', ys⟩
  · by_cases hd : A.c.rDropped = true
    · simp [hd]
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.some.injEq,
        Prod.mk.injEq, and_true]
      store_rw
  · obtain rfl := hr h' n hp
    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw
  · rfl

theorem write_B (A B : CS) (xs : List Val) (hB : B.dw = false)
    (hr : ∀ h n, B.c.pend = .read h n → h = 3) :
    step (toStore A B) (.streamWrite 4 xs) = onB A (B.write 3 4 xs) := by
  have ht : (toStore A B).tbl 4 = some (.streamW 3) := by simp [toStore, hB]
  have hc : (toStore A B).chans 3 = B.c := by simp [toStore]
  simp only [step, streamWrite, ht, hc, CS.write, onB]
  rcases hp : B.c.pend with _ | ⟨h', n⟩ | ⟨h', ys⟩
  · by_cases hd : B.c.rDropped = true
    · simp [hd]
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.some.injEq,
        Prod.mk.injEq, and_true]
      store_rw
  · obtain rfl := hr h' n hp
    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw
  · rfl

theorem read_A (A B : CS) (n : Nat) (hA : A.dr = false)
    (hw : ∀ h xs, A.c.pend = .write h xs → h = 2) :
    step (toStore A B) (.streamRead 1 n) = onA B (A.read 1 2 n) := by
  have ht : (toStore A B).tbl 1 = some (.streamR 1) := by simp [toStore, hA]
  have hc : (toStore A B).chans 1 = A.c := by simp [toStore]
  simp only [step, streamRead, ht, hc, CS.read, onA]
  rcases hp : A.c.pend with _ | ⟨h', m⟩ | ⟨h', ys⟩
  · by_cases hd : A.c.wDropped = true
    · simp [hd]
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.some.injEq,
        Prod.mk.injEq, and_true]
      store_rw
  · rfl
  · obtain rfl := hw h' ys hp
    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw

theorem read_B (A B : CS) (n : Nat) (hB : B.dr = false)
    (hw : ∀ h xs, B.c.pend = .write h xs → h = 4) :
    step (toStore A B) (.streamRead 3 n) = onB A (B.read 3 4 n) := by
  have ht : (toStore A B).tbl 3 = some (.streamR 3) := by simp [toStore, hB]
  have hc : (toStore A B).chans 3 = B.c := by simp [toStore]
  simp only [step, streamRead, ht, hc, CS.read, onB]
  rcases hp : B.c.pend with _ | ⟨h', m⟩ | ⟨h', ys⟩
  · by_cases hd : B.c.wDropped = true
    · simp [hd]
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.some.injEq,
        Prod.mk.injEq, and_true]
      store_rw
  · rfl
  · obtain rfl := hw h' ys hp
    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw

theorem dropR_A (A B : CS) (hA : A.dr = false) (hw : ∀ h xs, A.c.pend = .write h xs → h = 2) :
    step (toStore A B) (.streamDropR 1) = onA B (A.dropR 2) := by
  have ht : (toStore A B).tbl 1 = some (.streamR 1) := by simp [toStore, hA]
  have hc : (toStore A B).chans 1 = A.c := by simp [toStore]
  simp only [step, streamDropR, ht, hc, CS.dropR, onA]
  rcases hp : A.c.pend with _ | ⟨h', m⟩ | ⟨h', ys⟩
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw
  · rfl
  · obtain rfl := hw h' ys hp
    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw

theorem dropR_B (A B : CS) (hB : B.dr = false) (hw : ∀ h xs, B.c.pend = .write h xs → h = 4) :
    step (toStore A B) (.streamDropR 3) = onB A (B.dropR 4) := by
  have ht : (toStore A B).tbl 3 = some (.streamR 3) := by simp [toStore, hB]
  have hc : (toStore A B).chans 3 = B.c := by simp [toStore]
  simp only [step, streamDropR, ht, hc, CS.dropR, onB]
  rcases hp : B.c.pend with _ | ⟨h', m⟩ | ⟨h', ys⟩
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw
  · rfl
  · obtain rfl := hw h' ys hp
    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw

theorem dropW_A (A B : CS) (hA : A.dw = false) (hr : ∀ h n, A.c.pend = .read h n → h = 1) :
    step (toStore A B) (.streamDropW 2) = onA B (A.dropW 1) := by
  have ht : (toStore A B).tbl 2 = some (.streamW 1) := by simp [toStore, hA]
  have hc : (toStore A B).chans 1 = A.c := by simp [toStore]
  simp only [step, streamDropW, ht, hc, CS.dropW, onA]
  rcases hp : A.c.pend with _ | ⟨h', m⟩ | ⟨h', ys⟩
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw
  · obtain rfl := hr h' m hp
    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw
  · rfl

theorem dropW_B (A B : CS) (hB : B.dw = false) (hr : ∀ h n, B.c.pend = .read h n → h = 3) :
    step (toStore A B) (.streamDropW 4) = onB A (B.dropW 3) := by
  have ht : (toStore A B).tbl 4 = some (.streamW 3) := by simp [toStore, hB]
  have hc : (toStore A B).chans 3 = B.c := by simp [toStore]
  simp only [step, streamDropW, ht, hc, CS.dropW, onB]
  rcases hp : B.c.pend with _ | ⟨h', m⟩ | ⟨h', ys⟩
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw
  · obtain rfl := hr h' m hp
    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    store_rw
  · rfl

/-! ## Waiting -/

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem toStore_next (A B : CS) : (toStore A B).next = 8 := rfl

theorem toStore_tbl5 (A B : CS) : (toStore A B).tbl 5 = some .wset := rfl

theorem toStore_tbl6 (A B : CS) : (toStore A B).tbl 6 = some .wset := rfl

theorem toStore_tbl7 (A B : CS) : (toStore A B).tbl 7 = some .wset := rfl

theorem wait5_A (A B : CS) (e : Event) (hd : A.dr = false) (he : A.er = some e) :
    step (toStore A B) (.wait 5) = some (toStore { A with er := none } B, .event e) := by
  simp only [step, toStore_next, range8, toStore_tbl5]
  simp [toStore, firstReady, take, hd, he]
  store_ext

theorem wait5_B (A B : CS) (e : Event) (hA : A.er = none) (hd : B.dw = false)
    (he : B.ew = some e) :
    step (toStore A B) (.wait 5) = some (toStore A { B with ew := none }, .event e) := by
  simp only [step, toStore_next, range8, toStore_tbl5]
  simp [toStore, firstReady, take, hd, he, hA]
  store_ext

theorem wait5_none (A B : CS) (hA : A.er = none) (hB : B.ew = none) :
    step (toStore A B) (.wait 5) = some (toStore A B, .blocked) := by
  simp only [step, toStore_next, range8, toStore_tbl5]
  simp [toStore, firstReady, hA, hB]

theorem wait6_A (A B : CS) (e : Event) (hd : A.dw = false) (he : A.ew = some e) :
    step (toStore A B) (.wait 6) = some (toStore { A with ew := none } B, .event e) := by
  simp only [step, toStore_next, range8, toStore_tbl6]
  simp [toStore, firstReady, take, hd, he]
  store_ext

theorem wait6_none (A B : CS) (hA : A.ew = none) :
    step (toStore A B) (.wait 6) = some (toStore A B, .blocked) := by
  simp only [step, toStore_next, range8, toStore_tbl6]
  simp [toStore, firstReady, hA]

theorem wait7_B (A B : CS) (e : Event) (hd : B.dr = false) (he : B.er = some e) :
    step (toStore A B) (.wait 7) = some (toStore A { B with er := none }, .event e) := by
  simp only [step, toStore_next, range8, toStore_tbl7]
  simp [toStore, firstReady, take, hd, he]
  store_ext

theorem wait7_none (A B : CS) (hB : B.er = none) :
    step (toStore A B) (.wait 7) = some (toStore A B, .blocked) := by
  simp only [step, toStore_next, range8, toStore_tbl7]
  simp [toStore, firstReady, hB]

/-! ## The setup -/

/-- **The setup store** is the store of two fresh channels. -/
theorem setup_eq : runOps Store.empty setupOps = some (toStore {} {}) := by
  simp [runOps, setupOps, step, Store.alloc2, Store.empty, upd, Obj.isWaitable]
  store_ext

end Silmaril.Proofs.Wasm.Component.Streams.Proc
