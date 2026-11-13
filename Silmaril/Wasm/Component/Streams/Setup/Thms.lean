module

public import Silmaril.Wasm.Component.Streams.Setup.Defs

/-!
# The setup program yields the initial store

**`setup_init`**: running `setupOps net` (`stream.new` ×`m`, `waitable-set.new` ×`k`, then two
`waitable.join`s per stream) from the empty store succeeds, returns `setupRes net` (stream `c`'s
ends are `rh c` and `wh c`, node `i`'s set is `net.ws i`), and leaves exactly `Net.initStore net`.
So the systems `Net.Reach net` starts from are those the built-ins create, and the handles the
node programs use are the ones the built-ins return.

The proof follows the store through closed forms: after `n` streams and `j` sets the table is
`tblN n j`; after the joins of streams `0 … c-1` the membership is `joinedN net c`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Setup

open Silmaril.Wasm.Component.Async (Obj Res upd)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net

/-- The table after creating `n` streams and `j` waitable sets. -/
def tblN (n j : Nat) (h : Nat) : Option Obj :=
  if h = 0 then none
  else if h ≤ 2 * n then (if h % 2 = 1 then some (.streamR h) else some (.streamW (h - 1)))
  else if h ≤ 2 * n + j then some .wset else none

/-- The set membership after joining the ends of streams `0 … c-1`. -/
def joinedN (net : Network) (c : Nat) (h : Nat) : Option Nat :=
  if h = 0 then none
  else if h ≤ 2 * c then
    (if h % 2 = 1 then some (net.ws (net.rd (h / 2))) else some (net.ws (net.wr (h / 2 - 1)).1))
  else none

/-- The store after `n` streams, `j` sets and the joins of `c` streams. -/
def stN (net : Network) (n j c : Nat) : DStore where
  next := 2 * n + 1 + j
  tbl := tblN n j
  chans := fun _ => {}
  joined := joinedN net c

theorem runOps_append (st : DStore) (a b : List DOp) :
    runOps st (a ++ b) =
      (runOps st a).bind fun p => (runOps p.1 b).map fun q => (q.1, p.2 ++ q.2) := by
  induction a generalizing st with
  | nil => simp [runOps]
  | cons op a ih =>
    simp only [List.cons_append, runOps]
    cases dstep st op with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, ih]
      cases runOps p.1 a with
      | none => rfl
      | some q =>
        simp only [Option.bind_some, Option.map_some]
        cases runOps q.1 b <;> simp

theorem empty_eq (net : Network) : ({} : DStore) = stN net 0 0 0 := by
  have ht : (fun _ => none : Nat → Option Obj) = tblN 0 0 := by
    funext h; unfold tblN; split_ifs <;> first | rfl | omega
  have hj : (fun _ => none : Nat → Option Nat) = joinedN net 0 := by
    funext h; unfold joinedN; split_ifs <;> first | rfl | omega
  simp only [stN, ← ht, ← hj]

/-! ## `stream.new` -/

theorem tblN_new (n : Nat) :
    upd (upd (tblN n 0) (2 * n + 1) (some (.streamR (2 * n + 1)))) (2 * n + 1 + 1)
      (some (.streamW (2 * n + 1))) = tblN (n + 1) 0 := by
  funext h
  unfold upd tblN
  split_ifs <;> first | rfl | omega | (congr 2; omega)

theorem chans_new (r : Nat) : upd (fun _ => ({} : DChan)) r {} = fun _ => {} := by
  funext h
  unfold upd
  split_ifs <;> rfl

theorem dstep_new (net : Network) (n : Nat) :
    dstep (stN net n 0 0) .streamNew = some (stN net (n + 1) 0 0, .ends (rh n) (wh n)) := by
  have hnext : 2 * n + 1 + 0 + 2 = 2 * (n + 1) + 1 + 0 := by omega
  have hr : rh n = 2 * n + 1 + 0 := by simp [rh]
  have hw : wh n = 2 * n + 1 + 0 + 1 := by simp only [wh]
  simp only [dstep, stN, hnext, Nat.add_zero, chans_new, tblN_new, hr, hw]

theorem run_news (net : Network) (a n : Nat) (rest : List DOp) :
    runOps (stN net n 0 0) (List.replicate a .streamNew ++ rest) =
      (runOps (stN net (n + a) 0 0) rest).map
        fun q => (q.1, (List.range' n a).map (fun c => .ends (rh c) (wh c)) ++ q.2) := by
  induction a generalizing n with
  | zero => rcases h : runOps (stN net n 0 0) rest with _ | q <;> simp [h]
  | succ a ih =>
    have he : n + (a + 1) = n + 1 + a := by omega
    simp only [List.replicate_succ, List.cons_append, runOps, dstep_new, Option.bind_some, ih, he,
      List.range'_succ, List.map_cons]
    cases runOps (stN net (n + 1 + a) 0 0) rest <;> simp

/-! ## `waitable-set.new` -/

theorem tblN_ws (m j : Nat) :
    upd (tblN m j) (2 * m + 1 + j) (some .wset) = tblN m (j + 1) := by
  funext h
  unfold upd tblN
  split_ifs <;> first | rfl | omega

theorem dstep_ws (net : Network) (j : Nat) :
    dstep (stN net net.m j 0) .wsNew = some (stN net net.m (j + 1) 0, .nat (2 * net.m + 1 + j)) := by
  have hnext : 2 * net.m + 1 + j + 1 = 2 * net.m + 1 + (j + 1) := by omega
  simp only [dstep, stN, hnext, tblN_ws]

theorem run_wss (net : Network) (a j : Nat) (rest : List DOp) :
    runOps (stN net net.m j 0) (List.replicate a .wsNew ++ rest) =
      (runOps (stN net net.m (j + a) 0) rest).map
        fun q => (q.1, (List.range' j a).map (fun i => .nat (2 * net.m + 1 + i)) ++ q.2) := by
  induction a generalizing j with
  | zero => rcases h : runOps (stN net net.m j 0) rest with _ | q <;> simp [h]
  | succ a ih =>
    have he : j + (a + 1) = j + 1 + a := by omega
    simp only [List.replicate_succ, List.cons_append, runOps, dstep_ws, Option.bind_some, ih, he,
      List.range'_succ, List.map_cons]
    cases runOps (stN net net.m (j + 1 + a) 0) rest <;> simp

/-! ## `waitable.join` -/

theorem tblN_rh (net : Network) {c : Nat} (hc : c < net.m) :
    tblN net.m net.k (rh c) = some (.streamR (rh c)) := by
  unfold tblN rh
  split_ifs <;> first | rfl | omega

theorem tblN_wh (net : Network) {c : Nat} (hc : c < net.m) :
    tblN net.m net.k (wh c) = some (.streamW (rh c)) := by
  unfold tblN wh rh
  split_ifs <;> first | rfl | omega

theorem tblN_ws' (net : Network) (i : Fin net.k) : tblN net.m net.k (net.ws i) = some .wset := by
  unfold tblN Network.ws
  split_ifs <;> first | rfl | omega

theorem joinedN_succ (net : Network) (c : Nat) :
    upd (upd (joinedN net c) (rh c) (some (net.ws (net.rd c)))) (wh c)
      (some (net.ws (net.wr c).1)) = joinedN net (c + 1) := by
  funext h
  unfold upd joinedN rh wh
  by_cases h1 : h = 2 * c + 2
  · subst h1
    have e1 : (2 * c + 2) / 2 - 1 = c := by omega
    simp only [e1]
    split_ifs <;> first | rfl | omega
  · by_cases h2 : h = 2 * c + 1
    · subst h2
      have e2 : (2 * c + 1) / 2 = c := by omega
      simp only [e2]
      split_ifs <;> first | rfl | omega
    · simp only [h1, h2, ↓reduceIte]
      split_ifs <;> first | rfl | omega

theorem dstep_joins (net : Network) {c : Nat} (hc : c < net.m) :
    runOps (stN net net.m net.k c) [.join (rh c) (net.ws (net.rd c)), .join (wh c) (net.ws (net.wr c).1)] =
      some (stN net net.m net.k (c + 1), [.unit, .unit]) := by
  have h1 : (stN net net.m net.k c).tbl (rh c) = some (.streamR (rh c)) := tblN_rh net hc
  have h2 : (stN net net.m net.k c).tbl (wh c) = some (.streamW (rh c)) := tblN_wh net hc
  have h3 : (stN net net.m net.k c).tbl (net.ws (net.rd c)) = some .wset := tblN_ws' net _
  have h4 : (stN net net.m net.k c).tbl (net.ws (net.wr c).1) = some .wset := tblN_ws' net _
  simp only [runOps, dstep, h1, h3, ↓reduceIte, Option.bind_some]
  simp only [stN] at h2 h4 ⊢
  simp only [h2, h4, ↓reduceIte, Option.bind_some, Option.map_some, joinedN_succ]

theorem run_joins (net : Network) (n : Nat) (hn : n ≤ net.m) :
    runOps (stN net net.m net.k 0) (joinOps net n) =
      some (stN net net.m net.k n, List.replicate (2 * n) .unit) := by
  induction n with
  | zero => simp [joinOps, runOps]
  | succ n ih =>
    have ih' := ih (by omega)
    have hjo : joinOps net (n + 1) = joinOps net n ++
        [.join (rh n) (net.ws (net.rd n)), .join (wh n) (net.ws (net.wr n).1)] := by
      simp [joinOps, List.range_succ, List.flatMap_append]
    have hrep : List.replicate (2 * n) Res.unit ++ [.unit, .unit] =
        List.replicate (2 * (n + 1)) .unit := by
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, List.replicate_add]
      rfl
    rw [hjo, runOps_append, ih']
    simp only [Option.bind_some, dstep_joins net (show n < net.m by omega), Option.map_some, hrep]

/-! ## The whole program -/

theorem stN_init (net : Network) : stN net net.m net.k net.m = initStore net := by
  have ht : tblN net.m net.k = tblOf net fun _ => {} := by
    funext h; unfold tblN tblOf; split_ifs <;> first | rfl | omega
  have hj : joinedN net net.m = joinedOf net fun _ => {} := by
    funext h; unfold joinedN joinedOf; split_ifs <;> first | rfl | omega
  simp only [stN, initStore, ht, hj]

/-- **The setup program yields the initial store**, returning the handles the nodes use. -/
theorem setup_init (net : Network) :
    runOps {} (setupOps net) = some (initStore net, setupRes net) := by
  have h1 := run_news net net.m 0 (List.replicate net.k .wsNew ++ joinOps net net.m)
  have h2 := run_wss net net.k 0 (joinOps net net.m)
  have h3 := run_joins net net.m (le_refl _)
  simp only [Nat.zero_add] at h1 h2
  rw [setupOps, List.append_assoc, empty_eq net, h1, h2, h3, stN_init]
  simp only [Option.map_some, setupRes, List.append_assoc, List.range_eq_range']
  rfl

end Silmaril.Wasm.Component.Streams.Setup
