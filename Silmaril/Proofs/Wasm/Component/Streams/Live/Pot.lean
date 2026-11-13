module

public import Silmaril.Proofs.Wasm.Component.Streams.Live.Pos
public import Silmaril.Proofs.Wasm.Component.Streams.Net.Final

/-!
# Every step decreases the potential

`step_pot_lt`: in a system satisfying the network invariant (`Inv`) and the positivity facts
(`StPos`), every step of every node strictly decreases `pot B Bo`, provided the bounds hold after
the step. The step's effect on its node:

* `readBlk`: the input goes from `idle` to `busy`;
* `readNow`: `COMPLETED` delivers at least one item (`read_res`); `DROPPED` ends the input;
* `write`: `BLOCKED` makes the output `busy`; `COMPLETED` acknowledges at least one item
  (`write_res`); `DROPPED` makes it `dead`;
* `waitIn`: a `COMPLETED` event comes only to a busy input and delivers at least one item
  (`takeR_res`); `DROPPED` ends the input;
* `waitOut`: a `COMPLETED` event comes only to a busy output and acknowledges at least one item
  (`takeW_res`); `DROPPED` makes it `dead`;
* `dropIn`, `dropOut`: the end becomes `gone` or `closed`, of weight `0`.

Every item counted has weight `3`, and a state can rise by at most `1` (`busy` to `idle`), so the
potential falls by at least `1` at each step.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Live

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event upd blocked packCopy CopyResult)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Proofs.Wasm.Component.Streams.Net

/-! ## What the built-ins report -/

/-- A `COMPLETED` read delivers at least one item. -/
theorem read_res {c c' : DChan} {n p : Nat} {ys : List Val}
    (h : c.read n = some (c', .read p ys)) (hs : status p = 0) : ys ≠ [] := by
  unfold DChan.read at h
  split_ifs at h with h1 h2
  · split at h
    · obtain ⟨-, h3⟩ := Option.some.inj h |> Prod.mk.inj
      obtain ⟨rfl, -⟩ := Res.read.inj h3
      simp [status_packCopy, CopyResult.toNat] at hs
    · cases h
  · split at h
    · cases h
    · cases h
    · rename_i xs hx hb
      obtain ⟨-, h3⟩ := Option.some.inj h |> Prod.mk.inj
      obtain ⟨-, rfl⟩ := Res.read.inj h3
      have hn : n ≠ 0 := fun e => h1 (Or.inr (Or.inr e))
      have hl : 0 < xs.length := List.length_pos_iff.2 hx
      exact List.ne_nil_of_length_pos (by simp; omega)

/-- A `COMPLETED` write acknowledges at least one item, at most those offered. -/
theorem write_res {c c' : DChan} {xs : List Val} {r : Nat} (hP : c.Pos)
    (h : c.write xs = some (c', .nat r)) (hb : r ≠ blocked) (hs : status r = 0) :
    0 < count r ∧ count r ≤ xs.length := by
  unfold DChan.write at h
  split_ifs at h with h1 h2
  · split at h
    · obtain ⟨-, h3⟩ := Option.some.inj h |> Prod.mk.inj
      obtain rfl := Res.nat.inj h3
      simp [status_packCopy, CopyResult.toNat] at hs
    · cases h
  · split at h
    · obtain ⟨-, h3⟩ := Option.some.inj h |> Prod.mk.inj
      exact absurd (Res.nat.inj h3).symm hb
    · rename_i n hrc
      obtain ⟨-, h3⟩ := Option.some.inj h |> Prod.mk.inj
      obtain rfl := Res.nat.inj h3
      have hx : xs ≠ [] := fun e => h1 (Or.inr (Or.inr e))
      have hn : n ≠ 0 := fun e => hP.rcap (by rw [hrc, e])
      have hl : 0 < xs.length := List.length_pos_iff.2 hx
      rw [count_packCopy]
      omega

theorem takeR_some {c c' : DChan} {p : Nat} {ys : List Val} (h : c.takeR = some (c', p, ys)) :
    ∃ q, c.r.ev = some q ∧
      p = (if c.w.gone then packCopy .dropped q else packCopy .completed q) ∧ ys = c.rgot := by
  unfold DChan.takeR at h
  split at h
  · cases h
  · rename_i q hq
    obtain ⟨-, h3⟩ := Option.some.inj h |> Prod.mk.inj
    obtain ⟨hp, hy⟩ := Prod.mk.inj h3
    exact ⟨q, hq, hp.symm, hy.symm⟩

theorem takeW_some {c c' : DChan} {p : Nat} (h : c.takeW = some (c', p)) :
    ∃ q, c.w.ev = some q ∧ p = (if c.r.gone then packCopy .dropped q else packCopy .completed q) := by
  unfold DChan.takeW at h
  split at h
  · cases h
  · rename_i q hq
    exact ⟨q, hq, (Prod.mk.inj (Option.some.inj h)).2.symm⟩

theorem status_dropped {g : Bool} {q : Nat} (hs : status (if g then packCopy .dropped q else
    packCopy .completed q) = 0) : g = false := by
  cases g
  · rfl
  · simp [status_packCopy, CopyResult.toNat] at hs

/-- An event of an input: the input was idle or busy; a `COMPLETED` one was busy and delivers at
least one item. -/
theorem takeR_res {got : List Val} {R : RV} {c c' : DChan} {p : Nat}
    {ys : List Val} (hP : c.Pos) (hI : RInv R got c) (h : c.takeR = some (c', p, ys)) :
    (R = .idle ∨ R = .busy) ∧ (status p = 0 → R = .busy ∧ ys ≠ []) := by
  obtain ⟨q, hq, rfl, rfl⟩ := takeR_some h
  cases R with
  | idle =>
    have hev : c.r.ev = (if c.w.gone then some 0 else none) := hI.2.2.2.2.2
    have hw : c.w.gone = true := by cases hg : c.w.gone <;> simp_all
    exact ⟨Or.inl rfl, fun hs => absurd (status_dropped hs) (by simp [hw])⟩
  | busy =>
    refine ⟨Or.inr rfl, fun hs => ⟨rfl, ?_⟩⟩
    have hw : c.w.gone = false := status_dropped hs
    have hlen : q = c.rgot.length := hI.2.2.2.2.1 q hq
    exact List.ne_nil_of_length_pos (hlen ▸ hP.rev hw q hq)
  | ended => exact absurd hq (by simp [hI.2.2.2.2.1])
  | gone b => exact absurd hq (by simp [hI.2.2.2.2])

/-- An event of an output: the output was idle or busy; a `COMPLETED` one was busy and
acknowledges at least one item, at most those it offered. -/
theorem takeW_res {W : WV} {ack : List Val} {c c' : DChan} {p : Nat} (hP : c.Pos)
    (hI : WInv W ack c) (h : c.takeW = some (c', p)) :
    (W = .idle ∨ ∃ xs, W = .busy xs) ∧
      (status p = 0 → ∃ xs, W = .busy xs ∧ 0 < count p ∧ count p ≤ xs.length) := by
  obtain ⟨q, hq, rfl⟩ := takeW_some h
  cases W with
  | idle =>
    have hev : c.w.ev = (if c.r.gone then some 0 else none) := hI.2.2.2.2
    have hr : c.r.gone = true := by cases hg : c.r.gone <;> simp_all
    exact ⟨Or.inl rfl, fun hs => absurd (status_dropped hs) (by simp [hr])⟩
  | busy xs =>
    refine ⟨Or.inr ⟨xs, rfl⟩, fun hs => ⟨xs, rfl, ?_⟩⟩
    have hr : c.r.gone = false := status_dropped hs
    have hwp : c.wp ≤ xs.length := hI.2.2.2.1
    have hwq : c.wp = q := by simp [DChan.wp, hq]
    have hc : count (if c.r.gone then packCopy .dropped q else packCopy .completed q) = q := by
      simp [hr, count_packCopy]
    rw [hc]
    exact ⟨hP.wev hr q hq, hwq ▸ hwp⟩
  | dead => exact absurd hq (by simp [hI.2.2.2.1])
  | closed d => exact absurd hq (by simp [hI.2.2.2])

/-! ## Potentials -/

theorem oPot_push (bo : Nat) (ys : List Val) (o : Out) : oPot bo (o.push ys) = oPot bo o := by
  obtain ⟨st, a⟩ := o
  cases st <;> rfl

theorem outsPot_push (bo : Nat) (ys : List Val) (os : List Out) :
    outsPot bo (os.map (Out.push ys)) = outsPot bo os := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [outsPot, List.map_cons, List.sum_cons] at ih ⊢
    rw [oPot_push, ih]

theorem outsPot_set_lt {bo : Nat} {os : List Out} {j : Nat} {o o' : Out}
    (hj : os[j]? = some o) (hlt : oPot bo o' < oPot bo o) :
    outsPot bo (os.set j o') < outsPot bo os := by
  induction os generalizing j with
  | nil => simp at hj
  | cons a os ih =>
    cases j with
    | zero =>
      have ha : a = o := by simpa using hj
      subst ha
      simp only [outsPot, List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
    | succ j =>
      have hj' : os[j]? = some o := by simpa using hj
      have := ih hj'
      simp only [outsPot, List.set_cons_succ, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- An output that acknowledges more, or whose state falls, has a smaller potential. -/
theorem oPot_lt {bo : Nat} {o o' : Out} (hb : o'.ack.length ≤ bo)
    (h : (o.ack.length < o'.ack.length ∧ osW o'.st ≤ osW o.st + 1) ∨
      (o.ack.length ≤ o'.ack.length ∧ osW o'.st < osW o.st)) : oPot bo o' < oPot bo o := by
  unfold oPot
  omega

/-- After a write event (or result) `p`, a busy output's potential falls. -/
theorem oPot_onWrite_busy {bo : Nat} {xs q a : List Val} {p : Nat}
    (hb : (Out.onWrite ⟨.busy xs q, a⟩ p).ack.length ≤ bo)
    (hc : status p = 0 → 0 < count p ∧ count p ≤ xs.length) :
    oPot bo (Out.onWrite ⟨.busy xs q, a⟩ p) < oPot bo ⟨.busy xs q, a⟩ := by
  refine oPot_lt hb ?_
  by_cases hs : status p = 0
  · obtain ⟨h1, h2⟩ := hc hs
    left
    simp only [Out.onWrite, hs, ↓reduceIte, List.length_append, List.length_take, osW]
    omega
  · right
    simp [Out.onWrite, hs, osW]

/-- After an idle output's write event `p`, which is `DROPPED`, its potential falls. -/
theorem oPot_onWrite_idle {bo : Nat} {q a : List Val} {p : Nat} (hs : status p ≠ 0)
    (hb : (Out.onWrite ⟨.idle q, a⟩ p).ack.length ≤ bo) :
    oPot bo (Out.onWrite ⟨.idle q, a⟩ p) < oPot bo ⟨.idle q, a⟩ := by
  refine oPot_lt hb (Or.inr ?_)
  simp [Out.onWrite, hs, osW]

/-- After a write of a nonempty prefix of an idle output's queue, its potential falls. -/
theorem oPot_afterWrite {bo : Nat} {q a : List Val} {n r : Nat}
    (hb : (Out.afterWrite (q.take n) (q.drop n) a r).ack.length ≤ bo)
    (hc : r ≠ blocked → status r = 0 → 0 < count r ∧ count r ≤ (q.take n).length) :
    oPot bo (Out.afterWrite (q.take n) (q.drop n) a r) < oPot bo ⟨.idle q, a⟩ := by
  by_cases hr : r = blocked
  · subst hr
    unfold oPot
    simp [Out.afterWrite, osW]
  · have hb' : (Out.onWrite ⟨.busy (q.take n) (q.drop n), a⟩ r).ack.length ≤ bo := by
      simpa [Out.afterWrite, hr] using hb
    have h1 := oPot_onWrite_busy hb' (hc hr)
    have h2 : Out.afterWrite (q.take n) (q.drop n) a r =
        Out.onWrite ⟨.busy (q.take n) (q.drop n), a⟩ r := by simp [Out.afterWrite, hr]
    rw [h2]
    unfold oPot at h1 ⊢
    simp only [osW] at h1 ⊢
    omega

/-! ## Nodes -/

variable {σ : Type}

theorem nodePot_onRead_lt {b bo : Nat} {T : Tr σ Val Val} {x : NSt σ} {p : Nat} {ys : List Val}
    (hb : (x.onRead T p ys).got.length ≤ b) (hrd : x.rd = .idle ∨ x.rd = .busy)
    (hc : status p = 0 → ys ≠ []) : nodePot b bo (x.onRead T p ys) < nodePot b bo x := by
  have ho : outsPot bo (x.onRead T p ys).outs = outsPot bo x.outs := outsPot_push _ _ _
  have hw : rdW x.rd = 2 ∨ rdW x.rd = 3 := by rcases hrd with h | h <;> simp [h, rdW]
  have hg : (x.onRead T p ys).got.length = x.got.length + ys.length := by simp [NSt.onRead]
  unfold nodePot
  rw [ho, hg]
  rw [hg] at hb
  by_cases hs : status p = 0
  · have hy : 0 < ys.length := List.length_pos_iff.2 (hc hs)
    have hr : rdW (x.onRead T p ys).rd = 3 := by simp [NSt.onRead, hs, rdW]
    rw [hr]
    omega
  · have hr : rdW (x.onRead T p ys).rd = 1 := by simp [NSt.onRead, hs, rdW]
    rw [hr]
    omega

theorem nodePot_set_lt {b bo : Nat} {x : NSt σ} {j : Nat} {o o' : Out}
    (hj : x.outs[j]? = some o) (hlt : oPot bo o' < oPot bo o) :
    nodePot b bo { x with outs := x.outs.set j o' } < nodePot b bo x := by
  have := outsPot_set_lt hj hlt
  unfold nodePot
  simp only
  omega

theorem nodePot_stop_lt {b bo : Nat} {T : Tr σ Val Val} {x : NSt σ} (hm : x.mayStop T) :
    nodePot b bo (x.stop T) < nodePot b bo x := by
  have ho : outsPot bo (x.stop T).outs = outsPot bo x.outs := outsPot_push _ _ _
  have hw : 0 < rdW x.rd := by
    rcases hm with h | ⟨h, -⟩ <;> simp [h, rdW]
  have hg : (x.stop T).got = x.got := rfl
  have hr : rdW (x.stop T).rd = 0 := rfl
  unfold nodePot
  rw [ho, hg, hr]
  omega

theorem ack_le_of_set {bo : Nat} {os : List Out} {j : Nat} {o o' : Out} (hj : os[j]? = some o)
    (hbo : ∀ u ∈ os.set j o', u.ack.length ≤ bo) : o'.ack.length ≤ bo := by
  have hlt : j < os.length := (List.getElem?_eq_some_iff.1 hj).1
  exact hbo o' (List.mem_set hlt o')

/-- After a write event, whose report `takeW_res` describes, an output's potential falls. -/
theorem oPot_onWrite_ev {bo : Nat} {o : Out} {p : Nat}
    (hb : (o.onWrite p).ack.length ≤ bo)
    (hres : (o.st.view = .idle ∨ ∃ xs, o.st.view = .busy xs) ∧
      (status p = 0 → ∃ xs, o.st.view = .busy xs ∧ 0 < count p ∧ count p ≤ xs.length)) :
    oPot bo (o.onWrite p) < oPot bo o := by
  obtain ⟨st, a⟩ := o
  obtain ⟨h1, h2⟩ := hres
  cases st with
  | idle q =>
    refine oPot_onWrite_idle (fun hs => ?_) hb
    obtain ⟨xs, hx, -⟩ := h2 hs
    cases hx
  | busy xs q =>
    refine oPot_onWrite_busy hb (fun hs => ?_)
    obtain ⟨ys, hy, hc⟩ := h2 hs
    cases hy
    exact hc
  | dead => rcases h1 with h | ⟨_, h⟩ <;> cases h
  | closed d => rcases h1 with h | ⟨_, h⟩ <;> cases h

/-! ## Steps -/

variable {net : Network}

/-- The output `j` of node `i`, writing stream `c`, is the writer's output of `c`. -/
theorem wOut_eq (hwf : net.WF) (s : Sys net) {i : Fin net.k} {j c : Nat}
    (hout : (net.node i).outs[j]? = some c) : wOut s c = (s.ns i).outs[j]? := by
  obtain ⟨-, hw⟩ := hwf.out_wr i j c hout
  unfold wOut
  rw [hw]

theorem readBlk_pot_lt {σ : Type} {b bo : Nat} {x : NSt σ} (hrd : x.rd = .idle) :
    nodePot b bo { x with rd := .busy } < nodePot b bo x := by
  simp only [nodePot, hrd, rdW]
  omega

theorem write_pot_lt {s : Sys net} (hI : Inv net s) (hP : StPos s.st) {i : Fin net.k}
    {j c : Nat} {q a : List Val} {n r : Nat} {st' : DStore} {b bo : Nat}
    (hj : (s.ns i).outs[j]? = some ⟨.idle q, a⟩)
    (hbo : ∀ o ∈ ((s.ns i).outs.set j (Out.afterWrite (q.take n) (q.drop n) a r)),
      o.ack.length ≤ bo)
    (hds : dstep s.st (.streamWrite (wh c) (q.take n)) = some (st', .nat r)) :
    nodePot b bo { s.ns i with outs := (s.ns i).outs.set j (Out.afterWrite (q.take n) (q.drop n) a r) }
      < nodePot b bo (s.ns i) := by
  obtain ⟨-, c', hwr, -⟩ := dstep_write hI.coh hds
  have hres : r ≠ blocked → status r = 0 → 0 < count r ∧ count r ≤ (q.take n).length :=
    fun hr hs => write_res (hP _) hwr hr hs
  exact nodePot_set_lt hj (oPot_afterWrite (ack_le_of_set hj hbo) hres)

theorem waitIn_pot_lt (hwf : net.WF) {s : Sys net} (hI : Inv net s) (hP : StPos s.st)
    {i : Fin net.k} {c : Nat} (hinp : (net.node i).inp = some c) {st' : DStore} {e : Event}
    {b bo : Nat} (hb : ((s.ns i).onRead (net.node i).T e.payload e.items).got.length ≤ b)
    (hw : DWait s.st (net.ws i) (rh c) st' e) :
    nodePot b bo ((s.ns i).onRead (net.node i).T e.payload e.items) < nodePot b bo (s.ns i) := by
  obtain ⟨hm, c', htake, -⟩ := wait_rh hI.coh hw
  obtain ⟨-, hrd⟩ := hwf.inp_rd i c hinp
  obtain ⟨o, -, hinv⟩ := hI.chan c hm
  have hR : RInv (s.ns i).rd (s.ns i).got (s.st.chans (rh c)) := hrd ▸ hinv.2.1
  obtain ⟨h1, h2⟩ := takeR_res (hP _) hR htake
  exact nodePot_onRead_lt hb h1 (fun hs => (h2 hs).2)

theorem waitOut_pot_lt (hwf : net.WF) {s : Sys net} (hI : Inv net s) (hP : StPos s.st)
    {i : Fin net.k} {j c : Nat} (hout : (net.node i).outs[j]? = some c) {o : Out}
    (hj : (s.ns i).outs[j]? = some o) {st' : DStore} {e : Event} {b bo : Nat}
    (hbo : ∀ u ∈ ((s.ns i).outs.set j (o.onWrite e.payload)), u.ack.length ≤ bo)
    (hw : DWait s.st (net.ws i) (wh c) st' e) :
    nodePot b bo { s.ns i with outs := (s.ns i).outs.set j (o.onWrite e.payload) }
      < nodePot b bo (s.ns i) := by
  obtain ⟨hm, c', htake, -⟩ := wait_wh hI.coh hw
  obtain ⟨o₁, ho₁, hinv⟩ := hI.chan c hm
  have ho : o₁ = o := by
    rw [wOut_eq hwf s hout, hj] at ho₁
    exact (Option.some.inj ho₁).symm
  have hres := takeW_res (hP _) (ho ▸ hinv.1) htake
  exact nodePot_set_lt hj (oPot_onWrite_ev (ack_le_of_set hj hbo) hres)

theorem dropOut_pot_lt {σ : Type} {x : NSt σ} {j : Nat} {a : List Val} {d : Bool} {b bo : Nat}
    (hj : x.outs[j]? = some ⟨.idle [], a⟩ ∧ d = false ∨ x.outs[j]? = some ⟨.dead, a⟩ ∧ d = true)
    (hbo : ∀ u ∈ (x.outs.set j ⟨.closed d, a⟩), u.ack.length ≤ bo) :
    nodePot b bo { x with outs := x.outs.set j ⟨.closed d, a⟩ } < nodePot b bo x := by
  rcases hj with ⟨hj, -⟩ | ⟨hj, -⟩
  · exact nodePot_set_lt hj (oPot_lt (ack_le_of_set hj hbo) (Or.inr ⟨le_refl _, by simp [osW]⟩))
  · exact nodePot_set_lt hj (oPot_lt (ack_le_of_set hj hbo) (Or.inr ⟨le_refl _, by simp [osW]⟩))

/-- **A step of node `i` decreases its potential.** -/
theorem nstep_pot_lt (hwf : net.WF) {s : Sys net} (hI : Inv net s) (hP : StPos s.st)
    (i : Fin net.k) {st' : DStore} {x' : NSt (net.node i).σ}
    (hn : NStep (net.node i) (net.ws i) s.st (s.ns i) st' x') {b bo : Nat}
    (hb : x'.got.length ≤ b) (hbo : ∀ o ∈ x'.outs, o.ack.length ≤ bo) :
    nodePot b bo x' < nodePot b bo (s.ns i) := by
  cases hn with
  | readBlk _ hrd => exact readBlk_pot_lt hrd
  | readNow _ hrd _ _ hds =>
    obtain ⟨-, c', hread, -⟩ := dstep_read hI.coh hds
    exact nodePot_onRead_lt hb (Or.inl hrd) (read_res hread)
  | write _ hj _ _ hds => exact write_pot_lt hI hP hj hbo hds
  | waitIn hinp hw => exact waitIn_pot_lt hwf hI hP hinp hb hw
  | waitOut hout hj hw => exact waitOut_pot_lt hwf hI hP hout hj hbo hw
  | dropIn _ hstop _ => exact nodePot_stop_lt hstop
  | dropOut _ _ hj _ => exact dropOut_pot_lt hj hbo

/-- A sum over a list in which one summand falls and none rises falls. -/
theorem foldr_lt {k : Nat} (l : List (Fin k)) (f g : Fin k → Nat) (hle : ∀ j, g j ≤ f j)
    (hlt : ∃ j ∈ l, g j < f j) :
    l.foldr (fun j a => g j + a) 0 < l.foldr (fun j a => f j + a) 0 := by
  induction l with
  | nil => simp at hlt
  | cons a l ih =>
    simp only [List.foldr_cons]
    obtain ⟨j, hj, hjl⟩ := hlt
    rcases List.mem_cons.1 hj with rfl | hj'
    · have : l.foldr (fun j a => g j + a) 0 ≤ l.foldr (fun j a => f j + a) 0 := by
        clear ih hj
        induction l with
        | nil => exact le_refl _
        | cons b l ih' => simp only [List.foldr_cons]; have := hle b; omega
      omega
    · have := ih ⟨j, hj', hjl⟩
      have := hle a
      omega

/-- **Every step decreases the potential**, when the bounds hold after it. -/
theorem step_pot_lt (hwf : net.WF) {B Bo : Fin net.k → Nat} {s s' : Sys net} (hI : Inv net s)
    (hP : StPos s.st) (hB : Bounded B Bo s') (h : Step net s s') : pot B Bo s' < pot B Bo s := by
  obtain ⟨i, hn⟩ := h
  rename_i st' x'
  have hbi := hB i
  simp only [Function.update_self] at hbi
  have hlt := nstep_pot_lt hwf hI hP i hn hbi.1 hbi.2
  unfold pot
  refine foldr_lt _ _ _ (fun j => ?_) ⟨i, List.mem_finRange i, ?_⟩
  · by_cases e : j = i
    · subst e
      simp only [Function.update_self]
      exact le_of_lt hlt
    · simp [Function.update_of_ne e]
  · simp only [Function.update_self]
    exact hlt

end Silmaril.Proofs.Wasm.Component.Streams.Live
