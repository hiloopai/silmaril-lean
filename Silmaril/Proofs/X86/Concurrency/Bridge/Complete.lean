module

public import Silmaril.Proofs.X86.Concurrency.Bridge.Pieces
public import Silmaril.X86.Litmus.Complete.Thms
public import Silmaril.X86.Atomic9.Thms

/-!
# The pieces of a spin-cut function compose: the complete direction

`pieces_complete`: every domain-bounded run of the whole function (`DomRun` of
`whole th`) is matched by a trace of the `pexplore` for the spin bound `n` = the run's length.

* `fetch_prefix`: the fetch of a piece agrees with the fetch of any longer slice with the same
  start (the piece's window is a prefix of the longer one; `Atomic9.decode_append`);
* `fetch_suffix`: the fetch of a slice agrees with the fetch of any slice that starts earlier
  and ends at the same place (same bytes at the same offset);
* `explore_split`, `exploreT_split`: a run of the rest of the function from a piece's start
  splits at the piece's end into a run matched by one of the piece's traces and a run of the rest
  after the piece (the litmus completeness argument, `stepSym_complete`, step by step);
* `pexplore_complete`: induction over the pieces.

Nothing about the pieces' certificates is used: any cut of the code into pieces composes. What
is needed is that the code fits the address space (`L < 2 ^ 64`); a non-empty run implies it.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge

open Silmaril.X86 (State Word Byte maxInstrLength)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus
open Silmaril.X86.Concurrency.Cir.Tv (XThread SThread SPiece pexplore exploreT catTr stvRun pwalk)
open Silmaril.X86.Concurrency.Bridge

/-! ## Fetches of slices -/

theorem if_pos' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]


theorem sub_base (th : SThread) (lo hi : Nat) : (th.sub lo hi).base = th.base + BitVec.ofNat 64 lo := rfl
theorem sub_code (th : SThread) (lo hi : Nat) : (th.sub lo hi).code = (th.code.drop lo).take (hi - lo) := rfl
theorem sub_regions (th : SThread) (lo hi : Nat) : (th.sub lo hi).regions = th.regions := rfl

theorem take_drop_append {α : Type} (A B : List α) (o k : Nat) :
    ∃ more, ((A ++ B).drop o).take k = (A.drop o).take k ++ more := by
  rw [List.drop_append, List.take_append]
  exact ⟨_, rfl⟩

theorem take_drop_append_le {α : Type} (A B : List α) {o k : Nat} (h : o + k ≤ A.length) :
    ((A ++ B).drop o).take k = (A.drop o).take k := by
  rw [List.drop_append, List.take_append_of_le_length (by simp; omega)]

/-- The fetch of a piece is the fetch of any longer slice with the same start. -/
theorem fetch_prefix {th : SThread} {lo mid hi : Nat} (h0 : lo ≤ mid) (h1 : mid ≤ hi) {c : State}
    {i : Atomic9.Instr} {n : Nat} (h : (th.sub lo mid).fetch c = some (i, n)) :
    (th.sub lo hi).fetch c = some (i, n) := by
  have hb : (th.sub lo hi).base = (th.sub lo mid).base := rfl
  have hu : (th.sub lo hi).code = (th.sub lo mid).code ++ ((th.code.drop lo).drop (mid - lo)).take (hi - mid) := by
    simp only [sub_code]
    rw [show hi - lo = (mid - lo) + (hi - mid) by omega, List.take_add]
  unfold Thread.fetch at h ⊢
  rw [hb, hu]
  dsimp only at h ⊢
  generalize (c.rip - (th.sub lo mid).base).toNat = o at h ⊢
  generalize (th.sub lo mid).code = A at h ⊢
  generalize ((th.code.drop lo).drop (mid - lo)).take (hi - mid) = B
  split at h
  · rename_i i' n' hd
    split at h
    · rename_i hc
      cases h
      obtain ⟨more, hm⟩ := take_drop_append A B o maxInstrLength
      rw [hm, Atomic9.decode_append hd more]
      simp only
      rw [take_drop_append_le A B hc.1, List.length_append]
      simp only [hc.2, and_true]
      rw [if_pos' (by omega)]
    · cases h
  · cases h

/-- The fetch of a slice is the fetch of any slice that starts earlier and ends at the same
place (the code fits the address space). -/
theorem fetch_suffix {th : SThread} {lo mid hi : Nat} (h0 : lo ≤ mid) (h1 : mid ≤ hi)
    (h64 : hi < 2 ^ 64) {c : State} {i : Atomic9.Instr} {n : Nat}
    (h : (th.sub mid hi).fetch c = some (i, n)) : (th.sub lo hi).fetch c = some (i, n) := by
  have hU : (th.sub lo hi).code = (th.code.drop lo).take (hi - lo) := rfl
  have hV : (th.sub mid hi).code = (th.code.drop mid).take (hi - mid) := rfl
  have hBu : (th.sub lo hi).base = th.base + BitVec.ofNat 64 lo := rfl
  have hBv : (th.sub mid hi).base = th.base + BitVec.ofNat 64 mid := rfl
  unfold Thread.fetch at h ⊢
  dsimp only at h ⊢
  generalize (th.sub lo hi).code = U at hU ⊢
  generalize (th.sub mid hi).code = V at hV h
  generalize (th.sub lo hi).base = bu at hBu ⊢
  generalize (th.sub mid hi).base = bv at hBv h
  generalize ho3 : (c.rip - bv).toNat = o3 at h
  split at h
  · rename_i i' n' hd
    split at h
    · rename_i hc
      cases h
      have hlen : o3 ≤ hi - mid := by
        have := hc.1; rw [hV] at this; simp only [List.length_take, List.length_drop] at this; omega
      have ho : (c.rip - bu).toNat = o3 + (mid - lo) := by
        have hlen' := hlen
        rw [← ho3, hBv] at hlen' ⊢; rw [hBu]; bv_omega
      have hdrop : U.drop (o3 + (mid - lo)) = V.drop o3 := by
        rw [hU, hV, List.drop_take, List.drop_take, List.drop_drop, List.drop_drop]
        rw [show hi - lo - (o3 + (mid - lo)) = hi - mid - o3 by omega,
          show lo + (o3 + (mid - lo)) = mid + o3 by omega]
      rw [ho, hdrop, hd]
      simp only
      have hl1 : (U.drop (o3 + (mid - lo))).length = (V.drop o3).length := by rw [hdrop]
      simp only [List.length_drop] at hl1
      have hn : n ≠ 0 := by
        rintro rfl; have := hc.2; simp only [List.take_zero, Atomic9.decode_nil] at this; cases this
      rw [if_pos' ⟨by omega, hc.2⟩]
    · cases h
  · cases h

theorem stepSym_fetch {t : Thread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) : ∃ i n, t.fetch s = some (i, n) := by
  unfold stepSym at h
  split at h
  · cases h
  · rename_i i n hf; exact ⟨i, n, hf⟩

/-- No piece fetches at the end of a later slice. -/
theorem fetch_end {th : SThread} {lo mid hi : Nat} (h0 : lo ≤ mid) (h1 : mid ≤ hi) (h64 : hi < 2 ^ 64)
    {c : State} (hc : c.rip = th.base + BitVec.ofNat 64 hi) {i : Atomic9.Instr} {n : Nat}
    (h : (th.sub lo mid).fetch c = some (i, n)) : False := by
  have hL : (th.sub lo mid).code.length ≤ mid - lo := by simp [sub_code]
  have hb : (th.sub lo mid).base = th.base + BitVec.ofNat 64 lo := rfl
  unfold Thread.fetch at h
  dsimp only at h
  rw [hb] at h
  have ho : (c.rip - (th.base + BitVec.ofNat 64 lo)).toNat = hi - lo := by rw [hc]; bv_omega
  rw [ho] at h
  split at h
  · split at h
    · rename_i hc'
      cases h
      have hn : n ≠ 0 := by
        rintro rfl; have := hc'.2; simp only [List.take_zero, Atomic9.decode_nil] at this; cases this
      omega
    · cases h
  · cases h

/-- A run of the code from `lo` to `hi`, seen from a later start `mid`. -/
theorem domRun_later {th : SThread} {dom : List Nat} {lo mid : Nat} (h0 : lo ≤ mid)
    (h1 : mid ≤ th.code.length) (h64 : th.code.length < 2 ^ 64) :
    ∀ {s : State} {run : List SeqStep} {fin : State},
      DomRun (th.sub lo th.code.length) dom s run fin → DomRun (th.sub mid th.code.length) dom s run fin := by
  intro s run fin h
  have hE : (th.sub mid th.code.length).endRip = (th.sub lo th.code.length).endRip := by
    rw [sub_endRip h1 le_rfl, sub_endRip (by omega) le_rfl]
  induction h with
  | done s he => exact .done s (hE ▸ he)
  | step s q rest fin hne hR hl hd hs _ ih =>
    exact .step s q rest fin (hE ▸ hne) hR (loaded_sub h0 h1 le_rfl le_rfl hl)
      (fun i n hf => hd i n (fetch_suffix h0 h1 h64 hf)) hs ih

theorem mapM_some_mem' {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = some rs → ∀ {x : α}, x ∈ l →
      ∃ y, f x = some y ∧ y ∈ rs
  | [], _, _, _, hx => by simp at hx
  | a :: l, rs, h, x, hx => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hl, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy, by simp⟩
    · obtain ⟨y', h', hm⟩ := mapM_some_mem' hl hx
      exact ⟨y', h', by simp [hm]⟩

theorem forall₂_append {α β : Type} {R : α → β → Prop} {a b : List α} {c d : List β}
    (h₁ : List.Forall₂ R a c) (h₂ : List.Forall₂ R b d) : List.Forall₂ R (a ++ b) (c ++ d) := by
  induction h₁ with
  | nil => exact h₂
  | cons hr _ ih => exact .cons hr ih

/-- A trace step matches a run step. -/
def SM (r : StepRec) (q : SeqStep) : Prop :=
  r.post = q.post ∧ Answers q.pre r.acts ∧ applyWrites q.pre r.acts = some q.mem

/-- **Splitting a run at a straight piece's end.** -/
theorem explore_split {th : SThread} {dom : List Nat} {o len : Nat}
    (hfit : o + len ≤ th.code.length) (h64 : th.code.length < 2 ^ 64) :
    ∀ (fuel : Nat) {s : State} {trs : List Trace} {run : List SeqStep} {fin : State},
      explore (th.sub o (o + len)) dom fuel s = some trs →
      DomRun (th.sub o th.code.length) dom s run fin →
      ∃ tr ∈ trs, ∃ run₁ run₂, run = run₁ ++ run₂ ∧ List.Forall₂ SM tr.steps run₁ ∧
        tr.final.rip = th.base + BitVec.ofNat 64 (o + len) ∧
        DomRun (th.sub (o + len) th.code.length) dom tr.final run₂ fin := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs run fin h hr
    unfold explore at h
    split at h
    · rename_i he
      cases h
      refine ⟨_, List.mem_singleton_self _, [], run, rfl, .nil, ?_, domRun_later (by omega) hfit h64 hr⟩
      rw [he, sub_endRip (by omega) hfit]
    · cases h
  | succ f ih =>
    intro s trs run fin h hr
    unfold explore at h
    split at h
    · rename_i he
      cases h
      refine ⟨_, List.mem_singleton_self _, [], run, rfl, .nil, ?_, domRun_later (by omega) hfit h64 hr⟩
      rw [he, sub_endRip (by omega) hfit]
    · dsimp only at h
      split at h
      · cases h
      · rename_i outs hst
        obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        cases hr with
        | done _ he =>
          obtain ⟨i, n, hf⟩ := stepSym_fetch hst
          exact (fetch_end (by omega) hfit h64 (by rw [he, sub_endRip (by omega) le_rfl]) hf).elim
        | step _ q rest _ hne hR hl hd hs tail =>
          obtain ⟨o', ho', hpost, hans, hap⟩ := stepSym_complete hst hR
            (loaded_sub le_rfl (by omega) hfit le_rfl hl)
            (fun i n hf => hd i n (fetch_prefix (by omega) hfit hf)) hs
          obtain ⟨ys, hys, hyr⟩ := mapM_some_mem' hm ho'
          obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
          rw [hpost] at he
          obtain ⟨tr', htr', r₁, r₂, rfl, hm₁, hfin, hr₂⟩ := ih he tail
          refine ⟨⟨⟨o'.1, o'.2⟩ :: tr'.steps, tr'.final⟩, ?_, q :: r₁, r₂, rfl,
            .cons ⟨hpost, hans, hap⟩ hm₁, hfin, hr₂⟩
          exact List.mem_flatten.mpr ⟨_, hyr, List.mem_map.mpr ⟨tr', htr', rfl⟩⟩

/-- **Splitting a run at a spin's end**: as `explore_split`, for the truncating exploration,
when the run is shorter than the fuel. -/
theorem exploreT_split {th : SThread} {dom : List Nat} {o len : Nat}
    (hfit : o + len ≤ th.code.length) (h64 : th.code.length < 2 ^ 64) :
    ∀ (fuel : Nat) {s : State} {trs : List Trace} {run : List SeqStep} {fin : State},
      exploreT (th.sub o (o + len)) dom fuel s = some trs →
      DomRun (th.sub o th.code.length) dom s run fin → run.length < fuel →
      ∃ tr ∈ trs, ∃ run₁ run₂, run = run₁ ++ run₂ ∧ List.Forall₂ SM tr.steps run₁ ∧
        tr.final.rip = th.base + BitVec.ofNat 64 (o + len) ∧
        DomRun (th.sub (o + len) th.code.length) dom tr.final run₂ fin := by
  intro fuel
  induction fuel with
  | zero => intro s trs run fin _ _ hlen; omega
  | succ f ih =>
    intro s trs run fin h hr hlen
    unfold exploreT at h
    split at h
    · rename_i he
      cases h
      refine ⟨_, List.mem_singleton_self _, [], run, rfl, .nil, ?_, domRun_later (by omega) hfit h64 hr⟩
      rw [he, sub_endRip (by omega) hfit]
    · dsimp only at h
      split at h
      · cases h
      · rename_i outs hst
        obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        cases hr with
        | done _ he =>
          obtain ⟨i, n, hf⟩ := stepSym_fetch hst
          exact (fetch_end (by omega) hfit h64 (by rw [he, sub_endRip (by omega) le_rfl]) hf).elim
        | step _ q rest _ hne hR hl hd hs tail =>
          obtain ⟨o', ho', hpost, hans, hap⟩ := stepSym_complete hst hR
            (loaded_sub le_rfl (by omega) hfit le_rfl hl)
            (fun i n hf => hd i n (fetch_prefix (by omega) hfit hf)) hs
          obtain ⟨ys, hys, hyr⟩ := mapM_some_mem' hm ho'
          obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
          rw [hpost] at he
          obtain ⟨tr', htr', r₁, r₂, rfl, hm₁, hfin, hr₂⟩ := ih he tail (by simp at hlen; omega)
          refine ⟨⟨⟨o'.1, o'.2⟩ :: tr'.steps, tr'.final⟩, ?_, q :: r₁, r₂, rfl,
            .cons ⟨hpost, hans, hap⟩ hm₁, hfin, hr₂⟩
          exact List.mem_flatten.mpr ⟨_, hyr, List.mem_map.mpr ⟨tr', htr', rfl⟩⟩

/-- **The pieces from offset `o` are complete** for the runs of the code from `o`, with spin
bound `N` at least the run's length. -/
theorem pexplore_complete {th : SThread} {dom : List Nat} {fuel N : Nat}
    (h64 : th.code.length < 2 ^ 64) :
    ∀ (ps : List SPiece) (o : Nat) (s : State) (trs : List Trace) (run : List SeqStep) (fin : State),
      o + (ps.map SPiece.len).sum = th.code.length → s.rip = th.base + BitVec.ofNat 64 o →
      pexplore th dom fuel N o ps s = some trs →
      DomRun (th.sub o th.code.length) dom s run fin → run.length ≤ N →
      ∃ tr ∈ trs, tr.Matches run fin
  | [], o, s, trs, run, fin, hfit, hs, h, hr, _ => by
    simp only [pexplore, Option.some.injEq] at h
    subst h
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hfit
    cases hr with
    | done _ _ => exact ⟨_, List.mem_singleton_self _, rfl, .nil⟩
    | step _ q rest _ hne =>
      exfalso; apply hne
      rw [hs, sub_endRip (by omega) le_rfl, hfit]
  | p :: ps, o, s, trs, run, fin, hfit, hs, h, hr, hN => by
    simp only [List.map_cons, List.sum_cons] at hfit
    have hle : o + p.len ≤ th.code.length := by omega
    simp only [pexplore] at h
    obtain ⟨trs₁, hhere, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    have hsplit : ∃ tr ∈ trs₁, ∃ run₁ run₂, run = run₁ ++ run₂ ∧ List.Forall₂ SM tr.steps run₁ ∧
        tr.final.rip = th.base + BitVec.ofNat 64 (o + p.len) ∧
        DomRun (th.sub (o + p.len) th.code.length) dom tr.final run₂ fin := by
      rcases p with ⟨its⟩ | ⟨len⟩ | ⟨len, r, md, a, cc⟩
      · exact explore_split hle h64 _ hhere hr
      · exact explore_split hle h64 _ hhere hr
      · exact exploreT_split hle h64 _ hhere hr (by omega)
    obtain ⟨tr₁, htr₁, run₁, run₂, rfl, hm₁, hrip, hr₂⟩ := hsplit
    obtain ⟨ys, hys, hyr⟩ := mapM_some_mem' hm htr₁
    obtain ⟨trs₂, hrest, rfl⟩ := Option.map_eq_some_iff.mp hys
    have hreset : { tr₁.final with rip := th.base + BitVec.ofNat 64 (o + p.len) } = tr₁.final := by
      rw [← hrip]
    rw [hreset] at hrest
    obtain ⟨tr₂, htr₂, hfin, hm₂⟩ := pexplore_complete h64 ps (o + p.len) tr₁.final trs₂ run₂ fin
      (by omega) hrip hrest hr₂ (by simp only [List.length_append] at hN; omega)
    refine ⟨catTr tr₁ tr₂, List.mem_flatten.mpr ⟨_, hyr, List.mem_map.mpr ⟨tr₂, htr₂, rfl⟩⟩,
      hfin, ?_⟩
    exact forall₂_append hm₁ hm₂

/-- A non-empty run of the whole function fits its code in the address space. -/
theorem length_lt_of_run {th : SThread} {dom : List Nat} {run : List SeqStep} {fin : State}
    (h0 : th.init.rip = th.base) (hr : DomRun (whole th) dom th.init run fin) (hne : run ≠ []) :
    th.code.length < 2 ^ 64 := by
  cases hr with
  | done => exact absurd rfl hne
  | step _ q rest _ hne' _ hl =>
    have hw := hl.noWrap
    simp only [Silmaril.Process.addressLimit] at hw
    simp only [whole, Thread.endRip] at hne' hw
    rw [h0] at hne'
    by_contra hge
    have hL : th.code.length = 2 ^ 64 := by
      have := th.base.isLt; omega
    apply hne'
    rw [hL]
    simp

theorem sub_zero_whole (th : SThread) : th.sub 0 th.code.length = whole th := by
  simp [SThread.sub, whole]

/-- **Every domain-bounded run of a whole spin-cut function is a trace of its pieces**, for the
spin bound `n` = the run's length (when the run is non-empty or the code fits the address
space; `Bridge.Task.piecesComplete`). -/
theorem pieces_complete {th : SThread} {c : Silmaril.X86.Concurrency.Cir.Tv.SCert}
    {K : List Silmaril.X86.Concurrency.Cir.Reg} (h : stvRun th c = some K) {dom : List Nat}
    {fuel : Nat} (hsome : ∀ n, (pexplore th dom fuel n 0 c.pieces th.init).isSome = true)
    {run : List SeqStep} {fin : State} (hr : DomRun (whole th) dom th.init run fin)
    (hL : run ≠ [] ∨ th.code.length < 2 ^ 64) :
    ∃ n trs, pexplore th dom fuel n 0 c.pieces th.init = some trs ∧ ∃ tr ∈ trs, tr.Matches run fin := by
  simp only [stvRun] at h
  split at h
  · rename_i hc
    have h0 : th.init.rip = th.base := hc.1
    have hfit := pwalk_fits _ _ _ _ _ h
    have h64 : th.code.length < 2 ^ 64 := hL.elim (length_lt_of_run h0 hr) id
    obtain ⟨trs, htrs⟩ := Option.isSome_iff_exists.mp (hsome run.length)
    refine ⟨run.length, trs, htrs, ?_⟩
    rw [← sub_zero_whole] at hr
    exact pexplore_complete h64 c.pieces 0 th.init trs run fin (by simpa using hfit)
      (by rw [h0]; simp) htrs hr le_rfl
  · cases h

end Silmaril.Proofs.X86.Concurrency.Bridge
