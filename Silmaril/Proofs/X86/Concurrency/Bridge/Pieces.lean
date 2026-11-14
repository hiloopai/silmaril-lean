module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Litmus.Extract.Thms

/-!
# The pieces of a spin-cut function compose: proofs

`pexplore_replays` (header `Silmaril.X86.Concurrency.Bridge.Thms`): every trace of
`pexplore` replays as one trace of the whole function. The pieces:

* `explore_replay`, `exploreT_replay`: the litmus exploration (and the truncating one) from any core
  gives replaying traces (the litmus `explore_sound`, restated from the header's `stepSym_sound`);
* `loaded_slice`: a loaded image has every slice loaded;
* `replay_transport`, `replay_append`: a replay moves to a thread with the same regions and end
  whose code loading implies the old one's, and two replays of abutting slices concatenate;
* `pexplore_replay`: induction over the pieces; `pexplore`'s `rip` reset is the identity on a
  piece's final core, which is at the piece's end.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge

open Silmaril.X86 (State Word Byte)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus
open Silmaril.X86.Concurrency.Cir.Tv (XThread SThread SPiece pexplore exploreT catTr stvRun pwalk)
open Silmaril.X86.Concurrency.Bridge

/-! ## Exploration replays -/

theorem mapM_mem' {α β : Type} {f : α → Option (List β)} :
    ∀ {l : List α} {rss : List (List β)}, l.mapM f = some rss → ∀ {y : β}, y ∈ rss.flatten →
      ∃ x ∈ l, ∃ ys, f x = some ys ∧ y ∈ ys
  | [], rss, h, y, hy => by
    simp at h; subst h; simp at hy
  | x :: l, rss, h, y, hy => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ys, hx, rs, hl, rfl⟩ := h
    simp only [List.flatten_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ⟨x, by simp, ys, hx, hy⟩
    · obtain ⟨x', hx', ys', h', hy'⟩ := mapM_mem' hl hy
      exact ⟨x', by simp [hx'], ys', h', hy'⟩

/-- One explored step replays. -/
theorem step_replay {t : Thread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (hs : stepSym t dom s = some outs) {o : List Act × State} (ho : o ∈ outs) {tr : Trace}
    (h : Replay t o.2 tr.steps tr.final) : Replay t s (⟨o.1, o.2⟩ :: tr.steps) tr.final :=
  .step s ⟨o.1, o.2⟩ tr.steps tr.final
    (fun m hR hl hans => stepSym_sound hs ho m hR hl hans) h

/-- **The litmus exploration replays**, from any core. -/
theorem explore_replay {t : Thread} {dom : List Nat} :
    ∀ (fuel : Nat) {s : State} {trs : List Trace}, explore t dom fuel s = some trs →
      ∀ tr ∈ trs, Replay t s tr.steps tr.final := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs h tr htr
    unfold explore at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      exact .done s he
    · cases h
  | succ f ih =>
    intro s trs h tr htr
    unfold explore at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      exact .done s he
    · dsimp only at h
      split at h
      · cases h
      · rename_i outs hs
        obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨o, ho, ys, hys, hy⟩ := mapM_mem' hm htr
        obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
        simp only [consStep, List.mem_map] at hy
        obtain ⟨tr', htr', rfl⟩ := hy
        exact step_replay hs ho (ih he tr' htr')

/-- **The truncating exploration replays** (a branch out of fuel is dropped, never kept). -/
theorem exploreT_replay {t : XThread} {dom : List Nat} :
    ∀ (fuel : Nat) {s : State} {trs : List Trace}, exploreT t dom fuel s = some trs →
      ∀ tr ∈ trs, Replay t s tr.steps tr.final := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs h tr htr
    unfold exploreT at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      exact .done s he
    · cases h
      simp at htr
  | succ f ih =>
    intro s trs h tr htr
    unfold exploreT at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      exact .done s he
    · dsimp only at h
      split at h
      · cases h
      · rename_i outs hs
        obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨o, ho, ys, hys, hy⟩ := mapM_mem' hm htr
        obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
        simp only [consStep, List.mem_map] at hy
        obtain ⟨tr', htr', rfl⟩ := hy
        exact step_replay hs ho (ih he tr' htr')

/-! ## Replays across slices -/

/-- A replay ends at the thread's end. -/
theorem replay_final_rip {t : Thread} {s s' : State} {st : List StepRec} (h : Replay t s st s') :
    s'.rip = t.endRip := by
  induction h with
  | done s he => exact he
  | step _ _ _ _ _ _ ih => exact ih

/-- **Transport**: a replay holds for a thread with the same regions and end whose code being
loaded implies the old thread's. -/
theorem replay_transport {t t' : Thread} {s s' : State} {st : List StepRec} (h : Replay t s st s')
    (hR : t'.regions = t.regions) (hE : t'.endRip = t.endRip)
    (hL : ∀ m : Memory, Loaded m t'.base t'.code → Loaded m t.base t.code) :
    Replay t' s st s' := by
  induction h with
  | done s he => exact .done s (hE ▸ he)
  | step s r rest s' hstep _ ih =>
    exact .step s r rest s' (fun m hR' hl hans => hstep m (hR ▸ hR') (hL m hl) hans) ih

/-- **Concatenation**: a replay of `t₁` followed by a replay of `t` is a replay of `t`, when
`t`'s code being loaded implies `t₁`'s. -/
theorem replay_append {t t₁ : Thread} {s s₁ s₂ : State} {A B : List StepRec}
    (h₁ : Replay t₁ s A s₁) (h₂ : Replay t s₁ B s₂) (hR : t.regions = t₁.regions)
    (hL : ∀ m : Memory, Loaded m t.base t.code → Loaded m t₁.base t₁.code) :
    Replay t s (A ++ B) s₂ := by
  induction h₁ with
  | done s _ => exact h₂
  | step s r rest s' hstep _ ih =>
    exact .step s r (rest ++ B) s₂ (fun m hR' hl hans => hstep m (hR ▸ hR') (hL m hl) hans)
      (ih h₂)

/-- Every slice of a loaded image is loaded. -/
theorem loaded_slice {m : Memory} {b : Word} {bs : List Byte} (h : Loaded m b bs) {k j : Nat}
    (hk : k + j ≤ bs.length) : Loaded m (b + BitVec.ofNat 64 k) ((bs.drop k).take j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Loaded, Memory.fetchBytes, Memory.readWith, Memory.checkSpan, Memory.readBacking,
      Silmaril.Process.addressLimit]
    constructor <;> omega
  · have hw := h.noWrap
    have hsub := h.fetchBytes_sub hj hk
    have hlen : ((bs.drop k).take j).length = j := by simp; omega
    have haddr : (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
      simp only [Silmaril.Process.addressLimit] at hw
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
    unfold Loaded
    rw [haddr, hlen, hsub]

theorem sub_code_length {th : SThread} {lo hi : Nat} (_h : lo ≤ hi) (hhi : hi ≤ th.code.length) :
    (th.sub lo hi).code.length = hi - lo := by
  simp [SThread.sub]; omega

theorem sub_endRip {th : SThread} {lo hi : Nat} (h : lo ≤ hi) (hhi : hi ≤ th.code.length) :
    (th.sub lo hi).endRip = th.base + BitVec.ofNat 64 hi := by
  unfold Thread.endRip
  rw [sub_code_length h hhi]
  simp only [SThread.sub, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega

/-- A sub-slice of a loaded slice is loaded. -/
theorem loaded_sub {th : SThread} {lo hi lo' hi' : Nat} (h1 : lo ≤ lo') (h2 : lo' ≤ hi')
    (h3 : hi' ≤ hi) (h4 : hi ≤ th.code.length) {m : Memory}
    (hl : Loaded m (th.sub lo hi).base (th.sub lo hi).code) :
    Loaded m (th.sub lo' hi').base (th.sub lo' hi').code := by
  have := loaded_slice hl (k := lo' - lo) (j := hi' - lo')
    (by rw [sub_code_length (by omega) h4]; omega)
  simp only [SThread.sub, BitVec.add_assoc, BitVec.ofNat_add_ofNat, List.drop_take,
    List.drop_drop, List.take_take] at this ⊢
  rwa [show min (hi' - lo') (hi - lo - (lo' - lo)) = hi' - lo' by omega,
    show lo + (lo' - lo) = lo' by omega] at this

/-! ## The pieces -/

/-- The pieces' lengths fit: each piece from offset `o` lies in the code and the last one ends
at its end. -/
theorem pwalk_fits {th : SThread} :
    ∀ (ps : List SPiece) (o : Nat) (K Z : List Silmaril.X86.Concurrency.Cir.Reg)
      (K' : List Silmaril.X86.Concurrency.Cir.Reg),
      pwalk th o ps K Z = some K' → o + (ps.map SPiece.len).sum = th.code.length
  | [], o, K, Z, K', h => by
    simp only [pwalk] at h
    split at h
    · simp_all
    · cases h
  | p :: ps, o, K, Z, K', h => by
    simp only [pwalk] at h
    split at h
    · rename_i hfit
      have key : ∀ K₁ Z₁, pwalk th (o + p.len) ps K₁ Z₁ = some K' →
          o + ((p :: ps).map SPiece.len).sum = th.code.length := by
        intro K₁ Z₁ hw
        have := pwalk_fits ps (o + p.len) K₁ Z₁ K' hw
        simp only [List.map_cons, List.sum_cons]
        omega
      split at h
      · split at h
        · exact key _ _ h
        · cases h
      · split at h
        · exact key _ _ h
        · cases h
      · split at h
        · exact key _ _ h
        · cases h
    · cases h

/-- **The pieces from offset `o` replay as the slice from `o` to the end.** -/
theorem pexplore_replay {th : SThread} {dom : List Nat} {fuel n : Nat} :
    ∀ (ps : List SPiece) (o : Nat) (s : State) (trs : List Trace),
      o + (ps.map SPiece.len).sum = th.code.length → s.rip = th.base + BitVec.ofNat 64 o →
      pexplore th dom fuel n o ps s = some trs →
      ∀ tr ∈ trs, Replay (th.sub o th.code.length) s tr.steps tr.final
  | [], o, s, trs, hfit, hs, h => by
    simp only [pexplore, Option.some.injEq] at h
    subst h
    intro tr htr
    simp only [List.mem_singleton] at htr
    subst htr
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hfit
    refine .done s ?_
    rw [sub_endRip (by omega) (by omega), hs, hfit]
  | p :: ps, o, s, trs, hfit, hs, h => by
    simp only [List.map_cons, List.sum_cons] at hfit
    have hle : o + p.len ≤ th.code.length := by omega
    simp only [pexplore] at h
    obtain ⟨trs₁, hhere, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    intro tr htr
    obtain ⟨tr₁, htr₁, ys, hys, hy⟩ := mapM_mem' hm htr
    obtain ⟨trs₂, hrest, rfl⟩ := Option.map_eq_some_iff.mp hys
    simp only [List.mem_map] at hy
    obtain ⟨tr₂, htr₂, rfl⟩ := hy
    have h₁ : Replay (th.sub o (o + p.len)) s tr₁.steps tr₁.final := by
      rcases p with ⟨its⟩ | ⟨len⟩ | ⟨len, r, md, a, cc⟩
      · exact explore_replay _ hhere tr₁ htr₁
      · exact explore_replay _ hhere tr₁ htr₁
      · exact exploreT_replay _ hhere tr₁ htr₁
    have hend := replay_final_rip h₁
    rw [sub_endRip (by omega) hle] at hend
    have hreset : { tr₁.final with rip := th.base + BitVec.ofNat 64 (o + p.len) } = tr₁.final := by
      rw [← hend]
    rw [hreset] at hrest
    have h₂ := pexplore_replay ps (o + p.len) tr₁.final trs₂ (by omega) hend hrest tr₂ htr₂
    have h₂' : Replay (th.sub o th.code.length) tr₁.final tr₂.steps tr₂.final :=
      replay_transport h₂ rfl (by rw [sub_endRip (by omega) le_rfl, sub_endRip (by omega) le_rfl])
        (fun m hl => loaded_sub (by omega) (by omega) le_rfl le_rfl hl)
    exact replay_append h₁ h₂' rfl (fun m hl => loaded_sub le_rfl (by omega) hle le_rfl hl)

/-- **The pieces replay as the whole function.** -/
theorem pexplore_replays {th : SThread} {c : Silmaril.X86.Concurrency.Cir.Tv.SCert}
    {K : List Silmaril.X86.Concurrency.Cir.Reg} (h : stvRun th c = some K) {dom : List Nat}
    {fuel n : Nat} {trs : List Trace}
    (hx : pexplore th dom fuel n 0 c.pieces th.init = some trs) :
    ∀ tr ∈ trs, Replay (whole th) th.init tr.steps tr.final := by
  simp only [stvRun] at h
  split at h
  · rename_i hc
    have hfit := pwalk_fits _ _ _ _ _ h
    intro tr htr
    have := pexplore_replay c.pieces 0 th.init trs hfit (by simpa using hc.1) hx tr htr
    refine replay_transport this rfl ?_ ?_
    · rw [sub_endRip (by omega) le_rfl]; rfl
    · intro m hl
      simpa [SThread.sub, whole] using hl
  · cases h

end Silmaril.Proofs.X86.Concurrency.Bridge
