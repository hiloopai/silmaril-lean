module

public import Silmaril.Proofs.Wasm.Component.FXRes.ContPool.Step

/-!
# Continuations in the table or in a store: the moves of `new` and `take`, and the other steps

* `inv_cbNew`: `new` moves the identity of store entry `k` to the table entry it fills; the
  store entry is dead afterwards (`dead_after_new`);
* `inv_cbTake`: `take` moves the identity of the table entry to the new store entry; the table
  entry is dead afterwards (`dead_after_take`);
* `inv_cbOther`, `inv_spawn`, `inv_resume`, `inv_env`, `inv_finish`;
* **`gstep_inv`**: every `GStep` keeps `GInv`; `pstep_lift`: every pool step has its identity
  update; `gstep_proj`: every `GStep` is a pool step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContPool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (ContFX AdminFX)
open Silmaril.Wasm.Models.FXV (CtxV)
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXRes Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-! ## `new` -/

/-- After `new`, the moved store entry is dead. -/
theorem dead_after_new {s : EStore H} {ts : List (Option (ThreadV (CH H)))} {i k : ℕ}
    {t : ThreadV (CH H)} {K : KStore} {f : Frame} {code : List AdminFX}
    (hi : ts[i]? = some (some t)) :
    ¬ Live ⟨s, ts.set i (some (.fx (K.set k none) f code))⟩ (.store i k) := by
  intro h
  rcases live_store_set (s := s) hi h with ⟨-, C, hC⟩ | ⟨hne, -⟩
  · exact (live_of_set_none hC).2 rfl
  · exact hne rfl

theorem cbNew_back {s : Store (FXCode (CH H))} {tb tb' : Table ContFX}
    {ts : List (Option (ThreadV (CH H)))} {i k n : ℕ} {K : KStore} {f : Frame}
    {code code' : List AdminFX} (hi : ts[i]? = some (some (.fx K f code)))
    (hframe : ∀ j, j ≠ n → tb'.get? j = tb.get? j) :
    ∀ l, Live ⟨⟨s, tb'⟩, ts.set i (some (.fx (K.set k none) f code'))⟩ l →
      l ≠ .tab n → Live ⟨⟨s, tb⟩, ts⟩ l := by
  intro l hl hne
  cases l with
  | store i' j =>
    rcases live_store_set (s := ⟨s, tb⟩) hi hl with ⟨rfl, C', hC'⟩ | ⟨-, h⟩
    · exact ⟨_, hi, C', (live_of_set_none hC').1⟩
    · exact h
  | tab m =>
    obtain ⟨C', hC'⟩ := hl
    have hm : m ≠ n := fun hm => hne (by rw [hm])
    exact ⟨C', (hframe m hm) ▸ hC'⟩

theorem inv_cbNew {s : Store (FXCode (CH H))} {tb tb' : Table ContFX}
    {ts : List (Option (ThreadV (CH H)))} {g : Ghost} (hI : GInv ⟨⟨s, tb⟩, ts⟩ g) {i k n : ℕ}
    {K : KStore} {f : Frame} {code code' : List AdminFX} {C : ContFX}
    (hi : ts[i]? = some (some (.fx K f code))) (hk : K[k]? = some (some C))
    (ht : tb.add? C = some (n, tb')) :
    GInv ⟨⟨s, tb'⟩, ts.set i (some (.fx (K.set k none) f code'))⟩
      (g.move (.store i k) (.tab n)) := by
  obtain ⟨-, -, hframe, hwf⟩ := add?_fresh hI.wf ht
  exact inv_move hI hwf ⟨_, hi, C, hk⟩ (dead_after_new hi) (cbNew_back hi hframe)

/-! ## `take` -/

theorem tab_back_of_remove {tb tb' : Table ContFX} {N : ℕ} {C : ContFX}
    (ht : tb.remove? N = some (C, tb')) (hwf : FreeOK tb) :
    ∀ (m : ℕ) (C' : ContFX), tb'.get? m = some C' → ∃ C'' : ContFX, tb.get? m = some C'' := by
  intro m C' hC'
  obtain ⟨-, hrm, hframe, -⟩ := remove?_live hwf ht
  by_cases hm : m = N
  · subst hm
    rw [hrm] at hC'
    cases hC'
  · exact ⟨C', (hframe m hm) ▸ hC'⟩


/-- After `take`, the table entry is dead. -/
theorem dead_after_take {s : Store (FXCode (CH H))} {tb tb' : Table ContFX}
    {ts : List (Option (ThreadV (CH H)))} {N : ℕ} {C : ContFX}
    (ht : tb.remove? N = some (C, tb')) (hwf : FreeOK tb) : ¬ Live ⟨⟨s, tb'⟩, ts⟩ (.tab N) := by
  rintro ⟨C', hC'⟩
  obtain ⟨-, hrm, -, -⟩ := remove?_live hwf ht
  change tb'.get? N = some C' at hC'
  rw [hrm] at hC'
  cases hC'

theorem cbTake_back {s : Store (FXCode (CH H))} {tb tb' : Table ContFX}
    {ts : List (Option (ThreadV (CH H)))} {i N : ℕ} {K : KStore} {f : Frame}
    {code code' : List AdminFX} {C : ContFX} (hi : ts[i]? = some (some (.fx K f code)))
    (ht : tb.remove? N = some (C, tb')) (hwf : FreeOK tb) :
    ∀ l, Live ⟨⟨s, tb'⟩, ts.set i (some (.fx (K ++ [some C]) f code'))⟩ l →
      l ≠ .store i K.length → Live ⟨⟨s, tb⟩, ts⟩ l := by
  intro l hl hne
  cases l with
  | store i' j =>
    rcases live_store_set (s := ⟨s, tb⟩) hi hl with ⟨rfl, C', hC'⟩ | ⟨-, h⟩
    · have hj : j ≠ K.length := fun hj => hne (by rw [hj])
      exact ⟨_, hi, C', live_of_append hC' hj⟩
    · exact h
  | tab m =>
    obtain ⟨C', hC'⟩ := hl
    exact tab_back_of_remove ht hwf m C' hC'

theorem inv_cbTake {s : Store (FXCode (CH H))} {tb tb' : Table ContFX}
    {ts : List (Option (ThreadV (CH H)))} {g : Ghost} (hI : GInv ⟨⟨s, tb⟩, ts⟩ g) {i N : ℕ}
    {K : KStore} {f : Frame} {code code' : List AdminFX} {C : ContFX}
    (hi : ts[i]? = some (some (.fx K f code))) (ht : tb.remove? N = some (C, tb')) :
    GInv ⟨⟨s, tb'⟩, ts.set i (some (.fx (K ++ [some C]) f code'))⟩
      (g.move (.tab N) (.store i K.length)) := by
  obtain ⟨hold, -, -, hwf⟩ := remove?_live hI.wf ht
  exact inv_move hI hwf ⟨C, hold⟩ (dead_after_take ht hI.wf) (cbTake_back hi ht hI.wf)

/-! ## The other steps -/

theorem set_none_ne {K : KStore} {k : ℕ} {C : ContFX} (hk : K[k]? = some (some C)) :
    K.set k none ≠ K := by
  intro h
  have h1 : (K.set k none)[k]? = K[k]? := by rw [h]
  rw [List.getElem?_set_self', hk] at h1
  simp at h1

theorem append_ne (K : KStore) (x : Option ContFX) : K ++ [x] ≠ K := by
  intro h
  have h1 := congrArg List.length h
  simp at h1

theorem inv_cbOther {p : Pool H} {g : Ghost} (hI : GInv p g) {i : ℕ} {t t' : ThreadV (CH H)}
    {s' : EStore H} {ev : Option (Table.Event ContFX)} (hi : p.ts[i]? = some (some t))
    (hb : BStep (p.s, t) (s', t') ev) (hK : threadConts t' = threadConts t) :
    GInv ⟨s', p.ts.set i (some t')⟩ g := by
  obtain ⟨ps, pts⟩ := p
  change BStep (ps, t) (s', t') ev at hb
  have hKb : ∀ (j : ℕ) (C : ContFX), (threadConts t')[j]? = some (some C) →
      ∃ C' : ContFX, (threadConts t)[j]? = some (some C') := fun j C hC => ⟨C, hK ▸ hC⟩
  have hkeep : s'.tab = ps.tab → GInv ⟨s', pts.set i (some t')⟩ g := fun ht =>
    inv_mono hI (ht ▸ hI.wf) (live_set_mono (s := ps) hi hKb fun _ C hC => ⟨C, ht ▸ hC⟩)
  cases hb with
  | new _ _ hk _ => exact absurd hK (set_none_ne hk)
  | take => exact absurd hK (append_ne _ _)
  | drop _ _ ht =>
    exact inv_mono hI (remove?_live hI.wf ht).2.2.2
      (live_set_mono (s := ⟨_, _⟩) hi hKb (tab_back_of_remove ht hI.wf))
  | newUsed => exact hkeep rfl
  | newFull => exact hkeep rfl
  | dead => exact hkeep rfl

theorem inv_spawn {p : Pool H} {g : Ghost} (hI : GInv p g) (a : ℕ)
    (args : List Silmaril.Wasm.Component.Engine.FlatValue) :
    GInv ⟨p.s, p.ts ++ [some (.core (SingleThreaded.Thread.invokeFlat a args))]⟩ g := by
  refine inv_mono hI hI.wf fun l hl => ?_
  cases l with
  | store i j =>
    obtain ⟨u, hu, C, hC⟩ := hl
    rcases Nat.lt_or_ge i p.ts.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hu
      exact ⟨u, hu, C, hC⟩
    · rw [List.getElem?_append_right hge, List.getElem?_singleton] at hu
      split at hu
      · cases hu
        simp [threadConts] at hC
      · cases hu
  | tab n => exact hl

theorem inv_resume {p : Pool H} {g : Ghost} (hI : GInv p g) {i : ℕ} {t : ThreadV (CH H)}
    (res : Silmaril.Wasm.Component.Engine.CallResult) (hi : p.ts[i]? = some (some t)) :
    GInv ⟨p.s, p.ts.set i (some (resumeV p.s.core t res))⟩ g := by
  have hc : threadConts (resumeV p.s.core t res) = threadConts t := resumeV_conts p.s.core t res
  exact inv_mono hI hI.wf (live_set_mono (s := p.s) hi (fun j C hC => ⟨C, hc ▸ hC⟩)
    fun _ C hC => ⟨C, hC⟩)

theorem inv_env {p : Pool H} {g : Ghost} (hI : GInv p g) {s' : EStore H}
    (hs : s'.tab = p.s.tab) : GInv ⟨s', p.ts⟩ g := by
  refine inv_mono hI (hs ▸ hI.wf) fun l hl => ?_
  cases l with
  | store i j => exact hl
  | tab n =>
    obtain ⟨C, hC⟩ := hl
    exact ⟨C, hs ▸ hC⟩

theorem inv_finish {p : Pool H} {g : Ghost} (hI : GInv p g) (i : ℕ) :
    GInv ⟨p.s, p.ts.set i none⟩ g := by
  refine inv_mono hI hI.wf fun l hl => ?_
  cases l with
  | store i' j =>
    obtain ⟨u, hu, C, hC⟩ := hl
    exact ⟨u, (slot_none hu).2, C, hC⟩
  | tab n => exact hl

/-! ## Every step -/

/-- **Every step with its identity update keeps the invariant.** -/
theorem gstep_inv {x y : Pool H × Ghost} (h : GStep P x y) (hI : GInv x.1 x.2) :
    GInv y.1 y.2 := by
  cases h with
  | fx hi ht _ _ hk => exact inv_fx hI hi ht hk
  | cbNew hi _ _ hk ht => exact inv_cbNew hI hi hk ht
  | cbTake hi _ _ ht => exact inv_cbTake hI hi ht
  | cbOther hi hb hK => exact inv_cbOther hI hi hb hK
  | spawn a args => exact inv_spawn hI a args
  | resume res hi => exact inv_resume hI res hi
  | env hs => exact inv_env hI hs
  | finish i => exact inv_finish hI i

/-- Every pool step has its identity update. -/
theorem pstep_lift {p p' : Pool H} (h : PStep P p p') (g : Ghost) :
    ∃ g', GStep P (p, g) (p', g') := by
  cases h with
  | internal hi h =>
    rcases h with ⟨ht, hv, hn⟩ | ⟨ev, hb⟩
    · obtain ⟨evs, hk⟩ := internalV_kstep hv
      exact ⟨_, .fx hi ht hv hn hk⟩
    · obtain ⟨ps, pts⟩ := p
      change BStep (ps, _) _ ev at hb
      have hb' := hb
      cases hb with
      | new hc hb hk ht => exact ⟨_, .cbNew hi hc hb hk ht⟩
      | take hc hb ht => exact ⟨_, .cbTake hi hc hb ht⟩
      | drop => exact ⟨_, .cbOther hi hb' rfl⟩
      | newUsed => exact ⟨_, .cbOther hi hb' rfl⟩
      | newFull => exact ⟨_, .cbOther hi hb' rfl⟩
      | dead => exact ⟨_, .cbOther hi hb' rfl⟩
  | spawn a args => exact ⟨_, .spawn a args⟩
  | resume res hi => exact ⟨_, .resume res hi⟩
  | env hs => exact ⟨_, .env hs⟩
  | finish i => exact ⟨_, .finish i⟩

/-- Every step with identities is a pool step. -/
theorem gstep_proj {x y : Pool H × Ghost} (h : GStep P x y) : PStep P x.1 y.1 := by
  cases h with
  | fx hi ht hv hn _ => exact .internal hi (.inl ⟨ht, hv, hn⟩)
  | cbNew hi hc hb hk ht => exact .internal hi (.inr ⟨_, .new hc hb hk ht⟩)
  | cbTake hi hc hb ht => exact .internal hi (.inr ⟨_, .take hc hb ht⟩)
  | cbOther hi hb _ => exact .internal hi (.inr ⟨_, hb⟩)
  | spawn a args => exact .spawn a args
  | resume res hi => exact .resume res hi
  | env hs => exact .env hs
  | finish i => exact .finish i

end Silmaril.Wasm.Component.FXRes.ContPool
