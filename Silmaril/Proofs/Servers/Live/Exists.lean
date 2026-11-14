module

public import Silmaril.Servers.Live.Defs

/-!
# Proofs: fair runs exist

For a total machine `M` and a stream of requests `reqs` on the connection `c`, the run `run`
receives the `k`-th request with identity `⟨c, k⟩` at instant `3 k`, runs the handler on it at
`3 k + 1` (with an answer the machine allows, chosen) and sends the response at `3 k + 2`. It is
a run of the pipelining server, and no handler run or response stays enabled for two instants
in a row, so it is weakly fair, as a run of the pipelining server and as a run of the
atomic-handler server.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Live

open Silmaril.Servers

variable {A : Sig} {σ : Type} {M : Machine A σ}

section Run

variable (hM : M.Total) (q₀ : σ) (c : Nat) (reqs : Nat → A.Req)

/-- The machine state after `k` requests. -/
noncomputable def chain : Nat → σ
  | 0 => q₀
  | k + 1 => Classical.choose (Classical.choose_spec (hM (chain k) (reqs k)))

/-- The answer to the `k`-th request. -/
noncomputable def answer (k : Nat) : A.Resp := Classical.choose (hM (chain hM q₀ reqs k) (reqs k))

theorem chain_step (k : Nat) :
    M (chain hM q₀ reqs k) (reqs k) (answer hM q₀ reqs k) (chain hM q₀ reqs (k + 1)) :=
  Classical.choose_spec (Classical.choose_spec (hM (chain hM q₀ reqs k) (reqs k)))

/-- The identity of the `k`-th request. -/
def idx (k : Nat) : ReqId := ⟨c, k⟩

/-- The requests received before the `k`-th. -/
def reqOf (k : Nat) : ReqId → Option A.Req :=
  fun j => if j.conn = c ∧ j.seq < k then some (reqs j.seq) else none

/-- The monitor before the `k`-th request. -/
def mon0 (k : Nat) : LMon A := ⟨reqOf c reqs k, fun _ => none, fun _ => none⟩

/-- The monitor once the `k`-th request is received. -/
def mon1 (k : Nat) : LMon A :=
  ⟨Function.update (reqOf c reqs k) (idx c k) (some (reqs k)),
    Function.update (fun _ => none) (idx c k) (some (reqs k)), fun _ => none⟩

/-- The monitor once the handler has run on the `k`-th request. -/
noncomputable def mon2 (k : Nat) : LMon A :=
  ⟨Function.update (reqOf c reqs k) (idx c k) (some (reqs k)),
    Function.update (Function.update (fun _ => none) (idx c k) (some (reqs k))) (idx c k) none,
    Function.update (fun _ => none) (idx c k) (some (answer hM q₀ reqs k))⟩

/-- The state at each instant. -/
noncomputable def st (n : Nat) : σ × LMon A :=
  if n % 3 = 0 then (chain hM q₀ reqs (n / 3), mon0 c reqs (n / 3))
  else if n % 3 = 1 then (chain hM q₀ reqs (n / 3), mon1 c reqs (n / 3))
  else (chain hM q₀ reqs (n / 3 + 1), mon2 hM q₀ c reqs (n / 3))

/-- The step at each instant. -/
noncomputable def ev (n : Nat) : Option (LEvent A) :=
  if n % 3 = 0 then some (.ev (.recv (idx c (n / 3)) (reqs (n / 3))))
  else if n % 3 = 1 then some (.lin (idx c (n / 3)) (reqs (n / 3)) (answer hM q₀ reqs (n / 3)))
  else some (.ev (.send (idx c (n / 3)) (answer hM q₀ reqs (n / 3))))

theorem reqOf_succ (k : Nat) :
    Function.update (reqOf c reqs k) (idx c k) (some (reqs k)) = reqOf c reqs (k + 1) := by
  funext j
  obtain ⟨jc, js⟩ := j
  by_cases h : jc = c ∧ js = k
  · obtain ⟨rfl, rfl⟩ := h
    simp [reqOf, idx]
  · have hne : (⟨jc, js⟩ : ReqId) ≠ idx c k := by
      intro e; simp only [idx, ReqId.mk.injEq] at e; exact h e
    rw [Function.update_of_ne hne]
    simp only [reqOf]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem upd_none {α : Type} (i : ReqId) (x : Option α) :
    Function.update (Function.update (fun _ => (none : Option α)) i x) i none = fun _ => none := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem phases (n : Nat) : ∃ k, n = 3 * k ∨ n = 3 * k + 1 ∨ n = 3 * k + 2 := ⟨n / 3, by omega⟩

theorem st_0 (k : Nat) : st hM q₀ c reqs (3 * k) = (chain hM q₀ reqs k, mon0 c reqs k) := by
  simp [st, show 3 * k % 3 = 0 by omega, show 3 * k / 3 = k by omega]

theorem st_1 (k : Nat) : st hM q₀ c reqs (3 * k + 1) = (chain hM q₀ reqs k, mon1 c reqs k) := by
  simp [st, show (3 * k + 1) % 3 = 1 by omega, show (3 * k + 1) / 3 = k by omega]

theorem st_2 (k : Nat) :
    st hM q₀ c reqs (3 * k + 2) = (chain hM q₀ reqs (k + 1), mon2 hM q₀ c reqs k) := by
  simp [st, show (3 * k + 2) % 3 = 2 by omega, show (3 * k + 2) / 3 = k by omega]

theorem ev_0 (k : Nat) : ev hM q₀ c reqs (3 * k) = some (.ev (.recv (idx c k) (reqs k))) := by
  simp [ev, show 3 * k % 3 = 0 by omega, show 3 * k / 3 = k by omega]

theorem ev_1 (k : Nat) :
    ev hM q₀ c reqs (3 * k + 1) = some (.lin (idx c k) (reqs k) (answer hM q₀ reqs k)) := by
  simp [ev, show (3 * k + 1) % 3 = 1 by omega, show (3 * k + 1) / 3 = k by omega]

theorem ev_2 (k : Nat) :
    ev hM q₀ c reqs (3 * k + 2) = some (.ev (.send (idx c k) (answer hM q₀ reqs k))) := by
  simp [ev, show (3 * k + 2) % 3 = 2 by omega, show (3 * k + 2) / 3 = k by omega]

theorem pipeStep_at (n : Nat) :
    M.pipeStep (st hM q₀ c reqs n) ((ev hM q₀ c reqs n).get (by
      obtain ⟨k, rfl | rfl | rfl⟩ := phases n
      · rw [ev_0]; rfl
      · rw [ev_1]; rfl
      · rw [ev_2]; rfl)) (st hM q₀ c reqs (n + 1)) := by
  obtain ⟨k, rfl | rfl | rfl⟩ := phases n
  · simp only [ev_0, Option.get_some, st_0, st_1]
    refine ⟨⟨rfl, LMon.Step.recv (by simp [mon0, reqOf, idx])⟩, fun i s h => by cases h⟩
  · simp only [ev_1, Option.get_some, st_1, show 3 * k + 1 + 1 = 3 * k + 2 by omega, st_2]
    exact ⟨⟨chain_step hM q₀ reqs k, LMon.Step.lin (by simp [mon1])⟩, fun i s h => by cases h⟩
  · simp only [ev_2, Option.get_some, st_2, show 3 * k + 2 + 1 = 3 * (k + 1) by omega, st_0]
    have heq : (⟨(mon2 hM q₀ c reqs k).req, (mon2 hM q₀ c reqs k).pending,
        Function.update (mon2 hM q₀ c reqs k).ready (idx c k) none⟩ : LMon A) =
        mon0 c reqs (k + 1) := by
      simp only [mon2, mon0, reqOf_succ, upd_none]
    refine ⟨⟨rfl, heq ▸ LMon.Step.send (by simp [mon2])⟩, ?_⟩
    rintro i s h j hjc hjs -
    cases h
    have hne : j ≠ idx c k := by rintro rfl; simp [idx] at hjs
    simp [mon2, Function.update_of_ne hne]

/-- **The run.** -/
noncomputable def run : M.PRun q₀ where
  st := st hM q₀ c reqs
  ev := ev hM q₀ c reqs
  init := by
    rw [show (0 : Nat) = 3 * 0 from rfl, st_0]
    simp only [chain, mon0, LMon.init, Prod.mk.injEq, LMon.mk.injEq, true_and, and_true]
    funext j; simp [reqOf]
  step n := .inr ⟨_, Option.some_get _ |>.symm, pipeStep_at hM q₀ c reqs n⟩

theorem pending_phase {n : Nat} {j : ReqId} (h : (st hM q₀ c reqs n).2.pending j ≠ none) :
    n % 3 = 1 := by
  obtain ⟨k, rfl | rfl | rfl⟩ := phases n
  · rw [st_0] at h; exact absurd rfl h
  · omega
  · rw [st_2] at h; simp [mon2] at h

theorem ready_phase {n : Nat} {j : ReqId} (h : (st hM q₀ c reqs n).2.ready j ≠ none) :
    n % 3 = 2 := by
  obtain ⟨k, rfl | rfl | rfl⟩ := phases n
  · rw [st_0] at h; exact absurd rfl h
  · rw [st_1] at h; exact absurd rfl h
  · omega

theorem run_fair : (run hM q₀ c reqs).Fair := by
  refine ⟨fun i n h => ?_, fun i n h => ?_⟩
  · exfalso
    obtain ⟨_, h₁, _⟩ := h n le_rfl
    obtain ⟨_, h₂, _⟩ := h (n + 1) (by omega)
    have a := pending_phase hM q₀ c reqs (n := n) (j := i) fun e =>
      Option.some_ne_none _ (h₁.symm.trans e)
    have b := pending_phase hM q₀ c reqs (n := n + 1) (j := i) fun e =>
      Option.some_ne_none _ (h₂.symm.trans e)
    omega
  · exfalso
    have a := ready_phase hM q₀ c reqs (h n le_rfl).1
    have b := ready_phase hM q₀ c reqs (h (n + 1) (by omega)).1
    omega

theorem run_fair_irun : (run hM q₀ c reqs).toIRun.Fair := by
  refine ⟨(run_fair hM q₀ c reqs).1, fun i n h => ?_⟩
  exfalso
  have a := ready_phase hM q₀ c reqs (h n le_rfl)
  have b := ready_phase hM q₀ c reqs (h (n + 1) (by omega))
  omega

theorem run_obs_recv (k : Nat) :
    (run hM q₀ c reqs).obs (3 * k) = some (.recv ⟨c, k⟩ (reqs k)) := by
  simp only [Machine.PRun.obs, Machine.IRun.obs]
  rw [show (run hM q₀ c reqs).toIRun.ev (3 * k) = ev hM q₀ c reqs (3 * k) from rfl, ev_0]
  rfl

theorem run_obs_send (k : Nat) :
    (run hM q₀ c reqs).obs (3 * k + 2) = some (.send ⟨c, k⟩ (answer hM q₀ reqs k)) := by
  simp only [Machine.PRun.obs, Machine.IRun.obs]
  rw [show (run hM q₀ c reqs).toIRun.ev (3 * k + 2) = ev hM q₀ c reqs (3 * k + 2) from rfl, ev_2]
  rfl

end Run

end Silmaril.Proofs.Servers.Live
