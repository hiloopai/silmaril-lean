module

public import Silmaril.Raw.Elf.Link.Dyn.Proc.Progress

/-! # Runs of the process machine: what a `Must` theorem says about actual runs

A `Must` statement about `proc W` is vacuous at a **stuck** state (one with no outcome at all:
no `ok` successor and no `stop`): its step case holds there for every goal. The library's
contracts are relations, and a contract whose postcondition cannot be met (an unsatisfiable
`World.atMain`, a contract without an outcome) makes the machine stuck there. This file gives
the tools to rule that out:

* `must_run_or_stuck`: a `Must` yields a run that reaches the goal **or a stuck state** (no
  progress hypothesis);
* `must_run_of_reach`: a `Must` yields a run reaching the goal when every state reachable
  from the start has an outcome (local progress, along the runs only);
* `proc_progressG`: `proc_progressM` for worlds whose `atCall`/`atGate` are not trivial: every
  state has an outcome when `main` and the exit callbacks can be entered with the library's
  guarantees, the library's resumption at the gate (memory unchanged) meets `atGate`, and the
  named contracts have outcomes;
* `stuck_main` / `not_progress_main`: a world whose `atMain` forces a property `P` of `main`'s
  entry state that the registers of the `.main` job can contradict is stuck at the gate, so it
  has no global `Progress` (and Hello's route to a run, `proc_progress`, is closed for it).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res Must RunsInR)

section Generic

variable {σ : Type} {C : Silmaril.X86.RelIsa σ} {R Q : σ → Prop}

/-- **A `Must` yields a run to the goal or to a stuck state** (classical; no progress needed). -/
theorem must_run_or_stuck {s : σ} (hl : C.live s) (hm : Must C R Q s) :
    ∃ t, RunsInR C R s t ∧ (Q t ∨ ∀ r, ¬ C.step t r) := by
  induction hm with
  | done hq => exact ⟨_, .refl _, Or.inl hq⟩
  | @step s hr hs _ ih =>
    by_cases hp : ∃ r, C.step s r
    · obtain ⟨r, hr'⟩ := hp
      cases r with
      | stop => exact absurd hr' hs
      | ok t =>
        obtain ⟨u, hu, hq⟩ := ih t hr' (C.live_step hl hr')
        exact ⟨u, .step hr hr' hu, hq⟩
    · exact ⟨s, .refl _, Or.inr fun r h => hp ⟨r, h⟩⟩

/-- `t` is reachable from `s` (by `ok` steps). -/
inductive Reach (C : Silmaril.X86.RelIsa σ) : σ → σ → Prop
  | refl (s : σ) : Reach C s s
  | step {s s' t : σ} : C.step s (.ok s') → Reach C s' t → Reach C s t

theorem Reach.trans' {s t u : σ} (h : Reach C s t) (h' : C.step t (.ok u)) : Reach C s u := by
  induction h with
  | refl => exact .step h' (.refl _)
  | step hs _ ih => exact .step hs (ih h')

/-- **Local progress**: a `Must` yields a run reaching the goal when every state reachable from
the start has an outcome. -/
theorem must_run_of_reach {s : σ} (hl : C.live s) (hm : Must C R Q s)
    (hp : ∀ t, Reach C s t → ∃ r, C.step t r) : ∃ t, RunsInR C R s t ∧ Q t := by
  suffices H : ∀ u, Reach C s u → C.live u → Must C R Q u → ∃ t, RunsInR C R u t ∧ Q t from
    H s (.refl _) hl hm
  intro u hu hlu hmu
  induction hmu with
  | done hq => exact ⟨_, .refl _, hq⟩
  | @step v hr hs _ ih =>
    obtain ⟨r, hr'⟩ := hp v hu
    cases r with
    | stop => exact absurd hr' hs
    | ok t =>
      obtain ⟨w, hw, hq⟩ := ih t hr' (hu.trans' hr') (C.live_step hlu hr')
      exact ⟨w, .step hr hr' hw, hq⟩

end Generic

/-- **Every contract can be met, so the machine always has an outcome** (`proc_progressM` for
any `atCall`/`atGate`): `main` and the exit callbacks can be entered with the library's
guarantees (`hM`, `hK`, the latter also meeting `atGate`), and the library resuming at the gate
with its memory unchanged meets `atGate` (`hG`). -/
theorem proc_progressG (W : World) (hW : W.base.toNat + W.size ≤ 2 ^ 62)
    (hA : ∀ a, W.args a ∨ W.tls a → a < 2 ^ 62)
    (hslots : ∀ res slots, W.lazy = some (res, slots) → slots.length ≤ 2 ^ 64)
    (hN : ∀ n s, ∃ r, W.named n s r)
    (hM : ∀ s f a1 a2 a3 g, ∃ t, Enters W s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = g ∧ W.atMain t)
    (hK : ∀ s f g, ∃ t, Enters W s t f ∧ t.g = g ∧ W.atCall t ∧ W.atGate s t)
    (hG : ∀ s g, W.atGate s (gateState W s g))
    (hP : ∀ s, ∃ p, W.pending s p := by exact fun _ => ⟨[], rfl⟩) :
    Silmaril.X86.RelIsa.Progress (proc W) := by
  intro s _
  simp only [proc, step]
  cases hd : s.g.done with
  | some _ => exact ⟨.stop, rfl⟩
  | none =>
    simp only
    by_cases hin : W.InImage s.m.core.rip.toNat
    · simp only [hin, ↓reduceIte]
      cases Silmaril.X86.Open9.step s.m with
      | some m' => exact ⟨_, rfl⟩
      | none => exact ⟨.stop, rfl⟩
    · simp only [hin, ↓reduceIte]
      have hC : ∀ {pre : Prop} {post : PState → Prop}, (pre → ∃ t, post t) → ∃ r, Contract pre post r := by
        intro pre post h
        by_cases hp : pre
        · obtain ⟨t, ht⟩ := h hp; exact ⟨.ok t, fun _ => ⟨t, rfl, ht⟩⟩
        · exact ⟨.stop, fun h => absurd h hp⟩
      have hfn : ∀ f, ∃ r, fnStep W f s r := by
        intro f
        cases f with
        | puts =>
          exact hC fun ⟨_, str, hstr⟩ => ⟨retState s 0 { s.g with out := s.g.out ++ str ++ [10] },
            retState_returns W s 0 _, str, hstr, rfl, rfl, hd, ⟨rfl, rfl⟩,
            Or.inl ⟨rfl, by simp [retState, low32]⟩⟩
        | libcStartMain => exact hC fun _ => ⟨gateState W s _, gateState_at W s _, rfl⟩
        | cxaFinalize => exact hC fun _ => ⟨retState s 0 s.g, retState_returns W s 0 _, rfl, rfl⟩
        | exit => exact hC fun _ => ⟨gateState W s _, gateState_at W s _, rfl⟩
        | named n => exact hN n s
      have hfns : ∃ r, (match W.fns.find? (·.1 == s.m.core.rip) with
          | some (_, f) => fnStep W f s r
          | none => r = .stop) := by
        cases W.fns.find? (·.1 == s.m.core.rip) with
        | none => exact ⟨.stop, rfl⟩
        | some p => exact hfn p.2
      unfold extStep
      by_cases hg : s.m.core.rip = W.gate
      · simp only [hg, ↓reduceIte]
        unfold gateStep
        cases hj : s.g.jobs with
        | nil => exact ⟨.stop, trivial⟩
        | cons j js =>
          cases j with
          | call f a1 a2 a3 =>
            exact hC fun _ => exists_enters W hW hA s f a1 a2 a3 _
          | call0 f => exact hC fun _ =>
              (hK s f { s.g with jobs := js }).elim fun t h => ⟨t, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
          | main f a1 a2 a3 => exact hC fun _ => hM s f a1 a2 a3 _
          | exitRax => exact hC fun _ =>
              (hP s).elim fun p hp => ⟨gateState W s _, p, hp, gateState_at W s _, rfl, hG _ _⟩
          | exit st => exact hC fun _ => ⟨gateState W s _, gateState_at W s _, rfl, hG _ _⟩
          | halt st => exact hC fun _ => ⟨gateState W s { s.g with jobs := [], done := some (st.toNat % 256, s.g.out) },
              s.g.out, List.prefix_refl _, fun _ => rfl, rfl⟩
      · simp only [hg, ↓reduceIte]
        cases hl : W.lazy with
        | none => exact hfns
        | some p =>
          obtain ⟨res, slots⟩ := p
          simp only
          by_cases hr : s.m.core.rip = res
          · simp only [hr, ↓reduceIte]
            have hlen := hslots res slots hl
            unfold resolveStep
            cases hv : Silmaril.X86.Ext.loadN s.m.memory (s.m.core.read .rsp + 8#64) 8 with
            | none => exact ⟨.stop, fun j hj => by cases hj⟩
            | some v =>
              have huniq : ∀ j, BitVec.ofNat 64 j = v → j < slots.length → j = v.toNat := by
                intro j hj hjl
                rw [← hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              by_cases hj0 : v.toNat < slots.length
              · obtain ⟨r, hr'⟩ := hC (pre := SlotRW W slots[v.toNat] s) (post := ResPost W slots[v.toNat] s)
                  (fun hpre => exists_resolved W s _ hpre)
                refine ⟨r, fun j hj e he => ?_⟩
                have hjl : j < slots.length := by
                  by_contra hc; rw [List.getElem?_eq_none (by omega)] at he; cases he
                have := huniq j (Option.some.inj hj).symm hjl
                subst this
                rw [List.getElem?_eq_getElem hj0, Option.some.injEq] at he
                subst he
                exact hr'
              · refine ⟨.stop, fun j hj e he => ?_⟩
                have hjl : j < slots.length := by
                  by_contra hc; rw [List.getElem?_eq_none (by omega)] at he; cases he
                exact absurd (huniq j (Option.some.inj hj).symm hjl ▸ hjl) hj0
          · simp only [hr, ↓reduceIte]
            exact hfns

/-- **A world whose `atMain` forces `P` is stuck at a `.main` job whose registers refute `P`**:
the state `s` at the gate (outside the image) with the next job `.main f a1 a2 a3` has no outcome
when no callback entry with those registers satisfies `P`. -/
theorem stuck_main {W : World} {P : PState → Prop} (hP : ∀ t, W.atMain t → P t) {s : PState}
    (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat) (hrip : s.m.core.rip = W.gate)
    {f a1 a2 a3 : Word} {js : List Job} (hj : s.g.jobs = .main f a1 a2 a3 :: js)
    (hno : ∀ t, t.m.core.read .rdi = a1 → t.m.core.read .rsi = a2 → t.m.core.read .rdx = a3 → ¬ P t) :
    ∀ r, ¬ (proc W).step s r := by
  intro r h
  simp only [proc, step, hd, hout, ↓reduceIte] at h
  rw [extStep_gate hrip] at h
  simp only [gateStep, hj] at h
  obtain ⟨t, -, -, h2, h3, h4, -, h6⟩ := h trivial
  exact hno t h2 h3 h4 (hP t h6)

/-- The state at the gate about to call `main (a1, a2, a3)`. -/
def mainGateState (W : World) (f a1 a2 a3 : Word) : PState :=
  ⟨⟨⟨fun _ => 0, W.gate, ⟨none, none, none, none, none, none⟩, 0⟩, ⟨[], ∅⟩⟩,
    { jobs := [.main f a1 a2 a3], out := [], atexit := [], done := none }⟩

/-- **No global progress** for a world whose `atMain` forces a property that some `.main` job's
registers refute (with the gate outside the image). -/
theorem not_progress_main {W : World} {P : PState → Prop} (hP : ∀ t, W.atMain t → P t)
    (hout : ¬ W.InImage W.gate.toNat) {f a1 a2 a3 : Word}
    (hno : ∀ t, t.m.core.read .rdi = a1 → t.m.core.read .rsi = a2 → t.m.core.read .rdx = a3 → ¬ P t) :
    ¬ Silmaril.X86.RelIsa.Progress (proc W) := by
  intro hp
  obtain ⟨r, hr⟩ := hp (mainGateState W f a1 a2 a3) trivial
  exact stuck_main hP (s := mainGateState W f a1 a2 a3) rfl hout rfl rfl hno r hr

end Silmaril.Elf.Link.Dyn.Proc
