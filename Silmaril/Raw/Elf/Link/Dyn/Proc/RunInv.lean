module

public import Silmaril.Raw.Elf.Link.Dyn.Proc.Run

/-! # Runs from an invariant

`proc_progressP`: `proc_progressG` restricted to the states of a predicate `P` (the contracts,
`main` and the callbacks need outcomes only there). `must_run_of_inv`: a `Must` yields a run
reaching the goal when an invariant `I` holds at the start, every state of `I` has an outcome,
and `I` is kept by every `ok` step from a state of `I` that does not stop (a `Must` state never
stops, so a contract is called there only under its precondition).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res Must RunsInR)

theorem must_run_of_inv {σ : Type} {C : Silmaril.X86.RelIsa σ} {R Q : σ → Prop} (I : σ → Prop) {s : σ}
    (hl : C.live s) (hm : Must C R Q s) (hI : I s)
    (hp : ∀ t, I t → ∃ r, C.step t r)
    (hk : ∀ t u, I t → ¬ C.step t .stop → C.step t (.ok u) → I u) : ∃ t, RunsInR C R s t ∧ Q t := by
  induction hm with
  | done hq => exact ⟨_, .refl _, hq⟩
  | @step v hr hs _ ih =>
    obtain ⟨r, hr'⟩ := hp v hI
    cases r with
    | stop => exact absurd hr' hs
    | ok t =>
      obtain ⟨w, hw, hq⟩ := ih t hr' (C.live_step hl hr') (hk v t hI hs hr')
      exact ⟨w, .step hr hr' hw, hq⟩

theorem proc_progressP (W : World) (P : PState → Prop) (hW : W.base.toNat + W.size ≤ 2 ^ 62)
    (hA : ∀ a, W.args a ∨ W.tls a → a < 2 ^ 62)
    (hslots : ∀ res slots, W.lazy = some (res, slots) → slots.length ≤ 2 ^ 64)
    (hN : ∀ n s, P s → ∃ r, W.named n s r)
    (hM : ∀ s f a1 a2 a3 g, P s → ∃ t, Enters W s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = g ∧ W.atMain t)
    (hK : ∀ s f g, P s → ∃ t, Enters W s t f ∧ t.g = g ∧ W.atCall t ∧ W.atGate s t)
    (hG : ∀ s g, W.atGate s (gateState W s g))
    (hPd : ∀ s, ∃ p, W.pending s p := by exact fun _ => ⟨[], rfl⟩) :
    ∀ s, P s → ∃ r, (proc W).step s r := by
  intro s hP
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
        | named n => exact hN n s hP
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
              (hK s f { s.g with jobs := js } hP).elim fun t h => ⟨t, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
          | main f a1 a2 a3 => exact hC fun _ => hM s f a1 a2 a3 _ hP
          | exitRax => exact hC fun _ =>
              (hPd s).elim fun p hp => ⟨gateState W s _, p, hp, gateState_at W s _, rfl, hG _ _⟩
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


end Silmaril.Elf.Link.Dyn.Proc
