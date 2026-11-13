module

public import Silmaril.Wasm.FX.Asyncify.Tool.CoreSys.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Init

/-!
# Rounds of the bounded target system on Core 3.0

`obs_of_runN`: when the bounded target system (`tgtStepB`) stops with observation `o` from a
state related to a Core configuration reached from the export call, that call has observation
`o` on Core (`CoreObs`). Within a round, each machine step is matched by `crel_step`; at the end
of a round, the next round starts with `crel_init` from every store that realizes the host's
update.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSys

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

variable {H σ : Type} {Pf : Profile} {host : HostSemantics H} {cap : Nat} {E : Env}
  {Hh : Host σ} {mi : ModuleInst}

/-- An export call of defined function `e` with the right number of arguments. -/
def EntryOk (E : Env) (e : Nat) (args : List W) : Prop :=
  E.imps.length ≤ e ∧ e < 2 ^ 32 ∧ ∃ fd, E.fns[e - E.imps.length]? = some fd ∧
    args.length = fd.nparams

/-- The requests and answers of every import fit in `cap` bytes. -/
def ReqFits (cap : Nat) (E : Env) : Prop :=
  4 ≤ cap ∧ ∀ n m, (n, m) ∈ E.imps → 4 * (n + 1) ≤ cap ∧ 4 * m ≤ cap

theorem runN_zero_ne {X : Type} {step : X → SRes X σ} {x : X} {o : Obs σ} :
    runN step 0 x ≠ .stop o := fun h => by cases h

theorem runN_next {X : Type} {step : X → SRes X σ} {x x' : X} {k : Nat} (h : step x = .next x') :
    runN step (k + 1) x = runN step k x' := by
  simp only [runN, h]

theorem runN_stop {X : Type} {step : X → SRes X σ} {x : X} {k : Nat} {o o' : Obs σ}
    (h : step x = .stop o') (h' : runN step (k + 1) x = .stop o) : o = o' := by
  simp only [runN, h, SRes.stop.injEq] at h'
  exact h'.symm

theorem tgtStepB_next {t : TSt σ} {c' : Cfg} (h : stepB cap E t.cfg = .next c') :
    tgtStepB cap E Hh t = .next { t with cfg := c' } := by
  simp only [tgtStepB, h]

theorem tgtStepB_trap {t : TSt σ} (h : stepB cap E t.cfg = .trap) :
    tgtStepB cap E Hh t = .stop (.trap t.host) := by
  simp only [tgtStepB, h]

theorem tgtStepB_done {t : TSt σ} {vs : List W} {c' : Cfg} (h : stepB cap E t.cfg = .done vs c')
    (h1 : ¬ c'.globals[0]? = some 1) : tgtStepB cap E Hh t = .stop (.done vs t.host) := by
  simp only [tgtStepB, h, h1, ite_false]

theorem tgtStepB_bad {t : TSt σ} {vs : List W} {c' : Cfg} (h : stepB cap E t.cfg = .done vs c')
    (h1 : c'.globals[0]? = some 1) (hi : E.imps[(c'.mem 0).toNat]? = none) :
    tgtStepB cap E Hh t = .stop (.trap t.host) := by
  simp only [tgtStepB, h, h1, ite_true, hi]

/-- The next round of the protocol. -/
def nextRound (t : TSt σ) (fd : FnDef) (c' : Cfg) (m : Nat) (r : σ × List W) : TSt σ :=
  ⟨⟨[entry t.fid fd t.args], c'.globals.set 0 2, writeWords c'.mem 0 (fit m r.2)⟩, r.1, t.fid,
    t.args⟩

theorem tgtStepB_round {t : TSt σ} {vs : List W} {c' : Cfg} {fd : FnDef} {n m : Nat}
    (h : stepB cap E t.cfg = .done vs c') (h1 : c'.globals[0]? = some 1)
    (hi : E.imps[(c'.mem 0).toNat]? = some (n, m))
    (hfd : E.fns[t.fid - E.imps.length]? = some fd) :
    tgtStepB cap E Hh t = .next (nextRound t fd c' m (hostAns Hh t.host n c'.mem)) := by
  simp only [tgtStepB, h, h1, ite_true, hi, hfd]
  rfl

theorem ginv_state {gs : List W} (h : GInv gs) : GInv (gs.set 0 2) :=
  ginv_set h fun h0 => absurd h0 (by decide)

/-- The next round starts in the relation, from every store of the host's update. -/
theorem next_round {t : TSt σ} {c' : Cfg} {fd : FnDef} {m : Nat} {r : σ × List W}
    {s'' : Store H} (hE : EnvOk E) (hEn : EntryOk E t.fid t.args)
    (hfd : E.fns[t.fid - E.imps.length]? = some fd) (hG : GInv c'.globals)
    (hU : HostUpd cap E mi s'' c'.globals c'.mem (fit m r.2)) :
    ∃ Z, Execution.Core.Steps Pf host ⟨s'', ⟨[], mi⟩, callA t.fid t.args⟩ ⟨s'', ⟨[], mi⟩, Z⟩ ∧
      CRel cap E mi (nextRound t fd c' m r).cfg s'' Z := by
  obtain ⟨he, he32, fd', hfd', ha⟩ := hEn
  have hfe : fd' = fd := Option.some.inj (hfd'.symm.trans hfd)
  exact ⟨_, crel_init hE hU.1 he he32 hfd (hfe ▸ ha) hU.2.1 hU.2.2 (ginv_state hG)⟩

/-- **A stop of the bounded target system is an observation of the Core protocol.** -/
theorem obs_of_runN (hE : EnvOk E) (hF : ReqFits cap E) :
    ∀ (k : Nat) (t : TSt σ) (s₀ s : Store H) (Z : List Admin) (o : Obs σ),
      Execution.Core.Steps Pf host ⟨s₀, ⟨[], mi⟩, callA t.fid t.args⟩ ⟨s, ⟨[], mi⟩, Z⟩ →
      CRel cap E mi t.cfg s Z → EntryOk E t.fid t.args →
      runN (tgtStepB cap E Hh) k t = .stop o →
      CoreObs Pf host cap E Hh mi t.fid t.args s₀ t.host o
  | 0, _, _, _, _, _, _, _, _, h => absurd h runN_zero_ne
  | k + 1, t, s₀, s, Z, o, hC, hR, hEn, h => by
    have hm : CMatch Pf host cap E mi s Z (stepB cap E t.cfg) := crel_step hR
    cases hs : stepB cap E t.cfg with
    | next c' =>
      obtain ⟨s', Z', h1, hR'⟩ : CMatch Pf host cap E mi s Z (.next c') := hs ▸ hm
      exact obs_of_runN hE hF k { t with cfg := c' } s₀ s' Z' o (hC.trans h1) hR' hEn
        ((runN_next (tgtStepB_next hs)).symm.trans h)
    | trap =>
      obtain ⟨C', h1, h2⟩ : CMatch Pf host cap E mi s Z .trap := hs ▸ hm
      exact runN_stop (tgtStepB_trap hs) h ▸ .trap (hC.trans h1) h2
    | ask f as c' => exact (hs ▸ hm : CMatch Pf host cap E mi s Z (.ask f as c')).elim
    | done vs c' =>
      obtain ⟨s', h1, -, hG, hM, hGI⟩ : CMatch Pf host cap E mi s Z (.done vs c') := hs ▸ hm
      by_cases h1s : c'.globals[0]? = some 1
      · cases hi : E.imps[(c'.mem 0).toNat]? with
        | none => exact runN_stop (tgtStepB_bad hs h1s hi) h ▸
            .badReq (hC.trans h1) hG hM h1s hF.1 hi
        | some p =>
          obtain ⟨fd, hfd, -⟩ := hEn.2.2
          have hb := hF.2 p.1 p.2 (List.mem_of_getElem? hi)
          refine .round (n := p.1) (m := p.2) (hC.trans h1) hG hM h1s hi hb.1 hb.2 fun s'' hU => ?_
          obtain ⟨Z'', h2, hR''⟩ := next_round (Pf := Pf) (host := host) hE hEn hfd hGI hU
          exact obs_of_runN hE hF k (nextRound t fd c' p.2 (hostAns Hh t.host p.1 c'.mem)) s''
            s'' Z'' o h2 hR'' hEn
            ((runN_next (tgtStepB_round hs h1s hi hfd)).symm.trans h)
      · exact runN_stop (tgtStepB_done hs h1s) h ▸ .done (hC.trans h1) hG h1s

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSys
