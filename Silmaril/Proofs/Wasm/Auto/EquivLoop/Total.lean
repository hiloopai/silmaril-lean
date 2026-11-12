module

public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Auto.EquivLoop.Defs
public import Silmaril.Wasm.Logic.Total.Thms
public import Mathlib.Order.WellFounded

/-!
# The loop congruence for total correctness

`CEquiv.loop` (`Silmaril.Wasm.Auto.Equiv`) gives the lockstep loop congruence for partial
correctness by Löb induction on the step index of `HWP`. Total correctness (`TWP`, the inductive
`TSafe`) has no index; here the induction is on the **accessibility of the left loop's runs**:

* `acc_of_tsafe`: a totally safe configuration has no infinite run, so it is accessible for the
  converse of the step relation (Mathlib's `not_acc_iff_exists_descending_chain`, which uses
  choice, against `TSafe.not_diverges`); `Acc.transGen` gives accessibility for runs of one or
  more steps;
* `tsafe_reach`: every exit a totally safe run reaches is reachable (the postcondition is
  strengthened by the run to the exit);
* `tsafe_and_hwp`: total and partial facts about one configuration combine;
* **`tsafe_loop_congr`**: in the loop's next iteration, the left loop configuration is reachable
  from the current one in at least one step, so the induction hypothesis applies to it;
* **`CEquiv.loopT`**: the congruence under `loop` in **both readings** (`CEquiv`), for bodies that
  are `CEquiv` and typed at their back edges (`KeepsBr0`).

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EquivLoop

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv Silmaril.Wasm.Auto.EquivLoop
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem acc_of_tsafe {Q : Post H} {c : Config H} (h : TSafe P host Q c) : Acc (StepBack P host) c := by
  by_contra hn
  obtain ⟨g, hg0, hg⟩ := not_acc_iff_exists_descending_chain.mp hn
  exact TSafe.not_diverges h ⟨g, hg0, fun n => hg n⟩

theorem transGen_of_steps {c c₁ d : Config H} (h₁ : Step P host c c₁) (hs : Steps P host c₁ d) :
    Relation.TransGen (StepBack P host) d c := by
  induction hs with
  | refl => exact .single h₁
  | tail _ hst ih => exact Relation.TransGen.head hst ih

theorem tsafe_reach {Q : Post H} {c : Config H} (h : TSafe P host Q c) :
    ∀ c₀, Steps P host c₀ c →
      TSafe P host (fun s f o => Q s f o ∧ ∃ code, Exits o code ∧ Steps P host c₀ ⟨s, f, code⟩) c := by
  induction h with
  | exit o he hq => exact fun c₀ hr => .exit o he ⟨hq, _, he, hr⟩
  | step hp _ ih => exact fun c₀ hr => .step hp fun c' hc => ih c' hc c₀ (hr.tail hc)

theorem tsafe_and_hwp {Q Q' : Post H} {c : Config H} (h : TSafe P host Q c) :
    HWP P host c.store c.frame c.code Q' → TSafe P host (fun s f o => Q s f o ∧ Q' s f o) c := by
  induction h with
  | exit o he hq => exact fun hw => .exit o he ⟨hq, wp_exit_post (m := .part) hw he⟩
  | @step c hp _ ih =>
    intro hw
    refine .step hp fun c' hc => ih c' hc ?_
    rcases c with ⟨s, f, code⟩
    rcases c' with ⟨s', f', code'⟩
    exact wp_step_inv (m := .part) hw hc

theorem steps_label {n : Nat} {cont : List Instr} {us : List Val} {c c' : Config H}
    (hs : Steps P host c c') :
    Steps P host ⟨c.store, c.frame, vals us ++ [.label n cont c.code]⟩
      ⟨c'.store, c'.frame, vals us ++ [.label n cont c'.code]⟩ := by
  induction hs with
  | refl => exact .refl
  | @tail b d _ hst ih =>
    rcases b with ⟨s₁, f₁, c₁⟩
    rcases d with ⟨s₂, f₂, c₂⟩
    exact ih.tail (label_ctxt (m := n) (cont := cont) (us := us) hst)

/-- The back edge of a loop body: a branch to the loop's label re-enters the loop. -/
theorem step_backEdge {s : Store H} {f : Frame} {us vs : List Val} {bt : BlockType} {a : List Instr}
    {x : LabelIdx} {rest : List Admin} (hx : x.toNat = 0) :
    Step P host ⟨s, f, vals us ++ [.label 0 [.loop bt a] (vals vs ++ .plain (.br x) :: rest)]⟩
      ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩ := by
  have h₁ := Sim.Step.vals_left (Step.brLabelZero (P := P) (host := host) (s := s) (f := f) (n := 0)
    (cont := [.loop bt a]) (vs' := vs) (vs := []) (l := x) (rest := rest) hx rfl) us
  simpa [expression] using h₁

theorem labelPostT_ne_br0 {n : Nat} {c₁ c₂ : List Instr} {us : List Val} {Q : Post H}
    {s : Store H} {f : Frame} {o : Outcome} (ho : ∀ vs, o ≠ .br 0 vs)
    (h : labelPostT P host n c₁ us Q s f o) : labelPostT P host n c₂ us Q s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact h
  · exact (ho vs rfl).elim
  all_goals exact h

/-- **The loop congruence for total correctness**, by induction on the accessibility of the
left loop's runs. -/
theorem tsafe_loop_congr {lt : List IntType} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : CEquiv lt [] a b) (hk : KeepsBr0 lt a) (c : Config H)
    (hacc : Acc (Relation.TransGen (StepBack P host)) c) :
    ∀ {s : Store H} {f : Frame} {us : List Val} {Q : Post H},
      c = ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩ → TypedFrame lt f → NoFuncTop us →
      TSafe P host Q c → TSafe P host Q ⟨s, f, vals us ++ [.plain (.loop bt b)]⟩ := by
  induction hacc with
  | intro c _ ih =>
  intro s f us Q hc hf hus hw
  subst hc
  obtain ⟨t₂, ht⟩ := hbt f.module
  have hstepL : Step P host ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩
      ⟨s, f, vals us ++ [.label 0 [.loop bt a] (expression a)]⟩ := loop_step ht
  have hlab : TSafe P host Q ⟨s, f, vals us ++ [.label 0 [.loop bt a] (expression a)]⟩ :=
    TSafe.step_inv hw hstepL
  have hbA : TWP P host s f (expression a) (labelPostT P host 0 [.loop bt a] us Q) :=
    twp_label_inv hus hlab
  have hbA₁ := tsafe_and_hwp (tsafe_reach hbA ⟨s, f, expression a⟩ .refl)
    (hk P host s f _ hf (TWP.hwp hbA))
  have hbA₂ : TWP P host s f (expression a) (labelPostT P host 0 [.loop bt b] us Q) := by
    refine TSafe.post_mono hbA₁ fun s' F o ho => ?_
    obtain ⟨⟨hq, code, he, hr⟩, -, hty⟩ := ho
    by_cases hb0 : ∃ vs, o = .br 0 vs
    · show labelPostT P host 0 [.loop bt b] us Q s' F o
      obtain ⟨vs, rfl⟩ := hb0
      obtain ⟨vs₁, vs₂, hvs, hn, hw'⟩ := hq
      have hv : vs₂ = [] := List.eq_nil_of_length_eq_zero hn
      subst hv
      obtain ⟨x, rest, hx, hcode⟩ := he
      have hreach : Relation.TransGen (StepBack P host) ⟨s', F, vals us ++ [.plain (.loop bt a)]⟩
          ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩ := by
        have h₂ := steps_label (n := 0) (cont := [.loop bt a]) (us := us) hr
        rw [hcode] at h₂
        exact transGen_of_steps hstepL (h₂.tail (step_backEdge hx))
      have hwL : TSafe P host Q ⟨s', F, vals us ++ [.plain (.loop bt a)]⟩ := by
        simpa [expression] using hw'
      have hR := ih _ hreach rfl (hty vs rfl) hus hwL
      exact ⟨vs₁, [], hvs, rfl, by simpa [expression] using hR⟩
    · exact labelPostT_ne_br0 (fun vs hvs => hb0 ⟨vs, hvs⟩) hq
  have hbB : TWP P host s f (expression b) (labelPostT P host 0 [.loop bt b] us Q) :=
    (h.body_iff (m := .total) hf).mp hbA₂
  have hlabB : TSafe P host Q ⟨s, f, vals us ++ [.label 0 [.loop bt b] (expression b)]⟩ := by
    simpa using TSafe.label (m := 0) (cont := [.loop bt b]) (us := us) (c := ⟨s, f, expression b⟩) hbB
  refine TSafe.head ⟨rfl, by simp, rfl⟩ ⟨us, [], _, by simp, .loop ht rfl⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := head_loop hh
  obtain ⟨rfl, rfl⟩ : t₁' = [] ∧ t₂' = t₂ := by simpa [ht] using hbt'.symm
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hn'
  subst hargs
  have hus' : us' = us := by simpa using hW.symm
  subst hus'
  simpa using hlabB

/-- **Loops in both readings** (no parameters): equivalent bodies, typed at their back edges,
give equivalent loops. -/
theorem CEquiv.loopT {lt st : List IntType} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : CEquiv lt [] a b) (hk : KeepsBr0 lt a) :
    CEquiv lt st [.loop bt a] [.loop bt b] := by
  intro m P H host s f rs us rest Q hf hrs hus
  cases m with
  | part => exact CEquiv.loop hbt h hk P host s f rs us rest Q hf hrs hus
  | total =>
    have hU := noFuncTop_append hus hrs
    have e : ∀ x : List Instr, cfgCode us rs [.loop bt x] rest =
        (vals (us ++ rs.reverse) ++ [.plain (.loop bt x)]) ++ rest := fun x => by
      simp [cfgCode, expression]
    rw [e, e]
    constructor
    · intro hw
      have h₁ := twp_seq_inv hw
      exact TWP.seq (tsafe_loop_congr hbt h hk _ (acc_of_tsafe h₁).transGen rfl hf hU h₁)
    · intro hw
      have h₁ := twp_seq_inv hw
      exact TWP.seq (tsafe_loop_congr hbt h.symm (hk.of_cequiv h) _ (acc_of_tsafe h₁).transGen
        rfl hf hU h₁)

end Silmaril.Proofs.Wasm.Auto.EquivLoop