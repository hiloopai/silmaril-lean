module

public import Silmaril.Wasm.Auto.EquivLoop.Defs
public import Silmaril.Proofs.Wasm.Auto.EquivLoop.Total

/-!
# Loop equivalence under a state invariant

The proofs of `CEquiv.loop` (partial correctness, Löb induction) and `CEquiv.loopT` (total
correctness, accessibility induction) with the typed-frame condition replaced by an arbitrary
invariant `I` of the store and frame, kept at the back edges (`KeepsBr0I`):

* `safe_loop_congrI`, `tsafe_loop_congrI`;
* **`LoopEquivI.of_body`**: equivalent bodies (`BodyEquivI`) that keep the invariant at their back
  edges give equivalent loops, both readings.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EquivLoop

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivLoop
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem BodyEquivI.symm {I : SInv} {a b : List Instr} (h : BodyEquivI I a b) : BodyEquivI I b a :=
  fun m P _ host s f Q hI => (h m P host s f Q hI).symm

theorem KeepsBr0I.of_equiv {I : SInv} {a b : List Instr} (hk : KeepsBr0I I a)
    (h : BodyEquivI I a b) : KeepsBr0I I b := by
  intro P H host s f Q hI hb
  have ha : HWP P host s f (expression a) Q := (h .part P host s f Q hI).mpr hb
  exact (h .part P host s f _ hI).mp (hk P host s f Q hI ha)

/-- **Löb induction for the loop congruence under an invariant.** -/
theorem safe_loop_congrI {I : SInv} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : BodyEquivI I a b) (hk : KeepsBr0I I a) (n : Nat) :
    ∀ {s : Store H} {f : Frame} {us : List Val} {Q : Post H},
      I s f → NoFuncTop us → HWP P host s f (vals us ++ [.plain (.loop bt a)]) Q →
      Safe P host Q n ⟨s, f, vals us ++ [.plain (.loop bt b)]⟩ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s f us Q hf hus hw
  rcases n with _ | n
  · trivial
  obtain ⟨t₂, ht⟩ := hbt f.module
  have hbA : HWP P host s f (expression a) (labelPost P host 0 [.loop bt a] us Q) :=
    hwp_label_inv hus (hw.step_inv (loop_step ht))
  have hbB : HWP P host s f (expression b) (InvBr0 I (labelPost P host 0 [.loop bt a] us Q)) :=
    (h .part P host s f _ hf).mp (hk P host s f _ hf hbA)
  refine Safe.head ⟨rfl, by simp, rfl⟩ ⟨us, [], _, by simp, .loop ht rfl⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := head_loop hh
  obtain ⟨rfl, rfl⟩ : t₁' = [] ∧ t₂' = t₂ := by simpa [ht] using hbt'.symm
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hn'
  subst hargs
  have hus' : us' = us := by simpa using hW.symm
  subst hus'
  rcases n with _ | k
  · trivial
  have hb : Safe P host (labelPostK P host 0 [.loop bt b] us' Q k) (k + 1)
      ⟨s, f, vals [] ++ expression b⟩ := by
    refine ((hbB (k + 1)).post_mono fun s' F o ho => ?_)
    rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | x | ⟨vs, x, c⟩
    · exact ho.1
    · obtain ⟨vs₁, vs₂, he, hn, hw'⟩ := ho.1
      have hv : vs₂ = [] := List.eq_nil_of_length_eq_zero hn
      subst hv
      refine ⟨vs₁, [], he, rfl, ?_⟩
      have := ih k (by omega) (ho.2 _ rfl) hus (by simpa [expression] using hw')
      simpa [expression] using this
    all_goals exact ho.1
  simpa using Safe.label (us := us') (k := k) le_rfl hb

/-- **The loop congruence under an invariant, total correctness.** -/
theorem tsafe_loop_congrI {I : SInv} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : BodyEquivI I a b) (hk : KeepsBr0I I a) (c : Config H)
    (hacc : Acc (Relation.TransGen (StepBack P host)) c) :
    ∀ {s : Store H} {f : Frame} {us : List Val} {Q : Post H},
      c = ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩ → I s f → NoFuncTop us →
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
    (h .total P host s f _ hf).mp hbA₂
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

/-- **Loops under an invariant**: equivalent bodies that keep the invariant at their back edges
give equivalent loops, in both readings. -/
theorem LoopEquivI.of_body {I : SInv} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : BodyEquivI I a b) (hk : KeepsBr0I I a) : LoopEquivI I bt a b := by
  intro m P H host s f us rest Q hf hus
  cases m with
  | part =>
    constructor
    · intro hw
      exact HWP.seq fun n => safe_loop_congrI hbt h hk n hf hus (hwp_seq_inv hw)
    · intro hw
      exact HWP.seq fun n => safe_loop_congrI hbt (BodyEquivI.symm h) (KeepsBr0I.of_equiv hk h) n hf hus (hwp_seq_inv hw)
  | total =>
    constructor
    · intro hw
      have h₁ := twp_seq_inv hw
      exact TWP.seq (tsafe_loop_congrI hbt h hk _ (acc_of_tsafe h₁).transGen rfl hf hus h₁)
    · intro hw
      have h₁ := twp_seq_inv hw
      exact TWP.seq (tsafe_loop_congrI hbt (BodyEquivI.symm h) (KeepsBr0I.of_equiv hk h) _ (acc_of_tsafe h₁).transGen
        rfl hf hus h₁)

end Silmaril.Proofs.Wasm.Auto.EquivLoop