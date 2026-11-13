module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Selective.Exec

/-!
# Selective instrumentation: the simulation

Every step of the optimized machine `tstep (optP S Q)` is matched by one step of the
instrumented `tstep Q`, or by two when a frame returns to a caller that waits on a function in
`S` (the instrumented caller runs its check, the optimized one has none): **`sim`**, a
relational stuttering simulation (`RSim`) under the certificate `SafeProg S Q`.

* `return_rel`: a return, to a flagged or an unflagged frame;
* `normal_rel`: normal mode;
* `unwind_rel`, `rchk_unwind_rel`: an unwinding step (no frame is flagged while unwinding);
* `rewind_rel`: a rewinding step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Selective

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.RelSim Silmaril.Wasm.FX.Asyncify.Selective

variable {V : Type} {S : Nat → Bool} {Q : Prog (TIns V)} {test : V → Bool}

/-- A return to an unflagged frame, or to a flagged one whose code has no leading check. -/
theorem return_plain {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {ops : List (SV V)} {b' b : TFrame V} (hops : b'.ops = b.ops)
    (hcode : b'.code = opt S false b.code) {os us : List (TFrame V)}
    (tl : Stk S (SafeCode S ([] : List (TIns V)) ∧ SafeCode S b.code) os us) :
    ∃ n, 0 < n ∧ RRes (SR S) (tstep (optP S Q) test ⟨h', .normal, ⟨[], ops⟩ :: b' :: os⟩)
      (runN (tstep Q test) n ⟨h, .normal, ⟨[], ops⟩ :: b :: us⟩) := by
  refine ⟨1, Nat.one_pos, ?_⟩
  have hs : Stk S (SafeCode S b.code) os us := stk_mono tl fun h1 => h1.2
  have hr : SR S ⟨h', .normal, ⟨b'.code, ops ++ b'.ops⟩ :: os⟩
      ⟨h, .normal, ⟨b.code, ops ++ b.ops⟩ :: us⟩ := by
    rw [hcode, hops]; exact sr_normal hh hs
  rw [runN_one]
  exact .next hr

/-- A return to a flagged frame whose instrumented code starts with the check: two steps. -/
theorem return_skip {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {ops : List (SV V)} {b' b : TFrame V} {d : List (TIns V)} (hd : b.code = .chk :: d)
    (hops : b'.ops = b.ops) (hcode : b'.code = opt S true b.code) {os us : List (TFrame V)}
    (tl : Stk S (SafeCode S ([] : List (TIns V)) ∧ SafeCode S b.code) os us) :
    ∃ n, 0 < n ∧ RRes (SR S) (tstep (optP S Q) test ⟨h', .normal, ⟨[], ops⟩ :: b' :: os⟩)
      (runN (tstep Q test) n ⟨h, .normal, ⟨[], ops⟩ :: b :: us⟩) := by
  refine ⟨2, Nat.two_pos, ?_⟩
  have hs : Stk S (SafeCode S d) os us := stk_next (hd ▸ stk_mono tl fun h1 => h1.2)
  have hc' : b'.code = opt S false d := by rw [hcode, hd, opt_true_chk]
  have h1 : tstep Q test ⟨h, .normal, ⟨[], ops⟩ :: b :: us⟩ =
      .next ⟨h, .normal, ⟨.chk :: d, ops ++ b.ops⟩ :: us⟩ := by
    simp only [tstep, hd]
  have hr : SR S ⟨h', .normal, ⟨b'.code, ops ++ b'.ops⟩ :: os⟩
      ⟨h, .normal, ⟨d, ops ++ b.ops⟩ :: us⟩ := by
    rw [hc', hops]; exact sr_normal hh hs
  rw [runN_two h1]
  exact .next hr

/-- **A return.** -/
theorem return_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    (ops : List (SV V)) {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S ([] : List (TIns V))) os us) :
    ∃ n, 0 < n ∧ RRes (SR S) (tstep (optP S Q) test ⟨h', .normal, ⟨[], ops⟩ :: os⟩)
      (runN (tstep Q test) n ⟨h, .normal, ⟨[], ops⟩ :: us⟩) := by
  cases hstk with
  | nil => exact ⟨1, Nat.one_pos, by rw [runN_one]; exact .stop _⟩
  | @cons _ fb b' b os' us' hfr _ tl =>
    cases fb with
    | false => exact return_plain hh hfr.1 hfr.2 tl
    | true =>
      rcases opt_true_cases (S := S) b.code with ⟨d, hd⟩ | heq
      · exact return_skip hh hd hfr.1 hfr.2 tl
      · exact return_plain hh hfr.1 (hfr.2.trans heq) tl

/-- **Normal mode.** -/
theorem normal_rel (hQ : SafeProg S Q) {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {fo fu : TFrame V} (hfr : FR S false fo fu) {os us : List (TFrame V)}
    (hstk : Stk S (SafeCode S fu.code) os us) :
    ∃ n, 0 < n ∧ RRes (SR S) (tstep (optP S Q) test ⟨h', .normal, fo :: os⟩)
      (runN (tstep Q test) n ⟨h, .normal, fu :: us⟩) := by
  obtain ⟨co, oo⟩ := fo
  obtain ⟨cu, ou⟩ := fu
  obtain ⟨hops, hcode⟩ := hfr
  cases hops
  cases hcode
  cases cu with
  | nil => exact return_rel hh oo hstk
  | cons i c =>
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [runN_one]
    simp only [tstep, opt_false_cons]
    exact texec_rel hQ hh hstk _ _ rfl

/-- An unwinding step at an `rchk`. -/
theorem rchk_unwind_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h) {t : Nat}
    {p : List (SV V)} {bo bu : List (TFrame V)} (hb : List.Forall₂ (FR S false) bo bu)
    {hs : List Clause} {c : List (TIns V)} {ops : List (SV V)} {os us : List (TFrame V)}
    (tl : List.Forall₂ (FR S false) os us) :
    RRes (SR S) (tunwind (optP S Q) h' t p bo ⟨.rchk hs :: opt S false c, ops⟩ os)
      (tunwind Q h t p bu ⟨.rchk hs :: c, ops⟩ us) := by
  have hmid : FR S false ⟨.chk :: opt S false c, ops⟩ ⟨.chk :: c, ops⟩ :=
    ⟨rfl, (opt_false_cons .chk c).symm⟩
  have hh' : HR S (h' ++ [some bo]) (h ++ [some bu]) := forall₂_append_one hh (.some hb)
  have hlen : h'.length = h.length := hh.length_eq
  simp only [tunwind]
  rcases lookup t hs with _ | hf
  · exact .next ⟨hh, ⟨rfl, rfl, forall₂_append_one hb ⟨rfl, rfl⟩⟩, tl⟩
  · dsimp only
    rcases hq : Q hf with _ | ⟨np, body⟩
    · simp only [optP_none hq]; exact .stop _
    · simp only [optP_some hq, hlen]
      exact .next ⟨hh', trivial, ⟨rfl, rfl⟩, stk_of_forall₂ (.cons hmid tl) _⟩

/-- **An unwinding step.** -/
theorem unwind_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h) {t : Nat}
    {p : List (SV V)} {bo bu : List (TFrame V)} (hb : List.Forall₂ (FR S false) bo bu)
    {os us : List (TFrame V)} (hs : List.Forall₂ (FR S false) os us) :
    RRes (SR S) (tstep (optP S Q) test ⟨h', .unwind t p bo, os⟩)
      (tstep Q test ⟨h, .unwind t p bu, us⟩) := by
  cases hs with
  | nil => exact .stop _
  | @cons fo fu os' us' hfr tl =>
    obtain ⟨co, oo⟩ := fo
    obtain ⟨cu, ou⟩ := fu
    obtain ⟨hops, hcode⟩ := hfr
    cases hops
    cases hcode
    simp only [tstep]
    rcases cu with _ | ⟨i, c⟩
    · exact .stop _
    · rw [opt_false_cons]
      cases i
      case chk => exact .next ⟨hh, ⟨rfl, rfl, forall₂_append_one hb ⟨rfl, rfl⟩⟩, tl⟩
      case rchk hs => exact rchk_unwind_rel hh hb tl
      all_goals exact .stop _

/-- **A rewinding step.** -/
theorem rewind_rel {h' h : List (Option (List (TFrame V)))} (hh : HR S h' h)
    {args : List (SV V)} {po pu : List (TFrame V)} (hp : List.Forall₂ (FR S false) po pu)
    {os us : List (TFrame V)} (hs : List.Forall₂ (FR S false) os us) :
    RRes (SR S) (tstep (optP S Q) test ⟨h', .rewind po args, os⟩)
      (tstep Q test ⟨h, .rewind pu args, us⟩) := by
  cases hp with
  | nil => exact .stop _
  | @cons b' b po' pu' hfr tl =>
    cases tl with
    | nil =>
      have htop : FR S false ⟨b'.code, args ++ b'.ops⟩ ⟨b.code, args ++ b.ops⟩ := by
        rw [hfr.1]; exact ⟨rfl, hfr.2⟩
      exact .next ⟨hh, trivial, htop, stk_of_forall₂ hs _⟩
    | cons hfr2 tl2 => exact .next ⟨hh, ⟨rfl, .cons hfr2 tl2⟩, .cons hfr hs⟩

/-- **The selective lowering is simulated by the instrumented one.** -/
theorem sim (hQ : SafeProg S Q) : RSim (SR S) (tstep (optP S Q) test) (tstep Q test) := by
  rintro ⟨h', mo, so⟩ ⟨h, mu, su⟩ ⟨hh, hm, hst⟩
  cases mo <;> cases mu
  case normal.normal =>
    rcases so with _ | ⟨fo, os⟩ <;> rcases su with _ | ⟨fu, us⟩
    · exact ⟨1, Nat.one_pos, by rw [runN_one]; exact .stop _⟩
    · exact False.elim hst
    · exact False.elim hst
    · exact normal_rel hQ hh hst.1 hst.2
  case unwind.unwind t p bo t' p' bu =>
    obtain ⟨rfl, rfl, hb⟩ := hm
    exact ⟨1, Nat.one_pos, by rw [runN_one]; exact unwind_rel hh hb hst⟩
  case rewind.rewind po args pu args' =>
    obtain ⟨rfl, hp⟩ := hm
    exact ⟨1, Nat.one_pos, by rw [runN_one]; exact rewind_rel hh hp hst⟩
  all_goals exact False.elim hm

end Silmaril.Proofs.Wasm.FX.Asyncify.Selective
