module

public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Litmus.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Thms

/-!
# Message passing with a weak data store: the XL run and the TSO check
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.TameLitmus

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Csl.Tame.Litmus

/-- The explorer's fuel (the test has a handful of states). -/
def fuel : Nat := 200

theorem nt_tso_check : tsoCheck 2 fuel (mp .nt) notWeakB = true := by decide +kernel

theorem wb_tso_check : tsoCheck 2 fuel (mp .wb) notWeakB = true := by decide +kernel

set_option linter.unusedSimpArgs false in
/-- **The weak outcome on XL**, step by step: thread 0 buffers both stores, the flag store is
flushed first (it passes the `nt` data store), thread 1 reads the flag `1` and the data `0`, and
the data store is flushed last. -/
theorem nt_xl_run : ∃ C : OCfg, OReach .xl 2 (mp .nt).cfg.toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ weakOut (C.ts 1).2 := by
  refine ⟨_, .step (.buffered (t := 0) (by decide) (.seq .store) rfl rfl ?c1 ?k1)
    (.step (.tau (t := 0) (by decide) .seqSkip)
    (.step (.buffered (t := 0) (by decide) .store rfl rfl ?c2 ?k2)
    (.step (.flush (t := 0) (pre := [.st d 1 true]) (e := .st f 1 false) (post := [])
        (by decide) ?b1 ?p1 (Or.inl rfl))
    (.step (.buffered (t := 1) (by decide) (.seq (.load (v := 1) (by decide))) rfl rfl ?c3 ?k3)
    (.step (.tau (t := 1) (by decide) .seqSkip)
    (.step (.buffered (t := 1) (by decide) (.load (v := 0) (by decide)) rfl rfl ?c4 ?k4)
    (.step (.flush (t := 0) (pre := []) (e := .st d 1 true) (post := []) (by decide) ?b2
        ?p2 (Or.inr rfl)) .refl))))))), ?dr, ?fin, ?w⟩
  case fin =>
    intro t ht
    match t, ht with
    | 0, _ => rfl
    | 1, _ => rfl
  case dr =>
    intro t
    by_cases h0 : t = 0
    · subst h0; rfl
    · simp [upd, h0, Cfg.toO, CSt.cfg, Lab.ents]
  all_goals simp (config := {decide := true}) [Lab.Touches, Lab.reads, Lab.wval, Lab.okH,
    Lab.ents, view, newest, Ent.val, Ent.apply, Ent.passes, upd, Cfg.toO, OCfg.Drained, CSt.cfg,
    CSt.th, mp, start, memOf, d, f, weakOut, Expr.eval]

theorem not_weak_of_check {fl : Flav} (h : tsoCheck 2 fuel (mp fl) notWeakB = true)
    {C : OCfg} (hr : OReach .tso 2 (mp fl).cfg.toO C) (hd : C.Drained)
    (hf : ∀ t < 2, (C.ts t).1 = .skip) : ¬ weakOut (C.ts 1).2 := by
  obtain ⟨e, hP, rfl⟩ := tsoCheck_sound h hr hd hf
  rintro ⟨h1, h2⟩
  change (e.th 1).2 .rax = 1 at h1
  change (e.th 1).2 .rbx = 0 at h2
  simp [notWeakB, h1, h2] at hP

theorem nt_tso_forbidden {C : OCfg} (hr : OReach .tso 2 (mp .nt).cfg.toO C)
    (hd : C.Drained) (hf : ∀ t < 2, (C.ts t).1 = .skip) : ¬ weakOut (C.ts 1).2 :=
  not_weak_of_check nt_tso_check hr hd hf

theorem wb_tso_forbidden {C : OCfg} (hr : OReach .tso 2 (mp .wb).cfg.toO C)
    (hd : C.Drained) (hf : ∀ t < 2, (C.ts t).1 = .skip) : ¬ weakOut (C.ts 1).2 :=
  not_weak_of_check wb_tso_check hr hd hf

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.TameLitmus
