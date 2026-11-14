module

public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Defs
public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs

/-!
# Tame programs: XL runs are TSO runs

A thread step of a `wbStores` statement stays `wbStores` and buffers no weak entry; with no weak
entry buffered, XL's flush rule (`Ent.passes`) only lets the oldest entry go, which is TSO's.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Tame

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

-- The unused-tactic linter misreads `<;>` here (`;` breaks the proof).
set_option linter.unusedTactic false in
/-- A thread step of a tame statement stays tame and buffers only non-weak entries. -/
theorem tstep_wb {s : Stmt} {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep s rs l s' rs') (hw : s.wbStores = true) :
    s'.wbStores = true ∧ ∀ lab, l = some lab → ∀ e ∈ lab.ents, e.wb = true := by
  induction h with
  | store =>
    refine ⟨rfl, ?_⟩
    rintro lab ⟨⟩ e he
    simp only [Lab.ents, List.mem_singleton] at he
    subst he
    simp only [Stmt.wbStores, beq_iff_eq] at hw
    simp [Ent.wb, hw]
  | fence =>
    rename_i k _
    refine ⟨rfl, ?_⟩
    rintro lab ⟨⟩ e he
    cases k <;> simp_all [Lab.ents, Ent.wb]
  | blk =>
    refine ⟨rfl, ?_⟩
    rintro lab ⟨⟩ e he
    simp only [Lab.ents, List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    rfl
  | seq _ ih =>
    simp only [Stmt.wbStores, Bool.and_eq_true] at hw
    obtain ⟨h1, h2⟩ := ih hw.1
    exact ⟨by simp [Stmt.wbStores, h1, hw.2], h2⟩
  | seqSkip =>
    simp only [Stmt.wbStores, Bool.and_eq_true] at hw
    exact ⟨hw.2, by rintro _ ⟨⟩⟩
  | iteT =>
    simp only [Stmt.wbStores, Bool.and_eq_true] at hw
    exact ⟨hw.1, by rintro _ ⟨⟩⟩
  | iteF =>
    simp only [Stmt.wbStores, Bool.and_eq_true] at hw
    exact ⟨hw.2, by rintro _ ⟨⟩⟩
  | loopT =>
    simp only [Stmt.wbStores] at hw
    exact ⟨by simp [Stmt.wbStores, hw], by rintro _ ⟨⟩⟩
  | loopF => exact ⟨rfl, by rintro _ ⟨⟩⟩
  | _ => exact ⟨rfl, by rintro lab ⟨⟩ e he <;> simp [Lab.ents] at he⟩

/-- With no weak entry, an entry passes no earlier entry. -/
theorem passes_nil {e : Ent} {pre : List Ent} (hp : e.passes pre) (he : e.wb = true)
    (hpre : ∀ e' ∈ pre, e'.wb = true) : pre = [] := by
  cases e with
  | bar => exact hp
  | st a v w =>
    cases pre with
    | nil => rfl
    | cons e' pre =>
      have h := hp e' (List.mem_cons_self ..)
      have h' := hpre e' (List.mem_cons_self ..)
      cases e' with
      | bar => exact h.elim
      | st a' v' w' =>
        simp only [Ent.wb, Bool.not_eq_true'] at he h'
        subst he h'
        simp at h

theorem upd_ts {N : Nat} {C : OCfg} {t : Nat}
    (hw : ∀ u < N, (C.ts u).1.wbStores = true) {x : Stmt × Regs} (hx : x.1.wbStores = true) :
    ∀ u < N, (upd C.ts t x u).1.wbStores = true := by
  intro u hu
  unfold upd
  split
  · exact hx
  · exact hw u hu

/-- **One XL step of a tame configuration is a TSO step**, to a tame configuration. -/
theorem step_tso {N : Nat} {C D : OCfg} (h : OStep .xl N C D) (hw : C.Wb N) :
    OStep .tso N C D ∧ D.Wb N := by
  obtain ⟨hts, hbuf⟩ := hw
  cases h with
  | tau ht hs =>
    exact ⟨.tau ht hs, upd_ts hts (tstep_wb hs (hts _ ht)).1, hbuf⟩
  | buffered ht hs hm hd hc hok =>
    rename_i t l _ _
    refine ⟨.buffered ht hs hm hd hc hok, upd_ts hts (tstep_wb hs (hts _ ht)).1, ?_⟩
    intro u e he
    simp only [upd] at he
    split at he
    · subst u
      rcases List.mem_append.1 he with he | he
      · exact hbuf _ e he
      · exact (tstep_wb hs (hts _ ht)).2 l rfl e he
    · exact hbuf u e he
  | drained ht hs hm hd he hc hok =>
    exact ⟨.drained ht hs hm hd he hc hok, upd_ts hts (tstep_wb hs (hts _ ht)).1, hbuf⟩
  | flush ht hb hp hmod =>
    rename_i t pre e post
    have hall : ∀ x ∈ pre ++ e :: post, x.wb = true := fun x hx => hbuf t x (hb ▸ hx)
    have hpre : pre = [] := passes_nil hp (hall e (by simp))
      (fun x hx => hall x (List.mem_append_left _ hx))
    refine ⟨.flush ht hb hp (Or.inr hpre), hts, ?_⟩
    intro u x hx
    simp only [upd] at hx
    split at hx
    · subst u
      exact hall x (by
        rcases List.mem_append.1 hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    · exact hbuf u x hx

/-- **XL runs of a tame configuration are TSO runs.** -/
theorem reach_tso {N : Nat} {C D : OCfg} (h : OReach .xl N C D) (hw : C.Wb N) :
    OReach .tso N C D := by
  induction h with
  | refl => exact .refl
  | step h1 _ ih =>
    obtain ⟨s, w⟩ := step_tso h1 hw
    exact .step s (ih w)

/-- The start of a tame configuration is tame. -/
theorem wb_toO {N : Nat} {C : Cfg} (hw : C.WbStores N) : C.toO.Wb N :=
  ⟨hw, fun _ _ he => by simp [Cfg.toO] at he⟩

/-- **Every buffered model's runs from a tame start are TSO runs.** -/
theorem reach_tso_of_wb {M : OModel} {N : Nat} {C0 : Cfg} {C : OCfg} (hw : C0.WbStores N)
    (h : OReach M N C0.toO C) : OReach .tso N C0.toO C := by
  cases M with
  | tso => exact h
  | xl => exact reach_tso h (wb_toO hw)

/-- Setting loop bounds does not change the check. -/
theorem wbStores_setB (L : Nat) : ∀ s : Stmt, (TvCfg.setB L s).wbStores = s.wbStores
  | .seq s t => by simp [TvCfg.setB, Stmt.wbStores, wbStores_setB L s, wbStores_setB L t]
  | .ite c s t => by simp [TvCfg.setB, Stmt.wbStores, wbStores_setB L s, wbStores_setB L t]
  | .loop n c b => by simp [TvCfg.setB, Stmt.wbStores, wbStores_setB L b]
  | .skip | .assign .. | .load .. | .store .. | .rmw .. | .fence .. | .futexWait ..
  | .futexWake .. | .spawn .. | .join .. | .local .. => rfl

/-- The check of a chain is the conjunction. -/
theorem wbStores_chain : ∀ l : List Stmt, (Tv.chain l).wbStores = l.all Stmt.wbStores
  | [] => rfl
  | s :: l => by simp [Tv.chain, Stmt.wbStores, wbStores_chain l]

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Tame
