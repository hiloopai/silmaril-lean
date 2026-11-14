module

public import Silmaril.Process.Mt.Defs

/-!
# Proofs: the single-threaded process is the one-thread case

The header is `Silmaril/Process/Mt/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Solo

open Silmaril.X86 (Word)
open Silmaril.Process.Mt

variable {γ : Type} {U : UIsa γ} {P : PrimTable γ} {base : Base γ} {tid : Nat}

theorem setTh_self {σ : Type} (th : Nat → Option (TRec σ)) (t : Nat) (r : TRec σ) :
    setTh th t r t = some r := by simp [setTh, upd]

theorem setTh_other {σ : Type} (th : Nat → Option (TRec σ)) (t u : Nat) (r : TRec σ) (h : u ≠ t) :
    setTh th t r u = th u := by simp [setTh, upd, h]

theorem setTh_eq_self {σ : Type} {th : Nat → Option (TRec σ)} {t : Nat} {r : TRec σ}
    (h : th t = some r) : setTh th t r = th := by
  funext u; by_cases hu : u = t
  · subst hu; rw [setTh_self, h]
  · rw [setTh_other _ _ _ _ hu]

theorem only_tid {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) {t : Nat}
    {r : TRec U.St} (ht : C.th t = some r) : t = tid := by
  by_contra h; rw [hR.2.2.2.2.2.1 t h] at ht; cases ht

theorem run_st {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) (hl : x.status = none)
    {r : TRec U.St} {s : U.St} (ht : C.th tid = some r) (hr : r.st = .run s) : s = x.st := by
  obtain ⟨r0, h0, h1⟩ := hR.2.2.2.2.2.2
  rw [ht] at h0; cases h0
  rcases h1 with h1 | ⟨h1, _⟩
  · rw [hr] at h1; cases h1; rfl
  · rw [hl] at h1; cases h1

theorem not_wait {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) (hl : x.status = none)
    {r : TRec U.St} {a : Nat} {k : Word → U.St} (ht : C.th tid = some r) (hr : r.st = .wait a k) : False := by
  obtain ⟨r0, h0, h1⟩ := hR.2.2.2.2.2.2
  rw [ht] at h0; cases h0
  rcases h1 with h1 | ⟨h1, _⟩
  · rw [hr] at h1; cases h1
  · rw [hl] at h1; cases h1

theorem live_iff {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) :
    C.Live U ↔ x.Live U := by
  simp only [MtCfg.Live, SoloCfg.Live, hR.2.2.1, hR.2.2.2.2.1]

theorem sh_eq {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) : C.sh sc = x.sh := by
  simp only [MtCfg.sh, SoloCfg.sh, sc, hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1]

theorem step_eq {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) {o : UOut U.St γ} :
    U.step tid x.st (sc.view C.ms tid) C.g o ↔ U.step tid x.st x.mem x.g o := by
  have h1 : sc.view C.ms tid = x.mem := hR.1
  rw [h1, hR.2.2.1]

/-- After `tid` exits, no thread lives. -/
theorem none_live {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) (r : TRec U.St) :
    ¬ ∃ u, LiveT (setTh C.th tid { r with st := .exited }) u := by
  rintro ⟨u, r', hu, hx⟩
  by_cases h : u = tid
  · subst h; rw [setTh_self] at hu; cases hu; simp [TSt.isExited] at hx
  · rw [setTh_other _ _ _ _ h, hR.2.2.2.2.2.1 u h] at hu; cases hu

open Classical in
theorem lastExit_none_live {σ : Type} {th : Nat → Option (TRec σ)} {c : Nat} (h : ¬ ∃ u, LiveT th u) :
    lastExit th c = some c := by simp [lastExit, h]

/-- Building the relation after a step. -/
theorem rel_of {x x' : SoloCfg U.St γ} {C C' : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) (r' : TRec U.St)
    (hth : C'.th = setTh C.th tid r') (hms : C'.ms = x'.mem) (hps : C'.ps = x'.ps) (hg : C'.g = x'.g)
    (hmt : C'.mt = C.mt) (hst : C'.status = x'.status)
    (hr : r'.st = .run x'.st ∨ (x'.status.isSome ∧ r'.st = .exited)) : SoloRel tid x' C' := by
  refine ⟨hms, hps, hg, hmt.trans hR.2.2.2.1, hst, ?_, ⟨r', by rw [hth, setTh_self], hr⟩⟩
  intro t h; rw [hth, setTh_other _ _ _ _ h]; exact hR.2.2.2.2.2.1 t h

theorem run_rec {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) (hl : x.status = none) :
    ∃ r, C.th tid = some r ∧ r.st = .run x.st := by
  obtain ⟨r0, h0, h1⟩ := hR.2.2.2.2.2.2
  rcases h1 with h1 | ⟨h1, _⟩
  · exact ⟨r0, h0, h1⟩
  · rw [hl] at h1; cases h1

/-! ## Every single-threaded step is a one-thread step -/

theorem solo_step {x x' : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C)
    (h : SoloStep U P base tid x x') : ∃ C', MtStep U sc P base C C' ∧ SoloRel tid x' C' := by
  have hsh := sh_eq hR
  cases h with
  | user hl hs =>
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    exact ⟨_, .user ((live_iff hR).2 hl) h0 h1 ((step_eq hR).2 hs) rfl,
      rel_of hR _ rfl rfl hR.2.1 hR.2.2.1 rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | lib hl hs =>
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    exact ⟨_, .lib ((live_iff hR).2 hl) h0 h1 trivial ((step_eq hR).2 hs),
      rel_of hR _ rfl rfl hR.2.1 rfl rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | prim hl hs hp hpre hpost =>
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    exact ⟨_, .prim ((live_iff hR).2 hl) h0 h1 trivial ((step_eq hR).2 hs) hp (hsh ▸ hpre) (hsh ▸ hpost),
      rel_of hR _ rfl rfl rfl rfl rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | gettid hl hs =>
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    exact ⟨_, .gettid ((live_iff hR).2 hl) h0 h1 trivial ((step_eq hR).2 hs),
      rel_of hR _ rfl hR.1 hR.2.1 hR.2.2.1 rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | setTid hl hs =>
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    exact ⟨_, .setTid ((live_iff hR).2 hl) h0 h1 trivial ((step_eq hR).2 hs),
      rel_of hR _ rfl hR.1 hR.2.1 hR.2.2.1 rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | exit hl hs =>
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    refine ⟨_, .exitPlain ((live_iff hR).2 hl) h0 h1 trivial ((step_eq hR).2 hs)
      (fun _ _ _ => none_live hR r), rel_of hR _ rfl hR.1 hR.2.1 hR.2.2.1 rfl ?_ (.inr ⟨rfl, rfl⟩)⟩
    exact lastExit_none_live (none_live hR r)
  | exitGroup hl hs =>
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    refine ⟨_, .exitGroup ((live_iff hR).2 hl) h0 h1 trivial ((step_eq hR).2 hs), ?_⟩
    exact rel_of hR r (setTh_eq_self h0).symm hR.1 hR.2.1 hR.2.2.1 rfl rfl (.inl h1)
  | base hl hs hn hb =>
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    refine ⟨_, .base ((live_iff hR).2 hl) h0 h1 trivial ((step_eq hR).2 hs) hn
      (by rw [show sc.mem C.ms = x.mem from hR.1, hR.2.2.1]; exact hb),
      rel_of hR _ rfl rfl hR.2.1 rfl rfl hR.2.2.2.2.1 (.inl rfl)⟩

/-! ## Every one-thread step without `clone` and `futex` is a single-threaded step -/

theorem step_solo {x : SoloCfg U.St γ} {C C' : MtCfg U.St γ sc.S} (hR : SoloRel tid x C)
    (hn : NoThreadSys U tid x) (h : MtStep U sc P base C C') :
    ∃ x', SoloStep U P base tid x x' ∧ SoloRel tid x' C' := by
  have hsh := sh_eq hR
  cases h with
  | user hl ht hr hs hm =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    cases hm
    exact ⟨_, .user ((live_iff hR).1 hl) ((step_eq hR).1 hs),
      rel_of hR _ rfl rfl hR.2.1 hR.2.2.1 rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | lib hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact ⟨_, .lib ((live_iff hR).1 hl) ((step_eq hR).1 hs),
      rel_of hR _ rfl rfl hR.2.1 rfl rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | prim hl ht hr _ hs hp hpre hpost =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact ⟨_, .prim ((live_iff hR).1 hl) ((step_eq hR).1 hs) hp (hsh ▸ hpre) (hsh ▸ hpost),
      rel_of hR _ rfl rfl rfl rfl rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | gettid hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact ⟨_, .gettid ((live_iff hR).1 hl) ((step_eq hR).1 hs),
      rel_of hR _ rfl hR.1 hR.2.1 hR.2.2.1 rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | setTid hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact ⟨_, .setTid ((live_iff hR).1 hl) ((step_eq hR).1 hs),
      rel_of hR _ rfl hR.1 hR.2.1 hR.2.2.1 rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | futexBlock hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact absurd rfl (hn _ _ _ _ ((step_eq hR).1 hs)).2
  | futexAgain hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact absurd rfl (hn _ _ _ _ ((step_eq hR).1 hs)).2
  | futexWake hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact absurd rfl (hn _ _ _ _ ((step_eq hR).1 hs)).2
  | spurious hl ht hr =>
    obtain rfl := only_tid hR ht; exact (not_wait hR ((live_iff hR).1 hl).1 ht hr).elim
  | clone hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact absurd rfl (hn _ _ _ _ ((step_eq hR).1 hs)).1
  | exitClear hl ht hr _ hs _ _ hlive =>
    obtain rfl := only_tid hR ht
    exact (none_live hR _ hlive).elim
  | exitPlain hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact ⟨_, .exit ((live_iff hR).1 hl) ((step_eq hR).1 hs),
      rel_of hR _ rfl hR.1 hR.2.1 hR.2.2.1 rfl (lastExit_none_live (none_live hR _)) (.inr ⟨rfl, rfl⟩)⟩
  | exitGroup hl ht hr _ hs =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    exact ⟨_, .exitGroup ((live_iff hR).1 hl) ((step_eq hR).1 hs),
      rel_of hR _ (setTh_eq_self ht).symm hR.1 hR.2.1 hR.2.2.1 rfl rfl (.inl hr)⟩
  | base hl ht hr _ hs hn' hb =>
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    refine ⟨_, .base ((live_iff hR).1 hl) ((step_eq hR).1 hs) hn'
      (by rw [← show sc.mem C.ms = x.mem from hR.1, ← hR.2.2.1]; exact hb),
      rel_of hR _ rfl rfl hR.2.1 rfl rfl hR.2.2.2.2.1 (.inl rfl)⟩
  | flush hf => exact hf.elim

/-! ## Faults agree -/

theorem fault_iff {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) :
    MtFault U sc P C ↔ SoloFault U P tid x := by
  constructor
  · rintro ⟨hl, t, r, s, ht, hr, h⟩
    obtain rfl := only_tid hR ht; obtain rfl := run_st hR ((live_iff hR).1 hl).1 ht hr
    refine ⟨(live_iff hR).1 hl, ?_⟩
    rcases h with h | ⟨p, args, k, h1, h2⟩
    · exact .inl ((step_eq hR).1 h)
    · exact .inr ⟨p, args, k, (step_eq hR).1 h1, fun sp hp => sh_eq hR ▸ h2 sp hp⟩
  · rintro ⟨hl, h⟩
    obtain ⟨r, h0, h1⟩ := run_rec hR hl.1
    refine ⟨(live_iff hR).2 hl, tid, r, x.st, h0, h1, ?_⟩
    rcases h with h | ⟨p, args, k, h1, h2⟩
    · exact .inl ((step_eq hR).2 h)
    · exact .inr ⟨p, args, k, (step_eq hR).2 h1, fun sp hp => (sh_eq hR).symm ▸ h2 sp hp⟩

/-! ## Runs -/

theorem reach_solo {x x' : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C)
    (h : Relation.ReflTransGen (SoloStep U P base tid) x x') :
    ∃ C', MtReach U sc P base C C' ∧ SoloRel tid x' C' := by
  induction h with
  | refl => exact ⟨C, .refl, hR⟩
  | tail _ hs ih =>
    obtain ⟨C1, h1, hR1⟩ := ih
    obtain ⟨C2, h2, hR2⟩ := solo_step hR1 hs
    exact ⟨C2, h1.tail h2, hR2⟩

theorem solo_reach {x : SoloCfg U.St γ} {C C' : MtCfg U.St γ sc.S} (hR : SoloRel tid x C)
    (hn : ∀ y, Relation.ReflTransGen (SoloStep U P base tid) x y → NoThreadSys U tid y)
    (h : MtReach U sc P base C C') :
    ∃ x', Relation.ReflTransGen (SoloStep U P base tid) x x' ∧ SoloRel tid x' C' := by
  induction h with
  | refl => exact ⟨x, .refl, hR⟩
  | tail _ hs ih =>
    obtain ⟨x1, h1, hR1⟩ := ih
    obtain ⟨x2, h2, hR2⟩ := step_solo hR1 (hn x1 h1) hs
    exact ⟨x2, h1.tail h2, hR2⟩

/-! ## Demonic results transfer -/

theorem solo_must_aux {Q : SoloCfg U.St γ → Prop} {x : SoloCfg U.St γ}
    (h : SMust (SoloStep U P base tid) (SoloFault U P tid) Q x) :
    (∀ y, Relation.ReflTransGen (SoloStep U P base tid) x y → NoThreadSys U tid y) →
    ∀ C, SoloRel tid x C →
      SMust (MtStep U sc P base) (MtFault U sc P) (fun C => ∃ y, SoloRel tid y C ∧ Q y) C := by
  induction h with
  | done hq => exact fun _ C hR => .done ⟨_, hR, hq⟩
  | @step a hf _ ih =>
    intro hn C hR
    refine .step (fun h => hf ((fault_iff hR).1 h)) ?_
    intro C' hs
    obtain ⟨x', hx, hR'⟩ := step_solo hR (hn a .refl) hs
    exact ih x' hx (fun y hy => hn y (Relation.ReflTransGen.head hx hy)) C' hR'

end Silmaril.Proofs.Process.Mt.Solo
